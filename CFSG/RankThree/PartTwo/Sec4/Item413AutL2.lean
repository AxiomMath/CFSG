module

public import CFSG.RankThree.PartTwo.Sec4.Item413AutGen
public import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Assembly.RankThreeEven (projSL)

variable {K : Type} [Field K]

@[expose] def blockThree (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem blockThree_one : blockThree (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockThree]

theorem blockThree_mul (A C : Matrix (Fin 2) (Fin 2) K) :
    blockThree (A * C) = blockThree A * blockThree C := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockThree, Matrix.mul_apply, Fin.sum_univ_succ]

@[expose] def blockThreeHom : Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 3) (Fin 3) K where
  toFun := blockThree
  map_one' := blockThree_one
  map_mul' := blockThree_mul

@[simp] theorem blockThreeHom_apply (A : Matrix (Fin 2) (Fin 2) K) :
    blockThreeHom A = blockThree A := rfl

@[expose] noncomputable def slTwoToPGL3 :
    Matrix.SpecialLinearGroup (Fin 2) K →*
      GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K :=
  (QuotientGroup.mk' _).comp ((Units.map (blockThreeHom (K := K))).comp
    Matrix.SpecialLinearGroup.toGL)

theorem slTwoToPGL3_injective : Function.Injective (slTwoToPGL3 (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  rw [MonoidHom.mem_ker, slTwoToPGL3, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hs
  obtain ⟨c, hc⟩ := hs
  have hentry : ∀ i j, (Matrix.scalar (Fin 3) (c : K)) i j =
      blockThree (s : Matrix (Fin 2) (Fin 2) K) i j := fun i j => by
    have h := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) i j) hc
    simpa [Matrix.GeneralLinearGroup.coe_scalar] using h
  have h22 := hentry 2 2
  simp [blockThree, Matrix.scalar_apply] at h22
  rw [Subgroup.mem_bot]
  ext i j
  have h := hentry (Fin.castLE (by norm_num) i) (Fin.castLE (by norm_num) j)
  fin_cases i <;> fin_cases j <;>
    simp [blockThree, Matrix.scalar_apply, h22] at h ⊢ <;> simp [h]

theorem sq_eq_one_of_toPGL_eq_one {s : Matrix.SpecialLinearGroup (Fin 2) K}
    (hs : Matrix.SpecialLinearGroup.toPGL s = 1) : s ^ 2 = 1 := by
  have hc : s ∈ Subgroup.center _ := by
    rw [← Matrix.SpecialLinearGroup.toPGL_ker]
    exact hs
  obtain ⟨r, hr, hrs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrs, ← map_pow, hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem card_le_nine_of_pgl2 [Finite K] (h3 : (3 : K) ≠ 0) (E : Subgroup (PGL2 K))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ≤ 9 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Finite (PGL2 K) :=
    Finite.of_surjective _ (Matrix.ProjGenLinGroup.mk_surjective (n := Fin 2) (R := K))
  set φ : Matrix.SpecialLinearGroup (Fin 2) K →* PGL2 K := Matrix.SpecialLinearGroup.toPGL
  have hEr : E ≤ φ.range := by
    intro e he
    obtain ⟨x, hx⟩ := KFacts.exists_toPGL_eq_of_pow_three (hexp e he)
    induction x using QuotientGroup.induction_on with
    | H s => exact ⟨s, hx⟩
  set Et := E.comap φ
  have hdvd : Nat.card E ∣ Nat.card Et := by
    have h := Subgroup.card_map_dvd (H := Et) φ
    rwa [Subgroup.map_comap_eq_self hEr] at h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hexp g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  obtain ⟨P⟩ : Nonempty (Sylow 3 Et) := inferInstance
  have hP : 3 ^ k ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (hk ▸ hdvd)
  set Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := (P : Subgroup Et).map Et.subtype
  have hQcard : Nat.card Q = Nat.card P :=
    Subgroup.card_map_of_injective Et.subtype_injective
  have hQp : IsPGroup 3 Q := P.isPGroup'.map Et.subtype
  have htriv : ∀ s ∈ Q, φ s = 1 → s = 1 := by
    intro s hs h1
    obtain ⟨n, hn⟩ := hQp ⟨s, hs⟩
    have hn' : s ^ (3 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have h := pow_gcd_eq_one.mpr ⟨sq_eq_one_of_toPGL_eq_one h1, hn'⟩
    rwa [Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 2 3), pow_one] at h
  have hQE : ∀ s ∈ Q, φ s ∈ E := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hQcomm : ∀ s ∈ Q, ∀ t ∈ Q, s * t = t * s := by
    intro s hs t ht
    have h := htriv (s * t * s⁻¹ * t⁻¹)
      (Q.mul_mem (Q.mul_mem (Q.mul_mem hs ht) (Q.inv_mem hs)) (Q.inv_mem ht)) (by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm _ (hQE s hs) _ (hQE t ht)]
        group)
    calc s * t = s * t * s⁻¹ * t⁻¹ * (t * s) := by group
      _ = t * s := by rw [h, one_mul]
  have hQexp : ∀ s ∈ Q, s ^ 3 = 1 := fun s hs =>
    htriv _ (Q.pow_mem hs 3) (by rw [map_pow, hexp _ (hQE s hs)])
  have h9 := card_le_nine_of_pgl3 h3 (Q.map slTwoToPGL3) (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hQcomm x hx y hy]) (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hQexp x hx, map_one])
  rw [Subgroup.card_map_of_injective slTwoToPGL3_injective, hQcard] at h9
  rw [hk]
  exact (Nat.le_of_dvd Nat.card_pos hP).trans h9

variable [Finite K]

theorem card_le_27_of_mulAut_PSL2 (h3 : (3 : K) ≠ 0) (B : Subgroup (MulAut (PSL2 K)))
    (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 27 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, f, hp, hK⟩ := FiniteField.card' K
  have hcycK := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K
    (by rw [Nat.card_eq_fintype_card, hK])).2
  set N := (pglAction K).range
  set C := (psl2FieldAut K).range
  have hcyc : IsCyclic C :=
    isCyclic_of_surjective (psl2FieldAut K).rangeRestrict
      (psl2FieldAut K).rangeRestrict_surjective
  have hCN : C ≤ Subgroup.normalizer (N : Set (MulAut (PSL2 K))) := by
    rintro _ ⟨σ, rfl⟩
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨g, rfl⟩ := hx
    exact ⟨_, (KFacts.psl2FieldAut_mul_pglAction_mul_inv σ g).symm⟩
  have hBNC : ∀ b ∈ B, ∃ n ∈ N, ∃ c ∈ C, b = n * c := by
    intro b _
    obtain ⟨g, σ, hgσ⟩ := KFacts.exists_pglAction_mul_psl2FieldAut b
    exact ⟨pglAction K g, ⟨g, rfl⟩, psl2FieldAut K σ, ⟨σ, rfl⟩, hgσ⟩
  set E := (B ⊓ N).comap (pglAction K)
  have hcardE : Nat.card E = Nat.card (B ⊓ N : Subgroup _) := by
    have h := Subgroup.card_map_of_injective (K := E) (KFacts.pglAction_injective (K := K))
    rw [Subgroup.map_comap_eq_self inf_le_right] at h
    exact h.symm
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h9 : Nat.card (B ⊓ N : Subgroup _) ≤ 9 := by
    rw [← hcardE]
    refine card_le_nine_of_pgl2 h3 E (fun x hx y hy => KFacts.pglAction_injective ?_)
      (fun x hx => KFacts.pglAction_injective ?_)
    · rw [map_mul, map_mul]
      exact hBc _ (Subgroup.mem_comap.mp hx).1 _ (Subgroup.mem_comap.mp hy).1
    · rw [map_pow, map_one]
      exact hB.2 _ (Subgroup.mem_comap.mp hx).1
  have h1 := card_le_three_mul_card_inf hB hcyc hCN hBNC
  omega

theorem rankAutL2_holds : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 3 → 1 ≤ f →
    CFSG.pRank 3 (MulAut (projSL 2 (GaloisField p f))) ≤ 3 := by
  intro p f _ hp3 hf
  have h3 := three_ne_zero_of_card (Fact.out) hp3 (GaloisField.card p f (by omega))
  exact pRank_three_le_of_card_le (card_le_of_mulEquiv_mulAut (projSLEquivPSLn 2 _)
    (card_le_27_of_mulAut_PSL2 h3))

end CFSG.RankThree.PartTwo.Sec4
