module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofCentS

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof Subgroup
open scoped MatrixGroups Pointwise

theorem commutator_mem_of_mem_mul {G : Type*} [Group G] {H Q : Subgroup G}
    (hHQ : H ≤ normalizer (Q : Set G)) (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) {x y : G}
    (hx : x ∈ (H : Set G) * (Q : Set G)) (hy : y ∈ (H : Set G) * (Q : Set G)) :
    x * y * x⁻¹ * y⁻¹ ∈ Q := by
  obtain ⟨h, hh, q, hq, rfl⟩ := hx
  obtain ⟨h', hh', q', hq', rfl⟩ := hy
  have hn : ∀ g ∈ H, ∀ a ∈ Q, g * a * g⁻¹ ∈ Q := fun g hg a ha =>
    (mem_normalizer_iff.1 (hHQ hg) a).1 ha
  have hn' : ∀ g ∈ H, ∀ a ∈ Q, g⁻¹ * a * g ∈ Q := fun g hg a ha => by
    simpa using hn g⁻¹ (inv_mem hg) a ha
  have hq₁ := hn' h' hh' q hq
  have hq₂ := hn' h hh q' hq'
  have key : h * q * (h' * q') * (h * q)⁻¹ * (h' * q')⁻¹ =
      (h * h') * ((h'⁻¹ * q * h') * q' * q⁻¹ * (h⁻¹ * q' * h)⁻¹) * (h' * h)⁻¹ := by group
  rw [key, ← hH h hh h' hh']
  exact hn _ (mul_mem hh hh') _ (mul_mem (mul_mem (mul_mem hq₁ hq') (inv_mem hq)) (inv_mem hq₂))

section Outer

variable
  {L : Type} [Field L]

theorem torusGroup_mul_comm {L : Type} [Field L] {a b : ModGL TwistTag.D4.tag L}
    (ha : a ∈ torusGroup TwistTag.D4.tag L) (hb : b ∈ torusGroup TwistTag.D4.tag L) :
    a * b = b * a := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ha
  exact rootDiagUnit_mul_comm_of_mem_torusGroup l hb

theorem exists_HSL_of_sign {A : SL2 L} (hA : A = 1 ∨ A = -1) :
    ∃ a : Lˣ, a ^ 2 = 1 ∧ A = HSL a := by
  rcases hA with rfl | rfl
  · exact ⟨1, one_pow 2, HSL_units_one.symm⟩
  · exact ⟨-1, by norm_num, neg_one_eq_HSL⟩

theorem outerTriple_signs {A B C : SL2 L} (hA : A = 1 ∨ A = -1) (hB : B = 1 ∨ B = -1)
    (hC : C = 1 ∨ C = -1) (h : A * B * C = 1) : outerTriple L (A, B, C) = 1 := by
  obtain ⟨a, ha, rfl⟩ := exists_HSL_of_sign hA
  obtain ⟨b, hb, rfl⟩ := exists_HSL_of_sign hB
  obtain ⟨c, hc, rfl⟩ := exists_HSL_of_sign hC
  have habc : a * b * c = 1 := by
    rw [HSL_mul_units, HSL_mul_units] at h
    have h00 := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L) 0 0) h
    simp only [coe_HSL, Matrix.SpecialLinearGroup.coe_one] at h00
    exact Units.ext (by simpa using h00)
  rw [outerTriple_HSL_units, ← rootDiagUnit_one]
  congr 1
  funext j
  have e2 : ∀ x : Lˣ, x ^ (2 : ℤ) = x ^ 2 := fun x => zpow_ofNat x 2
  fin_cases j
  · simp only [Pi.one_apply]
    rw [show TwistTag.D4.tag.cartan n0 ⟨0, by decide⟩ = 2 by decide,
      show TwistTag.D4.tag.cartan n1 ⟨0, by decide⟩ = 0 by decide,
      show TwistTag.D4.tag.cartan n3 ⟨0, by decide⟩ = 0 by decide, e2, ha]
    simp
  · simp only [Pi.one_apply]
    rw [show TwistTag.D4.tag.cartan n0 ⟨1, by decide⟩ = 0 by decide,
      show TwistTag.D4.tag.cartan n1 ⟨1, by decide⟩ = 2 by decide,
      show TwistTag.D4.tag.cartan n3 ⟨1, by decide⟩ = 0 by decide, e2, hb]
    simp
  · simp only [Pi.one_apply]
    rw [show TwistTag.D4.tag.cartan n0 ⟨2, by decide⟩ = -1 by decide,
      show TwistTag.D4.tag.cartan n1 ⟨2, by decide⟩ = -1 by decide,
      show TwistTag.D4.tag.cartan n3 ⟨2, by decide⟩ = -1 by decide]
    simp only [_root_.zpow_neg_one]
    rw [← mul_inv, ← mul_inv, habc, inv_one]
  · simp only [Pi.one_apply]
    rw [show TwistTag.D4.tag.cartan n0 ⟨3, by decide⟩ = 0 by decide,
      show TwistTag.D4.tag.cartan n1 ⟨3, by decide⟩ = 0 by decide,
      show TwistTag.D4.tag.cartan n3 ⟨3, by decide⟩ = 2 by decide, e2, hc]
    simp

theorem map_sign (Fr : L →+* L) {A : SL2 L} (hA : A = 1 ∨ A = -1) :
    Matrix.SpecialLinearGroup.map Fr A = A := by
  rcases hA with rfl | rfl
  · exact map_one _
  · refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, map_neg, map_one]

theorem sign_mul_self {A : SL2 L} (hA : A = 1 ∨ A = -1) : A * A = 1 := by
  rcases hA with rfl | rfl
  · rw [one_mul]
  · rw [neg_one_mul, neg_neg]

theorem range_rankOneHom_le_outer {i : Fin TwistTag.D4.tag.rank} (hi : i = n0 ∨ i = n1 ∨ i = n3) :
    (rankOneHom TwistTag.D4 L i).range ≤ (outerTriple L).range := by
  rintro _ ⟨A, rfl⟩
  rcases hi with rfl | rfl | rfl
  · exact ⟨(A, 1, 1), by rw [outerTriple_apply]; simp⟩
  · exact ⟨(1, A, 1), by rw [outerTriple_apply]; simp⟩
  · exact ⟨(1, 1, A), by rw [outerTriple_apply]; simp⟩

theorem rootSubgroup_single_le_outer {i : Fin TwistTag.D4.tag.rank}
    (hi : i = n0 ∨ i = n1 ∨ i = n3) :
    rootSubgroup TwistTag.D4.tag L (Pi.single i 1) ≤ (outerTriple L).range ∧
      rootSubgroup TwistTag.D4.tag L (-Pi.single i 1) ≤ (outerTriple L).range := by
  have h := range_rankOneHom_le_outer (L := L) hi
  rw [range_rankOneHom_eq] at h
  exact ⟨le_sup_left.trans h, le_sup_right.trans h⟩

theorem rootSpan_sigmaB_le : rootSpan TwistTag.D4.tag L sigmaB ≤ (outerTriple L).range := by
  refine iSup₂_le fun α hα => ?_
  obtain ⟨k, hk, rfl⟩ := hα
  have e : ∀ (k : Fin 24) (v : Fin TwistTag.D4.tag.rank → ℤ),
      (∀ i, (d4RootVec k : Fin TwistTag.D4.tag.rank → ℤ) i = v i) →
        (d4RootVec k : Fin TwistTag.D4.tag.rank → ℤ) = v := fun k v h => funext h
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e 0 (Pi.single n0 1) (by intro i; fin_cases i <;> rfl)]
    exact (rootSubgroup_single_le_outer (Or.inl rfl)).1
  · rw [e 4 (-Pi.single n0 1) (by intro i; fin_cases i <;> rfl)]
    exact (rootSubgroup_single_le_outer (Or.inl rfl)).2
  · rw [e 1 (Pi.single n1 1) (by intro i; fin_cases i <;> rfl)]
    exact (rootSubgroup_single_le_outer (Or.inr (Or.inl rfl))).1
  · rw [e 6 (-Pi.single n1 1) (by intro i; fin_cases i <;> rfl)]
    exact (rootSubgroup_single_le_outer (Or.inr (Or.inl rfl))).2
  · rw [e 3 (Pi.single n3 1) (by intro i; fin_cases i <;> rfl)]
    exact (rootSubgroup_single_le_outer (Or.inr (Or.inr rfl))).1
  · rw [e 10 (-Pi.single n3 1) (by intro i; fin_cases i <;> rfl)]
    exact (rootSubgroup_single_le_outer (Or.inr (Or.inr rfl))).2

end Outer

section Rational

variable
  {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L]

theorem exists_map_algebraMap {A : SL2 L}
    (hA : ∀ i j, (A : Matrix (Fin 2) (Fin 2) L) i j ^ Nat.card K =
      (A : Matrix (Fin 2) (Fin 2) L) i j) :
    ∃ A' : SL2 K, Matrix.SpecialLinearGroup.map (algebraMap K L) A' = A := by
  choose M hM using fun i j => mem_range_algebraMap_of_pow_card_eq (k := K) (hA i j)
  have hdet : (Matrix.of M).det = 1 := by
    apply (algebraMap K L).injective
    rw [RingHom.map_det, map_one]
    have : (algebraMap K L).mapMatrix (Matrix.of M) = (A : Matrix (Fin 2) (Fin 2) L) :=
      Matrix.ext fun i j => hM i j
    rw [this]
    exact A.2
  exact ⟨⟨Matrix.of M, hdet⟩, Subtype.ext (Matrix.ext fun i j => hM i j)⟩

theorem mem_short_of_triEmb_eq_outerTriple {q : ℕ} (hK : Nat.card K = q ^ 3)
    (hσ : ∀ c, σ c = c ^ q) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ q)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} {X : SL2 L × SL2 L × SL2 L}
    (hz : triEmb K σ L z = outerTriple L X) : z ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom := by
  have hcomm : ∀ c, algebraMap K L (σ c) = Fr (algebraMap K L c) := fun c => by
    rw [hσ, hFr, map_pow]
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  obtain ⟨A, B, C⟩ := X
  have hfix : outerTriple L (Matrix.SpecialLinearGroup.map Fr C,
      Matrix.SpecialLinearGroup.map Fr A, Matrix.SpecialLinearGroup.map Fr B) =
        outerTriple L (A, B, C) := by
    rw [← twistHom_outerTriple, ← hz]
    exact triEmb_fixed Fr (RingHom.ext hcomm) z
  have hker : outerTriple L (Matrix.SpecialLinearGroup.map Fr C * A⁻¹,
      Matrix.SpecialLinearGroup.map Fr A * B⁻¹, Matrix.SpecialLinearGroup.map Fr B * C⁻¹) = 1 := by
    rw [show (Matrix.SpecialLinearGroup.map Fr C * A⁻¹, Matrix.SpecialLinearGroup.map Fr A * B⁻¹,
        Matrix.SpecialLinearGroup.map Fr B * C⁻¹) = (Matrix.SpecialLinearGroup.map Fr C,
          Matrix.SpecialLinearGroup.map Fr A, Matrix.SpecialLinearGroup.map Fr B) *
            (A, B, C)⁻¹ from rfl, map_mul, map_inv, hfix, mul_inv_cancel]
  obtain ⟨h0, h1, h3, hprod⟩ := outerTriple_ker hker
  set e₀ := Matrix.SpecialLinearGroup.map Fr C * A⁻¹ with he₀
  set e₁ := Matrix.SpecialLinearGroup.map Fr A * B⁻¹ with he₁
  set e₃ := Matrix.SpecialLinearGroup.map Fr B * C⁻¹ with he₃
  have hFA : Matrix.SpecialLinearGroup.map Fr A = e₁ * B := by rw [he₁]; group
  have hFB : Matrix.SpecialLinearGroup.map Fr B = e₃ * C := by rw [he₃]; group
  have hFC : Matrix.SpecialLinearGroup.map Fr C = e₀ * A := by rw [he₀]; group
  set A' := e₃ * A with hA'
  have hA'1 : Matrix.SpecialLinearGroup.map Fr A' = e₃ * e₁ * B := by
    rw [hA', map_mul, map_sign Fr h3, hFA]
    exact (mul_assoc _ _ _).symm
  have hA'2 : Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr A') =
      e₁ * C := by
    rw [hA'1, map_mul, map_mul, map_sign Fr h3, map_sign Fr h1, hFB]
    rcases h3 with h | h <;> rcases h1 with h' | h' <;> rw [h, h'] <;> simp
  have hA'3 : Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr
      (Matrix.SpecialLinearGroup.map Fr A')) = A' := by
    have hinv : ∀ {E : SL2 L}, (E = 1 ∨ E = -1) → E⁻¹ = E := fun hE =>
      inv_eq_of_mul_eq_one_right (sign_mul_self hE)
    have h3' : e₃ = (e₀ * e₁)⁻¹ := eq_inv_of_mul_eq_one_right hprod
    rw [hA'2, map_mul, map_sign Fr h1, hFC, hA', ← mul_assoc, h3', _root_.mul_inv_rev, hinv h1,
      hinv h0]
  have hent : ∀ i j, (A' : Matrix (Fin 2) (Fin 2) L) i j ^ Nat.card K =
      (A' : Matrix (Fin 2) (Fin 2) L) i j := by
    intro i j
    have := congrArg (fun Y : SL2 L => (Y : Matrix (Fin 2) (Fin 2) L) i j) hA'3
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hFr] at this
    rw [hK]
    rw [← pow_mul, ← pow_mul] at this
    rw [show q ^ 3 = q * (q * q) by ring]
    exact this
  obtain ⟨A'', hA''⟩ := exists_map_algebraMap (K := K) hent
  set f₁ : K →+* orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer :=
    (RingHom.id K).codRestrict _ (mem_orbitField_outer hσ3) with hf₁
  set B'' := Matrix.SpecialLinearGroup.map f₁ A'' with hB''
  have hB0 : Matrix.SpecialLinearGroup.map (outerEmb K σ L) B'' = A' := by
    rw [← hA'']
    exact Subtype.ext (Matrix.ext fun i j => rfl)
  refine ⟨B'', ?_⟩
  apply baseChangeGL_injective (algebraMap K L)
  change baseChangeGL (algebraMap K L)
    (orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer B'') = triEmb K σ L z
  rw [triEmb_orbitRankOneHom_frob hcomm, hB0, hz]
  change outerTriple L (A', Matrix.SpecialLinearGroup.map Fr A',
    Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr A')) = _
  rw [hA'2, hA'1]
  have hratio : outerTriple L (A', e₃ * e₁ * B, e₁ * C) =
      outerTriple L (e₃, e₃ * e₁, e₁) * outerTriple L (A, B, C) := by
    rw [← map_mul]
    rfl
  rw [hratio, outerTriple_signs h3 ?_ h1 ?_, one_mul]
  · rcases h3 with h | h <;> rcases h1 with h' | h' <;> rw [h, h'] <;> simp
  · calc e₃ * (e₃ * e₁) * e₁ = e₃ * e₃ * (e₁ * e₁) := by group
      _ = 1 := by rw [sign_mul_self h3, sign_mul_self h1, one_mul]

end Rational

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
