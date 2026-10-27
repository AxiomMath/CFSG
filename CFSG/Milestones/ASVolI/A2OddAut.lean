module

public import CFSG.Milestones.ASVolI.A2
public import CFSG.RankThree.PartOne.CTP.SpAut
public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofG2
public import CFSG.RankThree.PartTwo.KFacts.AutPSUInner
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Aut

public section

namespace CFSG.ASVolI

open CFSG.Open

section Induced

variable {G : Type} [Group G] (L : Subgroup G) [L.Normal]

@[expose] noncomputable def burnsideA26_barAut : G →* MulAut (↥L ⧸ pCore 2 ↥L) where
  toFun x := QuotientGroup.congr (pCore 2 ↥L) (pCore 2 ↥L) (MulAut.conjNormal x)
    (Subgroup.characteristic_iff_map_eq.1 inferInstance (MulAut.conjNormal x))
  map_one' := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H y => simp
  map_mul' x y := by
    ext z
    induction z using QuotientGroup.induction_on with
    | H z =>
      simp only [map_mul, MulAut.mul_apply]
      rfl

end Induced

@[expose] noncomputable def burnsideA26_descend (S : Type*) [Group S] :
    MulAut S →* MulAut (S ⧸ Subgroup.center S) where
  toFun σ := QuotientGroup.congr _ _ σ
    (Subgroup.characteristic_iff_map_eq.1 inferInstance σ)
  map_one' := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H y => rfl
  map_mul' σ τ := by
    ext z
    induction z using QuotientGroup.induction_on with
    | H z =>
      simp only [map_mul, MulAut.mul_apply]
      rfl

section Induced2

variable {G : Type} [Group G] (L : Subgroup G) [L.Normal]

@[expose] noncomputable def burnsideA26_indAut :
    G →* MulAut ((↥L ⧸ pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ pCore 2 ↥L)) :=
  (burnsideA26_descend (↥L ⧸ pCore 2 ↥L)).comp (burnsideA26_barAut L)

theorem burnsideA26_indAut_apply (x : G) (l : ↥L) :
    burnsideA26_indAut L x (QuotientGroup.mk (QuotientGroup.mk l)) =
      QuotientGroup.mk (QuotientGroup.mk (MulAut.conjNormal x l)) := rfl

theorem burnsideA26_orderOf_indAut_dvd (x : G) :
    orderOf (burnsideA26_indAut L x) ∣ orderOf x :=
  orderOf_map_dvd _ x

end Induced2

theorem burnsideA26_sqt_of_sections {G : Type} [Group G] [Finite G] (L : Subgroup G) [L.Normal]
    (hsec : ∀ (N : Subgroup ↥L) [N.Normal] [IsSimpleGroup (↥L ⧸ N)],
      (∃ a b : ↥L ⧸ N, a * b ≠ b * a) → CFSG.IsStronglyQuasithin (↥L ⧸ N))
    (hq : CFSG.IsQuasisimple (↥L ⧸ pCore 2 ↥L)) :
    CFSG.IsStronglyQuasithin ((↥L ⧸ pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ pCore 2 ↥L)) := by
  set Q := ↥L ⧸ pCore 2 ↥L
  let N : Subgroup ↥L := (Subgroup.center Q).comap (QuotientGroup.mk' (pCore 2 ↥L))
  haveI : N.Normal := inferInstance
  have hle : pCore 2 ↥L ≤ N := fun n hn => by
    show QuotientGroup.mk' (pCore 2 ↥L) n ∈ Subgroup.center Q
    have h1 : QuotientGroup.mk' (pCore 2 ↥L) n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [h1]
    exact one_mem _
  have hmap : N.map (QuotientGroup.mk' (pCore 2 ↥L)) = Subgroup.center Q :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  let e : Q ⧸ Subgroup.center Q ≃* ↥L ⧸ N :=
    (QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient (pCore 2 ↥L) N hle)
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hq.2.1
  haveI : IsSimpleGroup (↥L ⧸ N) := e.symm.isSimpleGroup
  have hnonab : ∃ a b : ↥L ⧸ N, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    refine ⟨e a, e b, fun h => hab ?_⟩
    apply e.injective
    rw [map_mul, map_mul, h]
  exact CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv e (hsec N hnonab)

theorem burnsideA26_isEvenLieThmC_of_sqt {S : Type} [Group S] [Finite S]
    (hSQT : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup S) ≤ 2)
    (hex : CFSG.Blueprint.ExceptionalRep S →
      (∃ f, 2 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel S .G2 2 f) ∨
      (∃ f, 1 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 2 f) ∨
      (∃ f, Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.ReeTitsModel S .twistedF4 2 f) ∨
      CFSG.Blueprint.ReeTitsModel S .Tits 2 1 ∨
      (∃ f, Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.SuzukiModel S 2 f))
    (h : ChA.IsEvenLieAll S) : ChA.IsEvenLieThmC S := by
  have hexc : CFSG.Blueprint.ExceptionalRep S → ChA.IsEvenLieThmC S := fun hE => by
    rcases hex hE with ⟨f, -, hm⟩ | ⟨f, -, hm⟩ | ⟨f, -, -, hm⟩ | hm | ⟨f, -, -, hm⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hm⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hm⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hm⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hm⟩))))))
  rcases h with ⟨t, n, f, -, hmodel⟩ | h6 | hU
  · rcases hmodel with ⟨-, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, -, hm⟩
    · rcases CFSG.SectionRank.ClassicalEven.sqt_even_classical_restriction hSQT hm with
        ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, hn45, rfl⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩
      · exact Or.inl ⟨f, hm⟩
      · exact Or.inr (Or.inl ⟨f, hm⟩)
      · rcases hn45 with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inl hm)))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inl hm))))))))))
      · exact Or.inr (Or.inr (Or.inl ⟨f, hm⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hm⟩)))
    · exact hexc (Or.inl ⟨t, 2, f, ht, hm⟩)
    · exact hexc (Or.inr (Or.inl ⟨t, 2, f, ht, hm⟩))
    · exact hexc (Or.inr (Or.inr ⟨2, f, hm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h6)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr hU)))))))))))

theorem burnsideA26_congr_congr_symm {S M : Type*} [Group S] [Group M] (e : S ≃* M)
    (φ : MulAut M) : MulAut.congr e (MulAut.congr e.symm φ) = φ := by
  ext x
  simp [MulAut.congr_apply]

theorem burnsideA26_congr_symm_congr {S M : Type*} [Group S] [Group M] (e : S ≃* M)
    (φ : MulAut S) : MulAut.congr e.symm (MulAut.congr e φ) = φ := by
  ext x
  simp [MulAut.congr_apply]

theorem burnsideA26_charP_two {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [← Nat.card_eq_fintype_card, hK])

theorem burnsideA26_mem_of_index_le_two {A : Type*} [Group A] [Finite A] (H : Subgroup A)
    (hH : H.index ≤ 2) {a : A} (ha : Odd (orderOf a)) : a ∈ H := by
  by_contra hne
  have hne1 : H.index ≠ 1 := fun h1 => hne (by rw [Subgroup.index_eq_one] at h1; rw [h1]; trivial)
  have h0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : H.index = 2 := by omega
  obtain ⟨m, hm⟩ := ha
  have h2 : a * a ∈ H := Subgroup.mul_self_mem_of_index_two hidx a
  have h3 : a ^ (2 * m) ∈ H := by
    rw [pow_mul, sq]
    exact pow_mem h2 m
  have h5 : a ^ (2 * m) * a ∈ H := by
    rw [← pow_succ]
    have : a ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one a
    rw [this]
    exact one_mem _
  exact hne (((Subgroup.mul_mem_iff_of_index_two hidx).mp h5).mp h3)

theorem burnsideA26_congr_trans_apply {S Q A : Type*} [Group S] [Group Q] [Group A]
    (e : S ≃* Q) (κ : Q ≃* A) (F : MulAut A) (q : Q) :
    MulAut.congr e (MulAut.congr (e.trans κ).symm F) q = κ.symm (F (κ q)) := by
  simp [MulAut.congr_apply]

section Sp4Fam

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.PartTwo.KFacts

theorem burnsideA26_sp4 {S : Type} [Group S] {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (e : S ≃* StatedProj (StatedSp 2 K)) (θ : MulAut S)
    (hθ : Odd (orderOf θ)) : ChA.IsInnDiagFieldAut S θ := by
  set α : MulAut (StatedProj (StatedSp 2 K)) := MulAut.congr e θ with hα
  have hαp : α ^ orderOf θ = 1 := by
    rw [hα, ← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨A, σ, hAσ⟩ := (mem_spSemilinearAutGroup_iff (r := 2) (K := K)).1
    (CFSG.RankThree.PartOne.CTP.mem_spSemilinearAutGroup_of_odd_pow hθ hαp)
  have hinner : IsInnerAut (MulAut.congr e.symm (conjAut 2 K A)) :=
    (isInnerAut_congr e.symm _).2 (conjAut_mem_inner_of_charTwo A)
  refine ⟨MulAut.congr e.symm (conjAut 2 K A), MulAut.congr e.symm (fieldAut 2 K σ),
    Or.inl hinner, ?_, ?_⟩
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨n, K, inferInstance, inferInstance, e, σ, hK, ?_⟩)))
    intro g
    refine ⟨fieldSp 2 K σ g, rfl, ?_⟩
    rw [burnsideA26_congr_congr_symm]
    rfl
  · rw [← map_mul, ← hAσ, hα, burnsideA26_congr_symm_congr]

end Sp4Fam

section G2Fam

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem burnsideA26_g2
    {S : Type} [Group S] {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hK4 : 4 ≤ Nat.card K) (e : S ≃* AdjointQuotient Tag.G2 K) (θ : MulAut S) :
    ChA.IsInnDiagFieldAut S θ := by
  haveI : CharP K 2 := burnsideA26_charP_two hK
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    norm_num
  have hZ := center_adjointGroup_eq_bot (τ := Tag.G2) (K := K)
  let κ : AdjointQuotient Tag.G2 K ≃* adjointGroup Tag.G2 K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hκ : ∀ g : adjointGroup Tag.G2 K, κ.symm g = QuotientGroup.mk g := fun g => by
    apply κ.injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  let ε : S ≃* adjointGroup Tag.G2 K := e.trans κ
  obtain ⟨g, σ, hgσ⟩ := (CFSG.RankThree.PartTwo.KFacts.g2_automorphism_normal_form hK3 hK4).1
    (MulAut.congr ε θ)
  have hθ : θ = MulAut.congr ε.symm (MulAut.conj g) * MulAut.congr ε.symm
      (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ) := by
    rw [← map_mul, ← hgσ, burnsideA26_congr_symm_congr]
  refine ⟨MulAut.congr ε.symm (MulAut.conj g),
    MulAut.congr ε.symm (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ), Or.inl ?_, ?_, hθ⟩
  · exact (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr ε.symm _).2
      (CFSG.RankThree.PartTwo.KFacts.isInnerAut_conj g)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨n, K, inferInstance, inferInstance, e, σ, hK, fun x => ?_⟩)))))
    refine ⟨CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ x, ?_, ?_⟩
    · exact CFSG.RankThree.PartTwo.KFacts.coe_g2FieldHom σ x
    · rw [burnsideA26_congr_trans_apply]
      have h1 : κ (QuotientGroup.mk x) = x := by rw [← hκ x]; exact κ.apply_symm_apply x
      rw [h1, hκ]

end G2Fam

section SzFam

open CFSG.Blueprint

theorem burnsideA26_sz
    {S : Type} [Group S] {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : S ≃* ↥(suzukiGroup a K)) (θ : MulAut S) :
    ChA.IsInnDiagFieldAut S θ := by
  obtain ⟨g, σ, hgσ⟩ := CFSG.RankThree.PartTwo.KFacts.exists_conj_mul_szFieldAut ha hK
    (MulAut.congr e θ)
  have hθ : θ = MulAut.congr e.symm (MulAut.conj g) * MulAut.congr e.symm
      (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K σ) := by
    rw [← map_mul, ← hgσ, burnsideA26_congr_symm_congr]
  refine ⟨MulAut.congr e.symm (MulAut.conj g),
    MulAut.congr e.symm (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K σ),
    Or.inl ?_, ?_, hθ⟩
  · exact (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e.symm _).2
      (CFSG.RankThree.PartTwo.KFacts.isInnerAut_conj g)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨a, K, inferInstance, inferInstance, e, σ, hK, fun x => ?_⟩))))
    refine ⟨CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K σ x, rfl, ?_⟩
    rw [burnsideA26_congr_congr_symm]

end SzFam

open CFSG.Blueprint in
@[expose] def burnsideA26_dcqEquiv {M : Type} [Group M] (H C : Subgroup M) (hHC : ⁅H, H⁆ = C)
    (hZ : Subgroup.center ↥C = ⊥) : DerivedCentralQuotient H ≃* ↥C := by
  subst hHC
  exact (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

theorem burnsideA26_dcqEquiv_mk {M : Type} [Group M] (H C : Subgroup M) (hHC : ⁅H, H⁆ = C)
    (hZ : Subgroup.center ↥C = ⊥) (g : ↥⁅H, H⁆) :
    ((burnsideA26_dcqEquiv H C hHC hZ (QuotientGroup.mk g) : ↥C) : M) = (g : M) := by
  subst hHC
  rfl

open CFSG.Blueprint in
theorem burnsideA26_dcq' {M : Type} [Group M] (H C : Subgroup M) (hHC : ⁅H, H⁆ = C)
    (hZ : Subgroup.center ↥C = ⊥) {S : Type} [Group S] (e : S ≃* DerivedCentralQuotient H)
    (θ : MulAut S) {Φ : Type*} (F : Φ → MulAut ↥C) (act : Φ → M → M)
    (hact : ∀ (β : Φ) (x : ↥C), ((F β x : ↥C) : M) = act β x) (x : ↥C) (β : Φ)
    (hxβ : MulAut.congr (e.trans (burnsideA26_dcqEquiv H C hHC hZ)) θ = MulAut.conj x * F β) :
    ∃ ψ₁ ψ₂ : MulAut S, CFSG.RankThree.PartTwo.KFacts.IsInnerAut ψ₁ ∧ θ = ψ₁ * ψ₂ ∧
      ∀ g : ↥⁅H, H⁆, ∃ g' : ↥⁅H, H⁆, (g' : M) = act β g ∧
        MulAut.congr e ψ₂ (QuotientGroup.mk g) = QuotientGroup.mk g' := by
  subst hHC
  set κ : DerivedCentralQuotient H ≃* ↥⁅H, H⁆ :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hκ : ∀ g : ↥⁅H, H⁆, κ (QuotientGroup.mk g) = g := fun g => rfl
  have hxβ' : MulAut.congr (e.trans κ) θ = MulAut.conj x * F β := hxβ
  refine ⟨MulAut.congr (e.trans κ).symm (MulAut.conj x),
    MulAut.congr (e.trans κ).symm (F β), ?_, ?_, fun g => ?_⟩
  · exact (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr (e.trans κ).symm _).2
      (CFSG.RankThree.PartTwo.KFacts.isInnerAut_conj x)
  · rw [← map_mul, ← hxβ', burnsideA26_congr_symm_congr]
  · refine ⟨F β g, hact β g, ?_⟩
    show (MulAut.congr e (MulAut.congr (e.trans κ).symm (F β))) (QuotientGroup.mk g) = _
    rw [burnsideA26_congr_trans_apply]
    apply κ.injective
    rw [MulEquiv.apply_symm_apply, hκ, hκ]

open CFSG.Blueprint in
theorem burnsideA26_dcq {M : Type} [Group M] (H C : Subgroup M) (hHC : ⁅H, H⁆ = C)
    (hZ : Subgroup.center ↥C = ⊥) {S : Type} [Group S] (e : S ≃* DerivedCentralQuotient H)
    (θ : MulAut S) {Φ : Type*} (F : Φ → MulAut ↥C) (act : Φ → M → M)
    (hact : ∀ (β : Φ) (x : ↥C), ((F β x : ↥C) : M) = act β x)
    (hNF : ∀ α : MulAut ↥C, ∃ (x : ↥C) (β : Φ), α = MulAut.conj x * F β) :
    ∃ ψ₁ ψ₂ : MulAut S, CFSG.RankThree.PartTwo.KFacts.IsInnerAut ψ₁ ∧ θ = ψ₁ * ψ₂ ∧
      ∃ β : Φ, ∀ g : ↥⁅H, H⁆, ∃ g' : ↥⁅H, H⁆, (g' : M) = act β g ∧
        MulAut.congr e ψ₂ (QuotientGroup.mk g) = QuotientGroup.mk g' := by
  obtain ⟨x, β, hxβ⟩ := hNF (MulAut.congr (e.trans (burnsideA26_dcqEquiv H C hHC hZ)) θ)
  obtain ⟨ψ₁, ψ₂, h1, h2, h3⟩ := burnsideA26_dcq' H C hHC hZ e θ F act hact x β hxβ
  exact ⟨ψ₁, ψ₂, h1, h2, β, h3⟩

section ReeF4Fam

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag

theorem burnsideA26_f4_aux
    {S : Type} [Group S] {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (H : Subgroup (ModGL Tag.F4 K))
    (hH : F4.reeGamma K a = H) (e : S ≃* DerivedCentralQuotient H) (θ : MulAut S) :
    ∃ ψ₁ ψ₂ : MulAut S, CFSG.RankThree.PartTwo.KFacts.IsInnerAut ψ₁ ∧ θ = ψ₁ * ψ₂ ∧
      ∃ σ : RingAut K, ∀ g : ↥⁅H, H⁆, ∃ g' : ↥⁅H, H⁆,
        (g' : ModGL Tag.F4 K) = Units.map (entrywiseHom (σ : K →+* K)) (g : ModGL Tag.F4 K) ∧
          MulAut.congr e ψ₂ (QuotientGroup.mk g) = QuotientGroup.mk g' := by
  have hperf : ⁅F4.reeGamma K a, F4.reeGamma K a⁆ = F4.reeGamma K a := by
    rw [← Subgroup.map_subtype_commutator, (ree_generic_fixed_group_perfect F4 a ha K hK).2.1,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  subst hH
  exact burnsideA26_dcq _ (F4.reeGamma K a) hperf (large_Ree_fixed_group_center_trivial a K hK) e θ
    (fun β : RingAut K => F4.reeGammaFieldAut K a β)
    (fun β g => Units.map (entrywiseHom (β : K →+* K)) g)
    (fun β x => coe_reeGammaFieldAut β x)
    (CFSG.RankThree.PartTwo.KFacts.largeRee_automorphism_normal_form ha hK).1

theorem burnsideA26_f4
    {S : Type} [Group S] {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : S ≃* DerivedCentralQuotient
      (reeFixedGroup Tag.F4 K reeF4Perm fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)))
    (θ : MulAut S) : ChA.IsInnDiagFieldAut S θ := by
  haveI : CharP K 2 := burnsideA26_charP_two hK
  haveI : CharP K F4.prime := (inferInstance : CharP K 2)
  obtain ⟨ψ₁, ψ₂, hin, hθ, σ, hσ⟩ :=
    burnsideA26_f4_aux ha hK _ (reeGamma_eq_reeFixedGroup (t := F4)) e θ
  exact ⟨ψ₁, ψ₂, Or.inl hin, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨a, K, inferInstance, inferInstance, e, σ, hK, hσ⟩))))))), hθ⟩

end ReeF4Fam

section RankFam

theorem burnsideA26_mem_of_pow_mem {Γ : Type} [Group Γ] [Finite Γ] {x y : Γ} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) {M : Subgroup Γ} (hyM : y ∈ M) :
    x ∈ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hoy : orderOf y = 3 := by
    have hdvd : orderOf y ∣ 3 := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← hox]
      exact orderOf_dvd_of_pow_eq_one (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, pow_orderOf_eq_one, one_zpow])
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := (Subgroup.zpowers_le).2 hy
  have heq : Subgroup.zpowers y = Subgroup.zpowers x := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, Nat.card_zpowers, hox, hoy]
  have hxz : x ∈ Subgroup.zpowers y := heq ▸ Subgroup.mem_zpowers x
  exact (Subgroup.zpowers_le).2 hyM hxz

theorem burnsideA26_three_le_pRank {Γ : Type} [Group Γ] [Finite Γ] {M : Subgroup Γ} {a b c : Γ}
    (ha : a ∈ M) (hb : b ∈ M) (hc : c ∉ M) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hc3 : c ^ 3 = 1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) (ha1 : a ≠ 1)
    (hb' : b ∉ Subgroup.zpowers a) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Γ) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc1 : c ≠ 1 := fun h => hc (h ▸ M.one_mem)
  have hb1 : b ≠ 1 := fun h => hb' (h ▸ Subgroup.one_mem _)
  set A := Subgroup.zpowers a
  set B := Subgroup.zpowers b
  set C := Subgroup.zpowers c
  have hAB : ∀ (u : A) (v : B), Commute (A.subtype u) (B.subtype v) := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    exact Commute.zpow_zpow hab i j
  have hAC : ∀ (u : A) (w : C), Commute (A.subtype u) (C.subtype w) := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    exact Commute.zpow_zpow hac i j
  have hBC : ∀ (v : B) (w : C), Commute (B.subtype v) (C.subtype w) := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    exact Commute.zpow_zpow hbc i j
  let φ₁ : A × B →* Γ := MonoidHom.noncommCoprod A.subtype B.subtype hAB
  have hφ₁C : ∀ (p : A × B) (w : C), Commute (φ₁ p) (C.subtype w) := by
    rintro ⟨u, v⟩ w
    exact (hAC u w).mul_left (hBC v w)
  let φ : (A × B) × C →* Γ := MonoidHom.noncommCoprod φ₁ C.subtype hφ₁C
  have hφ : ∀ (u : A) (v : B) (w : C), φ ((u, v), w) = u * v * w := fun u v w => rfl
  have hdecomp : ∀ x : Γ, x ^ 3 = 1 → x ≠ 1 → ∀ {y : Γ}, y ∈ Subgroup.zpowers x →
      ∀ {N : Subgroup Γ}, y ∈ N → y ≠ 1 → x ∈ N := fun x hx3 hx1 y hy N hyN hy1 =>
    burnsideA26_mem_of_pow_mem hx3 hx1 hy hy1 hyN
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨u, v⟩, w⟩ h
    rw [hφ] at h
    have hw : (w : Γ) ∈ M := by
      have : (w : Γ) = ((u : Γ) * v)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      refine M.inv_mem (M.mul_mem ?_ ?_)
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp u.2
        rw [← hi]; exact M.zpow_mem ha i
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp v.2
        rw [← hi]; exact M.zpow_mem hb i
    have hw1 : (w : Γ) = 1 := by
      by_contra hne
      exact hc (hdecomp c hc3 hc1 w.2 hw hne)
    rw [hw1, mul_one] at h
    have hu : (u : Γ) = (v : Γ)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hu1 : (u : Γ) = 1 := by
      by_contra hne
      have hvA : (b : Γ) ∈ A := by
        apply hdecomp b hb3 hb1 v.2 (N := A) _ _
        · rw [← inv_inv (v : Γ), ← hu]; exact A.inv_mem (u.2)
        · intro h1
          apply hne
          rw [hu, h1, inv_one]
      exact hb' hvA
    have hv1 : (v : Γ) = 1 := by rw [hu1] at hu; exact inv_eq_one.mp hu.symm
    refine Prod.ext (Prod.ext (Subtype.ext hu1) (Subtype.ext hv1)) (Subtype.ext hw1)
  have hcommA : ∀ u v : A, u * v = v * u := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    exact Subtype.ext (Commute.zpow_zpow_self a i j).eq
  have hcommB : ∀ u v : B, u * v = v * u := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    exact Subtype.ext (Commute.zpow_zpow_self b i j).eq
  have hcommC : ∀ u v : C, u * v = v * u := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    exact Subtype.ext (Commute.zpow_zpow_self c i j).eq
  have hcomm : ∀ x y : (A × B) × C, x * y = y * x := by
    rintro ⟨⟨u₁, v₁⟩, w₁⟩ ⟨⟨u₂, v₂⟩, w₂⟩
    exact Prod.ext (Prod.ext (hcommA u₁ u₂) (hcommB v₁ v₂)) (hcommC w₁ w₂)
  have hpowA : ∀ (x : Γ) (hx3 : x ^ 3 = 1) (u : Subgroup.zpowers x), u ^ 3 = 1 := by
    intro x hx3
    rintro ⟨_, i, rfl⟩
    exact Subtype.ext (by
      rw [Subgroup.coe_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3,
        one_zpow]
      rfl)
  have hpow : ∀ x : (A × B) × C, x ^ 3 = 1 := by
    rintro ⟨⟨u, v⟩, w⟩
    exact Prod.ext (Prod.ext (hpowA a ha3 u) (hpowA b hb3 v)) (hpowA c hc3 w)
  have hcardx : ∀ (x : Γ) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1), Nat.card (Subgroup.zpowers x) = 3 := by
    intro x hx3 hx1
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hcard : Nat.card ((A × B) × C) = 3 ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, hcardx a ha3 ha1, hcardx b hb3 hb1, hcardx c hc3 hc1]
    norm_num
  exact CFSG.SectionRank.le_pRank_of_injective (by norm_num : 1 < 3) hcomm hpow hcard φ hinj le_top

theorem burnsideA26_rank_ge_three {G : Type} [Group G] [Finite G] {L : Subgroup G} [L.Normal]
    {S : Type} [Group S] (π : ↥L →* S) (hπ : Function.Surjective π) (hK₀ : IsPGroup 2 π.ker)
    (hZ : Subgroup.center S = ⊥) (ρ : G →* MulAut S)
    (hρ : ∀ (x : G) (l : ↥L), π (MulAut.conjNormal x l) = ρ x (π l))
    (hρL : ∀ l : ↥L, ρ (l : G) = MulAut.conj (π l)) {z : G}
    (hz : IsPGroup 3 (Subgroup.zpowers z)) (hz3 : ρ z ^ 3 = 1)
    (hzin : ρ z ∉ (MulAut.conj : S →* MulAut S).range) {a b : S} (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb : b ∉ Subgroup.zpowers a)
    (hfa : ρ z a = a) (hfb : ρ z b = b) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K₀ : Subgroup G := π.ker.map L.subtype with hK₀def
  haveI : K₀.Normal := ⟨by
    rintro _ ⟨k, hk, rfl⟩ g
    refine ⟨MulAut.conjNormal g k, ?_, ?_⟩
    · show π (MulAut.conjNormal g k) = 1
      rw [hρ, MonoidHom.mem_ker.1 hk, map_one]
    · simp [MulAut.conjNormal_apply]⟩
  have hmemK₀ : ∀ l : ↥L, (l : G) ∈ K₀ ↔ π l = 1 := fun l => by
    constructor
    · rintro ⟨k, hk, hkl⟩
      have : k = l := Subtype.ext hkl
      rw [← this]
      exact MonoidHom.mem_ker.1 hk
    · intro h
      exact ⟨l, h, rfl⟩
  let ι₀ : ↥L →* G ⧸ K₀ := (QuotientGroup.mk' K₀).comp L.subtype
  have hker : π.ker ≤ ι₀.ker := fun k hk => by
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).2 ((hmemK₀ k).2 (MonoidHom.mem_ker.1 hk))
  let ι : S →* G ⧸ K₀ :=
    (QuotientGroup.lift π.ker ι₀ hker).comp
      (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.toMonoidHom
  have hι : ∀ l : ↥L, ι (π l) = QuotientGroup.mk (l : G) := fun l => by
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π l) =
        (QuotientGroup.mk l : ↥L ⧸ π.ker) :=
      ((QuotientGroup.quotientKerEquivOfSurjective π hπ).symm_apply_eq).2 rfl
    show (QuotientGroup.lift π.ker ι₀ hker)
      ((QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π l)) = _
    rw [h1]
    rfl
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro s hs
    obtain ⟨l, rfl⟩ := hπ s
    rw [hι] at hs
    exact (hmemK₀ l).1 ((QuotientGroup.eq_one_iff _).1 hs)
  have hιρ : ∀ (x : G) (s : S), ι (ρ x s) = QuotientGroup.mk x * ι s * (QuotientGroup.mk x)⁻¹ := by
    intro x s
    obtain ⟨l, rfl⟩ := hπ s
    rw [← hρ, hι, hι]
    have : ((MulAut.conjNormal x l : ↥L) : G) = x * (l : G) * x⁻¹ := MulAut.conjNormal_apply x l
    rw [this]
    simp
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℕ, orderOf z = 3 ^ a₀ := by
    obtain ⟨a₀, h⟩ := (IsPGroup.iff_orderOf.mp hz) ⟨z, Subgroup.mem_zpowers z⟩
    exact ⟨a₀, by rw [← h]; exact Subgroup.orderOf_coe ⟨z, Subgroup.mem_zpowers z⟩⟩
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hzin (by rw [map_one]; exact one_mem _)
  have ha₀pos : 1 ≤ a₀ := by
    by_contra h0
    obtain rfl : a₀ = 0 := by omega
    exact hz1 (orderOf_eq_one_iff.mp (by rw [ha₀]; rfl))
  set m : ℕ := 3 ^ (a₀ - 1) with hm
  have h3m : 3 * m = orderOf z := by
    rw [ha₀, hm, ← pow_succ']
    congr 1
    omega
  set t : G := z ^ m with ht
  have ht3 : t ^ 3 = 1 := by
    rw [ht, ← pow_mul, mul_comm, h3m]
    exact pow_orderOf_eq_one z
  have hm_lt : m < orderOf z := by
    rw [← h3m]
    have : 0 < m := by rw [hm]; positivity
    omega
  have ht1 : t ≠ 1 := pow_ne_one_of_lt_orderOf (by rw [hm]; positivity) hm_lt
  have hot : orderOf t = 3 := orderOf_eq_prime ht3 ht1
  have hρt : ρ t = ρ z ^ m := by rw [ht, map_pow]
  have htL : t ∉ L := by
    intro htL
    set tL : ↥L := ⟨t, htL⟩
    have hinn : ρ t = MulAut.conj (π tL) := hρL tL
    by_cases hr : ρ t = 1
    ·
      have h1 : π tL ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut S => φ g) (hinn.symm.trans hr)
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * π tL = (π tL * g * (π tL)⁻¹) * π tL := by rw [this]
          _ = π tL * g := by group
      rw [hZ, Subgroup.mem_bot] at h1
      have hkt : tL ∈ π.ker := h1
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hK₀) ⟨tL, hkt⟩
      have : orderOf tL = 3 := by
        rw [← Subgroup.orderOf_coe tL]
        exact hot
      have h2 : orderOf (⟨tL, hkt⟩ : π.ker) = 3 := by
        rw [← Subgroup.orderOf_coe ⟨tL, hkt⟩]
        exact this
      rw [hj] at h2
      have h3 : 3 ∣ 2 ^ j := by rw [h2]
      exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
    ·
      have hm1 : m = 1 := by
        by_contra hne
        have h3dvd : 3 ∣ m := by
          rw [hm]
          have : a₀ - 1 ≠ 0 := by
            intro h0
            apply hne
            rw [hm, h0, pow_zero]
          exact dvd_pow_self 3 this
        obtain ⟨m', hm'⟩ := h3dvd
        apply hr
        rw [hρt, hm', pow_mul, hz3, one_pow]
      rw [hm1, pow_one] at hρt
      exact hzin ⟨π tL, by rw [← hρt, hinn]⟩
  have hcommz : ∀ s : S, ρ z s = s → Commute (QuotientGroup.mk z : G ⧸ K₀) (ι s) := by
    intro s hs
    have h1 := hιρ z s
    rw [hs, eq_comm, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hmk : (QuotientGroup.mk t : G ⧸ K₀) = (QuotientGroup.mk z : G ⧸ K₀) ^ m := by
    rw [ht, QuotientGroup.mk_pow]
  have hcomma : Commute (ι a) (QuotientGroup.mk t : G ⧸ K₀) := by
    rw [hmk]
    exact ((hcommz a hfa).pow_left m).symm
  have hcommb : Commute (ι b) (QuotientGroup.mk t : G ⧸ K₀) := by
    rw [hmk]
    exact ((hcommz b hfb).pow_left m).symm
  have hcommab : Commute (ι a) (ι b) := by
    show ι a * ι b = ι b * ι a
    rw [← map_mul, ← map_mul, hab]
  have hct : (QuotientGroup.mk t : G ⧸ K₀) ∉ ι.range := by
    rintro ⟨s, hs⟩
    obtain ⟨l, rfl⟩ := hπ s
    rw [hι] at hs
    have h1 : ((l : G)⁻¹ * t) ∈ K₀ := QuotientGroup.eq.1 hs
    obtain ⟨k, -, hk⟩ := h1
    apply htL
    have : t = (l : G) * (k : G) := by
      have hk' : (k : G) = (l : G)⁻¹ * t := hk
      rw [hk']
      group
    rw [this]
    exact L.mul_mem l.2 k.2
  have hrk := burnsideA26_three_le_pRank (M := ι.range) (a := ι a) (b := ι b)
    (c := QuotientGroup.mk t) ⟨a, rfl⟩ ⟨b, rfl⟩ hct (by rw [← map_pow, ha3, map_one])
    (by rw [← map_pow, hb3, map_one]) (by rw [← QuotientGroup.mk_pow, ht3, QuotientGroup.mk_one])
    hcommab hcomma hcommb (fun h => ha1 (hιinj (h.trans (map_one ι).symm))) (by
      intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
      apply hb
      refine ⟨k, hιinj ?_⟩
      rw [← hk, map_zpow])
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardK₀ : ¬ 3 ∣ Nat.card K₀ := by
    rw [hK₀def, Subgroup.card_map_of_injective L.subtype_injective]
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hK₀
    rw [hj]
    intro h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  rw [← CFSG.SectionRank.pRank_quotient_eq K₀ hcardK₀]
  exact hrk

end RankFam

section CenterFam

open CFSG.SectionRank

theorem burnsideA26_pCore_quotient {L : Type} [Group L] [Finite L] :
    pCore 2 (L ⧸ pCore 2 L) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup L := pCore 2 L
  set M : Subgroup (L ⧸ N) := pCore 2 (L ⧸ N)
  have hMp : IsPGroup 2 (M.comap (QuotientGroup.mk' N)) := by
    refine IsPGroup.comap_of_ker_isPGroup (CFSG.pCore_isPGroup) _ ?_
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  haveI : (M.comap (QuotientGroup.mk' N)).Normal := Subgroup.Normal.comap inferInstance _
  have hle : M.comap (QuotientGroup.mk' N) ≤ N :=
    le_sSup (show M.comap (QuotientGroup.mk' N) ∈ {K : Subgroup L | K.Normal ∧ IsPGroup 2 K} from
      ⟨inferInstance, hMp⟩)
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective m
  have hl : l ∈ M.comap (QuotientGroup.mk' N) := hm
  exact (QuotientGroup.eq_one_iff l).2 (hle hl)

open CFSG.Blueprint in
theorem burnsideA26_center_bar
    {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple (L ⧸ pCore 2 L)) {n : ℕ}
    (hS : ChevalleyExceptionalModel ((L ⧸ pCore 2 L) ⧸ Subgroup.center (L ⧸ pCore 2 L))
      .trialityD4 2 n) : Subgroup.center (L ⧸ pCore 2 L) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := L ⧸ pCore 2 L
  haveI : Group.IsPerfect Q := hq.1
  have hodd : Odd (Nat.card (Subgroup.center Q)) := by
    by_contra hne
    have h2 : 2 ∣ Nat.card (Subgroup.center Q) := by
      rw [Nat.not_odd_iff_even] at hne
      exact even_iff_two_dvd.1 hne
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hcQ : orderOf (c : Q) = 2 := (Subgroup.orderOf_coe c).trans hc
    set H : Subgroup Q := Subgroup.zpowers (c : Q) with hH
    have hHp : IsPGroup 2 H := IsPGroup.of_card (n := 1) (by
      rw [hH, Nat.card_zpowers, hcQ]; rfl)
    have hHn : H.Normal := ⟨by
      intro n hn g
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      have hcj : (c : Q) ^ j ∈ Subgroup.center Q := Subgroup.zpow_mem _ c.2 j
      rw [Subgroup.mem_center_iff.1 hcj g, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j⟩
    have hle : H ≤ pCore 2 Q := le_sSup ⟨hHn, hHp⟩
    rw [burnsideA26_pCore_quotient] at hle
    have : (c : Q) ∈ (⊥ : Subgroup Q) := hle (Subgroup.mem_zpowers _)
    rw [Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hcQ
    exact absurd hcQ (by norm_num)
  have hker : (QuotientGroup.mk' (Subgroup.center Q)).ker = Subgroup.center Q :=
    QuotientGroup.ker_mk' _
  have := triality_even_perfect_odd_cover_trivial hS (QuotientGroup.mk' (Subgroup.center Q))
    (QuotientGroup.mk'_surjective _) (by rw [hker]) (by rw [hker]; exact hodd)
  rw [hker] at this
  exact this

end CenterFam

section G2E9Fam

open CFSG.Blueprint.Chevalley
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof

theorem burnsideA26_g2_E9
    {k : Type} [Field k] [Finite k] [CharP k 2] :
    ∃ y₁ y₂ : adjointGroup Tag.G2 k, y₁ ^ 3 = 1 ∧ y₂ ^ 3 = 1 ∧ y₁ * y₂ = y₂ * y₁ ∧ y₁ ≠ 1 ∧
      y₂ ∉ Subgroup.zpowers y₁ := by
  obtain ⟨eM⟩ := nonempty_mulEquiv_g2LongSL2 (K := k)
  obtain ⟨eS⟩ := nonempty_mulEquiv_g2ShortSL2 (K := k)
  have hM3 := CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.sl2Three_pow_three k
  have hM1 : CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.sl2Three k ≠ 1 := by
    intro h
    apply CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.sl2Three_ne_smul (k := k) 1
    rw [h, one_smul]
    rfl
  set y₁ : adjointGroup .G2 k :=
    ((eM (CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.sl2Three _) : g2LongSL2 k) :
      adjointGroup .G2 k) with hy₁
  set y₂ : adjointGroup .G2 k :=
    ((eS (CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.sl2Three _) : g2ShortSL2 k) :
      adjointGroup .G2 k) with hy₂
  have hy₁M : y₁ ∈ g2LongSL2 k := (eM _).2
  have hy₂S : y₂ ∈ g2ShortSL2 k := (eS _).2
  have hy₁3 : y₁ ^ 3 = 1 := by
    rw [hy₁, ← Subgroup.coe_pow, ← map_pow, hM3, map_one, Subgroup.coe_one]
  have hy₂3 : y₂ ^ 3 = 1 := by
    rw [hy₂, ← Subgroup.coe_pow, ← map_pow, hM3, map_one, Subgroup.coe_one]
  have hy₁1 : y₁ ≠ 1 := by
    intro h
    apply hM1
    apply eM.injective
    rw [map_one]
    exact Subtype.ext h
  have hy₂1 : y₂ ≠ 1 := by
    intro h
    apply hM1
    apply eS.injective
    rw [map_one]
    exact Subtype.ext h
  have hy₁₂ : y₁ * y₂ = y₂ * y₁ := (g2Short_commute_g2Long hy₂S hy₁M).symm
  have hy₂₁ : y₂ ∉ Subgroup.zpowers y₁ := by
    intro h
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
    have hy₂M : y₂ ∈ g2LongSL2 k := hj ▸ zpow_mem hy₁M j
    exact hy₂1 (CFSG.RankThree.PartTwo.Sec8.Item83Proof.eq_one_of_mem_g2LongSL2_of_mem_g2ShortSL2
      hy₂M hy₂S)
  exact ⟨y₁, y₂, hy₁3, hy₂3, hy₁₂, hy₁1, hy₂₁⟩

end G2E9Fam

section ExistsZFam

theorem burnsideA26_order_three_eq {A : Type} [Group A] [Finite A] [IsCyclic A] {σ τ : A}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) : τ = σ ∨ τ = σ⁻¹ := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := IsCyclic.card_pow_eq_one_le (α := A) (n := 3) (by norm_num)
  have hσinv1 : σ⁻¹ ≠ 1 := fun h => hσ1 (inv_eq_one.mp h)
  have hne : σ ≠ σ⁻¹ := by
    intro h
    have h2 : σ ^ 2 = 1 := by
      calc σ ^ 2 = σ * σ := by rw [sq]
        _ = σ * σ⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel σ
    apply hσ1
    calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hσ3, h2]; simp
  have hsub : ({1, σ, σ⁻¹} : Finset A) ⊆ Finset.univ.filter (fun a : A => a ^ 3 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 3
    · exact hσ3
    · rw [inv_pow, hσ3, inv_one]
  have hcard3 : ({1, σ, σ⁻¹} : Finset A).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hne
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hσ1.symm, hσinv1.symm⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hτmem : τ ∈ Finset.univ.filter (fun a : A => a ^ 3 = 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hτ3
  rw [← heq] at hτmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hτmem
  rcases hτmem with h | h | h
  · exact absurd h hτ1
  · exact Or.inl h
  · exact Or.inr h

theorem burnsideA26_exists_z {G : Type} [Group G] [Finite G] {C : Type} [Group C] {A : Type}
    [Group A] [Finite A] [IsCyclic A] (F : A →* MulAut C) (Θ : MulAut C →* A)
    (hNF : ∀ m : MulAut C, ∃ g : C, m = MulAut.conj g * F (Θ m)) (ρ' : G →* MulAut C)
    (hinn : ∀ c : C, ∃ y : G, ρ' y = MulAut.conj c) {σ : A} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    {x : G} (h3 : 3 ∣ orderOf (Θ (ρ' x))) :
    ∃ (z : G) (σ₁ : A), IsPGroup 3 (Subgroup.zpowers z) ∧ (σ₁ = σ ∨ σ₁ = σ⁻¹) ∧
      ρ' z = F σ₁ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set d : G →* A := Θ.comp ρ'
  have hdx : d x = Θ (ρ' x) := rfl
  have hpos : 0 < orderOf (d x) := orderOf_pos _
  rw [← hdx] at h3
  set y₀ : G := x ^ (orderOf (d x) / 3) with hy₀
  have hs₁ : orderOf (d y₀) = 3 := by
    rw [hy₀, map_pow]
    exact orderOf_pow_orderOf_div hpos.ne' h3
  set s₁ : A := d y₀
  have hs₁3 : s₁ ^ 3 = 1 := by rw [← hs₁]; exact pow_orderOf_eq_one _
  have hs₁1 : s₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs₁
    omega
  have hs : s₁ = σ ∨ s₁ = σ⁻¹ := burnsideA26_order_three_eq hσ3 hσ1 hs₁3 hs₁1
  obtain ⟨g₀, hg₀⟩ := hNF (ρ' y₀)
  have hΘy₀ : Θ (ρ' y₀) = s₁ := rfl
  rw [hΘy₀] at hg₀
  obtain ⟨y', hy'⟩ := hinn ((F s₁).symm g₀⁻¹)
  have hρ₁ : ρ' (y₀ * y') = F s₁ := by
    rw [map_mul, hg₀, hy']
    have hcomm : F s₁ * MulAut.conj ((F s₁).symm g₀⁻¹) * (F s₁)⁻¹ =
        MulAut.conj (F s₁ ((F s₁).symm g₀⁻¹)) :=
      CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv (F s₁) _
    rw [MulEquiv.apply_symm_apply] at hcomm
    calc MulAut.conj g₀ * F s₁ * MulAut.conj ((F s₁).symm g₀⁻¹) =
        MulAut.conj g₀ * (F s₁ * MulAut.conj ((F s₁).symm g₀⁻¹) * (F s₁)⁻¹) * F s₁ := by group
      _ = MulAut.conj g₀ * MulAut.conj g₀⁻¹ * F s₁ := by rw [hcomm]
      _ = F s₁ := by rw [← map_mul, mul_inv_cancel, map_one, one_mul]
  set y₁ : G := y₀ * y'
  obtain ⟨a, m, hm3, hN⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y₁).ne' 3 (by norm_num)
  have hm1 : (m * m) % 3 = 1 := by
    have h1 : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> simp [Nat.mul_mod, h1]
  refine ⟨y₁ ^ (m * m), s₁, ?_, hs, ?_⟩
  · refine IsPGroup.of_card_dvd_pow (n := a) ?_
    rw [Nat.card_zpowers]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← pow_mul, show m * m * 3 ^ a = orderOf y₁ * m by rw [hN]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]
  · rw [map_pow, hρ₁, ← map_pow]
    congr 1
    rw [← Nat.mod_add_div (m * m) 3, hm1, pow_add, pow_mul, hs₁3, one_pow, mul_one, pow_one]

end ExistsZFam

section L2Fam

open CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem burnsideA26_l2 {S : Type} [Group S] {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (e : S ≃* StatedProj (StatedSL 2 K)) (θ : MulAut S) :
    ChA.IsInnDiagFieldAut S θ := by
  haveI : CharP K 2 := burnsideA26_charP_two hK
  let Φ := projectiveSpecialLinearGroupEquivStatedProj 2 K
  obtain ⟨g, σ, hgσ⟩ := CFSG.RankThree.PartTwo.KFacts.exists_pglAction_mul_psl2FieldAut
    (MulAut.congr (e.trans Φ.symm) θ)
  obtain ⟨x, hx⟩ := CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.toPGL_surjective K g
  have hθ : θ = MulAut.congr (e.trans Φ.symm).symm (pglAction K g) *
      MulAut.congr (e.trans Φ.symm).symm (psl2FieldAut K σ) := by
    rw [← map_mul, ← hgσ, burnsideA26_congr_symm_congr]
  refine ⟨MulAut.congr (e.trans Φ.symm).symm (pglAction K g),
    MulAut.congr (e.trans Φ.symm).symm (psl2FieldAut K σ), Or.inl ?_, ?_, hθ⟩
  · refine (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr _ _).2 ?_
    rw [← hx, pglAction_toPGL]
    exact CFSG.RankThree.PartTwo.KFacts.isInnerAut_conj x
  · refine Or.inl ⟨n, K, inferInstance, inferInstance, e, σ, hK, fun g' => ?_⟩
    obtain ⟨u, hu⟩ := (specialLinearGroupEquivStatedSL 2 K).surjective g'
    refine ⟨specialLinearGroupEquivStatedSL 2 K (Matrix.SpecialLinearGroup.map (σ : K →+* K) u),
      ?_, ?_⟩
    · rw [← hu]
      apply Units.ext
      rfl
    · rw [burnsideA26_congr_trans_apply, ← hu]
      have h1 : Φ.symm (QuotientGroup.mk (specialLinearGroupEquivStatedSL 2 K u) :
          StatedProj (StatedSL 2 K)) = QuotientGroup.mk' (Subgroup.center _) u := by
        apply Φ.injective
        rw [Φ.apply_symm_apply]
        rfl
      show Φ (psl2FieldAut K σ (Φ.symm (QuotientGroup.mk (specialLinearGroupEquivStatedSL 2 K u) :
          StatedProj (StatedSL 2 K)))) = _
      rw [h1, psl2FieldAut_apply, psl2RingEquiv_mk]
      rfl

end L2Fam

section D4AbsFam

open CFSG.RankThree.PartTwo.KFacts

theorem burnsideA26_3d4_abs {G : Type} [Group G] [Finite G]
    (hSQT3 : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 2) (L : Subgroup G) [L.Normal]
    (hcenter : Subgroup.center (↥L ⧸ pCore 2 ↥L) = ⊥) {M : Type} [Group M] (H C : Subgroup M)
    (hHC : ⁅H, H⁆ = C) (hZC : Subgroup.center ↥C = ⊥)
    (e : ((↥L ⧸ pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ pCore 2 ↥L)) ≃*
      CFSG.Blueprint.DerivedCentralQuotient H)
    {A : Type} [Group A] [Finite A] [IsCyclic A] (F : A →* MulAut ↥C) (Θ : MulAut ↥C →* A)
    (hΘF : ∀ δ, Θ (F δ) = δ) (hΘker : Θ.ker = (MulAut.conj : ↥C →* MulAut ↥C).range)
    (hNF : ∀ m : MulAut ↥C, ∃ g : ↥C, m = MulAut.conj g * F (Θ m)) {σ : A} (hσ3 : σ ^ 3 = 1)
    (hσ1 : σ ≠ 1) {P : Type} [Group P] (ι : P →* ↥C) (hι : Function.Injective ι)
    (hιfix : ∀ p : P, F σ (ι p) = ι p) {y₁ y₂ : P} (hy₁3 : y₁ ^ 3 = 1) (hy₂3 : y₂ ^ 3 = 1)
    (hy₁₂ : y₁ * y₂ = y₂ * y₁) (hy₁1 : y₁ ≠ 1) (hy₂ : y₂ ∉ Subgroup.zpowers y₁) (x : G) :
    Nat.Coprime (orderOf (Θ (MulAut.congr
      (e.trans (burnsideA26_dcqEquiv H C hHC hZC)) (burnsideA26_indAut L x)))) 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hnc
  have h3 : 3 ∣ orderOf (Θ (MulAut.congr
      (e.trans (burnsideA26_dcqEquiv H C hHC hZC)) (burnsideA26_indAut L x))) := by
    by_contra hnd
    exact hnc ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd).symm
  let κ := burnsideA26_dcqEquiv H C hHC hZC
  let ε := e.trans κ
  let ρ := burnsideA26_indAut L
  let ρ' : G →* MulAut ↥C := (MulAut.congr ε).toMonoidHom.comp ρ
  let π : ↥L →* ((↥L ⧸ pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ pCore 2 ↥L)) :=
    (QuotientGroup.mk' (Subgroup.center (↥L ⧸ pCore 2 ↥L))).comp
      (QuotientGroup.mk' (pCore 2 ↥L))
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = pCore 2 ↥L := by
    ext l
    constructor
    · intro h
      have h1 : (QuotientGroup.mk' (pCore 2 ↥L) l) ∈ Subgroup.center (↥L ⧸ pCore 2 ↥L) :=
        (QuotientGroup.eq_one_iff _).1 h
      rw [hcenter, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff _).1 h1
    · intro h
      have h1 : (QuotientGroup.mk' (pCore 2 ↥L) l) = 1 := (QuotientGroup.eq_one_iff _).2 h
      show QuotientGroup.mk' (Subgroup.center (↥L ⧸ pCore 2 ↥L))
        (QuotientGroup.mk' (pCore 2 ↥L) l) = 1
      rw [h1, map_one]
  have hK₀ : IsPGroup 2 π.ker := by
    rw [hπker]
    exact CFSG.pCore_isPGroup
  have hZ : Subgroup.center ((↥L ⧸ pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ pCore 2 ↥L)) = ⊥ :=
    CFSG.SectionRank.center_eq_bot_of_mulEquiv' ε.symm hZC
  have hρ : ∀ (x : G) (l : ↥L), π (MulAut.conjNormal x l) = ρ x (π l) := fun x l =>
    (burnsideA26_indAut_apply L x l).symm
  have hρL : ∀ l : ↥L, ρ (l : G) = MulAut.conj (π l) := by
    intro l
    ext s
    obtain ⟨l', rfl⟩ := hπ s
    have hc : MulAut.conjNormal (l : G) l' = l * l' * l⁻¹ :=
      Subtype.ext (by simp [MulAut.conjNormal_apply])
    calc ρ (l : G) (π l') = π (MulAut.conjNormal (l : G) l') := (hρ _ _).symm
      _ = π (l * l' * l⁻¹) := by rw [hc]
      _ = (MulAut.conj (π l)) (π l') := by
        rw [map_mul, map_mul, map_inv, MulAut.conj_apply]
  have hinn : ∀ c : ↥C, ∃ y : G, ρ' y = MulAut.conj c := by
    intro c
    obtain ⟨l, hl⟩ := hπ (ε.symm c)
    refine ⟨l, ?_⟩
    show MulAut.congr ε (ρ (l : G)) = _
    rw [hρL, hl, congr_mulAutConj, MulEquiv.apply_symm_apply]
  have h3' : 3 ∣ orderOf (Θ (ρ' x)) := h3
  obtain ⟨z, σ₁, hzp, hσ₁, hρz⟩ := burnsideA26_exists_z F Θ hNF ρ' hinn hσ3 hσ1 h3'
  have hσ₁3 : σ₁ ^ 3 = 1 := by
    rcases hσ₁ with rfl | rfl
    · exact hσ3
    · rw [inv_pow, hσ3, inv_one]
  have hσ₁1 : σ₁ ≠ 1 := by
    rcases hσ₁ with rfl | rfl
    · exact hσ1
    · exact fun h => hσ1 (inv_eq_one.mp h)
  have hz3 : ρ z ^ 3 = 1 := by
    apply (MulAut.congr ε).injective
    rw [map_pow, map_one]
    show (ρ' z) ^ 3 = 1
    rw [hρz, ← map_pow, hσ₁3, map_one]
  have hzin : ρ z ∉ (MulAut.conj : _ →* MulAut ((↥L ⧸ pCore 2 ↥L) ⧸
      Subgroup.center (↥L ⧸ pCore 2 ↥L))).range := by
    rintro ⟨s, hs⟩
    have h1 : F σ₁ = MulAut.conj (ε s) := by
      rw [← hρz]
      show MulAut.congr ε (ρ z) = _
      rw [← hs, congr_mulAutConj]
    have h2 : F σ₁ ∈ Θ.ker := by
      rw [hΘker]
      exact ⟨ε s, h1.symm⟩
    rw [MonoidHom.mem_ker, hΘF] at h2
    exact hσ₁1 h2
  have hfix : ∀ p : P, F σ₁ (ι p) = ι p := by
    intro p
    rcases hσ₁ with rfl | rfl
    · exact hιfix p
    · rw [map_inv, MulAut.inv_def, MulEquiv.symm_apply_eq]
      exact (hιfix p).symm
  have hkey : ∀ s, ε (ρ z s) = F σ₁ (ε s) := by
    intro s
    rw [← hρz]
    show ε (ρ z s) = (MulAut.congr ε (ρ z)) (ε s)
    simp [MulAut.congr_apply]
  have hrk := burnsideA26_rank_ge_three π hπ hK₀ hZ ρ hρ hρL hzp hz3 hzin
    (a := ε.symm (ι y₁)) (b := ε.symm (ι y₂))
    (by rw [← map_pow, ← map_pow, hy₁3, map_one, map_one])
    (by rw [← map_pow, ← map_pow, hy₂3, map_one, map_one])
    (by simp only [← map_mul, hy₁₂])
    (by
      intro h
      apply hy₁1
      apply hι
      rw [map_one]
      have := ε.symm.injective (h.trans (map_one ε.symm).symm)
      exact this)
    (by
      intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
      apply hy₂
      refine ⟨k, hι ?_⟩
      have := congrArg ε hk
      rw [map_zpow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
      rw [map_zpow]
      exact this)
    (by
      apply ε.injective
      rw [hkey, MulEquiv.apply_symm_apply, hfix])
    (by
      apply ε.injective
      rw [hkey, MulEquiv.apply_symm_apply, hfix])
  omega

end D4AbsFam

section D4Fam

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.KFacts

theorem burnsideA26_3d4
    {G : Type} [Group G] [Finite G] (hSQT3 : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 2)
    (L : Subgroup G) [L.Normal] (hq : CFSG.IsQuasisimple (↥L ⧸ pCore 2 ↥L)) {n : ℕ}
    (hS : ChevalleyExceptionalModel
      ((↥L ⧸ pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ pCore 2 ↥L)) .trialityD4 2 n) (x : G) :
    ChA.IsInnDiagFieldAut ((↥L ⧸ pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ pCore 2 ↥L))
      (burnsideA26_indAut L x) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcenter : Subgroup.center (↥L ⧸ pCore 2 ↥L) = ⊥ := burnsideA26_center_bar hq hS
  obtain ⟨hadm, K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := id hS
  have hf : 1 ≤ n := hadm.2.1
  have hK : Nat.card K = (2 ^ n) ^ 3 := hcard
  obtain ⟨σ', hσ', hσ'ord, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf K hK
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  haveI : CharP K 2 := burnsideA26_charP_two (n := 3 * n) (by rw [hK, ← pow_mul, mul_comm])
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨hactEq, hNF, ⟨Θ, hΘ, -, hΘker, -⟩, hcyc, hcardAut, hHC, hZC, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ' hσ'
  haveI : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  haveI : IsCyclic (K ≃+* K) := hcyc
  have hσ'3 : σ' ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one σ'
    rwa [hσ'ord] at h1
  have hσ'1 : σ' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ'ord
    exact absurd hσ'ord (by decide)
  have hΘF : ∀ δ : K ≃+* K, Θ (fieldActorHom (t := TwistTag.D4) σ' δ) = δ := fun δ =>
    hΘ _ 1 δ (by rw [map_one, one_mul]; rfl)
  have hNF' : ∀ m : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ'.toRingHom),
      ∃ g, m = MulAut.conj g * fieldActorHom (t := TwistTag.D4) σ' (Θ m) := by
    intro m
    obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF m
    refine ⟨g, ?_⟩
    rw [hΘ m g δ hgδ]
    exact hgδ
  haveI : CharP (fixSubfield σ') 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2
    (by exact_mod_cast two_eq_zero_fixSubfield σ' hK2)
  haveI : Finite (fixSubfield σ') := Subtype.finite
  obtain ⟨y₁, y₂, hy₁3, hy₂3, hy₁₂, hy₁1, hy₂⟩ := burnsideA26_g2_E9 (k := fixSubfield σ')
  have hcop := fun x' : G => burnsideA26_3d4_abs hSQT3 L hcenter
    (twistedFixedGroup TwistTag.D4 K σ'.toRingHom)
    (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) hHC hZC e
    (fieldActorHom (t := TwistTag.D4) σ') Θ hΘF hΘker hNF' hσ'3 hσ'1
    (trialityG2Incl σ' hK2) (trialityG2Incl_injective σ' hK2)
    (fun p => (mem_range_trialityG2Incl_iff σ' hK2 _).1 ⟨p, rfl⟩) hy₁3 hy₂3 hy₁₂ hy₁1 hy₂ x'
  obtain ⟨g, hg⟩ := hNF' (MulAut.congr (e.trans (burnsideA26_dcqEquiv
    (twistedFixedGroup TwistTag.D4 K σ'.toRingHom) (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom)
    hHC hZC)) (burnsideA26_indAut L x))
  obtain ⟨ψ₁, ψ₂, hin, hθ, hfield⟩ := burnsideA26_dcq'
    (twistedFixedGroup TwistTag.D4 K σ'.toRingHom)
    (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) hHC hZC e (burnsideA26_indAut L x)
    (fieldActorHom (t := TwistTag.D4) σ') (fun δ g => Units.map (entrywiseHom δ.toRingHom) g)
    (fun δ g => hactEq δ g) g _ hg
  exact ⟨ψ₁, ψ₂, Or.inl hin, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨n, K, inferInstance, inferInstance, σ'.toRingHom, e, _, hK, hσ, hcop x, hfield⟩)))))), hθ⟩

end D4Fam

section LnFam

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] noncomputable def burnsideA26_statedToProjSL (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL n K) ≃* projectiveSL n K :=
  (projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)

theorem burnsideA26_statedToProjSL_mk (n : ℕ) (K : Type) [Field K]
    (u : Matrix.SpecialLinearGroup (Fin n) K) :
    burnsideA26_statedToProjSL n K
        (QuotientGroup.mk (specialLinearGroupEquivStatedSL n K u) : StatedProj (StatedSL n K)) =
      LinearFlag.proj n K u := by
  have h1 : (projectiveSpecialLinearGroupEquivStatedProj n K).symm
      (QuotientGroup.mk (specialLinearGroupEquivStatedSL n K u) : StatedProj (StatedSL n K)) =
      QuotientGroup.mk' (Subgroup.center _) u := by
    apply (projectiveSpecialLinearGroupEquivStatedProj n K).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  show LinearCover.projectiveSpecialLinearEquivProjectiveSL n K
    ((projectiveSpecialLinearGroupEquivStatedProj n K).symm
      (QuotientGroup.mk (specialLinearGroupEquivStatedSL n K u) : StatedProj (StatedSL n K))) = _
  rw [h1]
  exact QuotientGroup.quotientMulEquivOfEq_mk _ u

theorem burnsideA26_statedToProjSL_symm_proj (n : ℕ) (K : Type) [Field K]
    (u : Matrix.SpecialLinearGroup (Fin n) K) :
    (burnsideA26_statedToProjSL n K).symm (LinearFlag.proj n K u) =
      (QuotientGroup.mk (specialLinearGroupEquivStatedSL n K u) : StatedProj (StatedSL n K)) :=
  (burnsideA26_statedToProjSL n K).symm_apply_eq.2 (burnsideA26_statedToProjSL_mk n K u).symm

theorem burnsideA26_isProjConjAut {n : ℕ} {S : Type} [Group S] {K : Type} [Field K]
    (e : S ≃* StatedProj (StatedSL n K)) (A : GL (Fin n) K) :
    ChA.IsProjConjAut (StatedSL n K) A
      (MulAut.congr e (MulAut.congr (e.trans (burnsideA26_statedToProjSL n K)).symm
        (LinearFlag.conjAut n K A))) := by
  intro g
  obtain ⟨u, hu⟩ := (specialLinearGroupEquivStatedSL n K).surjective g
  refine ⟨specialLinearGroupEquivStatedSL n K
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A u), ?_, ?_⟩
  · rw [← hu]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact coe_slConjugation A u
  · rw [burnsideA26_congr_trans_apply, ← hu, burnsideA26_statedToProjSL_mk, conjAut_proj,
      burnsideA26_statedToProjSL_symm_proj]

theorem burnsideA26_isProjFieldAut {n : ℕ} {S : Type} [Group S] {K : Type} [Field K]
    (e : S ≃* StatedProj (StatedSL n K)) (σ : K ≃+* K) :
    ChA.IsProjFieldAut (StatedSL n K) σ
      (MulAut.congr e (MulAut.congr (e.trans (burnsideA26_statedToProjSL n K)).symm
        (fieldAut n K σ))) := by
  intro g
  obtain ⟨u, hu⟩ := (specialLinearGroupEquivStatedSL n K).surjective g
  refine ⟨specialLinearGroupEquivStatedSL n K (Matrix.SpecialLinearGroup.map σ.toRingHom u),
    ?_, ?_⟩
  · rw [← hu]
    apply Units.ext
    rfl
  · rw [burnsideA26_congr_trans_apply, ← hu, burnsideA26_statedToProjSL_mk, fieldAut_proj,
      burnsideA26_statedToProjSL_symm_proj]

theorem burnsideA26_ln_odd {n : ℕ} (hn : 3 ≤ n) {S : Type} [Group S] {K : Type} [Field K]
    [Finite K] (e : S ≃* StatedProj (StatedSL n K)) (θ : MulAut S) (hθ : Odd (orderOf θ)) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K),
      MulAut.congr (e.trans (burnsideA26_statedToProjSL n K)) θ =
        conjAut n K A * fieldAut n K σ := by
  obtain ⟨hR, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have hE : (semilinearAutGroup n K).index ≤ 2 := by
    rw [hR] at hidx
    have h2 : (semilinearAutGroup n K).relIndex ⊤ ≤ 2 := hidx
    rwa [Subgroup.relIndex_top_right] at h2
  have hodd : Odd (orderOf (MulAut.congr (e.trans (burnsideA26_statedToProjSL n K)) θ)) := by
    rwa [MulEquiv.orderOf_eq]
  exact mem_semilinearAutGroup_iff.1 (burnsideA26_mem_of_index_le_two _ hE hodd)

theorem burnsideA26_l3 {S : Type} [Group S] {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (e : S ≃* StatedProj (StatedSL 3 K)) (θ : MulAut S)
    (hθ : Odd (orderOf θ)) : ChA.IsInnDiagFieldAut S θ := by
  obtain ⟨A, σ, h⟩ := burnsideA26_ln_odd (by norm_num : 3 ≤ 3) e θ hθ
  have hθ' : θ = MulAut.congr (e.trans (burnsideA26_statedToProjSL 3 K)).symm (conjAut 3 K A) *
      MulAut.congr (e.trans (burnsideA26_statedToProjSL 3 K)).symm (fieldAut 3 K σ) := by
    rw [← map_mul, ← h, burnsideA26_congr_symm_congr]
  exact ⟨_, _, Or.inr (Or.inl ⟨n, K, inferInstance, inferInstance, e, A, hK,
    burnsideA26_isProjConjAut e A⟩), Or.inr (Or.inl ⟨n, K, inferInstance, inferInstance, e, σ, hK,
    burnsideA26_isProjFieldAut e σ⟩), hθ'⟩

theorem burnsideA26_small {S : Type} [Group S] (θ : MulAut S)
    (hin : (MulAut.conj : S →* MulAut S).range.carrier θ)
    (hS : StatedClassicalModel S .PSL 4 2 1 ∨ StatedClassicalModel S .PSL 5 2 1 ∨
      CFSG.Blueprint.ReeTitsModel S .Tits 2 1 ∨ Nonempty (S ≃* alternatingGroup (Fin 6)) ∨
      StatedClassicalModel S .PSU 3 3 1) : ChA.IsInnDiagFieldAut S θ :=
  ⟨θ, 1, Or.inl hin, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨rfl, hS⟩))))))), (mul_one θ).symm⟩

theorem burnsideA26_l45 {m : ℕ} (hm : 3 ≤ m) {S : Type} [Group S] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (e : S ≃* StatedProj (StatedSL m K)) (θ : MulAut S)
    (hθ : Odd (orderOf θ)) : (MulAut.conj : S →* MulAut S).range.carrier θ := by
  obtain ⟨A, σ, h⟩ := burnsideA26_ln_odd hm e θ hθ
  have hK01 : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : K)).1 hK
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr ((huniq x hx).trans (huniq 1 one_ne_zero).symm)
  have hσ : σ = 1 := by
    refine RingEquiv.ext fun x => ?_
    rcases hK01 x with rfl | rfl <;> simp
  have hdet : Matrix.GeneralLinearGroup.det A = 1 := by
    apply Units.ext
    rcases hK01 ((Matrix.GeneralLinearGroup.det A : Kˣ) : K) with h0 | h1
    · exact absurd h0 (Units.ne_zero _)
    · exact h1
  obtain ⟨g, hg⟩ : A ∈ (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin m) K →*
      GL (Fin m) K).range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet
  have hin : CFSG.RankThree.PartTwo.KFacts.IsInnerAut (MulAut.congr (e.trans
      (burnsideA26_statedToProjSL m K)) θ) := by
    rw [h, hσ, map_one, mul_one, ← hg, conjAut_toGL]
    exact CFSG.RankThree.PartTwo.KFacts.isInnerAut_conj _
  have := (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr (e.trans
    (burnsideA26_statedToProjSL m K)) θ).1 hin
  exact this

end LnFam

section U3Fam

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

theorem burnsideA26_psuPow {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (A : unitaryIsom3 h) (σ : K ≃+* K) (k : ℕ) :
    ∃ N : unitaryIsom3 h, (psuConj h A * psuField h σ) ^ k =
      psuConj h N * psuField h (σ ^ k) := by
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N * ⟨glAut (σ ^ k) A, glAut_mem_unitaryIsom3 (σ ^ k) A.2⟩, ?_⟩
    rw [pow_succ, hN, pow_succ, map_mul, map_mul, ← psuField_mul_psuConj_mul_inv]
    group

theorem burnsideA26_u3_odd {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) {S : Type} [Group S] (e : S ≃* unitaryPSU h 3) (θ : MulAut S)
    (hθ : Odd (orderOf θ)) :
    ∃ (A : unitaryIsom3 h) (σ : K ≃+* K), MulAut.congr e θ = psuConj h A * psuField h σ ∧
      Odd (orderOf σ) := by
  obtain ⟨A, σ, hAσ⟩ := exists_psuConj_mul_psuField hq (MulAut.congr e θ)
  refine ⟨A, σ, hAσ, ?_⟩
  have h1 : (psuConj h A * psuField h σ) ^ orderOf θ = 1 := by
    rw [← hAσ, ← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨N, hN⟩ := burnsideA26_psuPow h A σ (orderOf θ)
  rw [hN] at h1
  have h2 := (eq_one_of_psuConj_mul_psuField_eq_one N (σ ^ orderOf θ) h1).1
  exact hθ.of_dvd_nat (orderOf_dvd_of_pow_eq_one h2)

theorem burnsideA26_isProjConjAut_u3 {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {S : Type} [Group S] (e : S ≃* StatedProj (StatedSU 3 (p ^ f) K)) (A : unitaryIsom3 h) :
    ChA.IsProjConjAut (StatedSU 3 (p ^ f) K) (A : GL (Fin 3) K)
      (MulAut.congr e (MulAut.congr (e.trans (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm).symm
        (psuConj h A))) := by
  intro g
  refine ⟨suConj h A g, rfl, ?_⟩
  rw [burnsideA26_congr_trans_apply]
  have h1 : (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm.symm
      (psuConj h A ((unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm (QuotientGroup.mk g))) =
      QuotientGroup.mk (suConj h A g) := by
    have e1 : (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm
        (QuotientGroup.mk g : StatedProj (StatedSU 3 (p ^ f) K)) = unitaryProj h 3 g := by
      apply (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).injective
      rw [MulEquiv.apply_symm_apply, unitaryPSUEquiv_unitaryProj]
    rw [e1]
    show unitaryPSUEquiv h (by norm_num : 1 ≤ 3) (unitaryProj h 3 (suConj h A g)) = _
    exact unitaryPSUEquiv_unitaryProj h _ _
  exact h1

theorem burnsideA26_isProjFieldAut_u3 {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {S : Type} [Group S] (e : S ≃* StatedProj (StatedSU 3 (p ^ f) K)) (σ : K ≃+* K) :
    ChA.IsProjFieldAut (StatedSU 3 (p ^ f) K) σ
      (MulAut.congr e (MulAut.congr (e.trans (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm).symm
        (psuField h σ))) := by
  intro g
  refine ⟨suField h σ g, rfl, ?_⟩
  rw [burnsideA26_congr_trans_apply]
  have e1 : (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm
      (QuotientGroup.mk g : StatedProj (StatedSU 3 (p ^ f) K)) = unitaryProj h 3 g := by
    apply (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).injective
    rw [MulEquiv.apply_symm_apply, unitaryPSUEquiv_unitaryProj]
  show (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm.symm
    (psuField h σ ((unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm (QuotientGroup.mk g))) = _
  rw [e1]
  show unitaryPSUEquiv h (by norm_num : 1 ≤ 3) (unitaryProj h 3 (suField h σ g)) = _
  exact unitaryPSUEquiv_unitaryProj h _ _

theorem burnsideA26_u3 {S : Type} [Group S] {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (e : S ≃* StatedProj (StatedSU 3 (2 ^ n) K)) (θ : MulAut S)
    (hθ : Odd (orderOf θ)) : ChA.IsInnDiagFieldAut S θ := by
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : 2 < 2 ^ n := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨A, σ, hAσ, hodd⟩ := burnsideA26_u3_odd h hq
    (e.trans (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm) θ hθ
  have hθ' : θ = MulAut.congr (e.trans (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm).symm
      (psuConj h A) * MulAut.congr
      (e.trans (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm).symm (psuField h σ) := by
    rw [← map_mul, ← hAσ, burnsideA26_congr_symm_congr]
  exact ⟨_, _, Or.inr (Or.inr ⟨n, K, inferInstance, inferInstance, e, (A : GL (Fin 3) K), hK,
    burnsideA26_isProjConjAut_u3 h e A⟩), Or.inr (Or.inr (Or.inl ⟨n, K, inferInstance,
    inferInstance, e, σ, hK, hodd, burnsideA26_isProjFieldAut_u3 h e σ⟩)), hθ'⟩

theorem burnsideA26_u33 {S : Type} [Group S] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (3 ^ 1) ^ 2) (e : S ≃* StatedProj (StatedSU 3 (3 ^ 1) K)) (θ : MulAut S)
    (hθ : Odd (orderOf θ)) : (MulAut.conj : S →* MulAut S).range.carrier θ := by
  have h : UnitaryFieldData 3 1 K := ⟨Nat.prime_three, le_rfl, by rw [hK]; norm_num⟩
  have hq : 2 < 3 ^ 1 := by norm_num
  obtain ⟨A, σ, hAσ, hodd⟩ := burnsideA26_u3_odd h hq
    (e.trans (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm) θ hθ
  have hK9 : Nat.card K = 3 ^ 2 := by rw [hK]; norm_num
  have hcard := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_three K
    hK9).1
  have hσ2 : σ ^ 2 = 1 := by
    have := pow_card_eq_one' (G := RingAut K) (x := σ)
    rwa [hcard] at this
  have hσ : σ = 1 := by
    obtain ⟨m, hm⟩ := hodd
    have h1 : σ ^ (2 * m) = 1 := by rw [pow_mul, hσ2, one_pow]
    have h2 : σ ^ (2 * m + 1) = σ := by rw [pow_succ, h1, one_mul]
    rw [← h2, ← hm]
    exact pow_orderOf_eq_one σ
  have hnorm : h.norm (Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K) : K) = 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact norm_det_of_mem_unitaryIsom3 A.2
  have hnx : ∀ x : K, h.norm x = x ^ 4 := fun x => by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply]
    ring
  set d : Kˣ := Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K)
  have hd4 : d ^ 4 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ← hnx, hnorm, Units.val_one]
  have hinner : psuConj h A ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
    refine psuConj_mem_range_conj_of_det_eq_pow (u := d ^ 3) ?_ ?_
    · rw [hnx, ← Units.val_pow_eq_pow_val, ← pow_mul, show 3 * 4 = 4 * 3 from rfl, pow_mul, hd4,
        one_pow, Units.val_one]
    · calc d = d * (d ^ 4) ^ 2 := by rw [hd4]; simp
        _ = (d ^ 3) ^ 3 := by group
  have hin : CFSG.RankThree.PartTwo.KFacts.IsInnerAut
      (MulAut.congr (e.trans (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm) θ) := by
    rw [hAσ, hσ, map_one, mul_one]
    exact hinner
  exact (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr
    (e.trans (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm) θ).1 hin

end U3Fam

section SmallFam

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial

theorem burnsideA26_psl2_odd_inner {K : Type} [Field K] [Finite K] {p k : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ k) (hk : k = 1 ∨ k = 2) {S : Type} [Group S] (e : S ≃* PSL2 K)
    (θ : MulAut S) (hθ : Odd (orderOf θ)) :
    (MulAut.conj : S →* MulAut S).range.carrier θ := by
  set φ : MulAut (PSL2 K) := MulAut.congr e θ with hφ
  have hφm : φ ^ orderOf θ = 1 := by rw [hφ, ← map_pow, pow_orderOf_eq_one, map_one]
  set γ := (semilinearEquivAut K).symm φ with hγ
  have hγm : γ ^ orderOf θ = 1 := by rw [hγ, ← map_pow, hφm, map_one]
  have hψ : (SemidirectProduct.rightHom γ) ^ orderOf θ = 1 := by rw [← map_pow, hγm, map_one]
  have hcard : Nat.card (RingAut K) = k :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK).1
  have hcop : Nat.Coprime (orderOf θ) k := by
    rcases hk with rfl | rfl
    · exact Nat.coprime_one_right _
    · exact Nat.coprime_two_right.2 hθ
  have hord : orderOf (SemidirectProduct.rightHom γ) = 1 := by
    have h1 : orderOf (SemidirectProduct.rightHom γ) ∣ orderOf θ := orderOf_dvd_of_pow_eq_one hψ
    have h2 : orderOf (SemidirectProduct.rightHom γ) ∣ k := hcard ▸ orderOf_dvd_natCard _
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hψ1 : SemidirectProduct.rightHom γ = 1 := orderOf_eq_one_iff.mp hord
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.mem_range_pglAction_of_rightHom_eq_one hψ1
  have hg' : g ^ orderOf θ = 1 := by
    apply CFSG.RankThree.PartTwo.KFacts.pglAction_injective
    rw [map_pow, hg, hφm, map_one]
  obtain ⟨x, hx⟩ := CFSG.RankThree.PartTwo.KFacts.exists_toPGL_eq_of_pow_odd hθ hg'
  have hin : CFSG.RankThree.PartTwo.KFacts.IsInnerAut φ := by
    refine ⟨x, ?_⟩
    rw [← hg, ← hx]
    exact pglAction_toPGL K x ▸ rfl
  exact (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e θ).1 hin

theorem burnsideA26_a6 {S : Type} [Group S] (e : S ≃* alternatingGroup (Fin 6)) (θ : MulAut S)
    (hθ : Odd (orderOf θ)) : (MulAut.conj : S →* MulAut S).range.carrier θ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK9 : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)
  haveI : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  obtain ⟨e0⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism
    (GaloisField 3 2) (by rw [← Nat.card_eq_fintype_card, hK9]; norm_num)
  exact burnsideA26_psl2_odd_inner Nat.prime_three hK9 (Or.inr rfl) (e.trans e0.symm) θ hθ

theorem burnsideA26_tits
    {S : Type} [Group S] (hS : CFSG.Blueprint.ReeTitsModel S .Tits 2 1) (θ : MulAut S)
    (hθ : Odd (orderOf θ)) : (MulAut.conj : S →* MulAut S).range.carrier θ := by
  obtain ⟨h2, -⟩ := CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier S 2 1 hS
  obtain ⟨k, hk⟩ :=
    h2 (QuotientGroup.mk θ : CFSG.ComponentClassification.OuterAutomorphisms.Outer S)
  have hdvd : orderOf (QuotientGroup.mk θ :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣ orderOf θ :=
    orderOf_map_dvd (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner S)) θ
  have hodd : Odd (orderOf (QuotientGroup.mk θ :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer S)) := hθ.of_dvd_nat hdvd
  have hpow : orderOf (QuotientGroup.mk θ :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hpow
  have h1 : orderOf (QuotientGroup.mk θ :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer S) = 1 := by
    rcases j with _ | j
    · simpa using hj
    · exfalso
      have : Even (orderOf (QuotientGroup.mk θ :
          CFSG.ComponentClassification.OuterAutomorphisms.Outer S)) := by
        rw [hj]
        exact Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero j⟩
      exact (Nat.not_even_iff_odd.2 hodd) this
  have h2 := orderOf_eq_one_iff.mp h1
  exact (QuotientGroup.eq_one_iff θ).1 h2

end SmallFam

section MainA26

theorem as_A_2_6
    : A_2_6 := by
  intro G _ _ hG L _ hq hLie
  have hsec : ∀ (N : Subgroup ↥L) [N.Normal] [IsSimpleGroup (↥L ⧸ N)],
      (∃ a b : ↥L ⧸ N, a * b ≠ b * a) → CFSG.IsStronglyQuasithin (↥L ⧸ N) := fun N _ _ hn =>
    (CFSG.SectionRank.sqt_catalog_of_simple_section_of_sqtk hG L N hn).1
  have hSQT3 : ∀ {G : Type} [Group G] [Finite G], CFSG.SectionRank.IsSQTKCat G →
      CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 2 := fun hG' =>
    (CFSG.SectionRank.isStronglyQuasithin_iff.1 hG'.1) 3 Nat.prime_three (by norm_num)
  have hSQT := burnsideA26_sqt_of_sections L hsec hq
  have hSQT' := CFSG.SectionRank.isStronglyQuasithin_iff.1 hSQT
  have hThmC := burnsideA26_isEvenLieThmC_of_sqt hSQT'
    (fun h => CFSG.SectionRank.sqt_exceptional_restriction hSQT' h) hLie
  refine ⟨hThmC, fun x hx => ?_⟩
  have hodd : Odd (orderOf (burnsideA26_indAut L x)) :=
    hx.of_dvd_nat (burnsideA26_orderOf_indAut_dvd L x)
  refine ⟨burnsideA26_indAut L x, ?_, fun l => burnsideA26_indAut_apply L x l⟩
  set θ := burnsideA26_indAut L x
  rcases hThmC with ⟨n, hm⟩ | ⟨n, hm⟩ | ⟨n, hm⟩ | ⟨n, hm⟩ | ⟨n, hm⟩ | ⟨n, hm⟩ | ⟨n, hm⟩ |
    ⟨n, hm⟩ | hm | hm | hm | hm | hm
  ·
    obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hm
    exact burnsideA26_l2 hcard e θ
  ·
    obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hm
    exact burnsideA26_l3 hcard e θ hodd
  ·
    obtain ⟨⟨-, hn1, -, hne⟩, K, _, _, hcard, ⟨e⟩⟩ := hm
    have hn2 : 2 ≤ n := by
      by_contra hlt
      obtain rfl : n = 1 := by omega
      exact hne (by simp)
    exact burnsideA26_u3 hn2 hcard e θ hodd
  ·
    obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hm
    haveI := burnsideA26_charP_two hcard
    exact burnsideA26_sp4 hcard e θ hodd
  ·
    obtain ⟨⟨-, hn1, hn3⟩, K, _, _, hcard, ⟨e⟩⟩ := hm
    have hK4 : 4 ≤ Nat.card K := by
      rw [hcard]
      have : 2 ≤ n := by
        by_contra hlt
        obtain rfl : n = 1 := by omega
        omega
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this
    exact burnsideA26_g2 hcard hK4 e θ
  ·
    exact burnsideA26_3d4 (hSQT3 hG) L hq hm x
  ·
    obtain ⟨-, a, ha, K, _, _, hfa, hcard, ⟨e⟩⟩ := hm
    exact burnsideA26_sz ha (by rw [hcard, hfa]) e θ
  ·
    obtain ⟨⟨-, -, -, -, -, hf3⟩, a, hfa, K, _, _, hcard, ⟨e⟩⟩ := hm
    exact burnsideA26_f4 (by omega) (by rw [hcard, hfa]) e θ
  ·
    exact burnsideA26_small θ (burnsideA26_tits hm θ hodd) (Or.inr (Or.inr (Or.inl hm)))
  ·
    obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := id hm
    exact burnsideA26_small θ (burnsideA26_l45 (by norm_num) (by simpa using hcard) e θ hodd)
      (Or.inl hm)
  ·
    obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := id hm
    exact burnsideA26_small θ (burnsideA26_l45 (by norm_num) (by simpa using hcard) e θ hodd)
      (Or.inr (Or.inl hm))
  ·
    obtain ⟨e⟩ := id hm
    exact burnsideA26_small θ (burnsideA26_a6 e θ hodd) (Or.inr (Or.inr (Or.inr (Or.inl hm))))
  ·
    obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := id hm
    exact burnsideA26_small θ (burnsideA26_u33 hcard e θ hodd)
      (Or.inr (Or.inr (Or.inr (Or.inr hm))))

end MainA26

end CFSG.ASVolI
