module

public import CFSG.RankThree.PartTwo.KFacts.AutG2OrderThree
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.HardMathSupport.Lang.Proving.SylowMapFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction
import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

private theorem padicValNat_sl2_cubic {a : ℕ} (ha2 : 2 ≤ a) (ha3 : ¬ 3 ∣ a) :
    padicValNat 3 (a ^ 3 * ((a ^ 3) ^ 2 - 1)) =
      padicValNat 3 (a * (a ^ 2 - 1)) + 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hu : 1 < a ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have hmod : a ^ 2 % 3 = 1 := by
    have hm : a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases hm with hm | hm <;> simp [Nat.pow_mod, hm]
  have hdvd : 3 ∣ a ^ 2 - 1 := by
    generalize a ^ 2 = u at hmod hu ⊢
    omega
  have hn : ¬ 3 ∣ a ^ 2 := fun h => ha3 (Nat.prime_three.dvd_of_dvd_pow h)
  have hv : padicValNat 3 ((a ^ 2) ^ 3 - 1) = padicValNat 3 (a ^ 2 - 1) + 1 := by
    have h := padicValNat.pow_sub_pow (p := 3) (by decide : Odd 3) hu hdvd hn
      (n := 3) (by norm_num)
    simpa only [one_pow, padicValNat_self] using h
  have ha0 : a ≠ 0 := by omega
  have hc0 : a ^ 3 ≠ 0 := pow_ne_zero _ ha0
  have hs0 : a ^ 2 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hu
  have hl0 : (a ^ 2) ^ 3 - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by norm_num) hu)
  have hz : padicValNat 3 a = 0 := padicValNat.eq_zero_of_not_dvd ha3
  have hz3 : padicValNat 3 (a ^ 3) = 0 :=
    padicValNat.eq_zero_of_not_dvd fun h => ha3 (Nat.prime_three.dvd_of_dvd_pow h)
  rw [show (a ^ 3) ^ 2 = (a ^ 2) ^ 3 by ring, padicValNat.mul hc0 hl0,
    padicValNat.mul ha0 hs0, hz3, hz, hv]
  simp

private theorem isMulCommutative_sylow_three_sl2
    {F : Type} [Field F] [Finite F] (h3 : ringChar F ≠ 3) (h4 : 4 ≤ Nat.card F)
    (S : Sylow 3 (Matrix.SpecialLinearGroup (Fin 2) F)) :
    IsMulCommutative (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π := QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 2) F))
  have hmap : IsPGroup 3 ((S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).map π) :=
    S.isPGroup'.map π
  obtain ⟨Q, hQ⟩ := hmap.exists_le_sylow
  have : IsCyclic (Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :=
    CFSG.RankThree.PartTwo.KFacts.isCyclic_sylow_three_psl2 h3 h4 Q
  have : IsCyclic ((S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).map π) :=
    Subgroup.isCyclic_of_le hQ
  let ψ := π.subgroupMap (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
  apply MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center ψ
  intro a ha
  have hz : (a : Matrix.SpecialLinearGroup (Fin 2) F) ∈
      center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg Subtype.val ha
  rw [Subgroup.mem_center_iff]
  intro b
  exact Subtype.ext (Subgroup.mem_center_iff.mp hz b)

theorem exists_moved_abelian_of_sl2_field
    {F : Type} [Field F] [Finite F] (h3 : ringChar F ≠ 3) (h4 : 4 ≤ Nat.card F)
    (σ : F ≃+* F) (hσ : orderOf σ = 3) :
    ∃ S : Sylow 3 (Matrix.SpecialLinearGroup (Fin 2) F),
      IsMulCommutative (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      (∀ a ∈ (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
        Matrix.SpecialLinearGroup.map σ.toRingHom a ∈ (S : Subgroup _)) ∧
      ∃ a ∈ (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
        Matrix.SpecialLinearGroup.map σ.toRingHom a ≠ a := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ := CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 2) F σ
  have hφ : φ ^ 3 = 1 := by
    change (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 2) F σ) ^ 3 = 1
    rw [← map_pow, ← hσ, pow_orderOf_eq_one, map_one]
  obtain ⟨S, hS⟩ := CFSG.HardMathSupport.Lang.Proving.exists_sylow_map_eq_of_pow_three φ hφ
  have hstable : ∀ a ∈ (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
      Matrix.SpecialLinearGroup.map σ.toRingHom a ∈ (S : Subgroup _) := by
    intro a ha
    have hh := Subgroup.mem_map_of_mem φ.toMonoidHom ha
    rw [hS] at hh
    exact hh
  refine ⟨S, isMulCommutative_sylow_three_sl2 h3 h4 S, hstable, ?_⟩
  by_contra hfix
  push Not at hfix
  let ι : Matrix.SpecialLinearGroup (Fin 2) (CFSG.GH74.GLS.IVK.fixedField σ) →*
      Matrix.SpecialLinearGroup (Fin 2) F :=
    Matrix.SpecialLinearGroup.map (CFSG.GH74.GLS.IVK.fixedField σ).subtype
  have hi : Function.Injective ι := by
    intro A B h
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact Subtype.ext (congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) F => C i j) h)
  have hle : (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ≤ ι.range := by
    intro a ha
    refine CFSG.GH74.GLS.IVK.exists_specialLinear_map_eq σ a ?_
    intro i j
    exact congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) F => C i j) (hfix a ha)
  have hdvd : Nat.card (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ∣
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (CFSG.GH74.GLS.IVK.fixedField σ)) := by
    have hd := Subgroup.card_dvd_of_le hle
    rwa [← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv] at hd
  have hcard : Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) ^ 3 = Nat.card F := by
    simpa only [hσ] using CFSG.GH74.GLS.IVK.fixedField_card_pow σ
  have hq2 : 2 ≤ Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) :=
    Nat.succ_le_of_lt Finite.one_lt_card
  have hq3 : ¬ 3 ∣ Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) := by
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
    have hF3 : ¬ 3 ∣ Nat.card F := by
      rw [Nat.card_eq_fintype_card, hn]
      exact fun h => h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h)).symm
    exact fun h => hF3 (hcard ▸ (h.trans (dvd_pow_self _ (by norm_num : 3 ≠ 0))))
  have hSyl : Nat.card (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) =
      3 ^ padicValNat 3 (Nat.card (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    rw [Sylow.card_eq_multiplicity, Nat.factorization_def _ Nat.prime_three]
  have h0 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (CFSG.GH74.GLS.IVK.fixedField σ)) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  rw [hSyl, padicValNat_dvd_iff_le h0,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num),
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num)] at hdvd
  have hI : Finset.Icc 2 2 = ({2} : Finset ℕ) := by decide
  norm_num only [hI, Finset.prod_singleton, pow_one] at hdvd
  rw [← hcard, padicValNat_sl2_cubic hq2 hq3] at hdvd
  omega

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem exists_moved_abelian_of_g2_field
    {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    (σ : K ≃+* K) (hσ : orderOf σ = 3) :
    ∃ A : Subgroup (adjointGroup .G2 K),
      IsPGroup 3 A ∧ IsMulCommutative A ∧
      (∀ a ∈ A, CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ a ∈ A) ∧
      ∃ a ∈ A, CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ a ≠ a := by
  classical
  let ρ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup .G2 K :=
    (rootSL2 .G2 K ![1, 0]).codRestrict (adjointGroup .G2 K)
      (fun A => (exceptional_Lang_root_rank_one_data .G2 K ![1, 0]).2.2.2.2.1 A)
  have hρ : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
      (ρ A : ModGL .G2 K) = rootSL2 .G2 K ![1, 0] A := fun _ => rfl
  have hi : Function.Injective ρ := by
    intro A B h
    apply CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := .G2) (K := K) ![1, 0]
    exact congrArg Subtype.val h
  have heq : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
      CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ (ρ A) =
        ρ (Matrix.SpecialLinearGroup.map σ.toRingHom A) := by
    intro A
    apply Subtype.ext
    rw [CFSG.RankThree.PartTwo.KFacts.coe_g2FieldHom, hρ, hρ]
    exact CFSG.RankThree.Chevalley.entrywise_rootSL2_of_field
      (τ := .G2) (K := K) σ.toRingHom ![1, 0] A
  obtain ⟨S, hSab, hstable, a, ha, hmoved⟩ := exists_moved_abelian_of_sl2_field hK3 hK4 σ hσ
  let A := (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)).map ρ
  have hAp : IsPGroup 3 A := S.isPGroup'.map ρ
  have hAab : IsMulCommutative A := by
    let : IsMulCommutative (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) := hSab
    exact Subgroup.map_isMulCommutative (S : Subgroup _) ρ
  refine ⟨A, hAp, hAab, ?_, ρ a, Subgroup.mem_map_of_mem ρ ha, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    rw [heq]
    exact Subgroup.mem_map_of_mem ρ (hstable b hb)
  · rw [heq]
    exact fun h => hmoved (hi h)

theorem exists_moved_abelian_of_g2_outer
    {Y : Type} [Group Y] [Finite Y] {p f : ℕ}
    (hY : CFSG.Blueprint.LieModel Y .G2 0 p f) (hp3 : p ≠ 3)
    (_h9 : 9 ∣ (p ^ f) ^ 2 - 1) (hf3 : 3 ∣ f)
    (α : MulAut Y) (hα3 : α ^ 3 = 1)
    (hout : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner Y) :
    ∃ A : Subgroup Y, IsPGroup 3 A ∧ IsMulCommutative A ∧
      (∀ a ∈ A, α a ∈ A) ∧ ∃ a ∈ A, α a ≠ a := by
  classical
  have hmodel := hY.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hmodel.2
  have hK3 : ringChar K ≠ 3 := by
    have : CharP K p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      hmodel.1.1 (by have := hmodel.1.2.1; omega) hK
    rw [ringChar.eq K p]
    exact hp3
  have hfpos : 0 < f := by have := hmodel.1.2.1; omega
  have hfge : 3 ≤ f := Nat.le_of_dvd hfpos hf3
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfge
      _ ≤ p ^ f := Nat.pow_le_pow_left hmodel.1.1.two_le f
  let β := MulAut.congr e α
  have hβ3 : β ^ 3 = 1 := by
    rw [← map_pow, hα3, map_one]
  have hβout : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut β := by
    rintro ⟨k, hk⟩
    apply hout
    refine ⟨e.symm k, ?_⟩
    ext y
    apply e.injective
    have h := congrArg (fun δ : MulAut (adjointGroup .G2 K) => δ (e y)) hk
    simpa [β, MulAut.congr_apply, MulAut.conj_apply] using h
  obtain ⟨σ, hσ, k, hk⟩ :=
    CFSG.RankThree.PartTwo.KFacts.g2_order_three_field_descent hK3 hK4 hβ3 hβout
  obtain ⟨A, hAp, hAab, hstable, a, ha, hmoved⟩ :=
    exists_moved_abelian_of_g2_field hK3 hK4 σ hσ
  let θ : adjointGroup .G2 K ≃* Y := (MulAut.conj k).trans e.symm
  have hi : Function.Injective θ := θ.injective
  have heq : ∀ b : adjointGroup .G2 K,
      α (θ b) = θ (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ b) := by
    intro b
    apply e.injective
    have h := congrArg (fun δ : MulAut (adjointGroup .G2 K) => δ (MulAut.conj k b)) hk
    change e (α (e.symm (MulAut.conj k b))) =
      e (e.symm (MulAut.conj k (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ b)))
    rw [e.apply_symm_apply]
    change β (MulAut.conj k b) = _
    rw [hk, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  let B := A.map θ.toMonoidHom
  have hBp : IsPGroup 3 B := hAp.map θ.toMonoidHom
  have hBab : IsMulCommutative B := by
    let : IsMulCommutative A := hAab
    exact Subgroup.map_isMulCommutative A θ.toMonoidHom
  refine ⟨B, hBp, hBab, ?_, θ a, Subgroup.mem_map_of_mem θ.toMonoidHom ha, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    change α (θ b) ∈ B
    rw [heq]
    exact Subgroup.mem_map_of_mem θ.toMonoidHom (hstable b hb)
  · rw [heq]
    exact fun h => hmoved (hi h)

end CFSG.LocalAnalysis.UniquenessCase.UC22
