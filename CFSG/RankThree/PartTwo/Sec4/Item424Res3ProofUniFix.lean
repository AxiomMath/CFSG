module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofUniPair
public import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofUniOrder
public import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofLinFix
import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofTrialityPGL
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Card

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item424Res3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Matrix
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS.IVK (fixedField fixedField_apply)

theorem exists_isType424_quotient_of_hom {Y : Type*} [Group Y] (hY : IsQuasisimple Y)
    {Γ : Type} [Group Γ] [Finite Γ] (ρ : Y →* Γ) (hker : ρ.ker ≤ Subgroup.center Y)
    (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ ρ.range)
    (h : Sec11.KS11Lie2Proof.HasType424 Γ) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (ψ : Y →* X), Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center Y ∧ Sec11.IsType424 X ∧ IsQuasisimple X := by
  set ρ' := ρ.rangeRestrict with hρ'
  have hρ's : Function.Surjective ρ' := ρ.rangeRestrict_surjective
  have hker' : ρ'.ker ≤ Subgroup.center Y := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hN : IsQuasisimple ρ.range := CFSG.LocalCores.isQuasisimple_of_surjective hY ρ' hρ's hker'
  obtain ⟨hT, hQ⟩ := isType424_of_hasType424 ρ.range hN hcomm h
  exact ⟨_, inferInstance, inferInstance,
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ρ.range)).comp ρ',
    (QuotientGroup.mk'_surjective _).comp hρ's, ker_le_center_of_comp hY ρ' hρ's hker', hT, hQ⟩

theorem isSolvable_of_commutator_mem_range {Y Γ : Type*} [Group Y] [Group Γ]
    [Group.IsSolvable Y] (ρ : Y →* Γ) (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ ρ.range) :
    Group.IsSolvable Γ := by
  refine Group.isSolvable_of_ker_le_range ρ (Abelianization.of : Γ →* Abelianization Γ) ?_
  rw [Abelianization.ker_of, commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [commutatorElement_def]
  exact hcomm a b

theorem isSolvable_unitarySU_two {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (h2 : p ^ f = 2) : Group.IsSolvable (unitarySU p f K 3) := by
  have := h.finite
  have hc := GH74.GLS.Stage2.Signalizer.Odd87.card_unitarySU_three h
  rw [h2] at hc
  have : Fintype (unitarySU p f K 3) := Fintype.ofFinite _
  refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
    Nat.prime_two Nat.prime_three (by norm_num) ?_
  rw [← Nat.card_eq_fintype_card, hc]
  norm_num

theorem two_even_of_hasType424_of_su_hom {p f₀ : ℕ} {F₀ : Type} [Field F₀]
    (h₀ : UnitaryFieldData p f₀ F₀) {Γ : Type} [Group Γ] [Finite Γ]
    (ρ : unitarySU p f₀ F₀ 3 →* Γ) (hker : ρ.ker ≤ Subgroup.center (unitarySU p f₀ F₀ 3))
    (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ ρ.range)
    (h : Sec11.KS11Lie2Proof.HasType424 Γ) : p = 2 ∧ Even f₀ := by
  have := h₀.finite
  have : Fact p.Prime := ⟨h₀.prime⟩
  have hf₀ := h₀.one_le
  have hq1 : 2 ≤ p ^ f₀ := h₀.prime.two_le.trans (Nat.le_self_pow (by omega) p)
  by_cases hq2 : p ^ f₀ = 2
  · exfalso
    have := isSolvable_unitarySU_two h₀ hq2
    exact Res4Seven.not_hasType424_of_isSolvable (isSolvable_of_commutator_mem_range ρ hcomm) h
  have hq : 2 < p ^ f₀ := by omega
  have hcard : Nat.card F₀ = (p ^ f₀) ^ 2 := by rw [h₀.card, ← pow_mul, mul_comm]
  have hY : IsQuasisimple (unitarySU p f₀ F₀ 3) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard le_rfl (by
      intro hh
      simp only [Prod.mk.injEq, true_and] at hh
      omega)).1
  obtain ⟨X, _, _, ψ, hψs, hψker, hT, hQ⟩ := exists_isType424_quotient_of_hom hY ρ hker hcomm h
  have h1 := su3_mod_eq_one_of_isType424 h₀ hq hT hQ ψ hψker
  have hcen : Subgroup.center (unitarySU p f₀ F₀ 3) = ⊥ := by
    rw [KFacts.center_unitarySU_three (h := h₀) hq,
      KFacts.unitaryScalars_three_eq_bot_of_mod_three h₀ h1]
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hψker.trans hcen.le
  have hcardX : Nat.card X = (p ^ f₀) ^ 3 * ((p ^ f₀) ^ 2 - 1) * ((p ^ f₀) ^ 3 + 1) := by
    rw [← Nat.card_congr (MulEquiv.ofBijective ψ ⟨hinj, hψs⟩).toEquiv]
    exact GH74.GLS.Stage2.Signalizer.Odd87.card_unitarySU_three h₀
  have hp2 : p = 2 := by
    by_contra hp2
    have hq7 : 7 ≤ p ^ f₀ := by
      obtain ⟨j, hj⟩ := (h₀.prime.odd_of_ne_two hp2).pow (n := f₀)
      omega
    exact not_isType424_of_card_su h₀.prime hp2 hq7 hcardX hT
  subst hp2
  refine ⟨rfl, ?_⟩
  rcases Nat.even_or_odd f₀ with he | ho
  · exact he
  · exfalso
    obtain ⟨j, hj⟩ := ho
    rw [hj, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod] at h1
    norm_num at h1

section Models

variable {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F) {σ : F ≃+* F} {f₀ : ℕ}
  (h₀ : UnitaryFieldData p f₀ (fixedField σ))
  (hbar : ∀ x : fixedField σ, h.bar (x : F) = ((h₀.bar x : fixedField σ) : F))

@[expose] noncomputable def psuFixHom :
    unitarySU p f₀ (fixedField σ) 3 →* Item426.fixSub (KFacts.psuField h σ) :=
  ((unitaryProj h 3).comp (KFacts.suIncl h h₀ hbar)).codRestrict _ fun g₀ => by
    rw [Item426.mem_fixSub, MonoidHom.comp_apply]
    have hfix := (KFacts.mem_range_suIncl_iff h h₀ hbar (KFacts.suIncl h h₀ hbar g₀)).mp
      ⟨g₀, rfl⟩
    exact (KFacts.psuField_mk σ _).trans (congrArg (unitaryProj h 3) hfix)

theorem unitaryScalars_le_center : unitaryScalars h 3 ≤ Subgroup.center (unitarySU p f F 3) := by
  intro z hz
  obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.mp hz
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
  exact (commute_scalar c (g : GL (Fin 3) F)).eq

theorem psuFixHom_ker_le :
    (psuFixHom h h₀ hbar).ker ≤ Subgroup.center (unitarySU p f₀ (fixedField σ) 3) := by
  intro g₀ hg₀
  have h1 : unitaryProj h 3 (KFacts.suIncl h h₀ hbar g₀) = 1 := congrArg Subtype.val hg₀
  have h2 : KFacts.suIncl h h₀ hbar g₀ ∈ unitaryScalars h 3 :=
    (QuotientGroup.eq_one_iff _).mp h1
  have h3 := unitaryScalars_le_center h h2
  rw [Subgroup.mem_center_iff]
  intro b₀
  apply KFacts.suIncl_injective h h₀ hbar
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.mp h3 _

theorem commutator_mem_range_psuFixHom (a b : Item426.fixSub (KFacts.psuField h σ)) :
    a * b * a⁻¹ * b⁻¹ ∈ (psuFixHom h h₀ hbar).range := by
  obtain ⟨A, hA⟩ := unitaryProj_surjective h 3 a
  obtain ⟨B, hB⟩ := unitaryProj_surjective h 3 b
  have hσ : ∀ {A : unitarySU p f F 3},
      KFacts.psuField h σ (unitaryProj h 3 A) = unitaryProj h 3 A →
      ∃ u ∈ Subgroup.center (unitarySU p f F 3), KFacts.suField h σ A = A * u := by
    intro A hA
    have h1 : ((KFacts.suField h σ A : unitarySU p f F 3) : unitaryPSU h 3) =
        (A : unitaryPSU h 3) := (KFacts.psuField_mk σ A).symm.trans hA
    have h2 := QuotientGroup.eq.mp h1.symm
    exact ⟨_, unitaryScalars_le_center h h2, by group⟩
  obtain ⟨u, hu, hAu⟩ := hσ (hA ▸ a.2 : KFacts.psuField h σ (unitaryProj h 3 A) =
    unitaryProj h 3 A)
  obtain ⟨v, hv, hBv⟩ := hσ (hB ▸ b.2 : KFacts.psuField h σ (unitaryProj h 3 B) =
    unitaryProj h 3 B)
  have hfix : KFacts.suField h σ (A * B * A⁻¹ * B⁻¹) = A * B * A⁻¹ * B⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hAu, hBv]
    exact commutator_mul_central hu hv
  obtain ⟨M₀, hM₀⟩ := (KFacts.mem_range_suIncl_iff h h₀ hbar _).mpr hfix
  refine ⟨M₀, Subtype.ext ?_⟩
  change unitaryProj h 3 (KFacts.suIncl h h₀ hbar M₀) =
    ((a * b * a⁻¹ * b⁻¹ : Item426.fixSub (KFacts.psuField h σ)) : unitaryPSU h 3)
  rw [hM₀, map_mul, map_mul, map_mul, map_inv, map_inv, hA, hB]
  rfl

@[expose] noncomputable def suFixHom :
    unitarySU p f₀ (fixedField σ) 3 →* Item426.fixSub (KFacts.suField h σ) :=
  (KFacts.suIncl h h₀ hbar).codRestrict _ fun g₀ =>
    (KFacts.mem_range_suIncl_iff h h₀ hbar _).mp ⟨g₀, rfl⟩

theorem suFixHom_surjective : Function.Surjective (suFixHom h h₀ hbar) := by
  rintro ⟨A, hA⟩
  obtain ⟨A₀, hA₀⟩ := (KFacts.mem_range_suIncl_iff h h₀ hbar A).mpr hA
  exact ⟨A₀, Subtype.ext hA₀⟩

variable {h} in
theorem hasType424_psuField_imp (hσ : orderOf σ = 3)
    (hH : Sec11.KS11Lie2Proof.HasType424 (Item426.fixSub (KFacts.psuField h σ))) :
    p = 2 ∧ ∃ m : ℕ, f = 3 * m ∧ Even m := by
  have := h.finite
  obtain ⟨f₀, hf, hf₀, hcard⟩ := KFacts.exists_card_fixedField_of_orderOf_eq_three h hσ
  have h₀ : UnitaryFieldData p f₀ (fixedField σ) := ⟨h.prime, hf₀, hcard⟩
  have hbar := KFacts.bar_coe_fixedField h hf h₀
  obtain ⟨hp, he⟩ := two_even_of_hasType424_of_su_hom h₀ (psuFixHom h h₀ hbar)
    (psuFixHom_ker_le h h₀ hbar) (commutator_mem_range_psuFixHom h h₀ hbar) hH
  exact ⟨hp, f₀, hf, he⟩

variable {h} in
theorem hasType424_suField_imp (hσ : orderOf σ = 3)
    (hH : Sec11.KS11Lie2Proof.HasType424 (Item426.fixSub (KFacts.suField h σ))) :
    p = 2 ∧ ∃ m : ℕ, f = 3 * m ∧ Even m := by
  have := h.finite
  obtain ⟨f₀, hf, hf₀, hcard⟩ := KFacts.exists_card_fixedField_of_orderOf_eq_three h hσ
  have h₀ : UnitaryFieldData p f₀ (fixedField σ) := ⟨h.prime, hf₀, hcard⟩
  have hbar := KFacts.bar_coe_fixedField h hf h₀
  refine (fun hr => ⟨hr.1, f₀, hf, hr.2⟩) (two_even_of_hasType424_of_su_hom h₀
    (suFixHom h h₀ hbar) ?_ (fun a b => suFixHom_surjective h h₀ hbar _) hH)
  intro A₀ hA₀
  have h1 : suFixHom h h₀ hbar A₀ = suFixHom h h₀ hbar 1 := by rw [hA₀, map_one]
  rw [KFacts.suIncl_injective h h₀ hbar (congrArg Subtype.val h1)]
  exact Subgroup.one_mem _

end Models

end CFSG.RankThree.PartTwo.Sec4.Item424Res3
