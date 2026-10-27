module

public import CFSG.Quasithin.SteinbergCCOddPlaneActionBound
public import CFSG.Quasithin.SteinbergCBRadicalTransport
public import CFSG.Quasithin.H13.NQBlockCcommWholeFrattini
public import CFSG.LocalAnalysis.SteinbergCECComponentRadicalQuotient
public import CFSG.LocalAnalysis.SteinbergCCSQTKTwoCoreQuotient
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Hom
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.SectionRank.Ccomm CFSG.Quasithin

theorem comap_solvableRadical_mulEquiv {H₁ H₂ : Type*} [Group H₁] [Group H₂] [Finite H₁]
    (e : H₁ ≃* H₂) :
    (CFSG.solvableRadical H₂).comap e.toMonoidHom = CFSG.solvableRadical H₁ := by
  have hker : Group.IsSolvable ↥e.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
    infer_instance
  exact CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.comap_solvableRadical e.surjective
    hker

theorem autQuotient_eq_one_iff {G : Type*} [Group G] (N : Subgroup G) [N.Characteristic]
    (α : MulAut G) : autQuotient N α = 1 ↔ ∀ x : G, x⁻¹ * α x ∈ N := by
  constructor
  · intro h x
    have h1 : autQuotient N α (x : G ⧸ N) = (x : G ⧸ N) := by
      rw [h]
      rfl
    exact QuotientGroup.eq.mp h1.symm
  · intro h
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact (QuotientGroup.eq.mpr (h x)).symm

theorem card_map_autQuotient_solvableRadical_congr {H₁ H₂ : Type*} [Group H₁] [Group H₂]
    [Finite H₁] (e : H₁ ≃* H₂) (A : Subgroup (MulAut H₂)) :
    Nat.card ((A.map (MulAut.congr e).symm.toMonoidHom).map
        (autQuotient (CFSG.solvableRadical H₁))) =
      Nat.card (A.map (autQuotient (CFSG.solvableRadical H₂))) := by
  have : Finite H₂ := Finite.of_equiv _ e.toEquiv
  have hR := comap_solvableRadical_mulEquiv e
  let ψ₁ : ↥A →* MulAut (H₁ ⧸ CFSG.solvableRadical H₁) :=
    (autQuotient (CFSG.solvableRadical H₁)).comp
      ((MulAut.congr e).symm.toMonoidHom.comp A.subtype)
  let ψ₂ : ↥A →* MulAut (H₂ ⧸ CFSG.solvableRadical H₂) :=
    (autQuotient (CFSG.solvableRadical H₂)).comp A.subtype
  have hker : ψ₁.ker = ψ₂.ker := by
    ext α
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change autQuotient _ ((MulAut.congr e).symm (α : MulAut H₂)) = 1 ↔
      autQuotient _ (α : MulAut H₂) = 1
    rw [autQuotient_eq_one_iff, autQuotient_eq_one_iff]
    constructor
    · intro h y
      obtain ⟨x, rfl⟩ := e.surjective y
      have h1 := h x
      rw [← hR, mem_comap] at h1
      simpa [MulAut.congr_symm_apply] using h1
    · intro h x
      rw [← hR, mem_comap]
      simpa [MulAut.congr_symm_apply] using h (e x)
  have h1 : ψ₁.range = (A.map (MulAut.congr e).symm.toMonoidHom).map
      (autQuotient (CFSG.solvableRadical H₁)) := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, range_subtype]
  have h2 : ψ₂.range = A.map (autQuotient (CFSG.solvableRadical H₂)) := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← h1, ← h2]
  exact Nat.card_congr (NQBlock.rangeEquivOfKerEq ψ₁ ψ₂ hker).toEquiv

theorem nq_SQT_component_radical_action_bound {L : Type*} [Group L]
    [Finite L] (hSQT : CFSG.IsStronglyQuasithin L) (hLC : CFSG.IsCComponent (⊤ : Subgroup L))
    (hq : ¬ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)) :
    (∀ A : Subgroup (MulAut L), IsMulCommutative A → (∀ a ∈ A, a ^ 2 = 1) →
      Nat.card (A.map (autQuotient (CFSG.solvableRadical L))) ≤ 2) ∧
    ∀ (B : Type*) [Group B], CFSG.IsElementaryAbelian 2 B → Nat.card B = 4 →
      ∀ φ : B →* MulAut L,
        ¬ Function.Injective ((autQuotient (CFSG.solvableRadical L)).comp φ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup L := CFSG.pCore 2 L with hN
  have hNsolv : Group.IsSolvable ↥N := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := L)).isNilpotent
    infer_instance
  have hSQTbar : CFSG.IsStronglyQuasithin (L ⧸ N) := fun r hr hr2 => by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hr N
      (CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two hr hr2)]
    exact hSQT r hr hr2
  have hO2bar : CFSG.pCore 2 (L ⧸ N) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hLCbar : CFSG.IsCComponent (⊤ : Subgroup (L ⧸ N)) := by
    have h := map_mem_cComp_top (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      (by rw [QuotientGroup.ker_mk']; exact hNsolv) (mem_cComp_top_iff_isCComponent.mpr hLC)
    rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h
    exact mem_cComp_top_iff_isCComponent.mp h
  have hqbar : ¬ CFSG.IsQuasisimple ↥(⊤ : Subgroup (L ⧸ N)) := fun h =>
    hq ((CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr Subgroup.topEquiv).1 h)
  obtain ⟨-, hFne, -, -, hcores⟩ := NQBlock.whole_Frattini_assembly hSQTbar hO2bar hLCbar hqbar
  obtain ⟨r, hr⟩ :
      (Nat.card (CFSG.fittingSubgroup ↥(⊤ : Subgroup (L ⧸ N)))).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr ((Subgroup.one_lt_card_iff_ne_bot _).mpr hFne)
  obtain ⟨-, hr2, -, hdim, hrange, -, -, -⟩ := hcores r hr
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  have hker : ((autQuotient (frattini (CFSG.pCore r ↥(⊤ : Subgroup (L ⧸ N))))).comp
      (MulAut.conjNormal : ↥(⊤ : Subgroup (L ⧸ N)) →*
        MulAut (CFSG.pCore r ↥(⊤ : Subgroup (L ⧸ N))))).ker ≤
      CFSG.solvableRadical ↥(⊤ : Subgroup (L ⧸ N)) := by
    obtain ⟨-, hprop, -⟩ := CFSG.LocalAnalysis.Ccomponent_radical_quotient_simple hLCbar
    refine hprop _ ?_ (MonoidHom.normal_ker _).isSubnormal
    rw [lt_top_iff_ne_top]
    intro htop
    apply hrange
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ ((autQuotient (frattini (CFSG.pCore r ↥(⊤ : Subgroup (L ⧸ N))))).comp
        (MulAut.conjNormal : ↥(⊤ : Subgroup (L ⧸ N)) →*
          MulAut (CFSG.pCore r ↥(⊤ : Subgroup (L ⧸ N))))).ker := by
      rw [htop]
      exact mem_top x
    exact hx
  have hbound : ∀ A : Subgroup (MulAut L), IsMulCommutative A → (∀ a ∈ A, a ^ 2 = 1) →
      Nat.card (A.map (autQuotient (CFSG.solvableRadical L))) ≤ 2 := by
    intro A hA hA2
    let e₀ : ↥(⊤ : Subgroup (L ⧸ N)) ≃* L ⧸ N := Subgroup.topEquiv
    obtain ⟨Abar, hAbar⟩ : ∃ X : Subgroup (MulAut (L ⧸ N)), X = A.map (autQuotient N) :=
      ⟨_, rfl⟩
    obtain ⟨A₁, hA₁⟩ : ∃ X : Subgroup (MulAut ↥(⊤ : Subgroup (L ⧸ N))),
        X = Abar.map (MulAut.congr e₀).symm.toMonoidHom := ⟨_, rfl⟩
    have hAbarc : IsMulCommutative ↥Abar := by
      rw [hAbar]
      infer_instance
    have hA₁c : IsMulCommutative ↥A₁ := by
      rw [hA₁]
      infer_instance
    have hAbar2 : ∀ a ∈ Abar, a ^ 2 = 1 := by
      rw [hAbar]
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hA2 a ha, map_one]
    have hA₁2 : ∀ a ∈ A₁, a ^ 2 = 1 := by
      rw [hA₁]
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hAbar2 a ha, map_one]
    have h1 := SteinbergCC.characteristic_odd_plane_action_bound hrp hr2
      (Q := CFSG.pCore r ↥(⊤ : Subgroup (L ⧸ N))) CFSG.pCore_isPGroup hdim hker hA₁c hA₁2
    have h2 := card_map_autQuotient_solvableRadical_congr e₀ Abar
    obtain ⟨-, -, _, -, -, htrans⟩ :=
      SteinbergCB.nq_characteristic_solvable_quotient_radical_transport N hNsolv
    obtain ⟨-, hcard, -⟩ := htrans A
    rw [hcard, ← hAbar, ← h2, ← hA₁]
    exact h1
  refine ⟨hbound, fun B _ hB hB4 φ hinj => ?_⟩
  have hBc : IsMulCommutative B := hB.toIsMulCommutative
  have hφc : IsMulCommutative ↥φ.range := inferInstance
  have hφ2 : ∀ a ∈ φ.range, a ^ 2 = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 B) b, map_one]
  have h := hbound φ.range hφc hφ2
  rw [← MonoidHom.range_comp, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hB4] at h
  omega

end CFSG.Quasithin.H13.NQCore
