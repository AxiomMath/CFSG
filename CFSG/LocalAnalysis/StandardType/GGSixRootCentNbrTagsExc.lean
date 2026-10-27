module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNbr
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsExcF4
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsExcE
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsExcTwE6

public section

namespace CFSG.StandardType

section TagsF4

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

theorem ggRootCentDerivedQTag_F4 : GGRootCentDerivedQTag .F4 := by
  intro G _ _ n f ψ _ _ hker hC _ _ r hr
  have hψ := AutSt.ker_eq_center hker hC
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hr2
  have hγ' : IsRoot .F4 γ := mem_adjDatum_roots.mp hγ
  have hcz : GGRootCentQL z := RootCentQL.of_mem_rootGroup (K := GaloisField 2 f) _
    (RootCentQL.single_F4 _ (RootCentQL.xPar_f4HighRoot _)) hγ' hz hz1
  have hker' : (MonoidHom.id (ggU .F4 n f).K).ker = ψ.ker := by
    rw [MonoidHom.ker_id, hψ]
    exact (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)).symm
  exact ggRootCentDerivedAtQ_of_model (π := MonoidHom.id _) Function.surjective_id hker'
    Nat.prime_three (by norm_num) (hcz.conj u)

end TagsF4

section TagsE

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

theorem ggRootCentDerivedQTag_E8 : GGRootCentDerivedQTag .E8 := by
  intro G _ _ n f ψ _ _ hker hC _ _ r hr
  have hψ := AutSt.ker_eq_center hker hC
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hr2
  have hγ' : IsRoot .E8 γ := mem_adjDatum_roots.mp hγ
  have hcz : GGRootCentQL z := RootCentQL.of_mem_rootGroup (K := GaloisField 2 f) _
    (RootCentQL.single_E8 _ (RootCentQL.xPar_e8HighRoot _)) hγ' hz hz1
  have hker' : (MonoidHom.id (ggU .E8 n f).K).ker = ψ.ker := by
    rw [MonoidHom.ker_id, hψ]
    exact (center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)).symm
  exact ggRootCentDerivedAtQ_of_model (π := MonoidHom.id _) Function.surjective_id hker'
    Nat.prime_three (by norm_num) (hcz.conj u)

theorem ggRootCentDerivedQTag_E7 : GGRootCentDerivedQTag .E7 := by
  intro G _ _ n f ψ _ _ hker hC _ _ r hr
  have hψ := AutSt.ker_eq_center hker hC
  have hπker : (e7Isogeny (GaloisField 2 f)).ker = ψ.ker :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e7Isogeny_ker_eq_center.trans hψ.symm
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : e7Isogeny (GaloisField 2 f) z ≠ 1 := by
    intro h
    have hk : z ∈ ψ.ker := hπker ▸ (MonoidHom.mem_ker.mpr h)
    rw [MonoidHom.mem_ker] at hk
    rw [map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hcz := (RootCentQL.e7Isogeny_qL hγ hz hz1).conj (e7Isogeny (GaloisField 2 f) u)
  have e : e7Isogeny (GaloisField 2 f) (u * z * u⁻¹) = e7Isogeny (GaloisField 2 f) u *
      e7Isogeny (GaloisField 2 f) z * (e7Isogeny (GaloisField 2 f) u)⁻¹ := by
    erw [map_mul, map_mul, map_inv]
  rw [← e] at hcz
  exact ggRootCentDerivedAtQ_of_model (e7Isogeny_surjective _) hπker Nat.prime_three
    (by norm_num) hcz

theorem ggRootCentDerivedQTag_E6 : GGRootCentDerivedQTag .E6 := by
  intro G _ _ n f ψ _ _ hker hC _ _ r hr
  have hψ := AutSt.ker_eq_center hker hC
  have hπker : (e6Isogeny (GaloisField 2 f)).ker = ψ.ker :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center.trans hψ.symm
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : e6Isogeny (GaloisField 2 f) z ≠ 1 := by
    intro h
    have hk : z ∈ ψ.ker := hπker ▸ (MonoidHom.mem_ker.mpr h)
    rw [MonoidHom.mem_ker] at hk
    rw [map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hcz := (RootCentQL.e6Isogeny_qL hγ hz hz1).conj (e6Isogeny (GaloisField 2 f) u)
  have e : e6Isogeny (GaloisField 2 f) (u * z * u⁻¹) = e6Isogeny (GaloisField 2 f) u *
      e6Isogeny (GaloisField 2 f) z * (e6Isogeny (GaloisField 2 f) u)⁻¹ := by
    erw [map_mul, map_mul, map_inv]
  rw [← e] at hcz
  exact ggRootCentDerivedAtQ_of_model (e6Isogeny_surjective _) hπker Nat.prime_three
    (by norm_num) hcz

end TagsE

section TwE6

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Chevalley.E6GraphHighestRoot

namespace RootCentQL

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.SeitzReduction CFSG.SeitzReduction.TwistedE6Pilot
  RootCentExc

theorem derivedAtQ_twE6 {f : ℕ} (hf : 1 ≤ f) {G : Type} [Group G] [Finite G]
    (ψ : twistedE6Group 2 f →* G) (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {u z : twistedE6Group 2 f}
    (hz1 : ψ (u * z * u⁻¹) ≠ 1)
    (hzx : ∃ (x : twistedE6Group 2 f) (c : GaloisField 2 (2 * f)), frobQ 2 f c = c ∧
      ((x⁻¹ * z * x : twistedE6Group 2 f) : e6Data_valid.minGroup (GaloisField 2 (2 * f))) =
        e6Data_valid.xm _ RootCentExc.e6HighRoot c) :
    GGRootCentDerivedAtQ p ψ.range (ψ (u * z * u⁻¹)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have h2 : (2 : GaloisField 2 (2 * f)) = 0 := CharTwo.two_eq_zero
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobeniusEquiv_def _ 2 f c
  have hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f :=
    RingHom.ext fun c => by
      change iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = frobQ 2 f c
      rw [hσ, frobQ_apply]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hder, hZ, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf
      (GaloisField 2 (2 * f)) hK (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσ
  have hH : ⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f),
      twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆ =
      twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) := by
    rw [← hσθ]
    exact hder
  let π := (MulEquiv.subgroupCongr hH).toMonoidHom.comp (twistedE6Isogeny 2 f hf)
  have hπ : Function.Surjective π :=
    (MulEquiv.subgroupCongr hH).surjective.comp (twistedE6Isogeny_surjective 2 f hf)
  have hπvalT : ∀ z, ((π z : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) :=
    fun _ => rfl
  have hπker : π.ker = ψ.ker := by
    rw [AutSt.ker_eq_center hker hC]
    refine le_antisymm (RootDetectTwE6.ker_le_center f π hπvalT) fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have hzc := RootCentExc.map_mem_center_of_surjective hπ hz
    rw [hZ, Subgroup.mem_bot] at hzc
    exact hzc
  obtain ⟨x, c, hcθ, hc⟩ := hzx
  have hπz : ((π (x⁻¹ * z * x) : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot c := by
    rw [hπvalT, hc]
    change ((e6Isogeny (GaloisField 2 (2 * f)) (e6Data_valid.xm _ RootCentExc.e6HighRoot c) :
      adjointGroup .E6 (GaloisField 2 (2 * f))) : ModGL .E6 (GaloisField 2 (2 * f))) =
        pinnedX .E6 (GaloisField 2 (2 * f)) RootCentExc.e6HighRoot c
    rw [e6Isogeny_xm _ RootCentExc.isRoot_e6HighRoot, yPar,
      RootCentExc.coe_xPar_eq_pinnedX h2 _ RootCentExc.isRoot_e6HighRoot]
    have hδ : (relSignOr (rootOperatorFamily .E6) e6AdjData_valid RootCentExc.e6HighRoot :
        GaloisField 2 (2 * f)) = 1 := by
      have hm := relSignOr_mul_self (F := rootOperatorFamily .E6) (hD := e6AdjData_valid)
        (k := GaloisField 2 (2 * f)) RootCentExc.e6HighRoot
      set ε := (relSignOr (rootOperatorFamily .E6) e6AdjData_valid RootCentExc.e6HighRoot :
        GaloisField 2 (2 * f))
      have h' : (ε - 1) ^ 2 = 0 := by linear_combination hm + (1 - ε) * h2
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h')
    rw [hδ, one_mul]
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 : x⁻¹ * z * x = 1 := Subtype.ext (by rw [hc, MinData.Valid.xm_zero]; rfl)
    have hz1' : z = 1 := by
      calc z = x * (x⁻¹ * z * x) * x⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [hz1', mul_one, mul_inv_cancel, map_one] at hz1
    exact hz1 rfl
  have hcσ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom c = c := by
    rw [hσθ]
    exact hcθ
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ι⟩ := CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card hf hk hK
  let _ : Algebra (GaloisField 2 f) (GaloisField 2 (2 * f)) := ι.toAlgebra
  have hmem := (π (x⁻¹ * z * x)).2
  rw [hπz] at hmem
  have hcent := RootCentQL.pinnedX_highRoot_twE6 (k := GaloisField 2 f) hf hk hK
    (σ := (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom) hσ hc0 hcσ hmem
  have he : (⟨_, hmem⟩ : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) = π (x⁻¹ * z * x) :=
    Subtype.ext hπz.symm
  rw [he] at hcent
  have hw := hcent.conj (π (u * x))
  have e : π (u * x) * π (x⁻¹ * z * x) * (π (u * x))⁻¹ = π (u * z * u⁻¹) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  rw [e] at hw
  exact ggRootCentDerivedAtQ_of_model hπ hπker hp hp2 hw

end RootCentQL

theorem ggRootCentDerivedQTag_twistedE6 : GGRootCentDerivedQTag .twistedE6 := by
  intro G _ _ n f ψ hadm _ hker hC _ _ r hr
  obtain ⟨-, hf, -⟩ := hadm
  obtain ⟨hr2, γ, ⟨hγ, hlong⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  obtain ⟨w, γ₀, hγ₀, hmax, hγw⟩ := hlong (Or.inr (Or.inr rfl))
  have hγ₀' : IsRoot .F4 γ₀ := isRoot_of_mem_twistedDatum_roots _ hγ₀
  have hγ₀eq : γ₀ = RootCentExc.f4HighRoot := RootCentExc.eq_f4HighRoot_of_le hγ₀'
    (hmax RootCentExc.f4HighRoot (by
      change RootCentExc.f4HighRoot ∈ (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).roots
      rw [twistedDatum_roots]
      exact RootCentExc.isRoot_f4HighRoot))
  subst hγ₀eq
  subst hγw
  have hz1 : ψ (u * z * u⁻¹) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  exact RootCentQL.derivedAtQ_twE6 hf ψ hker hC Nat.prime_three (by norm_num) hz1
    (RootCentExc.exists_conj_xm_highRoot_twE6 hf w hz)

end TwE6

end CFSG.StandardType
