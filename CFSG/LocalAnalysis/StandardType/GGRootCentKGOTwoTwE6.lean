module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoExc
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoTwE6Step
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootExcTwE6
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListBasic
public import CFSG.LieType.Steinberg.Isogeny.E6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.SeitzReduction CFSG.SeitzReduction.TwistedE6Pilot RootCentExc
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Minuscule

namespace KGTwE6

section Model

variable {f : ℕ} {G : Type} [Group G] [Finite G]


private theorem exists_twE6_model (hf : 1 ≤ f) {ψ : twistedE6Group 2 f →* G}
    (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    ∃ (ψbar : twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) →* G)
      (π : twistedE6Group 2 f →* twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)),
      Function.Injective ψbar ∧ ψbar.range = ψ.range ∧ Function.Surjective π ∧
      π.ker = ψ.ker ∧ (∀ x, ψbar (π x) = ψ x) ∧
      (∀ z, ((π z : twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        ((e6IsogenyT (GaloisField 2 (2 * f))
          (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f) :=
    fun c => iterateFrobeniusEquiv_def _ 2 f c
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hder, hZ, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf
      (GaloisField 2 (2 * f)) hK (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσ
  have hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f :=
    RingHom.ext fun c => by
      change iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = frobQ 2 f c
      rw [hσ, frobQ_apply]
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
  haveI : ψ.ker.Normal := MonoidHom.normal_ker ψ
  let eC : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) ≃*
      twistedE6Group 2 f ⧸ ψ.ker :=
    (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hπker)
  let ψbar : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) →* G :=
    (QuotientGroup.kerLift ψ).comp eC.toMonoidHom
  have hcomp : ∀ x, ψbar (π x) = ψ x := by
    intro x
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π x) =
        (QuotientGroup.mk x : twistedE6Group 2 f ⧸ π.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [ψbar, eC, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp,
      Function.comp_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.kerLift_mk]
  refine ⟨ψbar, π, (QuotientGroup.kerLift_injective ψ).comp eC.injective, ?_, hπ, hπker, hcomp,
    hπvalT⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := hπ x
    rw [hcomp]
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨π a, hcomp a⟩

end Model

section Helper

variable {f : ℕ} {G : Type} [Group G] [Finite G]


private theorem pi_conj_xm_eq_pinnedX {f : ℕ}
    {π : twistedE6Group 2 f →* twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)}
    (hπvalT : ∀ z, ((π z : twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        ((e6IsogenyT (GaloisField 2 (2 * f))
          (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
    {x z : twistedE6Group 2 f} {c : GaloisField 2 (2 * f)}
    (hc : ((x⁻¹ * z * x : twistedE6Group 2 f) :
      e6Data_valid.minGroup (GaloisField 2 (2 * f))) =
        e6Data_valid.xm _ RootCentExc.e6HighRoot c) :
    ((π (x⁻¹ * z * x) : twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot c := by
  have h2 : (2 : GaloisField 2 (2 * f)) = 0 := CharTwo.two_eq_zero
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

private theorem exists_conj_pinnedX_one_torus {f : ℕ} {c : GaloisField 2 (2 * f)}
    (hc : c ≠ 0)
    (hcσ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom c = c) :
    ∃ s ∈ graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f),
      s * pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot c * s⁻¹ =
        pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot 1 := by
  obtain ⟨h, hh, -, hconj⟩ := exists_twistedE6_torus_conj_frame_prod
    (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom
    (F := [e6HighestRoot]) (fun γ hγ => by
      rw [List.mem_singleton] at hγ
      subst hγ
      exact ⟨isRoot_e6HighestRoot, permLattice_e6HighestRoot⟩)
    (List.pairwise_singleton _ _) (fun _ => c) (fun γ _ => ⟨hc, hcσ⟩)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hconj
  exact ⟨h, hh, hconj⟩

private theorem exists_twE6_model_pinnedX (hf : 1 ≤ f) {ψ : twistedE6Group 2 f →* G}
    (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {u x z : twistedE6Group 2 f}
    {c : GaloisField 2 (2 * f)} (hcθ : frobQ 2 f c = c)
    (hc : ((x⁻¹ * z * x : twistedE6Group 2 f) :
      e6Data_valid.minGroup (GaloisField 2 (2 * f))) =
        e6Data_valid.xm _ RootCentExc.e6HighRoot c)
    (hz1 : ψ (u * z * u⁻¹) ≠ 1) :
    ∃ (ψbar : twistedE6RootGroup (GaloisField 2 (2 * f))
          (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) →* G)
      (π : twistedE6Group 2 f →* twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))
      (hmem : pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot c ∈
        graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)),
      Function.Injective ψbar ∧ ψbar.range = ψ.range ∧ (∀ y, ψbar (π y) = ψ y) ∧
      (((π (x⁻¹ * z * x) : twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot c) ∧ c ≠ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψbar, π, hψbar_inj, hψbar_range, hπ, hπker, hcomp, hπvalT⟩ :=
    exists_twE6_model (f := f) (G := G) hf hker hC
  have hπz : ((π (x⁻¹ * z * x) : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot c :=
    pi_conj_xm_eq_pinnedX hπvalT hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 : x⁻¹ * z * x = 1 := Subtype.ext (by rw [hc, MinData.Valid.xm_zero]; rfl)
    have hz1' : z = 1 := by
      calc z = x * (x⁻¹ * z * x) * x⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [hz1', mul_one, mul_inv_cancel, map_one] at hz1
    exact hz1 rfl
  have hmem : pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot c ∈
      graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) := by
    have h := (π (x⁻¹ * z * x)).2
    rwa [hπz] at h
  exact ⟨ψbar, π, hmem, hψbar_inj, hψbar_range, hcomp, hπz, hc0⟩

private theorem exists_conj_pinnedX_one_of_model {f : ℕ} {c : GaloisField 2 (2 * f)}
    {π : twistedE6Group 2 f →* twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)}
    {x z : twistedE6Group 2 f}
    (hπz : (((π (x⁻¹ * z * x) : twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot c))
    (hc0 : c ≠ 0)
    (hcσ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom c = c) :
    ∃ s' : twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f),
      (((s' * π (x⁻¹ * z * x) * s'⁻¹ : twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot 1) := by
  obtain ⟨s, hs, hconj⟩ := exists_conj_pinnedX_one_torus hc0 hcσ
  refine ⟨⟨s, hs⟩, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hπz]
  exact hconj

private theorem psi_conj_eq {f : ℕ} {ψ : twistedE6Group 2 f →* G}
    {ψbar : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) →* G}
    {π : twistedE6Group 2 f →* twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)}
    (hcomp : ∀ y, ψbar (π y) = ψ y) {u x z : twistedE6Group 2 f}
    {s' : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)} :
    ψ (u * z * u⁻¹) =
      ψbar (MulAut.conj (π (u * x) * s'⁻¹) (s' * π (x⁻¹ * z * x) * s'⁻¹)) := by
  rw [MulAut.conj_apply, ← hcomp]
  congr 1
  have h1 : π (u * x) * s'⁻¹ * (s' * π (x⁻¹ * z * x) * s'⁻¹) * (π (u * x) * s'⁻¹)⁻¹ =
      π (u * x) * π (x⁻¹ * z * x) * (π (u * x))⁻¹ := by group
  have h2 : π ((u * x) * (x⁻¹ * z * x) * (u * x)⁻¹) =
      π (u * x) * π (x⁻¹ * z * x) * (π (u * x))⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [h1, ← h2]
  congr 1
  group

theorem pCoreOf_le_range_twE6_of_conj (hf : 1 ≤ f) (ψ : twistedE6Group 2 f →* G)
    (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {u z : twistedE6Group 2 f}
    (hz1 : ψ (u * z * u⁻¹) ≠ 1)
    (hzx : ∃ (x : twistedE6Group 2 f) (c : GaloisField 2 (2 * f)), frobQ 2 f c = c ∧
      ((x⁻¹ * z * x : twistedE6Group 2 f) : e6Data_valid.minGroup (GaloisField 2 (2 * f))) =
        e6Data_valid.xm _ RootCentExc.e6HighRoot c) :
    pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ (u * z * u⁻¹)}) ≤ ψ.range := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobeniusEquiv_def _ 2 f c
  obtain ⟨x, c, hcθ, hc⟩ := hzx
  obtain ⟨ψbar, π, hmem, hψbar_inj, hψbar_range, hcomp, hπz, hc0⟩ :=
    exists_twE6_model_pinnedX hf hker hC hcθ hc hz1
  have hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f :=
    RingHom.ext fun y => by
      change iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f y = frobQ 2 f y
      rw [iterateFrobeniusEquiv_def, frobQ_apply]
  have hcσ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom c = c := by
    rw [hσθ]
    exact hcθ
  obtain ⟨s', ht⟩ := exists_conj_pinnedX_one_of_model (c := c) hπz hc0 hcσ
  have hCbar : Subgroup.centralizer (ψbar.range : Set G) = ⊥ := by
    rw [hψbar_range]
    exact hC
  have hO : KGExc.OTwoFaithful (s' * π (x⁻¹ * z * x) * s'⁻¹) := by
    intro G' _ ψ' hψ' hC'
    exact pCoreOf_le_range_of_highRoot_twE6
      (σ := iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hf hK hσ hψ' hC' ht
  have hOt' : KGExc.OTwoFaithful
      (MulAut.conj (π (u * x) * s'⁻¹) (s' * π (x⁻¹ * z * x) * s'⁻¹)) :=
    hO.map (MulAut.conj (π (u * x) * s'⁻¹))
  have hconcl := hOt' G ψbar hψbar_inj hCbar
  have hval := psi_conj_eq (f := f) hcomp (u := u) (x := x) (z := z) (s' := s')
  rw [hψbar_range, ← hval] at hconcl
  exact hconcl

end Helper

end KGTwE6

section Tag


theorem ggRootCentOTwoTag_twistedE6 : GGRootCentOTwoTag .twistedE6 := by
  intro G _ _ n f ψ hadm _ hker _ _ hC _ r hr _
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
  exact KGTwE6.pCoreOf_le_range_twE6_of_conj hf ψ hker hC hz1
    (RootCentExc.exists_conj_xm_highRoot_twE6 hf w hz)

end Tag

end CFSG.StandardType
