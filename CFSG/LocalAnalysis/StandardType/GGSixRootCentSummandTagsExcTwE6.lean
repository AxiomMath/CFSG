module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsExcBasic
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcTwE6Root
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotNeighbourStandard

public section

namespace CFSG.StandardType

namespace RootCentQL

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.SeitzReduction CFSG.SeitzReduction.TwistedE6Pilot
  RootCentExc

section C0


variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem stdRepC_zero [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    GGRootCentQL (stdRepC (apply_apply_eq hK hσ) 0 : graphFixedRootGroup TwistTag.E6 K σ) := by
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ with hC₀
  have hC := centralizer_stdRepC_zero_eq (k := k) hf hk hK hσ
  have hct := centTwoGen_stdRepC_zero (k := k) hf hk hK hσ
  obtain ⟨-, hLN, -⟩ := centralizer_stdRep_zero_inf_eq (k := k) hf hk hK hσ
  have hQ2 : IsPGroup 2 ((tRadical σ).subgroupOf C₀) := by
    obtain ⟨-, hT⟩ := even_E6_graph_highest_root_normalizer f hf k K hk hK σ hσ
    obtain ⟨S, hS⟩ := hT.2.2.2.2.2.2.2.2.2.1
    refine S.isPGroup'.to_le ?_
    rw [hS]
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact mem_inf.2 ⟨parabolicRadical_le_posUnipotent _ (mem_inf.1 hx).1,
      graphFixedRootGroup_le _ _ _ x.2⟩
  have hLN' : (su6Levi σ).subgroupOf C₀ ≤ normalizer ((tRadical σ).subgroupOf C₀ : Set C₀) := by
    intro x hx
    rw [mem_subgroupOf] at hx
    rw [mem_normalizer_iff]
    intro y
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.1 (hLN hx) y
  exact ⟨_, _, hQ2, hC.symm, hLN', isQuasisimple_su6Levi_subgroupOf hf hk hK hσ,
    (le_sup_right.trans hC.ge).trans hct⟩

theorem pinnedX_highRoot_twE6 [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {c : K}
    (hc : c ≠ 0) (hcσ : σ c = c)
    (hmem : pinnedX TwistTag.E6.tag K e6HighestRoot c ∈ graphFixedRootGroup TwistTag.E6 K σ) :
    GGRootCentQL (⟨_, hmem⟩ : graphFixedRootGroup TwistTag.E6 K σ) := by
  have : Finite K := finite_of_card hK
  obtain ⟨h, hh, -, hconj⟩ := exists_twistedE6_torus_conj_frame_prod σ
    (F := [e6HighestRoot]) (fun γ hγ => by
      rw [List.mem_singleton] at hγ
      subst hγ
      exact ⟨isRoot_e6HighestRoot, permLattice_e6HighestRoot⟩)
    (List.pairwise_singleton _ _) (fun _ => c) (fun γ _ => ⟨hc, hcσ⟩)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hconj
  have e : (⟨h, hh⟩ : graphFixedRootGroup TwistTag.E6 K σ) * ⟨_, hmem⟩ * ⟨h, hh⟩⁻¹ =
      stdRepC (apply_apply_eq hK hσ) 0 := Subtype.ext hconj
  have h1 := stdRepC_zero (k := k) hf hk hK hσ
  rw [← e] at h1
  exact h1.of_conj

end C0

end RootCentQL

section TwE6

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Chevalley.E6GraphHighestRoot

theorem RootCentQL.derivedAt_twE6 {f : ℕ} (hf : 1 ≤ f) {G : Type} [Group G] [Finite G]
    (ψ : twistedE6Group 2 f →* G) (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {u z : twistedE6Group 2 f}
    (hz1 : ψ (u * z * u⁻¹) ≠ 1)
    (hzx : ∃ (x : twistedE6Group 2 f) (c : GaloisField 2 (2 * f)), frobQ 2 f c = c ∧
      ((x⁻¹ * z * x : twistedE6Group 2 f) : e6Data_valid.minGroup (GaloisField 2 (2 * f))) =
        e6Data_valid.xm _ RootCentExc.e6HighRoot c) :
    GGRootCentDerivedAt p ψ.range (ψ (u * z * u⁻¹)) := by
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
  exact ggRootCentDerivedAt_of_model hπ hπker hp hp2 hw

theorem ggRootCentDerivedTag_twistedE6 : GGRootCentDerivedTag .twistedE6 := by
  intro G _ _ p n f ψ hp hp2 hadm _ hker hC _ r hr
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
  exact RootCentQL.derivedAt_twE6 hf ψ hker hC hp hp2 hz1
    (RootCentExc.exists_conj_xm_highRoot_twE6 hf w hz)

end TwE6

end CFSG.StandardType
