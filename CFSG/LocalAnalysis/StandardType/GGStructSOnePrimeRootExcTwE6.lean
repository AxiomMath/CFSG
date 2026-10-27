module

public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootBasic
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsExcTwE6
public import CFSG.LieType.ChevTwo.Layered
public import CFSG.GH74.Generic.Context
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionPerfect
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5LayerSurj
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.RankThree.PartOne.KA5L.Final

public section

namespace CFSG.StandardType

open RootCentExc Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.SeitzReduction CFSG.SeitzReduction.TwistedE6Pilot
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.ChevTwo CFSG.Yardstones.Md0ec50421ce4

section Levi

variable {K : Type} [Field K] [CharP K 2]


theorem isChevTwoLayered_su6Levi_subgroupOf {f : ℕ} {k : Type} [Field k] [Algebra k K]
    (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsChevTwoLayered ↥((TwistedE6Pilot.su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)) := by
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ
  set L := (TwistedE6Pilot.su6Levi σ).subgroupOf C₀
  have hLq : CFSG.Open.IsQuasisimple ↥L :=
    ⟨(TwistedE6Pilot.isQuasisimple_su6Levi_subgroupOf hf hk hK hσ).1.commutator_eq_top,
      (TwistedE6Pilot.isQuasisimple_su6Levi_subgroupOf hf hk hK hσ).2.1⟩
  refine isChevTwoLayered_of_isQuasisimple hLq ?_
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, by omega⟩
  have hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [TauCeti.PrimePower.card_def]
  obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ :=
    CFSG.GH74.Generic.stated_of_lieModel_PSU
      (TwistedE6Pilot.lieModel_su6Levi_subgroupOf hf hk hK hσ)
  obtain ⟨eCat⟩ := CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.exists_catEquiv_statedProj
    (q := q) hv (ℓ := 2) (f := f) rfl rfl K' hK'
  have hchev : IsChevSimple 2 ↥L :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie
      ⟨.twistedA 5 q, hv⟩ (by rw [TauCeti.LieTypeIndex.characteristic_twistedA])
      (e.trans eCat.symm)
  haveI : IsSimpleGroup (TwistedE6Pilot.su6Levi σ) :=
    TwistedE6Pilot.isSimpleGroup_su6Levi hf hk hK hσ
  have hnc : ∃ a b : TwistedE6Pilot.su6Levi σ, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have := TwistedE6Pilot.isPerfect_su6Levi hf hk hK hσ
    exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b => hc a b⟩⟩
  have hZsu : Subgroup.center (TwistedE6Pilot.su6Levi σ) = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).2
  have hZ : Subgroup.center ↥L = ⊥ :=
    F4Pilot.center_eq_bot_congr
      (Subgroup.subgroupOfEquivOfLe (TwistedE6Pilot.su6Levi_le_graphFixedRootGroup σ)).symm hZsu
  let eZ : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact isChevSimple_of_mulEquiv eZ hchev

end Levi

section Base

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]


theorem stdRepC_zero_typed [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    GGRootCentQLTyped (stdRepC (apply_apply_eq hK hσ) 0 : graphFixedRootGroup TwistTag.E6 K σ) := by
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ with hC₀
  have hC := centralizer_stdRepC_zero_eq (k := k) hf hk hK hσ
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
  exact ⟨_, _, hQ2, hC.symm, hLN', isChevTwoLayered_su6Levi_subgroupOf hf hk hK hσ⟩

theorem pinnedX_highRoot_twE6_typed [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {c : K}
    (hc : c ≠ 0) (hcσ : σ c = c)
    (hmem : pinnedX TwistTag.E6.tag K e6HighestRoot c ∈ graphFixedRootGroup TwistTag.E6 K σ) :
    GGRootCentQLTyped (⟨_, hmem⟩ : graphFixedRootGroup TwistTag.E6 K σ) := by
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
  have h1 := stdRepC_zero_typed (k := k) hf hk hK hσ
  rw [← e] at h1
  exact h1.of_conj

end Base

section Tag


theorem derivedAt_twE6_typed {f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X] [Finite X]
    (ψ : twistedE6Group 2 f →* X) (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f))
    (hC : Subgroup.centralizer (ψ.range : Set X) = ⊥) {u z : twistedE6Group 2 f}
    (hz1 : ψ (u * z * u⁻¹) ≠ 1)
    (hzx : ∃ (x : twistedE6Group 2 f) (c : GaloisField 2 (2 * f)), frobQ 2 f c = c ∧
      ((x⁻¹ * z * x : twistedE6Group 2 f) : e6Data_valid.minGroup (GaloisField 2 (2 * f))) =
        e6Data_valid.xm _ RootCentExc.e6HighRoot c) :
    ∃ (C : Type) (_ : Group C) (π : twistedE6Group 2 f →* C) (w : twistedE6Group 2 f),
      Function.Surjective π ∧ π.ker = ψ.ker ∧ ψ w = ψ (u * z * u⁻¹) ∧
        GGRootCentQLTyped (π w) := by
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
  have hcent := pinnedX_highRoot_twE6_typed (k := GaloisField 2 f) hf hk hK
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
  exact ⟨_, inferInstance, π, u * z * u⁻¹, hπ, hπker, rfl, hw⟩

theorem ggRootInvolModelTypedTag_twistedE6 : GGRootInvolModelTypedTag .twistedE6 := by
  intro X _ _ n f ψ hadm hrank hker hC r hr
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
  exact derivedAt_twE6_typed hf ψ hker hC hz1
    (RootCentExc.exists_conj_xm_highRoot_twE6 hf w hz)

end Tag

end CFSG.StandardType
