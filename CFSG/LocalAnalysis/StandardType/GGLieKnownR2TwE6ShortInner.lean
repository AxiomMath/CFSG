module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NPanel
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NThmA
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NTor
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Transport
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6ShortTorus
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LieType.Chevalley.EvenExceptionalActorCoverage
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center

public section

namespace CFSG.StandardType.LieKnownR2.TwE6

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.LieKnownR2.Short
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed CFSG.SeitzReduction.TwistedE6Pilot
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

private theorem l10sw2_transport
    {f : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2] (hf : 2 ≤ f)
    (hK : Nat.card k = (2 ^ f) ^ 2) (θ : k →+* k) (hσ : ∀ c, θ c = c ^ (2 ^ f)) :
    Subgroup.normalizer
        ((((twistedDatum k θ).rootGroup twE6Alpha).map
          (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC (by omega) hK θ hσ) :
          Subgroup (graphFixedRootGroup TwistTag.E6 k θ)) :
          Set (graphFixedRootGroup TwistTag.E6 k θ)) ≤
      Subgroup.normalizer
        (((twE6Rad θ).map
          (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC (by omega) hK θ hσ) :
          Subgroup (graphFixedRootGroup TwistTag.E6 k θ)) :
          Set (graphFixedRootGroup TwistTag.E6 k θ)) ∧
    pCoreOf 2 (Subgroup.normalizer
        ((((twistedDatum k θ).rootGroup twE6Alpha).map
          (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC (by omega) hK θ hσ) :
          Subgroup (graphFixedRootGroup TwistTag.E6 k θ)) :
          Set (graphFixedRootGroup TwistTag.E6 k θ))) =
      (twE6Rad θ).map (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC (by omega) hK θ hσ) := by
  have hf1 : 1 ≤ f := by omega
  set π : fixedGroup k θ →* graphFixedRootGroup TwistTag.E6 k θ :=
    CFSG.SeitzReduction.F4Pilot.twistedIsogenyC (by omega) hK θ hσ with hπdef
  have hker_eq : π.ker = Subgroup.center (fixedGroup k θ) := by
    rw [hπdef]; exact CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC hf1 hK θ hσ
  have hodd : Odd (Nat.card π.ker) := by
    rw [hker_eq, (CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup
      (θ := θ) (q := 2 ^ f) hK hσ).1]
    rcases (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 (2 ^ f + 1)) with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hker : π.ker ≤ Subgroup.center (fixedGroup k θ) := hker_eq.le
  have hsurj : π.range = ⊤ := by
    rw [hπdef]
    exact MonoidHom.range_eq_top.2
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC_surjective hf1 hK θ hσ)
  have hθ : ∀ c, θ (θ c) = c :=
    CFSG.SeitzReduction.F4Pilot.involutive_of_natCard_eq hK hσ
  have hIT : TorusRegularAlpha3 θ := by
    have hunit : ∃ t : kˣ, (t : k) ≠ 1 := by
      haveI : Fintype kˣ := Fintype.ofFinite kˣ
      have hcard : 1 < Fintype.card kˣ := by
        rw [← Nat.card_eq_fintype_card, Nat.card_units]
        have h4 : 4 ≤ 2 ^ f := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
        have h16 : 16 ≤ (2 ^ f) ^ 2 := by
          calc (16 : ℕ) = 4 * 4 := by norm_num
            _ ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul h4 h4
            _ = (2 ^ f) ^ 2 := by ring
        have h15 : 15 ≤ Nat.card k := by rw [hK]; omega
        omega
      obtain ⟨t, ht⟩ := Fintype.exists_ne_of_one_lt_card hcard (1 : kˣ)
      exact ⟨t, fun h => ht (Units.ext h)⟩
    obtain ⟨t, ht⟩ := hunit
    have ht2 : (t : k) ^ 2 ≠ 1 := by
      intro h
      apply ht
      have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
      have hneg : (1 : k) = -1 := by
        rw [eq_neg_iff_add_eq_zero]
        have : (1 : k) + 1 = 2 := by norm_num
        rw [this]; exact h2
      have hsqt : ((t : k) - 1) ^ 2 = (t : k) ^ 2 - 1 := by rw [sub_sq, h2, hneg]; ring
      have hzero : ((t : k) - 1) ^ 2 = 0 := by rw [hsqt, h]; ring
      have hsub : (t : k) - 1 = 0 := (sq_eq_zero_iff).1 hzero
      exact sub_eq_zero.mp hsub
    exact torusRegularAlpha3 θ hθ (t := t) ht2
  have hγ : twE6Alpha ∈ (twistedDatum k θ).roots := twE6_alpha_mem_roots θ
  have hS : IsPGroup 2 (twE6RA θ) := isPGroup_two_twistedRootGroup θ hγ
  have hQ : IsPGroup 2 (twE6Rad θ) := isPGroup_two_twE6Rad θ hθ
  have hmapS := CFSG.StandardType.LieKnownR2.map_normalizer_eq_range_inf_normalizer_map
    (ψ := π) hker hodd hS
  have hmapQ := CFSG.StandardType.LieKnownR2.map_normalizer_eq_range_inf_normalizer_map
    (ψ := π) hker hodd hQ
  constructor
  · intro g hg
    have hA := CFSG.StandardType.LieKnownR2.Short.twE6_normalizer_alpha_le θ hθ
    have hmapA : (Subgroup.normalizer (twE6RA θ : Set (fixedGroup k θ))).map π ≤
        ((Subgroup.normalizer (twE6Rad θ : Set (fixedGroup k θ))).map π) :=
      Subgroup.map_mono hA
    have h1 : g ∈ (Subgroup.normalizer (twE6RA θ : Set (fixedGroup k θ))).map π := by
      rw [hmapS, hsurj, top_inf_eq]; exact hg
    have h2 := hmapA h1
    rw [hmapQ, hsurj, top_inf_eq] at h2
    exact h2
  · have hN : Subgroup.normalizer ((twE6RA θ).map π :
        Set (graphFixedRootGroup TwistTag.E6 k θ)) =
        (Subgroup.normalizer (twE6RA θ : Set (fixedGroup k θ))).map π := by
      rw [hmapS, hsurj, top_inf_eq]
    rw [hN]
    have hM : π.ker ≤ Subgroup.normalizer (twE6RA θ : Set (fixedGroup k θ)) :=
      hker.trans (Subgroup.center_le_normalizer (twE6RA θ : Set (fixedGroup k θ)))
    rw [← CFSG.StandardType.LieKnownR2.map_pCoreOf_eq_of_odd_central_ker
      (ψ := π) hker hodd hM]
    rw [twE6_pCoreOf_normalizer_alpha_eq θ hθ hIT]

private theorem l10sw2_exists_conj {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {t : G}
    (htQ : t ∈ Subgroup.normalizer (Q : Set G)) (hC : ∀ x ∈ Q, x * t = t * x → x = 1)
    {z : G} (hz : z * t⁻¹ ∈ Q) : ∃ x ∈ Q, z = x * t * x⁻¹ := by
  have hmem : ∀ x : Q, (x : G) * (t * (x : G)⁻¹ * t⁻¹) ∈ Q := fun x =>
    Q.mul_mem x.2 ((Subgroup.mem_normalizer_iff.1 htQ _).1 (Q.inv_mem x.2))
  let φ : Q → Q := fun x => ⟨(x : G) * (t * (x : G)⁻¹ * t⁻¹), hmem x⟩
  have hinj : Function.Injective φ := by
    intro x x' h
    have h' : (x : G) * (t * (x : G)⁻¹ * t⁻¹) = (x' : G) * (t * (x' : G)⁻¹ * t⁻¹) :=
      congrArg Subtype.val h
    have h2 : (x : G) * t * (x : G)⁻¹ = (x' : G) * t * (x' : G)⁻¹ := by
      calc (x : G) * t * (x : G)⁻¹ = (x : G) * (t * (x : G)⁻¹ * t⁻¹) * t := by group
        _ = (x' : G) * (t * (x' : G)⁻¹ * t⁻¹) * t := by rw [h']
        _ = (x' : G) * t * (x' : G)⁻¹ := by group
    have hc : ((x' : G)⁻¹ * x) * t = t * ((x' : G)⁻¹ * x) := by
      calc ((x' : G)⁻¹ * x) * t = (x' : G)⁻¹ * ((x : G) * t * (x : G)⁻¹) * x := by group
        _ = (x' : G)⁻¹ * ((x' : G) * t * (x' : G)⁻¹) * x := by rw [h2]
        _ = t * ((x' : G)⁻¹ * x) := by group
    have h1 := hC _ (Q.mul_mem (Q.inv_mem x'.2) x.2) hc
    exact Subtype.ext (inv_mul_eq_one.1 h1).symm
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.1 hinj ⟨z * t⁻¹, hz⟩
  have hx' : (x : G) * (t * (x : G)⁻¹ * t⁻¹) = z * t⁻¹ := congrArg Subtype.val hx
  refine ⟨x, x.2, ?_⟩
  calc z = (z * t⁻¹) * t := by group
    _ = (x : G) * (t * (x : G)⁻¹ * t⁻¹) * t := by rw [hx']
    _ = (x : G) * t * (x : G)⁻¹ := by group

private theorem l10sw2_inner_of_odd {G : Type*} [Group G] (y y' : MulAut G) (x : G)
    (hyx : y = MulAut.conj x * y') (hy2 : ∃ n : ℕ, y ^ 2 ^ n = 1) {N : ℕ} (hN : Odd N)
    (hy'N : y' ^ N = 1) : ∃ w : G, y = MulAut.conj w := by
  obtain ⟨n, hn⟩ := hy2
  let φ : MulAut G →* CFSG.ComponentClassification.OuterAutomorphisms.Outer G :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner G)
  have hφy : φ y = φ y' := by
    rw [hyx, map_mul]
    have hconj : φ (MulAut.conj x) = 1 :=
      (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner G)
        (MulAut.conj x)).mpr ⟨x, rfl⟩
    rw [hconj, one_mul]
  have hdvd1 : orderOf (φ y) ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hn, map_one])
  have hdvd2 : orderOf (φ y) ∣ N := by
    rw [hφy]
    exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hy'N, map_one])
  have hcop : Nat.Coprime N (2 ^ n) := (Nat.coprime_two_right.2 hN).pow_right n
  have h1 : orderOf (φ y) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvd1
  have hyin : y ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G :=
    (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner G) y).mp
      (orderOf_eq_one_iff.mp h1)
  obtain ⟨w, hw⟩ := hyin
  exact ⟨w, hw.symm⟩

private theorem l10sw2_rootDiagUnit_pow {τ : Tag} {K : Type} [Field K] (l : Fin τ.rank → Kˣ)
    (N : ℕ) : rootDiagUnit τ l ^ N = rootDiagUnit τ (l ^ N) := by
  induction N with
  | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
  | succ N ih => rw [pow_succ, ih, ← rootDiagUnit_mul, pow_succ]

theorem ggRootNormInner_adj_twistedE6_shortHighest
    {f : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2] (hf : 2 ≤ f)
    (hK : Nat.card k = (2 ^ f) ^ 2) (θ : k →+* k) (hσ : ∀ c, θ c = c ^ (2 ^ f)) :
    GGRootNormInner (((twistedDatum k θ).rootGroup twE6Alpha).map
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC (by omega) hK θ hσ)) := by
  obtain ⟨σE, rfl⟩ := CFSG.SeitzReduction.TwistedE6Pilot.exists_ringEquiv_toRingHom_eq θ
  have hσE : ∀ c, σE c = c ^ 2 ^ f := hσ
  have hf1 : 1 ≤ f := by omega
  intro y hy2 _hyR hytriv
  obtain ⟨hNle, hO2⟩ := l10sw2_transport hf hK σE.toRingHom hσ
  obtain ⟨t, htN, htC, hRC0, htest⟩ := twE6_short_levelTorus_adj hf hK σE.toRingHom hσ
  have hyQ : ∀ n ∈ Subgroup.normalizer
      ((((twistedDatum k σE.toRingHom).rootGroup twE6Alpha).map
        (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf1 hK σE.toRingHom hσ) :
        Subgroup (graphFixedRootGroup TwistTag.E6 k σE.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.E6 k σE.toRingHom)),
      y n * n⁻¹ ∈ (twE6Rad σE.toRingHom).map
        (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf1 hK σE.toRingHom hσ) := by
    intro n hn
    rw [← hO2]
    exact hytriv n hn
  obtain ⟨x, hxQ, hxt⟩ := l10sw2_exists_conj (hNle htN) htC (hyQ t htN)
  set y' : MulAut (graphFixedRootGroup TwistTag.E6 k σE.toRingHom) := MulAut.conj x⁻¹ * y
    with hy'def
  have hy' : ∀ z, y' z = x⁻¹ * y z * x := fun z => by
    rw [hy'def, MulAut.mul_apply, MulAut.conj_apply, inv_inv]
  have hy't : y' t = t := by rw [hy', hxt]; group
  have hfix : ∀ z ∈ Subgroup.normalizer
      ((((twistedDatum k σE.toRingHom).rootGroup twE6Alpha).map
        (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf1 hK σE.toRingHom hσ) :
        Subgroup (graphFixedRootGroup TwistTag.E6 k σE.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.E6 k σE.toRingHom)), z * t = t * z → y' z = z := by
    intro z hz hzt
    have hrQ : y' z * z⁻¹ ∈ (twE6Rad σE.toRingHom).map
        (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf1 hK σE.toRingHom hσ) := by
      have e : y' z * z⁻¹ = x⁻¹ * (y z * z⁻¹) * (z * x * z⁻¹) := by rw [hy']; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxQ) (hyQ z hz))
        ((Subgroup.mem_normalizer_iff.1 (hNle hz) x).1 hxQ)
    have hc : Commute z t := hzt
    have h1 : Commute (y' z) t := by
      have e := congrArg y' hzt
      rw [map_mul, map_mul, hy't] at e
      exact e
    have hrt : Commute (y' z * z⁻¹) t := h1.mul_left hc.inv_left
    exact mul_inv_eq_one.1 (htC _ hrQ hrt)
  have hA := EvenExceptionalActorCoverage.fixedDiagonalFieldActors_E6_eq_top hf1 hK σE hσE
  obtain ⟨g, hg, a, -, δ, -, hβ⟩ :=
    ((Chevalley_diagonal_field_actor_data.2 TwistTag.E6 k σE).1 y').1 (hA ▸ Subgroup.mem_top y')
  let ι : graphFixedRootGroup TwistTag.E6 k σE.toRingHom → ModGL .E6 k :=
    fun z => (show ModGL .E6 k from z.1)
  let gE : ModGL .E6 k := (show ModGL .E6 k from g)
  have hβ' : ∀ z : graphFixedRootGroup TwistTag.E6 k σE.toRingHom,
      ι (y' z) = gE * rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) (ι z) *
        (rootDiagUnit .E6 a)⁻¹ * gE⁻¹ := hβ
  have hgx : ∀ {z : ModGL .E6 k} (hz : z ∈ graphFixedRootGroup TwistTag.E6 k σE.toRingHom),
      y' ⟨z, hz⟩ = ⟨z, hz⟩ →
      gE * (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) z *
        (rootDiagUnit .E6 a)⁻¹) * gE⁻¹ = z := by
    intro z hz h
    have e := congrArg ι h
    rw [hβ'] at e
    have e' : gE * rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) z *
        (rootDiagUnit .E6 a)⁻¹ * gE⁻¹ = z := e
    rw [show gE * (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) z *
        (rootDiagUnit .E6 a)⁻¹) * gE⁻¹ = gE * rootDiagUnit .E6 a *
          Units.map (entrywiseHom δ.toRingHom) z * (rootDiagUnit .E6 a)⁻¹ * gE⁻¹ by group]
    exact e'
  have hT : ∀ z : ModGL .E6 k, z ∈ omegaMinusLevi σE.toRingHom →
      z ∈ torusGroup TwistTag.E6.tag k →
      gE * (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) z *
        (rootDiagUnit .E6 a)⁻¹) * gE⁻¹ = z := by
    intro z hzL hzT
    have hzC := omegaMinusLevi_le_graphFixedRootGroup σE.toRingHom hzL
    obtain ⟨hzN, hzt⟩ := htest ⟨z, hzC⟩ (Or.inl ⟨hzL, hzT⟩)
    exact hgx hzC (hfix _ hzN hzt)
  have hσι : ∀ c : fixedSubfield σE.toRingHom,
      σE.toRingHom (algebraMap (fixedSubfield σE.toRingHom) k c) =
        algebraMap (fixedSubfield σE.toRingHom) k c := fun c => theta_coe σE.toRingHom c
  have hW : ∀ c : (fixedSubfield σE.toRingHom)ˣ,
      gE * (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom)
        (rootDiagUnit .E6 (d4CentralDiag
          (Units.map (algebraMap (fixedSubfield σE.toRingHom) k).toMonoidHom c)
          (Units.map (algebraMap (fixedSubfield σE.toRingHom) k).toMonoidHom c))) *
            (rootDiagUnit .E6 a)⁻¹) * gE⁻¹ =
          rootDiagUnit .E6 (d4CentralDiag
            (Units.map (algebraMap (fixedSubfield σE.toRingHom) k).toMonoidHom c)
            (Units.map (algebraMap (fixedSubfield σE.toRingHom) k).toMonoidHom c)) := by
    intro c
    have hmem : rootDiagUnit .E6 (d4CentralDiag
        (Units.map (algebraMap (fixedSubfield σE.toRingHom) k).toMonoidHom c)
        (Units.map (algebraMap (fixedSubfield σE.toRingHom) k).toMonoidHom c)) ∈
          shortRootTorus (algebraMap (fixedSubfield σE.toRingHom) k) := ⟨c, rfl⟩
    have hzC := shortRootTorus_le_C0 (σ := σE.toRingHom) hσι hmem
    obtain ⟨hzN, hzt⟩ := htest ⟨_, hzC⟩ (Or.inr (Or.inl hmem))
    exact hgx hzC (hfix _ hzN hzt)
  have hR : ∀ γ ∈ twE6ShortCoreRoots,
      gE * (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) (pinnedX .E6 k γ 1) *
        (rootDiagUnit .E6 a)⁻¹) * gE⁻¹ = pinnedX .E6 k γ 1 := by
    intro γ hγ
    have hzC := hRC0 γ hγ
    obtain ⟨hzN, hzt⟩ := htest ⟨_, hzC⟩ (Or.inr (Or.inr ⟨γ, hγ, rfl⟩))
    exact hgx hzC (hfix _ hzN hzt)
  have hk0 : Nat.card (fixedSubfield σE.toRingHom) = 2 ^ f :=
    card_fixedSubfield_of_card σE.toRingHom hK hσ
  have hgA : gE ∈ adjointGroup .E6 k := (graphFixedRootGroup_le _ _ _ hg).1
  obtain ⟨hδ1, hm⟩ := core_shortRoot (k := fixedSubfield σE.toRingHom) hf hk0 hK hσ hgA a δ hT hW hR
  have hδ : δ = RingEquiv.refl k := RingEquiv.ext hδ1
  subst hδ
  set m : ModGL .E6 k := gE * rootDiagUnit .E6 a with hmdef
  have hy'm : ∀ z : graphFixedRootGroup TwistTag.E6 k σE.toRingHom, ι (y' z) = m * ι z * m⁻¹ := by
    intro z
    have e1 : Units.map (entrywiseHom (RingEquiv.refl k).toRingHom) (ι z) = ι z :=
      Units.ext (entrywise_id _)
    rw [hβ' z, e1, hmdef]
    group
  obtain ⟨l, hl⟩ := hm
  have hmN : m ^ Nat.card kˣ = 1 := by
    rw [hl]
    have hl1 : l ^ Nat.card kˣ = 1 := funext fun i => pow_card_eq_one'
    have h := l10sw2_rootDiagUnit_pow (τ := Tag.E6) (K := k) l (Nat.card kˣ)
    rw [hl1, rootDiagUnit_one] at h
    exact h
  have hpow : ∀ N : ℕ, ∀ z : graphFixedRootGroup TwistTag.E6 k σE.toRingHom,
      ι ((y' ^ N) z) = m ^ N * ι z * (m ^ N)⁻¹ := by
    intro N
    induction N with
    | zero =>
      intro z
      show ι z = 1 * ι z * 1⁻¹
      group
    | succ N ih =>
      intro z
      rw [pow_succ', MulAut.mul_apply, hy'm, ih, pow_succ']
      group
  have hy'N : y' ^ Nat.card kˣ = 1 := by
    refine MulEquiv.ext fun z => Subtype.ext ?_
    have h := hpow (Nat.card kˣ) z
    rw [hmN, one_mul, inv_one, mul_one] at h
    exact h
  have hodd : Odd (Nat.card kˣ) := by
    rw [Nat.card_units, hK]
    have h4 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    have hpos : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    obtain ⟨m', hm'⟩ := h4
    rw [Nat.odd_iff]
    omega
  have hyx : y = MulAut.conj x * y' := by
    rw [hy'def, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  exact l10sw2_inner_of_odd y y' x hyx hy2 hodd hy'N

end CFSG.StandardType.LieKnownR2.TwE6
