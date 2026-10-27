module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcTwE6
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcTwE6Cent
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcConj
public import CFSG.LocalAnalysis.StandardType.GGRootDetectTwE6
public import CFSG.LieType.Steinberg.TwistedE6.Generation
public import CFSG.LieType.Steinberg.TwistedE6.Datum
public import CFSG.LieType.Steinberg.BruhatWeyl
public import CFSG.LieType.Chevalley.E6GraphFullDiagonalCoset

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Chevalley.E6GraphHighestRoot

namespace RootCentExc

theorem eq_f4HighRoot_of_le {γ : Fin Tag.F4.rank → ℤ}
    (hγ : IsRoot .F4 γ) (h : ∑ i, f4HighRoot i ≤ ∑ i, γ i) : γ = f4HighRoot := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hγ
  have hall : (List.range Tag.F4.rootCertificate.roots.length).all fun k =>
      decide (∑ i, f4HighRoot i ≤ ∑ i, Tag.F4.rootCertificate.root k i →
        Tag.F4.rootCertificate.root k = f4HighRoot) := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
  exact hall k hk h

theorem proj_e6HighRoot : proj e6HighRoot = f4HighRoot := by
  decide +kernel

theorem rho_e6HighRoot : rho e6HighRoot = e6HighRoot := by
  decide +kernel

theorem map_mem_center_of_surjective {A B : Type*} [Group A] [Group B] {φ : A →* B}
    (hφ : Function.Surjective φ) {z : A} (hz : z ∈ Subgroup.center A) :
    φ z ∈ Subgroup.center B := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨y', rfl⟩ := hφ y
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y']

end RootCentExc

section TwE6


theorem RootCentExc.exists_conj_xm_highRoot_twE6 {f : ℕ} (hf : 1 ≤ f)
    (w : (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)).Group)
    {z : twistedE6Group 2 f}
    (hz : z ∈ twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f)
      (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w RootCentExc.f4HighRoot)) :
    ∃ (x : twistedE6Group 2 f) (c : GaloisField 2 (2 * f)), frobQ 2 f c = c ∧
      ((x⁻¹ * z * x : twistedE6Group 2 f) : e6Data_valid.minGroup (GaloisField 2 (2 * f))) =
        e6Data_valid.xm _ RootCentExc.e6HighRoot c := by
  have hct := twistedDatum_isCTGroupDatum (frobQ 2 f) (frobQ_frobQ 2 f hf)
    (iSup_twistedDatum_rootGroup (frobQ 2 f) (frobQ_frobQ 2 f hf))
  have hroot : weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w RootCentExc.f4HighRoot ∈
      (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).roots := by
    rw [twistedDatum_roots]
    exact IsRoot.smul RootCentExc.isRoot_f4HighRoot w
  have h := (actsAs_nrep hct w).inv_conj_mem hroot hz
  have e : weylAction (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).isFiniteType w⁻¹
      (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w RootCentExc.f4HighRoot) =
        RootCentExc.f4HighRoot := by
    change (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w⁻¹ *
      weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w) RootCentExc.f4HighRoot = _
    rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [e] at h
  obtain ⟨c, hcθ, hc⟩ := (mem_twistedRootGroup_iff_of_fixed (frobQ 2 f)
    RootCentExc.isRoot_e6HighRoot RootCentExc.proj_e6HighRoot RootCentExc.rho_e6HighRoot _).1 h
  exact ⟨_, c, hcθ, hc⟩

theorem RootCentExc.inf_centralizer_le_twE6 {f : ℕ} (hf : 1 ≤ f) {G : Type} [Group G]
    (ψ : twistedE6Group 2 f →* G) (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {u z : twistedE6Group 2 f}
    (hz1 : ψ (u * z * u⁻¹) ≠ 1)
    (hzx : ∃ (x : twistedE6Group 2 f) (c : GaloisField 2 (2 * f)), frobQ 2 f c = c ∧
      ((x⁻¹ * z * x : twistedE6Group 2 f) : e6Data_valid.minGroup (GaloisField 2 (2 * f))) =
        e6Data_valid.xm _ RootCentExc.e6HighRoot c) :
    ψ.range ⊓ Subgroup.centralizer {ψ (u * z * u⁻¹)} ≤
      ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {ψ (u * z * u⁻¹)}) := by
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
  have hcent := RootCentExc.centTwoGen_pinnedX_highRoot (k := GaloisField 2 f) hf hk hK
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
  exact RootCentExc.inf_centralizer_le_of_model hπ hπker hw

theorem ggTwE6RootCentralizerTwoGenInput_holds : GGTwE6RootCentralizerTwoGenInput := by
  intro G _ _ n f ψ hadm hker hC r hr
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
  exact RootCentExc.inf_centralizer_le_twE6 hf ψ hker hC hz1
    (RootCentExc.exists_conj_xm_highRoot_twE6 hf w hz)

theorem ggRootCentralizerCyclicTag_twistedE6_of_cyclic (h : GGTwE6InnerDiagCyclicInput) :
    GGRootCentralizerCyclicTag .twistedE6 :=
  ggRootCentralizerCyclicTag_twistedE6_of_inputs ggTwE6RootCentralizerTwoGenInput_holds h

end TwE6

end CFSG.StandardType
