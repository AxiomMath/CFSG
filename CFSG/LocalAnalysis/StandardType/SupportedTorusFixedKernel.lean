module

public import CFSG.LocalAnalysis.StandardType.CyclotomicBlockKernelOrder
public import CFSG.LocalAnalysis.StandardType.E8SubsystemBlockMatrix
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.HardMathSupport.Foote.Coordinator.LangTorus.Monomial
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.StandardType

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Foote.Coordinator (blockP)
open CFSG.HardMathSupport.Foote.Coordinator
  (supportedTorusHom_eq' conj_frob_rootDiagUnit weylTuple_pow_tupd monoHom_sub_one)
open CFSG.HardMathSupport.Lang.TwE6Step3 (monoHom monoHom_apply monoHom_monoHom)

section Torus

variable {τ : Tag} {Ω : Type} [Field Ω] {J : Set (Fin τ.rank)} [Fintype J] [DecidableEq J]

theorem supportedTorusHom_conj_twisted (hsym : τ.symmetrizer = 1) {Fr : Ω →+* Ω} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (n : ModGL τ Ω) (hnm : n ∈ monomialSubgroup τ Ω)
    (hJ : ∀ β ∈ parabolicRoots τ J, weylQuotientHom τ Ω ⟨n, hnm⟩ • β ∈ parabolicRoots τ J)
    (c : J → Ωˣ) :
    n * Units.map (entrywiseHom Fr) (supportedTorusHom τ Ω J c) * n⁻¹ =
      supportedTorusHom τ Ω J
        (monoHom ((q : ℤ) • blockP (weylQuotientHom τ Ω ⟨n, hnm⟩) J) c) := by
  have h1 : ∀ j : J, τ.symmetrizer j j = 1 := by
    intro j
    rw [hsym]
    simp
  have hcoe : (fun j : J => c j ^ τ.symmetrizer j j) = c := by
    funext j
    rw [h1 j, zpow_one]
  have hcoe' : (fun m : J =>
        (monoHom ((q : ℤ) • blockP (weylQuotientHom τ Ω ⟨n, hnm⟩) J) c m) ^
          τ.symmetrizer m m) =
      monoHom ((q : ℤ) • blockP (weylQuotientHom τ Ω ⟨n, hnm⟩) J) c := by
    funext m
    rw [h1 m, zpow_one]
  have key : n * Units.map (entrywiseHom Fr)
        (supportedTorusHom τ Ω J (fun j : J => c j ^ τ.symmetrizer j j)) * n⁻¹ =
      supportedTorusHom τ Ω J
        (fun m : J =>
          (monoHom ((q : ℤ) • blockP (weylQuotientHom τ Ω ⟨n, hnm⟩) J) c m) ^
            τ.symmetrizer m m) := by
    rw [supportedTorusHom_eq' J (fun j : J => c j ^ τ.symmetrizer j j),
      conj_frob_rootDiagUnit hFr n hnm, weylTuple_pow_tupd hJ,
      ← supportedTorusHom_eq' J]
  rw [hcoe, hcoe'] at key
  exact key

theorem supportedTorusHom_mem_rootSpan (c : J → Ωˣ) :
    supportedTorusHom τ Ω J c ∈ rootSpan τ Ω (parabolicRoots τ J) := by
  have h := supportedTorus_le_subsystemGroup (K := Ω) (τ := τ) J (supportedTorusHom_mem J c)
  rwa [subsystemGroup_eq_rootSpan] at h

theorem pow_det_eq_one_of_prod_cartan_eq_one (a : J → Ωˣ)
    (h : ∀ i : J, ∏ j : J, a j ^ τ.cartan j i = 1) (j : J) :
    a j ^ (cartanBlock τ J).det = 1 := by
  have hc : monoHom ((cartanBlock τ J)ᵀ) a = 1 := by
    funext i
    simpa only [Pi.one_apply, monoHom_apply, Matrix.transpose_apply, cartanBlock,
      Matrix.of_apply] using h i
  have hker := pow_eq_one_of_mem_ker_monoHom (A := (cartanBlock τ J)ᵀ)
    (B := ((cartanBlock τ J)ᵀ).adjugate) (N := ((cartanBlock τ J)ᵀ).det)
    (by rw [Matrix.adjugate_mul]) hc j
  rwa [Matrix.det_transpose] at hker

theorem eq_one_of_supportedTorusHom_eq_one (c : J → Ωˣ) {N : ℤ}
    (hN : ∀ j, c j ^ N = 1) (hcop : IsCoprime N (cartanBlock τ J).det)
    (h1 : supportedTorusHom τ Ω J c = 1) : c = 1 := by
  have hprod : ∀ i : J, ∏ j : J, c j ^ τ.cartan j i = 1 :=
    fun i => (supportedTorusHom_eq_one_iff J c).1 h1 i
  have hdet : ∀ j, c j ^ (cartanBlock τ J).det = 1 :=
    fun j => pow_det_eq_one_of_prod_cartan_eq_one c hprod j
  obtain ⟨a, b, hab⟩ := hcop
  funext j
  rw [Pi.one_apply]
  calc c j = c j ^ (a * N + b * (cartanBlock τ J).det) := by rw [hab, zpow_one]
    _ = 1 := by
      rw [_root_.zpow_add, mul_comm a, mul_comm b, _root_.zpow_mul, _root_.zpow_mul,
        hN j, hdet j]
      simp

theorem exists_subgroup_le_rootSpan_inf_twistedFixedPoints [IsAlgClosed Ω] (hsym : τ.symmetrizer = 1)
    {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (n : ModGL τ Ω)
    (hnm : n ∈ monomialSubgroup τ Ω)
    (hJ : ∀ β ∈ parabolicRoots τ J, weylQuotientHom τ Ω ⟨n, hnm⟩ • β ∈ parabolicRoots τ J)
    (hrel : ∀ x : Fin τ.rank → ℤ,
      weylQuotientHom τ Ω ⟨n, hnm⟩ • weylQuotientHom τ Ω ⟨n, hnm⟩ • x +
        weylQuotientHom τ Ω ⟨n, hnm⟩ • x + x = 0)
    (hdet : (cartanBlock τ J).det ≠ 0) (hq : ((q : Ω) ^ 2 + q + 1) ≠ 0)
    (hcop : IsCoprime ((q : ℤ) ^ 2 + q + 1) (cartanBlock τ J).det) :
    ∃ E : Subgroup (ModGL τ Ω),
      E ≤ rootSpan τ Ω (parabolicRoots τ J) ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧
        Nat.card E ^ 2 = (q ^ 2 + q + 1) ^ Fintype.card J := by
  classical
  let K' : Subgroup (J → Ωˣ) :=
    (monoHom (G := Ωˣ) ((q : ℤ) • blockP (weylQuotientHom τ Ω ⟨n, hnm⟩) J - 1)).ker
  let g : K' →* ModGL τ Ω :=
    (supportedTorusHom τ Ω J).comp K'.subtype
  have hP : blockP (weylQuotientHom τ Ω ⟨n, hnm⟩) J *
        blockP (weylQuotientHom τ Ω ⟨n, hnm⟩) J +
        blockP (weylQuotientHom τ Ω ⟨n, hnm⟩) J + 1 = 0 :=
    blockP_sq_add_self_add_one (w := weylQuotientHom τ Ω ⟨n, hnm⟩) hJ hrel
  have hG : (blockP (weylQuotientHom τ Ω ⟨n, hnm⟩) J)ᵀ * cartanBlock τ J *
      blockP (weylQuotientHom τ Ω ⟨n, hnm⟩) J = cartanBlock τ J :=
    blockP_transpose_mul_cartanBlock_mul_self (w := weylQuotientHom τ Ω ⟨n, hnm⟩) hsym hJ
  have hcard : Nat.card K' ^ 2 = (q ^ 2 + q + 1) ^ Fintype.card J :=
    natCard_ker_monoHom_cyclotomic hP hG hdet hq
  have hfix_of_mem : ∀ c : J → Ωˣ, c ∈ K' →
      monoHom ((q : ℤ) • blockP (weylQuotientHom τ Ω ⟨n, hnm⟩) J) c = c := by
    intro c hc
    have h : monoHom ((q : ℤ) • blockP (weylQuotientHom τ Ω ⟨n, hnm⟩) J - 1) c = 1 := by
      simpa only [K', MonoidHom.mem_ker] using hc
    rw [monoHom_sub_one] at h
    exact mul_inv_eq_one.mp h
  have htriv : ∀ c : J → Ωˣ, c ∈ K' → supportedTorusHom τ Ω J c = 1 → c = 1 := by
    intro c hc hfc
    have hpow : ∀ j, c j ^ ((q : ℤ) ^ 2 + (q : ℤ) + 1) = 1 := by
      intro j
      refine pow_eq_one_of_mem_ker_monoHom_cyclotomic hP (q : ℤ) ?_ j
      simpa only [K', MonoidHom.mem_ker] using hc
    exact eq_one_of_supportedTorusHom_eq_one c hpow hcop hfc
  have hg_inj : Function.Injective g := by
    intro c d hcd
    have hcd' : supportedTorusHom τ Ω J c.1 = supportedTorusHom τ Ω J d.1 :=
      show supportedTorusHom τ Ω J c.1 = supportedTorusHom τ Ω J d.1 from hcd
    have hmem : c.1⁻¹ * d.1 ∈ K' := K'.mul_mem (K'.inv_mem c.2) d.2
    have hfe : supportedTorusHom τ Ω J (c.1⁻¹ * d.1) = 1 := by
      rw [map_mul, map_inv, hcd', inv_mul_cancel]
    exact Subtype.ext (inv_mul_eq_one.mp (htriv _ hmem hfe))
  refine ⟨g.range, ?_, ?_⟩
  · rintro x ⟨c, hx⟩
    rw [← hx]
    refine ⟨supportedTorusHom_mem_rootSpan c.1, ?_⟩
    change g c ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr))
    rw [mem_twistedFixedPoints]
    show n * Units.map (entrywiseHom Fr) (supportedTorusHom τ Ω J c.1) * n⁻¹ =
      supportedTorusHom τ Ω J c.1
    rw [supportedTorusHom_conj_twisted hsym hFr n hnm hJ c.1, hfix_of_mem c.1 c.2]
  · have h1 := Subgroup.card_map_of_injective (K := ⊤) hg_inj
    rw [Subgroup.card_top, ← MonoidHom.range_eq_map] at h1
    rw [h1, hcard]

end Torus

section Center

variable {τ : Tag} {Ω : Type} [Field Ω] {J : Set (Fin τ.rank)} [Fintype J] [DecidableEq J]

theorem zpow_det_eq_one_of_mem_center_rootSpan (hsym : τ.symmetrizer = 1) {z : ModGL τ Ω}
    (hzQ : z ∈ rootSpan τ Ω (parabolicRoots τ J))
    (hzC : z ∈ Subgroup.centralizer (rootSpan τ Ω (parabolicRoots τ J) : Set (ModGL τ Ω))) :
    z ^ (cartanBlock τ J).det = 1 := by
  have hzQ' : z ∈ subsystemGroup τ Ω J := by
    rwa [subsystemGroup_eq_rootSpan]
  have hzcenter : (⟨z, hzQ'⟩ : subsystemGroup τ Ω J) ∈
      Subgroup.center (subsystemGroup τ Ω J) := by
    rw [Subgroup.mem_center_iff]
    intro y
    refine Subtype.ext ?_
    change y.1 * z = z * y.1
    exact (Subgroup.mem_centralizer_iff.mp hzC) y.1 (by
      rw [← subsystemGroup_eq_rootSpan]; exact y.2)
  have hcenter :=
    (mem_center_subsystemGroup_iff (K := Ω) (J := J) ⟨z, hzQ'⟩).1 hzcenter
  obtain ⟨a, ha⟩ := hcenter.1
  have ha' : supportedTorusHom τ Ω J a = z := ha
  have hprod : ∀ i : J, ∏ j : J, a j ^ τ.cartan j i = 1 := by
    intro i
    have hmem : (Pi.single (i : Fin τ.rank) 1 : Fin τ.rank → ℤ) ∈ parabolicRoots τ J :=
      single_mem_parabolicRoots i.2
    have h1 : torusRootChar z (Pi.single (i : Fin τ.rank) 1) = 1 :=
      hcenter.2 (Pi.single (i : Fin τ.rank) 1) hmem
    rw [← ha'] at h1
    rw [torusRootChar_supportedTorusHom J a (isRoot_single τ (i : Fin τ.rank))] at h1
    have hs : ∀ j : J, ∑ k, τ.cartan j k *
        (Pi.single (i : Fin τ.rank) 1 : Fin τ.rank → ℤ) k = τ.cartan j i := fun j => by
      rw [Finset.sum_eq_single (i : Fin τ.rank)
        (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mul_zero])
        (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, mul_one]
    simp only [hs] at h1
    exact Units.ext h1
  have hdet : ∀ j : J, a j ^ (cartanBlock τ J).det = 1 :=
    fun j => pow_det_eq_one_of_prod_cartan_eq_one a hprod j
  rw [← ha']
  calc supportedTorusHom τ Ω J a ^ (cartanBlock τ J).det
      = supportedTorusHom τ Ω J (a ^ (cartanBlock τ J).det) :=
        (map_zpow (supportedTorusHom τ Ω J) a _).symm
    _ = supportedTorusHom τ Ω J 1 := by
        rw [show a ^ (cartanBlock τ J).det = 1 from funext hdet]
    _ = 1 := map_one _

theorem eq_one_of_pow_eq_one_of_mem_center_rootSpan (hsym : τ.symmetrizer = 1) {z : ModGL τ Ω}
    (hzQ : z ∈ rootSpan τ Ω (parabolicRoots τ J))
    (hzC : z ∈ Subgroup.centralizer (rootSpan τ Ω (parabolicRoots τ J) : Set (ModGL τ Ω)))
    {N : ℕ} (hcop : IsCoprime (N : ℤ) (cartanBlock τ J).det) (hz : z ^ N = 1) : z = 1 := by
  have h1 := zpow_det_eq_one_of_mem_center_rootSpan hsym hzQ hzC
  obtain ⟨a, b, hab⟩ := hcop
  calc z = z ^ (a * (N : ℤ) + b * (cartanBlock τ J).det) := by rw [hab, zpow_one]
    _ = 1 := by
      rw [_root_.zpow_add, mul_comm a, mul_comm b, _root_.zpow_mul, _root_.zpow_mul,
        zpow_natCast, hz, h1]
      simp

end Center

end CFSG.StandardType
