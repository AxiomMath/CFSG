module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeModel
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagLift
public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGLieM6cDefs
public import CFSG.LocalAnalysis.StandardType.GGLieM6cCommute
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E7FourPlane
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KGD.D4QA1
public import CFSG.RankThree.PartOne.KLCE.Sector

public section

namespace CFSG.StandardType.LieCore.M6c

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
open CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag)

theorem minBC_eq_inv_of_mem_center
    {k : Type} [Field k] (φ : k →+* k)
    (hφ : ∀ v : kˣ, v ^ 3 = 1 → Units.map (φ : k →* k) v = v⁻¹)
    {z : e6Data_valid.minGroup k} (hz : z ∈ Subgroup.center (e6Data_valid.minGroup k)) :
    minBC e6Data_valid φ z = z⁻¹ := by
  obtain ⟨u, rfl, hu⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.exists_minTorus_of_mem_center_E6 hz
  rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.minBC_minTorus_E6]
  have h1 : (fun j => Units.map φ.toMonoidHom (u j)) = fun j => (u j)⁻¹ := by
    funext j
    exact hφ (u j) (hu j)
  rw [h1, show (fun j => (u j)⁻¹) = u⁻¹ from rfl, map_inv]

theorem ggPhi_E6_baseChangeGL
    {k : Type} [Field k] (θ : k →+* k) (ι : k →+* GGL) (f : ℕ)
    (hθ : ∀ c, ι (θ c) = ggFrobT f (ι c)) (g : ModGL Tag.E6 k) :
    ggPhi .E6 f (baseChangeGL ι g) = baseChangeGL ι (Units.map (entrywiseHom θ) g) := by
  change Units.map (entrywiseHom (ggFrobT f)) (baseChangeGL ι g) =
    baseChangeGL ι (Units.map (entrywiseHom θ) g)
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_baseChangeGL
    ι (ggFrobT f) θ (RingHom.ext fun c => (hθ c).symm) g

private theorem m6c_two_pow_odd_mod_three (m : ℕ) : 2 ^ (2 * m + 1) % 3 = 2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hpow : 2 ^ (2 * (m + 1) + 1) = 2 ^ (2 * m + 1) * 4 := by
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, pow_add]
      norm_num
    rw [hpow, Nat.mul_mod, ih]

private theorem m6c_abelianPreimage_unfolded
    {f : ℕ} (hf : Odd f) {A : Subgroup (ModGL Tag.E6 GGL)} (hA : A ≤ ratPoints (ggPhi .E6 f))
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    ∀ (k : Type) [Field k] [Finite k] (ι : k →+* GGL) (x y : ↥(e6Data_valid.minGroup k)),
      baseChangeGL ι (e6Isogeny k x : ModGL Tag.E6 k) ∈ A →
      baseChangeGL ι (e6Isogeny k y : ModGL Tag.E6 k) ∈ A → x * y = y * x := by
  intro k hk hkfin ι x y hx hy
  classical
  haveI : CharP k 2 := ι.charP ι.injective 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : ExpChar k 2 := expChar_prime k 2
  let θ : k →+* k := iterateFrobenius k 2 f
  have hθ : ∀ c, ι (θ c) = ggFrobT f (ι c) := by
    intro c
    rw [ggFrobT_apply, show θ c = c ^ 2 ^ f from iterateFrobenius_def 2 f c, map_pow]
  have hmod : 2 ^ f % 3 = 2 := by
    obtain ⟨m, rfl⟩ := hf
    exact m6c_two_pow_odd_mod_three m
  have hφ : ∀ v : kˣ, v ^ 3 = 1 → Units.map (θ : k →* k) v = v⁻¹ := by
    intro v hv
    have hv2 : v ^ 2 = v⁻¹ := by
      have hmul : v ^ 2 * v = 1 := by rw [← pow_succ, hv]
      exact eq_inv_of_mul_eq_one_left hmul
    have hsplit : 2 ^ f = 3 * (2 ^ f / 3) + 2 := by
      conv_lhs => rw [← Nat.div_add_mod (2 ^ f) 3]
      rw [hmod]
    have hvval : (v : k) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hv, Units.val_one]
    refine Units.ext ?_
    rw [Units.coe_map,
      show (θ : k →* k) (v : k) = (v : k) ^ 2 ^ f from iterateFrobenius_def 2 f (v : k)]
    calc (v : k) ^ 2 ^ f = (v : k) ^ (3 * (2 ^ f / 3) + 2) := by
          conv_lhs => rw [hsplit]
      _ = ((v : k) ^ 3) ^ (2 ^ f / 3) * (v : k) ^ 2 := by rw [pow_add, pow_mul]
      _ = (v : k) ^ 2 := by rw [hvval, one_pow, one_mul]
      _ = ((v⁻¹ : kˣ) : k) := by rw [← hv2, Units.val_pow_eq_pow_val]
  set π : ↥(e6Data_valid.minGroup k) →* ModGL Tag.E6 GGL :=
    (baseChangeGL ι).comp ((adjointGroup Tag.E6 k).subtype.comp (e6Isogeny k)) with hπ
  have hπker : π.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup k) := by
    intro z hz
    rw [hπ] at hz
    have hz1 : (e6Isogeny k z : ModGL Tag.E6 k) = 1 := by
      have hz' : baseChangeGL ι (e6Isogeny k z : ModGL Tag.E6 k) =
          baseChangeGL ι (1 : ModGL Tag.E6 k) := by
        simpa using hz
      exact baseChangeGL_injective ι hz'
    have hzker : z ∈ (e6IsogenyT k).ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext hz1
    exact CFSG.LieType.Steinberg.Isogeny.ker_e6IsogenyT_le_center k hzker
  have hexp : ∀ z ∈ π.ker, z ^ 3 = 1 := by
    intro z hz
    exact CFSG.ClassicalInvolution.ModelFacts.A2Isogeny.center_pow_three_e6 (k := k) (hπker hz)
  have hF_lift : ∀ g, π (minBC e6Data_valid θ g) = ggPhi .E6 f (π g) := by
    intro g
    rw [hπ]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_minBC (k := k) (k' := k) θ g,
      ← CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self]
    exact (ggPhi_E6_baseChangeGL θ ι f hθ (e6Isogeny k g : ModGL Tag.E6 k)).symm
  have hinv : ∀ z ∈ π.ker, minBC e6Data_valid θ z = z⁻¹ := by
    intro z hz
    exact minBC_eq_inv_of_mem_center θ hφ (hπker hz)
  have hxF : ggPhi .E6 f (π x) = π x := by
    rw [hπ]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact (hA hx).2
  have hyF : ggPhi .E6 f (π y) = π y := by
    rw [hπ]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact (hA hy).2
  have hxy : π x * π y = π y * π x := by
    rw [hπ]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact hab _ hx _ hy
  exact commute_of_lift_inverts_center π hπker hexp (minBC e6Data_valid θ) (ggPhi .E6 f)
    hF_lift hinv hxF hyF hxy

theorem abelianPreimage_of_ratPoints_E6
    {f : ℕ} (hf : Odd f) {A : Subgroup (ModGL Tag.E6 GGL)} (hA : A ≤ ratPoints (ggPhi .E6 f))
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : GGLieAbelianPreimageE6 A := by
  simp only [GGLieAbelianPreimageE6]
  exact m6c_abelianPreimage_unfolded hf hA hab

end CFSG.StandardType.LieCore.M6c
