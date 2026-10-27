module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeModel
public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center
public import CFSG.LocalAnalysis.StandardType.GGLieM6cDefs
public import CFSG.LocalAnalysis.StandardType.GGLieM6cCommute
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
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
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools

public section

namespace CFSG.StandardType.LieCore.M6c

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
open CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.Steinberg.CentralExt.AdjointClosed
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag)

private theorem m6c_three_dvd_two_pow_sub_one {f : ℕ} (hf : Even f) : 3 ∣ 2 ^ f - 1 := by
  obtain ⟨t, rfl⟩ := hf
  have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
  have h : (2 : ℕ) ^ (t + t) ≡ 1 [MOD 3] := by
    rw [show t + t = 2 * t by ring, pow_mul]
    simpa using h4.pow t
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow' (t + t) 1)).1 h.symm

private theorem m6c_center_pow_three
    (k : Type) [Field k] {z : e6Data_valid.minGroup k}
    (hz : z ∈ Subgroup.center (e6Data_valid.minGroup k)) : z ^ 3 = 1 := by
  obtain ⟨u, rfl⟩ := center_le_range_minTorus e6Data_valid k isFiniteType_cartan_E6
    (e6Datum_isCTGroupDatum k) (e6Datum_steinbergExtras k) (e6Datum_bruhatExtras k) hz
  have hu : u ∈ centerChars .E6 k := (minTorus_mem_center_iff e6Data_valid k u).1 hz
  have hu3 : u ^ 3 = 1 := by
    funext m
    exact pow_eq_one_of_mem_centerChars e6B_spec hu m
  rw [← map_pow, hu3, map_one]

theorem sigma_eq_inv_of_mem_center
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ v : kˣ, v ^ 3 = 1 → Units.map (θ : k →* k) v = v)
    {z : e6Data_valid.minGroup k} (hz : z ∈ Subgroup.center (e6Data_valid.minGroup k)) :
    CFSG.LieType.Steinberg.TwistedE6.sigma k θ z = z⁻¹ := by
  obtain ⟨u, rfl⟩ := center_le_range_minTorus e6Data_valid k isFiniteType_cartan_E6
    (e6Datum_isCTGroupDatum k) (e6Datum_steinbergExtras k) (e6Datum_bruhatExtras k) hz
  have hu : u ∈ centerChars .E6 k := (minTorus_mem_center_iff e6Data_valid k u).1 hz
  set v : kˣ := u ⟨0, by decide⟩ with hv
  have hv3 : v ^ 3 = 1 := by
    rw [hv]
    exact pow_eq_one_of_mem_centerChars e6B_spec hu ⟨0, by decide⟩
  have hut : u = tvec v e6c := by
    funext i
    rw [hv]
    exact (eq_zpow_of_mem_centerChars e6C_spec hu i).trans (by simp [tvec])
  rw [hut, sigma_minTorus_tvec θ hv3, hθ v hv3, ← map_inv]
  congr 1
  funext i
  simp only [tvec, Pi.inv_apply]
  rw [inv_zpow]

theorem ggPhi_twistedE6_baseChangeGL
    {k : Type} [Field k] (θ : k →+* k) (ι : k →+* GGL) (f : ℕ)
    (hθ : ∀ c, ι (θ c) = ggFrobT f (ι c)) (g : ModGL TwistTag.E6.tag k) :
    ggPhi .twistedE6 f (baseChangeGL ι g) = baseChangeGL ι (twistHom TwistTag.E6 k θ g) := by
  change twistHom TwistTag.E6 GGL (ggFrobT f) (baseChangeGL ι g) =
    baseChangeGL ι (twistHom TwistTag.E6 k θ g)
  rw [twistHom_apply, twistHom_apply]
  simp only [map_mul, map_inv]
  rw [baseChangeGL_diagramMap ι TwistTag.E6,
    CFSG.RankThree.Chevalley.entrywise_baseChangeGL_eq ι (ggFrobT f) θ
      (fun b => (hθ b).symm) g]

private theorem m6c_twistHom_fixed_of_mem_ratPoints
    {k : Type} [Field k] [Finite k] (θ : k →+* k) (ι : k →+* GGL) (f : ℕ)
    (hθ : ∀ c, ι (θ c) = ggFrobT f (ι c)) {A : Subgroup (ModGL Tag.E6 GGL)}
    (hA : A ≤ ratPoints (ggPhi .twistedE6 f)) {x : e6Data_valid.minGroup k}
    (hx : baseChangeGL ι (e6IsogenyT k x : ModGL TwistTag.E6.tag k) ∈ A) :
    twistHom TwistTag.E6 k θ (e6IsogenyT k x : ModGL TwistTag.E6.tag k) =
      (e6IsogenyT k x : ModGL TwistTag.E6.tag k) := by
  have hxr : baseChangeGL ι (e6IsogenyT k x : ModGL TwistTag.E6.tag k) ∈
      ratPoints (ggPhi .twistedE6 f) := hA hx
  have hfix : ggPhi .twistedE6 f (baseChangeGL ι (e6IsogenyT k x : ModGL TwistTag.E6.tag k)) =
      baseChangeGL ι (e6IsogenyT k x : ModGL TwistTag.E6.tag k) := (Subgroup.mem_inf.1 hxr).2
  refine baseChangeGL_injective (τ := TwistTag.E6.tag) (f := ι) ?_
  rw [← ggPhi_twistedE6_baseChangeGL θ ι f hθ (e6IsogenyT k x : ModGL TwistTag.E6.tag k)]
  exact hfix

theorem abelianPreimage_of_ratPoints_twistedE6
    {f : ℕ} (hf : Even f) {A : Subgroup (ModGL Tag.E6 GGL)}
    (hA : A ≤ ratPoints (ggPhi .twistedE6 f)) (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    GGLieAbelianPreimageE6 A := by
  unfold GGLieAbelianPreimageE6
  intro k _ _ ι x y hx hy
  haveI : CharP k 2 := ι.charP ι.injective 2
  let θ : k →+* k := iterateFrobenius k 2 f
  have hθ : ∀ c, ι (θ c) = ggFrobT f (ι c) := by
    intro c
    rw [show θ c = c ^ 2 ^ f from iterateFrobenius_def 2 f c, map_pow, ggFrobT_apply]
  have hθfix : ∀ v : kˣ, v ^ 3 = 1 → Units.map (θ : k →* k) v = v := by
    intro v hv
    obtain ⟨m, hm⟩ := m6c_three_dvd_two_pow_sub_one hf
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_pow' f 1
    have hpow : (2 : ℕ) ^ f = 3 * m + 1 := by omega
    apply Units.ext
    change θ (v : k) = (v : k)
    have hvk : (v : k) ^ 3 = 1 := by
      have := congrArg (fun u : kˣ => (u : k)) hv
      simpa using this
    rw [show θ (v : k) = (v : k) ^ 2 ^ f from iterateFrobenius_def 2 f (v : k),
      hpow, pow_add, pow_mul, hvk, one_pow, one_mul, pow_one]
  let G := ↥(e6Data_valid.minGroup k)
  let H := ModGL TwistTag.E6.tag k
  let π : G →* H := (adjointGroup TwistTag.E6.tag k).subtype.comp (e6IsogenyT k)
  let Ft : G →* G := CFSG.LieType.Steinberg.TwistedE6.sigma k θ
  let F : H →* H := twistHom TwistTag.E6 k θ
  have hπ : π.ker ≤ Subgroup.center G := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    exact ker_e6IsogenyT_le_center k (Subtype.ext (by simpa [π] using hz))
  have hexp : ∀ z ∈ π.ker, z ^ 3 = 1 := fun z hz => m6c_center_pow_three k (hπ hz)
  have hF : ∀ g, π (Ft g) = F (π g) := by
    intro g
    change (e6IsogenyT k (CFSG.LieType.Steinberg.TwistedE6.sigma k θ g) :
        ModGL TwistTag.E6.tag k) =
      twistHom TwistTag.E6 k θ (e6IsogenyT k g : ModGL TwistTag.E6.tag k)
    rw [e6IsogenyT_sigma θ g, coe_twistC]
  have hinv : ∀ z ∈ π.ker, Ft z = z⁻¹ := fun z hz =>
    sigma_eq_inv_of_mem_center θ hθfix (hπ hz)
  have hxfix : F (π x) = π x := by
    change twistHom TwistTag.E6 k θ (e6IsogenyT k x : ModGL TwistTag.E6.tag k) =
      (e6IsogenyT k x : ModGL TwistTag.E6.tag k)
    exact m6c_twistHom_fixed_of_mem_ratPoints θ ι f hθ hA hx
  have hyfix : F (π y) = π y := by
    change twistHom TwistTag.E6 k θ (e6IsogenyT k y : ModGL TwistTag.E6.tag k) =
      (e6IsogenyT k y : ModGL TwistTag.E6.tag k)
    exact m6c_twistHom_fixed_of_mem_ratPoints θ ι f hθ hA hy
  have hxy : π x * π y = π y * π x := by
    refine baseChangeGL_injective (τ := TwistTag.E6.tag) (f := ι) ?_
    rw [map_mul, map_mul]
    exact hab _ hx _ hy
  exact commute_of_lift_inverts_center π hπ hexp Ft F hF hinv hxfix hyfix hxy

end CFSG.StandardType.LieCore.M6c
