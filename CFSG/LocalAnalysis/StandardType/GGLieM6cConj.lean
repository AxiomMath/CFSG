module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.LocalAnalysis.StandardType.GGLieM6cDefs
public import CFSG.LocalAnalysis.StandardType.GGLieM6cDescent
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

public section

namespace CFSG.StandardType.LieCore.M6c

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
open CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag)

private theorem m6c_minEndBC_injective {d : ℕ} {k k' : Type*} [Field k] [Field k']
    (ι : k →+* k') : Function.Injective (minEndBC (d := d) ι) := by
  intro A B h
  refine minEnd_ext fun b => Finsupp.ext fun c => ?_
  have h1 := congrArg (fun f : Module.End k' (Fin d →₀ k') => f (Finsupp.single b 1) c) h
  simp only [minEndBC_single, Finsupp.mapRange_apply] at h1
  exact ι.injective h1

private theorem m6c_minBC_injective
    {τ : Tag} {D : MinData τ} (hV : D.Valid) {k k' : Type*}
    [Field k] [Field k'] (ι : k →+* k') : Function.Injective (minBC hV ι) := by
  intro g h e
  apply Subtype.ext
  apply Units.ext
  apply m6c_minEndBC_injective ι
  exact congrArg (fun x : hV.minGroup k' => ((x : (Module.End k' (Fin D.d →₀ k'))ˣ) :
    Module.End k' (Fin D.d →₀ k'))) e

theorem abelianPreimage_map_conj
    {A : Subgroup (ModGL Tag.E6 GGL)} (hA : GGLieAbelianPreimageE6 A)
    {g : ModGL Tag.E6 GGL} (hg : g ∈ adjointGroup Tag.E6 GGL) :
    GGLieAbelianPreimageE6 (A.map (MulAut.conj g).toMonoidHom) := by
  refine fun k hk hkfin ι x y hx hy => ?_
  obtain ⟨b, hbA, hb_eq⟩ := Subgroup.mem_map.mp hx
  obtain ⟨c, hcA, hc_eq⟩ := Subgroup.mem_map.mp hy
  obtain ⟨k', _, _, κ, ι', hcomp, hlift⟩ :=
    exists_finite_subfield_lift_adjoint {g} (by
      intro s hs
      simp only [Finset.mem_coe, Finset.mem_singleton] at hs
      rw [hs]
      exact hg) k ι
  obtain ⟨g', hg'mem, hg'eq⟩ := hlift g (by simp)
  obtain ⟨h, hh⟩ := e6Isogeny_surjective (k := k') ⟨g', hg'mem⟩
  have hh2 : (e6Isogeny k' h : ModGL Tag.E6 k') = g' := congrArg Subtype.val hh
  let F : ↥(adjointGroup Tag.E6 k') →* ModGL Tag.E6 GGL :=
    (baseChangeGL (τ := Tag.E6) ι').comp (adjointGroup Tag.E6 k').subtype
  have hFh : F (e6Isogeny k' h) = g := by
    show baseChangeGL ι' (e6Isogeny k' h : ModGL Tag.E6 k') = g
    rw [hh2, hg'eq]
  let x' : ↥(e6Data_valid.minGroup k') := minBC e6Data_valid κ x
  let y' : ↥(e6Data_valid.minGroup k') := minBC e6Data_valid κ y
  have hxmin : F (e6Isogeny k' x') = baseChangeGL ι (e6Isogeny k x) := by
    show baseChangeGL ι' (e6Isogeny k' x' : ModGL Tag.E6 k') = baseChangeGL ι (e6Isogeny k x)
    rw [show (e6Isogeny k' x' : ModGL Tag.E6 k') =
        baseChangeGL κ ((e6Isogeny k x : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) from
      e6Isogeny_minBC κ x]
    rw [baseChangeGL_baseChangeGL, hcomp]
  have hymin : F (e6Isogeny k' y') = baseChangeGL ι (e6Isogeny k y) := by
    show baseChangeGL ι' (e6Isogeny k' y' : ModGL Tag.E6 k') = baseChangeGL ι (e6Isogeny k y)
    rw [show (e6Isogeny k' y' : ModGL Tag.E6 k') =
        baseChangeGL κ ((e6Isogeny k y : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) from
      e6Isogeny_minBC κ y]
    rw [baseChangeGL_baseChangeGL, hcomp]
  have hx' : baseChangeGL ι' (e6Isogeny k' (h⁻¹ * x' * h) : ModGL Tag.E6 k') = b := by
    change F (e6Isogeny k' (h⁻¹ * x' * h)) = b
    have h1 : e6Isogeny k' (h⁻¹ * x' * h) =
        (e6Isogeny k' h)⁻¹ * e6Isogeny k' x' * e6Isogeny k' h := by
      rw [map_mul, map_mul, map_inv]
    rw [h1, map_mul, map_mul, map_inv, hFh, hxmin]
    rw [← hb_eq]
    show g⁻¹ * (g * b * g⁻¹) * g = b
    group
  have hy' : baseChangeGL ι' (e6Isogeny k' (h⁻¹ * y' * h) : ModGL Tag.E6 k') = c := by
    change F (e6Isogeny k' (h⁻¹ * y' * h)) = c
    have h1 : e6Isogeny k' (h⁻¹ * y' * h) =
        (e6Isogeny k' h)⁻¹ * e6Isogeny k' y' * e6Isogeny k' h := by
      rw [map_mul, map_mul, map_inv]
    rw [h1, map_mul, map_mul, map_inv, hFh, hymin]
    rw [← hc_eq]
    show g⁻¹ * (g * c * g⁻¹) * g = c
    group
  have hcomm := hA k' ι' (h⁻¹ * x' * h) (h⁻¹ * y' * h)
    (by rw [hx']; exact hbA) (by rw [hy']; exact hcA)
  have hxy' : x' * y' = y' * x' := by
    calc x' * y' = h * ((h⁻¹ * x' * h) * (h⁻¹ * y' * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * y' * h) * (h⁻¹ * x' * h)) * h⁻¹ := by rw [hcomm]
      _ = y' * x' := by group
  have hxy : minBC e6Data_valid κ (x * y) = minBC e6Data_valid κ (y * x) := by
    rw [map_mul, map_mul]
    exact hxy'
  exact (m6c_minBC_injective e6Data_valid κ) hxy

end CFSG.StandardType.LieCore.M6c
