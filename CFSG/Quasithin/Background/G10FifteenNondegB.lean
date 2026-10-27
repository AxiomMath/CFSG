module

public import CFSG.Quasithin.Background.G11BridgeRestrict
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem restrictEquiv_mul {I : Submodule (ZMod 2) V} {a b : GLV V} (ha : conjSub a I = I)
    (hb : conjSub b I = I) (hab : conjSub (a * b) I = I) :
    restrictEquiv (a * b) I hab = restrictEquiv a I ha * restrictEquiv b I hb := by
  ext i
  rfl

theorem restrictEquiv_inv {I : Submodule (ZMod 2) V} {a : GLV V} (ha : conjSub a I = I)
    (hai : conjSub a⁻¹ I = I) : restrictEquiv a⁻¹ I hai = (restrictEquiv a I ha)⁻¹ := by
  ext i
  rfl

theorem invariant_stabilizerOf (X : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) :
    Invariant (stabilizerOf X I) I := fun k hk u hu => by
  have h : k u ∈ conjSub k I := apply_mem_conjSub hu
  rwa [hk.2] at h

theorem fullTransvections_congr {Y : Subgroup (GLV V)} {U U' : Submodule (ZMod 2) V} {c : V}
    {hc : c ∈ U} (h : U = U') (hFT : FullTransvections Y U c hc) :
    FullTransvections Y U' c (h ▸ hc) := by
  subst h
  exact hFT

theorem fullTransvections_restrict {Y : Subgroup (GLV V)} {I U : Submodule (ZMod 2) V} {c : V}
    (hY : Invariant Y I) (hUI : U ≤ I) (hc : c ∈ U) (hFT : FullTransvections Y U c hc) :
    FullTransvections (restrictRange Y I hY) (U.comap I.subtype) ⟨c, hUI hc⟩
      (show (⟨c, hUI hc⟩ : ↥I) ∈ U.comap I.subtype from hc) := by
  let e : U.comap I.subtype ≃ₗ[ZMod 2] U := Submodule.comapSubtypeEquivOfLe hUI
  have he : ∀ u, ((e u : ↥U) : V) = (((u : ↥I) : V)) := fun u => rfl
  obtain ⟨hFT1, hFT2⟩ := hFT
  constructor
  · rintro q ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨f, hf0, hf⟩ := hFT1 y hy
    refine ⟨f.comp e.toLinearMap, ?_, fun u => ?_⟩
    · show f (e ⟨⟨c, hUI hc⟩, hc⟩) = 0
      have : e ⟨⟨c, hUI hc⟩, hc⟩ = ⟨c, hc⟩ := rfl
      rw [this]
      exact hf0
    · apply Subtype.ext
      have h1 := hf (e u)
      rw [he] at h1
      show y ((u : ↥I) : V) = ((u : ↥I) : V) + (f (e u)) • c
      exact h1
  · intro f hf0
    obtain ⟨y, hy, hyf⟩ := hFT2 (f.comp e.symm.toLinearMap) (by
      show f (e.symm ⟨c, hc⟩) = 0
      have : e.symm ⟨c, hc⟩ = ⟨⟨c, hUI hc⟩, hc⟩ := rfl
      rw [this]
      exact hf0)
    refine ⟨restrictHom Y I hY ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, fun u => ?_⟩
    apply Subtype.ext
    have h1 := hyf (e u)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h1
    show y ((u : ↥I) : V) = ((u : ↥I) : V) + (f u) • c
    have h3 : ((e u : ↥U) : V) = ((u : ↥I) : V) := rfl
    rw [h3] at h1
    exact h1

end G11

end CFSG.Quasithin
