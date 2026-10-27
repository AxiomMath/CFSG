module

public import CFSG.LocalAnalysis.StandardType.GGK2E6D5DSPFromCoordEven
public import CFSG.LocalAnalysis.StandardType.GGK2E6SignedReflectionOddEdgeAnyDim

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.FrameRoute CFSG.StandardType.HdRo7D
open CFSG.StandardType.SpCoord CFSG.StandardType.HdRo7C

theorem d5_actual_simple_dsp
    {G : Type} [Group G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin 6) (ZMod 3) V)
    (AL : Subgroup (MulAut ↥Bs))
    (f : (ggCoxeterMatrixD 5).Group ≃* AL)
    (φ : Fin 5 → MulAut ↥Bs)
    (hf : ∀ i : Fin 5,
      (f ((ggCoxeterMatrixD 5).simple i) : MulAut ↥Bs) = φ i)
    (hC2 : ∀ i : Fin 5, C2SP 3 b (ggLin (p := 3) ι (φ i)))
    (hR : ∀ i : Fin 5, GGIsReflection 3 (φ i)) :
    ∀ i : Fin 5, DSP 3 b (ggLin (p := 3) ι (φ i)) := by
  classical
  let μ := coordMulEquiv ι b
  let eAut : MulAut ↥Bs ≃* MulAut (Fin 6 → Multiplicative (ZMod 3)) :=
    MulAut.congr μ
  let H : Subgroup (MulAut (Fin 6 → Multiplicative (ZMod 3))) :=
    AL.map eAut.toMonoidHom
  let fH : (ggCoxeterMatrixD 5).Group ≃* H :=
    f.trans (eAut.subgroupMap AL)
  have hsign : ∀ i : Fin 5,
      (fH ((ggCoxeterMatrixD 5).simple i) :
        MulAut (Fin 6 → Multiplicative (ZMod 3))) ∈
        modelReflSet (signedPermSet 6) := by
    intro i
    have hfc : (fH ((ggCoxeterMatrixD 5).simple i) :
        MulAut (Fin 6 → Multiplicative (ZMod 3))) = eAut (φ i) := by
      change ((eAut.subgroupMap AL) (f ((ggCoxeterMatrixD 5).simple i)) :
        MulAut (Fin 6 → Multiplicative (ZMod 3))) = eAut (φ i)
      rw [MulEquiv.coe_subgroupMap_apply, hf i]
    rw [hfc]
    exact reflection_coordAut_mem_modelReflSet ι b (φ i) (hC2 i) (hR i)
  have heven := d5_signed_simple_even fH hsign
  have hfix : ∀ i : Fin 5, ggLin (p := 3) ι (φ i) (b 0) = b 0 := by
    intro i
    obtain ⟨σ, c, hσ0, hc0, hc, hspec⟩ := hC2 i
    rw [hspec 0, hσ0, hc0, one_smul]
  intro i
  have heven_i : eAut (φ i) ∈ evenSignedPermSet 6 := by
    have h := (heven i).1
    rwa [show (fH ((ggCoxeterMatrixD 5).simple i) :
      MulAut (Fin 6 → Multiplicative (ZMod 3))) = eAut (φ i) by
        change ((eAut.subgroupMap AL) (f ((ggCoxeterMatrixD 5).simple i)) :
          MulAut (Fin 6 → Multiplicative (ZMod 3))) = eAut (φ i)
        rw [MulEquiv.coe_subgroupMap_apply, hf i]] at h
  exact dsp_of_coord_even ι b (φ i) heven_i (hfix i)

end CFSG.StandardType

end
