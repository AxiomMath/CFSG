module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DMT
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DMPFactor
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DMPForm
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DMPSplitMain

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9.MP

open scoped Matrix MatrixGroups
open CFSG.RankThree.GF2n.Stroth80.HS9.M1

theorem step95Module_holds : Step95ModuleStatement := by
  intro K _ _ _ hK W _ _ _ Act bw qw _ hnd hinv hqs hqa hqinv X hS1 hS2 hM12 hI5 hM11 hP1
  obtain ⟨Y₁, Y₂, i1, i2, j1, j2, c, hc⟩ :=
    step95_structure_of sl2Factor_holds K hK W Act bw hnd hinv X hS1 hS2 hM12 hI5 hM11 hP1
  have hsymm : ∀ (g h : SL(2, K)) (x : Wd K Y₁ Y₂),
      c.symm (actW (g : Matrix (Fin 2) (Fin 2) K) (h : Matrix (Fin 2) (Fin 2) K) x) =
        Act (g, h) (c.symm x) := by
    intro g h x
    rw [LinearEquiv.symm_apply_eq, hc (g, h) (c.symm x), LinearEquiv.apply_symm_apply]
  let B : Wd K Y₁ Y₂ →ₗ[K] Wd K Y₁ Y₂ →ₗ[K] K :=
    bw.compl₁₂ (c.symm : Wd K Y₁ Y₂ →ₗ[K] W) (c.symm : Wd K Y₁ Y₂ →ₗ[K] W)
  have hB : ∀ x x', B x x' = bw (c.symm x) (c.symm x') := fun x x' => rfl
  obtain ⟨β₁, β₂, h1, h2, h3, h4, h5⟩ := step95_form K hK B (fun x => qw (c.symm x))
    (fun x hx => by
      have h0 : c.symm x = 0 := hnd _ fun w' => by
        have := hx (c w')
        rwa [hB, LinearEquiv.symm_apply_apply] at this
      simpa using h0)
    (fun g h x x' => by
      rw [hB, hB, hsymm, hsymm]
      exact hinv (g, h) _ _)
    (fun a x => by
      show qw (c.symm (a • x)) = a ^ 2 * qw (c.symm x)
      rw [map_smul]
      exact hqs a _)
    (fun x x' => by
      show qw (c.symm (x + x')) = qw (c.symm x) + qw (c.symm x') + bw (c.symm x) (c.symm x')
      rw [map_add]
      exact hqa _ _)
    (fun g h x => by
      show qw (c.symm (actW (g : Matrix (Fin 2) (Fin 2) K) (h : Matrix (Fin 2) (Fin 2) K) x)) =
        qw (c.symm x)
      rw [hsymm]
      exact hqinv (g, h) _)
  refine ⟨Y₁, Y₂, i1, i2, j1, j2, β₁, β₂, c, h1, h2, h3, h4, hc, fun w w' => ?_⟩
  have h := h5 (c w) (c w')
  rwa [hB, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h

end CFSG.RankThree.GF2n.Stroth80.HS9.MP
