module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2PairO1
public import CFSG.LocalAnalysis.WeakClosure81.W183B2PairExt

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

section Certified


namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

private theorem w183b2_pair_conj_eq
    (M : ModDataE H (eOmegaZ H D.T)) {g : G} (j : ↥H) :
    (M.img (vInH V H g)).map (MulAut.conj (M.ρ j)).toMonoidHom =
      M.img (vInH V H (g * (j : G)⁻¹)) := by
  have hle : vInH V H g ≤ H := by
    unfold vInH
    exact inf_le_right
  have h := M.img_conj (A := vInH V H g) hle j
  rw [← vInH_mul g (H.inv_mem j.2)] at h
  simpa only [CFSG.SignalizerFunctorTheorem.Quadratic.cj] using h

theorem pairTest
    (hL28 : FinPairGenL28) (hSz8 : FinPairGenSz8)
    (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hK : IsSolvable ↥(H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)))
    (h13 : ¬ 13 ∣ Nat.card (M.img H)) :
    PairTest (M.img H) (packFamilyU D V H i M) := by
  intro A hA y hy hviol
  obtain ⟨g, hg, rfl⟩ := hA
  obtain ⟨j, _, hyj⟩ := M.mem_img.1 hy
  rw [← hyj] at hviol
  have hh : (j : G)⁻¹ ∈ H := H.inv_mem j.2
  have hconj := w183b2_pair_conj_eq (D := D) (V := V) (H := H) (g := g) M j
  unfold PairViolation at hviol
  rw [hconj] at hviol
  obtain ⟨hnot1, hnot2, hk1, hk2, hnotOK⟩ := hviol
  refine hnotOK ?_
  exact Ctx188.pair_ext (D := D) (V₀ := V₀) (V := V) (H := H) (i := i)
    hL28 hSz8 x M hK h13 hg hh hnot1 hnot2 hk1 hk2
    (Ctx188.pair_inCalOStar (D := D) (V₀ := V₀) (V := V) (H := H) (i := i)
      x M hg hh hnot1 hnot2 hk1 hk2)

end Ctx188

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
