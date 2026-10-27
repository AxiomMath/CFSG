module

public import CFSG.LocalAnalysis.WeakClosure81.W18Pack

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
  Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace ModDataE

variable {J E : Subgroup G} (M : ModDataE J E)

theorem mRank_img {A : Subgroup G} (hA : A ≤ J) (hAab : IsElemAbelian 2 A) :
    mRank (M.img A) = E3.mQuot A (A ⊓ Subgroup.centralizer (E : Set G)) := by
  have hp : IsPGroup 2 A := fun g => ⟨1, Subtype.ext (by simpa using hAab.2 g.1 g.2)⟩
  have h1 : Nat.card (M.img A) = 2 ^ E3.mQuot A (A ⊓ Subgroup.centralizer (E : Set G)) := by
    rw [M.card_img hA, ← Subgroup.inf_relIndex_left (H := A), E3.relIndex_eq_two_pow hp]
  unfold mRank
  rw [h1, Nat.log_pow Nat.one_lt_two]

end ModDataE

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem mRank_le_iStar (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    {A : Subgroup (LGL 2 M.W)} (hA : A ∈ x.packFamily M) : mRank A ≤ x.iStar := by
  obtain ⟨g, hg, rfl⟩ := hA
  have hVg := E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g
  have hab : IsElemAbelian 2 (vInH V H g) := hVg.mono inf_le_left
  have hle : vInH V H g ≤ H := inf_le_right
  rw [M.mRank_img hle hab]
  exact hg.2

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
