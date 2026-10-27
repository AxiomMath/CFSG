module

public import CFSG.LocalAnalysis.WeakClosure81.FiveKer
import all CFSG.LocalAnalysis.WeakClosure81.FiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.FiveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem five_four_one {H M A X : Subgroup G} (hM : maxOver H A = {M})
    (hX : IsMinNormalOver H (kerMOf M H) X) : H = X ⊔ A := by
  obtain ⟨hMmax, hAM, hunique⟩ := isUniqueMaxOver_iff.mp hM
  have hsup : X ⊔ A ≤ H := sup_le hX.2.1 (hAM.trans hMmax.le)
  refine le_antisymm ?_ hsup
  by_contra hnot
  have hlt : X ⊔ A < H := lt_of_le_of_ne hsup (fun heq => hnot (le_of_eq heq.symm))
  obtain ⟨N, hNmax, hNsup⟩ := exists_isMaxSubgroupIn hlt
  have hNM : N = M := hunique N hNmax (le_sup_right.trans hNsup)
  have hXM : X ≤ M := le_sup_left.trans (hNsup.trans (le_of_eq hNM))
  exact absurd (le_kerMOf_of_normal hX.2.1 hX.2.2.1 hXM) (not_le_of_gt hX.1)

theorem five_four_two {H M A X : Subgroup G} (hM : maxOver H A = {M})
    (hX : IsMinNormalOver H (kerMOf M H) X) {K : Subgroup G} (hKH : K ≤ H) (hAK : A ≤ K)
    (hXK : X ≤ K ⊔ kerMOf M H) : K = H := by
  obtain ⟨hMmax, hAM, hunique⟩ := isUniqueMaxOver_iff.mp hM
  by_contra hne
  have hlt : K < H := lt_of_le_of_ne hKH hne
  obtain ⟨N, hNmax, hNsup⟩ := exists_isMaxSubgroupIn hlt
  have hNM : N = M := hunique N hNmax (hAK.trans hNsup)
  have hKM : K ≤ M := hNsup.trans (le_of_eq hNM)
  have hXM : X ≤ M := hXK.trans (sup_le hKM (kerMOf_le_left M H))
  exact absurd (le_kerMOf_of_normal hX.2.1 hX.2.2.1 hXM) (not_le_of_gt hX.1)

end CFSG.LocalAnalysis.WeakClosure81
