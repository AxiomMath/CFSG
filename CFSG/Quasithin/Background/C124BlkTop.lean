module

public import CFSG.Quasithin.Background.C124BlkBasic

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] {V : Subgroup G}

theorem commV_autI_eq_top (hV : IsElemAbelian 2 V) {L : Subgroup G}
    (hLN : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V) :
    commV (autI hV L) = ⊤ := by
  have h := map_blkVal_commV hV hLN
  rw [hVL] at h
  rw [eq_top_iff]
  intro w _
  have hw : blkVal hV w ∈ (commV (autI hV L)).map (blkVal hV) := by
    rw [h]
    exact w.val_mem
  obtain ⟨x, hx, hxw⟩ := hw
  have : x = w := blkVal_injective hV hxw
  rw [← this]
  exact hx

end CFSG.Quasithin.C124
