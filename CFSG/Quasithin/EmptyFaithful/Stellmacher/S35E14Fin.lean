module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin3

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.E14

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

theorem std_cen_all : ∀ d : Perm (Fin 5),
    (∀ w ∈ commF zStd, orth.act d w = w) → d ∈ S5ThatF := by
  unfold commF zStd; decide +kernel

theorem cenW_commW_std_le :
    cenW (commW orth (Subgroup.zpowers zStd) ⊤) ≤ S5That := by
  intro d hd
  rw [mem_cenW] at hd
  rw [mem_S5That_iff]
  exact std_cen_all d fun w hw => hd w ((mem_commW_zpowers_iff zStd w).mpr hw)

theorem cenW_commW_le_That {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    cenW (commW orth (Subgroup.zpowers (zc D)) ⊤) ≤ That D := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  have hT : That (cj g S5Syl) = cj g S5That := by rw [← cj_That, That_std]
  have hz : zc (cj g S5Syl) = g * zStd * g⁻¹ :=
    zc_eq (card_cj_S5Syl g) (isCentInv_cj_std_iff.mpr rfl)
  rw [hT, hz, ← cj_zpowers, commW_cj_top, cenW_mp]
  exact Subgroup.map_mono cenW_commW_std_le

theorem That_le {D : Subgroup (Perm (Fin 5))} : That D ≤ D :=
  (Subgroup.closure_le _).mpr fun _ h => h.1

end CFSG.Quasithin.F53.Stellmacher.S35.E14
