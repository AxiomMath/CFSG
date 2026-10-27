module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24ECheck
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Facts
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24EData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi24K

open CFSG.Blueprint CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.QuasithinUnique.K1.SporadicPerm (img img_tab act_eq tab genTabs)

@[expose] def fi24ESt : List (Array ℕ) := [
  #[16, 18, 11, 14, 8, 1, 4, 20, 12, 5, 23, 21, 6, 2, 17, 22, 10, 19, 9, 3, 15, 13, 7, 0],
  #[7, 1, 3, 2, 5, 4, 6, 0, 8, 9, 21, 20, 18, 13, 16, 17, 14, 15, 12, 19, 11, 10, 22, 23],
  #[7, 1, 2, 3, 12, 5, 8, 0, 6, 9, 10, 23, 4, 20, 22, 15, 19, 21, 18, 16, 13, 17, 14, 11],
  #[23, 1, 13, 19, 4, 5, 6, 22, 8, 9, 20, 17, 12, 2, 21, 16, 15, 11, 18, 3, 10, 14, 7, 0]]

theorem m24STabs_eq_fi24ESt : m24STabs = fi24ESt := by decide +kernel

theorem fi24ESb_conj : ∀ k : Fin 4, ∀ j : Fin 24,
    (fi24ESb[k.val]!)[(fi24EC j).val]! =
      (fi24EC (Fin.ofNat 24 (img fi24ESt[k.val]! j.val))).val := by
  decide +kernel

theorem length_m24Sg : m24Sg.length = 4 := by
  have h := congrArg List.length m24_sGens.1
  rwa [genTabs, List.length_map, m24STabs_eq_fi24ESt] at h

theorem val_m24Sg_apply {k : ℕ} (hk : k < m24Sg.length) (j : Fin 24) :
    ((m24Sg[k] : Equiv.Perm (Fin 24)) j).val = img fi24ESt[k]! j.val := by
  have e : fi24ESt[k]! = (tab 24 m24Sg[k]).toArray := by
    rw [← m24STabs_eq_fi24ESt, ← m24_sGens.1, genTabs,
      getElem!_pos _ k (by rw [List.length_map]; exact hk), List.getElem_map]
  rw [e, img_tab, act_eq]
  rfl

theorem fi24ESb_eq {k : ℕ} (hk : k < m24Sg.length) (i : Fin 24) :
    (fi24ESb[k]!)[i.val]! = ((fi24EC * (m24Sg[k] : Equiv.Perm (Fin 24)) * fi24EC⁻¹) i).val := by
  obtain ⟨j, rfl⟩ := fi24EC.surjective i
  have hk4 : k < 4 := length_m24Sg ▸ hk
  have h1 : (fi24ESb[k]!)[(fi24EC j).val]! =
      (fi24EC (Fin.ofNat 24 (img fi24ESt[k]! j.val))).val := fi24ESb_conj ⟨k, hk4⟩ j
  rw [h1, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv, Equiv.symm_apply_apply,
    ← val_m24Sg_apply hk j, Fin.ofNat_val_eq_self]

end Fi24K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
