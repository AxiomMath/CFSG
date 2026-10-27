module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z1a

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24
open scoped Pointwise

@[expose] noncomputable def rho1 :
    ↥Z1 →* Equiv.Perm (Fin LO.length) :=
  listHom Z1 LO LO_nodup Z1_inv

theorem gens1_mem : ∀ x ∈ gens1, x ∈ Z1 := fun _ hx => Subgroup.subset_closure hx

theorem gens1_length : gens1.length = 5 := by
  simp [gens1, m24Sg_length]

@[expose] def wS : List (List ℕ) := [[0], [1], [2], [3]]

@[expose] def wE9 : List (List ℕ) :=
  [[3, 4, 1, 4, 4, 0, 4, 0, 1, 0, 0], [2, 0, 1, 2, 4, 0, 4, 0, 2, 4]]

@[expose] def img1 (ws : List (List ℕ)) : List (List ℕ) :=
  ws.map (fun w => indTab actPt LO (wordTab 24 gens1T w))

theorem enum1_S : EnumOK 8 (img1 wS) (bfsL 8 (img1 wS) 200).1 (bfsL 8 (img1 wS) 200).2 := by
  decide +kernel

theorem len1_S : (bfsL 8 (img1 wS) 200).1.length = 64 := by decide +kernel

theorem enum1_E9 : EnumOK 8 (img1 wE9) (bfsL 8 (img1 wE9) 200).1 (bfsL 8 (img1 wE9) 200).2 := by
  decide +kernel

theorem len1_E9 : (bfsL 8 (img1 wE9) 200).1.length = 9 := by decide +kernel

theorem enum1_5 : EnumOK 8 (img1 [[4]]) (bfsL 8 (img1 [[4]]) 200).1
    (bfsL 8 (img1 [[4]]) 200).2 := by decide +kernel

theorem len1_5 : (bfsL 8 (img1 [[4]]) 200).1.length = 5 := by decide +kernel

theorem enum1_7 : EnumOK 8 (img1 [y7w]) (bfsL 8 (img1 [y7w]) 200).1
    (bfsL 8 (img1 [y7w]) 200).2 := by decide +kernel

theorem len1_7 : (bfsL 8 (img1 [y7w]) 200).1.length = 7 := by decide +kernel

theorem rho1_dvd : 20160 ∣ Nat.card (rho1).range := by
  have hn : ∀ ws : List (List ℕ), (∀ w ∈ ws, ∀ l ∈ w, l < 5) →
      ∀ {Lg par}, EnumOK 8 (img1 ws) Lg par → Lg.length ∣ Nat.card (rho1).range :=
    fun ws hws {Lg par} h => card_dvd_range_words actPt hact_pt LO LO_nodup Z1_inv gens1 gens1_mem
      gens1T gens1_tab ws (by rw [gens1_length]; exact hws) h
  have h64 := hn wS (by decide) enum1_S
  have h9 := hn wE9 (by decide) enum1_E9
  have h5 := hn [[4]] (by decide) enum1_5
  have h7 := hn [y7w] (by decide) enum1_7
  rw [len1_S] at h64
  rw [len1_E9] at h9
  rw [len1_5] at h5
  rw [len1_7] at h7
  omega

end CFSG.Quasithin.A312M24
