module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518Ctx

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem z_ne_y2 (F : FanTree Γ G) (H : Lab18 L) (C : Ctx L T a) :
    L.z (xv T a 2) ≠ L.z (zA L T a 5 • xv T a 2) := by
  have hmove : ∀ i : ℤ, i ≤ 3 → zA L T a 5 • xv T a i ≠ xv T a i := fun i hi h =>
    absurd ((zA_fix C 5 i).1 h) (by omega)
  have hfix4 : zA L T a 5 • xv T a 4 = xv T a 4 := (zA_fix C 5 4).2 (by omega)
  have hbr : Br Γ (xv T a 4) (xv T a 3) (xv T a 2) := xv_br_bwd T a 2
  have hbr' : Br Γ (xv T a 4) (zA L T a 5 • xv T a 3) (zA L T a 5 • xv T a 2) := by
    have := Br.smul F (zA L T a 5) hbr
    rwa [hfix4] at this
  have hd : Γ.dist (xv T a 2) (zA L T a 5 • xv T a 2) = 4 :=
    dist_four F hbr hbr' (fun h => hmove 3 le_rfl h.symm)
  have h2 : valence Γ (xv T a 2) = 5 := C.val_even F 1
  have h2' : valence Γ (zA L T a 5 • xv T a 2) = 5 := by
    rw [F.valence_smul_eq]
    exact h2
  exact H.hyp.dist _ _ (fun h => hmove 2 (by omega) h.symm) h2 h2' (Or.inr hd)

theorem b3_of_ab (F : FanTree Γ G) (H : Lab18 L) (C : Ctx L T a)
    (ha : wE L T a * uE L T a = 1 ∨ wE L T a * uE L T a = L.z (xv T a 2))
    (hb : wE L T a * uE L T a = 1 ∨ wE L T a * uE L T a = L.z (zA L T a 5 • xv T a 2)) :
    wE L T a * uE L T a = 1 := by
  rcases ha with ha | ha
  · exact ha
  · rcases hb with hb | hb
    · exact hb
    · exact absurd (ha.symm.trans hb) (z_ne_y2 F H C)

end P518

end CFSG.Quasithin.Fan86
