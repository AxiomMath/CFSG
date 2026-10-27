module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Orb0
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Orb2

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem cIdx_le_sq (S : B2Set F L T a) {x : G} (hx : x ∈ MulAction.stabilizer G (xv T a 6))
    (hxo : orderOf x = 5) :
    cIdx Γ x (xv T a 6) ≤
      ((nbrStab Γ G (xv T a 6) ⊓ MulAction.stabilizer G (xv T a 0)).relIndex
        (nbrStab Γ G (xv T a 6))) ^ 2 := by
  have hv6 : valence Γ (pv T a 0) = 5 := by simpa [pv] using S.val_even 3
  have hfix : ∀ j : ℕ, j ≤ 6 → zA L T a 0 • pv T a j = pv T a j := fun j hj =>
    (S.zA_fix_iff 0 (6 - (j : ℤ))).2 ⟨by omega, by omega⟩
  have hc : ∀ g : G, g • pv T a (6 - 1) = pv T a (6 - 1) → g • pv T a 6 = pv T a 6 →
      g * zA L T a 0 = zA L T a 0 * g := by
    intro g _ h6
    have hg : g ∈ MulAction.stabilizer G (xv T a 0) :=
      MulAction.mem_stabilizer_iff.2 (by simpa [pv] using h6)
    exact (L.isCentral _ S.ctx.val5).2.2.2 g hg
  have hK : zA L T a 0 ∉ nbrStab Γ G (pv T a 0) := by
    intro h
    have h7 := mem_nbrStab.1 h (xv T a (6 + 1)) (xv_adj T a 6)
    have := (S.zA_fix_iff 0 (6 + 1)).1 h7
    omega
  have h := fan52_ray_orb F (pv_adj T a) (pv_nb T a) (m := 6) (by norm_num) (z := zA L T a 0)
    (zA_sq F S.ctx 0) hfix hc hK (x := x) (by simpa [pv] using hx) (by rw [hxo, hv6])
  simpa [pv, cIdx] using h

theorem orbit_chain (S : B2Set F L T a) :
    (nbrStab Γ G (xv T a 6) ⊓ MulAction.stabilizer G (xv T a 0)).relIndex
      (nbrStab Γ G (xv T a 6)) ≤ 2 * nOrb T a * 2 * nOrb T a * 2 := by
  let f : ℕ → ℕ := fun j => if j = 2 ∨ j = 4 then nOrb T a else 2
  have hf : ∀ j, 1 ≤ j → j < 6 → (nbrStab Γ G (pv T a j)).relIndex
      (nbrStab Γ G (pv T a 0) ⊓ MulAction.stabilizer G (pv T a j)) ≤ f j := by
    intro j h1 h6
    have hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · simpa [f] using stage_three F (pv_adj T a) (pv_nb T a) (j := 1) le_rfl
        (by simpa [pv] using S.val_odd 2)
    · simpa [f, pv] using (stage_x4 S).le
    · simpa [f] using stage_three F (pv_adj T a) (pv_nb T a) (j := 3) (by norm_num)
        (by simpa [pv] using S.val_odd 1)
    · simpa [f, pv] using stage_x2 S
    · simpa [f] using stage_three F (pv_adj T a) (pv_nb T a) (j := 5) (by norm_num)
        (by simpa [pv] using S.val_odd 0)
  have hchain := relIndex_chain_img F (pv_adj T a) (pv_nb T a) (m := 6) f hf 6 (by norm_num)
    le_rfl
  have hprod : ∏ j ∈ Finset.Ico 1 6, f j = 2 * nOrb T a * 2 * nOrb T a * 2 := by
    rw [Finset.prod_Ico_eq_prod_range]
    simp [Finset.prod_range_succ, f]
  rw [hprod] at hchain
  simpa [pv] using hchain

end P518

end CFSG.Quasithin.Fan86
