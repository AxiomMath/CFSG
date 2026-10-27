module

public import Mathlib.Data.ZMod.Basic

import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.E9

abbrev Z3 := ZMod 3 × ZMod 3

@[expose] def ev (a b c d : ZMod 3) (x : Z3) : Z3 := (a * x.1 + c * x.2, b * x.1 + d * x.2)

theorem addhom_apply (F : Z3 →+ Z3) :
    ∃ a b c d : ZMod 3, ∀ x : Z3, F x = ev a b c d x := by
  refine ⟨(F (1, 0)).1, (F (1, 0)).2, (F (0, 1)).1, (F (0, 1)).2, fun x => ?_⟩
  have hx : x = x.1.val • ((1 : ZMod 3), (0 : ZMod 3)) +
      x.2.val • ((0 : ZMod 3), (1 : ZMod 3)) := by
    ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add, map_nsmul, map_nsmul]
  ext <;> simp [ev] <;> ring

set_option synthInstance.maxSize 20000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem key_poly : ∀ a1 b1 c1 d1 am bm cm dm : ZMod 3,
    (∀ x, ev am bm cm dm (ev a1 b1 c1 d1 x) = ev a1 b1 c1 d1 (ev am bm cm dm x)) →
    ¬ (bm = 0 ∧ cm = 0 ∧ am = dm) →
    ∃ s t : ZMod 3, a1 = s + t * am ∧ b1 = t * bm ∧ c1 = t * cm ∧ d1 = s + t * dm := by
  decide +kernel

set_option synthInstance.maxSize 20000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem key_commute : ∀ s1 t1 s2 t2 am bm cm dm : ZMod 3, ∀ x,
    ev (s1 + t1 * am) (t1 * bm) (t1 * cm) (s1 + t1 * dm)
      (ev (s2 + t2 * am) (t2 * bm) (t2 * cm) (s2 + t2 * dm) x) =
    ev (s2 + t2 * am) (t2 * bm) (t2 * cm) (s2 + t2 * dm)
      (ev (s1 + t1 * am) (t1 * bm) (t1 * cm) (s1 + t1 * dm) x) := by
  decide +kernel

theorem comm_scalar (F₁ F₂ M : Z3 →+ Z3) (hnc : ∃ x, F₁ (F₂ x) ≠ F₂ (F₁ x))
    (h1 : ∀ x, M (F₁ x) = F₁ (M x)) (h2 : ∀ x, M (F₂ x) = F₂ (M x)) :
    ∃ l : ZMod 3, ∀ x, M x = (l * x.1, l * x.2) := by
  obtain ⟨a1, b1, c1, d1, e1⟩ := addhom_apply F₁
  obtain ⟨a2, b2, c2, d2, e2⟩ := addhom_apply F₂
  obtain ⟨am, bm, cm, dm, em⟩ := addhom_apply M
  by_cases hs : bm = 0 ∧ cm = 0 ∧ am = dm
  · obtain ⟨hb, hc, ha⟩ := hs
    refine ⟨am, fun x => ?_⟩
    rw [em]
    simp [ev, hb, hc, ← ha]
  · exfalso
    have p1 := key_poly a1 b1 c1 d1 am bm cm dm (fun x => by
      rw [← em, ← e1, ← e1, h1]; rw [em, e1]) hs
    have p2 := key_poly a2 b2 c2 d2 am bm cm dm (fun x => by
      rw [← em, ← e2, ← e2, h2]; rw [em, e2]) hs
    obtain ⟨s1, t1, ha1, hb1, hc1, hd1⟩ := p1
    obtain ⟨s2, t2, ha2, hb2, hc2, hd2⟩ := p2
    obtain ⟨x, hx⟩ := hnc
    apply hx
    rw [e1, e2, e2, e1, ha1, hb1, hc1, hd1, ha2, hb2, hc2, hd2]
    exact key_commute s1 t1 s2 t2 am bm cm dm x

end CFSG.RankThree.PartTwo.Sec21.FF79.E9
