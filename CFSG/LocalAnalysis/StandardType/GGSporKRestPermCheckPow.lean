module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheck

public section

namespace CFSG.StandardType.SporadicShape.PermCover

open Equiv

@[expose] def specPow {n : ℕ} (p : ℕ) (a b : Perm (Fin n)) (sylowOrder : ℕ) (d : Data) : Prop :=
  (tab a b d).length = sylowOrder ∧ (tab a b d).Nodup ∧ (1 : Perm (Fin n)) ∈ tab a b d ∧
  (∀ t ∈ tab a b d, ∀ g ∈ sg a b d, t * g ∈ tab a b d ∧ t * g⁻¹ ∈ tab a b d) ∧
  (∀ c ∈ d.classes,
    (∀ e ∈ c.ent, e.idx < (tab a b d).length ∧
      (sporKRestEval [a, b] (sporKRestParse e.h))⁻¹ * rep a b c * sporKRestEval [a, b] (sporKRestParse e.h) = (tab a b d).getD e.idx 1 ∧
      ∀ zw ∈ e.zs, sporKRestEval [a, b] (sporKRestParse zw) * (tab a b d).getD e.idx 1 =
        (tab a b d).getD e.idx 1 * sporKRestEval [a, b] (sporKRestParse zw)) ∧
    sporKRestEval (letters a b d c) (sporKRestParse c.wa) = a ∧ sporKRestEval (letters a b d c) (sporKRestParse c.wb) = b) ∧
  (∀ t ∈ tab a b d, t ≠ 1 → t ^ p = 1 → ∃ e ∈ d.census, e.cls < d.classes.length ∧ (tab a b d).getD e.t 1 = t ∧
    (sporKRestEval [a, b] (sporKRestParse e.g))⁻¹ * rep a b (d.classes.getD e.cls ⟨"", [], "", ""⟩) *
      sporKRestEval [a, b] (sporKRestParse e.g) = t)

@[expose] def checkPow {n : ℕ} (p : ℕ) (a b : Perm (Fin n)) (sylowOrder : ℕ) (d : Data) : Bool :=
  let sg := sg a b d
  let tab := tab a b d
  decide (tab.length = sylowOrder) && decide tab.Nodup && decide ((1 : Perm (Fin n)) ∈ tab) &&
  tab.all (fun t => sg.all fun g => decide (t * g ∈ tab) && decide (t * g⁻¹ ∈ tab)) &&
  d.classes.all (fun c =>
    c.ent.all (fun e => decide (e.idx < tab.length) &&
      decide ((sporKRestEval [a, b] (sporKRestParse e.h))⁻¹ * rep a b c * sporKRestEval [a, b] (sporKRestParse e.h) = tab.getD e.idx 1) &&
      e.zs.all fun zw => decide (sporKRestEval [a, b] (sporKRestParse zw) * tab.getD e.idx 1 =
        tab.getD e.idx 1 * sporKRestEval [a, b] (sporKRestParse zw))) &&
    decide (sporKRestEval (letters a b d c) (sporKRestParse c.wa) = a) &&
    decide (sporKRestEval (letters a b d c) (sporKRestParse c.wb) = b)) &&
  tab.all (fun t => decide (t = 1) || decide (t ^ p ≠ 1) || d.census.any fun e => decide (e.cls < d.classes.length) &&
    decide (tab.getD e.t 1 = t) &&
    decide ((sporKRestEval [a, b] (sporKRestParse e.g))⁻¹ * rep a b (d.classes.getD e.cls ⟨"", [], "", ""⟩) *
      sporKRestEval [a, b] (sporKRestParse e.g) = t))

theorem checkPow_sound {n : ℕ} {p : ℕ} {a b : Perm (Fin n)} {sylowOrder : ℕ} {d : Data}
    (h : checkPow p a b sylowOrder d = true) : specPow p a b sylowOrder d := by
  unfold checkPow at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true] at h
  unfold specPow
  refine ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, ?_, ?_⟩
  · intro c hc
    obtain ⟨⟨hent, hwa⟩, hwb⟩ := h.1.2 c hc
    refine ⟨?_, hwa, hwb⟩
    intro e he
    obtain ⟨⟨hidx, hh⟩, hzs⟩ := hent e he
    exact ⟨hidx, hh, hzs⟩
  · intro t ht hne hp
    rcases h.2 t ht with h1 | h1
    · rcases h1 with h1 | h1
      · exact absurd h1 hne
      · exact absurd hp h1
    · obtain ⟨e, he, ⟨⟨hcls, hget⟩, hconj⟩⟩ := h1
      exact ⟨e, he, hcls, hget, hconj⟩

end CFSG.StandardType.SporadicShape.PermCover
