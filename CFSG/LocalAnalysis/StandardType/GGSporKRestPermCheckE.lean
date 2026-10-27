module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheck
public import CFSG.LocalAnalysis.StandardType.GGSporKRestIdx

public section

namespace CFSG.StandardType.SporadicShape.PermCover

open Equiv

structure DataE where
  base : Data
  mulS : String

@[expose] def parseMul (s : String) : List (List ℕ) :=
  (s.splitOn ";").map fun row => (row.splitOn " ").filterMap String.toNat?

@[expose] def goodOf (d : Data) (n : ℕ) : List Bool :=
  (List.range n).map fun i => d.census.any fun e => e.t == i

@[expose] def specE {n : ℕ} (p : ℕ) (a b : Perm (Fin n)) (sylowOrder : ℕ) (d : DataE) : Prop :=
  (tab a b d.base).length = sylowOrder ∧ (tab a b d.base).Nodup ∧
  (tab a b d.base).getD 0 1 = 1 ∧
  (∀ t ∈ tab a b d.base, ∀ g ∈ sg a b d.base,
    t * g ∈ tab a b d.base ∧ t * g⁻¹ ∈ tab a b d.base) ∧
  (∀ c ∈ d.base.classes,
    (∀ e ∈ c.ent, e.idx < (tab a b d.base).length ∧
      (sporKRestEval [a, b] (sporKRestParse e.h))⁻¹ * rep a b c * sporKRestEval [a, b] (sporKRestParse e.h) =
        (tab a b d.base).getD e.idx 1 ∧
      ∀ zw ∈ e.zs, sporKRestEval [a, b] (sporKRestParse zw) * (tab a b d.base).getD e.idx 1 =
        (tab a b d.base).getD e.idx 1 * sporKRestEval [a, b] (sporKRestParse zw)) ∧
    sporKRestEval (letters a b d.base c) (sporKRestParse c.wa) = a ∧
      sporKRestEval (letters a b d.base c) (sporKRestParse c.wb) = b) ∧
  (∀ e ∈ d.base.census, e.cls < d.base.classes.length ∧ e.t < (tab a b d.base).length ∧ e.t ≠ 0 ∧
    (sporKRestEval [a, b] (sporKRestParse e.g))⁻¹ *
      rep a b (d.base.classes.getD e.cls ⟨"", [], "", ""⟩) * sporKRestEval [a, b] (sporKRestParse e.g) =
        (tab a b d.base).getD e.t 1) ∧
  (∀ i < (tab a b d.base).length, ∀ j < (tab a b d.base).length,
    sporKRestMulIdx (parseMul d.mulS) i j < (tab a b d.base).length ∧
      (tab a b d.base).getD i 1 * (tab a b d.base).getD j 1 =
        (tab a b d.base).getD (sporKRestMulIdx (parseMul d.mulS) i j) 1) ∧
  sporKRestECond (tab a b d.base).length p (parseMul d.mulS)
    (goodOf d.base (tab a b d.base).length) = true

@[expose] def checkE {n : ℕ} (p : ℕ) (a b : Perm (Fin n)) (sylowOrder : ℕ) (d : DataE) : Bool :=
  let sg := sg a b d.base
  let tab := tab a b d.base
  let mul := parseMul d.mulS
  decide (tab.length = sylowOrder) && decide tab.Nodup && decide (tab.getD 0 1 = 1) &&
  tab.all (fun t => sg.all fun g => decide (t * g ∈ tab) && decide (t * g⁻¹ ∈ tab)) &&
  d.base.classes.all (fun c =>
    c.ent.all (fun e => decide (e.idx < tab.length) &&
      decide ((sporKRestEval [a, b] (sporKRestParse e.h))⁻¹ * rep a b c * sporKRestEval [a, b] (sporKRestParse e.h) =
        tab.getD e.idx 1) &&
      e.zs.all fun zw => decide (sporKRestEval [a, b] (sporKRestParse zw) * tab.getD e.idx 1 =
        tab.getD e.idx 1 * sporKRestEval [a, b] (sporKRestParse zw))) &&
    decide (sporKRestEval (letters a b d.base c) (sporKRestParse c.wa) = a) &&
    decide (sporKRestEval (letters a b d.base c) (sporKRestParse c.wb) = b)) &&
  d.base.census.all (fun e => decide (e.cls < d.base.classes.length) && decide (e.t < tab.length) &&
    decide (e.t ≠ 0) &&
    decide ((sporKRestEval [a, b] (sporKRestParse e.g))⁻¹ *
      rep a b (d.base.classes.getD e.cls ⟨"", [], "", ""⟩) * sporKRestEval [a, b] (sporKRestParse e.g) =
        tab.getD e.t 1)) &&
  (List.range tab.length).all (fun i => (List.range tab.length).all fun j =>
    decide (sporKRestMulIdx mul i j < tab.length) &&
      decide (tab.getD i 1 * tab.getD j 1 = tab.getD (sporKRestMulIdx mul i j) 1)) &&
  sporKRestECond tab.length p mul (goodOf d.base tab.length)

theorem checkE_sound {n : ℕ} {p : ℕ} {a b : Perm (Fin n)} {sylowOrder : ℕ} {d : DataE}
    (h : checkE p a b sylowOrder d = true) : specE p a b sylowOrder d := by
  unfold checkE at h
  dsimp only at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  unfold specE
  refine ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, ?_, ?_,
    h.1.2, h.2⟩
  · intro c hc
    obtain ⟨⟨hent, hwa⟩, hwb⟩ := h.1.1.1.2 c hc
    refine ⟨?_, hwa, hwb⟩
    intro e he
    obtain ⟨⟨hidx, hh⟩, hzs⟩ := hent e he
    exact ⟨hidx, hh, hzs⟩
  · intro e he
    obtain ⟨⟨⟨hcls, ht⟩, hne⟩, hconj⟩ := h.1.1.2 e he
    exact ⟨hcls, ht, hne, hconj⟩

end CFSG.StandardType.SporadicShape.PermCover
