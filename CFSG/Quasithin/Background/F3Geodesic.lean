module

public import CFSG.Quasithin.Background.F3Paths
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Nat.Periodic

public section

namespace CFSG.Quasithin

universe u

variable {V : Type u} {Γ : SimpleGraph V}

@[expose] def UniqueGeod (Γ : SimpleGraph V) (m : ℕ) : Prop :=
  ∀ (n : ℕ) (p q : GPath Γ n), p.IsGeodesic → q.IsGeodesic → p 0 = q 0 → p n = q n → n < m → p = q

@[expose] def IsPolygon (Γ : SimpleGraph V) (S : Set V) (k : ℕ) : Prop :=
  Nonempty (SimpleGraph.cycleGraph k ≃g Γ.induce S)

theorem cycleGraph_adj_iff {M : ℕ} (hM : 3 ≤ M) (i j : Fin M) :
    (SimpleGraph.cycleGraph M).Adj i j ↔
      (j.val = i.val + 1 ∨ i.val = j.val + 1 ∨ (i.val = 0 ∧ j.val = M - 1) ∨
        (j.val = 0 ∧ i.val = M - 1)) := by
  rw [SimpleGraph.cycleGraph_adj', Fin.val_sub, Fin.val_sub]
  have hi := i.2
  have hj := j.2
  by_cases hji : j.val ≤ i.val
  · have e1 : (M - j.val + i.val) % M = i.val - j.val := by
      have : M - j.val + i.val = (i.val - j.val) + M := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    by_cases hij : i.val ≤ j.val
    · have : i.val = j.val := le_antisymm hij hji
      have e2 : (M - i.val + j.val) % M = 0 := by
        have : M - i.val + j.val = M := by omega
        rw [this, Nat.mod_self]
      rw [e1, e2]
      omega
    · have e2 : (M - i.val + j.val) % M = M - (i.val - j.val) := by
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      rw [e1, e2]
      omega
  · have e1 : (M - j.val + i.val) % M = M - (j.val - i.val) := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have e2 : (M - i.val + j.val) % M = j.val - i.val := by
      have : M - i.val + j.val = (j.val - i.val) + M := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e1, e2]
    omega

theorem isPolygon_of_periodic_aux {m : ℕ} (hm : 2 ≤ m) (z : ℕ → V)
    (hadj : ∀ i, Γ.Adj (z i) (z (i + 1))) (hper : ∀ i, z (i + 2 * m) = z i)
    (hinj : ∀ i j, i < j → j < 2 * m → z i ≠ z j)
    (hAdj : ∀ i j, i < j → j < 2 * m → Γ.Adj (z i) (z j) → j = i + 1 ∨ (i = 0 ∧ j = 2 * m - 1)) :
    IsPolygon Γ (Set.range z) (2 * m) := by
  have hM : 0 < 2 * m := by omega
  let f : Fin (2 * m) → ↥(Set.range z) := fun i => ⟨z i, ⟨i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h1 : z a = z b := congrArg Subtype.val hab
      by_contra hne
      rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
      · exact hinj a b h b.2 h1
      · exact hinj b a h a.2 h1.symm
    · rintro ⟨v, ⟨j, rfl⟩⟩
      refine ⟨⟨j % (2 * m), Nat.mod_lt _ hM⟩, ?_⟩
      apply Subtype.ext
      show z (j % (2 * m)) = z j
      exact (Function.Periodic.map_mod_nat (f := z) (fun x => hper x)) j
  refine ⟨{ toEquiv := Equiv.ofBijective f hf, map_rel_iff' := ?_ }⟩
  intro a b
  show Γ.Adj (z a) (z b) ↔ (SimpleGraph.cycleGraph (2 * m)).Adj a b
  rw [cycleGraph_adj_iff (by omega)]
  constructor
  · intro h
    rcases lt_trichotomy a.val b.val with hab | hab | hab
    · rcases hAdj a b hab b.2 h with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inl h1))
    · exact absurd h (by rw [Fin.ext hab]; exact (SimpleGraph.irrefl _))
    · rcases hAdj b a hab a.2 h.symm with h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inr ⟨h1.1, h1.2⟩))
  · rintro (h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [h]; exact hadj a
    · rw [h]; exact (hadj b).symm
    · have h3 : Γ.Adj (z (2 * m - 1)) (z (2 * m - 1 + 1)) := hadj _
      have e : 2 * m - 1 + 1 = 0 + 2 * m := by omega
      rw [e, hper 0] at h3
      rw [h1, h2]
      exact h3.symm
    · have h3 : Γ.Adj (z (2 * m - 1)) (z (2 * m - 1 + 1)) := hadj _
      have e : 2 * m - 1 + 1 = 0 + 2 * m := by omega
      rw [e, hper 0] at h3
      rw [h1, h2]
      exact h3

namespace GPath

variable {c : V → Bool}

theorem isGeodesic_of_noBack (hΓ : Γ.Connected) (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) {m : ℕ}
    (hU : UniqueGeod Γ m) : ∀ (k : ℕ), k ≤ m → ∀ p : GPath Γ k, p.NoBack → p.IsGeodesic := by
  intro k
  induction k with
  | zero =>
    intro _ p _
    show Γ.dist (p 0) (p 0) = 0
    exact SimpleGraph.dist_self
  | succ k ih =>
    intro hk p hp
    have hgeo : (p.take k (Nat.le_succ k)).IsGeodesic := ih (by omega) _ (hp.take k _)
    have hgeo' : Γ.dist (p 0) (p k) = k := by
      have := hgeo
      simpa [IsGeodesic, take_apply_of_le _ _ _ (le_refl k),
        take_apply_of_le _ _ _ (Nat.zero_le k)] using this
    show Γ.dist (p 0) (p (k + 1)) = k + 1
    rcases dist_adj_succ_or hΓ hc (p 0) (p.adj k (Nat.lt_succ_self k)) with h | h
    · omega
    · exfalso
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hd : Γ.dist (p 0) (p (j + 1 + 1)) = j := by omega
      obtain ⟨q', hq0, hq', -⟩ := exists_geodesic' hΓ (p 0) (p (j + 1 + 1)) hd
      have hadj : Γ.Adj (q' j) (p (j + 1)) := by
        rw [hq']
        exact (p.adj (j + 1) (Nat.lt_succ_self _)).symm
      set q := q'.snoc (p (j + 1)) hadj with hq
      have hq_0 : q 0 = p 0 := by
        rw [hq, snoc_of_le _ _ _ (Nat.zero_le j), hq0]
      have hq_last : q (j + 1) = p (j + 1) := by
        rw [hq, snoc_last]
      have hqgeo : q.IsGeodesic := by
        show Γ.dist (q 0) (q (j + 1)) = j + 1
        rw [hq_0, hq_last]
        exact hgeo'
      have heq : q = p.take (j + 1) (Nat.le_succ _) :=
        hU (j + 1) q _ hqgeo hgeo
          (by rw [hq_0, take_apply_of_le _ _ _ (Nat.zero_le _)])
          (by rw [hq_last, take_apply_of_le _ _ _ (le_refl _)]) (by omega)
      have h2 : q j = (p.take (j + 1) (Nat.le_succ _)) j := congrArg (fun r : GPath Γ (j + 1) => r j) heq
      rw [hq, snoc_of_le _ _ _ (le_refl j), hq', take_apply_of_le _ _ _ (Nat.le_succ j)] at h2
      exact hp j le_rfl h2.symm

theorem two_mul_le_of_periodic (hΓ : Γ.Connected) (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) {m : ℕ}
    (hU : UniqueGeod Γ m) (z : ℕ → V) (hadj : ∀ i, Γ.Adj (z i) (z (i + 1)))
    (hnb : ∀ i, z i ≠ z (i + 2)) {M : ℕ} (hM : 0 < M) (hper : ∀ i, z (i + M) = z i) :
    2 * m ≤ M := by
  by_contra hlt0
  have hlt : M < 2 * m := not_le.mp hlt0
  have hM2 : 2 ≤ M := by
    by_contra h1
    have h2 : M = 1 := by omega
    subst h2
    exact (hadj 0).ne (hper 0).symm
  obtain ⟨k, hk⟩ : ∃ k, k = M / 2 := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, l = M - k := ⟨_, rfl⟩
  have hkl : k + l = M := by omega
  have hk1 : 1 ≤ k := by omega
  have hkm : k < m := by omega
  have hlm : l ≤ m := by omega
  let P1 : GPath Γ k := seqPath z hadj 0 k
  let P2 : GPath Γ l := seqPathRev z hadj M l (by omega)
  have hP1 : P1.NoBack := fun i hi h => by
    have h1 : P1 i = z i := by simp [P1, seqPath_apply z hadj 0 k (show i ≤ k by omega)]
    have h2 : P1 (i + 2) = z (i + 2) := by
      simp [P1, seqPath_apply z hadj 0 k (show i + 2 ≤ k by omega)]
    rw [h1, h2] at h
    exact hnb i h
  have hP2 : P2.NoBack := fun i hi h => by
    have h1 : P2 i = z (M - i) := by
      simp [P2, seqPathRev_apply z hadj M l (by omega) (show i ≤ l by omega)]
    have h2 : P2 (i + 2) = z (M - (i + 2)) := by
      simp [P2, seqPathRev_apply z hadj M l (by omega) (show i + 2 ≤ l by omega)]
    rw [h1, h2] at h
    have h3 : M - i = (M - (i + 2)) + 2 := by omega
    rw [h3] at h
    exact hnb _ h.symm
  have g1 : P1.IsGeodesic := isGeodesic_of_noBack hΓ hc hU k (by omega) P1 hP1
  have g2 : P2.IsGeodesic := isGeodesic_of_noBack hΓ hc hU l hlm P2 hP2
  have e10 : P1 0 = z 0 := by simp [P1]
  have e1k : P1 k = z k := by simp [P1]
  have e20 : P2 0 = z 0 := by
    have := hper 0
    simp only [zero_add] at this
    simp [P2, this]
  have e2l : P2 l = z k := by
    have : M - l = k := by omega
    simp [P2, this]
  have hd1 : Γ.dist (z 0) (z k) = k := by
    have := g1
    simpa [IsGeodesic, e10, e1k] using this
  have hd2 : Γ.dist (z 0) (z k) = l := by
    have := g2
    simpa [IsGeodesic, e20, e2l] using this
  have hkl' : k = l := hd1.symm.trans hd2
  subst hkl'
  have heq : P1 = P2 := hU k P1 P2 g1 g2 (by rw [e10, e20]) (by rw [e1k, e2l]) hkm
  have h1 : P1 1 = P2 1 := congrArg (fun r : GPath Γ k => r 1) heq
  have e11 : P1 1 = z 1 := by simp [P1, seqPath_apply z hadj 0 k hk1]
  have e21 : P2 1 = z (M - 1) := by
    simp [P2, seqPathRev_apply z hadj M k (by omega) hk1]
  rw [e11, e21] at h1
  have h2 := hnb (M - 1)
  have h3 : M - 1 + 2 = 1 + M := by omega
  rw [h3, hper 1] at h2
  exact h2 h1.symm

theorem window_dist (hΓ : Γ.Connected) (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) {m : ℕ}
    (hU : UniqueGeod Γ m) (z : ℕ → V) (hadj : ∀ i, Γ.Adj (z i) (z (i + 1)))
    (hnb : ∀ i, z i ≠ z (i + 2)) (i : ℕ) {d : ℕ} (hd : d ≤ m) : Γ.dist (z i) (z (i + d)) = d := by
  have hnb' : (seqPath z hadj i d).NoBack := fun j hj h => by
    rw [seqPath_apply z hadj i d (show j ≤ d by omega),
      seqPath_apply z hadj i d (show j + 2 ≤ d by omega), ← add_assoc] at h
    exact hnb (i + j) h
  have := isGeodesic_of_noBack hΓ hc hU d hd _ hnb'
  simpa [IsGeodesic] using this

theorem periodic_distinct_adj (hΓ : Γ.Connected) (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) {m : ℕ}
    (hU : UniqueGeod Γ m) (z : ℕ → V) (hadj : ∀ i, Γ.Adj (z i) (z (i + 1)))
    (hnb : ∀ i, z i ≠ z (i + 2)) (hper : ∀ i, z (i + 2 * m) = z i) :
    (∀ i j, i < j → j < 2 * m → z i ≠ z j) ∧
      (∀ i j, i < j → j < 2 * m → Γ.Adj (z i) (z j) → j = i + 1 ∨ (i = 0 ∧ j = 2 * m - 1)) := by
  have key : ∀ i j, i < j → j < 2 * m →
      (j - i ≤ m ∧ Γ.dist (z i) (z j) = j - i) ∨
      (m < j - i ∧ Γ.dist (z j) (z i) = 2 * m - (j - i)) := by
    intro i j hij hj
    by_cases h : j - i ≤ m
    · left
      refine ⟨h, ?_⟩
      have := window_dist hΓ hc hU z hadj hnb i h
      rwa [show i + (j - i) = j by omega] at this
    · right
      refine ⟨by omega, ?_⟩
      have h' : 2 * m - (j - i) ≤ m := by omega
      have := window_dist hΓ hc hU z hadj hnb j h'
      rwa [show j + (2 * m - (j - i)) = i + 2 * m by omega, hper] at this
  constructor
  · intro i j hij hj heq
    rcases key i j hij hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [heq, SimpleGraph.dist_self] at h2
      omega
    · rw [heq, SimpleGraph.dist_self] at h2
      omega
  · intro i j hij hj hA
    rcases key i j hij hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      have := SimpleGraph.dist_eq_one_iff_adj.mpr hA
      omega
    · right
      have := SimpleGraph.dist_eq_one_iff_adj.mpr hA.symm
      omega

theorem isPolygon_of_periodic (hΓ : Γ.Connected) (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) {m : ℕ}
    (hm : 2 ≤ m) (hU : UniqueGeod Γ m) (z : ℕ → V) (hadj : ∀ i, Γ.Adj (z i) (z (i + 1)))
    (hnb : ∀ i, z i ≠ z (i + 2)) (hper : ∀ i, z (i + 2 * m) = z i) :
    IsPolygon Γ (Set.range z) (2 * m) := by
  obtain ⟨h1, h2⟩ := periodic_distinct_adj hΓ hc hU z hadj hnb hper
  exact isPolygon_of_periodic_aux hm z hadj hper h1 h2

theorem periodic_eq_iff (hΓ : Γ.Connected) (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) {m : ℕ}
    (hm : 1 ≤ m) (hU : UniqueGeod Γ m) (z : ℕ → V) (hadj : ∀ i, Γ.Adj (z i) (z (i + 1)))
    (hnb : ∀ i, z i ≠ z (i + 2)) (hper : ∀ i, z (i + 2 * m) = z i) (i j : ℕ) :
    z i = z j ↔ i % (2 * m) = j % (2 * m) := by
  obtain ⟨h1, -⟩ := periodic_distinct_adj hΓ hc hU z hadj hnb hper
  have hmod : ∀ a, z a = z (a % (2 * m)) := fun a =>
    ((Function.Periodic.map_mod_nat (f := z) (fun x => hper x)) a).symm
  have hlt : 0 < 2 * m := by omega
  constructor
  · intro h
    rw [hmod i, hmod j] at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact h1 _ _ h' (Nat.mod_lt _ hlt) h
    · exact h1 _ _ h' (Nat.mod_lt _ hlt) h.symm
  · intro h
    rw [hmod i, hmod j, h]

end GPath

end CFSG.Quasithin
