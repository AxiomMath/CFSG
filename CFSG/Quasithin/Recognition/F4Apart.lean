module

public import CFSG.Quasithin.Recognition.F4Thirteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w'

namespace GPath

variable {V : Type u} {Γ : SimpleGraph V}

@[expose] noncomputable def polyWalk {M : ℕ} (hM : 0 < M) {S : Set V}
    (φ : SimpleGraph.cycleGraph M ≃g Γ.induce S) (i₀ k : ℕ) : V :=
  (φ ⟨(i₀ + k) % M, Nat.mod_lt _ hM⟩ : ↥S)

variable {M : ℕ} (hM : 0 < M) {S : Set V} (φ : SimpleGraph.cycleGraph M ≃g Γ.induce S) (i₀ : ℕ)

theorem polyWalk_mem (k : ℕ) : polyWalk hM φ i₀ k ∈ S :=
  (φ ⟨(i₀ + k) % M, Nat.mod_lt _ hM⟩).2

theorem polyWalk_per (k : ℕ) : polyWalk hM φ i₀ (k + M) = polyWalk hM φ i₀ k := by
  unfold polyWalk
  have : (i₀ + (k + M)) % M = (i₀ + k) % M := by
    rw [← add_assoc, Nat.add_mod_right]
  simp only [this]

theorem polyWalk_adj (hM3 : 3 ≤ M) (k : ℕ) :
    Γ.Adj (polyWalk hM φ i₀ k) (polyWalk hM φ i₀ (k + 1)) := by
  have h1 : (Γ.induce S).Adj (φ ⟨(i₀ + k) % M, Nat.mod_lt _ hM⟩)
      (φ ⟨(i₀ + (k + 1)) % M, Nat.mod_lt _ hM⟩) := by
    rw [φ.map_rel_iff, cycleGraph_adj_iff hM3]
    simp only
    have hlt := Nat.mod_lt (i₀ + k) hM
    by_cases hc : (i₀ + k) % M + 1 < M
    · left
      have : (i₀ + (k + 1)) % M = (i₀ + k) % M + 1 := by
        rw [← add_assoc, Nat.add_mod, Nat.mod_eq_of_lt (show 1 < M by omega),
          Nat.mod_eq_of_lt hc]
      exact this
    · right; right; right
      refine ⟨?_, ?_⟩
      · have : (i₀ + (k + 1)) % M = 0 := by
          rw [← add_assoc, Nat.add_mod, Nat.mod_eq_of_lt (show 1 < M by omega)]
          have : (i₀ + k) % M + 1 = M := by omega
          rw [this, Nat.mod_self]
        exact this
      · omega
  exact h1

theorem polyWalk_nb (hM3 : 3 ≤ M) (k : ℕ) :
    polyWalk hM φ i₀ k ≠ polyWalk hM φ i₀ (k + 2) := by
  intro h
  have h1 : φ ⟨(i₀ + k) % M, Nat.mod_lt _ hM⟩ = φ ⟨(i₀ + (k + 2)) % M, Nat.mod_lt _ hM⟩ :=
    Subtype.ext h
  have h2 := φ.injective h1
  have h3 : (i₀ + k) % M = (i₀ + (k + 2)) % M := congrArg Fin.val h2
  have h4 := Nat.sub_mod_eq_zero_of_mod_eq h3.symm
  rw [show i₀ + (k + 2) - (i₀ + k) = 2 by omega] at h4
  have h5 := Nat.le_of_dvd (by norm_num) (Nat.dvd_of_mod_eq_zero h4)
  omega

theorem polyWalk_surj (v : V) (hv : v ∈ S) :
    ∃ k, k < M ∧ polyWalk hM φ i₀ k = v := by
  obtain ⟨j, hj⟩ := φ.surjective ⟨v, hv⟩
  refine ⟨(j.val + M - i₀ % M) % M, Nat.mod_lt _ hM, ?_⟩
  have h1 : (i₀ + (j.val + M - i₀ % M) % M) % M = (i₀ + (j.val + M - i₀ % M)) % M :=
    Nat.add_mod_mod _ _ _
  have h2 : i₀ + (j.val + M - i₀ % M) = j.val + M * (i₀ / M + 1) := by
    have := Nat.mod_add_div i₀ M
    have hr := Nat.mod_lt i₀ hM
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have h3 : (j.val + M * (i₀ / M + 1)) % M = j.val := by
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt j.2
  have h4 : (i₀ + (j.val + M - i₀ % M) % M) % M = j.val := by rw [h1, h2, h3]
  unfold polyWalk
  have h5 : (⟨(i₀ + (j.val + M - i₀ % M) % M) % M, Nat.mod_lt _ hM⟩ : Fin M) = j :=
    Fin.ext h4
  rw [h5, hj]

theorem polyWalk_zero (i : Fin M) : polyWalk hM φ i.val 0 = (φ i : V) := by
  unfold polyWalk
  have : (⟨(i.val + 0) % M, Nat.mod_lt _ hM⟩ : Fin M) = i :=
    Fin.ext (show (i.val + 0) % M = i.val by rw [Nat.add_zero]; exact Nat.mod_eq_of_lt i.2)
  rw [this]

end GPath

namespace GPath

variable {V : Type u} {Γ : SimpleGraph V}

theorem exists_arcs_of_polygon (hΓ : Γ.Connected) {m : ℕ} (hm : 2 ≤ m) {S : Set V}
    (hS : IsPolygon Γ S (2 * m)) {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hab : Γ.dist a b = m) :
    ∃ p q : GPath Γ m, p.IsGeodesic ∧ q.IsGeodesic ∧ p 0 = a ∧ q 0 = a ∧ p m = b ∧ q m = b ∧
      p ≠ q ∧ S = Set.range (cycSeq p q) := by
  obtain ⟨φ⟩ := hS
  have hM : 0 < 2 * m := by omega
  have hM3 : 3 ≤ 2 * m := by omega
  obtain ⟨i₀, hi₀⟩ := φ.surjective ⟨a, ha⟩
  set z := polyWalk hM φ i₀.val with hz
  have hz0 : z 0 = a := by
    rw [hz, polyWalk_zero hM φ i₀, hi₀]
  have hadj : ∀ i, Γ.Adj (z i) (z (i + 1)) := polyWalk_adj hM φ i₀.val hM3
  have hper : ∀ i, z (i + 2 * m) = z i := polyWalk_per hM φ i₀.val
  have hnb : ∀ i, z i ≠ z (i + 2) := polyWalk_nb hM φ i₀.val hM3
  obtain ⟨d, hd, hdb0⟩ := polyWalk_surj hM φ i₀.val b hb
  have hdb : z d = b := hdb0
  have hdm : d = m := by
    have h1 : Γ.dist (z 0) (z d) ≤ d := by
      have := dist_le_length hΓ (seqPath z hadj 0 d)
      rwa [seqPath_apply _ _ _ _ (Nat.zero_le d), seqPath_apply _ _ _ _ le_rfl, Nat.zero_add,
        Nat.zero_add] at this
    have h2 : Γ.dist (z d) (z 0) ≤ 2 * m - d := by
      have := dist_le_length hΓ (seqPath z hadj d (2 * m - d))
      rwa [seqPath_apply _ _ _ _ (Nat.zero_le _), seqPath_apply _ _ _ _ le_rfl, Nat.add_zero,
        show d + (2 * m - d) = 0 + 2 * m by omega, hper 0] at this
    rw [hz0, hdb, hab] at h1
    rw [hz0, hdb, SimpleGraph.dist_comm, hab] at h2
    omega
  have hzm : z m = b := by rw [← hdm]; exact hdb
  have hm' : 1 ≤ m := by omega
  refine ⟨arc₁ z hadj m 0, arc₂ z hadj m 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Γ.dist (arc₁ z hadj m 0 0) (arc₁ z hadj m 0 m) = m
    rw [arc₁_zero, arc₁_last, hz0, Nat.zero_add, hzm, hab]
  · show Γ.dist (arc₂ z hadj m 0 0) (arc₂ z hadj m 0 m) = m
    rw [arc₂_zero z hadj m hper, arc₂_last, hz0, Nat.zero_add, hzm, hab]
  · rw [arc₁_zero, hz0]
  · rw [arc₂_zero z hadj m hper, hz0]
  · rw [arc₁_last, Nat.zero_add, hzm]
  · rw [arc₂_last, Nat.zero_add, hzm]
  · exact arc_ne z hadj hnb m hper hm' 0
  ·
    have hcyc : ∀ i, cycSeq (arc₁ z hadj m 0) (arc₂ z hadj m 0) i = z i := by
      have h0 : arc₁ z hadj m 0 0 = arc₂ z hadj m 0 0 := by
        rw [arc₁_zero, arc₂_zero z hadj m hper]
      have hmm : arc₁ z hadj m 0 m = arc₂ z hadj m 0 m := by
        rw [arc₁_last, arc₂_last]
      have hbase : ∀ i, i ≤ 2 * m →
          cycSeq (arc₁ z hadj m 0) (arc₂ z hadj m 0) i = z i := by
        intro i hi
        by_cases him : i ≤ m
        · rw [cycSeq_of_le _ _ hm' him, arc₁, seqPath_apply _ _ _ _ him, Nat.zero_add]
        · rw [cycSeq_of_ge _ _ hm' h0 hmm (by omega) hi, arc₂,
            seqPathRev_apply _ _ _ _ _ (by omega)]
          congr 1
          omega
      intro i
      have e1 : cycSeq (arc₁ z hadj m 0) (arc₂ z hadj m 0) i =
          cycSeq (arc₁ z hadj m 0) (arc₂ z hadj m 0) (i % (2 * m)) :=
        ((Function.Periodic.map_mod_nat (f := cycSeq (arc₁ z hadj m 0) (arc₂ z hadj m 0))
          (fun x => cycSeq_per _ _ x)) i).symm
      have e2 : z i = z (i % (2 * m)) :=
        ((Function.Periodic.map_mod_nat (f := z) (fun x => hper x)) i).symm
      rw [e1, e2]
      exact hbase _ (by have := Nat.mod_lt i hM; omega)
    ext v
    constructor
    · intro hv
      obtain ⟨k, -, hk⟩ := polyWalk_surj hM φ i₀.val v hv
      exact ⟨k, by rw [hcyc]; exact hk⟩
    · rintro ⟨k, rfl⟩
      rw [hcyc]
      exact polyWalk_mem hM φ i₀.val k

@[expose] def verts {m : ℕ} (p : GPath Γ m) : Set V := {v | ∃ i, i ≤ m ∧ p i = v}

theorem mem_verts {m : ℕ} {p : GPath Γ m} {i : ℕ} (hi : i ≤ m) : p i ∈ p.verts := ⟨i, hi, rfl⟩

theorem range_cycSeq {m : ℕ} (hm : 1 ≤ m) {p q : GPath Γ m} (h0 : p 0 = q 0) (hmm : p m = q m) :
    Set.range (cycSeq p q) = p.verts ∪ q.verts := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    have hlt := Nat.mod_lt i (show 0 < 2 * m by omega)
    by_cases h : i % (2 * m) ≤ m
    · left
      exact ⟨i % (2 * m), h, by simp [cycSeq, h]⟩
    · right
      exact ⟨2 * m - i % (2 * m), by omega, by simp [cycSeq, h]⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact ⟨i, cycSeq_of_le p q hm hi⟩
    · refine ⟨2 * m - j, ?_⟩
      rw [cycSeq_of_ge p q hm h0 hmm (by omega) (by omega)]
      congr 1
      omega

theorem range_cycSeq_comm {m : ℕ} (hm : 1 ≤ m) {p q : GPath Γ m} (h0 : p 0 = q 0)
    (hmm : p m = q m) : Set.range (cycSeq p q) = Set.range (cycSeq q p) := by
  rw [range_cycSeq hm h0 hmm, range_cycSeq hm h0.symm hmm.symm, Set.union_comm]

variable {c : V → Bool}

theorem cycSeq_adj_start (hΓ : Γ.Connected) (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) {m : ℕ}
    (hU : UniqueGeod Γ m) (hm : 2 ≤ m) {p q : GPath Γ m} (hp : p.IsGeodesic) (hq : q.IsGeodesic)
    (h0 : p 0 = q 0) (hmm : p m = q m) (hne : p ≠ q) {w : V} (hw : w ∈ Set.range (cycSeq p q))
    (hadj : Γ.Adj (p 0) w) : w = p 1 ∨ w = q 1 := by
  have hm' : 1 ≤ m := by omega
  obtain ⟨h1, h2⟩ := geod_first_last_ne hΓ hU hm' hp hq h0 hmm hne
  have hz := cycSeq_adj p q hm' h0 hmm
  have hnb := cycSeq_nb p q hm (noBack_of_dist_eq hΓ p hp) (noBack_of_dist_eq hΓ q hq) h0 hmm h1 h2
  have hper := cycSeq_per' p q
  obtain ⟨-, hadjonly⟩ := periodic_distinct_adj hΓ hc hU (cycSeq p q) hz hnb hper
  obtain ⟨i, rfl⟩ := hw
  have hlt := Nat.mod_lt i (show 0 < 2 * m by omega)
  have hk : cycSeq p q i = cycSeq p q (i % (2 * m)) :=
    ((Function.Periodic.map_mod_nat (f := cycSeq p q) (fun x => cycSeq_per p q x)) i).symm
  rw [hk] at hadj ⊢
  have hz0 : cycSeq p q 0 = p 0 := cycSeq_of_le p q hm' (Nat.zero_le m)
  rcases Nat.eq_zero_or_pos (i % (2 * m)) with h | h
  · rw [h, hz0] at hadj
    exact absurd hadj (SimpleGraph.irrefl _)
  · rw [← hz0] at hadj
    rcases hadjonly 0 (i % (2 * m)) h hlt hadj with h3 | ⟨-, h3⟩
    · left
      rw [show i % (2 * m) = 1 by omega, cycSeq_of_le p q hm' hm']
    · right
      rw [h3, cycSeq_of_ge p q hm' h0 hmm (by omega) (by omega)]
      congr 1
      omega

end GPath

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] [Finite Y] {c : α.Completion Y} {m : ℕ}
  (F : Facts46 c m)

include F

omit [Finite Y] in
theorem Facts46.lemma_F414_1 {a b : c.Γ} (hab : c.graph.dist a b = m) (S : Set c.Γ) :
    (c.IsApartment m S ∧ a ∈ S ∧ b ∈ S) ↔
      ∃ p q : GPath c.graph m, p ∈ c.geods m a b ∧ q ∈ c.geods m a b ∧ p ≠ q ∧
        S = Set.range (GPath.cycSeq p q) := by
  have hm := F.hm
  constructor
  · rintro ⟨hS, ha, hb⟩
    obtain ⟨p, q, hp, hq, hp0, hq0, hpm, hqm, hne, hSeq⟩ :=
      GPath.exists_arcs_of_polygon (connected_graph c) hm hS ha hb hab
    exact ⟨p, q, ⟨hp0, hpm, hp⟩, ⟨hq0, hqm, hq⟩, hne, hSeq⟩
  · rintro ⟨p, q, ⟨hp0, hpm, hp⟩, ⟨hq0, hqm, hq⟩, hne, rfl⟩
    refine ⟨GPath.polygon_of_two_geods (c := CosetGeom.vtype) (connected_graph c)
      (fun _ _ h => CosetGeom.vtype_ne_of_adj h) F.uniqueGeod hm hp hq (hp0.trans hq0.symm)
      (hpm.trans hqm.symm) hne, ?_, ?_⟩
    · exact ⟨0, by rw [GPath.cycSeq_of_le p q (by omega) (Nat.zero_le m)]; exact hp0⟩
    · exact ⟨m, by rw [GPath.cycSeq_of_le p q (by omega) le_rfl]; exact hpm⟩

theorem Facts46.lemma_F414_2 (hs : c.IsSmall m) {a b : c.Γ} (hab : c.graph.dist a b = m)
    {y : c.Γ} (hy : c.graph.Adj a y) :
    ∃! t : GPath c.graph m, t ∈ c.geods m a b ∧ t 1 = y := by
  have hbij := F.allBij hs hab
  obtain ⟨t, ht, hty⟩ := hbij.2.2 (show y ∈ CosetGeom.nbrs a from hy)
  refine ⟨t, ⟨ht, hty⟩, ?_⟩
  rintro t' ⟨ht', hty'⟩
  exact hbij.2.1 ht' ht (hty'.trans hty.symm)

theorem Facts46.eq_of_verts_subset (hs : c.IsSmall m) {a b : c.Γ} (hab : c.graph.dist a b = m)
    {p q t : GPath c.graph m} (hp : p ∈ c.geods m a b) (hq : q ∈ c.geods m a b) (hpq : p ≠ q)
    (ht : t ∈ c.geods m a b) (hsub : ∀ i, i ≤ m → t i ∈ Set.range (GPath.cycSeq p q)) :
    t = p ∨ t = q := by
  have hm := F.hm
  have hadj : c.graph.Adj (p 0) (t 1) := by
    have := t.adj 0 (by omega)
    rwa [ht.1, ← hp.1] at this
  rcases GPath.cycSeq_adj_start (c := CosetGeom.vtype) (connected_graph c)
      (fun _ _ h => CosetGeom.vtype_ne_of_adj h) F.uniqueGeod hm hp.2.2 hq.2.2
      (hp.1.trans hq.1.symm) (hp.2.1.trans hq.2.1.symm) hpq (hsub 1 (by omega)) hadj with h | h
  · obtain ⟨u, -, hu⟩ := F.lemma_F414_2 hs hab (show c.graph.Adj a (t 1) by rw [← ht.1]; exact t.adj 0 (by omega))
    left
    exact (hu t ⟨ht, rfl⟩).trans (hu p ⟨hp, h.symm⟩).symm
  · obtain ⟨u, -, hu⟩ := F.lemma_F414_2 hs hab (show c.graph.Adj a (t 1) by rw [← ht.1]; exact t.adj 0 (by omega))
    right
    exact (hu t ⟨ht, rfl⟩).trans (hu q ⟨hq, h.symm⟩).symm

theorem Facts46.ncard_apartments (hs : c.IsSmall m) {a b : c.Γ} (hab : c.graph.dist a b = m) :
    {S : Set c.Γ | c.IsApartment m S ∧ a ∈ S ∧ b ∈ S}.ncard =
      (Nat.card (CosetGeom.nbrs a)).choose 2 := by
  have hm := F.hm
  have hbij := F.allBij hs hab
  have hcard : Nat.card ↥(c.geods m a b) = Nat.card ↥(CosetGeom.nbrs a) :=
    Nat.card_congr hbij.equiv
  rw [← hcard, ← Sym2.natCard_subtype_not_diag, ← Nat.card_coe_set_eq]
  symm
  apply Nat.card_congr
  let g : Sym2 ↥(c.geods m a b) → Set c.Γ :=
    Sym2.lift ⟨fun p q => Set.range (GPath.cycSeq p.1 q.1), fun p q =>
      GPath.range_cycSeq_comm (by omega) (p.2.1.trans q.2.1.symm)
        (p.2.2.1.trans q.2.2.1.symm)⟩
  have hg : ∀ p q : ↥(c.geods m a b), g s(p, q) = Set.range (GPath.cycSeq p.1 q.1) :=
    fun _ _ => rfl
  have hnd : ∀ p q : ↥(c.geods m a b), ¬ s(p, q).IsDiag ↔ p.1 ≠ q.1 := by
    intro p q
    rw [Sym2.mk_isDiag_iff]
    exact ⟨fun h h' => h (Subtype.ext h'), fun h h' => h (congrArg Subtype.val h')⟩
  have hmem : ∀ z : {z : Sym2 ↥(c.geods m a b) // ¬z.IsDiag},
      g z.1 ∈ {S : Set c.Γ | c.IsApartment m S ∧ a ∈ S ∧ b ∈ S} := by
    rintro ⟨z, hz⟩
    induction z using Sym2.ind with
    | _ p q =>
      rw [hg]
      exact (F.lemma_F414_1 hab _).mpr ⟨p.1, q.1, p.2, q.2, (hnd p q).mp hz, rfl⟩
  refine Equiv.ofBijective (fun z => ⟨g z.1, hmem z⟩) ⟨?_, ?_⟩
  · rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
    have h' : g z = g z' := congrArg Subtype.val h
    induction z using Sym2.ind with
    | _ p q =>
    induction z' using Sym2.ind with
    | _ p' q' =>
    rw [hg, hg] at h'
    have hpq := (hnd p q).mp hz
    have hpq' := (hnd p' q').mp hz'
    have key : ∀ t : ↥(c.geods m a b),
        (∀ i, i ≤ m → t.1 i ∈ Set.range (GPath.cycSeq p.1 q.1)) → t = p ∨ t = q := by
      intro t ht
      rcases F.eq_of_verts_subset hs hab p.2 q.2 hpq t.2 ht with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    have hS : ∀ i, i ≤ m → ∀ (t : ↥(c.geods m a b)), t = p' ∨ t = q' →
        t.1 i ∈ Set.range (GPath.cycSeq p.1 q.1) := by
      intro i hi t ht
      rw [h', GPath.range_cycSeq (by omega) (p'.2.1.trans q'.2.1.symm)
        (p'.2.2.1.trans q'.2.2.1.symm)]
      rcases ht with rfl | rfl
      · exact Or.inl (GPath.mem_verts hi)
      · exact Or.inr (GPath.mem_verts hi)
    have hp' := key p' (fun i hi => hS i hi p' (Or.inl rfl))
    have hq' := key q' (fun i hi => hS i hi q' (Or.inr rfl))
    apply Subtype.ext
    show s(p, q) = s(p', q')
    rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
    · exact absurd rfl hpq'
    · rfl
    · exact Sym2.eq_swap
    · exact absurd rfl hpq'
  · rintro ⟨S, hS⟩
    obtain ⟨p, q, hp, hq, hpq, rfl⟩ := (F.lemma_F414_1 hab S).mp hS
    refine ⟨⟨s(⟨p, hp⟩, ⟨q, hq⟩), (hnd ⟨p, hp⟩ ⟨q, hq⟩).mpr hpq⟩, ?_⟩
    apply Subtype.ext
    exact hg ⟨p, hp⟩ ⟨q, hq⟩

end RankTwoAmalgam.Completion

namespace RankTwoAmalgam

@[expose] noncomputable def qv (α : RankTwoAmalgam.{u}) (b : Bool) : ℕ :=
  if b then α.qTwo else α.qOne

end RankTwoAmalgam

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] [Finite Y] {c : α.Completion Y}

omit [Finite Y] in
theorem card_nbrs_smul (g : c.G0) (v : c.Γ) :
    Nat.card (CosetGeom.nbrs (g • v)) = Nat.card (CosetGeom.nbrs v) := by
  have h : CosetGeom.nbrs (g • v) = (fun w => g • w) '' CosetGeom.nbrs v := by
    ext w
    constructor
    · intro hw
      refine ⟨g⁻¹ • w, ?_, smul_inv_smul g w⟩
      show c.graph.Adj v (g⁻¹ • w)
      have := (CosetGeom.smul_adj g⁻¹).mpr hw
      rwa [inv_smul_smul] at this
    · rintro ⟨w', hw', rfl⟩
      exact (CosetGeom.smul_adj g).mpr hw'
  rw [h]
  exact Nat.card_image_of_injective (MulAction.injective g) _

theorem card_nbrs (hc : c.IsFaithful) (u : c.Γ) :
    Nat.card (CosetGeom.nbrs u) = α.qv (CosetGeom.vtype u) + 1 := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  have hcard : Nat.card (CosetGeom.nbrs u) =
      Nat.card (CosetGeom.nbrs (c.baseVert (CosetGeom.vtype u))) :=
    calc Nat.card (CosetGeom.nbrs u)
        = Nat.card (CosetGeom.nbrs (g • c.baseVert (CosetGeom.vtype u))) := by rw [hg]
      _ = _ := card_nbrs_smul g _
  have hf1 : Finite α.G1 := Finite.of_injective c.φ1 hc.1
  have hf2 : Finite α.G2 := Finite.of_injective c.φ2 hc.2.2
  have i1 : α.α1.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have i2 : α.α2.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  generalize CosetGeom.vtype u = b at hcard ⊢
  cases b
  · have : Nat.card (CosetGeom.nbrs c.xv) = α.α1.range.index := nbrs_xv_card hc
    rw [hcard]
    unfold RankTwoAmalgam.qv RankTwoAmalgam.qOne
    simp only [Bool.false_eq_true, ↓reduceIte]
    show Nat.card (CosetGeom.nbrs c.xv) = _
    rw [this]
    omega
  · have : Nat.card (CosetGeom.nbrs c.lv) = α.α2.range.index := nbrs_lv_card hc
    rw [hcard]
    unfold RankTwoAmalgam.qv RankTwoAmalgam.qTwo
    simp only [↓reduceIte]
    show Nat.card (CosetGeom.nbrs c.lv) = _
    rw [this]
    omega

end RankTwoAmalgam.Completion

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] [Finite Y] {c : α.Completion Y} {m : ℕ}

@[expose] def IsSimplex (c : α.Completion Y) (s : Set c.Γ) : Prop :=
  (∃ a, s = {a}) ∨ ∃ a b, c.graph.Adj a b ∧ s = {a, b}

omit [Finite Y] in
theorem IsSimplex.finite {s : Set c.Γ} (h : IsSimplex c s) : s.Finite := by
  rcases h with ⟨a, rfl⟩ | ⟨a, b, -, rfl⟩
  · exact Set.finite_singleton a
  · exact Set.toFinite _

omit [Finite Y] in
theorem IsSimplex.nonempty {s : Set c.Γ} (h : IsSimplex c s) : s.Nonempty := by
  rcases h with ⟨a, rfl⟩ | ⟨a, b, -, rfl⟩
  · exact Set.singleton_nonempty a
  · exact Set.insert_nonempty _ _

omit [Finite Y] in
theorem IsSimplex.around {s : Set c.Γ} (h : IsSimplex c s) {a : c.Γ} (ha : a ∈ s) :
    (∀ x ∈ s, x = a ∨ c.graph.Adj a x) ∧ (∀ x ∈ s, ∀ y ∈ s, x ≠ a → y ≠ a → x = y) := by
  rcases h with ⟨a0, rfl⟩ | ⟨a0, b0, hadj, rfl⟩
  · rw [Set.mem_singleton_iff] at ha
    subst ha
    refine ⟨fun x hx => Or.inl (Set.mem_singleton_iff.mp hx), fun x hx y hy hxa => ?_⟩
    exact absurd (Set.mem_singleton_iff.mp hx) hxa
  · rcases ha with rfl | ha
    · refine ⟨?_, ?_⟩
      · rintro x (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr hadj
      · rintro x (rfl | rfl) y (rfl | rfl) hx hy
        · exact absurd rfl hx
        · exact absurd rfl hx
        · exact absurd rfl hy
        · rfl
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      refine ⟨?_, ?_⟩
      · rintro x (rfl | rfl)
        · exact Or.inr hadj.symm
        · exact Or.inl rfl
      · rintro x (rfl | rfl) y (rfl | rfl) hx hy
        · rfl
        · exact absurd rfl hy
        · exact absurd rfl hx
        · exact absurd rfl hx

variable (F : Facts46 c m)

include F

theorem Facts46.exists_ne_geod (hs : c.IsSmall m) {a b : c.Γ} (hab : c.graph.dist a b = m)
    (P : GPath c.graph m) : ∃ Q ∈ c.geods m a b, Q ≠ P := by
  obtain ⟨y₁, y₂, h1, h2, hne⟩ := F.exists_two_nbrs a
  have hbij := F.allBij hs hab
  by_cases h : y₁ = P 1
  · obtain ⟨Q, hQ, hQ1⟩ := hbij.2.2 (show y₂ ∈ CosetGeom.nbrs a from h2)
    refine ⟨Q, hQ, fun hQP => hne ?_⟩
    have : Q 1 = P 1 := by rw [hQP]
    rw [h]
    exact this.symm.trans hQ1
  · obtain ⟨Q, hQ, hQ1⟩ := hbij.2.2 (show y₁ ∈ CosetGeom.nbrs a from h1)
    refine ⟨Q, hQ, fun hQP => h ?_⟩
    rw [← hQ1, hQP]

theorem Facts46.exists_cover (hs : c.IsSmall m) {s t : Set c.Γ} (hs' : IsSimplex c s)
    (ht' : IsSimplex c t) :
    ∃ (a b : c.Γ) (P Q : GPath c.graph m), c.graph.dist a b = m ∧ P ∈ c.geods m a b ∧
      Q ∈ c.geods m a b ∧ P ≠ Q ∧ s ∪ t ⊆ P.verts ∪ Q.verts := by
  have hm := F.hm
  have hconn := connected_graph c
  have hbip : ∀ x y : c.Γ, c.graph.Adj x y → CosetGeom.vtype x ≠ CosetGeom.vtype y :=
    fun _ _ h => CosetGeom.vtype_ne_of_adj h
  obtain ⟨a, ha, u, hu, hmax⟩ : ∃ a ∈ s, ∃ u ∈ t, ∀ a' ∈ s, ∀ u' ∈ t,
      c.graph.dist a' u' ≤ c.graph.dist a u := by
    obtain ⟨⟨a, u⟩, ⟨ha, hu⟩, hmax⟩ := Set.exists_max_image (s ×ˢ t)
      (fun x => c.graph.dist x.1 x.2) (hs'.finite.prod ht'.finite)
      (hs'.nonempty.prod ht'.nonempty)
    exact ⟨a, ha, u, hu, fun a' ha' u' hu' => hmax (a', u') ⟨ha', hu'⟩⟩
  obtain ⟨hs1, hs2⟩ := hs'.around ha
  obtain ⟨ht1, ht2⟩ := ht'.around hu
  obtain ⟨n, hn⟩ : ∃ n, c.graph.dist a u = n := ⟨_, rfl⟩
  have hnm : n ≤ m := hn ▸ F.diam_le hs a u
  have hn' : c.graph.dist u a = n := by rw [SimpleGraph.dist_comm, hn]
  have hx : ∀ x ∈ s, x ≠ a → ∃ n', n = n' + 1 ∧ c.graph.dist u x = n' := by
    intro x hxs hxa
    have hadj : c.graph.Adj a x := (hs1 x hxs).resolve_left hxa
    have hle := hmax x hxs u hu
    rcases GPath.dist_adj_succ_or hconn hbip u hadj with h | h
    · exfalso
      have e : c.graph.dist x u = c.graph.dist u x := SimpleGraph.dist_comm
      rw [e, h, hn', hn] at hle
      omega
    · exact ⟨c.graph.dist u x, by omega, rfl⟩
  have hy : ∀ y ∈ t, y ≠ u → ∃ n', n = n' + 1 ∧ c.graph.dist a y = n' := by
    intro y hyt hyu
    have hadj : c.graph.Adj u y := (ht1 y hyt).resolve_left hyu
    have hle := hmax a ha y hyt
    rcases GPath.dist_adj_succ_or hconn hbip a hadj with h | h
    · exfalso
      rw [h, hn] at hle
      omega
    · exact ⟨c.graph.dist a y, by omega, rfl⟩
  obtain ⟨r, hr0, hrn, hrnb⟩ := GPath.exists_geodesic' hconn a u hn
  obtain ⟨p, hp, hpr⟩ := GPath.exists_extend_to F.hval hnm
    (show r ∈ GPath.nbPaths c.graph a n from ⟨hr0, hrnb⟩)
  have hpi : ∀ i, i ≤ n → p i = r i := fun i hi => by
    have := congrArg (fun s : GPath c.graph n => s i) hpr
    simpa [GPath.take_apply_of_le _ _ _ hi] using this
  have hpa : p 0 = a := hp.1
  have hpu : p n = u := by rw [hpi n le_rfl, hrn]
  have hdm := F.dist_m a p hp
  rcases Nat.lt_or_ge n m with hlt | hge
  ·
    have hX : ∀ x ∈ s, x ≠ a → x = p 1 := by
      intro x hxs hxa
      obtain ⟨n', hn1, hd⟩ := hx x hxs hxa
      subst hn1
      obtain ⟨g, hg0, hgn, -⟩ := GPath.exists_geodesic' hconn u x hd
      have hadj' : c.graph.Adj (g n') a := by
        rw [hgn]; exact ((hs1 x hxs).resolve_left hxa).symm
      let q := g.snoc a hadj'
      have hq0 : q 0 = u := by rw [GPath.snoc_of_le _ _ _ (Nat.zero_le _)]; exact hg0
      have hqn : q (n' + 1) = a := GPath.snoc_last _ _ _
      let P := (p.take (n' + 1) hnm).rev
      have hP0 : P 0 = u := by
        show (p.take (n' + 1) hnm).rev 0 = u
        rw [GPath.rev_apply _ (Nat.zero_le _), Nat.sub_zero,
          GPath.take_apply_of_le _ _ _ le_rfl]
        exact hpu
      have hPn : P (n' + 1) = a := by
        show (p.take (n' + 1) hnm).rev (n' + 1) = a
        rw [GPath.rev_apply _ le_rfl, Nat.sub_self, GPath.take_apply_of_le _ _ _ (Nat.zero_le _)]
        exact hpa
      have hPmem : P ∈ GPath.nbPaths c.graph u (n' + 1) :=
        ⟨hP0, (hp.2.take _ hnm).rev⟩
      have hqgeod : q.IsGeodesic := by
        show c.graph.dist (q 0) (q (n' + 1)) = n' + 1
        rw [hq0, hqn]; exact hn'
      have heq := ((F.uniq (n' + 1) hlt u P hPmem).2 q hq0 (hqn.trans hPn.symm) hqgeod)
      have h1 : q n' = x := by
        show g.snoc a hadj' n' = x
        rw [GPath.snoc_of_le _ _ _ le_rfl]; exact hgn
      have h2 : P n' = p 1 := by
        show (p.take (n' + 1) hnm).rev n' = p 1
        rw [GPath.rev_apply _ (by omega), show n' + 1 - n' = 1 by omega,
          GPath.take_apply_of_le _ _ _ (by omega)]
      rw [← h1, heq, h2]
    have hY : ∀ y ∈ t, y ≠ u → y = p (n - 1) := by
      intro y hyt hyu
      obtain ⟨n', hn1, hd⟩ := hy y hyt hyu
      subst hn1
      obtain ⟨g, hg0, hgn, -⟩ := GPath.exists_geodesic' hconn a y hd
      have hadj' : c.graph.Adj (g n') u := by
        rw [hgn]; exact ((ht1 y hyt).resolve_left hyu).symm
      let q := g.snoc u hadj'
      have hq0 : q 0 = a := by rw [GPath.snoc_of_le _ _ _ (Nat.zero_le _)]; exact hg0
      have hqn : q (n' + 1) = u := GPath.snoc_last _ _ _
      let P := p.take (n' + 1) hnm
      have hP0 : P 0 = a := by
        show p.take (n' + 1) hnm 0 = a
        rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le _)]; exact hpa
      have hPn : P (n' + 1) = u := by
        show p.take (n' + 1) hnm (n' + 1) = u
        rw [GPath.take_apply_of_le _ _ _ le_rfl]; exact hpu
      have hPmem : P ∈ GPath.nbPaths c.graph a (n' + 1) := ⟨hP0, hp.2.take _ hnm⟩
      have hqgeod : q.IsGeodesic := by
        show c.graph.dist (q 0) (q (n' + 1)) = n' + 1
        rw [hq0, hqn]; exact hn
      have heq := ((F.uniq (n' + 1) hlt a P hPmem).2 q hq0 (hqn.trans hPn.symm) hqgeod)
      have h1 : q n' = y := by
        show g.snoc u hadj' n' = y
        rw [GPath.snoc_of_le _ _ _ le_rfl]; exact hgn
      have h2 : P n' = p n' := by
        show p.take (n' + 1) hnm n' = p n'
        rw [GPath.take_apply_of_le _ _ _ (by omega)]
      rw [← h1, heq, h2]
      rfl
    obtain ⟨Q, hQ, hQne⟩ := F.exists_ne_geod hs hdm p
    refine ⟨a, p m, p, Q, hdm, F.mem_geods hp, hQ, hQne.symm, ?_⟩
    rintro v (hv | hv)
    · left
      rcases hs1 v hv with rfl | hadj
      · exact ⟨0, by omega, hpa⟩
      · exact ⟨1, by omega, (hX v hv hadj.ne.symm).symm⟩
    · left
      by_cases hvu : v = u
      · exact ⟨n, hnm, by rw [hpu, hvu]⟩
      · exact ⟨n - 1, by omega, (hY v hv hvu).symm⟩
  · have hnm' : n = m := le_antisymm hnm hge
    have hpu' : p m = u := by rw [hnm'] at hpu; exact hpu
    have hab : c.graph.dist a u = m := by rw [hn, hnm']
    have hpg : p ∈ c.geods m a u := by
      have := F.mem_geods hp
      rwa [hpu'] at this
    have hbij := F.allBij hs hab
    obtain ⟨P₀, hP₀, hP₀x⟩ : ∃ P₀ ∈ c.geods m a u, ∀ x ∈ s, x ≠ a → P₀ 1 = x := by
      by_cases hX : ∃ x ∈ s, x ≠ a
      · obtain ⟨x, hxs, hxa⟩ := hX
        obtain ⟨P₀, hP₀, hP₀1⟩ :=
          hbij.2.2 (show x ∈ CosetGeom.nbrs a from (hs1 x hxs).resolve_left hxa)
        refine ⟨P₀, hP₀, fun x' hx' hx'a => ?_⟩
        have hxx' := hs2 x hxs x' hx' hxa hx'a
        rw [← hxx']
        exact hP₀1
      · push Not at hX
        exact ⟨p, hpg, fun x hxs hxa => absurd (hX x hxs) hxa⟩
    have hP₀0 : P₀ 0 = a := hP₀.1
    have hP₀m : P₀ m = u := hP₀.2.1
    have hsub_s : ∀ x ∈ s, x ∈ P₀.verts := by
      intro x hxs
      rcases hs1 x hxs with rfl | hadj
      · exact ⟨0, by omega, hP₀0⟩
      · exact ⟨1, by omega, hP₀x x hxs hadj.ne.symm⟩
    by_cases hY : ∃ y ∈ t, y ≠ u ∧ y ≠ P₀ (m - 1)
    · obtain ⟨y, hyt, hyu, hyP⟩ := hY
      have hadjy : c.graph.Adj u y := (ht1 y hyt).resolve_left hyu
      have hba : c.graph.dist u a = m := by rw [SimpleGraph.dist_comm]; exact hab
      obtain ⟨Q', ⟨hQ'mem, hQ'1⟩, -⟩ := F.lemma_F414_2 hs hba hadjy
      let Q := Q'.rev
      have hQ0 : Q 0 = a := by
        show Q'.rev 0 = a
        rw [GPath.rev_apply _ (Nat.zero_le _), Nat.sub_zero]
        exact hQ'mem.2.1
      have hQm : Q m = u := by
        show Q'.rev m = u
        rw [GPath.rev_apply _ le_rfl, Nat.sub_self]
        exact hQ'mem.1
      have hQy : Q (m - 1) = y := by
        show Q'.rev (m - 1) = y
        rw [GPath.rev_apply _ (by omega), show m - (m - 1) = 1 by omega]
        exact hQ'1
      have hQmem : Q ∈ c.geods m a u := ⟨hQ0, hQm, hQ'mem.2.2.rev⟩
      have hne : P₀ ≠ Q := by
        intro h
        apply hyP
        rw [h]
        exact hQy.symm
      refine ⟨a, u, P₀, Q, hab, hP₀, hQmem, hne, ?_⟩
      rintro v (hv | hv)
      · exact Or.inl (hsub_s v hv)
      · by_cases hvu : v = u
        · exact Or.inl ⟨m, le_rfl, by rw [hP₀m, hvu]⟩
        · have hvy := ht2 v hv y hyt hvu hyu
          exact Or.inr ⟨m - 1, by omega, by rw [hQy, hvy]⟩
    · push Not at hY
      obtain ⟨Q, hQ, hQne⟩ := F.exists_ne_geod hs hab P₀
      refine ⟨a, u, P₀, Q, hab, hP₀, hQ, hQne.symm, ?_⟩
      rintro v (hv | hv)
      · exact Or.inl (hsub_s v hv)
      · by_cases hvu : v = u
        · exact Or.inl ⟨m, le_rfl, by rw [hP₀m, hvu]⟩
        · exact Or.inl ⟨m - 1, by omega, (hY v hv hvu).symm⟩

theorem Facts46.lemma_F414_4 (hs : c.IsSmall m) {s t : Set c.Γ} (hs' : IsSimplex c s)
    (ht' : IsSimplex c t) : ∃ S : Set c.Γ, c.IsApartment m S ∧ s ⊆ S ∧ t ⊆ S := by
  obtain ⟨a, b, P, Q, hab, hP, hQ, hPQ, hsub⟩ := F.exists_cover hs hs' ht'
  have hm := F.hm
  refine ⟨Set.range (GPath.cycSeq P Q), ?_, ?_, ?_⟩
  · refine ((F.lemma_F414_1 hab _).mpr ⟨P, Q, hP, hQ, hPQ, rfl⟩).1
  · intro v hv
    rw [GPath.range_cycSeq (by omega) (hP.1.trans hQ.1.symm) (hP.2.1.trans hQ.2.1.symm)]
    exact hsub (Or.inl hv)
  · intro v hv
    rw [GPath.range_cycSeq (by omega) (hP.1.trans hQ.1.symm) (hP.2.1.trans hQ.2.1.symm)]
    exact hsub (Or.inr hv)

theorem Facts46.lemma_F414_3 (hs : c.IsSmall m) {a b : c.Γ} (hab : c.graph.dist a b = m) :
    {S : Set c.Γ | c.IsApartment m S ∧ a ∈ S ∧ b ∈ S}.ncard =
      (α.qv (CosetGeom.vtype a) + 1).choose 2 := by
  rw [F.ncard_apartments hs hab, card_nbrs F.faithful a]

omit [Finite Y] in
theorem Facts46.no_polygon {n : ℕ} (hn2 : 2 ≤ n) (hn : n < m) (S : Set c.Γ) :
    ¬ IsPolygon c.graph S (2 * n) := by
  rintro ⟨φ⟩
  have hM : 0 < 2 * n := by omega
  have hM3 : 3 ≤ 2 * n := by omega
  have := GPath.two_mul_le_of_periodic (c := CosetGeom.vtype) (connected_graph c)
    (fun _ _ h => CosetGeom.vtype_ne_of_adj h) F.uniqueGeod (GPath.polyWalk hM φ 0)
    (GPath.polyWalk_adj hM φ 0 hM3) (GPath.polyWalk_nb hM φ 0 hM3) hM (GPath.polyWalk_per hM φ 0)
  omega

end RankTwoAmalgam.Completion

end CFSG.Quasithin
