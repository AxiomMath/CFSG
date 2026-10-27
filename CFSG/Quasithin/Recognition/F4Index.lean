module

public import CFSG.Quasithin.Recognition.F4Apart

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w'

namespace RankTwoAmalgam

@[expose] noncomputable def pathNum (α : RankTwoAmalgam.{u}) (b : Bool) : ℕ → ℕ
  | 0 => 1
  | n + 1 => pathNum α b n *
      (if n = 0 then α.qv b + 1 else α.qv (if n % 2 = 0 then b else !b))

theorem pathNum_succ_odd (α : RankTwoAmalgam.{u}) (b : Bool) (j : ℕ) :
    α.pathNum b (2 * j + 2) = α.pathNum b (2 * j + 1) * α.qv (!b) := by
  have e1 : ¬ (2 * j + 1 = 0) := by omega
  have e2 : ¬ ((2 * j + 1) % 2 = 0) := by omega
  show α.pathNum b (2 * j + 1 + 1) = _
  simp only [pathNum, e1, e2, ite_false]

theorem pathNum_succ_even (α : RankTwoAmalgam.{u}) (b : Bool) (j : ℕ) :
    α.pathNum b (2 * j + 3) = α.pathNum b (2 * j + 2) * α.qv b := by
  have e1 : ¬ (2 * j + 2 = 0) := by omega
  have e2 : (2 * j + 2) % 2 = 0 := by omega
  show α.pathNum b (2 * j + 2 + 1) = _
  simp only [pathNum, e1, e2, ite_false, ite_true]

theorem pathNum_odd (α : RankTwoAmalgam.{u}) (b : Bool) (j : ℕ) :
    α.pathNum b (2 * j + 1) = (α.qv b + 1) * (α.qv b * α.qv (!b)) ^ j := by
  induction j with
  | zero => simp [pathNum]
  | succ j ih =>
    have h1 : α.pathNum b (2 * (j + 1) + 1) = α.pathNum b (2 * j + 2) * α.qv b := by
      have := pathNum_succ_even α b j
      rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring]
      exact this
    rw [h1, pathNum_succ_odd, ih]
    ring

theorem pathNum_even (α : RankTwoAmalgam.{u}) (b : Bool) (j : ℕ) :
    α.pathNum b (2 * j + 2) = (α.qv b + 1) * (α.qv b * α.qv (!b)) ^ j * α.qv (!b) := by
  rw [pathNum_succ_odd, pathNum_odd]

end RankTwoAmalgam

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] [Finite Y] {c : α.Completion Y}

omit [Finite Y] in
theorem vtype_path_iff {n : ℕ} (p : GPath c.graph n) {k : ℕ} (hk : k ≤ n) :
    (CosetGeom.vtype (p k) = CosetGeom.vtype (p 0) ↔ k % 2 = 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hne := CosetGeom.vtype_ne_of_adj (p.adj k (by omega))
    have ih' := ih (by omega)
    generalize CosetGeom.vtype (p 0) = b at ih' ⊢
    generalize CosetGeom.vtype (p k) = x at ih' hne
    generalize CosetGeom.vtype (p (k + 1)) = y at hne ⊢
    cases b <;> cases x <;> cases y <;> simp_all <;> omega

@[expose] def extSet {n : ℕ} (q : GPath c.graph n) : Set c.Γ :=
  {w | c.graph.Adj (q n) w ∧ (1 ≤ n → w ≠ q (n - 1))}

theorem card_extSet (hc : c.IsFaithful) {n : ℕ} (q : GPath c.graph n) :
    Nat.card ↥(extSet q) =
      if n = 0 then α.qv (CosetGeom.vtype (q 0)) + 1 else α.qv (CosetGeom.vtype (q n)) := by
  by_cases hn : n = 0
  · subst hn
    have : extSet q = CosetGeom.nbrs (q 0) := by
      ext w
      simp only [extSet, Set.mem_ofPred_eq]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, fun h1 => absurd h1 (by omega)⟩
    rw [this, card_nbrs hc]
    simp
  · have hn1 : 1 ≤ n := by omega
    have hadj : c.graph.Adj (q n) (q (n - 1)) := by
      have := (q.adj (n - 1) (by omega)).symm
      rwa [show n - 1 + 1 = n by omega] at this
    have : extSet q = CosetGeom.nbrs (q n) \ {q (n - 1)} := by
      ext w
      simp only [extSet, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · exact fun h => ⟨h.1, h.2 hn1⟩
      · exact fun h => ⟨h.1, fun _ => h.2⟩
    rw [this]
    simp only [hn, ↓reduceIte]
    have h1 : (CosetGeom.nbrs (q n) \ {q (n - 1)}).ncard = (CosetGeom.nbrs (q n)).ncard - 1 :=
      Set.ncard_sdiff_singleton_of_mem hadj
    have h2 : Nat.card ↥(CosetGeom.nbrs (q n)) = α.qv (CosetGeom.vtype (q n)) + 1 :=
      card_nbrs hc _
    rw [Nat.card_coe_set_eq, h1, ← Nat.card_coe_set_eq, h2]
    simp

omit [Finite Y] in
noncomputable def fiberEquiv (a : c.Γ) {n : ℕ} (q : ↥(GPath.nbPaths c.graph a n)) :
    {p : ↥(GPath.nbPaths c.graph a (n + 1)) // p.1.take n (Nat.le_succ n) = q.1} ≃
      ↥(extSet q.1) where
  toFun p := ⟨p.1.1 (n + 1), by
    have e : p.1.1 n = q.1 n := by
      have := congrArg (fun r : GPath c.graph n => r n) p.2
      simpa [GPath.take_apply_of_le _ _ _ le_rfl] using this
    refine ⟨?_, fun hn => ?_⟩
    · have h := p.1.1.adj n (Nat.lt_succ_self n)
      rwa [e] at h
    · intro h
      have hb := p.1.2.2 (n - 1) (by omega)
      apply hb
      have e' : p.1.1 (n - 1) = q.1 (n - 1) := by
        have := congrArg (fun r : GPath c.graph n => r (n - 1)) p.2
        simpa [GPath.take_apply_of_le _ _ _ (show n - 1 ≤ n by omega)] using this
      rw [show n - 1 + 2 = n + 1 by omega, e']
      exact h.symm⟩
  invFun w := ⟨⟨q.1.snoc w.1 w.2.1,
    ⟨by rw [GPath.snoc_of_le _ _ _ (Nat.zero_le n)]; exact q.2.1,
      GPath.noBack_snoc q.2.2 w.2.1 w.2.2⟩⟩, GPath.snoc_take_self q.1 w.1 w.2.1⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply GPath.ext'
    intro i hi
    dsimp only
    by_cases h : i ≤ n
    · rw [GPath.snoc_of_le _ _ _ h]
      have := congrArg (fun r : GPath c.graph n => r i) p.2
      simpa [GPath.take_apply_of_le _ _ _ h] using this.symm
    · have : i = n + 1 := by omega
      subst this
      exact GPath.snoc_last _ _ _
  right_inv w := by
    apply Subtype.ext
    exact GPath.snoc_last q.1 w.1 w.2.1

theorem finite_gpath (n : ℕ) : Finite (GPath c.graph n) :=
  Finite.of_injective (fun p : GPath c.graph n => fun i : Fin (n + 1) => p i)
    (fun p q h => GPath.ext' fun i hi => congrFun h ⟨i, by omega⟩)

omit [Finite Y] in
theorem vtype_path_end {a : c.Γ} {n : ℕ} (q : ↥(GPath.nbPaths c.graph a n)) :
    CosetGeom.vtype (q.1 n) = if n % 2 = 0 then CosetGeom.vtype a else !CosetGeom.vtype a := by
  have h := vtype_path_iff q.1 (le_refl n)
  have h0 : CosetGeom.vtype (q.1 0) = CosetGeom.vtype a := by rw [q.2.1]
  rw [h0] at h
  by_cases hn : n % 2 = 0
  · simp only [hn, ↓reduceIte]
    exact h.mpr hn
  · simp only [hn, ↓reduceIte]
    have := mt h.mp hn
    generalize CosetGeom.vtype (q.1 n) = x at this ⊢
    generalize CosetGeom.vtype a = b at this ⊢
    cases b <;> cases x <;> simp_all

theorem card_nbPaths_succ (hc : c.IsFaithful) (a : c.Γ) (n : ℕ) :
    Nat.card ↥(GPath.nbPaths c.graph a (n + 1)) = Nat.card ↥(GPath.nbPaths c.graph a n) *
      (if n = 0 then α.qv (CosetGeom.vtype a) + 1
        else α.qv (if n % 2 = 0 then CosetGeom.vtype a else !CosetGeom.vtype a)) := by
  have := finite_gpath (c := c) n
  have := finite_gpath (c := c) (n + 1)
  have hfin : Finite ↥(GPath.nbPaths c.graph a n) := inferInstance
  have := Fintype.ofFinite ↥(GPath.nbPaths c.graph a n)
  let f : ↥(GPath.nbPaths c.graph a (n + 1)) → ↥(GPath.nbPaths c.graph a n) := fun p =>
    ⟨p.1.take n (Nat.le_succ n),
      ⟨by rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le n)]; exact p.2.1, p.2.2.take n _⟩⟩
  have hfib : ∀ q : ↥(GPath.nbPaths c.graph a n),
      Nat.card {p // f p = q} = if n = 0 then α.qv (CosetGeom.vtype a) + 1
        else α.qv (if n % 2 = 0 then CosetGeom.vtype a else !CosetGeom.vtype a) := by
    intro q
    have e1 : {p // f p = q} ≃ {p : ↥(GPath.nbPaths c.graph a (n + 1)) //
        p.1.take n (Nat.le_succ n) = q.1} :=
      Equiv.subtypeEquivRight fun p => by
        simp only [f, Subtype.ext_iff]
    rw [Nat.card_congr (e1.trans (fiberEquiv a q)), card_extSet hc]
    have h0 : CosetGeom.vtype (q.1 0) = CosetGeom.vtype a := by rw [q.2.1]
    by_cases hn : n = 0
    · subst hn
      simp [h0]
    · simp only [hn, ↓reduceIte, vtype_path_end q]
  have hsum : Nat.card ↥(GPath.nbPaths c.graph a (n + 1)) =
      ∑ q : ↥(GPath.nbPaths c.graph a n), Nat.card {p // f p = q} := by
    have : ∀ q : ↥(GPath.nbPaths c.graph a n), Finite {p // f p = q} := fun q => inferInstance
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
  rw [hsum]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Fintype.card_eq_nat_card]

theorem card_nbPaths (hc : c.IsFaithful) (a : c.Γ) (n : ℕ) :
    Nat.card ↥(GPath.nbPaths c.graph a n) = α.pathNum (CosetGeom.vtype a) n := by
  induction n with
  | zero =>
    have : GPath.nbPaths c.graph a 0 = {GPath.triv a} := by
      ext p
      simp only [GPath.nbPaths, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h0, -⟩
        exact GPath.ext' fun i hi => by
          have : i = 0 := by omega
          subst this
          exact h0
      · rintro rfl
        exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
    rw [this]
    simp [pathNum]
  | succ n ih =>
    rw [card_nbPaths_succ hc, ih]
    rfl

theorem relIndex_stabPath (hc : c.IsFaithful) {a : c.Γ} {n : ℕ} (hT : c.PathTrans a n)
    {p : GPath c.graph n} (hp : p ∈ GPath.nbPaths c.graph a n) :
    (p.stabPath : Subgroup c.G0).relIndex (stv c a) = α.pathNum (CosetGeom.vtype a) n := by
  rw [← card_nbPaths hc a n]
  have := finite_gpath (c := c) n
  let p0 : PathSet c.graph a := ⟨n, p, hp.1⟩
  have hstab : MulAction.stabilizer (stv c a) p0 =
      (p.stabPath : Subgroup c.G0).subgroupOf (stv c a) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, GPath.mem_stabPath_iff]
    constructor
    · intro h i hi
      have := congrArg (fun x : PathSet c.graph a => x.2.1 i) h
      simpa [PathSet.smul_def] using this
    · intro h
      refine PathSet.ext rfl fun i => ?_
      show ((g : c.G0) • p) i = p i
      rw [GPath.smul_apply]
      by_cases hi : i ≤ n
      · exact h i hi
      · rw [p.tail i (by omega)]
        exact h n le_rfl
  rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer]
  let ι : ↥(GPath.nbPaths c.graph a n) → PathSet c.graph a := fun q => ⟨n, q.1, q.2.1⟩
  have hι : Function.Injective ι := fun q q' h => by
    have h1 : q.1 = q'.1 := by
      have := Sigma.mk.inj h
      exact eq_of_heq (by simpa using this.2)
    exact Subtype.ext h1
  have horb : MulAction.orbit (stv c a) p0 = Set.range ι := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨⟨(g : c.G0) • p, ⟨?_, GPath.smul_noBack hp.2⟩⟩, rfl⟩
      rw [GPath.smul_apply, hp.1]
      exact MulAction.mem_stabilizer_iff.mp g.2
    · rintro ⟨q, rfl⟩
      obtain ⟨g, hg1, hg2⟩ := hT p q.1 hp q.2
      refine ⟨⟨g, MulAction.mem_stabilizer_iff.mpr hg1⟩, ?_⟩
      exact PathSet.ext rfl fun i => by
        show (g • p) i = q.1 i
        rw [hg2]
  rw [horb, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hι]

end RankTwoAmalgam.Completion

end CFSG.Quasithin
