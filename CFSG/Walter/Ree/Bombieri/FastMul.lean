module

public import CFSG.Walter.Ree.Bombieri.PExpr

public section

namespace CFSG.Walter.Ree.Bombieri

namespace F3P

@[expose] def idx (m : ℕ) (a : F3P) : ℕ := a.p + a.n <<< m

structure Tab where
  f : F3P
  m : ℕ
  q1 : ℕ
  expT : Array F3P
  logT : Array ℕ

@[expose] def mkTab (f : F3P) (m : ℕ) (g : F3P) : Tab :=
  let q1 := 3 ^ m - 1
  let expT := Id.run do
    let mut e : Array F3P := Array.mkEmpty q1
    let mut x := one
    for _ in [0:q1] do
      e := e.push x
      x := mulMod f m x g
    return e
  let logT := Id.run do
    let mut l : Array ℕ := Array.replicate (4 ^ m) 0
    for i in [0:q1] do
      l := l.set! (idx m (expT.getD i zero)) i
    return l
  ⟨f, m, q1, expT, logT⟩

@[expose] def mulT (T : Tab) (a b : F3P) : F3P :=
  let la := T.logT.getD (idx T.m a) 0
  let lb := T.logT.getD (idx T.m b) 0
  if la < T.q1 && lb < T.q1 && T.expT.getD la zero == a && T.expT.getD lb zero == b then
    T.expT.getD ((la + lb) % T.q1) zero
  else mulMod T.f T.m a b

@[expose] def tabCheck (T : Tab) : Bool :=
  T.expT.size == T.q1 && 2 ≤ T.q1 && T.expT.getD 0 zero == one &&
    (List.range T.q1).all (fun i => (T.expT.getD i zero).p &&& (T.expT.getD i zero).n == 0) &&
    (List.range (T.q1 - 1)).all (fun i =>
      T.expT.getD (i + 1) zero == mulMod T.f T.m (T.expT.getD i zero) (T.expT.getD 1 zero)) &&
    mulMod T.f T.m (T.expT.getD (T.q1 - 1) zero) (T.expT.getD 1 zero) == one

variable {R : Type*} [CommRing R] {ι : ZMod 3 →+* R} {r : R}

theorem isMul_mulT {T : Tab} (hT : tabCheck T = true) (hf : T.f.Valid)
    (hf0 : ev ι r T.f = 0) : PE.IsMul ι r (mulT T) := by
  simp only [tabCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hT
  obtain ⟨⟨⟨⟨⟨hsize, hq⟩, h0⟩, hval⟩, hstep⟩, hlast⟩ := hT
  set g := T.expT.getD 1 zero
  have hvalid : ∀ i < T.q1, (T.expT.getD i zero).Valid := fun i hi =>
    (valid_iff _).mpr (hval i hi)
  have hg : g.Valid := hvalid 1 (by omega)
  have hpow : ∀ i < T.q1, ev ι r (T.expT.getD i zero) = ev ι r g ^ i := by
    intro i hi
    induction i with
    | zero => rw [h0, ev_one, pow_zero]
    | succ i ih =>
      rw [hstep i (by omega), ev_mulMod hf (hvalid i (by omega)) hg hf0, ih (by omega),
        pow_succ]
  have hq1 : ev ι r g ^ T.q1 = 1 := by
    have := congrArg (ev ι r) hlast
    rw [ev_mulMod hf (hvalid _ (by omega)) hg hf0, ev_one, hpow _ (by omega), ← pow_succ,
      Nat.sub_add_cancel (by omega)] at this
    exact this
  unfold PE.IsMul
  intro a b ha hb
  unfold mulT
  dsimp only
  split_ifs with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨hla, hlb⟩, hea⟩, heb⟩ := h
    have hlt : (T.logT.getD (idx T.m a) 0 + T.logT.getD (idx T.m b) 0) % T.q1 < T.q1 :=
      Nat.mod_lt _ (by omega)
    refine ⟨hvalid _ hlt, ?_⟩
    set la := T.logT.getD (idx T.m a) 0
    set lb := T.logT.getD (idx T.m b) 0
    calc ev ι r (T.expT.getD ((la + lb) % T.q1) zero) = ev ι r g ^ ((la + lb) % T.q1) :=
          hpow _ hlt
      _ = ev ι r g ^ (la + lb) := by
          conv_rhs => rw [← Nat.div_add_mod (la + lb) T.q1, pow_add, pow_mul, hq1, one_pow,
            one_mul]
      _ = ev ι r (T.expT.getD la zero) * ev ι r (T.expT.getD lb zero) := by
          rw [hpow _ hla, hpow _ hlb, pow_add]
      _ = ev ι r a * ev ι r b := by rw [hea, heb]
  · exact ⟨valid_mulMod hf ha, ev_mulMod hf ha hb hf0⟩

end F3P

end CFSG.Walter.Ree.Bombieri
