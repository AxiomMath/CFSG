module

public import CFSG.RepresentationTheory.SzMartineau.Linearized
public import CFSG.RepresentationTheory.SzMartineau.Cocycle
public import CFSG.RepresentationTheory.SzMartineau.Relations

public section

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit Matrix

namespace CFSG.RepresentationTheory.SzMartineau

variable {a : ℕ}

noncomputable local instance fintypeF (a : ℕ) : Fintype (F a) := Fintype.ofFinite (F a)

private noncomputable def frobVec {a : ℕ} (c : ℕ) (v : Fin 4 → F a) : Fin 4 → F a :=
  fun i => v i ^ 2 ^ c

private lemma frobVec_add {a : ℕ} (c : ℕ) (u v : Fin 4 → F a) :
    frobVec c (u + v) = frobVec c u + frobVec c v := by
  ext i
  simp only [frobVec, Pi.add_apply]
  rw [add_pow_char_pow]

private lemma frobVec_mulVec {a : ℕ} (c : ℕ) (M : Matrix (Fin 4) (Fin 4) (F a))
    (v : Fin 4 → F a) :
    frobVec c (M *ᵥ v) = M.map (· ^ 2 ^ c) *ᵥ frobVec c v := by
  ext i
  simp only [frobVec, Matrix.mulVec_apply_eq_sum, Matrix.map_apply]
  have hsum : (∑ j : Fin 4, M i j * v j) ^ 2 ^ c =
      ∑ j : Fin 4, (M i j * v j) ^ 2 ^ c := by
    simpa using (sum_pow_char_pow (p := 2) (n := c)
      (s := Finset.univ) (f := fun j : Fin 4 => M i j * v j))
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow]

@[expose] noncomputable def natAct (a : ℕ) : ↥(Sz a) →* AddMonoid.End (Fin 4 → F a) where
  toFun g :=
    { toFun := fun v => natHom a g *ᵥ v
      map_zero' := by simp
      map_add' := fun u v => by simp [Matrix.mulVec_add] }
  map_one' := by
    apply AddMonoidHom.ext
    intro v
    apply funext
    intro i
    change (natHom a 1 *ᵥ v) i = v i
    rw [map_one, Matrix.one_mulVec]
  map_mul' g h := by
    apply AddMonoidHom.ext
    intro v
    apply funext
    intro i
    change (natHom a (g * h) *ᵥ v) i = (natHom a g *ᵥ (natHom a h *ᵥ v)) i
    rw [map_mul, Matrix.mulVec_mulVec]

@[simp] theorem natAct_apply (a : ℕ) (g : ↥(Sz a)) (v : Fin 4 → F a) :
    natAct a g v = ((g : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) *ᵥ v := by
  rfl

private lemma natAct_mulVec (g : ↥(Sz a)) (M : Matrix (Fin 4) (Fin 4) (F a))
    (v : Fin 4 → F a) :
    natAct a g (M *ᵥ v) = (natHom a g * M) *ᵥ v := by
  simp only [natAct_apply, natHom_apply, Matrix.mulVec_mulVec]

private lemma frobVec_natAct (c : ℕ) (h : ↥(Sz a)) (v : Fin 4 → F a) :
    frobVec c (natAct a h v) = twHom a c h *ᵥ frobVec c v := by
  simp only [natAct_apply, natHom_apply, frobVec_mulVec, twHom_apply]

private lemma frobVec_zero {a : ℕ} (c : ℕ) :
    frobVec c (0 : Fin 4 → F a) = 0 := by
  ext i
  simp only [frobVec, Pi.zero_apply]
  rw [zero_pow (Nat.two_pow_pos c).ne']

private noncomputable def frobEnd {a : ℕ} (X : Matrix (Fin 4) (Fin 4) (F a)) (c : ℕ) :
    AddMonoid.End (Fin 4 → F a) where
  toFun v := X *ᵥ frobVec c v
  map_zero' := by rw [frobVec_zero, Matrix.mulVec_zero]
  map_add' u v := by simp [Matrix.mulVec_add, frobVec_add]

private noncomputable def frobSum {a : ℕ} (n : ℕ)
    (X : ℕ → Matrix (Fin 4) (Fin 4) (F a)) : AddMonoid.End (Fin 4 → F a) :=
  ∑ c ∈ Finset.range n, frobEnd (X c) c

private lemma frobSum_apply {a n : ℕ} (X : ℕ → Matrix (Fin 4) (Fin 4) (F a))
    (v : Fin 4 → F a) :
    frobSum n X v = ∑ c ∈ Finset.range n, X c *ᵥ frobVec c v := by
  classical
  change (∑ c ∈ Finset.range n, frobEnd (X c) c) v =
    ∑ c ∈ Finset.range n, X c *ᵥ frobVec c v
  induction (Finset.range n) using Finset.induction_on with
  | empty => simp
  | insert c s hc ih =>
      rw [Finset.sum_insert hc, Finset.sum_insert hc]
      change (frobEnd (X c) c) v + (∑ x ∈ s, frobEnd (X x) x) v =
        X c *ᵥ frobVec c v + ∑ x ∈ s, X x *ᵥ frobVec x v
      rw [ih]
      rfl

private lemma natAct_frobSum_apply {a n : ℕ} (X : ℕ → Matrix (Fin 4) (Fin 4) (F a))
    (g : ↥(Sz a)) (v : Fin 4 → F a) :
    natAct a g (frobSum n X v) =
      ∑ c ∈ Finset.range n, (natHom a g * X c) *ᵥ frobVec c v := by
  rw [frobSum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [natAct_mulVec]

private lemma frobSum_natAct_apply {a n : ℕ} (X : ℕ → Matrix (Fin 4) (Fin 4) (F a))
    (g : ↥(Sz a)) (v : Fin 4 → F a) :
    frobSum n X (natAct a g v) =
      ∑ c ∈ Finset.range n, (X c * twHom a c g) *ᵥ frobVec c v := by
  rw [frobSum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [frobVec_natAct, Matrix.mulVec_mulVec]

private lemma coboundary_frobSum_apply {a n : ℕ} (X : ℕ → Matrix (Fin 4) (Fin 4) (F a))
    (g : ↥(Sz a)) (v : Fin 4 → F a) :
    ((natAct a g : (Fin 4 → F a) →+ (Fin 4 → F a)) *
        (frobSum n X : (Fin 4 → F a) →+ (Fin 4 → F a)) -
        (frobSum n X : (Fin 4 → F a) →+ (Fin 4 → F a)) *
          (natAct a g : (Fin 4 → F a) →+ (Fin 4 → F a))) v =
      ∑ c ∈ Finset.range n,
        ((natHom a g * X c - X c * twHom a c g) *ᵥ frobVec c v) := by
  change natAct a g (frobSum n X v) - frobSum n X (natAct a g v) =
    ∑ c ∈ Finset.range n,
      ((natHom a g * X c - X c * twHom a c g) *ᵥ frobVec c v)
  rw [natAct_frobSum_apply, frobSum_natAct_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.sub_mulVec]

private lemma cocycle_sum_eq {n : ℕ}
    (A : ℕ → ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a))
    (Y : ↥(Sz a) → AddMonoid.End (Fin 4 → F a))
    (hA : ∀ g v, Y g v = ∑ c ∈ Finset.range n, A c g *ᵥ frobVec c v)
    (hY : ∀ g h, Y (g * h) = natAct a g * Y h + Y g * natAct a h)
    (g h : ↥(Sz a)) (v : Fin 4 → F a) :
    (∑ c ∈ Finset.range n, A c (g * h) *ᵥ frobVec c v) =
      ∑ c ∈ Finset.range n,
        (natHom a g * A c h + A c g * twHom a c h) *ᵥ frobVec c v := by
  calc
    (∑ c ∈ Finset.range n, A c (g * h) *ᵥ frobVec c v) = Y (g * h) v :=
      (hA (g * h) v).symm
    _ = (natAct a g * Y h + Y g * natAct a h) v := by rw [hY g h]
    _ = natAct a g (Y h v) + Y g (natAct a h v) := rfl
    _ = natAct a g (∑ c ∈ Finset.range n, A c h *ᵥ frobVec c v) +
          ∑ c ∈ Finset.range n, A c g *ᵥ frobVec c (natAct a h v) := by
        rw [hA h v, hA g (natAct a h v)]
    _ = (∑ c ∈ Finset.range n, (natHom a g * A c h) *ᵥ frobVec c v) +
          ∑ c ∈ Finset.range n, (A c g * twHom a c h) *ᵥ frobVec c v := by
        rw [map_sum]
        congr 1
        · refine Finset.sum_congr rfl fun c _ => ?_
          rw [natAct_mulVec]
        · refine Finset.sum_congr rfl fun c _ => ?_
          rw [frobVec_natAct, Matrix.mulVec_mulVec]
    _ = ∑ c ∈ Finset.range n,
          (natHom a g * A c h + A c g * twHom a c h) *ᵥ frobVec c v := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Matrix.add_mulVec]

private lemma twisted_cocycle_of_decomp {n : ℕ}
    (hq : Fintype.card (F a) = 2 ^ n)
    (A : ℕ → ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a))
    (Y : ↥(Sz a) → AddMonoid.End (Fin 4 → F a))
    (hA : ∀ g v, Y g v = ∑ c ∈ Finset.range n, A c g *ᵥ frobVec c v)
    (hY : ∀ g h, Y (g * h) = natAct a g * Y h + Y g * natAct a h) :
    ∀ c < n, IsTwistedCocycle (natHom a) (twHom a c) (A c) := by
  intro c hc g h
  let B : ℕ → Matrix (Fin 4) (Fin 4) (F a) := fun d =>
    A d (g * h) - (natHom a g * A d h + A d g * twHom a d h)
  have hzero : ∀ v, ∑ d ∈ Finset.range n, B d *ᵥ frobVec d v = 0 := by
    intro v
    have hsum := cocycle_sum_eq A Y hA hY g h v
    calc
      (∑ d ∈ Finset.range n, B d *ᵥ frobVec d v)
          = ∑ d ∈ Finset.range n,
              (A d (g * h) *ᵥ frobVec d v -
                (natHom a g * A d h + A d g * twHom a d h) *ᵥ frobVec d v) := by
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [show B d = A d (g * h) -
              (natHom a g * A d h + A d g * twHom a d h) from rfl, Matrix.sub_mulVec]
      _ = (∑ d ∈ Finset.range n, A d (g * h) *ᵥ frobVec d v) -
            ∑ d ∈ Finset.range n,
              (natHom a g * A d h + A d g * twHom a d h) *ᵥ frobVec d v := by
            rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hsum, sub_self]
  have hB := frobenius_decomp_eq_zero hq B hzero c hc
  exact sub_eq_zero.mp hB

theorem addCocycle_eq_coboundary_of {a : ℕ}
    (hL2 : ∀ c < 2 * a + 1, ∀ Y : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a),
      IsTwistedCocycle (natHom a) (twHom a c) Y →
        ∃ X, ∀ g, Y g = coboundary (natHom a) (twHom a c) X g)
    (Y : ↥(Sz a) → AddMonoid.End (Fin 4 → F a))
    (hY : ∀ g h, Y (g * h) = natAct a g * Y h + Y g * natAct a h) :
    ∃ X : AddMonoid.End (Fin 4 → F a), ∀ g, Y g = natAct a g * X - X * natAct a g := by
  classical
  let n := 2 * a + 1
  have hq : Fintype.card (F a) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (2 * a + 1) (by omega)
  choose A hA using fun g : ↥(Sz a) =>
    exists_frobenius_decomp (K := F a) (m := 4) hq (Y g)
  let Amat : ℕ → ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a) := fun c g => A g c
  have hAmat : ∀ g v, (Y g : (Fin 4 → F a) →+ (Fin 4 → F a)) v =
      ∑ c ∈ Finset.range n, Amat c g *ᵥ frobVec c v := by
    intro g v
    calc
      (Y g : (Fin 4 → F a) →+ (Fin 4 → F a)) v =
          ∑ c ∈ Finset.range n, A g c *ᵥ (fun i => v i ^ 2 ^ c) := hA g v
      _ = ∑ c ∈ Finset.range n, Amat c g *ᵥ frobVec c v := by rfl
  have hTw : ∀ c < n, IsTwistedCocycle (natHom a) (twHom a c) (Amat c) :=
    twisted_cocycle_of_decomp hq Amat Y hAmat hY
  let Xmat : ℕ → Matrix (Fin 4) (Fin 4) (F a) := fun c =>
    if h : c < n then Classical.choose (hL2 c h (Amat c) (hTw c h)) else 0
  have hXmat : ∀ c (hc : c < n) (g : ↥(Sz a)),
      Amat c g = coboundary (natHom a) (twHom a c) (Xmat c) g := by
    intro c hc g
    have hX : Xmat c = Classical.choose (hL2 c hc (Amat c) (hTw c hc)) := by
      simp only [Xmat, dif_pos hc]
    rw [hX]
    exact Classical.choose_spec (hL2 c hc (Amat c) (hTw c hc)) g
  refine ⟨frobSum n Xmat, fun g => ?_⟩
  apply AddMonoidHom.ext
  intro v
  change (Y g : (Fin 4 → F a) →+ (Fin 4 → F a)) v =
    ((natAct a g : (Fin 4 → F a) →+ (Fin 4 → F a)) *
        (frobSum n Xmat : (Fin 4 → F a) →+ (Fin 4 → F a)) -
        (frobSum n Xmat : (Fin 4 → F a) →+ (Fin 4 → F a)) *
          (natAct a g : (Fin 4 → F a) →+ (Fin 4 → F a))) v
  rw [coboundary_frobSum_apply, hAmat g v]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [hXmat c (Finset.mem_range.mp hc) g, coboundary_apply]

end CFSG.RepresentationTheory.SzMartineau
