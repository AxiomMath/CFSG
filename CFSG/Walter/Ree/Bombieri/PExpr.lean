module

public import CFSG.Walter.Ree.Bombieri.F3Poly
public import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.Walter.Ree.Bombieri

inductive PE : Type
  | var : ℕ → PE
  | atom : ℕ → PE
  | const : ℤ → PE
  | add : PE → PE → PE
  | sub : PE → PE → PE
  | mul : PE → PE → PE
  | pow : PE → ℕ → PE
  | neg : PE → PE
deriving Repr, Inhabited

namespace PE

instance : Add PE := ⟨add⟩
instance : Sub PE := ⟨sub⟩
instance : Mul PE := ⟨mul⟩
instance : Neg PE := ⟨neg⟩
instance : HPow PE ℕ PE := ⟨pow⟩
instance {n : ℕ} : OfNat PE n := ⟨const n⟩

section eval

variable {R : Type*} [CommRing R]

@[expose] def eval (ρ α : ℕ → R) : PE → R
  | var i => ρ i
  | atom k => α k
  | const c => c
  | add a b => eval ρ α a + eval ρ α b
  | sub a b => eval ρ α a - eval ρ α b
  | mul a b => eval ρ α a * eval ρ α b
  | pow a n => eval ρ α a ^ n
  | neg a => -eval ρ α a

@[simp] theorem eval_var (ρ α : ℕ → R) (i : ℕ) : eval ρ α (var i) = ρ i := rfl
@[simp] theorem eval_atom (ρ α : ℕ → R) (k : ℕ) : eval ρ α (atom k) = α k := rfl
@[simp] theorem eval_const (ρ α : ℕ → R) (c : ℤ) : eval ρ α (const c) = c := rfl
@[simp] theorem eval_add (ρ α : ℕ → R) (a b : PE) :
    eval ρ α (a + b) = eval ρ α a + eval ρ α b := rfl
@[simp] theorem eval_sub (ρ α : ℕ → R) (a b : PE) :
    eval ρ α (a - b) = eval ρ α a - eval ρ α b := rfl
@[simp] theorem eval_mul (ρ α : ℕ → R) (a b : PE) :
    eval ρ α (a * b) = eval ρ α a * eval ρ α b := rfl
@[simp] theorem eval_pow (ρ α : ℕ → R) (a : PE) (n : ℕ) :
    eval ρ α (a ^ n) = eval ρ α a ^ n := rfl
@[simp] theorem eval_neg (ρ α : ℕ → R) (a : PE) : eval ρ α (-a) = -eval ρ α a := rfl
@[simp] theorem eval_ofNat (ρ α : ℕ → R) (n : ℕ) [n.AtLeastTwo] :
    eval ρ α (OfNat.ofNat n : PE) = OfNat.ofNat n := by
  change ((n : ℤ) : R) = _
  rw [Int.cast_natCast]
  rfl

@[simp] theorem eval_zero (ρ α : ℕ → R) : eval ρ α (0 : PE) = 0 := by
  change ((0 : ℕ) : ℤ) = (0 : R)
  simp

@[simp] theorem eval_one (ρ α : ℕ → R) : eval ρ α (1 : PE) = 1 := by
  change ((1 : ℕ) : ℤ) = (1 : R)
  simp

theorem map_eval {S : Type*} [CommRing S] (h : R →+* S) (ρ α : ℕ → R) :
    ∀ e : PE, h (eval ρ α e) = eval (h ∘ ρ) (h ∘ α) e
  | var _ => rfl
  | atom _ => rfl
  | const c => by simp [eval]
  | add a b => by simp [eval, map_eval h ρ α a, map_eval h ρ α b]
  | sub a b => by simp [eval, map_eval h ρ α a, map_eval h ρ α b]
  | mul a b => by simp [eval, map_eval h ρ α a, map_eval h ρ α b]
  | pow a n => by simp [eval, map_eval h ρ α a]
  | neg a => by simp [eval, map_eval h ρ α a]

end eval

@[expose] def ofInt (c : ℤ) : F3P :=
  if c % 3 = 0 then F3P.zero else if c % 3 = 1 then F3P.one else F3P.neg F3P.one

@[expose] def powM (mulF : F3P → F3P → F3P) (a : F3P) : ℕ → F3P
  | 0 => F3P.one
  | n + 1 => mulF (powM mulF a n) a

@[expose] def evalM (mulF : F3P → F3P → F3P) (ρ α : ℕ → F3P) : PE → F3P
  | var i => ρ i
  | atom j => α j
  | const c => ofInt c
  | add a b => F3P.add (evalM mulF ρ α a) (evalM mulF ρ α b)
  | sub a b => F3P.sub (evalM mulF ρ α a) (evalM mulF ρ α b)
  | mul a b => mulF (evalM mulF ρ α a) (evalM mulF ρ α b)
  | pow a n => powM mulF (evalM mulF ρ α a) n
  | neg a => F3P.neg (evalM mulF ρ α a)

theorem valid_ofInt (c : ℤ) : (ofInt c).Valid := by
  unfold ofInt
  split_ifs
  · exact F3P.valid_zero
  · exact F3P.valid_one
  · exact F3P.valid_neg F3P.valid_one

section ev

variable {R : Type*} [CommRing R] {ι : ZMod 3 →+* R} {r : R}

theorem ev_ofInt (c : ℤ) : F3P.ev ι r (ofInt c) = c := by
  have hc : (c : R) = ι (c : ZMod 3) := (map_intCast ι c).symm
  rw [hc, ← ZMod.intCast_mod c 3]
  unfold ofInt
  have h3 := Int.emod_nonneg c (by norm_num : (3 : ℤ) ≠ 0)
  have h3' := Int.emod_lt_of_pos c (by norm_num : (0 : ℤ) < 3)
  split_ifs with h0 h1
  · rw [F3P.ev_zero, Nat.cast_ofNat, h0]; simp
  · rw [F3P.ev_one, Nat.cast_ofNat, h1]; simp
  · have h2 : c % 3 = 2 := by omega
    rw [F3P.ev_neg, F3P.ev_one, Nat.cast_ofNat, h2]
    have : ((2 : ℤ) : ZMod 3) = -1 := by decide
    rw [this, map_neg, map_one]

@[expose] def IsMul (ι : ZMod 3 →+* R) (r : R) (mulF : F3P → F3P → F3P) : Prop :=
  ∀ a b : F3P, a.Valid → b.Valid →
    (mulF a b).Valid ∧ F3P.ev ι r (mulF a b) = F3P.ev ι r a * F3P.ev ι r b

theorem powM_spec {mulF : F3P → F3P → F3P} (hm : IsMul ι r mulF) {a : F3P} (ha : a.Valid) :
    ∀ n : ℕ, (powM mulF a n).Valid ∧ F3P.ev ι r (powM mulF a n) = F3P.ev ι r a ^ n
  | 0 => ⟨F3P.valid_one, by simp [powM, F3P.ev_one]⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := powM_spec hm ha n
    obtain ⟨h3, h4⟩ := hm _ _ h1 ha
    exact ⟨h3, by rw [powM, h4, h2, pow_succ]⟩

theorem evalM_spec {mulF : F3P → F3P → F3P} (hm : IsMul ι r mulF) {ρ α : ℕ → F3P}
    (hρ : ∀ i, (ρ i).Valid) (hα : ∀ j, (α j).Valid) :
    ∀ e : PE, (evalM mulF ρ α e).Valid ∧
      F3P.ev ι r (evalM mulF ρ α e) = eval (F3P.ev ι r ∘ ρ) (F3P.ev ι r ∘ α) e
  | var i => by simp only [evalM, eval]; exact ⟨hρ i, rfl⟩
  | atom j => by simp only [evalM, eval]; exact ⟨hα j, rfl⟩
  | const c => ⟨valid_ofInt c, ev_ofInt c⟩
  | add a b => by
    obtain ⟨ha, ea⟩ := evalM_spec hm hρ hα a
    obtain ⟨hb, eb⟩ := evalM_spec hm hρ hα b
    exact ⟨F3P.valid_add ha hb, by simp only [evalM, eval]; rw [F3P.ev_add ha hb, ea, eb]⟩
  | sub a b => by
    obtain ⟨ha, ea⟩ := evalM_spec hm hρ hα a
    obtain ⟨hb, eb⟩ := evalM_spec hm hρ hα b
    exact ⟨F3P.valid_sub ha hb, by simp only [evalM, eval]; rw [F3P.ev_sub ha hb, ea, eb]⟩
  | mul a b => by
    obtain ⟨ha, ea⟩ := evalM_spec hm hρ hα a
    obtain ⟨hb, eb⟩ := evalM_spec hm hρ hα b
    obtain ⟨h1, h2⟩ := hm _ _ ha hb
    exact ⟨h1, by simp only [evalM, eval]; rw [h2, ea, eb]⟩
  | pow a n => by
    obtain ⟨ha, ea⟩ := evalM_spec hm hρ hα a
    obtain ⟨h1, h2⟩ := powM_spec hm ha n
    exact ⟨h1, by simp only [evalM, eval]; rw [h2, ea]⟩
  | neg a => by
    obtain ⟨ha, ea⟩ := evalM_spec hm hρ hα a
    exact ⟨F3P.valid_neg ha, by simp only [evalM, eval]; rw [F3P.ev_neg, ea]⟩

theorem isMul_mulMod {f : F3P} {k : ℕ} (hf : f.Valid) (hf0 : F3P.ev ι r f = 0) :
    IsMul ι r (F3P.mulMod f k) :=
  fun _ _ ha hb => ⟨F3P.valid_mulMod hf ha, F3P.ev_mulMod hf ha hb hf0⟩

end ev

@[expose] def degB (dv da : ℕ → ℕ) : PE → ℕ
  | var i => dv i
  | atom j => da j
  | const _ => 0
  | add a b => max (degB dv da a) (degB dv da b)
  | sub a b => max (degB dv da a) (degB dv da b)
  | mul a b => degB dv da a + degB dv da b
  | pow a n => n * degB dv da a
  | neg a => degB dv da a

theorem degreeOf_eval_le {σ : Type*} {S : Type*} [CommRing S] (v : σ)
    {ρ α : ℕ → MvPolynomial σ S} {dv da : ℕ → ℕ} (hρ : ∀ i, (ρ i).degreeOf v ≤ dv i)
    (hα : ∀ j, (α j).degreeOf v ≤ da j) :
    ∀ e : PE, (eval ρ α e).degreeOf v ≤ degB dv da e
  | var i => hρ i
  | atom j => hα j
  | const c => by
    simp only [eval, degB]
    rw [← map_intCast (MvPolynomial.C : S →+* MvPolynomial σ S) c, MvPolynomial.degreeOf_C]
  | add a b => (MvPolynomial.degreeOf_add_le v _ _).trans
      (max_le_max (degreeOf_eval_le v hρ hα a) (degreeOf_eval_le v hρ hα b))
  | sub a b => (MvPolynomial.degreeOf_sub_le v _ _).trans
      (max_le_max (degreeOf_eval_le v hρ hα a) (degreeOf_eval_le v hρ hα b))
  | mul a b => (MvPolynomial.degreeOf_mul_le v _ _).trans
      (add_le_add (degreeOf_eval_le v hρ hα a) (degreeOf_eval_le v hρ hα b))
  | pow a n => (MvPolynomial.degreeOf_pow_le v _ n).trans
      (Nat.mul_le_mul_left n (degreeOf_eval_le v hρ hα a))
  | neg a => by
    simp only [eval, degB]
    rw [MvPolynomial.degreeOf_neg]
    exact degreeOf_eval_le v hρ hα a

end PE

end CFSG.Walter.Ree.Bombieri
