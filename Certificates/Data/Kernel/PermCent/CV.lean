module

public import CFSG.Certificates.Kernel.Spor.PinvSSound
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

namespace CFSG.Certificates.Kernel.PkCV

open CFSG.Certificates CFSG.KC.Enum CFSG.KS CFSG.KS.PF CFSG.KS.PinvS
  CFSG.Certificates.Kernel.PkEnum

@[expose] def wC (n : Nat) : Nat := (n + 1).log2 + 1

theorem lt_wC (n : Nat) : n + 1 < 2 ^ wC n := Nat.lt_log2_self

theorem wC_pos (n : Nat) : 0 < wC n := Nat.succ_pos _

@[expose] def Canon (n p : Nat) : Prop := p >>> (n * wC n) = 0 ∧ InjK n (wC n) p

abbrev CV (n : Nat) := {p : Nat // Canon n p}

variable {n : Nat}

noncomputable abbrev img (n p i : Nat) : Nat := pg (wC n) (mask (wC n)) p i

theorem fld_pmk {w : Nat} {f : Nat → Nat} (hn : n < 16777216) (hf : ∀ x < n, f x < 2 ^ w) :
    Fld w (pmk n w f) (fun i => if i < n then f i else 0) := by
  have hc := clog_spec hn
  have h := fld_pmkT n w f hf (clog n) 0
  have e : pmk n w f = pmkT n w f (clog n) 0 := by
    unfold pmk
    rw [strictN_eqP]
  rw [e]
  refine fld_congr h ?_
  intro i
  by_cases hi : i < n
  · have h2 : i < 2 ^ clog n := by omega
    simp [hi, h2]
  · simp [hi]

theorem pg_pmk {w i : Nat} {f : Nat → Nat} (hn : n < 16777216) (hf : ∀ x < n, f x < 2 ^ w)
    (hi : i < n) : pg w (mask w) (pmk n w f) i = f i := by
  rw [pg_of_fld (fld_pmk hn hf) (by simp only [hi, ↓reduceIte]; exact hf i hi)]
  simp [hi]

theorem pmk_shr {w : Nat} {f : Nat → Nat} (hn : n < 16777216) (hw : 0 < w)
    (hf : ∀ x < n, f x < 2 ^ w) : pmk n w f >>> (n * w) = 0 :=
  shr_zero_of_fld hw (fld_pmk hn hf) (fun i hi => by
    have : ¬ i < n := by omega
    simp [this])

theorem canon_pmk {f : Nat → Nat} (hn : n < 16777216) (hf : ∀ x < n, f x < n)
    (hinj : ∀ a < n, ∀ b < n, f a = f b → a = b) : Canon n (pmk n (wC n) f) := by
  have hf' : ∀ x < n, f x < 2 ^ wC n := fun x hx => (hf x hx).trans (by have := lt_wC n; omega)
  refine ⟨pmk_shr hn (wC_pos n) hf', fun i hi => ?_, fun a ha b hb e => ?_⟩
  · rw [pg_pmk hn hf' hi]
    exact hf i hi
  · rw [pg_pmk hn hf' ha, pg_pmk hn hf' hb] at e
    exact hinj a ha b hb e

class Small (n : Nat) : Prop where
  lt : n < 16777216

instance : Small 8 := ⟨by decide⟩
instance : Small 21 := ⟨by decide⟩
instance : Small 26 := ⟨by decide⟩
instance : Small 28 := ⟨by decide⟩
instance : Small 42 := ⟨by decide⟩
instance : Small 45 := ⟨by decide⟩

variable [hs : Small n]

theorem lt32 : n < 2 ^ 32 := by have := hs.lt; omega

theorem hw : n < 2 ^ wC n := by have := lt_wC n; omega

noncomputable instance : Mul (CV n) :=
  ⟨fun a b => ⟨pcomp n (wC n) (mask (wC n)) a.1 b.1,
    pcomp_shr a.1 b.1 lt32 (wC_pos n), injK_pcomp lt32 a.2.2 b.2.2⟩⟩

noncomputable instance : One (CV n) :=
  ⟨⟨pidn n (wC n), pidn_shr hs.lt (lt_wC n),
    fun i hi => by rw [pg_pidn hs.lt (lt_wC n) hi]; exact hi,
    fun a ha b hb e => by rwa [pg_pidn hs.lt (lt_wC n) ha, pg_pidn hs.lt (lt_wC n) hb] at e⟩⟩

noncomputable instance : Inv (CV n) :=
  ⟨fun a => ⟨pinvS n (wC n) (mask (wC n)) a.1, pinvS_shr hw a.2.2.1, injK_pinvS hw a.2.2⟩⟩

noncomputable instance : Div (CV n) := ⟨fun a b => a * b⁻¹⟩

@[expose] noncomputable def sqN (n a h : Nat) (odd : Bool) : Nat :=
  strictN h fun x => strictN (pcomp n (wC n) (mask (wC n)) x x) fun y =>
    if odd then pcomp n (wC n) (mask (wC n)) y a else y

theorem sqN_eq (a h : CV n) (odd : Bool) :
    sqN n a.1 h.1 odd = (if odd then h * h * a else h * h).1 := by
  unfold sqN
  rw [strictN_eqP, strictN_eqP]
  cases odd <;> rfl

@[expose] noncomputable def sqC (a h : CV n) (odd : Bool) : CV n :=
  ⟨sqN n a.1 h.1 odd, by rw [sqN_eq]; exact (if odd then h * h * a else h * h).2⟩

@[expose] noncomputable def powF (a : CV n) : Nat → Nat → CV n
  | 0, _ => 1
  | f + 1, k => if k = 0 then 1 else sqC a (powF a f (k / 2)) (k % 2 != 0)

@[expose, instance_reducible] noncomputable def npowC : Pow (CV n) Nat := ⟨fun a k => powF a k k⟩

@[expose, instance_reducible] noncomputable def zpowC : Pow (CV n) Int := ⟨fun a k => match k with
  | .ofNat m => powF a m m
  | .negSucc m => (powF a (m + 1) (m + 1))⁻¹⟩

theorem img_inv_img (a : CV n) {i : Nat} (hi : i < n) :
    img n (pinvS n (wC n) (mask (wC n)) a.1) (img n a.1 i) = i := pg_pinvS hw a.2.2 hi

theorem img_img_inv (a : CV n) {j : Nat} (hj : j < n) :
    img n a.1 (img n (pinvS n (wC n) (mask (wC n)) a.1) j) = j := by
  obtain ⟨i, hi, rfl⟩ := surj_of_injK a.2.2 j hj
  rw [img_inv_img a hi]

@[expose] noncomputable def ev (a : CV n) : Equiv.Perm (Fin n) where
  toFun i := ⟨img n a.1 i, a.2.2.1 i i.2⟩
  invFun i := ⟨img n (pinvS n (wC n) (mask (wC n)) a.1) i, pinvS_lt hw a.2.2 i i.2⟩
  left_inv i := Fin.ext (img_inv_img a i.2)
  right_inv i := Fin.ext (img_img_inv a i.2)

theorem ev_apply (a : CV n) (i : Fin n) : (ev a i : Nat) = img n a.1 i := rfl

theorem ev_mul (a b : CV n) : ev (a * b) = ev a * ev b := by
  ext i
  rw [Equiv.Perm.mul_apply, ev_apply, ev_apply, ev_apply]
  exact pg_pcomp lt32 i.2

theorem ev_one : ev (1 : CV n) = 1 := by
  ext i
  rw [ev_apply]
  exact pg_pidn hs.lt (lt_wC n) i.2

theorem ev_inv (a : CV n) : ev a⁻¹ = (ev a)⁻¹ := Equiv.ext fun _ => rfl

theorem ev_injective : Function.Injective (ev : CV n → Equiv.Perm (Fin n)) := by
  intro a b h
  apply Subtype.ext
  refine eq_of_fields (wC_pos n) a.2.1 b.2.1 fun i hi => ?_
  exact congrArg (fun σ : Equiv.Perm (Fin n) => (σ ⟨i, hi⟩ : Nat)) h

theorem ev_powF (a : CV n) (f : Nat) : ∀ k, k < 2 ^ f → ev (powF a f k) = ev a ^ k := by
  induction f with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rw [powF, ev_one, pow_zero]
  | succ f ih =>
    intro k hk
    rw [powF]
    by_cases h0 : k = 0
    · rw [if_pos h0, ev_one, h0, pow_zero]
    · rw [if_neg h0]
      have hm : k / 2 < 2 ^ f := by
        rw [Nat.pow_succ] at hk
        omega
      have ihm := ih (k / 2) hm
      have hsq : ∀ (h : CV n) (odd : Bool), sqC a h odd = if odd then h * h * a else h * h :=
        fun h odd => Subtype.ext (sqN_eq a h odd)
      rw [hsq]
      by_cases he : k % 2 = 0
      · have : (k % 2 != 0) = false := by simp [he]
        rw [this, if_neg (by simp), ev_mul, ihm, ← pow_add]
        congr 1
        omega
      · have : (k % 2 != 0) = true := by simp only [bne_iff_ne, ne_eq]; exact he
        rw [this, if_pos rfl, ev_mul, ev_mul, ihm, ← pow_add, ← pow_succ]
        congr 1
        omega

theorem ev_npowC (a : CV n) (k : Nat) : ev (@HPow.hPow _ _ _ (@instHPow _ _ npowC) a k) = ev a ^ k :=
  ev_powF a k k Nat.lt_two_pow_self

theorem ev_zpowC (a : CV n) (k : Int) :
    ev (@HPow.hPow _ _ _ (@instHPow _ _ zpowC) a k) = ev a ^ k := by
  cases k with
  | ofNat m =>
    change ev (powF a m m) = ev a ^ (Int.ofNat m)
    rw [Int.ofNat_eq_natCast, zpow_natCast, ev_powF a m m Nat.lt_two_pow_self]
  | negSucc m =>
    change ev (powF a (m + 1) (m + 1))⁻¹ = ev a ^ (Int.negSucc m)
    rw [zpow_negSucc, ev_inv, ev_powF a (m + 1) (m + 1) Nat.lt_two_pow_self]

theorem ev_div (a b : CV n) : ev (a / b) = ev a / ev b := by
  change ev (a * b⁻¹) = ev a / ev b
  rw [ev_mul, ev_inv, div_eq_mul_inv]

noncomputable instance : Group (CV n) := by
  let _i1 : Pow (CV n) Nat := npowC
  let _i2 : Pow (CV n) Int := zpowC
  exact Function.Injective.group ev ev_injective ev_one ev_mul ev_inv ev_div ev_npowC ev_zpowC

@[expose] noncomputable def evHom (n : Nat) [Small n] : CV n →* Equiv.Perm (Fin n) where
  toFun := ev
  map_one' := ev_one
  map_mul' := ev_mul

@[expose] noncomputable def eq22C (a b c d : CV n) : Bool :=
  eq22 n (wC n) (mask (wC n)) a.1 b.1 c.1 d.1

theorem eq22C_eq (a b c d : CV n) : eq22C a b c d = decide (a * b = c * d) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, eq22C, eq22, CFSG.KS.PK.allN_iff]
  constructor
  · intro h
    apply ev_injective
    rw [ev_mul, ev_mul]
    ext i
    have := h i i.2
    rw [Nat.beq_eq] at this
    simp only [Equiv.Perm.mul_apply, ev_apply]
    exact this
  · intro h i hi
    have h' := congrArg (fun σ : CV n => (ev σ ⟨i, hi⟩ : Nat)) h
    simp only [ev_mul, Equiv.Perm.mul_apply, ev_apply] at h'
    exact Nat.beq_eq.mpr h'

@[expose] noncomputable def powOneC (a : CV n) (k : Nat) : Bool :=
  allN n fun i => Nat.beq (fpow (img n a.1) k i) i

theorem fpow_succ' (f : Nat → Nat) (k q : Nat) : fpow f (k + 1) q = fpow f k (f q) := by
  change strictN (f q) (fpow f k) = fpow f k (f q)
  rw [strictN_eqP]

theorem fpow_ev (a : CV n) (k : Nat) (i : Fin n) :
    fpow (img n a.1) k i = ((ev a ^ k) i : Nat) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    rw [fpow_succ', pow_succ, Equiv.Perm.mul_apply]
    have := ih ⟨img n a.1 i, a.2.2.1 i i.2⟩
    exact this

theorem powOneC_eq (a : CV n) (k : Nat) : powOneC a k = decide (a ^ k = 1) := by
  have hk : ∀ b : CV n, b = 1 ↔ ev b = 1 := fun b => by rw [← ev_one]; exact ev_injective.eq_iff.symm
  rw [Bool.eq_iff_iff, decide_eq_true_iff, powOneC, CFSG.KS.PK.allN_iff, hk]
  have hp : ev (a ^ k) = ev a ^ k := map_pow (evHom n) a k
  rw [hp]
  constructor
  · intro h
    ext i
    have := h i i.2
    rw [Nat.beq_eq, fpow_ev a k ⟨i, i.2⟩] at this
    exact this
  · intro h i hi
    rw [Nat.beq_eq, fpow_ev a k ⟨i, hi⟩, h]
    rfl

@[expose] def orderIsP {M : Type*} [Monoid M] [DecidableEq M] (g : M) (m : Nat) (ps : List Nat) :
    Bool :=
  decide (g ^ m = 1) && ps.all fun p => !decide (g ^ (m / p) = 1)

@[expose] noncomputable def toCV (a : VP n) : CV n :=
  ⟨pmk n (wC n) (fun i => CFSG.KS.PK.fd (wd n) a.1.1 i),
    canon_pmk hs.lt (fun x hx => (a.2 x hx).1) (fun x hx y hy e => by
      rw [← (a.2 x hx).2.2.1, e, (a.2 y hy).2.2.1])⟩

@[expose] noncomputable def cOf (σ : Equiv.Perm (Fin n)) : CV n :=
  ⟨pmk n (wC n) (fun i => if h : i < n then (σ ⟨i, h⟩ : Nat) else 0),
    canon_pmk hs.lt (fun x hx => by rw [dif_pos hx]; exact (σ _).2) (fun x hx y hy e => by
      rw [dif_pos hx, dif_pos hy] at e
      exact congrArg Fin.val (σ.injective (Fin.ext e)))⟩

@[expose] noncomputable def productsC : List (List (CV n)) → List (CV n)
  | [] => [1]
  | T :: Ts => T.flatMap fun t => (productsC Ts).map (t * ·)

@[expose] noncomputable def elemsC (Q : RawSchreierDatum n) : List (CV n) :=
  productsC ((List.finRange Q.baseCount).map fun i =>
    (transV (levelV (strongV Q) Q.base i)).map toCV)

@[expose] noncomputable def siftC (Q : RawSchreierDatum n) (c : CV n) (i : Nat) : Bool :=
  siftV (levelsV (strongV Q) Q.base i) (codeV (ev c))

end CFSG.Certificates.Kernel.PkCV

end
