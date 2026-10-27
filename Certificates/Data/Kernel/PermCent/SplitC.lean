module

public import CFSG.Certificates.Kernel.PermCent.CVSound

public section

namespace CFSG.Certificates.Kernel.PkCV

open CFSG.KC.Enum CFSG.KS

variable {n : Nat}

@[expose] noncomputable def eq3C (r p q s : CV n) : Bool :=
  eq3 n (wC n) (mask (wC n)) r.1 p.1 q.1 s.1

theorem eq3C_eq [Small n] (r p q s : CV n) : eq3C r p q s = decide (r = p * q * s) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, eq3C, eq3, CFSG.KS.PK.allN_iff]
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

variable [Small n]

@[expose] noncomputable def levelsC (Q : CFSG.Certificates.RawSchreierDatum n) : List (List (CV n)) :=
  (List.finRange Q.baseCount).map fun i =>
    (CFSG.Certificates.Kernel.PkEnum.transV
      (CFSG.Certificates.Kernel.PkEnum.levelV (CFSG.Certificates.Kernel.PkEnum.strongV Q) Q.base i)).map
      toCV

theorem elemsC_eq_levelsC (Q : CFSG.Certificates.RawSchreierDatum n) :
    elemsC Q = productsC (levelsC Q) := rfl

@[expose] noncomputable def allSplit (L : List (List (CV n))) (g : CV n → CV n → Bool) : Bool :=
  match L with
  | [] => g 1 1
  | T :: Ts => T.all fun t => (productsC Ts).all fun r => g t r

theorem allSplit_eq (L : List (List (CV n))) (f : CV n → Bool) :
    allSplit L (fun t r => f (t * r)) = (productsC L).all f := by
  cases L with
  | nil =>
    change f (1 * 1) = [(1 : CV n)].all f
    rw [mul_one, List.all_cons, List.all_nil, Bool.and_true]
  | cons T Ts =>
    simp only [allSplit, productsC, List.all_flatMap, List.all_map, Function.comp_def]

theorem allSplit_congr (L : List (List (CV n))) {g h : CV n → CV n → Bool}
    (e : ∀ t r, g t r = h t r) : allSplit L g = allSplit L h := by
  have : g = h := funext fun t => funext fun r => e t r
  rw [this]

theorem allSplit_pre (L : List (List (CV n))) (pre : CV n → CV n → Bool) (f : CV n → Bool)
    (h : ∀ t r, pre t r = false → f (t * r) = true) :
    allSplit L (fun t r => !pre t r || f (t * r)) = (productsC L).all f := by
  rw [← allSplit_eq]
  apply allSplit_congr
  intro t r
  cases hp : pre t r
  · rw [h t r hp]
    rfl
  · rfl

@[expose] noncomputable def sqPt (t r : CV n) (p : Nat) : Bool :=
  Nat.beq (img n t.1 (img n r.1 (img n t.1 (img n r.1 p)))) p

theorem sqPt_of {t r : CV n} {p : Nat} (hp : p < n) (h : powOneC (t * r) 2 = true) :
    sqPt t r p = true := by
  rw [powOneC_eq, decide_eq_true_iff, pow_two] at h
  have h' := congrArg (fun σ : CV n => (ev σ ⟨p, hp⟩ : Nat)) h
  simp only [ev_mul, ev_one, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, ev_apply, Fin.val_mk] at h'
  exact Nat.beq_eq.mpr h'

@[expose] noncomputable def cmPt (t r q : CV n) (p : Nat) : Bool :=
  Nat.beq (img n t.1 (img n r.1 (img n q.1 p))) (img n q.1 (img n t.1 (img n r.1 p)))

theorem cmPt_of {t r q : CV n} {p : Nat} (hp : p < n) (h : eq22C (t * r) q q (t * r) = true) :
    cmPt t r q p = true := by
  rw [eq22C_eq, decide_eq_true_iff] at h
  have h' := congrArg (fun σ : CV n => (ev σ ⟨p, hp⟩ : Nat)) h
  simp only [ev_mul, Equiv.Perm.mul_apply, ev_apply, Fin.val_mk] at h'
  exact Nat.beq_eq.mpr h'

@[expose] noncomputable def sqEqPt (t r c : CV n) (p : Nat) : Bool :=
  Nat.beq (img n t.1 (img n r.1 (img n t.1 (img n r.1 p)))) (img n c.1 p)

theorem sqEqPt_of {t r c : CV n} {p : Nat} (hp : p < n) (h : eq22C (t * r) (t * r) c 1 = true) :
    sqEqPt t r c p = true := by
  rw [eq22C_eq, decide_eq_true_iff, mul_one] at h
  have h' := congrArg (fun σ : CV n => (ev σ ⟨p, hp⟩ : Nat)) h
  simp only [ev_mul, Equiv.Perm.mul_apply, ev_apply, Fin.val_mk] at h'
  exact Nat.beq_eq.mpr h'

@[expose] noncomputable def filterSplit (L : List (List (CV n))) (pre : CV n → CV n → Bool)
    (f : CV n → Bool) : List (CV n) :=
  match L with
  | [] => [1].filter f
  | T :: Ts => T.flatMap fun t => (productsC Ts).flatMap fun r =>
      Bool.rec [] [t * r] (pre t r && f (t * r))

theorem filterSplit_eq (L : List (List (CV n))) (pre : CV n → CV n → Bool) (f : CV n → Bool)
    (h : ∀ t r, pre t r = false → f (t * r) = false) :
    filterSplit L pre f = (productsC L).filter f := by
  cases L with
  | nil => rfl
  | cons T Ts =>
    rw [filterSplit, productsC, List.filter_flatMap]
    congr 1
    funext t
    induction productsC Ts with
    | nil => rfl
    | cons r rs ih =>
      rw [List.flatMap_cons, List.map_cons, List.filter_cons, ih]
      cases hf : f (t * r)
      · rw [Bool.and_false]
        rfl
      · cases hp : pre t r
        · exact absurd (h t r hp) (by rw [hf]; decide)
        · rfl

end CFSG.Certificates.Kernel.PkCV

end
