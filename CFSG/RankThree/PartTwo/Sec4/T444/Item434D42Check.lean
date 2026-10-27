module

public import CFSG.Monster.B.Mathieu.SylowSound
public import CFSG.RankThree.Native.PermEnumeration
public import Mathlib.Algebra.Order.Ring.Star
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434D42

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
  CFSG.RankThree.Native

variable {n : ℕ}

@[expose] def periodGo (f : ℕ → ℕ) (i : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, cur, ℓ => if f cur = i then ℓ + 1 else periodGo f i fuel (f cur) (ℓ + 1)

@[expose] def period (f : ℕ → ℕ) (i fuel : ℕ) : ℕ := periodGo f i fuel i 0

theorem periodGo_spec (f : ℕ → ℕ) (i : ℕ) : ∀ (fuel cur ℓ r : ℕ), cur = f^[ℓ] i →
    (∀ j, 0 < j → j ≤ ℓ → f^[j] i ≠ i) → periodGo f i fuel cur ℓ = r → 0 < r →
    f^[r] i = i ∧ ∀ j, 0 < j → j < r → f^[j] i ≠ i := by
  intro fuel
  induction fuel with
  | zero =>
    intro cur ℓ r _ _ h hr
    simp only [periodGo] at h
    omega
  | succ fuel ih =>
    intro cur ℓ r hcur hmin h hr
    simp only [periodGo] at h
    by_cases hf : f cur = i
    · rw [ite_eq_left hf] at h
      subst h
      refine ⟨?_, fun j hj hjl => hmin j hj (by omega)⟩
      rw [Function.iterate_succ_apply', ← hcur]
      exact hf
    · rw [ite_eq_right hf] at h
      refine ih (f cur) (ℓ + 1) r ?_ ?_ h hr
      · rw [Function.iterate_succ_apply', ← hcur]
      · intro j hj hjl
        rcases Nat.lt_or_ge j (ℓ + 1) with h1 | h1
        · exact hmin j hj (by omega)
        · have : j = ℓ + 1 := by omega
          subst this
          rw [Function.iterate_succ_apply', ← hcur]
          exact hf

theorem period_spec {f : ℕ → ℕ} {i fuel ℓ : ℕ} (h : period f i fuel = ℓ) (hℓ : 0 < ℓ) :
    f^[ℓ] i = i ∧ ∀ j, 0 < j → j < ℓ → f^[j] i ≠ i :=
  periodGo_spec f i fuel i 0 ℓ rfl (fun j hj hj0 => by omega) h hℓ

theorem dvd_of_period {f : ℕ → ℕ} {i ℓ m : ℕ} (hℓ : 0 < ℓ) (h1 : f^[ℓ] i = i)
    (hmin : ∀ j, 0 < j → j < ℓ → f^[j] i ≠ i) (hm : f^[m] i = i) : ℓ ∣ m := by
  have hper : ∀ q, f^[ℓ * q] i = i := by
    intro q
    induction q with
    | zero => rfl
    | succ q ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, h1]
      exact ih
  have hmod : f^[m % ℓ] i = i := by
    have h2 : f^[m % ℓ + ℓ * (m / ℓ)] i = i := by
      rw [Nat.mod_add_div]
      exact hm
    rw [Function.iterate_add_apply, hper] at h2
    exact h2
  by_contra hnd
  have hpos : 0 < m % ℓ := Nat.pos_of_ne_zero fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
  exact hmin _ hpos (Nat.mod_lt _ hℓ) hmod

@[expose] def permFun (W : Equiv.Perm (Fin n)) (p : ℕ) : ℕ :=
  if h : p < n then (W ⟨p, h⟩ : ℕ) else p

theorem permFun_lt (W : Equiv.Perm (Fin n)) {p : ℕ} (hp : p < n) : permFun W p < n := by
  rw [permFun, dite_eq_left hp]
  exact (W ⟨p, hp⟩).2

theorem iterate_permFun (W : Equiv.Perm (Fin n)) {i : ℕ} (hi : i < n) :
    ∀ k : ℕ, (permFun W)^[k] i = ((W ^ k) ⟨i, hi⟩ : ℕ) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hk : ((W ^ k) ⟨i, hi⟩ : ℕ) < n := ((W ^ k) ⟨i, hi⟩).2
    rw [permFun, dite_eq_left hk, pow_succ']
    rfl

theorem iterate_eq_of_agree {f : ℕ → ℕ} (W : Equiv.Perm (Fin n)) (hf : ∀ p < n, f p = permFun W p)
    {i : ℕ} (hi : i < n) : ∀ k : ℕ, f^[k] i = (permFun W)^[k] i := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    apply hf
    rw [iterate_permFun W hi]
    exact ((W ^ k) ⟨i, hi⟩).2

theorem three_dvd_orderOf_of_period {f : ℕ → ℕ} (W : Equiv.Perm (Fin n))
    (hf : ∀ p < n, f p = permFun W p) {i fuel : ℕ} (hi : i < n) {ℓ : ℕ}
    (h : period f i fuel = ℓ) (hℓ : 0 < ℓ) (h3 : ℓ % 3 = 0) : 3 ∣ orderOf W := by
  obtain ⟨h1, hmin⟩ := period_spec h hℓ
  have hag := iterate_eq_of_agree W hf hi
  have hordo : (permFun W)^[orderOf W] i = i := by
    rw [iterate_permFun W hi, pow_orderOf_eq_one]
    rfl
  have hdvd : ℓ ∣ orderOf W :=
    dvd_of_period hℓ (by rw [← hag]; exact h1) (fun j hj hjl => by rw [← hag]; exact hmin j hj hjl)
      hordo
  exact (Nat.dvd_of_mod_eq_zero h3).trans hdvd

@[expose] def upow (u : Array ℕ) : ℕ → ℕ → ℕ
  | 0, p => p
  | 1, p => u[p]!
  | _, p => u[u[p]!]!

@[expose] def yconj (u y : Array ℕ) (k p : ℕ) : ℕ := upow u k (y[upow u ((3 - k) % 3) p]!)

@[expose] def wordPt (u y : Array ℕ) : List ℕ → ℕ → ℕ
  | [], p => p
  | a :: w, p => yconj u y a (wordPt u y w p)

@[expose] def wordLetters : ℕ → List ℕ
  | 0 => [0, 1]
  | 1 => [0, 0, 1]
  | 2 => [0, 1, 2]
  | _ => [0, 2, 1]

theorem wordLetters_lt (wc : ℕ) : ∀ a ∈ wordLetters wc, a < 3 := by
  intro a ha
  unfold wordLetters at ha
  split at ha <;> simp at ha <;> omega

@[expose] def pairWitOK (n : ℕ) (u y : Array ℕ) (wc p fuel : ℕ) : Bool :=
  decide (p < n) && decide (0 < period (wordPt u y (wordLetters wc)) p fuel) &&
    decide (period (wordPt u y (wordLetters wc)) p fuel % 3 = 0)

@[expose] def selfWitOK (n : ℕ) (y : Array ℕ) (p fuel : ℕ) : Bool :=
  decide (p < n) && decide (0 < period (fun q => y[q]!) p fuel) &&
    decide (period (fun q => y[q]!) p fuel % 3 = 0)

@[expose] def yk (U Y : Equiv.Perm (Fin n)) (k : ℕ) : Equiv.Perm (Fin n) :=
  U ^ k * Y * (U ^ k)⁻¹

@[expose] def wordProd (U Y : Equiv.Perm (Fin n)) : List ℕ → Equiv.Perm (Fin n)
  | [] => 1
  | a :: w => yk U Y a * wordProd U Y w

theorem upow_eq {u : Array ℕ} {U : Equiv.Perm (Fin n)} (hu : Rep n u U) {k : ℕ} (hk : k < 3)
    {p : ℕ} (hp : p < n) : upow u k p = ((U ^ k) ⟨p, hp⟩ : ℕ) := by
  interval_cases k
  · rfl
  · simp only [upow, pow_one]
    exact hu.apply hp
  · have h1 : u[p]! = (U ⟨p, hp⟩ : ℕ) := hu.apply hp
    have h2 : u[(U ⟨p, hp⟩ : ℕ)]! = (U (U ⟨p, hp⟩) : ℕ) := hu.apply (U ⟨p, hp⟩).2
    simp only [upow, pow_two, Equiv.Perm.mul_apply]
    rw [h1]
    exact h2

theorem inv_pow_eq {U : Equiv.Perm (Fin n)} (hU3 : U ^ 3 = 1) {k : ℕ} (hk : k < 3) :
    (U ^ k)⁻¹ = U ^ ((3 - k) % 3) := by
  interval_cases k
  · simp
  · refine inv_eq_of_mul_eq_one_right ?_
    rw [pow_one, show (3 - 1) % 3 = 2 by norm_num, ← pow_succ']
    exact hU3
  · refine inv_eq_of_mul_eq_one_right ?_
    rw [show (3 - 2) % 3 = 1 by norm_num, ← pow_add]
    exact hU3

theorem yconj_eq {u y : Array ℕ} {U Y : Equiv.Perm (Fin n)} (hu : Rep n u U) (hy : Rep n y Y)
    (hU3 : U ^ 3 = 1) {k : ℕ} (hk : k < 3) {p : ℕ} (hp : p < n) :
    yconj u y k p = ((yk U Y k) ⟨p, hp⟩ : ℕ) := by
  have hk' : (3 - k) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have h1 := upow_eq hu hk' hp
  set q : Fin n := (U ^ ((3 - k) % 3)) ⟨p, hp⟩ with hq
  have h2 : y[upow u ((3 - k) % 3) p]! = (Y q : ℕ) := by
    rw [h1]
    exact hy.apply q.2
  have h3 := upow_eq hu hk (Y q).2
  unfold yconj
  rw [h2, h3]
  simp only [yk, Equiv.Perm.mul_apply, inv_pow_eq hU3 hk]
  rfl

theorem wordPt_eq {u y : Array ℕ} {U Y : Equiv.Perm (Fin n)} (hu : Rep n u U) (hy : Rep n y Y)
    (hU3 : U ^ 3 = 1) {w : List ℕ} (hw : ∀ a ∈ w, a < 3) {p : ℕ} (hp : p < n) :
    wordPt u y w p = ((wordProd U Y w) ⟨p, hp⟩ : ℕ) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ih' := ih (fun b hb => hw b (List.mem_cons_of_mem a hb))
    have hlt : wordPt u y w p < n := by
      rw [ih']
      exact ((wordProd U Y w) ⟨p, hp⟩).2
    have e1 := yconj_eq hu hy hU3 (hw a List.mem_cons_self) hlt
    have e2 : (⟨wordPt u y w p, hlt⟩ : Fin n) = (wordProd U Y w) ⟨p, hp⟩ := Fin.ext ih'
    simp only [wordPt, wordProd]
    rw [e1, e2]
    rfl

theorem three_dvd_orderOf_of_selfWitOK {y : Array ℕ} {Y : Equiv.Perm (Fin n)} (hy : Rep n y Y)
    {p fuel : ℕ} (h : selfWitOK n y p fuel = true) : 3 ∣ orderOf Y := by
  simp only [selfWitOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp, hpos⟩, hmod⟩ := h
  refine three_dvd_orderOf_of_period Y (f := fun q => y[q]!) (fun q hq => ?_) hp rfl hpos hmod
  rw [permFun, dite_eq_left hq]
  exact hy.apply hq

theorem three_dvd_orderOf_wordProd {u y : Array ℕ} {U Y : Equiv.Perm (Fin n)} (hu : Rep n u U)
    (hy : Rep n y Y) (hU3 : U ^ 3 = 1) {wc p fuel : ℕ} (h : pairWitOK n u y wc p fuel = true) :
    3 ∣ orderOf (wordProd U Y (wordLetters wc)) := by
  simp only [pairWitOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp, hpos⟩, hmod⟩ := h
  refine three_dvd_orderOf_of_period (wordProd U Y (wordLetters wc))
    (f := wordPt u y (wordLetters wc)) (fun q hq => ?_) hp rfl hpos hmod
  rw [wordPt_eq hu hy hU3 (wordLetters_lt wc) hq, permFun, dite_eq_left hq]

theorem wordProd_mem {U Y : Equiv.Perm (Fin n)} {D : Subgroup (Equiv.Perm (Fin n))} (hY : Y ∈ D)
    (hU : U ∈ Subgroup.normalizer (D : Set (Equiv.Perm (Fin n)))) (w : List ℕ) :
    wordProd U Y w ∈ D := by
  induction w with
  | nil => exact D.one_mem
  | cons a w ih =>
    exact D.mul_mem ((Subgroup.mem_normalizer_iff.mp (pow_mem hU a) Y).mp hY) ih

@[expose] def uFlag (n : ℕ) (x u : Array ℕ) : Bool :=
  !(eqA n u (idA n)) && eqA n (powArr n u 3) (idA n) && !(eqA n u x) &&
    !(eqA n u (powArr n x 2))

@[expose] def yFlag (n fuel : ℕ) (y : Array ℕ) (sp : ℕ) : Bool :=
  !(eqA n y (idA n)) && !(selfWitOK n y sp fuel)

@[expose] def flagRanks (fl : Array Bool) : Array ℕ :=
  (fl.foldl (fun (acc : Array ℕ × ℕ) b => (acc.1.push acc.2, if b then acc.2 + 1 else acc.2))
    (#[], 0)).1

@[expose] def flagCount (fl : Array Bool) : ℕ :=
  fl.foldl (fun acc b => if b then acc + 1 else acc) 0

@[expose] def localOK (n fuel : ℕ) (x : Array ℕ) (pts : Array (Array ℕ))
    (selfPt pairWit : Array ℕ) : Bool :=
  let uF : Array Bool := pts.map (uFlag n x)
  let yF : Array Bool :=
    Array.ofFn (n := pts.size) fun iy => yFlag n fuel pts[iy.val]! selfPt[iy.val]!
  let uR := flagRanks uF
  let yR := flagRanks yF
  let ny := flagCount yF
  allLt pts.size fun iu => !uF[iu]! || allLt pts.size fun iy => !yF[iy]! ||
    pairWitOK n pts[iu]! pts[iy]! (pairWit[uR[iu]! * ny + yR[iy]!]! % 4)
      (pairWit[uR[iu]! * ny + yR[iy]!]! / 4) fuel

theorem localOK_spec {fuel : ℕ} {x : Array ℕ} {pts : Array (Array ℕ)} {selfPt pairWit : Array ℕ}
    (h : localOK n fuel x pts selfPt pairWit = true) {iu iy : ℕ} (hiu : iu < pts.size)
    (hiy : iy < pts.size) (hu : uFlag n x pts[iu]! = true)
    (hy : yFlag n fuel pts[iy]! selfPt[iy]! = true) :
    ∃ wc p, pairWitOK n pts[iu]! pts[iy]! wc p fuel = true := by
  unfold localOK at h
  dsimp only at h
  have h1 := allLt_spec h hiu
  have hF : (pts.map (uFlag n x))[iu]! = true := by
    rw [getElem!_pos _ iu (by simpa using hiu), Array.getElem_map, ← getElem!_pos pts iu hiu]
    exact hu
  rw [hF, Bool.not_true, Bool.false_or] at h1
  have h2 := allLt_spec h1 hiy
  have hG : (Array.ofFn (n := pts.size) fun iy => yFlag n fuel pts[iy.val]! selfPt[iy.val]!)[iy]!
      = true := by
    rw [getElem!_pos _ iy (by simpa using hiy), Array.getElem_ofFn]
    exact hy
  rw [hG, Bool.not_true, Bool.false_or] at h2
  exact ⟨_, _, h2⟩

theorem eq_bot_of_localOK {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ q ∈ ps, q < n) (hE : enumOK n gs ps c = true) {x : Array ℕ}
    {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {fuel : ℕ} {selfPt pairWit : Array ℕ}
    (hloc : localOK n fuel x c.pts selfPt pairWit = true) {U : Equiv.Perm (Fin n)}
    (hUC : U ∈ Subgroup.closure (permsA n gs)) (hU3 : U ^ 3 = 1) (hU1 : U ≠ 1) (hUX : U ≠ X)
    (hUX2 : U ≠ X ^ 2) {D : Subgroup (Equiv.Perm (Fin n))}
    (hDC : D ≤ Subgroup.closure (permsA n gs)) (hD3 : ¬ 3 ∣ Nat.card D)
    (hUD : U ∈ Subgroup.normalizer (D : Set (Equiv.Perm (Fin n)))) : D = ⊥ := by
  by_contra hD
  obtain ⟨Y, hY1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD
  have hY1' : (Y : Equiv.Perm (Fin n)) ≠ 1 := fun h => hY1 (Subtype.ext h)
  obtain ⟨iy, hiy, hYrep⟩ := enumOK_exists_rep hps hE (hDC Y.2)
  obtain ⟨iu, hiu, hUrep⟩ := enumOK_exists_rep hps hE hUC
  have huF : uFlag n x c.pts[iu]! = true := by
    have e1 : eqA n c.pts[iu]! (idA n) = false := by
      rw [Bool.eq_false_iff]
      exact fun h => hU1 ((eqA_iff hUrep rep_idA).1 h)
    have e2 : eqA n (powArr n c.pts[iu]! 3) (idA n) = true :=
      (eqA_iff (rep_powArr hUrep 3) rep_idA).2 hU3
    have e3 : eqA n c.pts[iu]! x = false := by
      rw [Bool.eq_false_iff]
      exact fun h => hUX ((eqA_iff hUrep hx).1 h)
    have e4 : eqA n c.pts[iu]! (powArr n x 2) = false := by
      rw [Bool.eq_false_iff]
      exact fun h => hUX2 ((eqA_iff hUrep (rep_powArr hx 2)).1 h)
    simp [uFlag, e1, e2, e3, e4]
  have hyF : yFlag n fuel c.pts[iy]! selfPt[iy]! = true := by
    have e1 : eqA n c.pts[iy]! (idA n) = false := by
      rw [Bool.eq_false_iff]
      exact fun h => hY1' ((eqA_iff hYrep rep_idA).1 h)
    have e2 : selfWitOK n c.pts[iy]! selfPt[iy]! fuel = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hD3 ((three_dvd_orderOf_of_selfWitOK hYrep h).trans
        (Subgroup.orderOf_dvd_natCard D Y.2))
    simp [yFlag, e1, e2]
  obtain ⟨wc, p, hw⟩ := localOK_spec hloc hiu hiy huF hyF
  have h3 := three_dvd_orderOf_wordProd hUrep hYrep hU3 hw
  exact hD3 (h3.trans (Subgroup.orderOf_dvd_natCard D (wordProd_mem Y.2 hUD _)))

end CFSG.RankThree.PartTwo.Sec4.Item434D42
