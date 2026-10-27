module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeyl
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusFinite
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusOrbitEps
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeylEx
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusSimpleFix
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusFormal
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusOuterBound

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

open CFSG.StandardType in
private lemma w135c2_omfMOrb_spIsSign_ite_two {m : ℕ} (a b : Fin m) {e e' : ℤ}
    (he : e = 1 ∨ e = -1) (he' : e' = 1 ∨ e' = -1) :
    SpIsSign (fun x : Fin m => if x = a then e else if x = b then e' else 1) := by
  intro x
  change (if x = a then e else if x = b then e' else 1) = 1 ∨
    (if x = a then e else if x = b then e' else 1) = -1
  by_cases hx : x = a
  · rw [if_pos hx]; exact he
  · rw [if_neg hx]
    by_cases hx' : x = b
    · rw [if_pos hx']; exact he'
    · rw [if_neg hx']; exact Or.inl rfl

open CFSG.StandardType in
private lemma w135c2_omfMOrb_spIsSign_ite_three {m : ℕ} (a b d : Fin m) {e e' e'' : ℤ}
    (he : e = 1 ∨ e = -1) (he' : e' = 1 ∨ e' = -1) (he'' : e'' = 1 ∨ e'' = -1) :
    SpIsSign (fun x : Fin m => if x = a then e else if x = b then e'
      else if x = d then e'' else 1) := by
  intro x
  change (if x = a then e else if x = b then e' else if x = d then e'' else 1) = 1 ∨
    (if x = a then e else if x = b then e' else if x = d then e'' else 1) = -1
  by_cases hx : x = a
  · rw [if_pos hx]; exact he
  · rw [if_neg hx]
    by_cases hx' : x = b
    · rw [if_pos hx']; exact he'
    · rw [if_neg hx']
      by_cases hx'' : x = d
      · rw [if_pos hx'']; exact he''
      · rw [if_neg hx'']; exact Or.inl rfl

private lemma w135c2_omfMOrb_swap_eval {l : ℕ} (a last c : Fin l) (s v : Fin l → ℤ)
    (h1 : c ≠ a) (h2 : c ≠ last) :
    omqSignedActZ (Equiv.swap a last) s v c = s c * v c := by
  rw [omqSignedActZ, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne h1 h2]

private lemma w135c2_omfMOrb_swap_eval_left {l : ℕ} (a last : Fin l) (s v : Fin l → ℤ) :
    omqSignedActZ (Equiv.swap a last) s v a = s last * v last := by
  rw [omqSignedActZ, Equiv.symm_swap, Equiv.swap_apply_left]

private lemma w135c2_omfMOrb_swap_eval_right {l : ℕ} (a last : Fin l) (s v : Fin l → ℤ) :
    omqSignedActZ (Equiv.swap a last) s v last = s a * v a := by
  rw [omqSignedActZ, Equiv.symm_swap, Equiv.swap_apply_right]
private lemma w135c2_omfMOrb_inj_of_vals_zp {l : ℕ} (u : Fin 7 → Fin l → ℤ) (z p : Fin l)
    (huz : ∀ i, u i z = ![0, 0, 1, -1, 1, -1, -1] i)
    (hup : ∀ i, u i p = ![1, -1, 0, 0, 1, 1, -1] i) : Function.Injective u := by
  intro i i' h
  have hz := congrFun h z
  have hp := congrFun h p
  fin_cases i <;> fin_cases i' <;> simp_all

private lemma w135c2_omfMOrb_inj_of_vals_zpw {l : ℕ} (u : Fin 7 → Fin l → ℤ) (z p w : Fin l)
    (huz : ∀ i, u i z = ![1, -1, 0, 0, 1, -1, 0] i)
    (hup : ∀ i, u i p = ![0, 0, 1, -1, 0, 0, 1] i)
    (huw : ∀ i, u i w = ![0, 0, 0, 0, 1, 1, 1] i) : Function.Injective u := by
  intro i i' h
  have hz := congrFun h z
  have hp := congrFun h p
  have hw := congrFun h w
  fin_cases i <;> fin_cases i' <;> simp_all

private lemma w135c2_omfMOrb_inj_of_vals_zpq {l : ℕ} (u : Fin 7 → Fin l → ℤ) (z p q : Fin l)
    (huz : ∀ i, u i z = ![1, 1, 1, 1, -1, -1, -1] i)
    (hup : ∀ i, u i p = ![1, 1, -1, -1, 1, 1, -1] i)
    (huq : ∀ i, u i q = ![1, -1, 1, -1, 1, -1, 1] i) : Function.Injective u := by
  intro i i' h
  have hz := congrFun h z
  have hp := congrFun h p
  have hq := congrFun h q
  fin_cases i <;> fin_cases i' <;> simp_all

private lemma w135c2_omfMOrb_move_of_last {l : ℕ} (u : Fin 7 → Fin l → ℤ) (last : Fin l)
    (s : Fin l → ℤ) (hul : ∀ i, u i last = 1) (hs : s last = -1) :
    ∀ i i', u i ≠ omqSignedActZ 1 s (u i') := by
  intro i i' h
  have hval := congrFun h last
  change u i last = s last * u i' last at hval
  rw [hul i, hul i', hs] at hval
  norm_num at hval

private lemma w135c2_omfMOrb_move_one {l : ℕ} (u : Fin 7 → Fin l → ℤ) (w last : Fin l)
    (s : Fin l → ℤ) (huw : ∀ i, u i w = ![0, 0, 0, 0, 1, 1, 1] i)
    (hul : ∀ i, u i last = ![1, 1, 1, 1, 0, 0, 0] i) (hsw : s w = -1) (hsl : s last = -1) :
    ∀ i i', u i ≠ omqSignedActZ 1 s (u i') := by
  intro i i' h
  have hval := congrFun h last
  have hvalw := congrFun h w
  change u i last = s last * u i' last at hval
  change u i w = s w * u i' w at hvalw
  fin_cases i <;> fin_cases i' <;> simp_all

private lemma w135c2_omfMOrb_weylAction_ofStdB {m : ℕ}
    (w : (coxeterMatrix (isFiniteType_cartanB m)).Group) (π : Equiv.Perm (Fin m))
    (s : Fin m → ℤ) (v : Fin m → ℤ) (hw : omqnfRealizes m w π s) :
    weylAction (isFiniteType_cartanB m) w (ofStdB m v) = ofStdB m (omqSignedActZ π s v) := by
  apply toStdB_injective m
  rw [hw (ofStdB m v), toStdB_ofStdB, toStdB_ofStdB]
  rfl

private lemma w135c2_omfMOrb_fix_weylAction {m : ℕ} {v : Fin m → ℤ} {t : Fin m}
    (h : omqSignedActZ (omqMinusSimple m t).1 (omqMinusSimple m t).2 v = v) :
    weylAction (isFiniteType_cartanB m)
      ((coxeterMatrix (isFiniteType_cartanB m)).toCoxeterSystem.simple t) (ofStdB m v)
      = ofStdB m v := by
  apply toStdB_injective m
  by_cases ht : t.val + 1 < m
  · have hr := omqnfRealizes_simple_of_lt ht (ofStdB m v)
    rw [hr]
    simp only [omqMinusSimple, dif_pos ht] at h
    rw [toStdB_ofStdB]
    funext b
    have h' := congrFun h b
    simpa [omqSignedActZ] using h'
  · have hr := omqnfRealizes_simple_of_not_lt ht (ofStdB m v)
    rw [hr]
    simp only [omqMinusSimple, dif_neg ht] at h
    rw [toStdB_ofStdB]
    funext b
    have h' := congrFun h b
    simpa [omqSignedActZ] using h'

private lemma w135c2_omfMOrb_inj_move_of_smul {m : ℕ} {α : Type*} [Monoid α]
    [MulAction α (Fin m → ℤ)]
    {u f : Fin 4 → Fin m → ℤ} {b c : Fin 4 → α} {v' : Fin m → ℤ}
    (hb : ∀ i, b i • v' = ofStdB m (u i)) (hc : ∀ i, c i • v' = ofStdB m (f i))
    (hinj : Function.Injective u) (hmove : ∀ i j, u i ≠ f j) :
    (∀ i j, i ≠ j → b i • v' ≠ b j • v') ∧ (∀ i j, b i • v' ≠ c j • v') := by
  refine ⟨?_, ?_⟩
  · intro i j hij h
    rw [hb i, hb j] at h
    exact hij (hinj (by
      have := congrArg (toStdB m) h
      simpa [toStdB_ofStdB] using this))
  · intro i j h
    rw [hb i, hc j] at h
    exact hmove i j (by
      have := congrArg (toStdB m) h
      simpa [toStdB_ofStdB] using this)

open CFSG.StandardType in
private def w135c2_omfMOrb_geTwoPts {l : ℕ} (z p q last : Fin l) (v : Fin l → ℤ) :
    Fin 7 → Fin l → ℤ :=
  ![omqSignedActZ (Equiv.swap z last) 1 v,
    omqSignedActZ (Equiv.swap z last) (spSgn p) v,
    omqSignedActZ (Equiv.swap p last) 1 v,
    omqSignedActZ (Equiv.swap p last) (spSgn z) v,
    omqSignedActZ (Equiv.swap q last) 1 v,
    omqSignedActZ (Equiv.swap q last) (spSgn z) v,
    omqSignedActZ (Equiv.swap q last)
      (fun b : Fin l => if b = z then -1 else if b = p then -1 else 1) v]

open CFSG.StandardType in
private lemma w135c2_omfMOrb_geTwo_val_z {l : ℕ} {z p q last : Fin l} {v : Fin l → ℤ}
    (hzp : z ≠ p) (hzq : z ≠ q) (hzl : z ≠ last) (hpl : p ≠ last)
    (hv_z : v z = 1) (hv_l : v last = 0) :
    ∀ i, w135c2_omfMOrb_geTwoPts z p q last v i z = ![0, 0, 1, -1, 1, -1, -1] i := by
  intro i
  fin_cases i
  · change omqSignedActZ (Equiv.swap z last) (1 : Fin l → ℤ) v z = 0
    rw [w135c2_omfMOrb_swap_eval_left z last 1 v, Pi.one_apply, one_mul, hv_l]
  · change omqSignedActZ (Equiv.swap z last) (spSgn p) v z = 0
    rw [w135c2_omfMOrb_swap_eval_left z last (spSgn p) v, spSgn,
      if_neg (Ne.symm hpl), one_mul, hv_l]
  · change omqSignedActZ (Equiv.swap p last) (1 : Fin l → ℤ) v z = 1
    rw [w135c2_omfMOrb_swap_eval p last z 1 v hzp hzl, Pi.one_apply, one_mul, hv_z]
  · change omqSignedActZ (Equiv.swap p last) (spSgn z) v z = -1
    rw [w135c2_omfMOrb_swap_eval p last z (spSgn z) v hzp hzl, spSgn, if_pos rfl,
      hv_z, mul_one]
  · change omqSignedActZ (Equiv.swap q last) (1 : Fin l → ℤ) v z = 1
    rw [w135c2_omfMOrb_swap_eval q last z 1 v hzq hzl, Pi.one_apply, one_mul, hv_z]
  · change omqSignedActZ (Equiv.swap q last) (spSgn z) v z = -1
    rw [w135c2_omfMOrb_swap_eval q last z (spSgn z) v hzq hzl, spSgn, if_pos rfl,
      hv_z, mul_one]
  · change omqSignedActZ (Equiv.swap q last)
      (fun b : Fin l => if b = z then -1 else if b = p then -1 else 1) v z = -1
    rw [w135c2_omfMOrb_swap_eval q last z
      (fun b : Fin l => if b = z then -1 else if b = p then -1 else 1) v hzq hzl,
      if_pos rfl, hv_z, mul_one]

open CFSG.StandardType in
private lemma w135c2_omfMOrb_geTwo_val_p {l : ℕ} {z p q last : Fin l} {v : Fin l → ℤ}
    (hzp : z ≠ p) (hpq : p ≠ q) (hzl : z ≠ last) (hpl : p ≠ last)
    (hv_p : v p = 1) (hv_l : v last = 0) :
    ∀ i, w135c2_omfMOrb_geTwoPts z p q last v i p = ![1, -1, 0, 0, 1, 1, -1] i := by
  intro i
  fin_cases i
  · change omqSignedActZ (Equiv.swap z last) (1 : Fin l → ℤ) v p = 1
    rw [w135c2_omfMOrb_swap_eval z last p 1 v (Ne.symm hzp) hpl, Pi.one_apply,
      one_mul, hv_p]
  · change omqSignedActZ (Equiv.swap z last) (spSgn p) v p = -1
    rw [w135c2_omfMOrb_swap_eval z last p (spSgn p) v (Ne.symm hzp) hpl, spSgn,
      if_pos rfl, hv_p, mul_one]
  · change omqSignedActZ (Equiv.swap p last) (1 : Fin l → ℤ) v p = 0
    rw [w135c2_omfMOrb_swap_eval_left p last 1 v, Pi.one_apply, one_mul, hv_l]
  · change omqSignedActZ (Equiv.swap p last) (spSgn z) v p = 0
    rw [w135c2_omfMOrb_swap_eval_left p last (spSgn z) v, spSgn,
      if_neg (Ne.symm hzl), one_mul, hv_l]
  · change omqSignedActZ (Equiv.swap q last) (1 : Fin l → ℤ) v p = 1
    rw [w135c2_omfMOrb_swap_eval q last p 1 v hpq hpl, Pi.one_apply, one_mul, hv_p]
  · change omqSignedActZ (Equiv.swap q last) (spSgn z) v p = 1
    rw [w135c2_omfMOrb_swap_eval q last p (spSgn z) v hpq hpl, spSgn,
      if_neg (Ne.symm hzp), one_mul, hv_p]
  · change omqSignedActZ (Equiv.swap q last)
      (fun b : Fin l => if b = z then -1 else if b = p then -1 else 1) v p = -1
    rw [w135c2_omfMOrb_swap_eval q last p
      (fun b : Fin l => if b = z then -1 else if b = p then -1 else 1) v hpq hpl,
      if_neg (Ne.symm hzp), if_pos rfl, hv_p, mul_one]

open CFSG.StandardType in
private lemma w135c2_omfMOrb_geTwo_val_last {l : ℕ} {z p q last : Fin l} {v : Fin l → ℤ}
    (hzp : z ≠ p) (hzq : z ≠ q) (hpq : p ≠ q)
    (hv_z : v z = 1) (hv_p : v p = 1) (hv_q : v q = 1) :
    ∀ i, w135c2_omfMOrb_geTwoPts z p q last v i last = 1 := by
  intro i
  fin_cases i
  · change omqSignedActZ (Equiv.swap z last) (1 : Fin l → ℤ) v last = 1
    rw [w135c2_omfMOrb_swap_eval_right z last 1 v, Pi.one_apply, one_mul, hv_z]
  · change omqSignedActZ (Equiv.swap z last) (spSgn p) v last = 1
    rw [w135c2_omfMOrb_swap_eval_right z last (spSgn p) v, spSgn, if_neg hzp,
      one_mul, hv_z]
  · change omqSignedActZ (Equiv.swap p last) (1 : Fin l → ℤ) v last = 1
    rw [w135c2_omfMOrb_swap_eval_right p last 1 v, Pi.one_apply, one_mul, hv_p]
  · change omqSignedActZ (Equiv.swap p last) (spSgn z) v last = 1
    rw [w135c2_omfMOrb_swap_eval_right p last (spSgn z) v, spSgn,
      if_neg (Ne.symm hzp), one_mul, hv_p]
  · change omqSignedActZ (Equiv.swap q last) (1 : Fin l → ℤ) v last = 1
    rw [w135c2_omfMOrb_swap_eval_right q last 1 v, Pi.one_apply, one_mul, hv_q]
  · change omqSignedActZ (Equiv.swap q last) (spSgn z) v last = 1
    rw [w135c2_omfMOrb_swap_eval_right q last (spSgn z) v, spSgn,
      if_neg (Ne.symm hzq), one_mul, hv_q]
  · change omqSignedActZ (Equiv.swap q last)
      (fun b : Fin l => if b = z then -1 else if b = p then -1 else 1) v last = 1
    rw [w135c2_omfMOrb_swap_eval_right q last
      (fun b : Fin l => if b = z then -1 else if b = p then -1 else 1) v,
      if_neg (Ne.symm hzq), if_neg (Ne.symm hpq), one_mul, hv_q]

open CFSG.StandardType in
private lemma w135c2_omfMOrb_geTwo_horb {l : ℕ} (z p q last : Fin l) (v : Fin l → ℤ) :
    ∀ i, OmqFormalInOrbit v (w135c2_omfMOrb_geTwoPts z p q last v i) := by
  intro i
  fin_cases i
  · exact ⟨Equiv.swap z last, 1, spIsSign_one, rfl⟩
  · exact ⟨Equiv.swap z last, spSgn p, spIsSign_spSgn p, rfl⟩
  · exact ⟨Equiv.swap p last, 1, spIsSign_one, rfl⟩
  · exact ⟨Equiv.swap p last, spSgn z, spIsSign_spSgn z, rfl⟩
  · exact ⟨Equiv.swap q last, 1, spIsSign_one, rfl⟩
  · exact ⟨Equiv.swap q last, spSgn z, spIsSign_spSgn z, rfl⟩
  · exact ⟨Equiv.swap q last, (fun b : Fin l => if b = z then -1 else if b = p then -1 else 1),
      w135c2_omfMOrb_spIsSign_ite_two z p (Or.inr rfl) (Or.inr rfl), rfl⟩

open CFSG.StandardType in
private theorem w135c2_omfMOrb_seven_flag_ge_two {n : ℕ} (hn : 5 ≤ n) {j : ℕ} (hj1 : 2 ≤ j)
    (hj2 : j + 2 ≤ n - 1) :
    ∃ u : Fin 7 → Fin (n - 1) → ℤ, Function.Injective u ∧
      (∀ i, OmqFormalInOrbit (omqMinusFlag (n - 1) j) (u i)) ∧
      ∀ i i', u i ≠ omqSignedActZ 1
        (fun a : Fin (n - 1) => if n ≤ a.val + 3 then -1 else 1) (u i') := by
  let z : Fin (n - 1) := ⟨0, by omega⟩
  let p : Fin (n - 1) := ⟨1, by omega⟩
  let q : Fin (n - 1) := ⟨2, by omega⟩
  let last : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hzp : z ≠ p := by intro h; simp [z, p] at h
  have hzq : z ≠ q := by intro h; simp [z, q] at h
  have hpq : p ≠ q := by intro h; simp [p, q] at h
  have hzl : z ≠ last := by intro h; simp [z, last] at h; omega
  have hpl : p ≠ last := by intro h; simp [p, last] at h; omega
  have hql : q ≠ last := by intro h; simp [q, last] at h; omega
  let v : Fin (n - 1) → ℤ := omqMinusFlag (n - 1) j
  have hv_z : v z = 1 := by simp only [v, omqMinusFlag, z]; rw [if_pos (by omega)]
  have hv_p : v p = 1 := by simp only [v, omqMinusFlag, p]; rw [if_pos (by omega)]
  have hv_q : v q = 1 := by simp only [v, omqMinusFlag, q]; rw [if_pos (by omega)]
  have hv_l : v last = 0 := by simp only [v, omqMinusFlag, last]; rw [if_neg (by omega)]
  have hs2l : (fun a : Fin (n - 1) => if n ≤ a.val + 3 then -1 else 1) last = -1 := by
    simp only [last]; rw [if_pos]; omega
  exact ⟨w135c2_omfMOrb_geTwoPts z p q last v,
    w135c2_omfMOrb_inj_of_vals_zp _ z p
      (w135c2_omfMOrb_geTwo_val_z hzp hzq hzl hpl hv_z hv_l)
      (w135c2_omfMOrb_geTwo_val_p hzp hpq hzl hpl hv_p hv_l),
    w135c2_omfMOrb_geTwo_horb z p q last v,
    w135c2_omfMOrb_move_of_last _ last _
      (w135c2_omfMOrb_geTwo_val_last hzp hzq hpq hv_z hv_p hv_q) hs2l⟩

open CFSG.StandardType in
private def w135c2_omfMOrb_onePts {l : ℕ} (z p w last : Fin l) (v : Fin l → ℤ) :
    Fin 7 → Fin l → ℤ :=
  ![omqSignedActZ (Equiv.swap p last) 1 v,
    omqSignedActZ (Equiv.swap p last) (spSgn z) v,
    omqSignedActZ (Equiv.swap z last) 1 v,
    omqSignedActZ (Equiv.swap z last) (spSgn p) v,
    omqSignedActZ (Equiv.swap p w) 1 v,
    omqSignedActZ (Equiv.swap p w) (spSgn z) v,
    omqSignedActZ (Equiv.swap z w) 1 v]

open CFSG.StandardType in
private lemma w135c2_omfMOrb_one_val_z {l : ℕ} {z p w last : Fin l} {v : Fin l → ℤ}
    (hzp : z ≠ p) (hzl : z ≠ last) (hzw : z ≠ w) (hpl : p ≠ last)
    (hv_z : v z = 1) (hv_w : v w = 0) (hv_l : v last = 0) :
    ∀ i, w135c2_omfMOrb_onePts z p w last v i z = ![1, -1, 0, 0, 1, -1, 0] i := by
  intro i
  fin_cases i
  · change omqSignedActZ (Equiv.swap p last) (1 : Fin l → ℤ) v z = 1
    rw [w135c2_omfMOrb_swap_eval p last z 1 v hzp hzl, Pi.one_apply,
      one_mul, hv_z]
  · change omqSignedActZ (Equiv.swap p last) (spSgn z) v z = -1
    rw [w135c2_omfMOrb_swap_eval p last z (spSgn z) v hzp hzl, spSgn,
      if_pos rfl, hv_z, mul_one]
  · change omqSignedActZ (Equiv.swap z last) (1 : Fin l → ℤ) v z = 0
    rw [w135c2_omfMOrb_swap_eval_left z last 1 v, Pi.one_apply, one_mul, hv_l]
  · change omqSignedActZ (Equiv.swap z last) (spSgn p) v z = 0
    rw [w135c2_omfMOrb_swap_eval_left z last (spSgn p) v, spSgn,
      if_neg (Ne.symm hpl), one_mul, hv_l]
  · change omqSignedActZ (Equiv.swap p w) (1 : Fin l → ℤ) v z = 1
    rw [w135c2_omfMOrb_swap_eval p w z 1 v hzp hzw, Pi.one_apply, one_mul, hv_z]
  · change omqSignedActZ (Equiv.swap p w) (spSgn z) v z = -1
    rw [w135c2_omfMOrb_swap_eval p w z (spSgn z) v hzp hzw, spSgn, if_pos rfl,
      hv_z, mul_one]
  · change omqSignedActZ (Equiv.swap z w) (1 : Fin l → ℤ) v z = 0
    rw [w135c2_omfMOrb_swap_eval_left z w 1 v, Pi.one_apply, one_mul, hv_w]

open CFSG.StandardType in
private lemma w135c2_omfMOrb_one_val_p {l : ℕ} {z p w last : Fin l} {v : Fin l → ℤ}
    (hzp : z ≠ p) (hzw : z ≠ w) (hzl : z ≠ last) (hpl : p ≠ last) (hpw : p ≠ w)
    (hv_w : v w = 0) (hv_p : v p = 1) (hv_l : v last = 0) :
    ∀ i, w135c2_omfMOrb_onePts z p w last v i p = ![0, 0, 1, -1, 0, 0, 1] i := by
  intro i
  fin_cases i
  · change omqSignedActZ (Equiv.swap p last) (1 : Fin l → ℤ) v p = 0
    rw [w135c2_omfMOrb_swap_eval_left p last 1 v, Pi.one_apply, one_mul, hv_l]
  · change omqSignedActZ (Equiv.swap p last) (spSgn z) v p = 0
    rw [w135c2_omfMOrb_swap_eval_left p last (spSgn z) v, spSgn,
      if_neg (Ne.symm hzl), one_mul, hv_l]
  · change omqSignedActZ (Equiv.swap z last) (1 : Fin l → ℤ) v p = 1
    rw [w135c2_omfMOrb_swap_eval z last p 1 v (Ne.symm hzp) hpl, Pi.one_apply,
      one_mul, hv_p]
  · change omqSignedActZ (Equiv.swap z last) (spSgn p) v p = -1
    rw [w135c2_omfMOrb_swap_eval z last p (spSgn p) v (Ne.symm hzp) hpl, spSgn,
      if_pos rfl, hv_p, mul_one]
  · change omqSignedActZ (Equiv.swap p w) (1 : Fin l → ℤ) v p = 0
    rw [w135c2_omfMOrb_swap_eval_left p w 1 v, Pi.one_apply, one_mul, hv_w]
  · change omqSignedActZ (Equiv.swap p w) (spSgn z) v p = 0
    rw [w135c2_omfMOrb_swap_eval_left p w (spSgn z) v, spSgn,
      if_neg (Ne.symm hzw), one_mul, hv_w]
  · change omqSignedActZ (Equiv.swap z w) (1 : Fin l → ℤ) v p = 1
    rw [w135c2_omfMOrb_swap_eval z w p 1 v (Ne.symm hzp) hpw, Pi.one_apply,
      one_mul, hv_p]

open CFSG.StandardType in
private lemma w135c2_omfMOrb_one_val_w {l : ℕ} {z p w last : Fin l} {v : Fin l → ℤ}
    (hzp : z ≠ p) (hzw : z ≠ w) (hpw : p ≠ w) (hwl : w ≠ last)
    (hv_w : v w = 0) (hv_p : v p = 1) (hv_z : v z = 1) :
    ∀ i, w135c2_omfMOrb_onePts z p w last v i w = ![0, 0, 0, 0, 1, 1, 1] i := by
  intro i
  fin_cases i
  · change omqSignedActZ (Equiv.swap p last) (1 : Fin l → ℤ) v w = 0
    rw [w135c2_omfMOrb_swap_eval p last w 1 v (Ne.symm hpw) hwl, Pi.one_apply,
      one_mul, hv_w]
  · change omqSignedActZ (Equiv.swap p last) (spSgn z) v w = 0
    rw [w135c2_omfMOrb_swap_eval p last w (spSgn z) v (Ne.symm hpw) hwl, spSgn,
      if_neg (Ne.symm hzw), one_mul, hv_w]
  · change omqSignedActZ (Equiv.swap z last) (1 : Fin l → ℤ) v w = 0
    rw [w135c2_omfMOrb_swap_eval z last w 1 v (Ne.symm hzw) hwl, Pi.one_apply,
      one_mul, hv_w]
  · change omqSignedActZ (Equiv.swap z last) (spSgn p) v w = 0
    rw [w135c2_omfMOrb_swap_eval z last w (spSgn p) v (Ne.symm hzw) hwl, spSgn,
      if_neg (Ne.symm hpw), one_mul, hv_w]
  · change omqSignedActZ (Equiv.swap p w) (1 : Fin l → ℤ) v w = 1
    rw [w135c2_omfMOrb_swap_eval_right p w 1 v, Pi.one_apply, one_mul, hv_p]
  · change omqSignedActZ (Equiv.swap p w) (spSgn z) v w = 1
    rw [w135c2_omfMOrb_swap_eval_right p w (spSgn z) v, spSgn,
      if_neg (Ne.symm hzp), one_mul, hv_p]
  · change omqSignedActZ (Equiv.swap z w) (1 : Fin l → ℤ) v w = 1
    rw [w135c2_omfMOrb_swap_eval_right z w 1 v, Pi.one_apply, one_mul, hv_z]

open CFSG.StandardType in
private lemma w135c2_omfMOrb_one_val_last {l : ℕ} {z p w last : Fin l} {v : Fin l → ℤ}
    (hzp : z ≠ p) (hzl : z ≠ last) (hpl : p ≠ last) (hwl : w ≠ last)
    (hv_p : v p = 1) (hv_z : v z = 1) (hv_l : v last = 0) :
    ∀ i, w135c2_omfMOrb_onePts z p w last v i last = ![1, 1, 1, 1, 0, 0, 0] i := by
  intro i
  fin_cases i
  · change omqSignedActZ (Equiv.swap p last) (1 : Fin l → ℤ) v last = 1
    rw [w135c2_omfMOrb_swap_eval_right p last 1 v, Pi.one_apply, one_mul, hv_p]
  · change omqSignedActZ (Equiv.swap p last) (spSgn z) v last = 1
    rw [w135c2_omfMOrb_swap_eval_right p last (spSgn z) v, spSgn,
      if_neg (Ne.symm hzp), one_mul, hv_p]
  · change omqSignedActZ (Equiv.swap z last) (1 : Fin l → ℤ) v last = 1
    rw [w135c2_omfMOrb_swap_eval_right z last 1 v, Pi.one_apply, one_mul, hv_z]
  · change omqSignedActZ (Equiv.swap z last) (spSgn p) v last = 1
    rw [w135c2_omfMOrb_swap_eval_right z last (spSgn p) v, spSgn, if_neg hzp,
      one_mul, hv_z]
  · change omqSignedActZ (Equiv.swap p w) (1 : Fin l → ℤ) v last = 0
    rw [w135c2_omfMOrb_swap_eval p w last 1 v (Ne.symm hpl) (Ne.symm hwl), Pi.one_apply,
      one_mul, hv_l]
  · change omqSignedActZ (Equiv.swap p w) (spSgn z) v last = 0
    rw [w135c2_omfMOrb_swap_eval p w last (spSgn z) v (Ne.symm hpl) (Ne.symm hwl), spSgn,
      if_neg (Ne.symm hzl), one_mul, hv_l]
  · change omqSignedActZ (Equiv.swap z w) (1 : Fin l → ℤ) v last = 0
    rw [w135c2_omfMOrb_swap_eval z w last 1 v (Ne.symm hzl) (Ne.symm hwl), Pi.one_apply,
      one_mul, hv_l]

open CFSG.StandardType in
private lemma w135c2_omfMOrb_one_horb {l : ℕ} (z p w last : Fin l) (v : Fin l → ℤ) :
    ∀ i, OmqFormalInOrbit v (w135c2_omfMOrb_onePts z p w last v i) := by
  intro i
  fin_cases i
  · exact ⟨Equiv.swap p last, 1, spIsSign_one, rfl⟩
  · exact ⟨Equiv.swap p last, spSgn z, spIsSign_spSgn z, rfl⟩
  · exact ⟨Equiv.swap z last, 1, spIsSign_one, rfl⟩
  · exact ⟨Equiv.swap z last, spSgn p, spIsSign_spSgn p, rfl⟩
  · exact ⟨Equiv.swap p w, 1, spIsSign_one, rfl⟩
  · exact ⟨Equiv.swap p w, spSgn z, spIsSign_spSgn z, rfl⟩
  · exact ⟨Equiv.swap z w, 1, spIsSign_one, rfl⟩

open CFSG.StandardType in
private theorem w135c2_omfMOrb_seven_flag_one {n : ℕ} (hn : 5 ≤ n) :
    ∃ u : Fin 7 → Fin (n - 1) → ℤ, Function.Injective u ∧
      (∀ i, OmqFormalInOrbit (omqMinusFlag (n - 1) 1) (u i)) ∧
      ∀ i i', u i ≠ omqSignedActZ 1
        (fun a : Fin (n - 1) => if n ≤ a.val + 3 then -1 else 1) (u i') := by
  let z : Fin (n - 1) := ⟨0, by omega⟩
  let p : Fin (n - 1) := ⟨1, by omega⟩
  let w : Fin (n - 1) := ⟨n - 3, by omega⟩
  let last : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hzp : z ≠ p := by intro h; simp [z, p] at h
  have hzw : z ≠ w := by intro h; simp [z, w] at h; omega
  have hzl : z ≠ last := by intro h; simp [z, last] at h; omega
  have hpw : p ≠ w := by intro h; simp [p, w] at h; omega
  have hpl : p ≠ last := by intro h; simp [p, last] at h; omega
  have hwl : w ≠ last := by intro h; simp [w, last] at h; omega
  let v : Fin (n - 1) → ℤ := omqMinusFlag (n - 1) 1
  have hv_z : v z = 1 := by simp only [v, omqMinusFlag, z]; rw [if_pos (by omega)]
  have hv_p : v p = 1 := by simp only [v, omqMinusFlag, p]; rw [if_pos (by omega)]
  have hv_w : v w = 0 := by simp only [v, omqMinusFlag, w]; rw [if_neg (by omega)]
  have hv_l : v last = 0 := by simp only [v, omqMinusFlag, last]; rw [if_neg (by omega)]
  have hs2l : (fun a : Fin (n - 1) => if n ≤ a.val + 3 then -1 else 1) last = -1 := by
    simp only [last]; rw [if_pos]; omega
  have hsw : (fun a : Fin (n - 1) => if n ≤ a.val + 3 then -1 else 1) w = -1 := by
    simp only [w]; rw [if_pos]; omega
  have huw := w135c2_omfMOrb_one_val_w hzp hzw hpw hwl hv_w hv_p hv_z
  exact ⟨w135c2_omfMOrb_onePts z p w last v,
    w135c2_omfMOrb_inj_of_vals_zpw _ z p w
      (w135c2_omfMOrb_one_val_z hzp hzl hzw hpl hv_z hv_w hv_l)
      (w135c2_omfMOrb_one_val_p hzp hzw hzl hpl hpw hv_w hv_p hv_l) huw,
    w135c2_omfMOrb_one_horb z p w last v,
    w135c2_omfMOrb_move_one _ w last _
      huw (w135c2_omfMOrb_one_val_last hzp hzl hpl hwl hv_p hv_z hv_l) hsw hs2l⟩

private def w135c2_omfMOrb_cubePts {l : ℕ} (z p q : Fin l) : Fin 7 → Fin l → ℤ :=
  fun i b => if b = z then (![1, 1, 1, 1, -1, -1, -1] : Fin 7 → ℤ) i
    else if b = p then (![1, 1, -1, -1, 1, 1, -1] : Fin 7 → ℤ) i
    else if b = q then (![1, -1, 1, -1, 1, -1, 1] : Fin 7 → ℤ) i else 1

private lemma w135c2_omfMOrb_cube_val_z {l : ℕ} (z p q : Fin l) :
    ∀ i, w135c2_omfMOrb_cubePts z p q i z = ![1, 1, 1, 1, -1, -1, -1] i := by
  intro i
  simp [w135c2_omfMOrb_cubePts]

private lemma w135c2_omfMOrb_cube_val_p {l : ℕ} (z p q : Fin l) (hzp : z ≠ p) :
    ∀ i, w135c2_omfMOrb_cubePts z p q i p = ![1, 1, -1, -1, 1, 1, -1] i := by
  intro i
  simp [w135c2_omfMOrb_cubePts, Ne.symm hzp]

private lemma w135c2_omfMOrb_cube_val_q {l : ℕ} (z p q : Fin l) (hzq : z ≠ q) (hpq : p ≠ q) :
    ∀ i, w135c2_omfMOrb_cubePts z p q i q = ![1, -1, 1, -1, 1, -1, 1] i := by
  intro i
  simp [w135c2_omfMOrb_cubePts, Ne.symm hzq, Ne.symm hpq]

private lemma w135c2_omfMOrb_cube_val_last {l : ℕ} (z p q last : Fin l)
    (hzl : z ≠ last) (hpl : p ≠ last) (hql : q ≠ last) :
    ∀ i, w135c2_omfMOrb_cubePts z p q i last = 1 := by
  intro i
  simp [w135c2_omfMOrb_cubePts, Ne.symm hzl, Ne.symm hpl, Ne.symm hql]

open CFSG.StandardType in
private lemma w135c2_omfMOrb_cube_hsign {l : ℕ} (z p q : Fin l) :
    ∀ i, SpIsSign (w135c2_omfMOrb_cubePts z p q i) := by
  intro i
  fin_cases i
  · exact w135c2_omfMOrb_spIsSign_ite_three z p q (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  · exact w135c2_omfMOrb_spIsSign_ite_three z p q (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  · exact w135c2_omfMOrb_spIsSign_ite_three z p q (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
  · exact w135c2_omfMOrb_spIsSign_ite_three z p q (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
  · exact w135c2_omfMOrb_spIsSign_ite_three z p q (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  · exact w135c2_omfMOrb_spIsSign_ite_three z p q (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
  · exact w135c2_omfMOrb_spIsSign_ite_three z p q (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)

open CFSG.StandardType in
private lemma w135c2_omfMOrb_cube_horb {l : ℕ} (z p q : Fin l) :
    ∀ i, OmqFormalInOrbit (omqMinusCube l) (w135c2_omfMOrb_cubePts z p q i) := by
  intro i
  exact ⟨1, w135c2_omfMOrb_cubePts z p q i, w135c2_omfMOrb_cube_hsign z p q i,
    by funext b; simp [omqSignedActZ, omqMinusCube, Equiv.Perm.one_def]⟩

private theorem w135c2_omfMOrb_seven_cube {n : ℕ} (hn : 5 ≤ n) :
    ∃ u : Fin 7 → Fin (n - 1) → ℤ, Function.Injective u ∧
      (∀ i, OmqFormalInOrbit (omqMinusCube (n - 1)) (u i)) ∧
      ∀ i i', u i ≠ omqSignedActZ 1
        (fun a : Fin (n - 1) => if n ≤ a.val + 3 then -1 else 1) (u i') := by
  let z : Fin (n - 1) := ⟨0, by omega⟩
  let p : Fin (n - 1) := ⟨1, by omega⟩
  let q : Fin (n - 1) := ⟨2, by omega⟩
  let last : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hzp : z ≠ p := by intro h; simp [z, p] at h
  have hzq : z ≠ q := by intro h; simp [z, q] at h
  have hpq : p ≠ q := by intro h; simp [p, q] at h
  have hzl : z ≠ last := by intro h; simp [z, last] at h; omega
  have hpl : p ≠ last := by intro h; simp [p, last] at h; omega
  have hql : q ≠ last := by intro h; simp [q, last] at h; omega
  have hs2l : (fun a : Fin (n - 1) => if n ≤ a.val + 3 then -1 else 1) last = -1 := by
    simp only [last]; rw [if_pos]; omega
  exact ⟨w135c2_omfMOrb_cubePts z p q,
    w135c2_omfMOrb_inj_of_vals_zpq _ z p q
      (w135c2_omfMOrb_cube_val_z z p q)
      (w135c2_omfMOrb_cube_val_p z p q hzp)
      (w135c2_omfMOrb_cube_val_q z p q hzq hpq),
    w135c2_omfMOrb_cube_horb z p q,
    w135c2_omfMOrb_move_of_last _ last _
      (w135c2_omfMOrb_cube_val_last z p q last hzl hpl hql) hs2l⟩

private lemma w135c2_omfMOrb_fix_flag {n : ℕ} (hn : 5 ≤ n) {k : Type} [Field k] [CharP k 2]
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k} {j : Fin (n - 1)}
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hsep : μ j = (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).dScalar χ j)
    (hj2 : j.val + 2 ≤ n - 1) :
    ∀ t : Fin (n - 1), μ t ≠ (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).dScalar χ t →
      omqSignedActZ (omqMinusSimple (n - 1) t).1 (omqMinusSimple (n - 1) t).2
        (omqMinusFlag (n - 1) j.val) = omqMinusFlag (n - 1) j.val := by
  intro t htne
  have htj : t.val ≠ j.val := fun h => htne (by rw [Fin.ext h]; exact hsep)
  exact omq_minus_simpleFix_flag hj2 htj

private lemma w135c2_omfMOrb_fix_flag_one {n : ℕ} (hn : 5 ≤ n) {k : Type} [Field k] [CharP k 2]
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k} {j : Fin (n - 1)}
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hsep : μ j = (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).dScalar χ j)
    (hj1 : j.val = 1) :
    ∀ t : Fin (n - 1), μ t ≠ (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).dScalar χ t →
      omqSignedActZ (omqMinusSimple (n - 1) t).1 (omqMinusSimple (n - 1) t).2
        (omqMinusFlag (n - 1) 1) = omqMinusFlag (n - 1) 1 := by
  intro t htne
  have htj : t.val ≠ 1 := by
    intro h
    apply htne
    have ht' : t = j := Fin.ext (by rw [h, hj1])
    rw [ht']; exact hsep
  exact omq_minus_simpleFix_flag (by omega : 1 + 2 ≤ n - 1) htj

private lemma w135c2_omfMOrb_fix_cube {n : ℕ} (hn : 5 ≤ n) {k : Type} [Field k] [CharP k 2]
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k} {j : Fin (n - 1)}
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hsep : μ j = (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).dScalar χ j)
    (hj_eq : j.val = n - 2) :
    ∀ t : Fin (n - 1), μ t ≠ (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).dScalar χ t →
      omqSignedActZ (omqMinusSimple (n - 1) t).1 (omqMinusSimple (n - 1) t).2
        (omqMinusCube (n - 1)) = omqMinusCube (n - 1) := by
  intro t htne
  have htj : t.val ≠ n - 2 := by
    intro h
    apply htne
    have ht' : t = j := Fin.ext (by rw [h, hj_eq])
    rw [ht']; exact hsep
  have htl : t.val + 1 < n - 1 := by have := t.isLt; omega
  exact omq_minus_simpleFix_cube htl

theorem omMinus_seven_le_rank_negLastTwo {n : ℕ} (hn : 5 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k V : Type} [Field k] [CharP k 2] [AddCommGroup V]
    [Module k V] [Module.Finite k V] {σ : Representation k (spinGroup (quadMinus n K b c)) V}
    (hσ : IsSimpleRep σ) {y : V} {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).IsCurtisType σ y χ μ)
    {j : Fin (n - 1)} (hj : j.val ≠ 0)
    (hsep : μ j = (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).dScalar χ j)
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group}
    (hxr : omqnfRealizes (n - 1) x 1 (fun a => if n ≤ a.val + 3 then -1 else 1)) :
    7 ≤ Module.finrank k
      (LinearMap.range (σ ((SmallO8mCurtis.curtisDatum n (by omega) hirrQ).nW x) - 1)) := by
  classical
  by_cases hj2 : j.val + 2 ≤ n - 1
  · by_cases hj1 : j.val = 1
    · obtain ⟨u, hinj, horb, hmove⟩ := w135c2_omfMOrb_seven_flag_one hn
      exact omq_omMinus_rank_of_eps_orbit (by omega : 4 ≤ n) hirrQ hσ ht hxr
        (w135c2_omfMOrb_fix_flag_one hn hirrQ hsep hj1) hinj horb hmove
    · obtain ⟨u, hinj, horb, hmove⟩ :=
        w135c2_omfMOrb_seven_flag_ge_two hn (by omega : 2 ≤ j.val) hj2
      exact omq_omMinus_rank_of_eps_orbit (by omega : 4 ≤ n) hirrQ hσ ht hxr
        (w135c2_omfMOrb_fix_flag hn hirrQ hsep hj2) hinj horb hmove
  · have hj_eq : j.val = n - 2 := by have := j.isLt; omega
    obtain ⟨u, hinj, horb, hmove⟩ := w135c2_omfMOrb_seven_cube hn
    exact omq_omMinus_rank_of_eps_orbit (by omega : 4 ≤ n) hirrQ hσ ht hxr
      (w135c2_omfMOrb_fix_cube hn hirrQ hsep hj_eq) hinj horb hmove

private theorem w135c2_omfMOrb_four_of_orbit {n : ℕ} (hn : 5 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k V : Type} [Field k] [CharP k 2] [AddCommGroup V]
    [Module k V] [Module.Finite k V] {σ : Representation k (spinGroup (quadMinus n K b c)) V}
    (hσ : IsSimpleRep σ) {y : V} {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).IsCurtisType σ y χ μ)
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group} {π : Equiv.Perm (Fin (n - 1))}
    (hxr : omqnfRealizes (n - 1) x π 1) (v : Fin (n - 1) → ℤ)
    (hvform : ∀ t : Fin (n - 1),
      μ t ≠ (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).dScalar χ t →
      omqSignedActZ (omqMinusSimple (n - 1) t).1 (omqMinusSimple (n - 1) t).2 v = v)
    (T : V →ₗ[k] V)
    (hT : ∀ w, ∃ a : k, T (σ ((SmallO8mCurtis.curtisDatum n (by omega) hirrQ).nW w) y) =
      a • σ ((SmallO8mCurtis.curtisDatum n (by omega) hirrQ).nW (x * w)) y)
    {u : Fin 4 → Fin (n - 1) → ℤ} (hinj : Function.Injective u)
    (horb : ∀ i, OmqFormalInOrbit v (u i))
    (hmove : ∀ i i', u i ≠ omqSignedActZ π 1 (u i')) :
    4 ≤ Module.finrank k (LinearMap.range (T - 1)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D := SmallO8mCurtis.curtisDatum n (by omega : 4 ≤ n) hirrQ
  let cs := (coxeterMatrix (isFiniteType_cartanB (n - 1))).toCoxeterSystem
  let : MulAction (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group (Fin (n - 1) → ℤ) :=
    MulAction.compHom (Fin (n - 1) → ℤ) (weylAction (isFiniteType_cartanB (n - 1)))
  let v' : Fin (n - 1) → ℤ := ofStdB (n - 1) v
  have hsm : ∀ (w : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group)
      (z : Fin (n - 1) → ℤ), w • z = weylAction (isFiniteType_cartanB (n - 1)) w z :=
    fun w z => by simp [MulAction.compHom_smul_def, Module.End.smul_def]
  have hv' : ∀ t : Fin (n - 1), μ t ≠ D.dScalar χ t → cs.simple t • v' = v' := by
    intro t htne
    rw [hsm]
    exact w135c2_omfMOrb_fix_weylAction (v := v) (t := t) (hvform t htne)
  choose πi si hsi hacti using horb
  choose bi hbi using fun i => exists_omqnfRealizes_of_signedPerm (πi i) (hsi i)
  let cc : Fin 4 → (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group := fun i => x * bi i
  choose a ha using hT
  have hb : ∀ i, bi i • v' = ofStdB (n - 1) (u i) := by
    intro i
    rw [hsm, w135c2_omfMOrb_weylAction_ofStdB (bi i) (πi i) (si i) v (hbi i), hacti i]
  have hc : ∀ i, cc i • v' = ofStdB (n - 1) (omqSignedActZ π 1 (u i)) := by
    intro i
    rw [mul_smul, hb i, hsm]
    exact w135c2_omfMOrb_weylAction_ofStdB x π 1 (u i) hxr
  obtain ⟨hinj', hmove'⟩ := w135c2_omfMOrb_inj_move_of_smul hb hc hinj hmove
  exact le_finrank_range_sub_one_of_map_orbit (D := D) hσ ht hv' T bi cc (fun i => a (bi i))
    (fun j => ha (bi j)) hinj' hmove'

theorem omMinus_four_le_rank_of_map_shapeA {n : ℕ} (hn : 5 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k V : Type} [Field k] [CharP k 2] [AddCommGroup V]
    [Module k V] [Module.Finite k V] {σ : Representation k (spinGroup (quadMinus n K b c)) V}
    (hσ : IsSimpleRep σ) {y : V} {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).IsCurtisType σ y χ μ)
    {j : Fin (n - 1)} (hj : j.val ≠ 0)
    (hsep : μ j = (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).dScalar χ j)
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group} {π : Equiv.Perm (Fin (n - 1))}
    (hxr : omqnfRealizes (n - 1) x π 1) (hπ : π * π = 1)
    (hπ0 : π ⟨0, by omega⟩ = ⟨1, by omega⟩) (hπ1 : π ⟨1, by omega⟩ = ⟨0, by omega⟩)
    (T : V →ₗ[k] V)
    (hT : ∀ w, ∃ a : k, T (σ ((SmallO8mCurtis.curtisDatum n (by omega) hirrQ).nW w) y) =
      a • σ ((SmallO8mCurtis.curtisDatum n (by omega) hirrQ).nW (x * w)) y) :
    4 ≤ Module.finrank k (LinearMap.range (T - 1)) := by
  classical
  have hsh : OmqMinusShape (by omega : 2 ≤ n - 1) π 1 :=
    Or.inl ⟨fun _ => rfl, hπ, hπ0, hπ1⟩
  by_cases hj2 : j.val + 2 ≤ n - 1
  · obtain ⟨u, hinj, horb, hmove⟩ :=
      omq_minus_exists_four_flag (by omega : 3 ≤ n - 1) (by omega : 1 ≤ j.val) hj2
        (CFSG.StandardType.spIsSign_one (m := n - 1)) hsh
    exact w135c2_omfMOrb_four_of_orbit hn hirrQ hσ ht hxr (omqMinusFlag (n - 1) j.val)
      (w135c2_omfMOrb_fix_flag hn hirrQ hsep hj2) T hT hinj horb hmove
  · have hj_eq : j.val = n - 2 := by have := j.isLt; omega
    obtain ⟨u, hinj, horb, hmove⟩ :=
      omq_minus_exists_four_cube (by omega : 3 ≤ n - 1)
        (CFSG.StandardType.spIsSign_one (m := n - 1)) hsh (Or.inl (by omega : 4 ≤ n - 1))
    exact w135c2_omfMOrb_four_of_orbit hn hirrQ hσ ht hxr (omqMinusCube (n - 1))
      (w135c2_omfMOrb_fix_cube hn hirrQ hsep hj_eq) T hT hinj horb hmove

end CFSG.LocalAnalysis.WeakClosure81
