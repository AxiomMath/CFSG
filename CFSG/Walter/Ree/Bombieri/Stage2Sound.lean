module

public import CFSG.Walter.Ree.Bombieri.Stage2Comp
public import CFSG.Walter.Ree.Bombieri.SpecSound
import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Spec

open F3P hiding X

theorem normalize_eq_self {a : F3P} (ha : a.Valid) : normalize a = a := by
  obtain ⟨p, n⟩ := a
  rw [valid_iff] at ha
  simp only at ha
  simp [F3P.normalize, Nat.and_comm n p, ha]

section

variable {K : Type*} [Field K] [CharP K 3] {T : Tab} {r : K}

theorem frobT_spec (hm : PE.IsMul (castThree K) r (mulT T)) {a : F3P} (ha : a.Valid) :
    ∀ e, (frobT T a e).Valid ∧
      F3P.ev (castThree K) r (frobT T a e) = F3P.ev (castThree K) r a ^ 3 ^ e
  | 0 => ⟨ha, by simp [frobT]⟩
  | e + 1 => by
    obtain ⟨h1, h2⟩ := frobT_spec hm ha e
    obtain ⟨h3, h4⟩ := hm _ _ h1 h1
    obtain ⟨h5, h6⟩ := hm _ _ h1 h3
    simp only [frobT]
    refine ⟨h5, ?_⟩
    rw [h6, h4, h2, pow_succ, pow_mul]
    ring

theorem check2_sound (hT : tabCheck T = true) (hf : T.f.Valid)
    (hr : F3P.ev (castThree K) r T.f = 0) {k lam : ℕ} {neg : Bool} {ws : List F3P}
    (h : check2 T k lam neg ws = true) : Elim.Hs k lam neg ≠ 0 := by
  have hm := F3P.isMul_mulT hT hf hr
  set c := substPt T k lam neg ws with hc
  have hcs : ∀ j, (c j).Valid ∧ F3P.ev (castThree K) r (c j) =
      F3P.ev (castThree K) r (normalize (ws.getD (substIdx k neg j) zero)) ^
        3 ^ substExp k lam neg j :=
    fun j => frobT_spec hm (valid_normalize _) _
  set w : Fin (k + 1) → K := fun i => F3P.ev (castThree K) r (normalize (ws.getD i zero))
    with hw
  set cK : Fin 5 → K :=
    fun j => w ⟨substIdx k neg j, substIdx_lt k neg j⟩ ^ 3 ^ substExp k lam neg j with hcK
  have hcK' : ∀ j (hj : j < 5), F3P.ev (castThree K) r (c j) = cK ⟨j, hj⟩ :=
    fun j _ => (hcs j).2
  simp only [check2, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hq0, hq1⟩, hq2⟩, hspec⟩ := h
  have hQ : ∀ ε : ℤ, unitT T (qVal T c ε) = true → Elim.evA5 cK (Elim.Qε ε) ≠ 0 := by
    intro ε hu
    obtain ⟨hv, he⟩ := PE.evalM_spec hm (ρ := c) (α := fun _ => zero) (fun j => (hcs j).1)
      (fun _ => valid_zero) (Elim.qExpr ε)
    have hne := ev_ne_zero_of_unitT hm hv hu
    rw [he] at hne
    rw [Elim.evA5_Qε]
    convert hne using 1
    simp only [Elim.qExpr, PE.eval_sub, PE.eval_mul, PE.eval_add, PE.eval_pow, PE.eval_var,
      PE.eval_const, PE.eval_one, Function.comp_apply]
    rw [hcK' 0 (by norm_num), hcK' 1 (by norm_num), hcK' 2 (by norm_num)]
    rfl
  have hH0 : Elim.evA5 cK Elim.H0 ≠ 0 := by
    have h0 := specCheck_sound hT hf hr hspec
    have hfun : (![F3P.ev (castThree K) r (normalize (c 0)),
        F3P.ev (castThree K) r (normalize (c 1)), F3P.ev (castThree K) r (normalize (c 2)),
        F3P.ev (castThree K) r (normalize (c 3)), F3P.ev (castThree K) r (normalize (c 4))] :
          Fin 5 → K) = cK := by
      funext j
      fin_cases j <;> simp [normalize_eq_self (hcs _).1, hcK']
    rw [← hc, hfun] at h0
    exact h0
  intro h0
  have hval := congrArg (MvPolynomial.eval₂ (castThree K) w) h0
  rw [MvPolynomial.eval₂_zero, Elim.eval₂_Hs, Elim.evA5_H] at hval
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hQ 0 hq0) (hQ 1 hq1)) (hQ (-1) hq2)) hH0 hval

end

theorem fieldBatchCheck_sound {f : F3P} {m : ℕ} (hm : m ≠ 0) (hf : f.Valid) {g : F3P}
    {es : List Entry} (h : fieldBatchCheck f m g es = true) :
    ∀ e ∈ es, Elim.Hs e.k e.lam e.neg ≠ 0 := by
  simp only [fieldBatchCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hroot, htab⟩, hb⟩ := h
  let _ : Fintype (GaloisField 3 m) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 m) = 3 ^ m := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 3 m hm
  obtain ⟨r, hr⟩ := exists_root_of_rootCheck hcard hroot
  intro e he
  simp only [batchCheck, List.all_eq_true] at hb
  exact check2_sound (K := GaloisField 3 m) (T := mkTab f m g) htab hf hr (hb e he)

end Spec

end CFSG.Walter.Ree.Bombieri
