module

public import CFSG.Quasithin.Vol2.Ch10StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Quasithin

@[expose] def wrIota (q : Multiplicative (ZMod 2)) : Equiv.Perm (Fin 5) →* SymFiveWrTwo where
  toFun σ := ⟨Pi.mulSingle q σ, 1⟩
  map_one' := by
    refine RegularWreathProduct.ext ?_ rfl
    funext x
    simp [Pi.mulSingle_apply]
  map_mul' σ τ := by
    refine RegularWreathProduct.ext ?_ ?_
    · funext x
      show (Pi.mulSingle q (σ * τ) : Multiplicative (ZMod 2) → Equiv.Perm (Fin 5)) x =
        (Pi.mulSingle q σ : Multiplicative (ZMod 2) → Equiv.Perm (Fin 5)) x *
          (Pi.mulSingle q τ : Multiplicative (ZMod 2) → Equiv.Perm (Fin 5))
            ((1 : Multiplicative (ZMod 2))⁻¹ * x)
      have e : (1 : Multiplicative (ZMod 2))⁻¹ * x = x := by revert x; decide
      rw [e, Pi.mulSingle_mul]
      rfl
    · exact (one_mul 1).symm

theorem wrIota_injective (q : Multiplicative (ZMod 2)) : Function.Injective (wrIota q) := by
  intro σ τ h
  have := congrArg (fun w : SymFiveWrTwo => w.left q) h
  simpa [wrIota] using this

@[expose] def wrBase : Subgroup SymFiveWrTwo where
  carrier := {w | w.right = 1 ∧ ∀ q, w.left q ∈ alternatingGroup (Fin 5)}
  mul_mem' {a b} ha hb := by
    refine ⟨by rw [RegularWreathProduct.mul_right, ha.1, hb.1, one_mul], fun q => ?_⟩
    have e : a.right⁻¹ * q = q := by rw [ha.1]; revert q; decide
    show a.left q * b.left (a.right⁻¹ * q) ∈ alternatingGroup (Fin 5)
    rw [e]
    exact (alternatingGroup (Fin 5)).mul_mem (ha.2 q) (hb.2 q)
  one_mem' := ⟨rfl, fun _ => (alternatingGroup (Fin 5)).one_mem⟩
  inv_mem' {a} ha := by
    refine ⟨by rw [RegularWreathProduct.inv_right, ha.1]; exact inv_one, fun q => ?_⟩
    have e : a.right * q = q := by rw [ha.1]; exact one_mul q
    show (a.left)⁻¹ (a.right * q) ∈ alternatingGroup (Fin 5)
    rw [e, Pi.inv_apply]
    exact (alternatingGroup (Fin 5)).inv_mem (ha.2 q)

theorem zmod2_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = Multiplicative.ofAdd (1 : ZMod 2) := by
  revert q
  decide

theorem left_pow_of_right_eq_one {w : SymFiveWrTwo} (hw : w.right = 1) (n : ℕ) :
    (w ^ n).right = 1 ∧ (w ^ n).left = w.left ^ n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have e : ∀ x : Multiplicative (ZMod 2), (1 : Multiplicative (ZMod 2))⁻¹ * x = x := by decide
    rw [pow_succ, RegularWreathProduct.mul_right, RegularWreathProduct.mul_left, ih.1, hw,
      one_mul, ih.2]
    refine ⟨rfl, ?_⟩
    funext x
    simp only [Pi.mul_apply, Pi.pow_apply, pow_succ]
    exact congrArg (fun y => w.left x ^ n * w.left y) (e x)

theorem mem_wrBase_of_odd {w : SymFiveWrTwo} (hw : Odd (orderOf w)) : w ∈ wrBase := by
  have hr : w.right = 1 := by
    have h1 := orderOf_map_dvd (RegularWreathProduct.rightHom) w
    have hsq : ∀ r : Multiplicative (ZMod 2), r ^ 2 = 1 := by decide
    have h2 : orderOf (RegularWreathProduct.rightHom w : Multiplicative (ZMod 2)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (hsq _)
    have h3 := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one ((Nat.coprime_two_right).mpr hw)] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  refine ⟨hr, fun q => ?_⟩
  obtain ⟨-, hl⟩ := left_pow_of_right_eq_one hr (orderOf w)
  have hpow : (w.left q) ^ orderOf w = 1 := by
    have := congrArg (fun f => f q) hl
    simp only [pow_orderOf_eq_one, Pi.pow_apply] at this
    rw [← this]
    rfl
  rw [Equiv.Perm.mem_alternatingGroup]
  have hs : (Equiv.Perm.sign (w.left q)) ^ orderOf w = 1 := by rw [← map_pow, hpow, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (w.left q)) with h | h
  · exact h
  · rw [h, Odd.neg_one_pow hw] at hs
    exact absurd hs (by decide)

end CFSG.Quasithin.Vol2.Ch10.SecD
