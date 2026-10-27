module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinH
public import CFSG.Quasithin.EmptyFaithful.S143A6Nat

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm

theorem conj_five (a r : Perm (Fin 6)) :
    (r⁻¹ * a * r) * (r⁻¹ * a * r) * (r⁻¹ * a * r) * (r⁻¹ * a * r) * (r⁻¹ * a * r) =
      r⁻¹ * (a * a * a * a * a) * r := by group

theorem conj_three (a r : Perm (Fin 6)) :
    (r⁻¹ * a * r) * (r⁻¹ * a * r) * (r⁻¹ * a * r) = r⁻¹ * (a * a * a) * r := by group

theorem conj_four (a r : Perm (Fin 6)) :
    (r⁻¹ * a * r) * (r⁻¹ * a * r) * (r⁻¹ * a * r) * (r⁻¹ * a * r) = r⁻¹ * (a * a * a * a) * r := by
  group

theorem conj_w3 (p q r : Perm (Fin 6)) :
    w3 (r⁻¹ * p * r) (r⁻¹ * q * r) = r⁻¹ * w3 p q * r := by
  unfold w3
  group

theorem pairs_conj (p q : Perm (Fin 6)) (hp : sign p = 1) (hp1 : p ≠ 1) (hp2 : p * p = 1)
    (hq : sign q = 1) (hq4 : q * q * q * q = 1)
    (h5 : (p * q) * (p * q) * (p * q) * (p * q) * (p * q) = 1)
    (h5' : (p * (q * q)) * (p * (q * q)) * (p * (q * q)) * (p * (q * q)) * (p * (q * q)) = 1)
    (h3 : w3 p q * w3 p q * w3 p q = 1) (h31 : w3 p q ≠ 1) (hfix : ∃ i, w3 p q i = i) :
    ∃ s : Perm (Fin 6), s * x0P = p * s ∧ s * y0P = q * s := by
  have hx0A : x0P ∈ alternatingGroup (Fin 6) := mem_alternatingGroup.mpr sign_x0P
  have hpA : p ∈ alternatingGroup (Fin 6) := mem_alternatingGroup.mpr hp
  have hx01 : x0P ≠ 1 := by unfold x0P; decide
  obtain ⟨r, -, hr⟩ := CFSG.Quasithin.S143.alt6_invol_conj x0P p hx0A hpA hx01 hp1
    rel_x0y0.1 hp2
  have hx : x0P = r⁻¹ * p * r := by rw [← hr]; group
  set q' : Perm (Fin 6) := r⁻¹ * q * r with hq'
  have e1 : x0P * q' = r⁻¹ * (p * q) * r := by rw [hx, hq']; group
  have e2 : x0P * (q' * q') = r⁻¹ * (p * (q * q)) * r := by rw [hx, hq']; group
  have e3 : w3 x0P q' = r⁻¹ * w3 p q * r := by rw [hx, hq']; exact conj_w3 p q r
  have hq'4 : q' * q' * q' * q' = 1 := by rw [hq']; rw [conj_four, hq4]; group
  have hq's : sign q' = 1 := by
    rw [hq']
    simp [hq]
  have h5q : (x0P * q') * (x0P * q') * (x0P * q') * (x0P * q') * (x0P * q') = 1 := by
    rw [e1, conj_five, h5]; group
  have h5q' : (x0P * (q' * q')) * (x0P * (q' * q')) * (x0P * (q' * q')) * (x0P * (q' * q')) *
      (x0P * (q' * q')) = 1 := by
    rw [e2, conj_five, h5']; group
  have h3q : w3 x0P q' * w3 x0P q' * w3 x0P q' = 1 := by
    rw [e3, conj_three, h3]; group
  have h31q : w3 x0P q' ≠ 1 := by
    rw [e3]
    intro h
    apply h31
    have := congrArg (fun t => r * t * r⁻¹) h
    simpa [mul_assoc] using this
  have hfixq : ∃ i, w3 x0P q' i = i := by
    obtain ⟨i, hi⟩ := hfix
    refine ⟨r⁻¹ i, ?_⟩
    rw [e3]
    simp [Perm.mul_apply, hi]
  obtain ⟨t, ht1, ht2⟩ := pairs_conj_x0 q' hq'4 hq's h5q h5q' h3q h31q hfixq
  refine ⟨r * t, ?_, ?_⟩
  · calc r * t * x0P = r * (t * x0P) := by group
      _ = r * (x0P * t) := by rw [ht1]
      _ = (r * x0P) * t := by group
      _ = p * (r * t) := by rw [hx]; group
  · calc r * t * y0P = r * (t * y0P) := by group
      _ = r * (q' * t) := by rw [ht2]
      _ = q * (r * t) := by rw [hq']; group

end CFSG.Quasithin.A6Fin
