module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.C1

open CFSG.Quasithin CFSG.Quasithin.F53Mod

@[expose] def dotO (u w : orth.W) : ZMod 2 :=
  ∑ i, Multiplicative.toAdd (u : ↥(G6.coreMod 5)).1 i *
    Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 i

theorem dotO_mul_left (u u' w : orth.W) : dotO (u * u') w = dotO u w + dotO u' w := by
  unfold dotO
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (Multiplicative.toAdd (u.1 * u'.1) i) * _ = _
  simp [add_mul]

theorem dotO_mul_right (u w w' : orth.W) : dotO u (w * w') = dotO u w + dotO u w' := by
  unfold dotO
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show _ * (Multiplicative.toAdd (w.1 * w'.1) i) = _
  simp [mul_add]

theorem dotO_one_right (u : orth.W) : dotO u 1 = 0 := by
  have h := dotO_mul_right u 1 1
  rw [mul_one] at h
  exact add_eq_left.mp h.symm

theorem dotO_one_left (w : orth.W) : dotO 1 w = 0 := by
  have h := dotO_mul_left 1 1 w
  rw [mul_one] at h
  exact add_eq_left.mp h.symm

theorem dotO_inj : ∀ u u' : orth.W, (∀ w, dotO u w = dotO u' w) → u = u' := by
  decide +kernel

theorem dotO_act (σ : Equiv.Perm (Fin 5)) (u w : orth.W) :
    dotO (orth.act σ u) (orth.act σ w) = dotO u w := by
  unfold dotO
  exact Equiv.sum_comp σ⁻¹ (fun j => Multiplicative.toAdd (u : ↥(G6.coreMod 5)).1 j *
    Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 j)

theorem dotO_act_inv (σ : Equiv.Perm (Fin 5)) (u w : orth.W) :
    dotO u (orth.act σ⁻¹ w) = dotO (orth.act σ u) w := by
  have h := dotO_act σ u (orth.act σ⁻¹ w)
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h
  exact h.symm

theorem eps_mem : ∀ i : Fin 4, ∑ j : Fin 5, ((if j = 0 then (1 : ZMod 2) else 0) +
    (if j = i.succ then 1 else 0)) = 0 := by decide

@[expose] def epsO (i : Fin 4) : orth.W :=
  ⟨Multiplicative.ofAdd (fun j : Fin 5 => (if j = 0 then (1 : ZMod 2) else 0) +
    (if j = i.succ then 1 else 0)), eps_mem i⟩

@[expose] def bitO (a : ZMod 2) (x : orth.W) : orth.W := if a = 0 then 1 else x

private theorem epsO_repr : ∀ w : orth.W,
    w = bitO (Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 1) (epsO 0) *
      bitO (Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 2) (epsO 1) *
      bitO (Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 3) (epsO 2) *
      bitO (Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 4) (epsO 3) := by decide +kernel

private theorem exists_dual : ∀ t : Fin 4 → ZMod 2, ∃ u : orth.W, ∀ i, dotO u (epsO i) = t i := by
  decide +kernel

private theorem add_repr (ψ : orth.W → ZMod 2) (hψ : ∀ x y, ψ (x * y) = ψ x + ψ y) (w : orth.W) :
    ψ w = Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 1 * ψ (epsO 0) +
      Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 2 * ψ (epsO 1) +
      Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 3 * ψ (epsO 2) +
      Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 4 * ψ (epsO 3) := by
  have h1 : ψ 1 = 0 := by
    have h := hψ 1 1
    rw [mul_one] at h
    exact add_eq_left.mp h.symm
  have hb : ∀ (a : ZMod 2) (x : orth.W), ψ (bitO a x) = a * ψ x := by
    intro a x
    unfold bitO
    split_ifs with h
    · rw [h1, h, zero_mul]
    · have : a = 1 := by revert h a; decide
      rw [this, one_mul]
  conv_lhs => rw [epsO_repr w]
  rw [hψ, hψ, hψ, hb, hb, hb, hb]

theorem exists_dotO (φ : orth.W → ZMod 2) (hφ : ∀ x y, φ (x * y) = φ x + φ y) :
    ∃ u : orth.W, ∀ w, φ w = dotO u w := by
  obtain ⟨u, hu⟩ := exists_dual (fun i => φ (epsO i))
  refine ⟨u, fun w => ?_⟩
  rw [add_repr φ hφ w, add_repr (dotO u) (dotO_mul_right u) w, hu, hu, hu, hu]

end CFSG.Quasithin.F53.Stellmacher.S35.C1
