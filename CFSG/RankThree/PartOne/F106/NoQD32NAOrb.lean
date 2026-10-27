module

public import CFSG.RankThree.PartOne.F106.QD32Center

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY

section Fixed

variable {V : Type} [Group V] [Finite V]

@[expose] def invertedPart (hcomm : ∀ x y : V, x * y = y * x) (z : MulAut V) : Subgroup V where
  carrier := {w | z w = w⁻¹}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change z a = a⁻¹ at ha
    change z b = b⁻¹ at hb
    change z (a * b) = (a * b)⁻¹
    rw [map_mul, ha, hb, mul_inv_rev, hcomm]
  inv_mem' := by
    intro a ha
    change z a = a⁻¹ at ha
    change z a⁻¹ = (a⁻¹)⁻¹
    rw [map_inv, ha]

@[expose] def fixedPart (z : MulAut V) : Subgroup V where
  carrier := {v | z v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change z a = a at ha
    change z b = b at hb
    change z (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    change z a = a at ha
    change z a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_invertedPart {hcomm : ∀ x y : V, x * y = y * x} {z : MulAut V} {w : V} :
    w ∈ invertedPart hcomm z ↔ z w = w⁻¹ := Iff.rfl

theorem mem_fixedPart {z : MulAut V} {v : V} : v ∈ fixedPart z ↔ z v = v := Iff.rfl

theorem eq_one_of_sq_eq_one {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {x : V} (hx : x ^ q = 1)
    (h : x * x = 1) : x = 1 := by
  have hcop : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  have h3 : orderOf x ∣ Nat.gcd 2 q :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h))
      (orderOf_dvd_of_pow_eq_one hx)
  rw [hcop.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem qd32_fixed_point_free {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hcomm : ∀ x y : V, x * y = y * x) (hexp : ∀ x : V, x ^ q = 1)
    (f : QD32 →* MulAut V) (hf : Function.Injective f) (hV : Nat.card V < q ^ 5) :
    ∀ v : V, v ≠ 1 → f qd32Z v ≠ v := by
  classical
  intro v hv1 hzv
  set z : MulAut V := f qd32Z with hz
  have hZ1 : z ≠ 1 := fun h => by
    have h1 : qd32Z = 1 := hf (h.trans (map_one f).symm)
    have h2 := orderOf_qd32Z
    rw [h1, orderOf_one] at h2
    omega
  have hzc : ∀ g : QD32, z * f g = f g * z := fun g => by
    rw [hz, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp qd32Z_mem_center g]
  have hzz : ∀ x : V, z (z x) = x := fun x => by
    have : f (qd32Z * qd32Z) = 1 := by rw [qd32_Z_mul_self, map_one]
    have h2 := congrArg (fun g : MulAut V => g x) this
    simpa [map_mul] using h2
  set W := invertedPart hcomm z with hW
  set C := fixedPart z with hC
  have hCW : ∀ x : V, x ∈ C → x ∈ W → x = 1 := fun x hxC hxW => by
    have h1 : x = x⁻¹ := (mem_fixedPart.mp hxC).symm.trans (mem_invertedPart.mp hxW)
    exact eq_one_of_sq_eq_one hq hq2 (hexp x) (by
      calc x * x = x * x⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel x)
  obtain ⟨w₀, hw₀W, hw₀1⟩ : ∃ w ∈ W, w ≠ 1 := by
    have hne : ∃ x : V, z x ≠ x := by
      by_contra hcon
      push Not at hcon
      exact hZ1 (MulEquiv.ext hcon)
    obtain ⟨x, hx⟩ := hne
    refine ⟨x * (z x)⁻¹, ?_, fun h => hx (by
      have := mul_inv_eq_one.mp h
      exact this.symm)⟩
    rw [mem_invertedPart, map_mul, map_inv, hzz, mul_inv_rev, inv_inv, hcomm]
  have hinv : ∀ (g : QD32) (w : V), w ∈ W → f g w ∈ W := fun g w hw => by
    rw [mem_invertedPart]
    have h1 := congrArg (fun m : MulAut V => m w) (hzc g)
    simp only [MulAut.mul_apply] at h1
    rw [h1, mem_invertedPart.mp hw, map_inv]
  have hl : ∀ (g : QD32) (w : V), f g⁻¹ (f g w) = w := fun g w => by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hr : ∀ (g : QD32) (w : V), f g (f g⁻¹ w) = w := fun g w => by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  let φ : QD32 →* MulAut W :=
    { toFun := fun g =>
        { toFun := fun w => ⟨f g w, hinv g w w.2⟩
          invFun := fun w => ⟨f g⁻¹ w, hinv g⁻¹ w w.2⟩
          left_inv := fun w => Subtype.ext (hl g w)
          right_inv := fun w => Subtype.ext (hr g w)
          map_mul' := fun a b => Subtype.ext (by simp) }
      map_one' := by
        ext w
        simp
      map_mul' := fun a b => by
        ext w
        simp }
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    by_contra hg1
    have hker : (φ.ker).Normal := inferInstance
    have hne : φ.ker ≠ ⊥ := fun h => hg1 (by
      have : g ∈ φ.ker := hg
      rw [h] at this
      exact this)
    have hzK : qd32Z ∈ φ.ker := qd32Z_mem_of_normal hne
    have h1 : φ qd32Z = 1 := hzK
    have h2 := congrArg (fun m : MulAut W => (m ⟨w₀, hw₀W⟩ : V)) h1
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
      MulAut.one_apply] at h2
    have h3 : w₀ = w₀⁻¹ := h2.symm.trans hw₀W
    exact hw₀1 (eq_one_of_sq_eq_one hq hq2 (hexp w₀) (by
      calc w₀ * w₀ = w₀ * w₀⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel w₀))
  have hW4 : q ^ 4 ≤ Nat.card W :=
    card_ge_pow_four_of_qd32 hq hq2 (fun x y => Subtype.ext (hcomm x y))
      (fun x => Subtype.ext (hexp x)) φ hφ
  have hCq : q ≤ Nat.card C := by
    have hvC : v ∈ C := hzv
    have hord : orderOf v = q := by
      have h1 : orderOf v ∣ q := orderOf_dvd_of_pow_eq_one (hexp v)
      rcases (Nat.dvd_prime hq).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hv1
      · exact h
    have hle : Subgroup.zpowers v ≤ C := (Subgroup.zpowers_le).mpr hvC
    have h2 : Nat.card (Subgroup.zpowers v) ≤ Nat.card C :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    rw [Nat.card_zpowers, hord] at h2
    exact h2
  have hinj : Function.Injective (fun p : C × W => (p.1 : V) * (p.2 : V)) := by
    rintro ⟨c, w⟩ ⟨c', w'⟩ h
    simp only at h
    have h1 : (c' : V)⁻¹ * c = (w' : V) * (w : V)⁻¹ := by
      calc (c' : V)⁻¹ * c = (c' : V)⁻¹ * (c * w) * (w : V)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel_right]
        _ = (c' : V)⁻¹ * (c' * w') * (w : V)⁻¹ := by rw [h]
        _ = (w' : V) * (w : V)⁻¹ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    have hC1 : (c' : V)⁻¹ * c ∈ C := C.mul_mem (C.inv_mem c'.2) c.2
    have hW1 : (w' : V) * (w : V)⁻¹ ∈ W := W.mul_mem w'.2 (W.inv_mem w.2)
    have h2 : (c' : V)⁻¹ * c = 1 := hCW _ hC1 (h1 ▸ hW1)
    have h3 : (w' : V) * (w : V)⁻¹ = 1 := h1 ▸ h2
    have hc : c = c' := Subtype.ext (by
      have := h2
      rw [inv_mul_eq_one] at this
      exact this.symm)
    have hw : w = w' := Subtype.ext (by
      have := h3
      rw [mul_inv_eq_one] at this
      exact this.symm)
    rw [hc, hw]
  have hprod : Nat.card C * Nat.card W ≤ Nat.card V := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective _ hinj
  have : q ^ 5 ≤ Nat.card V := by
    calc q ^ 5 = q * q ^ 4 := by ring
      _ ≤ Nat.card C * Nat.card W := Nat.mul_le_mul hCq hW4
      _ ≤ Nat.card V := hprod
  omega

theorem qd32_dvd_card_of_invariant (f : QD32 →* MulAut V) (A : Finset V)
    (hinv : ∀ (g : QD32), ∀ v ∈ A, f g v ∈ A) (hmove : ∀ v ∈ A, f qd32Z v ≠ v) :
    16 ∣ A.card := by
  classical
  let _ : MulAction QD32 A :=
    { smul := fun g a => ⟨f g a, hinv g a a.2⟩
      one_smul := fun a => Subtype.ext (by
        change (f 1) (a : V) = a
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        change (f (a * b)) (x : V) = (f a) ((f b) (x : V))
        simp) }
  have : Fintype QD32 := Fintype.ofFinite QD32
  have h := MulAction.card_eq_sum_card_group_div_card_stabilizer QD32 A
  rw [Fintype.card_coe] at h
  rw [h]
  refine Finset.dvd_sum fun ω _ => ?_
  set a : A := ω.out with ha
  have hz : qd32Z ∉ MulAction.stabilizer QD32 a := fun hz' =>
    hmove a a.2 (congrArg Subtype.val hz')
  have h1 := qd32_card_le_two_of_not_mem hz
  have e1 : Fintype.card QD32 = 32 := by rw [← Nat.card_eq_fintype_card, card_QD32]
  have e2 : Fintype.card (MulAction.stabilizer QD32 a) =
      Nat.card (MulAction.stabilizer QD32 a) := Nat.card_eq_fintype_card.symm
  have h3 : 0 < Nat.card (MulAction.stabilizer QD32 a) := Nat.card_pos
  rw [e1, e2]
  interval_cases hc : Nat.card (MulAction.stabilizer QD32 a) <;> norm_num

theorem qd32_dvd_card_of_invariant_nonzero {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hcomm : ∀ x y : V, x * y = y * x) (hexp : ∀ x : V, x ^ q = 1)
    (f : QD32 →* MulAut V) (hf : Function.Injective f) (hV : Nat.card V < q ^ 5)
    (A : Finset V) (hA1 : (1 : V) ∉ A) (hinv : ∀ (g : QD32), ∀ v ∈ A, f g v ∈ A) :
    16 ∣ A.card :=
  qd32_dvd_card_of_invariant f A hinv fun v hv =>
    qd32_fixed_point_free hq hq2 hcomm hexp f hf hV v (fun h => hA1 (h ▸ hv))

theorem eq_one_of_fixed_of_order_five (hV : Nat.card V = 3 ^ 4) (τ : MulAut V) (hτ5 : τ ^ 5 = 1)
    (hτ1 : τ ≠ 1) : ∀ v : V, τ v = v → v = 1 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fintype V := Fintype.ofFinite V
  let g : Function.End V := fun v => τ v
  have hgp : ∀ n : ℕ, ∀ v, (g ^ n) v = (τ ^ n) v := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [pow_succ, pow_succ]
      exact (ih (τ v))
  have hg5 : g ^ 5 ^ 1 = 1 := by
    funext v
    rw [pow_one, hgp, hτ5]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq hg5
  set Fx : Subgroup V := fixedPart τ with hFx
  have hcard : Fintype.card g.fixedPoints = Nat.card Fx := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.refl _)
  rw [hcard, ← Nat.card_eq_fintype_card, hV] at hmod
  have hdvd : Nat.card Fx ∣ 3 ^ 4 := hV ▸ Subgroup.card_subgroup_dvd_card Fx
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hmod' : 3 ^ 4 ≡ 3 ^ j [MOD 5] := hjeq ▸ hmod
  have hj' : j = 0 ∨ j = 4 := by
    interval_cases j <;> first | omega | exact absurd hmod' (by decide)
  rcases hj' with rfl | rfl
  · intro v hv
    have h1 : Nat.card Fx = 1 := by simpa using hjeq
    have hbot : Fx = ⊥ := Subgroup.card_eq_one.mp h1
    have : v ∈ Fx := hv
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  · exfalso
    apply hτ1
    have h4 : Nat.card Fx = Nat.card V := by rw [hV]; simpa using hjeq
    have htop : Fx = ⊤ := (Subgroup.card_eq_iff_eq_top Fx).mp h4
    ext v
    have : v ∈ Fx := htop ▸ Subgroup.mem_top v
    exact this

theorem five_dvd_card_of_invariant (hV : Nat.card V = 3 ^ 4) (τ : MulAut V) (hτ5 : τ ^ 5 = 1)
    (hτ1 : τ ≠ 1) (A : Finset V) (hA1 : (1 : V) ∉ A) (hinv : ∀ v ∈ A, τ v ∈ A) :
    5 ∣ A.card := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfree := eq_one_of_fixed_of_order_five hV τ hτ5 hτ1
  let g : Function.End A := fun a => ⟨τ a, hinv a a.2⟩
  have hgp : ∀ n : ℕ, ∀ a : A, ((g ^ n) a : V) = (τ ^ n) a := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [pow_succ, pow_succ]
      exact (ih (g a))
  have hg5 : g ^ 5 ^ 1 = 1 := by
    funext a
    apply Subtype.ext
    rw [pow_one, hgp, hτ5]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq hg5
  have hempty : Fintype.card g.fixedPoints = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨a, ha⟩ => ?_⟩
    have h1 : τ a = a := congrArg Subtype.val ha
    exact hA1 (hfree a h1 ▸ a.2)
  rw [hempty, Fintype.card_coe] at hmod
  exact (Nat.modEq_zero_iff_dvd).mp hmod

end Fixed

end CFSG.RankThree.PartOne.F106
