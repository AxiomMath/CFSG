module

public import CFSG.RankThree.GroupTheory.SteinbergBYQD32Extraspecial


public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement

attribute [local instance] qdFintypeD

theorem qd32_Z_mul_self : qd32Z * qd32Z = 1 := by
  have : qd32Z ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [orderOf_qd32Z])
  rwa [pow_two] at this

theorem qd32_V_mul_self : qd32V * qd32V = 1 := by
  rw [qd32V, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_one, qd32_mk_eq_mk_iff]
  decide

theorem qd32_V_UV : qd32V * (qd32U * qd32V) = qd32Z * ((qd32U * qd32V) * qd32V) := by
  rw [qd32V, qd32U, qd32Z_eq]
  simp only [← QuotientGroup.mk_mul]
  rw [qd32_mk_eq_mk_iff]
  decide

theorem qd32_I_J : qd32I * qd32J = qd32Z * (qd32J * qd32I) := by
  have h := commutatorElement_qd32I_qd32J
  rw [commutatorElement_def] at h
  rw [← h]
  group

theorem qd32_comm_QD (q : QuaternionGroup 2) (d : QuaternionDihedralD) :
    (((q, 1) : QuaternionGroup 2 × QuaternionDihedralD) : QD32) *
        (((1, d) : QuaternionGroup 2 × QuaternionDihedralD) : QD32) =
      (((1, d) : QuaternionGroup 2 × QuaternionDihedralD) : QD32) *
        (((q, 1) : QuaternionGroup 2 × QuaternionDihedralD) : QD32) := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  simp

theorem qd32_V_I : qd32V * qd32I = qd32I * qd32V := (qd32_comm_QD _ _).symm
theorem qd32_V_J : qd32V * qd32J = qd32J * qd32V := (qd32_comm_QD _ _).symm

theorem card_ge_pow_four_of_relations {V : Type} [Group V] [Finite V] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hcomm : ∀ x y : V, x * y = y * x) (hexp : ∀ x : V, x ^ q = 1)
    (Z A B I J : MulAut V) (hZ1 : Z ≠ 1) (hZZ : Z * Z = 1) (hAA : A * A = 1)
    (hAZ : Z * A = A * Z) (hBZ : Z * B = B * Z) (hIZ : Z * I = I * Z) (hJZ : Z * J = J * Z)
    (hAB : A * B = Z * (B * A)) (hIJ : I * J = Z * (J * I)) (hAI : A * I = I * A)
    (hAJ : A * J = J * A) :
    q ^ 4 ≤ Nat.card V := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have eZZ : ∀ v, Z (Z v) = v := fun v => by
    have := congrArg (fun f : MulAut V => f v) hZZ
    simpa using this
  have eAA : ∀ v, A (A v) = v := fun v => by
    have := congrArg (fun f : MulAut V => f v) hAA
    simpa using this
  have eAZ : ∀ v, Z (A v) = A (Z v) := fun v => by
    have := congrArg (fun f : MulAut V => f v) hAZ
    simpa using this
  have eBZ : ∀ v, Z (B v) = B (Z v) := fun v => by
    have := congrArg (fun f : MulAut V => f v) hBZ
    simpa using this
  have eIZ : ∀ v, Z (I v) = I (Z v) := fun v => by
    have := congrArg (fun f : MulAut V => f v) hIZ
    simpa using this
  have eJZ : ∀ v, Z (J v) = J (Z v) := fun v => by
    have := congrArg (fun f : MulAut V => f v) hJZ
    simpa using this
  have eAB : ∀ v, A (B v) = Z (B (A v)) := fun v => by
    have := congrArg (fun f : MulAut V => f v) hAB
    simpa using this
  have eIJ : ∀ v, I (J v) = Z (J (I v)) := fun v => by
    have := congrArg (fun f : MulAut V => f v) hIJ
    simpa using this
  have eAI : ∀ v, A (I v) = I (A v) := fun v => by
    have := congrArg (fun f : MulAut V => f v) hAI
    simpa using this
  have eAJ : ∀ v, A (J v) = J (A v) := fun v => by
    have := congrArg (fun f : MulAut V => f v) hAJ
    simpa using this
  let Wp : Subgroup V :=
    { carrier := {v | Z v = v⁻¹ ∧ A v = v}
      mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul, ha.1, hb.1, mul_inv_rev, hcomm],
        by rw [map_mul, ha.2, hb.2]⟩
      one_mem' := ⟨by simp, by simp⟩
      inv_mem' := fun {a} ha => ⟨by rw [map_inv, ha.1], by rw [map_inv, ha.2]⟩ }
  let Wm : Subgroup V :=
    { carrier := {v | Z v = v⁻¹ ∧ A v = v⁻¹}
      mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul, ha.1, hb.1, mul_inv_rev, hcomm],
        by rw [map_mul, ha.2, hb.2, mul_inv_rev, hcomm]⟩
      one_mem' := ⟨by simp, by simp⟩
      inv_mem' := fun {a} ha => ⟨by rw [map_inv, ha.1], by rw [map_inv, ha.2]⟩ }
  have hWp : ∀ v, v ∈ Wp ↔ Z v = v⁻¹ ∧ A v = v := fun v => Iff.rfl
  have hWm : ∀ v, v ∈ Wm ↔ Z v = v⁻¹ ∧ A v = v⁻¹ := fun v => Iff.rfl
  have hinv : ∀ t : V, t = t⁻¹ → t = 1 := by
    intro t ht
    have h2 : t ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [ht]
      exact inv_mul_cancel t
    have h3 : orderOf t ∣ Nat.gcd 2 q :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one (hexp t))
    have hcop : Nat.gcd 2 q = 1 :=
      ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)).gcd_eq_one
    rw [hcop] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hinj : Function.Injective (fun p : Wp × Wm => (p.1 : V) * (p.2 : V)) := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have h' : (x : V) * y = x' * y' := h
    have ht : (x' : V)⁻¹ * x = y' * (y : V)⁻¹ := by
      have : (x' : V)⁻¹ * (x * y) = (x' : V)⁻¹ * (x' * y') := by rw [h']
      calc (x' : V)⁻¹ * x = (x' : V)⁻¹ * (x * y) * (y : V)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel_right]
        _ = (x' : V)⁻¹ * (x' * y') * (y : V)⁻¹ := by rw [this]
        _ = y' * (y : V)⁻¹ := by rw [inv_mul_cancel_left]
    have hp : (x' : V)⁻¹ * x ∈ Wp := Wp.mul_mem (Wp.inv_mem x'.2) x.2
    have hm : y' * (y : V)⁻¹ ∈ Wm := Wm.mul_mem y'.2 (Wm.inv_mem y.2)
    rw [ht] at hp
    have h1 := hp.2
    have h2 := hm.2
    have h3 : (y' : V) * (y : V)⁻¹ = ((y' : V) * (y : V)⁻¹)⁻¹ := h1.symm.trans h2
    have h4 := hinv _ h3
    have hxx : (x : V) = x' := by
      rw [← ht] at h4
      calc (x : V) = (x' : V) * ((x' : V)⁻¹ * x) := by rw [mul_inv_cancel_left]
        _ = x' := by rw [h4, mul_one]
    have hyy : (y : V) = y' := by
      have := mul_inv_eq_one.mp h4
      exact this.symm
    exact Prod.ext (Subtype.ext hxx) (Subtype.ext hyy)
  have hnt : ∃ w : V, w ∈ Wp ∧ w ≠ 1 := by
    obtain ⟨v, hv⟩ : ∃ v, Z v ≠ v := by
      by_contra hcon
      push Not at hcon
      exact hZ1 (MulEquiv.ext fun v => by simpa using hcon v)
    obtain ⟨u, hu⟩ : ∃ u : V, u = v * (Z v)⁻¹ := ⟨_, rfl⟩
    have hu1 : u ≠ 1 := by
      intro h
      apply hv
      have : v = Z v := mul_inv_eq_one.mp (hu ▸ h)
      exact this.symm
    have hZu : Z u = u⁻¹ := by
      rw [hu, map_mul, map_inv, eZZ, mul_inv_rev, inv_inv, hcomm]
    obtain ⟨u₁, hu₁⟩ : ∃ u₁ : V, u₁ = u * A u := ⟨_, rfl⟩
    have hu₁p : u₁ ∈ Wp := by
      refine ⟨?_, ?_⟩
      · rw [hu₁, map_mul, hZu, eAZ, hZu, map_inv, mul_inv_rev, hcomm]
      · rw [hu₁, map_mul, eAA, hcomm]
    by_cases h1 : u₁ = 1
    ·
      have hAu : A u = u⁻¹ := by
        have : u * A u = 1 := hu₁ ▸ h1
        exact eq_inv_of_mul_eq_one_right this
      refine ⟨B u, ⟨?_, ?_⟩, fun h => hu1 (by simpa using (map_eq_one_iff B B.injective).mp h)⟩
      · rw [eBZ, hZu, map_inv]
      · rw [eAB, hAu, map_inv, map_inv, eBZ, hZu, map_inv, inv_inv]
    · exact ⟨u₁, hu₁p, h1⟩
  obtain ⟨w, hwp, hw1⟩ := hnt
  have hwo : orderOf w = q := orderOf_eq_prime (hexp w) hw1
  have hIp : ∀ v ∈ Wp, I v ∈ Wp := fun v hv => ⟨by rw [eIZ, hv.1, map_inv], by rw [eAI, hv.2]⟩
  have hJp : ∀ v ∈ Wp, J v ∈ Wp := fun v hv => ⟨by rw [eJZ, hv.1, map_inv], by rw [eAJ, hv.2]⟩
  obtain ⟨w', hw'p, hw'n⟩ : ∃ w' ∈ Wp, w' ∉ zpowers w := by
    by_cases hI : I w ∈ zpowers w
    · refine ⟨J w, hJp w hwp, fun hJw => ?_⟩
      obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp hI
      obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp hJw
      have h1 : I (J w) = w ^ (s * t) := by
        rw [← ht, map_zpow, ← hs, ← zpow_mul]
      have h2 : Z (J (I w)) = (w ^ (t * s))⁻¹ := by
        rw [← hs, map_zpow, ← ht, ← zpow_mul, map_zpow, hwp.1, inv_zpow]
      have h3 : w ^ (2 * (s * t)) = 1 := by
        have h4 := eIJ w
        rw [h1, h2] at h4
        rw [two_mul, zpow_add]
        nth_rewrite 2 [mul_comm s t]
        rw [h4, ← mul_comm, mul_comm, mul_comm t s]
        exact inv_mul_cancel _
      have h5 : (q : ℤ) ∣ 2 * (s * t) := by
        rw [← hwo]
        exact orderOf_dvd_iff_zpow_eq_one.mpr h3
      have hqp : _root_.Prime (q : ℤ) := _root_.Nat.prime_iff_prime_int.mp hq
      rcases hqp.dvd_or_dvd h5 with h6 | h6
      · exact hq2 (by
          have h7 : q ∣ 2 := by exact_mod_cast h6
          exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h7)
      · rcases hqp.dvd_or_dvd h6 with h7 | h7
        · have : w ^ s = 1 := orderOf_dvd_iff_zpow_eq_one.mp (hwo ▸ h7)
          rw [hs] at this
          exact hw1 (by simpa using (map_eq_one_iff I I.injective).mp this)
        · have : w ^ t = 1 := orderOf_dvd_iff_zpow_eq_one.mp (hwo ▸ h7)
          rw [ht] at this
          exact hw1 (by simpa using (map_eq_one_iff J J.injective).mp this)
    · exact ⟨I w, hIp w hwp, hI⟩
  have hS : q ^ 2 ≤ Nat.card Wp := by
    set S : Subgroup V := Subgroup.closure {w, w'} with hSdef
    have hSle : S ≤ Wp := (Subgroup.closure_le Wp).mpr (by
      intro x hx
      rcases hx with rfl | rfl
      · exact hwp
      · exact hw'p)
    have hzS : zpowers w ≤ S := Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have hw'S : w' ∈ S := Subgroup.subset_closure (by simp)
    have hpS : IsPGroup q S := fun x => ⟨1, Subtype.ext (by simpa using hexp x.1)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hpS
    have hdvd : q ∣ Nat.card S := by
      have := Subgroup.card_dvd_of_le hzS
      rwa [Nat.card_zpowers, hwo] at this
    have hn2 : 2 ≤ n := by
      by_contra hlt
      push Not at hlt
      interval_cases n
      · rw [hn] at hdvd
        simp at hdvd
        exact hq.one_lt.ne' hdvd
      · have hcard : Nat.card S ≤ Nat.card (zpowers w) := by
          rw [Nat.card_zpowers, hwo, hn]
          simp
        exact hw'n ((Subgroup.eq_of_le_of_card_ge hzS hcard) ▸ hw'S)
    calc q ^ 2 ≤ q ^ n := Nat.pow_le_pow_right hq.pos hn2
      _ = Nat.card S := hn.symm
      _ ≤ Nat.card Wp := Subgroup.card_le_of_le hSle
  have hBm : ∀ v ∈ Wp, B v ∈ Wm := fun v hv => ⟨by rw [eBZ, hv.1, map_inv], by
    rw [eAB, hv.2, eBZ, hv.1, map_inv]⟩
  have hBle : Nat.card Wp ≤ Nat.card Wm :=
    Nat.card_le_card_of_injective (fun x : Wp => (⟨B x, hBm x x.2⟩ : Wm)) (by
      intro x y hxy
      exact Subtype.ext (B.injective (congrArg Subtype.val hxy)))
  have hprod : Nat.card Wp * Nat.card Wm ≤ Nat.card V := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective _ hinj
  calc q ^ 4 = q ^ 2 * q ^ 2 := by ring
    _ ≤ Nat.card Wp * Nat.card Wm := Nat.mul_le_mul hS (hS.trans hBle)
    _ ≤ Nat.card V := hprod

theorem card_ge_pow_four_of_qd32 {V : Type} [Group V] [Finite V] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hcomm : ∀ x y : V, x * y = y * x) (hexp : ∀ x : V, x ^ q = 1)
    (f : QD32 →* MulAut V) (hf : Function.Injective f) : q ^ 4 ≤ Nat.card V := by
  have hZ1 : f qd32Z ≠ 1 := fun h => by
    have h1 : qd32Z = 1 := hf (h.trans (map_one f).symm)
    have h2 := orderOf_qd32Z
    rw [h1, orderOf_one] at h2
    omega
  have hc : ∀ g : QD32, f qd32Z * f g = f g * f qd32Z := fun g =>
    by rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp qd32Z_mem_center g]
  refine card_ge_pow_four_of_relations hq hq2 hcomm hexp (f qd32Z) (f qd32V) (f (qd32U * qd32V))
    (f qd32I) (f qd32J) hZ1 ?_ ?_ (hc _) (hc _) (hc _) (hc _) ?_ ?_ ?_ ?_
  · rw [← map_mul, qd32_Z_mul_self, map_one]
  · rw [← map_mul, qd32_V_mul_self, map_one]
  · simpa only [map_mul] using congrArg f qd32_V_UV
  · simpa only [map_mul] using congrArg f qd32_I_J
  · rw [← map_mul, ← map_mul, qd32_V_I]
  · rw [← map_mul, ← map_mul, qd32_V_J]

end CFSG.RankThree.PartOne.F106
