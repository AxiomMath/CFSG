module

public import CFSG.RankThree.PartOne.KC.CommutatorOdd
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.RankThree.PartOne

open Subgroup
open scoped commutatorElement

namespace KCOddCommutator

variable {C : Type*} [Group C]

theorem normal_center_map {N : Subgroup C} (hN : N.Normal) :
    ((Subgroup.center N).map N.subtype).Normal := by
  refine ⟨fun z hz c => ?_⟩
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨⟨c * n * c⁻¹, hN.conj_mem n n.2 c⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro m
  apply Subtype.ext
  have hm : c⁻¹ * (m : C) * c ∈ N := by
    have := hN.conj_mem m m.2 c⁻¹
    simpa [mul_assoc] using this
  have hcomm := congrArg Subtype.val (Subgroup.mem_center_iff.mp hn ⟨c⁻¹ * (m : C) * c, hm⟩)
  simp only [Subgroup.coe_mul] at hcomm ⊢
  calc (m : C) * (c * n * c⁻¹) = c * ((c⁻¹ * (m : C) * c) * n) * c⁻¹ := by group
    _ = c * (n * (c⁻¹ * (m : C) * c)) * c⁻¹ := by rw [← hcomm]
    _ = c * n * c⁻¹ * (m : C) := by group

@[expose] def oddPart (Z : Subgroup C) (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) : Subgroup C where
  carrier := {c | c ∈ Z ∧ Odd (orderOf c)}
  mul_mem' := by
    rintro a b ⟨haZ, ha⟩ ⟨hbZ, hb⟩
    refine ⟨Z.mul_mem haZ hbZ, ?_⟩
    have hcomm : Commute a b := hZ a haZ b hbZ
    have h1 : orderOf (a * b) ∣ Nat.lcm (orderOf a) (orderOf b) := hcomm.orderOf_mul_dvd_lcm
    exact Odd.of_dvd_nat (ha.mul hb) (h1.trans (Nat.lcm_dvd_mul _ _))
  one_mem' := ⟨Z.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨haZ, ha⟩
    exact ⟨Z.inv_mem haZ, by rwa [orderOf_inv]⟩

theorem mem_oddPart {Z : Subgroup C} {hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a} {c : C} :
    c ∈ oddPart Z hZ ↔ c ∈ Z ∧ Odd (orderOf c) :=
  Iff.rfl

theorem normal_oddPart {Z : Subgroup C} (hZn : Z.Normal) (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) :
    (oddPart Z hZ).Normal := by
  refine ⟨fun c hc g => ?_⟩
  obtain ⟨hcZ, hco⟩ := hc
  refine ⟨hZn.conj_mem c hcZ g, ?_⟩
  have : orderOf (g * c * g⁻¹) = orderOf c :=
    orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective c
  rwa [this]

theorem odd_card_oddPart [Finite C] {Z : Subgroup C} (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) :
    Odd (Nat.card (oddPart Z hZ)) := by
  by_contra h
  have h2 : 2 ∣ Nat.card (oddPart Z hZ) := by
    rcases Nat.even_or_odd (Nat.card (oddPart Z hZ)) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hxo : Odd (orderOf (x : C)) := x.2.2
  rw [Subgroup.orderOf_coe, hx] at hxo
  exact absurd hxo (by decide)

theorem exists_pow_two_pow_mem_oddPart [Finite C] {Z : Subgroup C}
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) {c : C} (hc : c ∈ Z) :
    ∃ k : ℕ, c ^ 2 ^ k ∈ oddPart Z hZ := by
  obtain ⟨k, b, hb, hord⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf c)
    (orderOf_pos c).ne'
  refine ⟨k, Z.pow_mem hc _, ?_⟩
  have h1 : orderOf (c ^ 2 ^ k) = b := by
    rw [orderOf_pow' c (by positivity), hord, Nat.gcd_eq_right (dvd_mul_right _ _),
      Nat.mul_div_cancel_left _ (by positivity)]
  rw [h1]
  exact hb

theorem commutator_mem_oddPart [Finite C] {Z : Subgroup C} (hZn : Z.Normal)
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) {α : C}
    (hfix : ∀ z ∈ Z, (∃ k : ℕ, z ^ 2 ^ k = 1) → α * z * α⁻¹ = z) {c : C} (hc : c ∈ Z) :
    ⁅α, c⁆ ∈ oddPart Z hZ := by
  obtain ⟨k, b, hb, hord⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf c)
    (orderOf_pos c).ne'
  have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) (b : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hb))
  obtain ⟨u, v, huv⟩ := hcop
  have huv' : ((2 ^ k : ℕ) : ℤ) * u + (b : ℤ) * v = 1 := by linarith
  have hdec : c = (c ^ 2 ^ k) ^ u * (c ^ b) ^ v := by
    calc c = c ^ (((2 ^ k : ℕ) : ℤ) * u + (b : ℤ) * v) := by rw [huv', zpow_one]
      _ = (c ^ 2 ^ k) ^ u * (c ^ b) ^ v := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  set x : C := (c ^ 2 ^ k) ^ u with hx
  set y : C := (c ^ b) ^ v with hy
  have hxZ : x ∈ Z := Z.zpow_mem (Z.pow_mem hc _) u
  have hyZ : y ∈ Z := Z.zpow_mem (Z.pow_mem hc _) v
  have hxodd : Odd (orderOf x) := by
    have h1 : orderOf (c ^ 2 ^ k) = b := by
      rw [orderOf_pow' c (by positivity), hord, Nat.gcd_eq_right (dvd_mul_right _ _),
        Nat.mul_div_cancel_left _ (by positivity)]
    have h2 : orderOf x ∣ orderOf (c ^ 2 ^ k) := orderOf_dvd_of_pow_eq_one (by
      rw [hx, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
        one_zpow])
    rw [h1] at h2
    exact Odd.of_dvd_nat hb h2
  have hy2 : y ^ 2 ^ k = 1 := by
    rw [hy, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul, mul_comm,
      ← hord, pow_orderOf_eq_one, one_zpow]
  have hαy : α * y * α⁻¹ = y := hfix y hyZ ⟨k, hy2⟩
  have hcomm : ⁅α, c⁆ = (α * x * α⁻¹) * x⁻¹ := by
    rw [commutatorElement_def]
    calc α * c * α⁻¹ * c⁻¹ = α * (x * y) * α⁻¹ * (x * y)⁻¹ := by rw [← hdec]
      _ = (α * x * α⁻¹) * (α * y * α⁻¹) * y⁻¹ * x⁻¹ := by group
      _ = (α * x * α⁻¹) * x⁻¹ := by rw [hαy]; group
  rw [hcomm]
  refine (oddPart Z hZ).mul_mem ?_ ((oddPart Z hZ).inv_mem ⟨hxZ, hxodd⟩)
  refine ⟨hZn.conj_mem x hxZ α, ?_⟩
  have : orderOf (α * x * α⁻¹) = orderOf x :=
    orderOf_injective (MulAut.conj α).toMonoidHom (MulAut.conj α).injective x
  rwa [this]

theorem odd_commutator_of_central_residue [Finite C] {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {N J S A : Subgroup C} (hN : N.Normal) (hA : IsPGroup p A)
    (hAS : ∀ α ∈ A, ∀ s ∈ S, α * s * α⁻¹ ∈ S) (hSAN : ⁅S, A⁆ ≤ N)
    (hSJ : ∀ s ∈ S, ∀ j ∈ J, s * j = j * s)
    (hCJ : ∀ n ∈ N, (∀ j ∈ J, n * j = j * n) → ∀ m ∈ N, n * m = m * n)
    (hfix : ∀ α ∈ A, ∀ z ∈ N, (∀ m ∈ N, z * m = m * z) → (∃ k : ℕ, z ^ 2 ^ k = 1) →
      α * z * α⁻¹ = z) :
    Odd (Nat.card (⁅S, A⁆ : Subgroup C)) := by
  set Z : Subgroup C := (Subgroup.center N).map N.subtype with hZ
  have hZmem : ∀ z : C, z ∈ Z ↔ z ∈ N ∧ ∀ m ∈ N, z * m = m * z := by
    intro z
    constructor
    · intro hz
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hz
      refine ⟨n.2, fun m hm => ?_⟩
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hn ⟨m, hm⟩)
      simpa using this.symm
    · rintro ⟨hzN, hz⟩
      exact Subgroup.mem_map.mpr ⟨⟨z, hzN⟩, Subgroup.mem_center_iff.mpr fun m =>
        Subtype.ext (by simpa using (hz m m.2).symm), rfl⟩
  have hZn : Z.Normal := normal_center_map hN
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    ((hZmem a).mp ha).2 b ((hZmem b).mp hb).1
  have : (oddPart Z hZcomm).Normal := normal_oddPart hZn hZcomm
  have hSAZ : ⁅S, A⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro s hs α hα
    have hsa : ⁅s, α⁆ ∈ S := by
      have h := hAS α hα s⁻¹ (S.inv_mem hs)
      have : ⁅s, α⁆ = s * (α * s⁻¹ * α⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact S.mul_mem hs h
    have hsn : ⁅s, α⁆ ∈ N := hSAN (Subgroup.commutator_mem_commutator hs hα)
    exact (hZmem _).mpr ⟨hsn, hCJ _ hsn (fun j hj => hSJ _ hsa j hj)⟩
  exact (commutator_subgroup_odd_of_fixed_two_part hp hA
    (fun α hα c hc => commutator_mem_oddPart hZn hZcomm
      (fun z hz h2 => hfix α hα z ((hZmem z).mp hz).1 ((hZmem z).mp hz).2 h2) hc)
    (fun c hc => exists_pow_two_pow_mem_oddPart hZcomm hc) hSAZ (odd_card_oddPart hZcomm)).2

end KCOddCommutator

end CFSG.RankThree.PartOne
