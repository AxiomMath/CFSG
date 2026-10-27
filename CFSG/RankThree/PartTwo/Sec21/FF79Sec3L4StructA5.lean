module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open Equiv Equiv.Perm

namespace A5Klein

def kF : Finset (Perm (Fin 5)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

theorem kF_mul : ∀ a ∈ kF, ∀ b ∈ kF, a * b ∈ kF := by decide +kernel
theorem kF_inv : ∀ a ∈ kF, a⁻¹ ∈ kF := by decide +kernel
def cc : Perm (Fin 5) := swap 0 1 * swap 1 2

theorem cc_alt : sign cc = 1 := by decide +kernel
theorem cc_norm : ∀ a ∈ kF, cc * a * cc⁻¹ ∈ kF := by decide +kernel
theorem cc_ord : orderOf cc = 3 := by
  apply orderOf_eq_prime <;> decide +kernel

def kV : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {σ | σ.1 ∈ kF}
  mul_mem' := fun {_ _} ha hb => kF_mul _ ha _ hb
  one_mem' := by decide +kernel
  inv_mem' := fun {_} ha => kF_inv _ ha

theorem kV_card : Nat.card kV = 4 := by
  have : Nat.card kV = Nat.card {σ : alternatingGroup (Fin 5) // σ.1 ∈ kF} := rfl
  rw [this, Nat.card_eq_fintype_card]
  decide +kernel

def cA : alternatingGroup (Fin 5) := ⟨cc, by rw [mem_alternatingGroup]; exact cc_alt⟩

theorem cA_ord : orderOf cA = 3 := by
  rw [← Subgroup.orderOf_coe]; exact cc_ord

theorem cA_norm : ∀ x ∈ kV, cA * x * cA⁻¹ ∈ kV := fun x hx => cc_norm _ hx

theorem card_A5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

end A5Klein

open A5Klein

theorem a5_klein_data {L : Type*} [Group L] (e : L ≃* alternatingGroup (Fin 5)) :
    ∃ (P : Subgroup L) (c : L), Nat.card P = 4 ∧ orderOf c = 3 ∧
      ∀ x ∈ P, c * x * c⁻¹ ∈ P := by
  refine ⟨kV.map e.symm.toMonoidHom, e.symm cA, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, kV_card]
  · rw [← cA_ord]
    exact orderOf_injective e.symm.toMonoidHom e.symm.injective cA
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨cA * y * cA⁻¹, cA_norm y hy, by simp⟩

variable {H : Type*} [Group H] [Finite H]

theorem index_eq_relIndex_of_sup_eq_top {N L : Subgroup H} [L.Normal] (h : N ⊔ L = ⊤) :
    N.index = (N ⊓ L).relIndex L := by
  have h1 := Subgroup.relIndex_mul_index (inf_le_left : N ⊓ L ≤ N)
  have h2 := Subgroup.relIndex_mul_index (inf_le_right : N ⊓ L ≤ L)
  have h3 : (N ⊓ L).relIndex N = L.relIndex N := Subgroup.inf_relIndex_left N L
  have h4 : L.relIndex (N ⊔ L) = L.relIndex N := Subgroup.relIndex_sup_right N L
  rw [h, Subgroup.relIndex_top_right] at h4
  rw [h3, ← h4] at h1
  have hpos : 0 < L.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have : L.index * N.index = L.index * (N ⊓ L).relIndex L := by
    rw [h1, ← h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem exists_normalized_two_subgroup {L : Subgroup H} [hL : L.Normal]
    (e : L ≃* alternatingGroup (Fin 5)) {A : Subgroup H} (hA : IsPGroup 3 A) :
    ∃ P : Subgroup H, P ≤ L ∧ IsPGroup 2 P ∧ P ≠ ⊥ ∧ ∀ a ∈ A, ∀ x ∈ P, a * x * a⁻¹ ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P0, c0, hP0, hc0, hnorm⟩ := a5_klein_data e
  have hL60 : Nat.card L = 60 := by rw [Nat.card_congr e.toEquiv]; exact card_A5
  have h2grp : IsPGroup 2 P0 := IsPGroup.of_card (n := 2) (by rw [hP0]; norm_num)
  have hidx : ¬ 2 ∣ P0.index := by
    have h := Subgroup.card_mul_index P0
    rw [hP0, hL60] at h
    have : P0.index = 15 := by omega
    rw [this]; norm_num
  let S : Sylow 2 L := h2grp.toSylow hidx
  have hF : Subgroup.normalizer ((S : Subgroup L).map L.subtype : Set H) ⊔ L = ⊤ :=
    Sylow.normalizer_sup_eq_top S
  set Q : Subgroup H := P0.map L.subtype with hQ
  have hF' : Subgroup.normalizer (Q : Set H) ⊔ L = ⊤ := hF
  set N : Subgroup H := Subgroup.normalizer (Q : Set H) with hN
  have hinv : ∀ y ∈ P0, c0⁻¹ * y * c0 ∈ P0 := by
    intro y hy
    have hc3 : c0 ^ 3 = 1 := hc0 ▸ pow_orderOf_eq_one c0
    have h1 : c0 * c0 = c0⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv, mul_assoc, ← pow_two, ← pow_succ']; exact hc3
    have h2 : c0⁻¹ * c0⁻¹ = c0 := by
      calc c0⁻¹ * c0⁻¹ = c0⁻¹ * c0⁻¹ * (c0 ^ 3) := by rw [hc3, mul_one]
        _ = c0 := by group
    have : c0⁻¹ * y * c0 = c0 * (c0 * y * c0⁻¹) * c0⁻¹ := by
      calc c0⁻¹ * y * c0 = (c0 * c0) * y * (c0⁻¹ * c0⁻¹) := by rw [h1, h2]
        _ = _ := by group
    rw [this]
    exact hnorm _ (hnorm _ hy)
  have hcN : (c0 : H) ∈ N := by
    rw [hN, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨c0 * y * c0⁻¹, hnorm y hy, by simp⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨c0⁻¹ * y * c0, hinv y hy, ?_⟩
      have : (y : H) = c0 * x * (c0 : H)⁻¹ := by simpa using hyx
      show ((c0⁻¹ * y * c0 : L) : H) = x
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, this]
      group
  have hcL : (c0 : H) ∈ N ⊓ L := ⟨hcN, c0.2⟩
  have h3dvd : 3 ∣ Nat.card (N ⊓ L : Subgroup H) := by
    have := Subgroup.orderOf_dvd_natCard (N ⊓ L) hcL
    rwa [Subgroup.orderOf_coe, hc0] at this
  have hrel : (N ⊓ L).relIndex L * Nat.card (N ⊓ L : Subgroup H) = 60 := by
    have h := Subgroup.card_mul_index ((N ⊓ L).subgroupOf L)
    rw [hL60] at h
    have hc : Nat.card ((N ⊓ L).subgroupOf L) = Nat.card (N ⊓ L : Subgroup H) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [hc] at h
    rw [← h, mul_comm]; rfl
  have hnd : ¬ 3 ∣ N.index := by
    rw [index_eq_relIndex_of_sup_eq_top hF']
    intro h3
    have h9 : 3 * 3 ∣ 60 := hrel ▸ Nat.mul_dvd_mul h3 h3dvd
    omega
  have hmod := hA.card_modEq_card_fixedPoints (H ⧸ N)
  have hnfix : Nat.card (MulAction.fixedPoints A (H ⧸ N)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    apply hnd
    exact (Nat.modEq_zero_iff_dvd).1 hmod
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.mp hnfix).1
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hgN : ∀ a ∈ A, g⁻¹ * a * g ∈ N := by
    intro a ha
    have h1 := hx ⟨a, ha⟩
    have h2 : ((a * g : H) : H ⧸ N) = (g : H ⧸ N) := h1
    have h3 := QuotientGroup.eq.1 h2
    have h4 : (g⁻¹ * a * g)⁻¹ ∈ N := by
      have : (g⁻¹ * a * g)⁻¹ = (a * g)⁻¹ * g := by group
      rw [this]; exact h3
    simpa using N.inv_mem h4
  have hcardP : Nat.card (Q.map (MulAut.conj g).toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hQ,
      Subgroup.card_map_of_injective L.subtype_injective, hP0]
  refine ⟨Q.map (MulAut.conj g).toMonoidHom, ?_, IsPGroup.of_card (n := 2) (by
    rw [hcardP]; norm_num), ?_, ?_⟩
  · rintro _ ⟨q, ⟨y, -, rfl⟩, rfl⟩
    exact hL.conj_mem _ y.2 g
  · intro hbot
    rw [hbot, Subgroup.card_bot] at hcardP
    omega
  · rintro a ha _ ⟨q, hq, rfl⟩
    have hn := hgN a ha
    refine ⟨g⁻¹ * a * g * q * (g⁻¹ * a * g)⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 hn q).1 hq
    · show g * (g⁻¹ * a * g * q * (g⁻¹ * a * g)⁻¹) * g⁻¹ = a * (g * q * g⁻¹) * a⁻¹
      group

end CFSG.RankThree.PartTwo.Sec21.FF79
