module

public import CFSG.Quasithin.H13.A7Nat1236InspBase
public import CFSG.Quasithin.Background.C2Blocks

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin
open scoped Pointwise

variable {W : Type*} [Group W] [Finite W]

theorem false_of_partition {Y D C : Subgroup W} (hYD : Y ≤ D) (hDC : D ≤ C)
    (e : ↥C ≃* Perm (Fin 7)) {P : Finset (Finset (Fin 7))}
    (hP : (D.subgroupOf C).map e.toMonoidHom ≤ MulAction.stabilizer (Perm (Fin 7)) P)
    (hcov : P.biUnion id = Finset.univ) (hPc : P.card < 5) (hB : ∀ B ∈ P, B.card < 5)
    {f : ↥Y →* alternatingGroup (Fin 6)} (hf : Function.Surjective f) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 5
    (dvd_trans (by norm_num) (card_alt_six_dvd hf))
  have hyC : (y : W) ∈ C := hDC (hYD y.2)
  have hσ : e ⟨y, hyC⟩ ∈ MulAction.stabilizer (Perm (Fin 7)) P :=
    hP ⟨⟨y, hyC⟩, hYD y.2, rfl⟩
  have hord : orderOf (e ⟨y, hyC⟩) = 5 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    exact hy
  have h5 : (e ⟨y, hyC⟩) ^ 5 = 1 := hord ▸ pow_orderOf_eq_one _
  have h1 := perm_eq_one_of_pow_five_of_mem_stabilizer h5 hσ hcov hPc hB
  rw [h1, orderOf_one] at hord
  norm_num at hord

theorem card_lt_five_of_isPartitionOfType {P : Finset (Finset (Fin 7))} {sizes : Multiset ℕ}
    (hP : IsPartitionOfType P sizes) (hs : sizes = {4, 3} ∨ sizes = {2, 2, 2, 1}) :
    P.card < 5 ∧ ∀ B ∈ P, B.card < 5 := by
  obtain ⟨-, -, -, hmap⟩ := hP
  have hcard : P.card = Multiset.card sizes := by
    rw [← hmap, Multiset.card_map]
    rfl
  refine ⟨?_, fun B hB => ?_⟩
  · rw [hcard]
    rcases hs with rfl | rfl <;> decide
  · have hmem : B.card ∈ sizes := hmap ▸ Multiset.mem_map_of_mem _ hB
    rcases hs with rfl | rfl <;> simp at hmem <;> omega

theorem false_of_five_sq {G : Type*} [Group G] [Finite G] {K M X : Subgroup G}
    (hK : ¬ 25 ∣ Nat.card K) (h5 : 5 ∣ M.relIndex K) (hX : X ≤ K ⊓ M)
    (hX5 : 5 ∣ Nat.card X) : False := by
  have h1 := (M.subgroupOf K).card_mul_index
  have h2 : Nat.card X ∣ Nat.card (M.subgroupOf K) := by
    have hle : X.subgroupOf K ≤ M.subgroupOf K := fun x hx => (hX hx).2
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hX.trans inf_le_left)).toEquiv] at this
  apply hK
  rw [← h1]
  exact Nat.mul_dvd_mul (hX5.trans h2) h5

theorem false_of_card_dvd_of_ne {Y D C : Subgroup W} (hYD : Y ≤ D) (hDC : D ≤ C) (hDne : D ≠ C)
    (hC : Nat.card C ∣ 360) {f : ↥Y →* alternatingGroup (Fin 6)}
    (hf : Function.Surjective f) : False := by
  have h1 := card_alt_six_dvd hf
  have h2 : Nat.card Y ∣ Nat.card D := Subgroup.card_dvd_of_le hYD
  have h3 : Nat.card D ∣ Nat.card C := Subgroup.card_dvd_of_le hDC
  have h4 : Nat.card D ≠ Nat.card C := fun h => hDne (Subgroup.eq_of_le_of_card_ge hDC h.ge)
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hDpos : 0 < Nat.card D := Nat.card_pos
  obtain ⟨k, hk⟩ := h3
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    exact h4 hk.symm
  have hk2 : 2 ≤ k := by omega
  have h5 : Nat.card C ≤ 360 := Nat.le_of_dvd (by norm_num) hC
  have h6 : 360 ≤ Nat.card D := Nat.le_of_dvd hDpos (h1.trans h2)
  have h7 : 2 * Nat.card D ≤ Nat.card C := by
    rw [hk]
    nlinarith
  omega

theorem false_of_card_not_dvd {Y C : Subgroup W} (hYC : Y ≤ C) (hC : ¬ 5 ∣ Nat.card C)
    {f : ↥Y →* alternatingGroup (Fin 6)} (hf : Function.Surjective f) : False :=
  hC (dvd_trans (by norm_num) ((card_alt_six_dvd hf).trans (Subgroup.card_dvd_of_le hYC)))

end CFSG.Quasithin.H13.A7
