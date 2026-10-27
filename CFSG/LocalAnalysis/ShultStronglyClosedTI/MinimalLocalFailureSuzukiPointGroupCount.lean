module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPointGroupSemilinear

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open scoped Pointwise

variable {G : Type} [Group G]

theorem card_eq_relIndex_mul_card {A K : Subgroup G} (h : A ≤ K) :
    Nat.card K = A.relIndex K * Nat.card A := by
  rw [← Subgroup.relIndex_mul_card, inf_eq_left.mpr h]

variable [Finite G]

theorem odd_relIndex_of_card {H B J L M : Subgroup G} (hBH : B ≤ H) (hJB : J ≤ B) (hLJ : L ≤ J)
    (hMH : M ≤ H) {q N : ℕ} (hq : 0 < q) (hHB : B.relIndex H = q ^ 3 * N) (hN : Odd N)
    (hBJ : Odd (J.relIndex B)) (hJL : Odd (L.relIndex J))
    (hM : Nat.card M = q ^ 3 * Nat.card L) : Odd (M.relIndex H) := by
  have h1 := card_eq_relIndex_mul_card hMH
  rw [card_eq_relIndex_mul_card hBH, card_eq_relIndex_mul_card hJB,
    card_eq_relIndex_mul_card hLJ, hHB, hM] at h1
  have hpos : 0 < q ^ 3 * Nat.card L := Nat.mul_pos (pow_pos hq 3) Nat.card_pos
  have h2 : M.relIndex H = N * (J.relIndex B * L.relIndex J) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [← h1]
    ring
  rw [h2]
  exact hN.mul (hBJ.mul hJL)

theorem exists_sylow_le_of_odd_relIndex {H C M : Subgroup G} (hMC : M ≤ C) (hCH : C ≤ H)
    (hM : Odd (M.relIndex H)) :
    (∃ S : Sylow 2 ↥H, (S : Subgroup ↥H).map H.subtype ≤ C) ∧ Odd (C.relIndex H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S₀ : Sylow 2 M := default
  set S₀g := (S₀ : Subgroup M).map M.subtype with hS₀g
  have hS₀M : S₀g ≤ M := Subgroup.map_subtype_le _
  have hS₀idx : S₀g.relIndex M = (S₀ : Subgroup M).index := by
    change (S₀g.subgroupOf M).index = _
    rw [hS₀g, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hodd : Odd (S₀g.relIndex H) := by
    rw [← Subgroup.relIndex_mul_relIndex S₀g M H hS₀M (hMC.trans hCH), hS₀idx]
    exact (Nat.not_even_iff_odd.mp fun h2 => S₀.not_dvd_index (even_iff_two_dvd.mp h2)).mul hM
  have hS₀2 : IsPGroup 2 S₀g := S₀.isPGroup'.map M.subtype
  have hS2 : IsPGroup 2 (S₀g.subgroupOf H) := hS₀2.comap_subtype
  have hnd : ¬ 2 ∣ (S₀g.subgroupOf H).index := fun h2 =>
    (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  refine ⟨⟨hS2.toSylow hnd, ?_⟩, hodd.of_dvd_nat (Subgroup.relIndex_dvd_of_le_left H
    (hS₀M.trans hMC))⟩
  rw [IsPGroup.toSylow_coe, Subgroup.subgroupOf_map_subtype]
  exact inf_le_left.trans (hS₀M.trans hMC)

theorem relIndex_sup_eq {T J P : Subgroup G} (hTJ : T ≤ Subgroup.centralizer (J : Set G))
    (hinf : T ⊓ J = ⊥) (hPJ : P ≤ J) : (T ⊔ P).relIndex (T ⊔ J) = P.relIndex J := by
  have hTP : T ≤ Subgroup.centralizer (P : Set G) :=
    hTJ.trans (Subgroup.centralizer_le hPJ)
  have hinfP : T ⊓ P = ⊥ := eq_bot_iff.mpr ((inf_le_inf_left T hPJ).trans hinf.le)
  have h1 := card_eq_relIndex_mul_card (sup_le_sup_left hPJ T)
  rw [card_sup_of_commute hTJ hinf, card_sup_of_commute hTP hinfP,
    card_eq_relIndex_mul_card hPJ] at h1
  have hpos : 0 < Nat.card T * Nat.card P := Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← h1]
  ring

omit [Finite G] in
theorem mem_coset_normalizer_of_conj_mem {Q C : Subgroup G}
    (hCQ : C ≤ Subgroup.centralizer (Q : Set G)) {u c : G} (hc : c ∈ C)
    (hcu : u⁻¹ * (c * u * c⁻¹) ∈ Q) : c ∈ Subgroup.normalizer (u • (Q : Set G)) := by
  have hcomm : ∀ y ∈ Q, c * y = y * c := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp (hCQ hc) y hy).symm
  refine Subgroup.mem_set_normalizer_iff.mpr fun x => ?_
  rw [mem_leftCoset_iff, mem_leftCoset_iff]
  have hx : u⁻¹ * (c * x * c⁻¹) = (u⁻¹ * (c * u * c⁻¹)) * (c * (u⁻¹ * x) * c⁻¹) := by group
  constructor
  · intro hux
    rw [hx, hcomm _ hux, mul_inv_cancel_right]
    exact Q.mul_mem hcu hux
  · intro hux
    have h1 : c * (u⁻¹ * x) * c⁻¹ ∈ Q := by
      rw [hx] at hux
      have := Q.mul_mem (Q.inv_mem hcu) hux
      rwa [inv_mul_cancel_left] at this
    have h2 : u⁻¹ * x = c⁻¹ * (c * (u⁻¹ * x) * c⁻¹) * c := by group
    rw [h2, mul_assoc, ← hcomm _ h1, inv_mul_cancel_left]
    exact h1

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
