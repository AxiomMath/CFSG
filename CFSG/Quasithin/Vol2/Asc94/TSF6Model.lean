module

public import CFSG.Quasithin.Vol2.Asc94.TSFrame2
public import CFSG.Quasithin.Vol2.Asc94.TSF6Comb

public section

namespace CFSG.Quasithin.A94.L52

open CFSG.Quasithin.A94.F6Comb (IsUp gm)

private theorem isUp_cm_sub_one {x : Hc} (hx : x ∈ Tm) : IsUp (cm x - 1) := by
  rw [mem_Tm] at hx
  unfold IsUp
  intro i j hij
  exact hx i j (not_lt.2 hij)

private theorem supp_SA {N : Mt} (hU : IsUp N) (h01 : N 0 1 = 0) (h23 : N 2 3 = 0)
    (h34 : N 3 4 = 0) (h24 : N 2 4 = 0) : SuppIn SA N := by
  intro i j hij
  by_cases hji : j ≤ i
  · exact hU i j hji
  · have key : ∀ i j : Fin 5, ¬ j ≤ i → ¬ SA i j →
        (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
      decide
    rcases key i j hji hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h01
    · exact h23
    · exact h24
    · exact h34

private theorem supp_SA2 {N : Mt} (hU : IsUp N) (h01 : N 0 1 = 0) (h12 : N 1 2 = 0)
    (h34 : N 3 4 = 0) (h02 : N 0 2 = 0) : SuppIn SA2 N := by
  intro i j hij
  by_cases hji : j ≤ i
  · exact hU i j hji
  · have key : ∀ i j : Fin 5, ¬ j ≤ i → ¬ SA2 i j →
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 3 ∧ j = 4) ∨ (i = 0 ∧ j = 2) := by
      decide
    rcases key i j hji hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h01
    · exact h12
    · exact h34
    · exact h02

private theorem cm_mul_sub_one (x y : Hc) : cm (x * y) - 1 = gm (cm x - 1) (cm y - 1) := by
  rw [cm_mul]
  unfold F6Comb.gm
  noncomm_ring

private theorem sq_sub_one_of_sq_one {x : Hc} (hx : x * x = 1) :
    (cm x - 1) * (cm x - 1) = 0 := by
  have hc : cm x * cm x = 1 := by rw [← cm_mul, hx, cm_one]
  have h2 : cm x + cm x = 0 := F6Comb.mat_add_self _
  have h1 : (1 : Mt) + 1 = 0 := F6Comb.mat_add_self 1
  calc (cm x - 1) * (cm x - 1) = cm x * cm x - (cm x + cm x) + 1 := by noncomm_ring
    _ = 1 - (cm x + cm x) + 1 := by rw [hc]
    _ = 1 + 1 := by rw [h2]; abel
    _ = 0 := h1

theorem f6Model_holds : F6Model := by
  intro E hET hEA hEc
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; norm_num)
  haveI : Fintype E := Fintype.ofFinite E
  let 𝒩 : Finset (Matrix (Fin 5) (Fin 5) (ZMod 2)) :=
    Finset.univ.image (fun x : E => cm x.1 - 1)
  have hmem : ∀ N, N ∈ 𝒩 ↔ ∃ x ∈ E, cm x - 1 = N := by
    intro N
    simp only [𝒩, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hinj : Function.Injective (fun x : E => cm x.1 - 1) := by
    intro x y hxy
    have h' : cm x.1 - 1 = cm y.1 - 1 := hxy
    have hc : cm x.1 = cm y.1 := sub_left_inj.1 h'
    exact Subtype.ext (Subtype.ext (Subtype.ext hc))
  have hcard : 𝒩.card = 64 := by
    show (Finset.univ.image (fun x : E => cm x.1 - 1)).card = 64
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card, hEc]
  have hup : ∀ N ∈ 𝒩, IsUp N := by
    intro N hN
    obtain ⟨x, hx, rfl⟩ := (hmem N).1 hN
    exact isUp_cm_sub_one (hET hx)
  have hgm : ∀ N ∈ 𝒩, ∀ M ∈ 𝒩, gm N M ∈ 𝒩 := by
    intro N hN M hM
    obtain ⟨x, hx, rfl⟩ := (hmem N).1 hN
    obtain ⟨y, hy, rfl⟩ := (hmem M).1 hM
    exact (hmem _).2 ⟨x * y, E.mul_mem hx hy, cm_mul_sub_one x y⟩
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, cm x * cm y = cm y * cm x := by
    intro x hx y hy
    have h : x * y = y * x := congrArg Subtype.val (hEA.1.is_comm.comm
      (⟨x, hx⟩ : E) ⟨y, hy⟩)
    rw [← cm_mul, ← cm_mul, h]
  have hcomm : ∀ N ∈ 𝒩, ∀ M ∈ 𝒩, N * M = M * N := by
    intro N hN M hM
    obtain ⟨x, hx, rfl⟩ := (hmem N).1 hN
    obtain ⟨y, hy, rfl⟩ := (hmem M).1 hM
    have h := hcommE x hx y hy
    have e1 : (cm x - 1) * (cm y - 1) = cm x * cm y - (cm x + cm y) + 1 := by noncomm_ring
    have e2 : (cm y - 1) * (cm x - 1) = cm y * cm x - (cm y + cm x) + 1 := by noncomm_ring
    rw [e1, e2, h, add_comm (cm y) (cm x)]
  have hsq : ∀ N ∈ 𝒩, N * N = 0 := by
    intro N hN
    obtain ⟨x, hx, rfl⟩ := (hmem N).1 hN
    have hx2 : x * x = 1 := by
      rw [← sq]
      exact hEA.2 x hx
    exact sq_sub_one_of_sq_one hx2
  rcases F6Comb.classify 𝒩 hup hgm hcomm hsq hcard with h | h
  ·
    left
    haveI : Finite A1 := Nat.finite_of_card_ne_zero (by rw [card_A1]; norm_num)
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro x hx
      have hN := h (cm x - 1) ((hmem _).2 ⟨x, hx, rfl⟩)
      obtain ⟨h01, h23, h34, h24⟩ := hN
      exact (mem_patSub hSA).2 (supp_SA (isUp_cm_sub_one (hET hx)) h01 h23 h34 h24)
    · rw [card_A1, hEc]
      norm_num
  ·
    right
    haveI : Finite A2 := Nat.finite_of_card_ne_zero (by rw [card_A2]; norm_num)
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro x hx
      have hN := h (cm x - 1) ((hmem _).2 ⟨x, hx, rfl⟩)
      obtain ⟨h01, h12, h34, h02⟩ := hN
      exact (mem_patSub hSA2).2 (supp_SA2 (isUp_cm_sub_one (hET hx)) h01 h12 h34 h02)
    · rw [card_A2, hEc]
      norm_num

end CFSG.Quasithin.A94.L52
