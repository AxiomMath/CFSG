module

public import CFSG.RankThree.PartOne.S11c.SuFiveAut
public import CFSG.RankThree.PartOne.S11c.SuFiveTorus
public import CFSG.RankThree.PartOne.S11c.SuFiveFrame

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

section Frame

variable {f : ℕ} {K : Type} [Field K]

theorem torusEq_le_gamma5 (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) (i j : Fin 5) :
    torusEq i j K ≤ gamma5 h := by
  have := torusEq_le_unitarySU h h5 i j
  rwa [unitarySU_eq_gramSU h 5] at this

theorem swapUnit_mem_gamma5 (h : UnitaryFieldData 2 f K) (i j : Fin 5) :
    KFSU5.swapUnit K i j ∈ gamma5 h := by
  have := swapUnit_mem_unitarySU h (i := i) (j := j)
  rwa [unitarySU_eq_gramSU h 5] at this

@[expose] noncomputable def frameA (h : UnitaryFieldData 2 f K) (P : unit5 h) (i j : Fin 5) :
    Subgroup (gamma5 h) :=
  ((torusEq i j K).subgroupOf (gamma5 h)).map (primeFormConjSU h _ P).toMonoidHom

@[expose] noncomputable def frameR (h : UnitaryFieldData 2 f K) (P : unit5 h) (i j : Fin 5) :
    gamma5 h :=
  primeFormConjSU h _ P ⟨KFSU5.swapUnit K i j, swapUnit_mem_gamma5 h i j⟩

theorem coe_frameR (h : UnitaryFieldData 2 f K) (P : unit5 h) (i j : Fin 5) :
    ((frameR h P i j : gamma5 h) : GL (Fin 5) K) =
      (P : GL (Fin 5) K) * KFSU5.swapUnit K i j * (P : GL (Fin 5) K)⁻¹ := rfl

theorem exists_of_mem_frameA {h : UnitaryFieldData 2 f K} {P : unit5 h} {i j : Fin 5}
    {a : gamma5 h} (ha : a ∈ frameA h P i j) :
    ∃ t ∈ torusEq i j K, (a : GL (Fin 5) K) = (P : GL (Fin 5) K) * t * (P : GL (Fin 5) K)⁻¹ := by
  obtain ⟨b, hb, rfl⟩ := ha
  exact ⟨(b : GL (Fin 5) K), hb, rfl⟩

theorem isElementaryAbelian_frameA (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    (P : unit5 h) (i j : Fin 5) : IsElementaryAbelian 5 (frameA h P i j) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h1 := isElementaryAbelian_torusEq (K := K) i j
  have h2 : IsElementaryAbelian 5 ((torusEq i j K).subgroupOf (gamma5 h)) :=
    IsElementaryAbelian.subgroupOf (torusEq_le_gamma5 h h5 i j)
  exact IsElementaryAbelian.map (primeFormConjSU h _ P).toMonoidHom

theorem card_frameA (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) (P : unit5 h)
    {i j : Fin 5} (hij : i ≠ j) : Nat.card (frameA h P i j) = 5 ^ 3 := by
  have : Finite K := h.finite
  rw [frameA, Subgroup.card_map_of_injective (primeFormConjSU h _ P).injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (torusEq_le_gamma5 h h5 i j)).toEquiv]
  exact card_torusEq h h5 hij

theorem orderOf_frameR (h : UnitaryFieldData 2 f K) (P : unit5 h) {i j : Fin 5} (hij : i ≠ j) :
    orderOf (frameR h P i j) = 2 := by
  have hsub : orderOf ((frameR h P i j : gamma5 h) : GL (Fin 5) K) = 2 := by
    rw [coe_frameR]
    have : (P : GL (Fin 5) K) * KFSU5.swapUnit K i j * (P : GL (Fin 5) K)⁻¹ =
        MulAut.conj (P : GL (Fin 5) K) (KFSU5.swapUnit K i j) := rfl
    rw [this, MulEquiv.orderOf_eq, KFSU5.orderOf_swapUnit hij]
  rw [← Subgroup.orderOf_coe]
  exact hsub

theorem frameR_comm (h : UnitaryFieldData 2 f K) (P : unit5 h) {i j : Fin 5} {a : gamma5 h}
    (ha : a ∈ frameA h P i j) : a * frameR h P i j = frameR h P i j * a := by
  obtain ⟨t, ht, hat⟩ := exists_of_mem_frameA ha
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_frameR, hat]
  have hc := swapUnit_comm_of_mem_torusEq ht
  calc (P : GL (Fin 5) K) * t * (P : GL (Fin 5) K)⁻¹ *
        ((P : GL (Fin 5) K) * KFSU5.swapUnit K i j * (P : GL (Fin 5) K)⁻¹) =
      (P : GL (Fin 5) K) * (t * KFSU5.swapUnit K i j) * (P : GL (Fin 5) K)⁻¹ := by group
    _ = (P : GL (Fin 5) K) * (KFSU5.swapUnit K i j * t) * (P : GL (Fin 5) K)⁻¹ := by rw [← hc]
    _ = _ := by group

end Frame

section Contradiction

variable {f : ℕ} {K : Type} [Field K]

theorem frame_contradiction {H : Type} [Group H] [Finite H] {L : Subgroup H}
    (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) (ψ : gamma5 h ≃* L) {x : H}
    (hx5 : x ^ 5 = 1) (hxL : x ∉ L) (θ : gamma5 h ≃* gamma5 h)
    (hθ : ∀ g, ((ψ (θ g) : L) : H) = x * ((ψ g : L) : H) * x⁻¹) (P : unit5 h) {i j : Fin 5}
    (hij : i ≠ j) (hA : ∀ a ∈ frameA h P i j, θ a = a) (hr : θ (frameR h P i j) = frameR h P i j) :
    3 < evenRank H := by
  have hcomm : ∀ g : gamma5 h, θ g = g → x * ((ψ g : L) : H) = ((ψ g : L) : H) * x := by
    intro g hg
    have := hθ g
    rw [hg] at this
    calc x * ((ψ g : L) : H) = x * ((ψ g : L) : H) * x⁻¹ * x := by group
      _ = ((ψ g : L) : H) * x := by rw [← this]
  exact three_lt_evenRank_of_frame ψ (isElementaryAbelian_frameA h h5 P i j)
    (card_frameA h h5 P hij) (orderOf_frameR h P hij) (fun a ha => frameR_comm h P ha) hx5 hxL
    (fun a ha => hcomm a (hA a ha)) (hcomm _ hr)

end Contradiction

end CFSG.RankThree.PartOne
