module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.Blueprint.LieModelAPI
public import CFSG.CGT.Timmesfeld75.L2Real

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms

theorem IsL2.isL2Ev {X : Type} [Group X] {f : ℕ} (h : IsL2 X f) : IsL2Ev X f := by
  have hf1 : 1 ≤ f := h.admissible.2.1
  obtain ⟨-, hmodel⟩ := CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide) |>.1 h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  haveI : CharP K 2 := uc22p22d_charP_two hf1 hK
  have hZ := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot (K := K)
  let q : StatedProj (StatedSL 2 K) ≃* StatedSL 2 K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans q⟩⟩

theorem card_outer_dvd_of_isL2 {X : Type} [Group X] [Finite X] {f : ℕ} (h : IsL2 X f) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ∣ f := by
  have hL2 : IsL2Ev X f := h.isL2Ev
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := P22y.exists_equiv_psl2 hL2
  have hout := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
    (p := 2) (f := f) Nat.prime_two F hF).2 X ⟨e⟩
  have hf1 : 1 ≤ f := h.admissible.2.1
  have hodd : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  rw [Nat.coprime_two_left.mpr hodd, mul_one] at hout
  exact hout

theorem mem_inner_of_pow_eq_one_of_coprime_card_outer {X : Type} [Group X] [Finite X] {r : ℕ}
    {β : MulAut X} (hβ : β ^ r = 1)
    (hcop : Nat.Coprime r (Nat.card (Outer X))) : β ∈ inner X := by
  let π : MulAut X →* Outer X := QuotientGroup.mk' (inner X)
  have hπr : π β ^ r = 1 := by rw [← map_pow, hβ, map_one]
  have hdvd : orderOf (π β) ∣ r := orderOf_dvd_of_pow_eq_one hπr
  have hcard : orderOf (π β) ∣ Nat.card (Outer X) := orderOf_dvd_natCard _
  have hgcd : Nat.gcd r (Nat.card (Outer X)) = 1 := hcop
  have h1 : orderOf (π β) = 1 := Nat.dvd_one.mp (hgcd ▸ Nat.dvd_gcd hdvd hcard)
  exact (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.mp h1)

theorem exists_mul_self_conj_eq_inv_of_isL2Ev {X : Type} [Group X] [Finite X] {f : ℕ}
    (hL2 : IsL2Ev X f) (x : X) :
    ∃ w : X, w * w = 1 ∧ w * x * w⁻¹ = x⁻¹ := by
  obtain ⟨F, _, _, _, _, ⟨e⟩⟩ := P22y.exists_equiv_sl2 hL2
  obtain ⟨a, ha2, hax⟩ := CFSG.CGT.Timmesfeld75.exists_mul_self_eq_one_conj_eq_inv (e x)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  refine ⟨e.symm a, e.injective ?_, e.injective ?_⟩
  · rw [map_mul, e.apply_symm_apply, ha2, map_one]
  · rw [map_mul, map_mul, e.apply_symm_apply, map_inv, e.apply_symm_apply, hai, hax, map_inv]

end CFSG.LocalAnalysis.UniquenessCase.UC22
