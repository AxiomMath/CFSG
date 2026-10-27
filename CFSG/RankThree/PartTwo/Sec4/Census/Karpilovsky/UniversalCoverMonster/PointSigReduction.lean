module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSigTransfer

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec14
open scoped commutatorElement

section

variable {Γ : Type} [Group Γ] [Finite Γ] {A L R : Subgroup Γ} {b : Γ} (d : Data A L R b)

theorem not_bar_le_core {W Q : Subgroup Γ} (hW : W ≤ L ⊔ R) (hQW : Q ≤ W)
    (h : ¬ Q ≤ pPrimeCoreOf 3 W) : ¬ bar d Q ≤ pPrimeCoreOf 3 (bar d W) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hle
  apply h
  set O := pPrimeCoreOf 3 (bar d W) with hO
  have hO3 : ¬ 3 ∣ Nat.card O := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 (bar d W)) h3
  set M : Subgroup Γ := W ⊓ (O.comap (rho d)).map (L ⊔ R).subtype with hM
  have hmem : ∀ g : Γ, g ∈ M ↔ g ∈ W ∧ ∃ hg : g ∈ L ⊔ R, rho d ⟨g, hg⟩ ∈ O := by
    intro g
    rw [hM, Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨hgW, y, hy, rfl⟩
      exact ⟨hgW, y.2, hy⟩
    · rintro ⟨hgW, hg, h⟩
      exact ⟨hgW, ⟨⟨g, hg⟩, h, rfl⟩⟩
  have hMW : M ≤ W := inf_le_left
  have hM3 : ¬ 3 ∣ Nat.card M := not_dvd_card_of_no_order_three fun g hg h3 => by
    obtain ⟨-, hgLR, hgO⟩ := (hmem g).mp hg
    have : (rho d ⟨g, hgLR⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨g, hgLR⟩ : ↥(L ⊔ R)) ^ 3 = 1 := Subtype.ext h3
      rw [this, map_one]
    have h1 := eq_one_of_pow_three_of_not_dvd hO3 hgO this
    exact d.eq_one_of_rho_one ⟨g, hgLR⟩ h1 h3
  have hWM : W ≤ Subgroup.normalizer (M : Set Γ) := by
    refine le_normalizer_of_conj_mem fun w hw g hg => ?_
    obtain ⟨hgW, hgLR, hgO⟩ := (hmem g).mp hg
    have hwLR : w ∈ L ⊔ R := hW hw
    have hconjLR : w * g * w⁻¹ ∈ L ⊔ R := mul_mem (mul_mem hwLR hgLR) (inv_mem hwLR)
    refine (hmem _).mpr ⟨W.mul_mem (W.mul_mem hw hgW) (W.inv_mem hw), hconjLR, ?_⟩
    have e : rho d ⟨w * g * w⁻¹, hconjLR⟩ =
        rho d ⟨w, hwLR⟩ * rho d ⟨g, hgLR⟩ * (rho d ⟨w, hwLR⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    have hrw : rho d ⟨w, hwLR⟩ ∈ bar d W := rho_mem_bar d hwLR hw
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pPrimeCoreOf 3 (bar d W) hrw) _).mp hgO
  have hMcore : M ≤ pPrimeCoreOf 3 W :=
    le_pPrimeCoreOf hMW hWM ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hM3)
  intro q hq
  refine hMcore ((hmem q).mpr ⟨hQW hq, hW (hQW hq), ?_⟩)
  exact hle (rho_mem_bar d (hW (hQW hq)) hq)

end

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig
