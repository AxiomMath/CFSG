module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_mbar_of_rank (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {n : ℕ}
    (hn : ∀ τ ∈ Mbar D.M V₀ V h.isElemAbelian, τ ^ 2 = 1 → τ ≠ 1 →
      2 ^ (n + 1) ≤ Nat.card ↥(commSub (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian))
        (Subgroup.zpowers τ)))
    (hex : ∃ τ ∈ Mbar D.M V₀ V h.isElemAbelian, τ ^ 2 = 1 ∧ τ ≠ 1) :
    MBarGT D.M V₀ V n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.isElemAbelian
  have hpow : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  rw [Hyp125.mBarGT_iff_lt_mBar h n]
  unfold mBar E3.mParam
  have hev : Even (Nat.card ↥(Mbar D.M V₀ V hV)) := by
    obtain ⟨τ, hτ, hτ2, hτ1⟩ := hex
    have ho : orderOf τ = 2 := orderOf_eq_prime_iff.2 ⟨hτ2, hτ1⟩
    rw [even_iff_two_dvd]
    exact ho ▸ Subgroup.orderOf_dvd_natCard (Mbar D.M V₀ V hV) hτ
  rw [if_pos hev]
  have hmem : sInf {k : ℕ | ∃ t ∈ Mbar D.M V₀ V hV, orderOf t = 2 ∧
      k = rkIdx (fixV (Subgroup.zpowers t))} ∈
      {k : ℕ | ∃ t ∈ Mbar D.M V₀ V hV, orderOf t = 2 ∧
        k = rkIdx (fixV (Subgroup.zpowers t))} := by
    obtain ⟨τ, hτ, hτ2, hτ1⟩ := hex
    exact Nat.sInf_mem ⟨_, τ, hτ, orderOf_eq_prime_iff.2 ⟨hτ2, hτ1⟩, rfl⟩
  obtain ⟨t, ht, hto, hkeq⟩ := hmem
  have ht2 : t ^ 2 = 1 := (orderOf_eq_prime_iff.1 hto).1
  have ht1 : t ≠ 1 := (orderOf_eq_prime_iff.1 hto).2
  have hcard := hn t ht ht2 ht1
  have hcard2 : Nat.card ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV))
      (Subgroup.zpowers t)) = 2 ^ rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV))
        (Subgroup.zpowers t)) :=
    card_eq_two_pow hpow _
  have hrk : n + 1 ≤ rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (Subgroup.zpowers t)) := by
    rw [hcard2] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard
  have hrkidx : n < rkIdx (fixV (Subgroup.zpowers t)) := by
    rw [rkIdx_fixV_zpowers, commV_eq_commSub]
    omega
  rw [hkeq]
  exact hrkidx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
