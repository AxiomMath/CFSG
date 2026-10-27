module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row21Sl2

public section

namespace CFSG.Quasithin

open scoped commutatorElement

namespace Stellmacher.L3YC

namespace Row21

variable {K : Type} [Group K]

theorem not_quasisimple {N : Subgroup K} (hq : CFSG.IsQuasisimple ↥N)
    (hcomm : ⁅(CFSG.oddCore ↥N).map N.subtype, N⁆ ≠ ⊥)
    (hSL : IsSL2 7 (↥N ⧸ CFSG.oddCore ↥N)) : False := by
  obtain ⟨-, hs, -⟩ := hq
  have hPn : ((CFSG.oddCore ↥N).map (QuotientGroup.mk' (Subgroup.center ↥N))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hdich : (CFSG.oddCore ↥N).map (QuotientGroup.mk' (Subgroup.center ↥N)) = ⊥ ∨
      (CFSG.oddCore ↥N).map (QuotientGroup.mk' (Subgroup.center ↥N)) = ⊤ := by
    have := hPn
    exact hs.eq_bot_or_eq_top_of_normal _
  rcases hdich with h | h
  · apply hcomm
    rw [eq_bot_iff, Subgroup.commutator_le]
    rintro _ ⟨o, ho, rfl⟩ g hg
    have hoc : o ∈ Subgroup.center ↥N := by
      have : QuotientGroup.mk' (Subgroup.center ↥N) o ∈ (⊥ : Subgroup (↥N ⧸ Subgroup.center ↥N)) :=
        h ▸ ⟨o, ho, rfl⟩
      exact (QuotientGroup.eq_one_iff o).mp (Subgroup.mem_bot.mp this)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hoc ⟨g, hg⟩)).symm
  · obtain ⟨a, b, hab⟩ := Row21.not_commutative
    obtain ⟨e⟩ := hSL
    apply hab
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    have hcen : ∀ w : ↥N ⧸ CFSG.oddCore ↥N, ∃ z ∈ Subgroup.center ↥N, (QuotientGroup.mk z : _) = w := by
      intro w
      obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective w
      have hw : QuotientGroup.mk' (Subgroup.center ↥N) w' ∈
          (CFSG.oddCore ↥N).map (QuotientGroup.mk' (Subgroup.center ↥N)) := h ▸ Subgroup.mem_top _
      obtain ⟨o, ho, hoe⟩ := hw
      refine ⟨o⁻¹ * w', QuotientGroup.eq.mp hoe, ?_⟩
      rw [QuotientGroup.eq]
      have : (o⁻¹ * w')⁻¹ * w' = w'⁻¹ * o * w' := by group
      rw [this]
      exact (inferInstance : (CFSG.oddCore ↥N).Normal).conj_mem' o ho w'
    obtain ⟨z, hz, rfl⟩ := hcen x
    obtain ⟨z', hz', rfl⟩ := hcen y
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      Subgroup.mem_center_iff.mp hz' z]

theorem natural_of_strong {N : Subgroup K} (hA : A36Strong N)
    (hcomm : ⁅(CFSG.oddCore ↥N).map N.subtype, N⁆ ≠ ⊥)
    (hSL : IsSL2 7 (↥N ⧸ CFSG.oddCore ↥N)) :
    NaturalSL2Action 7 ↥N (CFSG.fittingSubgroup ↥N) ∧
      CFSG.fittingSubgroup ↥N = CFSG.oddCore ↥N := by
  obtain ⟨hconcl, hcommon, -⟩ := hA
  have hFO : CFSG.fittingSubgroup ↥N = CFSG.oddCore ↥N := hcommon.1
  have hO : (CFSG.oddCore ↥N).index = 336 := by
    obtain ⟨e⟩ := hSL
    rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv, card_sl2_seven]
  rcases hconcl with ⟨hc, -⟩ | ⟨hc, -⟩ | h3 | h4
  · exact (not_quasisimple hc.1 hcomm hSL).elim
  · exact (not_quasisimple hc.1 hcomm hSL).elim
  · obtain ⟨p, hp, hp3, -, -, hnat⟩ := h3
    have : Fact p.Prime := ⟨hp⟩
    have hnat' := hnat
    obtain ⟨e, ψ, hsurj, hker, -⟩ := hnat'
    have hidx : (CFSG.fittingSubgroup ↥N).index = p * (p ^ 2 - 1) := by
      rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, card_sl2]
    rw [hFO, hO] at hidx
    have hp7 : p = 7 := by
      have hle : p ≤ 7 := by
        by_contra hlt
        push Not at hlt
        have h1 : 64 ≤ p ^ 2 := by nlinarith
        have : 8 * 63 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
      interval_cases p <;> first | rfl | omega
    subst hp7
    exact ⟨hnat, hFO⟩
  · obtain ⟨-, -, h5, -⟩ := h4
    obtain ⟨e⟩ := h5
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h120 : (CFSG.fittingSubgroup ↥N).index = 120 := by
      rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv, card_sl2]
      norm_num
    rw [hFO, hO] at h120
    omega

end Row21

end Stellmacher.L3YC

end CFSG.Quasithin
