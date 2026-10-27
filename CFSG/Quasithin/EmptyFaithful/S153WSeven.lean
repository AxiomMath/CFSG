module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S153WAU

public section

namespace CFSG.QuasithinUnique.AppCS2W

open CFSG.QuasithinUnique.AppCS2 CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G}

namespace WDbl

variable {t : G} (D : WDbl H S L t)
include D

theorem exists_good {M₀ : Subgroup G} (hC52 : C5.NoCommonNormal S H M₀) (hSM : S ≤ M₀)
    (h2 : S.relIndex M₀ = 2) :
    ∃ x ∈ M₀, x ∉ S ∧ ⁅blockU L, conjR (blockU L) x⁆ ≠ ⊥ := by
  have hne : S ≠ M₀ := by
    intro h
    rw [← h] at h2
    simp at h2
  obtain ⟨x, hxM, hxS⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
  have hxN : x ∈ normalizer (S : Set G) := normalizer_of_relIndex_two hSM h2 hxM
  have hnot := D.not_conj_le_of_mem_diff hC52 hSM h2 hxM hxS
  have hVS : conjR (blockU L) x ≤ S := by
    have := C5.conjSubgroup_mono D.blockU_le_S x
    rwa [C5.conjSubgroup_eq_self hxN] at this
  have hVc : ¬ conjR (blockU L) x ≤ centralizer ((U0 L t : Subgroup G) : Set G) := by
    intro h
    apply hnot
    intro v hv
    rw [← D.campbell_pkg.2.2.2]
    exact Subgroup.mem_inf.2 ⟨hVS hv, Subgroup.mem_centralizer_iff.2 fun u hu =>
      Subgroup.mem_centralizer_iff.1 (h hv) u hu⟩
  obtain ⟨v, hv, hvc⟩ : ∃ v ∈ conjR (blockU L) x,
      v ∉ centralizer ((U0 L t : Subgroup G) : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hVc hcon
  obtain ⟨u, hu, hnc⟩ : ∃ u ∈ U0 L t, ¬ u * v = v * u := by
    by_contra hcon
    push Not at hcon
    exact hvc (Subgroup.mem_centralizer_iff.2 hcon)
  obtain ⟨a, ha, b, hb, rfl⟩ := D.exists_mul_of_mem_U0 hu
  by_cases hav : a * v = v * a
  ·
    have hbv : ¬ b * v = v * b := by
      intro hbv
      apply hnc
      calc a * b * v = a * (b * v) := by group
        _ = a * (v * b) := by rw [hbv]
        _ = (a * v) * b := by group
        _ = (v * a) * b := by rw [hav]
        _ = v * (a * b) := by group
    refine ⟨x * t⁻¹, M₀.mul_mem hxM (M₀.inv_mem (hSM D.ht)), ?_, ?_⟩
    · intro h
      apply hxS
      have := S.mul_mem h D.ht
      simpa using this
    · intro hbot
      have h1 : ⁅blockU2 L t, conjR (blockU L) x⁆ = ⊥ := by
        have e : conjR ⁅blockU2 L t, conjR (blockU L) x⁆ t⁻¹ =
            ⁅blockU L, conjR (blockU L) (x * t⁻¹)⁆ := by
          have e1 : conjR ⁅blockU2 L t, conjR (blockU L) x⁆ t⁻¹ =
              ⁅conjR (blockU2 L t) t⁻¹, conjR (conjR (blockU L) x) t⁻¹⁆ :=
            C5.conjSubgroup_commutator _ _ t⁻¹
          rw [e1, show conjR (blockU2 L t) t⁻¹ = blockU L from WDbl.conjR_conjR_inv (blockU L) t,
            WDbl.conjR_conjR]
        rw [hbot] at e
        exact Lin2.conjR_eq_bot_iff.1 e
      have hc : b ∈ centralizer (conjR (blockU L) x : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1 hb
      exact hbv (Subgroup.mem_centralizer_iff.1 hc v hv).symm
  · refine ⟨x, hxM, hxS, fun hbot => ?_⟩
    apply hav
    have hc : a ∈ centralizer (conjR (blockU L) x : Set G) := by
      have : blockU L ≤ centralizer (conjR (blockU L) x : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      exact this ha
    exact (Subgroup.mem_centralizer_iff.1 hc v hv).symm

end WDbl

end CFSG.QuasithinUnique.AppCS2W
