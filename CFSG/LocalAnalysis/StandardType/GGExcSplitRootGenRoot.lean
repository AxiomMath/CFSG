module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignLevi
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignLevi
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignLevi
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.QuasithinDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.ExcSplitRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {p : ℕ}

section Helpers

open CFSG.LieType.Steinberg.Adjoint

private theorem exists_smul_of_forall_sum_eq_zero {r : ℕ} [Fact p.Prime]
    {α β : Fin r → ℤ}
    (h : ∀ t : Fin r → ZMod p, ∑ j, (α j : ZMod p) * t j = 0 →
      ∑ j, (β j : ZMod p) * t j = 0) :
    ∃ c : ZMod p, ∀ j, (β j : ZMod p) = c * (α j : ZMod p) := by
  have hsingle : ∀ (v : Fin r → ℤ) (i : Fin r),
      ∑ l, (v l : ZMod p) * (Pi.single i 1 : Fin r → ZMod p) l = (v i : ZMod p) := by
    intro v i
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  by_cases hα : ∃ k, (α k : ZMod p) ≠ 0
  · obtain ⟨k, hk⟩ := hα
    refine ⟨(β k : ZMod p) * ((α k : ZMod p))⁻¹, fun j => ?_⟩
    by_cases hjk : j = k
    · subst hjk
      rw [mul_assoc, inv_mul_cancel₀ hk, mul_one]
    · set c₀ : ZMod p := (α j : ZMod p) * ((α k : ZMod p))⁻¹ with hc₀
      have hαj : ∑ i, (α i : ZMod p) * (Pi.single j 1 : Fin r → ZMod p) i =
          (α j : ZMod p) := hsingle α j
      have hαk : ∑ i, (α i : ZMod p) * (Pi.single k 1 : Fin r → ZMod p) i =
          (α k : ZMod p) := hsingle α k
      have hβj : ∑ i, (β i : ZMod p) * (Pi.single j 1 : Fin r → ZMod p) i =
          (β j : ZMod p) := hsingle β j
      have hβk : ∑ i, (β i : ZMod p) * (Pi.single k 1 : Fin r → ZMod p) i =
          (β k : ZMod p) := hsingle β k
      have hsumα : ∑ i, (α i : ZMod p) * ((Pi.single j 1 : Fin r → ZMod p) i -
          c₀ * (Pi.single k 1 : Fin r → ZMod p) i) = 0 := by
        calc ∑ i, (α i : ZMod p) * ((Pi.single j 1 : Fin r → ZMod p) i -
              c₀ * (Pi.single k 1 : Fin r → ZMod p) i)
            = ∑ i, ((α i : ZMod p) * (Pi.single j 1 : Fin r → ZMod p) i -
                c₀ * ((α i : ZMod p) * (Pi.single k 1 : Fin r → ZMod p) i)) :=
              Finset.sum_congr rfl fun i _ => by ring
          _ = (∑ i, (α i : ZMod p) * (Pi.single j 1 : Fin r → ZMod p) i) -
                ∑ i, c₀ * ((α i : ZMod p) * (Pi.single k 1 : Fin r → ZMod p) i) :=
              Finset.sum_sub_distrib _ _
          _ = (∑ i, (α i : ZMod p) * (Pi.single j 1 : Fin r → ZMod p) i) -
                c₀ * ∑ i, (α i : ZMod p) * (Pi.single k 1 : Fin r → ZMod p) i := by
              rw [Finset.mul_sum]
          _ = (α j : ZMod p) - c₀ * (α k : ZMod p) := by rw [hαj, hαk]
          _ = 0 := by rw [hc₀, mul_assoc, inv_mul_cancel₀ hk, mul_one, sub_self]
      have hsumβ : ∑ i, (β i : ZMod p) * ((Pi.single j 1 : Fin r → ZMod p) i -
          c₀ * (Pi.single k 1 : Fin r → ZMod p) i) =
          (β j : ZMod p) - c₀ * (β k : ZMod p) := by
        calc ∑ i, (β i : ZMod p) * ((Pi.single j 1 : Fin r → ZMod p) i -
              c₀ * (Pi.single k 1 : Fin r → ZMod p) i)
            = ∑ i, ((β i : ZMod p) * (Pi.single j 1 : Fin r → ZMod p) i -
                c₀ * ((β i : ZMod p) * (Pi.single k 1 : Fin r → ZMod p) i)) :=
              Finset.sum_congr rfl fun i _ => by ring
          _ = (∑ i, (β i : ZMod p) * (Pi.single j 1 : Fin r → ZMod p) i) -
                ∑ i, c₀ * ((β i : ZMod p) * (Pi.single k 1 : Fin r → ZMod p) i) :=
              Finset.sum_sub_distrib _ _
          _ = (∑ i, (β i : ZMod p) * (Pi.single j 1 : Fin r → ZMod p) i) -
                c₀ * ∑ i, (β i : ZMod p) * (Pi.single k 1 : Fin r → ZMod p) i := by
              rw [Finset.mul_sum]
          _ = (β j : ZMod p) - c₀ * (β k : ZMod p) := by rw [hβj, hβk]
      have hb := h _ hsumα
      rw [hsumβ] at hb
      rw [sub_eq_zero.1 hb, hc₀]
      ring
  · push Not at hα
    refine ⟨0, fun j => ?_⟩
    have ht : ∑ i, (α i : ZMod p) * (Pi.single j 1 : Fin r → ZMod p) i = 0 := by
      rw [Finset.sum_eq_single j]
      · simp [hα]
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, mul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have hb := h _ ht
    rw [Finset.sum_eq_single j] at hb
    · simpa using hb
    · intro b _ hb'
      rw [Pi.single_eq_of_ne hb', mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj

private theorem iform_self_root_cases
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    iform α α = 2 ∨ iform α α = 4 := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact Or.inl (SimplyLacedCover.iform_self_eq_two (τ := .E6)
      (fun i => by simp [Tag.symmetrizer]) hα)
  · exact Or.inl (SimplyLacedCover.iform_self_eq_two (τ := .E7)
      (fun i => by simp [Tag.symmetrizer]) hα)
  · exact Or.inl (SimplyLacedCover.iform_self_eq_two (τ := .E8)
      (fun i => by simp [Tag.symmetrizer]) hα)
  · exact CFSG.SeitzReduction.F4Pilot.iform_self_eq_two_or_four hα

private theorem abs_iform_le_three
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hαα : iform α α = 2 ∨ iform α α = 4) (hββ : iform β β = 2 ∨ iform β β = 4)
    (hne : α ≠ β) (hne' : α ≠ -β) : |iform α β| ≤ 3 := by
  have hprod : iform α α * iform β β ≤ 16 := by
    rcases hαα with h | h <;> rcases hββ with h' | h' <;> rw [h, h'] <;> norm_num
  have hq2 : iform α β ^ 2 < 16 := by
    have := iform_sq_lt hα hβ hne hne'
    linarith
  rw [abs_le]
  constructor
  · have h : (-4 : ℤ) < iform α β := by nlinarith [sq_nonneg (iform α β + 4)]
    omega
  · have h : iform α β < 4 := by nlinarith [sq_nonneg (iform α β - 4)]
    omega

private theorem eq_or_eq_neg_of_norm_bound
    [Fact p.Prime] (hp2 : p ≠ 2)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hαα : iform α α = 2 ∨ iform α α = 4) (hββ : iform β β = 2 ∨ iform β β = 4)
    (h : ∀ t : Fin τ.rank → ZMod p, ∑ j, (α j : ZMod p) * t j = 0 →
      ∑ j, (β j : ZMod p) * t j = 0) :
    β = α ∨ β = -α := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨c, hc⟩ := exists_smul_of_forall_sum_eq_zero (p := p) h
  set c' : ℤ := c.valMinAbs with hc'def
  have hc'cast : (c' : ZMod p) = c := ZMod.coe_valMinAbs c
  have hdiv : ∀ j, (p : ℤ) ∣ β j - c' * α j := by
    intro j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hc j, hc'cast]
    ring
  choose v hv using hdiv
  have hu : β - c' • α = (p : ℤ) • v := by
    ext j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact hv j
  have hexp : iform (β - c' • α) (β - c' • α) =
      iform β β - 2 * (c' * iform α β) + c' ^ 2 * iform α α := by
    rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_smul_left,
      iform_smul_right, iform_smul_left, iform_smul_right, iform_comm β α]
    ring
  have hexp2 : (iform (β - c' • α) (β - c' • α) : ZMod 2) = 0 := by
    have h2 : (2 : ZMod 2) = 0 := by decide
    have hα2 : (iform α α : ZMod 2) = 0 := by
      rcases hαα with h | h <;> rw [h] <;> decide
    have hβ2 : (iform β β : ZMod 2) = 0 := by
      rcases hββ with h | h <;> rw [h] <;> decide
    rw [hexp]
    push_cast
    rw [hβ2, hα2, h2]
    ring
  by_contra hcon
  push Not at hcon
  have hne : α ≠ β := fun h' => hcon.1 h'.symm
  have hne' : α ≠ -β := fun h' => hcon.2 (by rw [h', neg_neg])
  have hu_ne : β - c' • α ≠ 0 := by
    intro h0
    have hβeq : β = c' • α := sub_eq_zero.1 h0
    have hnot : ¬ CFSG.LieType.Steinberg.LinIndepPair β α := by
      intro hlin
      have hz : (1 : ℤ) • β + (-c') • α = 0 := by
        rw [one_smul, neg_smul, ← sub_eq_add_neg, hβeq, sub_self]
      exact one_ne_zero (hlin 1 (-c') hz).1
    rcases CFSG.LieType.Steinberg.TagRoots.eq_or_eq_neg_of_not_linIndepPair
      hβ hα hnot with h' | h'
    · exact hcon.1 h'
    · exact hcon.2 h'
  have hv_ne : v ≠ 0 := by
    intro hv0
    exact hu_ne (by rw [hu, hv0, smul_zero])
  have hvv_pos : 0 < iform v v := iform_self_pos hv_ne
  have hvv_even : 2 ∣ iform v v := by
    have h1 := hexp2
    have hsq : iform (β - c' • α) (β - c' • α) = (p : ℤ) ^ 2 * iform v v := by
      rw [hu, iform_smul_left, iform_smul_right]
      ring
    rw [hsq] at h1
    have hp2z : (p : ZMod 2) = 1 := by
      obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [ht]
      push_cast
      rw [h2]
      ring
    push_cast at h1
    rw [hp2z] at h1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (iform v v) 2).1 (by simpa using h1)
  have hvv_ge : (2 : ℤ) ≤ iform v v := by
    obtain ⟨l, hl⟩ := hvv_even
    have hl0 : 0 < l := by nlinarith
    nlinarith
  have hlow : 2 * (p : ℤ) ^ 2 ≤ iform (β - c' • α) (β - c' • α) := by
    rw [hu, iform_smul_left, iform_smul_right]
    nlinarith [hvv_ge]
  have hq_abs : |iform α β| ≤ 3 := abs_iform_le_three hα hβ hαα hββ hne hne'
  have hB2 : 2 * (((p - 1) / 2 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    have hk' : ((p - 1) / 2 : ℕ) = k := by omega
    rw [hk', hk]
    push_cast
    ring
  have hBnonneg : (0 : ℤ) ≤ (((p - 1) / 2 : ℕ) : ℤ) := by positivity
  have hc'bound : |c'| ≤ (((p - 1) / 2 : ℕ) : ℤ) := by
    have hle : c'.natAbs ≤ (p - 1) / 2 := by
      have h0 := ZMod.natAbs_valMinAbs_le c
      have hpdiv : p / 2 = (p - 1) / 2 := by omega
      rwa [hpdiv] at h0
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hle
  have hkey : 4 + 6 * (((p - 1) / 2 : ℕ) : ℤ) + 4 * (((p - 1) / 2 : ℕ) : ℤ) ^ 2 =
      (p : ℤ) ^ 2 + p + 2 := by
    have hk' : ((p - 1) / 2 : ℕ) = k := by omega
    rw [hk', hk]
    push_cast
    ring
  have hubound : iform (β - c' • α) (β - c' • α) ≤ (p : ℤ) ^ 2 + p + 2 := by
    have hααle : iform α α ≤ 4 := by rcases hαα with h' | h' <;> omega
    have hααnonneg : (0 : ℤ) ≤ iform α α := by rcases hαα with h' | h' <;> omega
    have hββle : iform β β ≤ 4 := by rcases hββ with h' | h' <;> omega
    have hq := abs_le.1 hq_abs
    have hcabs := abs_le.1 hc'bound
    have hPabs : |c' * iform α β| ≤ 3 * (((p - 1) / 2 : ℕ) : ℤ) := by
      rw [abs_mul]
      calc |c'| * |iform α β| ≤ (((p - 1) / 2 : ℕ) : ℤ) * 3 :=
            mul_le_mul hc'bound hq_abs (abs_nonneg _) hBnonneg
        _ = 3 * (((p - 1) / 2 : ℕ) : ℤ) := by ring
    have hP := abs_le.1 hPabs
    have hsq : c' ^ 2 ≤ (((p - 1) / 2 : ℕ) : ℤ) ^ 2 := sq_le_sq' hcabs.1 hcabs.2
    have hsq2 : c' ^ 2 * iform α α ≤ 4 * (((p - 1) / 2 : ℕ) : ℤ) ^ 2 := by
      calc c' ^ 2 * iform α α ≤ (((p - 1) / 2 : ℕ) : ℤ) ^ 2 * iform α α :=
            mul_le_mul_of_nonneg_right hsq hααnonneg
        _ ≤ (((p - 1) / 2 : ℕ) : ℤ) ^ 2 * 4 :=
            mul_le_mul_of_nonneg_left hααle (sq_nonneg _)
        _ = 4 * (((p - 1) / 2 : ℕ) : ℤ) ^ 2 := by ring
    rw [hexp]
    nlinarith [hββle, hP.1, hP.2, hsq2, hkey]
  have hp3z : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  nlinarith [hlow, hubound]

end Helpers

theorem eq_or_eq_neg_of_forall_sum_eq_zero
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    [Fact p.Prime] (hp2 : p ≠ 2) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (h : ∀ t : Fin τ.rank → ZMod p, ∑ j, (α j : ZMod p) * t j = 0 →
      ∑ j, (β j : ZMod p) * t j = 0) :
    β = α ∨ β = -α :=
  eq_or_eq_neg_of_norm_bound hp2 hα hβ
    (iform_self_root_cases hτ hα) (iform_self_root_cases hτ hβ) h

end CFSG.StandardType.ExcSplitRootGen
