module

public import CFSG.Quasithin.Recognition.F112Crit.Setting

import CFSG.Quasithin.Recognition.Stroth.Str86CaseIBasics
public import CFSG.Quasithin.Recognition.Stroth.BenderH7

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise

section Generic

variable {G : Type*} [Group G]

structure CritHypN (G₀ G₁ G₂ T Z : Subgroup G) : Prop where
  amalgam : AmalgamHyp G₀ G₁ G₂ T
  ne_bot : Z ≠ ⊥
  normalizes : G₁ ≤ Subgroup.normalizer (Z : Set G)

namespace CritHypN

variable {G₀ G₁ G₂ T Z : Subgroup G}

theorem Zv_le_ballStab_smul_iff (hc : CritHypN G₀ G₁ G₂ T Z) (g : ↥G₀)
    (μ : CosetGeom G₀ G₁ G₂) :
    Vv Z (g • γ₀ G₀ G₁ G₂) ≤ ballStab 1 (g • μ) ↔ Z ≤ ballStab 1 μ := by
  rw [CosetGeom.Vv_smul_γ₀ hc.normalizes g, CosetGeom.ballStab_smul,
    F112Crit.conjSub_le_conjSub_iff]

variable [Finite G]

theorem critB_set_nonempty (hc : CritHypN G₀ G₁ G₂ T Z) :
    {n : ℕ | ∃ μ ∈ sphere n (γ₀ G₀ G₁ G₂), ¬ Z ≤ ballStab 1 μ}.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have h : ∀ μ : CosetGeom G₀ G₁ G₂, Z ≤ ballStab 1 μ := fun μ => by
    by_contra hμ
    have : CosetGeom.dist (γ₀ G₀ G₁ G₂) μ ∈
        {n : ℕ | ∃ μ ∈ sphere n (γ₀ G₀ G₁ G₂), ¬ Z ≤ ballStab 1 μ} := ⟨μ, rfl, hμ⟩
    rw [hne] at this
    exact this
  obtain ⟨n, -, hbot⟩ := CosetGeom.exists_ballStab_eq_bot hc.amalgam
  have hZ : Z ≤ ballStab n (γ₀ G₀ G₁ G₂) := fun x hx =>
    CosetGeom.mem_ballStab.mpr fun δ _ => CosetGeom.ballStab_le_stab 1 δ (h δ hx)
  rw [hbot] at hZ
  exact hc.ne_bot (le_bot_iff.mp hZ)

theorem lt_critB_imp (hc : CritHypN G₀ G₁ G₂ T Z) {μ : CosetGeom G₀ G₁ G₂}
    (hμ : CosetGeom.dist (γ₀ G₀ G₁ G₂) μ < F112Crit.critB G₀ G₁ G₂ Z) : Z ≤ ballStab 1 μ := by
  by_contra h
  exact absurd (Nat.sInf_le (s := {n : ℕ | ∃ μ ∈ sphere n (γ₀ G₀ G₁ G₂), ¬ Z ≤ ballStab 1 μ})
    ⟨μ, rfl, h⟩) (not_le.mpr hμ)

theorem exists_dist_eq_critB (hc : CritHypN G₀ G₁ G₂ T Z) :
    ∃ μ : CosetGeom G₀ G₁ G₂, CosetGeom.dist (γ₀ G₀ G₁ G₂) μ = F112Crit.critB G₀ G₁ G₂ Z ∧
      ¬ Z ≤ ballStab 1 μ := by
  obtain ⟨μ, hμ, hμ'⟩ := Nat.sInf_mem (critB_set_nonempty hc)
  exact ⟨μ, hμ, hμ'⟩

theorem le_critB_iff (hc : CritHypN G₀ G₁ G₂ T Z) (k : ℕ) :
    k ≤ F112Crit.critB G₀ G₁ G₂ Z ↔
      ∀ μ : CosetGeom G₀ G₁ G₂, CosetGeom.dist (γ₀ G₀ G₁ G₂) μ < k → Z ≤ ballStab 1 μ := by
  refine ⟨fun hk μ hμ => lt_critB_imp hc (lt_of_lt_of_le hμ hk), fun h => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨μ, hμ, hμ'⟩ := exists_dist_eq_critB hc
  exact hμ' (h μ (hμ ▸ hlt))

theorem le_critB_iff_at (hc : CritHypN G₀ G₁ G₂ T Z) {γ : CosetGeom G₀ G₁ G₂}
    (hγ : vtype γ = false) (k : ℕ) :
    k ≤ F112Crit.critB G₀ G₁ G₂ Z ↔
      ∀ μ : CosetGeom G₀ G₁ G₂, CosetGeom.dist γ μ < k → Vv Z γ ≤ ballStab 1 μ := by
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hγ
  rw [le_critB_iff hc]
  constructor
  · intro h μ hμ
    obtain ⟨μ', rfl⟩ : ∃ μ', μ = g • μ' := ⟨g⁻¹ • μ, by simp⟩
    rw [CosetGeom.dist_smul] at hμ
    exact (Zv_le_ballStab_smul_iff hc g μ').mpr (h μ' hμ)
  · intro h μ' hμ'
    refine (Zv_le_ballStab_smul_iff hc g μ').mp (h (g • μ') ?_)
    rwa [CosetGeom.dist_smul]

theorem le_stab_of_dist_le (hc : CritHypN G₀ G₁ G₂ T Z) (hb : 1 ≤ F112Crit.critB G₀ G₁ G₂ Z)
    {μ : CosetGeom G₀ G₁ G₂}
    (hμ : CosetGeom.dist (γ₀ G₀ G₁ G₂) μ ≤ F112Crit.critB G₀ G₁ G₂ Z) : Z ≤ stab μ := by
  rcases Nat.eq_zero_or_pos (CosetGeom.dist (γ₀ G₀ G₁ G₂) μ) with h0 | hpos
  · rw [← (CosetGeom.dist_eq_zero_iff hc.amalgam.gen).mp h0]
    exact (lt_critB_imp hc (by rw [CosetGeom.dist_self]; omega)).trans
      (CosetGeom.ballStab_le_stab 1 _)
  · obtain ⟨d, hd⟩ : ∃ d, CosetGeom.dist (γ₀ G₀ G₁ G₂) μ = d + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    obtain ⟨ν, hμν, hν⟩ := CosetGeom.exists_adj_dist_eq hc.amalgam.gen hd
    exact (lt_critB_imp hc (by omega)).trans (CosetGeom.ballStab_le_stab_of_dist_le
      (CosetGeom.dist_eq_one_iff_adj.mpr hμν.symm).le)

theorem le_stab_of_dist_le_at (hc : CritHypN G₀ G₁ G₂ T Z)
    (hb : 1 ≤ F112Crit.critB G₀ G₁ G₂ Z) {γ μ : CosetGeom G₀ G₁ G₂} (hγ : vtype γ = false)
    (hμ : CosetGeom.dist γ μ ≤ F112Crit.critB G₀ G₁ G₂ Z) : Vv Z γ ≤ stab μ := by
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hγ
  obtain ⟨μ', rfl⟩ : ∃ μ', μ = g • μ' := ⟨g⁻¹ • μ, by simp⟩
  rw [CosetGeom.dist_smul] at hμ
  rw [CosetGeom.Vv_smul_γ₀ hc.normalizes g, CosetGeom.stab_smul,
    F112Crit.conjSub_le_conjSub_iff]
  exact le_stab_of_dist_le hc hb hμ

end CritHypN

end Generic

section Str86

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev str86CritB (L1 L2 S : Subgroup G) : ℕ :=
  F112Crit.critB (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) (Z2 L1 L2 S)

theorem str86_critHypN {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (h1 : VU3Big L1) (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    CritHypN (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) S (Z2 L1 L2 S) where
  amalgam := F112W.amalgamHyp_alpha (Hyp111R.of_hyp111 rankOneListedFacts hF.1)
  ne_bot := by
    obtain ⟨hZ1eq, hZ1Z2, -, -, -⟩ := str86_caseI_basics hF hSB h1 hB2 h2 hZI
    intro hbot
    apply omegaOneCenterOf_ne_bot_of_hyp111 hF.1
    rw [← hZ1eq]
    exact le_bot_iff.mp (hZ1Z2.trans (le_of_eq hbot))
  normalizes := SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S)

end Str86

end CFSG.Quasithin.Stroth

end
