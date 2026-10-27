module

public import CFSG.Quasithin.Background.C124Z3Glaub
public import CFSG.Quasithin.Background.C1PackC126Solv

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.Z3

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.LieType.BorelTits
  CFSG.Quasithin.C126.A5 CFSG.Quasithin.C1Pack

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable {X R Y : Subgroup G} (s : Setup X R Y)

include s

theorem charTwo_P₃ : CharTwo (Y ⊔ baum R) := by
  have hY : CharTwo Y := A4.charTwo_of_normal (le_sup_left : Y ≤ Y ⊔ R₁ X R)
    (fun g hg => s.P₁_le_normalizer hg) s.charTwo_P₁
  exact A4.charTwo_sup hY s.S_norm (s.R_pGroup.to_le s.S_le_R)

theorem isSolvable_P₃ : Group.IsSolvable ↥(Y ⊔ baum R) := by
  have := s.isSolvable_P₁
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective s.P₃_le_P₁)

theorem pRank_le_two_P₃ (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (Y ⊔ baum R) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 (s.R_pGroup.to_le s.S_le_R)
  have h1 := Subgroup.relIndex_mul_card (baum R) (Y ⊔ baum R)
  rw [inf_eq_left.2 (le_sup_right : baum R ≤ Y ⊔ baum R), s.relIndex_S_P₃ hYS] at h1
  exact pRank_le_two_of_card_dvd (a := a) (by rw [← h1, ha, mul_comm])

theorem minParabolic_P₃ (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    MinParabolic (Y ⊔ baum R) (baum R) (baum R) where
  isSylow := s.sylow_S hYS
  not_normal := s.not_P₃_le_normalizer hYS
  uniqueMax := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨⟨s.S_lt_P₃ hYS, fun K hK hKP => ?_⟩, le_rfl⟩, ?_⟩
    · rcases s.sandwich_P₃ hYS hK.le hKP with h | h
      · exact absurd h hK.ne'
      · exact h
    · rintro N ⟨⟨hlt, _⟩, hSN⟩
      rcases s.sandwich_P₃ hYS hSN hlt.le with h | h
      · exact h
      · exact absurd h hlt.ne

theorem twoResidual_P₃ : twoResidual (Y ⊔ baum R) = Y := by
  refine le_antisymm (twoResidual_le_of_isTwoQuotient le_sup_left s.P₃_le_normalizer
    (isTwoQuotient_of_sup_eq (s.R_pGroup.to_le s.S_le_R) s.P₃_le_normalizer (sup_comm _ _))) ?_
  have := twoResidual_mono (le_sup_left : Y ≤ Y ⊔ baum R)
  rwa [s.Y_res] at this

theorem Z_le_Z_S :
    quasithinOmegaOneCenter (R₁ X R) ≤ quasithinOmegaOneCenter (baum R) := by
  unfold quasithinOmegaOneCenter
  rw [Subgroup.closure_le]
  intro z hz
  have hzb : z ∈ baum (R₁ X R) := C1GN.omegaOneCenterOf_le_baum (R₁ X R)
    (Subgroup.subset_closure hz)
  rw [s.baum_R₁] at hzb
  exact Subgroup.subset_closure ⟨⟨hzb, Subgroup.centralizer_le s.S_le_R₁ hz.1.2⟩, hz.2⟩

theorem hJ_S (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    ¬ thompsonJ (baum R) ≤ Subgroup.centralizer (VZ (baum R) (Y ⊔ baum R) : Set G) := by
  intro hJS
  obtain ⟨-, -, hredP⟩ := conjClosure_isTwoReducedIn_of_charTwo (s.sylow_S hYS) s.charTwo_P₃
    (Z := quasithinOmegaOneCenter (baum R)) le_rfl
  by_cases hPV : Y ⊔ baum R ≤ Subgroup.centralizer (VZ (baum R) (Y ⊔ baum R) : Set G)
  · apply s.Y_not_C
    have hZV : quasithinOmegaOneCenter (R₁ X R) ≤ VZ (baum R) (Y ⊔ baum R) :=
      s.Z_le_Z_S.trans (le_conjClosure _ _)
    exact le_sup_left.trans (hPV.trans (Subgroup.centralizer_le hZV))
  · have htfae := MinParabolic.tfae_thompsonJ (s.minParabolic_P₃ hYS) hredP hPV
    have h1 : ⁅VZ (baum R) (Y ⊔ baum R), thompsonJ (baum R)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hJS
    have h3 : baum (baum R) = baum (pCoreOf 2 (Y ⊔ baum R)) := (htfae.out 1 3).1 h1
    rw [C1GN.baum_baum] at h3
    apply s.not_P₃_le_normalizer hYS
    have hh := (le_normalizer_pCoreOf 2 (Y ⊔ baum R)).trans
      (normalizer_le_normalizer_baum (pCoreOf 2 (Y ⊔ baum R)))
    rwa [← h3] at hh

theorem inClassG_P₃ (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    InClassG (Y ⊔ baum R) (baum R) :=
  inClassG_of_solvable_minParabolic (s.minParabolic_P₃ hYS) s.charTwo_P₃ s.isSolvable_P₃
    (s.pRank_le_two_P₃ hYS) (s.hJ_S hYS) (C1GN.baum_baum R)

theorem R_ne_bot : R ≠ ⊥ := by
  intro hR
  apply s.Y_not_C
  have h1 : R₁ X R = ⊥ := le_bot_iff.1 (s.R₁_le_R.trans hR.le)
  have h2 : quasithinOmegaOneCenter (R₁ X R) ≤ R₁ X R := C1GN.omegaOneCenterOf_le_self _
  rw [le_bot_iff.1 (h2.trans (le_of_eq h1))]
  intro y _
  refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
  have hz1 : z = 1 := by simpa using hz
  subst hz1
  simp

theorem dichotomy_all {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂) :
    Y ≤ Subgroup.centralizer (C₁ (baum R) : Set G) ∨
      Y ≤ Subgroup.normalizer (C₂ (baum R) : Set G) ∨
      (IsBlock2 (Y ⊔ baum R) Y ∧ IsAltType Y 3) := by
  have hSp : IsPGroup 2 (baum R) := s.R_pGroup.to_le s.S_le_R
  have hS0 : baum R ≠ ⊥ := C1GN.baum_ne_bot s.R_pGroup s.R_ne_bot
  obtain ⟨-, h1Z, -, -, h2B, h2char, -⟩ := hC.pair (baum R) hSp hS0
  rw [C1GN.baum_baum] at h2B h2char
  by_cases hYS : Y ≤ Subgroup.normalizer (baum R : Set G)
  · right; left
    exact hYS.trans (normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char)
  · have hcls : InClassG (Y ⊔ baum R) (baum (baum R)) := by
      rw [C1GN.baum_baum]
      exact s.inClassG_P₃ hYS
    rcases hC.dichotomy hSp hS0 hcls with h | h | h
    · left
      intro y hy
      refine Subgroup.mem_centralizer_iff.2 fun c hc => ?_
      exact (Subgroup.mem_centralizer_iff.1 (h hc).2 y (Subgroup.mem_sup_left hy)).symm
    · right; left
      exact le_sup_left.trans h
    · right; right
      rw [s.twoResidual_P₃] at h
      exact ⟨h.1, isAltType_three_of_isBlock2_of_solvable h.1 s.isSolvable_P₃⟩

end Setup

end CFSG.Quasithin.C124.Z3
