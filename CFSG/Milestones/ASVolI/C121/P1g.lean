module

public import CFSG.Milestones.ASVolI.C121.P1f

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

namespace burnsideC121_YCtx

variable {Ω : Type} [Group Ω] [Finite Ω] {X R T Y W : Subgroup Ω}
  (c : burnsideC121_YCtx X R T Y W) {n : ℕ} {F : Type} [Field F] [Fintype F]
  (D : burnsideC121_NatD Y W n F)

include c

theorem twoResidual_YS : twoResidual (Y ⊔ baum T) = Y := by
  refine le_antisymm (twoResidual_le_of_isTwoQuotient le_sup_left c.YS_le_normalizer
    (B6.isTwoQuotient_of_sup_eq c.S_pGroup c.YS_le_normalizer (sup_comm _ _))) ?_
  have := C126.A5.twoResidual_mono (le_sup_left : Y ≤ Y ⊔ baum T)
  rwa [c.twoResidual_Y] at this

include D

theorem T_ne_bot : T ≠ ⊥ := by
  intro hT
  have hQ : pCoreOf 2 X = ⊥ := le_bot_iff.1 (c.QR.trans (c.RT.trans hT.le))
  have hX : X ≤ ⊥ := by
    have h := c.charTwo
    unfold CharTwo at h
    rw [hQ] at h
    intro x hx
    refine h ⟨hx, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hg
    rw [hg, one_mul, mul_one]
  apply c.not_le_pCore D
  intro y hy
  have : y = 1 := Subgroup.mem_bot.1 (hX (c.hY.le hy))
  rw [this]
  exact Subgroup.one_mem _

theorem S_ne_bot : baum T ≠ ⊥ := C1GN.baum_ne_bot c.hT (c.T_ne_bot D)

theorem inClassG_YS (h610 : B_6_10) (h123 : I_2_3)
    (hYS : ¬ Y ≤ Subgroup.normalizer (baum T : Set Ω)) :
    IsSylowTwoOf (baum T) (Y ⊔ baum T) ∧ InClassG (Y ⊔ baum T) (baum T) := by
  by_cases hn : 2 ≤ n
  · obtain ⟨hSyl, -⟩ := c.b610 D h610 hn hYS
    obtain ⟨M₁, hM₁⟩ := c.minParabolic_YS D hYS hSyl
    exact ⟨hSyl, hSyl, c.charTwo_YS, (minParabolic_iff.1 hM₁).1,
      c.hasNaturalFstar_n2 D h610 h123 hn hYS⟩
  · have hn1 : n = 1 := by have := D.one_le; omega
    obtain ⟨hSyl, -⟩ := c.e23 D hn1 hYS
    obtain ⟨M₁, hM₁⟩ := c.minParabolic_YS D hYS hSyl
    refine ⟨hSyl, ?_⟩
    have hF₁ : CharTwo (Y ⊔ baum T) := c.charTwo_YS
    have hsolv : Group.IsSolvable ↥(Y ⊔ baum T) :=
      F1.isSolvable_sup_of_le_normalizer (c.isSolvable_Y D hn1)
        (F1.isSolvable_of_isPGroup_two c.S_pGroup) c.S_le_normalizer
    have hsyl : IsSylowTwoOf (baum T ⊓ Y) Y :=
      A4.isSylowTwoOf_inf_normal hSyl le_sup_left c.YS_le_normalizer
    have hO : pCoreOf 2 Y ≤ baum T := (B6.pCoreOf_two_le_of_isSylowTwoOf hsyl).trans inf_le_left
    have hSY : Y ⊓ baum T = pCoreOf 2 Y := by
      rw [inf_comm]
      exact CFSG.Quasithin.C124.Z3.eq_of_relIndex_three_of_isPGroup (le_inf hO (pCoreOf_le 2 Y))
        inf_le_right (c.relIndex_pCore_three D hn1) (c.S_pGroup.to_le inf_le_left)
    have hcard : Nat.card ↥(Y ⊔ baum T) = 3 * Nat.card ↥(baum T) := by
      have h1 := C126.A5.card_sup_mul_card_inf_of_le_normalizer c.S_le_normalizer
      rw [hSY] at h1
      have h2 := Subgroup.relIndex_mul_card (pCoreOf 2 Y) Y
      rw [inf_eq_left.2 (pCoreOf_le 2 Y), c.relIndex_pCore_three D hn1] at h2
      have hpos : 0 < Nat.card ↥(pCoreOf 2 Y) := Nat.card_pos
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [h1, ← h2]
      ring
    have hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (Y ⊔ baum T) ≤ 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 c.S_pGroup
      exact C124.Z3.pRank_le_two_of_card_dvd (a := a) (by rw [hcard, ha, mul_comm])
    obtain ⟨-, -, hred₁⟩ := conjClosure_isTwoReducedIn_of_charTwo hSyl hF₁
      (Z := quasithinOmegaOneCenter (baum T)) le_rfl
    have hHV : ¬ Y ⊔ baum T ≤
        Subgroup.centralizer (VZ (baum T) (Y ⊔ baum T) : Set Ω) := by
      intro h
      apply c.not_le_centralizer_omega_n1 D hn1 hYS
      exact le_sup_left.trans (h.trans (Subgroup.centralizer_le (le_conjClosure _ _)))
    have hJ : ¬ thompsonJ (baum T) ≤
        Subgroup.centralizer (VZ (baum T) (Y ⊔ baum T) : Set Ω) := by
      intro hJS
      have htfae := MinParabolic.tfae_thompsonJ hM₁ hred₁ hHV
      have h1 : ⁅VZ (baum T) (Y ⊔ baum T), thompsonJ (baum T)⁆ = ⊥ := by
        rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact hJS
      have h3 : baum (baum T) = baum (pCoreOf 2 (Y ⊔ baum T)) := (htfae.out 1 3).1 h1
      rw [C1GN.baum_baum] at h3
      apply hYS
      have hh := (le_normalizer_pCoreOf 2 (Y ⊔ baum T)).trans
        (normalizer_le_normalizer_baum (pCoreOf 2 (Y ⊔ baum T)))
      rw [← h3] at hh
      exact le_sup_left.trans hh
    exact C1Pack.inClassG_of_solvable_minParabolic hM₁ hF₁ hsolv hSQT hJ (C1GN.baum_baum T)

end burnsideC121_YCtx

theorem burnsideC121_part1 (h610 : B_6_10) (h123 : I_2_3) {Ω : Type} [Group Ω] [Finite Ω]
    {C₁ C₂ : Subgroup Ω → Subgroup Ω} (hC : IsGNChoice C₁ C₂) {X R T Y : Subgroup Ω}
    (hX : CharTwo X) (hT : IsPGroup 2 T) (hSR : baum T ≤ R) (hRT : R ≤ T)
    (hQR : pCoreOf 2 X ≤ R) (hRX : R ≤ X) (hY : InYSet X R (baum T) Y) :
    (Y ≤ Subgroup.normalizer (C₂ T : Set Ω) ∨
        (Y ≤ Subgroup.centralizer (C₁ T : Set Ω) ∧
          Y ≤ Subgroup.centralizer (C₁ (baum T) : Set Ω)) ∨
        IsL2OrA3Block Y Y) ∧
      (Y ≤ Subgroup.normalizer (baum T : Set Ω) ∨
        (IsSylowTwoOf (baum T) (Y ⊔ baum T) ∧ ⁅Y, thompsonJ R⁆ = Y)) := by
  obtain ⟨W, hW, -⟩ := hY.natural
  have c : burnsideC121_YCtx X R T Y W := ⟨hX, hT, hSR, hRT, hQR, hRX, hY, hW⟩
  obtain ⟨n, F, _, _, ⟨D⟩⟩ := burnsideC121_exists_natD hY hW
  have hT0 := c.T_ne_bot D
  have hS0 := c.S_ne_bot D
  have hSp := c.S_pGroup
  obtain ⟨-, h1Z, -, -, h2B, h2char, -⟩ := hC.pair (baum T) hSp hS0
  rw [C1GN.baum_baum] at h2B h2char
  have hc2 : C₂ T = C₂ (baum T) := hC.c2_eq T hT hT0
  have hc1 : C₁ T ≤ C₁ (baum T) := by
    rw [hC.c1_eq T hT hT0]
    exact inf_le_right
  have hNC2 : Subgroup.normalizer (baum T : Set Ω) ≤ Subgroup.normalizer (C₂ T : Set Ω) := by
    rw [hc2]
    exact normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char
  by_cases hYS : Y ≤ Subgroup.normalizer (baum T : Set Ω)
  · exact ⟨Or.inl (hYS.trans hNC2), Or.inl hYS⟩
  · have hJ := c.commutator_thompsonJ_eq D hYS
    obtain ⟨hSyl, hcls⟩ := c.inClassG_YS D h610 h123 hYS
    refine ⟨?_, Or.inr ⟨hSyl, hJ⟩⟩
    have hcls' : InClassG (Y ⊔ baum T) (baum (baum T)) := by
      rw [C1GN.baum_baum]
      exact hcls
    rcases hC.dichotomy hSp hS0 hcls' with h | h | h
    · right; left
      have hYC : Y ≤ Subgroup.centralizer (C₁ (baum T) : Set Ω) := by
        intro y hy
        refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
        exact (Subgroup.mem_centralizer_iff.1 (h hz).2 y (Subgroup.mem_sup_left hy)).symm
      exact ⟨hYC.trans (Subgroup.centralizer_le hc1), hYC⟩
    · left
      rw [hc2]
      exact le_sup_left.trans h
    · right; right
      rw [c.twoResidual_YS] at h
      exact ⟨⟨h.1.1, le_rfl, by rw [Subgroup.subgroupOf_self]; exact Subgroup.IsSubnormal.top⟩,
        h.2⟩

end CFSG.ASVolI
