module

public import CFSG.RankThree.GF2n.Smith81.InspKFacts
public import CFSG.RankThree.GF2n.Smith81.LinSmallG2
public import CFSG.RankThree.GF2n.Smith81.LinLane
import CFSG.RankThree.GF2n.Smith81.InspK1NSL
import CFSG.RankThree.GF2n.Smith81.LinInspectData
import CFSG.RankThree.GF2n.Smith81.LinSmallOrder
import CFSG.RankThree.GF2n.Smith81.LinSmallCore
import CFSG.RankThree.GF2n.Smith81.Lin216E6
import CFSG.RankThree.GF2n.Smith81.TiBridge

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 CFSG.Timmesfeld
open CFSG.SeitzReduction.F4Pilot (ordSL)

variable {G : Type} [Group G]

section Certificates


theorem linInspectSmall_of (hK1 : K1NSLStatement) (hKG2 : KG2Statement) [Finite G]
    {M Q Z B V₁ V₂ : Subgroup G} {n : ℕ} (hc : Ctx M Q Z B) (hE6 : TypeE6 M Q Z B n)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : n = 2 ∨ n = 3)
    (h3 : Lin3Facts M Q Z B n V₁ V₂) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (hroot : Timmesfeld.IsRootInvolutionSet {g : G | IsConj z g})
    (hconj : ∀ w : G, IsConj z w →
      ∃ x ∈ Subgroup.normalClosure ({z} : Set G), w = x * z * x⁻¹) :
    ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
      CFSG.Blueprint.LieModel ↥(Subgroup.normalClosure ({z} : Set G)) .PSL (n + 2) 2 f := by
  obtain ⟨f, hf, hf2, hHyp, hl, hcardroot, hlow, hpow, hv⟩ :=
    linInspect_data hc hS (by omega) h3 hz hz1 hroot hconj
  rcases rootOutcome_of_K1NSL hK1 hHyp hl with ⟨t, k, f', -, htag, hL, hroot'⟩ | hU
  · have hff : f' = f := by
      have h1 := hroot' (selfIn z) (IsConj.refl z)
      rw [hcardroot] at h1
      exact (Nat.pow_right_injective (le_refl 2) h1).symm
    rw [hff] at htag hL hroot'
    rcases hn with rfl | rfl
    ·
      have hlo : 2 ^ (6 * f) ∣
          Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) := by
        have e : f * (2 * 2 + 1) + f * (2 * (2 - 1) / 2) = 6 * f := by
          norm_num
          ring
        rwa [e] at hlow
      have hup : (Nat.card ↥(Subgroup.normalClosure ({z} : Set G))).factorization 2 ≤
          6 * f + 2 * f.factorization 2 + 2 :=
        le_trans hv (factorization_card_le_lin_two hc hS hf)
      rcases linCoreTwo hf2 htag hL hlo hup with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨f, hf, hL⟩
      · exact (not_lieModel_G2_lin hKG2 hc hS h3 hz hz1 hHyp hf hf2 hroot' hL).elim
    ·
      have hlo : 2 ^ (10 * f) ∣
          Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) := by
        have e : f * (2 * 3 + 1) + f * (3 * (3 - 1) / 2) = 10 * f := by
          norm_num
          ring
        rwa [e] at hlow
      have hup : (Nat.card ↥(Subgroup.normalClosure ({z} : Set G))).factorization 2 ≤
          10 * f + 2 * f.factorization 2 + 1 :=
        le_trans hv (factorization_card_le_lin_three hc hE6 hS hf)
      obtain ⟨rfl, rfl⟩ := linCoreThree hf2 htag hL hlo hup
      exact ⟨f, hf, hL⟩
  ·
    exfalso
    have h5 := factorization_psu_three_three hU
    have hle :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hpow
    rw [h5] at hle
    have h10 : 10 ≤ f * (2 * n + 1) := by
      rcases hn with rfl | rfl <;> nlinarith [hf2]
    omega

theorem linTIIdentify_of (hKG2 : KG2Statement) [Finite G] {M Q Z B V₁ V₂ : Subgroup G} {n : ℕ}
    (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B) (hC : StrothConclusion M Q Z B)
    (hE6 : TypeE6 M Q Z B n) (hS : LinSetup M Q Z B n V₁ V₂) (hn : n = 2 ∨ n = 3)
    (h3 : Lin3Facts M Q Z B n V₁ V₂) :
    ∃ f : ℕ, Nat.card Z = 2 ^ f ∧ CFSG.Blueprint.LieModel (FStar G) .PSL (n + 2) 2 f := by
  obtain ⟨z, hz, hz1⟩ := exists_ne_one_mem_Z hc.hyp
  have hrem : RemCfg M Q Z B := ⟨⟨hc, hC⟩, Or.inr (Or.inr ⟨n, hE6⟩)⟩
  obtain ⟨hroot, hconj⟩ := linRootClass_of_lin3 hb hrem (by omega) h3 hz hz1
  obtain ⟨f, hf, hL⟩ :=
    linInspectSmall_of k1NSL_holds hKG2 hc hE6 hS hn h3 hz hz1 hroot hconj
  refine ⟨f, hf, ?_⟩
  obtain ⟨hF, -⟩ := generalizedFitting_eq_normalClosure hc.hyp hz hz1
  exact CFSG.Blueprint.LieModel.of_mulEquiv (MulEquiv.subgroupCongr hF.symm) hL

theorem linTIIdentifyStatement_of_kG2 (hKG2 : KG2Statement) : LinTIIdentifyStatement :=
  fun _ _ _ _ _ _ _ _ _ _ hb hc hC hE6 hS hn h3 => linTIIdentify_of hKG2 hb hc hC hE6 hS hn h3

end Certificates

end CFSG.RankThree.GF2n.Smith81.Insp
