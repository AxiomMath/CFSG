module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.AdapterFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEightSetup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Statements
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013
  (Standing4 Setup4 PartIAt Theorem1669At Theorem1930Four)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Four

variable {G : Type} [Group G] [Finite G]

theorem card_codimSet_eq_centMod {V₀ V : Subgroup G}
    (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {t : G}
    (ht : ∀ v ∈ V, t * v * t⁻¹ ∈ V) :
    Nat.card {v : G // v ∈ V ∧ v⁻¹ * (t * v * t⁻¹) ∈ V₀} =
      Nat.card (UC22.centMod V₀ V t) := by
  have hiff : ∀ v : G, (v ∈ V ∧ v⁻¹ * (t * v * t⁻¹) ∈ V₀) ↔
      (v ∈ V ∧ t * v * t⁻¹ * v⁻¹ ∈ V₀) := by
    intro v
    constructor
    · rintro ⟨hv, hmem⟩
      exact ⟨hv, by rwa [hV v⁻¹ (inv_mem hv) (t * v * t⁻¹) (ht v hv)] at hmem⟩
    · rintro ⟨hv, hmem⟩
      exact ⟨hv, by rwa [← hV v⁻¹ (inv_mem hv) (t * v * t⁻¹) (ht v hv)] at hmem⟩
  exact Nat.card_congr (Equiv.subtypeEquivRight hiff)

theorem mBarGT_of_minCodimGt {M V₀ V : Subgroup G}
    (hMV : M ≤ normalizer (V : Set G))
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {n : ℕ}
    (h : CFSG.Yardstones.Mf4cdcdf2e013.MinCodimGt M V₀ V n) :
    UC22.MBarGT M V₀ V n := by
  constructor
  · intro m hm hnm hm2
    have hmV : ∀ v ∈ V, m * v * m⁻¹ ∈ V := fun v hv =>
      (Subgroup.mem_set_normalizer_iff.mp (hMV hm) v).mp hv
    have hmV2 : ∀ v ∈ V, (m * m) * v * (m * m)⁻¹ ∈ V := by
      intro v hv
      convert hmV (m * v * m⁻¹) (hmV v hv) using 1
      group
    have hquot : ¬ CFSG.Yardstones.Mf4cdcdf2e013.CentralizesQuot V₀ V m :=
      fun hc => hnm ((centralizesQuot_iff hVab hmV).mp hc)
    have hquot2 : CFSG.Yardstones.Mf4cdcdf2e013.CentralizesQuot V₀ V (m * m) :=
      (centralizesQuot_iff hVab hmV2).mpr hm2
    have h1 := h.1 m hm hquot hquot2
    rwa [card_codimSet_eq_centMod hVab hmV] at h1
  · intro hCM
    refine h.2 fun t ht ht2 => ?_
    have htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V := fun v hv =>
      (Subgroup.mem_set_normalizer_iff.mp (hMV ht) v).mp hv
    have htV2 : ∀ v ∈ V, (t * t) * v * (t * t)⁻¹ ∈ V := by
      intro v hv
      convert htV (t * v * t⁻¹) (htV v hv) using 1
      group
    exact (centralizesQuot_iff hVab htV).mpr
      (hCM t ht ((centralizesQuot_iff hVab htV2).mp ht2))

theorem thm1669_dataOfSetup4_of_theorem1669At (hS : Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (h : Theorem1669At S.M S.T) :
    Thm1669 (UC6.dataOfSetup4 hS hU S) := by
  intro V₀ V h125 hcard
  obtain ⟨h123, H₀, hH, h124⟩ := h125
  have hV : UC22.InCalV S.M V := hyp123_inCalV h123
  refine mBarGT_of_minCodimGt hV.2.2.1
    (fun a ha b hb => CFSG.Open.IsElemAbelian.comm hV.2.2.2 ha hb) ?_
  exact h V₀ V H₀ ((hyp123_iff S.maxLocal S.T V₀ V).mpr h123) hH h124 hcard

theorem asc1930_of_dataOfSetup4 (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G)
    (S : Setup4 G) (h1214 : F12.R1214 (UC6.dataOfSetup4 hS hU S))
    (h1824 : S18.R18_24 (UC6.dataOfSetup4 hS hU S))
    (h19 : S19.Sec19Contra (UC6.dataOfSetup4 hS hU S)) :
    ∀ H ∈ CFSG.LocalAnalysis.RankThreeUC.hSet S.T S.M,
      CFSG.LocalAnalysis.RankThreeUC.Asc1930 S.M H := by
  intro H hH
  rw [CFSG.LocalAnalysis.RankThreeUC.asc1930_iff_not_hyp124]
  intro h124
  obtain ⟨V₀, V, hV⟩ := twelve_eight_ofSetup4 hS hU S h1214 ⟨H, hH, h124⟩
  exact h19 V₀ V hV (h1824 V₀ V hV)

theorem uc_theorem_19_30_four_of_sec_direct
    (h1214 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing4 G)
      (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G),
        S.InMSigma → PartIAt S.M → F12.R1214 (UC6.dataOfSetup4 hS hU S))
    (h1824 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing4 G)
      (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G),
        S.InMSigma → PartIAt S.M → Theorem1669At S.M S.T →
          S18.R18_24 (UC6.dataOfSetup4 hS hU S))
    (h19 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing4 G)
      (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G),
        S.InMSigma → PartIAt S.M → Theorem1669At S.M S.T →
          S19.Sec19Contra (UC6.dataOfSetup4 hS hU S)) :
    Theorem1930Four := by
  intro G _ _ hS hU S hMS hPart h1669 H hH
  exact asc1930_of_dataOfSetup4 hS hU S (h1214 G hS hU S hMS hPart)
    (h1824 G hS hU S hMS hPart h1669) (h19 G hS hU S hMS hPart h1669) H hH

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
