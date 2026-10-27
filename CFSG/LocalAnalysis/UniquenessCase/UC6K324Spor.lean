module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K324Act
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1415b
public import CFSG.LocalAnalysis.SectionRank.SporadicWitnesses
public import CFSG.LocalAnalysis.SectionRank.Alternating
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.OddSporadicHolds
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRCore
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpField
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentSplit
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ChainLemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ClosingAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Step
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitComp
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Input
public import CFSG.LocalAnalysis.OddStandard.SmallF3Interfaces
public import CFSG.LocalAnalysis.SteinbergCEOddResidualE6Graph
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Md0ec50421ce4 (PSimple)

theorem k324Simple_data {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) {s : S}
    (hso : orderOf s = 5) {Y : Subgroup S} (hYC : Y ≤ centralizer ({s} : Set S))
    (hYn : (Y.subgroupOf (centralizer ({s} : Set S))).Normal) (hY : IsAlt ↥Y 6) :
    (∃ a b : S, a * b ≠ b * a) ∧ 3 ∣ Nat.card S ∧ 25 ∣ Nat.card S ∧
      GLAPComponent 5 (centralizer ({s} : Set S)) Y ∧
      Nonempty (PSimple 5 Y ≃* alternatingGroup (Fin 6)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hYs, hY360, ⟨a, b, hab⟩, -⟩ := alt6_facts hY
  obtain ⟨φ⟩ := hY
  have hnab : ∃ a b : S, a * b ≠ b * a := ⟨a, b, fun h => hab (Subtype.ext h)⟩
  have hYcen : ∀ w ∈ Y, (∀ x ∈ Y, w * x = x * w) → w = 1 := by
    intro w hw hwc
    have hcen : (⟨w, hw⟩ : Y) ∈ center ↥Y :=
      mem_center_iff.2 fun g => Subtype.ext (hwc g g.2).symm
    haveI := hYs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥Y) with h | h
    · rw [h, mem_bot] at hcen
      exact congrArg Subtype.val hcen
    · exfalso
      have h1 : a ∈ center ↥Y := by rw [h]; exact mem_top _
      exact hab (mem_center_iff.1 h1 b).symm
  have hcomp : GLAPComponent 5 (centralizer ({s} : Set S)) Y :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.glaPComponent_of_simple Nat.prime_five hYC
      (IsSubnormal.step hYC hYn (IsSubnormal.refl _)) hYs ⟨a, b, hab⟩ (by rw [hY360]; norm_num)
  refine ⟨hnab, (show 3 ∣ Nat.card Y by rw [hY360]; norm_num).trans
    (Subgroup.card_subgroup_dvd_card Y), ?_, hcomp, ?_⟩
  ·
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 5 (by rw [hY360]; norm_num)
    have hyo : orderOf (y : S) = 5 := by rw [Subgroup.orderOf_coe]; exact hy
    have hsY : ∀ x ∈ Y, s * x = x * s := fun x hx =>
      mem_centralizer_iff.1 (hYC hx) s (Set.mem_singleton s)
    have hcomm : ∀ c ∈ zpowers s, ∀ d ∈ zpowers (y : S), c * d = d * c := by
      intro c hc d hd
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hc
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hd
      exact (Commute.zpow_zpow (show Commute s (y : S) from hsY y y.2) i j).eq
    have hE := (isElemAbelian_zpowers hso).sup_of_commute (isElemAbelian_zpowers hyo) hcomm
    have hyns : (y : S) ∉ zpowers s := by
      intro h
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
      have hy1 : (y : S) = 1 := by
        refine hYcen y y.2 fun x hx => ?_
        rw [← hk]
        exact (Commute.zpow_left (show Commute s x from hsY x hx) k).eq
      rw [hy1, orderOf_one] at hyo
      omega
    obtain ⟨k, hk⟩ := hE.isPGroup.exists_card_eq
    have hlt : Nat.card (zpowers s) < Nat.card ↥(zpowers s ⊔ zpowers (y : S)) := by
      by_contra hle
      push Not at hle
      have heq : zpowers s = zpowers s ⊔ zpowers (y : S) := eq_of_le_of_card_ge le_sup_left hle
      have hmem : (y : S) ∈ zpowers s ⊔ zpowers (y : S) := mem_sup_right (mem_zpowers _)
      rw [← heq] at hmem
      exact hyns hmem
    rw [Nat.card_zpowers, hso, hk] at hlt
    have hk2 : 2 ≤ k := by
      by_contra h2
      push Not at h2
      interval_cases k <;> norm_num at hlt
    have h25 : 25 ∣ Nat.card ↥(zpowers s ⊔ zpowers (y : S)) := by
      rw [hk, show (25 : ℕ) = 5 ^ 2 by norm_num]
      exact Nat.pow_dvd_pow 5 hk2
    exact h25.trans (Subgroup.card_subgroup_dvd_card _)
  · obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.FR.nonempty_pSimple_equiv_of_simple Nat.prime_five
      hYs ⟨a, b, hab⟩ hcomp
    exact ⟨e.trans φ⟩

theorem k324Simple_alt {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n)
    (e : S ≃* alternatingGroup (Fin n)) (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2)
    (h25 : 25 ∣ Nat.card S) : False := by
  have hrk := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
  by_cases h9 : 9 ≤ n
  · have := CFSG.SectionRank.three_le_pRank_alternating h9
    omega
  · push Not at h9
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at h25
    interval_cases n <;> revert h25 <;> decide

section Sporadic

open CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Sporadic.HeldB
  CFSG.Sporadic.Co2Cert CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.SuzOddCore
  CFSG.Sporadic.SmallOddCore
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415b

section J2


theorem sporNoAltDown5_six_J2
    (hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    SporNoAltDown 5 6 .J2 := by
  obtain ⟨⟨hQP, -, -, -, hsyl⟩, ⟨hlines, -⟩, hC, hsmall, hbig⟩ :=
    R3E_J2_full_five_centralizer_structure
  refine sporNoAltDown_of_lines Nat.prime_five (by omega)
    ((hBr .J2).some.symm.trans j2PermEquiv) j2P_le_j2R hQP hsyl hlines (B := 300) (fun i => ?_)
    (by decide)
  rw [inf_comm, ← (hC i).1]
  by_cases hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 4
  · rw [(hsmall i hi).1]
    norm_num
  · rw [(hbig i (by omega)).1]

end J2

section He


theorem sporNoAltDown5_six_He
    (hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    SporNoAltDown 5 6 .He := by
  obtain ⟨⟨hQP, hsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrec, ⟨-, hC0⟩, -⟩ :=
    R3E_He_full_five_centralizer_structures
  refine sporNoAltDown_of_lines Nat.prime_five (by omega)
    ((hBr .He).some.symm.trans heEquivP) heP_le_heAutGroup hQP hsyl hlines
    (B := 600) (fun j => ?_) (by decide)
  obtain ⟨hh, hc⟩ := htrans j
  rw [hrec j] at hc
  refine card_inf_le_of_transporter hh hc ?_
  rw [← (R3E_He_full_five_centralizer_structures).2.2.2.2.1.1, hC0]

end He

section Main


theorem k324Simple_spor
    {S : Type} [Group S] [Finite S] (name : TauCeti.SporadicName)
    (e : S ≃* (TauCeti.CFSGIndex.sporadic name).Group) (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2)
    (h125 : ¬ 125 ∣ Nat.card S) (h25 : 25 ∣ Nat.card S) {s : S} (hso : orderOf s = 5)
    {Y : Subgroup S} (hYc : GLAPComponent 5 (centralizer ({s} : Set S)) Y)
    (hYP : Nonempty (PSimple 5 Y ≃* alternatingGroup (Fin 6))) : False := by
  have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hcard : Nat.card S = CFSG.ComponentClassification.GSThmB.QPUSpor.sporOrder name := by
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (hbr name).some.toEquiv,
      CFSG.ComponentClassification.CatFC.card_carrier_eq_sporOrder_all]
  have hwit : name ∉ CFSG.SectionRank.sqtkSporadicNames → name ≠ .M → False := by
    intro h1 h2
    obtain ⟨E, hE, k, hk, hEc⟩ := CFSG.SectionRank.sporadicThreeRankWitnesses name h1 h2
    have f := (hbr name).some.trans e.symm
    have h4 := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top
      (CFSG.SectionRank.isElemAbelian_map hE f.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective f.injective, hEc])
    omega
  cases name with
  | J2 => exact (sporNoAltDown5_six_J2 hbr S ⟨e⟩ s hso Y hYc).false hYP.some
  | He => exact (sporNoAltDown5_six_He hbr S ⟨e⟩ s hso Y hYc).false hYP.some
  | Suz => exact hwit (by decide) (by decide)
  | Fi22 => exact hwit (by decide) (by decide)
  | Fi23 => exact hwit (by decide) (by decide)
  | Fi24Prime => exact hwit (by decide) (by decide)
  | _ =>
    rw [hcard] at h125 h25
    first
      | exact absurd h25 (by decide)
      | exact absurd h125 (by decide)

end Main

end Sporadic

end CFSG.LocalAnalysis.UniquenessCase.UCK
