module

public import CFSG.OddTranspositions.PartFour.Fourteen.TheoremFive
import CFSG.LocalAnalysis.WeakClosure81.TimTI.SpGlue
import CFSG.LocalAnalysis.WeakClosure81.TimTI.SUGlue
import CFSG.RankThree.GF2n.Tim79aTransvectionHyp
import CFSG.RankThree.GF2n.Tim79aRootTransportSU
import CFSG.RankThree.GF2n.Tim79aSpPair
import CFSG.RankThree.GF2n.Tim81.Cited.OddTranspRootL2
import CFSG.Timmesfeld.Transvection.OddBC2Rel
public import CFSG.Timmesfeld.Transvection.Statement

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp
open CFSG.Timmesfeld.Connectivity CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem isSymplecticTransvection_or_isUnitaryTransvection_of_meetsSq
    (hS : Setup G D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hconn : ¬ Disconnected D) (hsq : MeetsSq D) {s : G} (hs : s ∈ D) :
    ∃ m f : ℕ, 4 ≤ m ∧ 2 ≤ f ∧
      (SevenK.IsSymplecticTransvection G m f s ∨ SevenK.IsUnitaryTransvection G m f s) := by
  classical
  have hZ : Subgroup.center G = ⊥ := hrad _ inferInstance inferInstance
  have hP : CFSG.pCore 2 G = ⊥ := by
    haveI : Group.IsNilpotent (CFSG.pCore 2 G) := CFSG.pCore_isPGroup.isNilpotent
    exact hrad _ CFSG.pCore_normal inferInstance
  obtain ⟨f, hf, hcard, hconcl⟩ :=
    CFSG.Timmesfeld.Transvection.transvectionStatement_of_oddUnitary
      CFSG.Timmesfeld.Transvection.oddUnitaryStatement_holds G _
      (CFSG.RankThree.GF2n.Tim79a.transvectionHyp_of_connected
        CFSG.RankThree.GF2n.Tim81.oddTranspRootL2 hS hP hZ hsq hconn)
  have hWΔ : Subgroup.closure (rootSet D s) ∈
      {A | ∃ d ∈ D, A = Subgroup.closure (rootSet D d)} := ⟨s, hs, rfl⟩
  have h4 := CFSG.RankThree.GF2n.Tim79a.four_le_card_closure_rootSet hS hsq s hs
  rw [hcard _ hWΔ] at h4
  have hf2 : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by omega
    norm_num at h4
  have hsW : s ∈ Subgroup.closure (rootSet D s) := Subgroup.subset_closure (mem_rootSet_self hs)
  have hs1 : s ≠ 1 := hS.oddT.ne_one hs
  let ψ : G ⧸ Subgroup.center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hψ : ∀ x : G, ψ (QuotientGroup.mk x) = x := fun _ => rfl
  rcases (CFSG.RankThree.GF2n.Tim79a.transvectionConclusion_iff _ _ _ _).1 hconcl with hSp | hSU
  · obtain ⟨n, Φ, a, T, hn, hΦ, ha, hTa, hWT⟩ :=
      CFSG.RankThree.GF2n.Tim79a.exists_isTransGroup_of_transvConclusionSp_two hf hSp hWΔ
    obtain ⟨e, he⟩ := TimTI.exists_equiv_sp_of_isTransGroup Φ hΦ ha hTa
    rw [hWT] at hsW
    obtain ⟨t, htT, rfl⟩ := Subgroup.mem_map.mp hsW
    have ht1 : t ≠ 1 := by rintro rfl; exact hs1 (map_one Φ)
    refine ⟨2 * n, f, by omega, hf2, Or.inl ⟨n, rfl, GaloisField 2 f, inferInstance,
      inferInstance, GaloisField.card 2 f (by omega), ψ.trans e, ?_⟩⟩
    rw [MulEquiv.trans_apply, hψ]
    exact he t htT ht1
  · obtain ⟨m, Φ, a, T, hm, hΦ, hker, ha, -, hTa, hWT⟩ :=
      CFSG.RankThree.GF2n.Tim79a.exists_isUTransGroup_of_transvConclusionSU hf hSU hWΔ
    obtain ⟨-, e, he⟩ := TimTI.exists_equiv_psu_of_isUTransGroup hf2 hm Φ hΦ hker ha hTa
    rw [hWT] at hsW
    obtain ⟨t, htT, rfl⟩ := Subgroup.mem_map.mp hsW
    have ht1 : t ≠ 1 := by rintro rfl; exact hs1 (map_one Φ)
    refine ⟨m, f, hm, hf2, Or.inr ⟨GaloisField 2 (2 * f), inferInstance, inferInstance,
      CFSG.Timmesfeld.Transvection.card_galoisField_two_mul hf, ψ.trans e, ?_⟩⟩
    rw [MulEquiv.trans_apply, hψ]
    exact he t htT ht1

theorem ascList_of_meetsSq (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hsq : MeetsSq D) :
    AscList G D := by
  obtain ⟨m, f, hm, hf, h⟩ :=
    isSymplecticTransvection_or_isUnitaryTransvection_of_meetsSq hC.setup hrad hC.conn hsq hC.hd
  exact Or.inr (Or.inl ⟨hC.d, hC.hd, m, f, by omega, hf, h.imp_right Or.inl⟩)

theorem theorem5List_of_theorem5 (h5 : Theorem5) : Theorem5List :=
  fun G _ _ D hC hrad hW hE hMZ => ascList_of_meetsSq hC hrad (h5 G D hC hrad hW hE hMZ)

end CFSG.OddTranspositions.PartFour
