module

public import CFSG.LocalAnalysis.StandardType.FS81.GoldLayerSetup
import CFSG.Goldschmidt.Steps.G3b34
import CFSG.Goldschmidt.Steps.G37Wrappers
import CFSG.Goldschmidt.Steps.G37CoreTypeII
import Mathlib.GroupTheory.Transfer
import CFSG.Goldschmidt.StatementsG2
import CFSG.Goldschmidt.StatementsG3
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.SubnormalPSubgroupLeQCore
import CFSG.Walter.Bender1970.S2
import CFSG.Walter.Bender1970.S3.Basic
import CFSG.Walter.Bender1970.S3.OStar
import CFSG.Walter.PSL2Facts

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Goldschmidt

variable {Y : Type} [Group Y] [Finite Y] {S : Sylow 2 Y} {B L : Subgroup Y}

private theorem goldLayerC_inf_ne_bot (hF : G310.CompFacts B L) : B ⊓ L ≠ ⊥ := by
  intro hbot
  obtain ⟨x, hx, y, -, hxy⟩ := hF.noncentral
  rw [hbot, Subgroup.mem_bot] at hx
  exact hxy (by rw [hx, one_mul, mul_one])

private theorem goldLayerC_sylow_inf_eq
    (D : GoldLayerFacts Y S B)
    (hL : IsComponentOf L ⊤) (hF : G310.CompFacts B L) (hII : IsGoldTypeII L) :
    fusionIsSylowIn 2 (B ⊓ L) L ∧ (S : Subgroup Y) ⊓ L = B ⊓ L := by
  have hLq : GorensteinWalter.IsQuasisimple L := (G37.open_isQuasisimple_iff).mp hL.2.2
  have hLgw : GorensteinWalter.IsComponentOf L ⊤ := by
    refine ⟨hL.1, ?_, hLq⟩
    exact (CFSG.Open.IsSubnormal.iff_subgroupOf le_top).mp hL.2.1
  have hZ : Subgroup.center L = ⊥ := G37.center_eq_bot_typeII D.hyp.oddCore hLgw hII
  have hLs : IsSimpleGroup L := G37.isSimpleGroup_of_center_eq_bot hLq hZ
  have hBLne : B ⊓ L ≠ ⊥ := goldLayerC_inf_ne_bot hF
  have hA'ne : (B ⊓ L).subgroupOf L ≠ ⊥ := by
    intro hbot
    have h1 : B ⊓ L = ⊥ := by
      have h2 := congrArg (Subgroup.map L.subtype) hbot
      rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right, Subgroup.map_bot] at h2
    exact hBLne h1
  have hS' : IsSStarIn (⊤ : Subgroup L) ((B ⊓ L).subgroupOf L) := by
    have h1 := SStarTransport.isSStarIn_subgroupOf hF.sstar (le_refl L)
    rwa [Subgroup.subgroupOf_self] at h1
  have hSyl' : fusionIsSylowIn 2 ((B ⊓ L).subgroupOf L) ⊤ :=
    (G34 L hII ((B ⊓ L).subgroupOf L) hS' hA'ne).1
  let P : Sylow 2 L :=
    { toSubgroup := (B ⊓ L).subgroupOf L
      isPGroup' := hSyl'.2.1
      is_maximal' := fun {Q} hQ hAQ => hSyl'.2.2 Q le_top hQ hAQ }
  have hP : (P : Subgroup L) = (B ⊓ L).subgroupOf L := rfl
  have hBsyl : fusionIsSylowIn 2 (B ⊓ L) L :=
    SStarTransport.isSylowIn_of_sylow inf_le_right P hP
  refine ⟨hBsyl, ?_⟩
  have hBle : B ⊓ L ≤ (S : Subgroup Y) ⊓ L := inf_le_inf_right L D.hyp.le
  exact hBsyl.2.2 _ inf_le_right (S.isPGroup'.to_le inf_le_left) hBle

theorem goldLayer_inf_eq_of_typeII
    (D : GoldLayerFacts Y S B) (hL : IsComponentOf L ⊤)
    (hF : G310.CompFacts B L) (hII : IsGoldTypeII L) {P : Sylow 2 Y} (hBP : B ≤ P) :
    (P : Subgroup Y) ⊓ L = (S : Subgroup Y) ⊓ L := by
  obtain ⟨hBsyl, hST⟩ := goldLayerC_sylow_inf_eq D hL hF hII
  have hPle : (P : Subgroup Y) ⊓ L ≤ (P : Subgroup Y) := inf_le_left
  have hPp : IsPGroup 2 ((P : Subgroup Y) ⊓ L : Subgroup Y) := P.isPGroup'.to_le hPle
  have hBleP : B ⊓ L ≤ (P : Subgroup Y) ⊓ L := inf_le_inf_right L hBP
  exact (hBsyl.2.2 _ inf_le_right hPp hBleP).trans hST.symm

theorem goldLayer_exists_not_le_of_typeII
    (D : GoldLayerFacts Y S B)
    (hL : IsComponentOf L ⊤) (hF : G310.CompFacts B L) (hII : IsGoldTypeII L) :
    ∃ y ∈ L, y ∈ Subgroup.normalizer (((S : Subgroup Y) ⊓ L : Subgroup Y) : Set Y) ∧
      y ∉ (S : Subgroup Y) := by
  by_contra h
  obtain ⟨hBsyl, hST⟩ := goldLayerC_sylow_inf_eq D hL hF hII
  let T : Subgroup Y := (S : Subgroup Y) ⊓ L
  have hTBeq : T = B ⊓ L := by simpa [T] using hST
  have hTle : T ≤ L := by rw [hTBeq]; exact inf_le_right
  have hTne : T ≠ ⊥ := by rw [hTBeq]; exact goldLayerC_inf_ne_bot hF
  have hTsyl : fusionIsSylowIn 2 T L := by rw [hTBeq]; exact hBsyl
  have h' : ∀ y ∈ L, y ∈ Subgroup.normalizer
      (((S : Subgroup Y) ⊓ L : Subgroup Y) : Set Y) → y ∈ (S : Subgroup Y) := by
    intro y hyL hyN
    by_contra hyS
    exact h ⟨y, hyL, hyN, hyS⟩
  obtain ⟨P, hP⟩ := SStarTransport.exists_sylow_of_isSylowIn (p := 2) hTsyl
  have hPleB : (P : Subgroup L) ≤ B.subgroupOf L := by
    intro z hz
    rw [hP] at hz
    have hzT : (z : Y) ∈ T := Subgroup.mem_subgroupOf.mp hz
    rw [hTBeq] at hzT
    exact Subgroup.mem_subgroupOf.mpr hzT.1
  have hPcomm : IsMulCommutative (P : Subgroup L) := by
    haveI : IsMulCommutative B := D.hyp.comm
    haveI : IsMulCommutative (B.subgroupOf L) :=
      Subgroup.subgroupOf_isMulCommutative (K := L) (H := B)
    exact isMulCommutative_anti (t := B.subgroupOf L) hPleB
  have hN_le : Subgroup.normalizer ((P : Subgroup L) : Set L) ≤ (P : Subgroup L) := by
    intro y hy
    have hyT : (y : Y) ∈ Subgroup.normalizer (T : Set Y) := by
      have h2 : y ∈ (Subgroup.normalizer (T : Set Y)).subgroupOf L := by
        rw [Subgroup.subgroupOf_normalizer_eq hTle]
        have hy2 : y ∈ Subgroup.normalizer
            ((T.subgroupOf L : Subgroup L) : Set L) := by rwa [hP] at hy
        exact hy2
      exact Subgroup.mem_subgroupOf.mp h2
    have hyS : (y : Y) ∈ (S : Subgroup Y) :=
      h' (y : Y) y.2 (by simpa [T] using hyT)
    rw [hP]
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hyS, y.2⟩)
  have hPcent : (P : Subgroup L) ≤ Subgroup.centralizer ((P : Subgroup L) : Set L) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hPcomm.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hnorm : Subgroup.normalizer ((P : Subgroup L) : Set L) ≤
      Subgroup.centralizer ((P : Subgroup L) : Set L) :=
    hN_le.trans hPcent
  have hφ : MonoidHom.transferSylow P hnorm = 1 := by
    haveI : Group.IsPerfect L := ⟨hL.2.2.1⟩
    have : IsMulCommutative (P : Subgroup L) := hPcomm
    haveI : Group.IsPerfect (MonoidHom.transferSylow P hnorm).range :=
      Group.IsPerfect.range (MonoidHom.transferSylow P hnorm)
    haveI : Subsingleton (MonoidHom.transferSylow P hnorm).range :=
      Group.IsPerfect.subsingleton_of_isMulCommutative
    ext g
    have hsub := Subsingleton.elim
      (⟨MonoidHom.transferSylow P hnorm g, g, rfl⟩ :
        (MonoidHom.transferSylow P hnorm).range) 1
    simpa using congrArg Subtype.val hsub
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hnorm
  have hPbot : (P : Subgroup L) = ⊥ := by
    rw [← Subgroup.isComplement'_top_left]
    rwa [hφ, MonoidHom.ker_one] at hcomp
  have hTbot : T = ⊥ := by
    have h1 : T.subgroupOf L = ⊥ := by
      rw [← hP]
      exact hPbot
    have h2 := congrArg (Subgroup.map L.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hTle, Subgroup.map_bot] at h2
  exact hTne hTbot

end CFSG.StandardType.FrameRoute.FS81

end
