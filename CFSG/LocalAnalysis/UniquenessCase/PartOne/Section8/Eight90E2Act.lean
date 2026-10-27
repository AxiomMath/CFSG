module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs3
public import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofNoSz
import CFSG.GroupTheory.PLayer.CenterQuotientAction
import CFSG.Quasithin.Vol2.Ch10SecCGroup
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSub23.Sz
import CFSG.GroupTheory.Commutator.ThreeSubgroupsModNormal
import CFSG.Blueprint.LieModelAPI
import CFSG.Fischer.Aut.Complete
import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.SylowAutomorphism
import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartTwo.Sec16.Steps166 (NoSzSection)

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem pCoreOf_le_centralizer_of_pCore_le_ker {K C : Subgroup H} {A : Type*} [Group A]
    (φ : ↥K →* MulAut A) (hker : φ.ker = (K ⊓ centralizer (C : Set H)).subgroupOf K)
    (h : CFSG.pCore 2 ↥K ≤ φ.ker) : pCoreOf 2 K ≤ centralizer (C : Set H) := by
  intro x hx
  have hxK : x ∈ K := CFSG.openPCoreOf_le 2 K hx
  have hxP : (⟨x, hxK⟩ : ↥K) ∈ φ.ker := by
    apply h
    rw [← CFSG.openPCoreOf_subgroupOf 2 K]
    exact hx
  rw [hker, Subgroup.mem_subgroupOf] at hxP
  exact hxP.2

noncomputable def quotientRangeMulEquivOfKerLe {K A : Type*} [Group K] [Group A]
    (φ : K →* MulAut A) {P : Subgroup K} [P.Normal] (hker : φ.ker ≤ P)
    (M : Subgroup φ.range) [M.Normal] (hM : M = P.map φ.rangeRestrict) :
    (K ⧸ P) ≃* (φ.range ⧸ M) := by
  let f : K →* φ.range ⧸ M := (QuotientGroup.mk' M).comp φ.rangeRestrict
  have hfsurj : Function.Surjective f :=
    (QuotientGroup.mk'_surjective M).comp φ.rangeRestrict_surjective
  have hker' : φ.rangeRestrict.ker ≤ P := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hcomap : M.comap φ.rangeRestrict = P := by
    rw [hM]
    exact Subgroup.comap_map_eq_self hker'
  have hfker : f.ker = P := by
    ext x
    change (φ.rangeRestrict x : φ.range ⧸ M) = 1 ↔ x ∈ P
    rw [QuotientGroup.eq_one_iff, ← hcomap]
    exact Iff.rfl
  exact (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfsurj)

theorem le_centralizer_of_noSzSection {K C : Subgroup H} {n : ℕ} (hK : ⁅K, K⁆ = K)
    (hSz : IsSz (Bar2 K) n) (hC : CFSG.IsQuasisimple ↥C) (hKC : K ≤ normalizer (C : Set H))
    (hNo : NoSzSection (MulAut (↥C ⧸ center ↥C))) : K ≤ centralizer (C : Set H) := by
  by_contra hcon
  have hszModel : CFSG.Blueprint.SuzukiModel (Bar2 K) 2 n :=
    ((CFSG.Blueprint.LieModel.twistedB2_iff (G := Bar2 K)).mp hSz).2
  have hsimp : IsSimpleGroup (Bar2 K) :=
    (CFSG.LieType.Simplicity.fam_2b2_simplicity (Bar2 K) 2 n hszModel).2
  have hproper : K ⊓ centralizer (C : Set H) < K := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro h
    exact hcon (h ▸ inf_le_right)
  have hKcent : K ≤ normalizer ((centralizer (C : Set H) : Subgroup H) : Set H) := by
    have hconj := CFSG.GroupTheory.conj_mem_centralizer_of_le_normalizer hKC
      (le_refl (centralizer (C : Set H) : Subgroup H))
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨hconj k hk x, fun hx => by
      have h := hconj k⁻¹ (K.inv_mem hk) (k * x * k⁻¹) hx
      rwa [show k⁻¹ * (k * x * k⁻¹) * (k⁻¹)⁻¹ = x from by group] at h⟩
  have hXN : K ≤ normalizer ((K ⊓ centralizer (C : Set H) : Subgroup H) : Set H) :=
    CFSG.Quasithin.Vol2.Ch10.SecC.le_normalizer_inf' Subgroup.le_normalizer hKcent
  have hNle : K ⊓ centralizer (C : Set H) ≤ pCoreOf 2 K := by
    rcases CFSG.Quasithin.Vol2.Ch10.SecC.le_pCoreOf_or_eq_of_normal (X := K)
      (N := K ⊓ centralizer (C : Set H)) hK hsimp inf_le_left hXN with h | h
    · exact h
    · exact absurd h hproper.ne
  let φ : ↥K →* MulAut (↥C ⧸ center ↥C) := normalizerToCenterQuotientAut C K hKC
  have hker : φ.ker = (K ⊓ centralizer (C : Set H)).subgroupOf K :=
    ker_normalizerToCenterQuotientAut hC.1 hKC
  let P : Subgroup ↥K := CFSG.pCore 2 ↥K
  have hPnormal : P.Normal := CFSG.pCore_normal
  have hPN : P.Normal := hPnormal
  have hker_le : φ.ker ≤ P := by
    intro x hx
    rw [hker, Subgroup.mem_subgroupOf] at hx
    have hx' : x ∈ (pCoreOf 2 K).subgroupOf K := hNle hx
    rwa [CFSG.openPCoreOf_subgroupOf] at hx'
  let M : Subgroup φ.range := P.map φ.rangeRestrict
  have hMnormal : M.Normal := hPnormal.map φ.rangeRestrict φ.rangeRestrict_surjective
  have hMN : M.Normal := hMnormal
  have e : (↥K ⧸ P) ≃* (φ.range ⧸ M) :=
    quotientRangeMulEquivOfKerLe φ hker_le M rfl
  exact hNo φ.range M 2 n
    (CFSG.RankThree.PartTwo.Sec16.suzukiModel_of_mulEquiv e.symm hszModel)

theorem range_le_conj_range_of_isKGroup (hKSch : UCK.KSch) {K C : Subgroup H}
    (hK : ⁅K, K⁆ = K) (hC : CFSG.IsQuasisimple ↥C)
    (hCK : CFSG.Open.IsKGroup (↥C ⧸ center ↥C))
    (φ : ↥K →* MulAut (↥C ⧸ center ↥C)) :
    φ.range ≤ (MulAut.conj : (↥C ⧸ center ↥C) →* MulAut (↥C ⧸ center ↥C)).range := by
  have hKperf : Group.IsPerfect ↥K :=
    CFSG.Quasithin.Vol2.Ch10.SecC.isPerfect_of_commutator_eq hK
  have hrangeperf : Group.IsPerfect ↥φ.range := Group.IsPerfect.range (f := φ)
  have hOutSolv : Group.IsSolvable
      (MulAut (↥C ⧸ center ↥C) ⧸
        (MulAut.conj : (↥C ⧸ center ↥C) →* MulAut (↥C ⧸ center ↥C)).range) :=
    hKSch (↥C ⧸ center ↥C) hC.2.1 hCK
  have hbot := CFSG.Quasithin.Vol2.Ch10.SecC.map_eq_bot_of_isPerfect_of_isSolvable
    (QuotientGroup.mk' (MulAut.conj : (↥C ⧸ center ↥C) →* MulAut (↥C ⧸ center ↥C)).range)
    φ.range
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

theorem range_eq_bot_or_isSimpleGroup_of_isSz
    {K C : Subgroup H} {m : ℕ} (hK : ⁅K, K⁆ = K)
    (hC : CFSG.IsQuasisimple ↥C) (hCSz : IsSz (↥C ⧸ center ↥C) m)
    (φ : ↥K →* MulAut (↥C ⧸ center ↥C))
    (hInn : φ.range ≤ (MulAut.conj : (↥C ⧸ center ↥C) →* MulAut (↥C ⧸ center ↥C)).range) :
    φ.range = ⊥ ∨ IsSimpleGroup ↥φ.range := by
  have hKperf : Group.IsPerfect ↥K :=
    CFSG.Quasithin.Vol2.Ch10.SecC.isPerfect_of_commutator_eq hK
  have hrangeperf : Group.IsPerfect ↥φ.range := Group.IsPerfect.range (f := φ)
  let J : Type := ↥C ⧸ center ↥C
  have hJsimple : IsSimpleGroup J := hC.2.1
  have hZ : Subgroup.center J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hC.2.2
      exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm hab
  have hInj : Function.Injective (MulAut.conj : J →* MulAut J) :=
    CFSG.Fischer.mulAutConj_injective hZ
  let Y : Subgroup J := φ.range.comap (MulAut.conj : J →* MulAut J)
  have hYmap : Y.map (MulAut.conj : J →* MulAut J) = φ.range :=
    Subgroup.map_comap_eq_self hInn
  have hYcomm : ⁅Y, Y⁆ = Y := by
    apply Subgroup.map_injective hInj
    rw [Subgroup.map_commutator, hYmap]
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (f := φ))
  rcases CFSG.LocalAnalysis.UniquenessCase.UC22.KS23.eq_bot_or_isSimpleGroup_of_isSz
    hCSz Y hYcomm with hYbot | hYsimple
  · left
    rw [← hYmap, hYbot, Subgroup.map_bot]
  · right
    have hYsimple' : IsSimpleGroup ↥Y := hYsimple
    have eY : ↥Y ≃* ↥φ.range :=
      (Subgroup.equivMapOfInjective Y (MulAut.conj : J →* MulAut J) hInj).trans
        (MulEquiv.subgroupCongr hYmap)
    exact eY.symm.isSimpleGroup

theorem pCore_le_ker_of_isSz
    {K C : Subgroup H} {m : ℕ} (hK : ⁅K, K⁆ = K) (hC : CFSG.IsQuasisimple ↥C)
    (hCSz : IsSz (↥C ⧸ center ↥C) m)
    (φ : ↥K →* MulAut (↥C ⧸ center ↥C))
    (hInn : φ.range ≤ (MulAut.conj : (↥C ⧸ center ↥C) →* MulAut (↥C ⧸ center ↥C)).range) :
    CFSG.pCore 2 ↥K ≤ φ.ker := by
  have hKperf : Group.IsPerfect ↥K :=
    CFSG.Quasithin.Vol2.Ch10.SecC.isPerfect_of_commutator_eq hK
  have hrangeperf : Group.IsPerfect ↥φ.range := Group.IsPerfect.range (f := φ)
  let P : Subgroup ↥K := CFSG.pCore 2 ↥K
  have hPnormal : P.Normal := CFSG.pCore_normal
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
  rcases range_eq_bot_or_isSimpleGroup_of_isSz hK hC hCSz φ hInn with hbot | hsimple
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hxr : φ x ∈ φ.range := ⟨x, rfl⟩
    rw [hbot] at hxr
    exact Subgroup.mem_bot.mp hxr
  · have hRangeSimple : IsSimpleGroup ↥φ.range := hsimple
    let ψ : ↥K →* φ.range := φ.rangeRestrict
    have hNnormal : (P.map ψ).Normal := hPnormal.map ψ φ.rangeRestrict_surjective
    have hNbot : P.map ψ = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.map ψ) with h | h
      · exact h
      · exfalso
        have htop : IsPGroup 2 (⊤ : Subgroup φ.range) := h ▸ hP2.map ψ
        have hnil : Group.IsNilpotent ↥(⊤ : Subgroup φ.range) := htop.isNilpotent
        have hsolvTop : Group.IsSolvable ↥(⊤ : Subgroup φ.range) := IsNilpotent.to_isSolvable
        let t : ↥(⊤ : Subgroup φ.range) →* ↥φ.range := Subgroup.topEquiv.toMonoidHom
        have ht : Function.Surjective t := Subgroup.topEquiv.surjective
        have hsolv : Group.IsSolvable ↥φ.range := Group.isSolvable_of_surjective ht
        exact (Group.IsPerfect.not_isSolvable ↥φ.range) hsolv
    intro x hx
    have hxN : ψ x ∈ P.map ψ := Subgroup.mem_map_of_mem ψ hx
    rw [hNbot] at hxN
    exact MonoidHom.mem_ker.mpr (Subtype.ext_iff.mp (Subgroup.mem_bot.mp hxN))

theorem pCoreOf_le_centralizer_of_isSz
    (hKSch : UCK.KSch) {K C : Subgroup H} {m : ℕ}
    (hK : ⁅K, K⁆ = K) (hC : CFSG.IsQuasisimple ↥C)
    (hCK : CFSG.Open.IsKGroup (↥C ⧸ center ↥C)) (hCSz : IsSz (↥C ⧸ center ↥C) m)
    (hKC : K ≤ normalizer (C : Set H)) : pCoreOf 2 K ≤ centralizer (C : Set H) := by
  let φ : ↥K →* MulAut (↥C ⧸ center ↥C) := normalizerToCenterQuotientAut C K hKC
  exact pCoreOf_le_centralizer_of_pCore_le_ker φ
    (ker_normalizerToCenterQuotientAut hC.1 hKC)
    (pCore_le_ker_of_isSz hK hC hCSz φ
      (range_le_conj_range_of_isKGroup hKSch hK hC hCK φ))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
