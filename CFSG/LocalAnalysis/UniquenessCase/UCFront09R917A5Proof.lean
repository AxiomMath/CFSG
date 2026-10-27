module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R917A5
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09LinThreeOdd
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PSubgroupInfNormalNilpotentLePCore
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFBest
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R917A5L
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R917A5V
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92a
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R9R5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09l
import CFSG.Quasithin.Background.B2Factorization
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups
import CFSG.GroupTheory.PCore.Transport
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin CFSG.AGLEmbedding Subgroup
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open CFSG.Blueprint (LieModel)
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore primeComplementCore_coprime)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {Y H S : Subgroup G}

local notation "V₀" => conjClosure (omegaOneCenterOf S) (L9 Y H ⊔ S)

theorem thompsonJ_le_centralizer
    {D : Data G} {D₃ : Subgroup G} (hY : Hyp97 D Y H D₃ S) (hR : pCoreOf 2 Y ≠ ⊥)
    (hSM : ¬ IsSylowOf 2 S D.M) (hSH : IsSylowOf 2 S H)
    (hLie : LieModel (Lbar9 Y H) .PSL 3 5 1) : thompsonJ S ≤ centralizer (V₀ : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine iSup₂_le fun A hA => ?_
  have hYH : Y ≤ H := hY.1.2.1.1
  have hG₀H : L9 Y H ⊔ S ≤ H := sup_le (L9_le_of_le hYH) hSH.le
  have hG₀top : L9 Y H ⊔ S ≠ ⊤ := fun h =>
    ne_top_of_hyp97 hY hR (top_le_iff.1 (h.ge.trans hG₀H))
  have hSL : S ≤ normalizer (L9 Y H : Set G) := hSH.le.trans (le_normalizer_L9 Y H)
  obtain ⟨hred, hVS⟩ := isTwoReducedIn_conjClosure_L9 hY hSH
  have hG₀V : L9 Y H ⊔ S ≤ normalizer (V₀ : Set G) := hred.2.1
  have hVe : IsElemAbelian 2 V₀ := hred.2.2.1
  have hLb := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hLie
  have hs : IsSimpleGroup (Lbar9 Y H) := StatedAPI.isSimpleGroup_of_statedClassicalModel hLb
  have hLC := inf_centralizer_le_I9 hY hR hSM hs
  let _ : CommGroup V₀ := commGroupOfElemAbelian hVe
  let _ : Module (ZMod 2) (Additive V₀) := L34FF.moduleOfSq fun w => Subtype.ext (hVe.2 w w.2)
  set Γ := autOn (L9 Y H ⊔ S) V₀ with hΓ
  set f := L34FF.conjOnto V₀ (L9 Y H ⊔ S) hG₀V with hf
  set Ls : Subgroup ↥Γ := ((L9 Y H).subgroupOf (L9 Y H ⊔ S)).map f with hLs
  haveI hLn : Ls.Normal := (normal_subgroupOf_of_le_normalizer
    (hG₀H.trans (le_normalizer_L9 Y H))).map f (L34FF.conjOnto_surjective hG₀V)
  have hO2 : CFSG.pCore 2 ↥Γ = ⊥ := by
    have h := CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred
    rwa [CFSG.openPCoreOf_eq_map_pCore, map_eq_bot_iff_of_injective _ (subtype_injective _)] at h
  have hmod : StatedClassicalModel (↥Ls ⧸ primeComplementCore (G := ↥Ls) 3) .PSL 3 5 1 := by
    let g₁ : ↥(L9 Y H) →* ↥Ls := (f.comp (inclusion le_sup_left)).codRestrict Ls
      fun l => ⟨inclusion le_sup_left l, l.2, rfl⟩
    have hg₁ : Function.Surjective g₁ := by
      rintro ⟨_, ⟨x, hx, rfl⟩⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have hk₁ : Nat.Coprime 3 (Nat.card g₁.ker) := coprime_card_of_map_le_I9 (H := H) (by
      rintro _ ⟨l, hl, rfl⟩
      exact hLC ⟨l.2, (L34FF.conjOnto_eq_one_iff hG₀V _).1
        (congrArg Subtype.val (g₁.mem_ker.1 hl))⟩)
    obtain ⟨φ, hφ, hker⟩ := exists_surjective_Lbar9 hYH
    have hk₂ : Nat.Coprime 3 (Nat.card φ.ker) := coprime_card_of_map_le_I9 (H := H) (by
      rintro _ ⟨l, hl, rfl⟩
      exact (hker l).1 hl)
    obtain ⟨e₁⟩ := L34FF.nonempty_quotient_primeComplementCore_mulEquiv Nat.prime_three g₁ hg₁ hk₁
    obtain ⟨e₂⟩ := L34FF.nonempty_quotient_primeComplementCore_mulEquiv Nat.prime_three φ hφ hk₂
    have hO : primeComplementCore (G := Lbar9 Y H) 3 = ⊥ := by
      rcases hs.eq_bot_or_eq_top_of_normal (primeComplementCore (G := Lbar9 Y H) 3) with h | h
      · exact h
      · have hc := primeComplementCore_coprime (G := Lbar9 Y H) 3
        rw [h, card_top, StatedAPI.card_of_statedClassicalModel_psl_three_five hLb] at hc
        exact absurd ⟨124000, rfl⟩ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc)
    exact StatedAPI.statedClassicalModel_of_mulEquiv
      ((((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm.trans
        e₂.symm).trans e₁) hLb
  have hcen := le_centralizer_of_isBestOffender_linThree (X := ↥Γ) (W := Additive V₀)
    (ρ := (L34FF.autFTwoRep V₀).comp Γ.subtype)
    (L34FF.autFTwoRep_comp_injective hVe) (L34FF.isKGroup_autOn hG₀V D.standing.kProper hG₀top)
    hO2 hLn Nat.prime_five (by norm_num) hmod (L34FF.isElementaryAbelian_map_conjOnto hG₀V hA.2.1)
    (L34FF.isBestOffender_map_conjOnto hG₀V hVe hVS hA (hA.1.trans le_sup_right))
  have hq2 : IsPGroup 2 (↥Γ ⧸ Ls) := by
    intro q
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, rfl⟩ := L34FF.conjOnto_surjective hG₀V γ
    obtain ⟨l, hl, s, hs', hls⟩ : (g : G) ∈ (L9 Y H : Set G) * (S : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hSL]
      exact g.2
    obtain ⟨k, hk⟩ := hSH.isPGroup ⟨s, hs'⟩
    refine ⟨k, ?_⟩
    have hgs : (f g : ↥Γ ⧸ Ls) = (f ⟨s, mem_sup_right hs'⟩ : ↥Γ ⧸ Ls) := by
      rw [QuotientGroup.eq, ← map_inv, ← map_mul]
      refine mem_map_of_mem f ?_
      rw [mem_subgroupOf, coe_mul, coe_inv, ← hls, mul_inv_rev, mul_assoc]
      simpa [mul_assoc] using (mem_normalizer_iff.1 (hSL (S.inv_mem hs')) l⁻¹).1 (inv_mem hl)
    rw [hgs, ← QuotientGroup.mk_pow, ← map_pow]
    have hs0 : s ^ 2 ^ k = 1 := by simpa using congrArg (Subtype.val : ↥S → G) hk
    have hk' : (⟨s, mem_sup_right hs'⟩ : ↥(L9 Y H ⊔ S)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hs0)
    rw [hk', map_one, QuotientGroup.mk_one]
  have hCnil : Group.IsNilpotent ↥(centralizer (Ls : Set ↥Γ)) := by
    haveI : Group.IsNilpotent (↥Γ ⧸ Ls) := hq2.isNilpotent
    refine Subgroup.isNilpotent_of_ker_le_center
      ((QuotientGroup.mk' Ls).comp (centralizer _).subtype) ?_
    intro c hc
    rw [mem_center_iff]
    intro d
    have hcL : (c : ↥Γ) ∈ Ls := (QuotientGroup.eq_one_iff _).1 hc
    exact Subtype.ext ((mem_centralizer_iff.1 d.2 _ hcL).symm)
  have hA2 : IsPGroup 2 ((A.subgroupOf (L9 Y H ⊔ S)).map f) :=
    ((hSH.isPGroup.to_le hA.1).comap_subtype (K := L9 Y H ⊔ S)).map f
  have hbot := CFSG.GorensteinWalter.pSubgroup_inf_normal_nilpotent_le_pCore _ _ 2 Nat.prime_two
    hA2 inferInstance hCnil
  rw [inf_eq_left.2 hcen, hO2] at hbot
  intro a ha
  exact (L34FF.conjOnto_eq_one_iff hG₀V ⟨a, hA.1.trans le_sup_right ha⟩).1
    (mem_bot.1 (hbot (mem_map_of_mem f (show _ ∈ A.subgroupOf (L9 Y H ⊔ S) from ha))))

theorem eq_sup_I9_of_lie
    {D : Data G} {D₃ : Subgroup G} (hY : Hyp97 D Y H D₃ S) (hA5 : IsAlt (Bar2 (Opp 3 Y)) 5)
    (hR : pCoreOf 2 Y ≠ ⊥) (hSM : ¬ IsSylowOf 2 S D.M) (hSH : IsSylowOf 2 S H)
    (hLie : LieModel (Lbar9 Y H) .PSL 3 5 1) : H = (H ⊓ D.M) ⊔ I9 H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYH : Y ≤ H := hY.1.2.1.1
  have hLH : L9 Y H ≤ H := L9_le_of_le hYH
  have hG₀H : L9 Y H ⊔ S ≤ H := sup_le hLH hSH.le
  have hG₀V : L9 Y H ⊔ S ≤ normalizer (V₀ : Set G) := (isTwoReducedIn_conjClosure_L9 hY hSH).1.2.1
  have hs : IsSimpleGroup (Lbar9 Y H) := StatedAPI.isSimpleGroup_of_statedClassicalModel
    (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hLie)
  have hJ := thompsonJ_le_centralizer hY hR hSM hSH hLie
  obtain ⟨hSY, hS2, hoddY⟩ := isSylowOf_iff.1 hY.2.2.2
  have hS1 : S ≠ ⊥ := fun h =>
    hR (le_bot_iff.1 ((pCoreOf_two_le_of_sylowIn hSY hS2 hoddY).trans h.le))
  have hSC : S ⊓ centralizer (V₀ : Set G) = Y ⊓ centralizer (V₀ : Set G) :=
    le_antisymm (inf_le_inf_right _ hSY)
      (le_inf (inf_centralizer_le_of_hyp97 hY hA5 hR hSM hs) inf_le_right)
  have hJS : thompsonJ S = thompsonJ (S ⊓ centralizer (V₀ : Set G)) :=
    thompsonJ_eq_of_le (le_inf (thompsonJ_le_self S) hJ) inf_le_left
  have hYJ : Y ≤ normalizer (thompsonJ S : Set G) := by
    rw [hJS, hSC]
    exact (B2F.le_normalizer_inf le_normalizer (B2F.le_normalizer_centralizer
      ((le_L9_sup hY).trans hG₀V))).trans (normalizer_le_normalizer_thompsonJ _)
  have hNJ := normalizer_le_of_hyp97 (r910_holds D) hY hSM (thompsonJ_le_self S)
    (CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hS2 hS1)
    (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ S) hYJ
  obtain ⟨-, -, hodd⟩ := isSylowOf_iff.1 (hSH.of_le le_sup_right hG₀H)
  have hfac := (B2_7_of_le_factor hG₀V ⟨le_sup_right, hS2, hodd⟩ hJ).2
  have hLC := inf_centralizer_le_I9 hY hR hSM hs
  set W := (H ⊓ D.M) ⊔ I9 H
  have key : ∀ g ∈ L9 Y H, ∀ y ∈ L9 Y H ⊓ W, g * y * g⁻¹ ∈ L9 Y H ⊓ W := by
    intro g hg y hy
    obtain ⟨hyL, hyW⟩ := mem_inf.1 hy
    obtain ⟨n, hn, c, hc, rfl⟩ := hfac g (mem_sup_left hg)
    obtain ⟨hnG, hnJ⟩ := mem_inf.1 hn
    obtain ⟨hcG, hcV⟩ := mem_inf.1 hc
    have hN : ∀ x ∈ L9 Y H ⊔ S, ∀ z ∈ L9 Y H, x * z * x⁻¹ ∈ L9 Y H := fun x hx z hz =>
      (mem_normalizer_iff.1 (le_normalizer_L9 Y H (hG₀H hx)) z).1 hz
    have hcy : c * y * c⁻¹ * y⁻¹ ∈ I9 H := by
      refine hLC (mem_inf.2 ⟨mul_mem (hN c hcG y hyL) (inv_mem hyL), ?_⟩)
      have hyc := (mem_normalizer_iff.1 (B2F.le_normalizer_centralizer hG₀V
        (mem_sup_left hyL)) c⁻¹).1 (inv_mem hcV)
      simpa [mul_assoc] using mul_mem hcV hyc
    have hzW : c * y * c⁻¹ ∈ W := by
      simpa using W.mul_mem (le_sup_right (a := H ⊓ D.M) hcy) hyW
    have hnW : n ∈ W := le_sup_left (a := H ⊓ D.M) (b := I9 H) (mem_inf.2 ⟨hG₀H hnG, hNJ hnJ⟩)
    rw [show n * c * y * (n * c)⁻¹ = n * (c * y * c⁻¹) * n⁻¹ by group]
    exact mem_inf.2 ⟨hN n hnG _ (hN c hcG y hyL), W.mul_mem (W.mul_mem hnW hzW) (W.inv_mem hnW)⟩
  have hLN : L9 Y H ≤ normalizer ((L9 Y H ⊓ W : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_iff.2 fun y => ⟨key g hg y, fun h => by
      simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ h⟩
  rcases le_I9_or_le_of_isSimpleGroup hYH inf_le_left hLN hs with h | h
  ·
    have hD₃ : D₃ ≤ I9 H := h.trans' (le_inf (hY.1.2.2.1.trans (opp_le_L9 Y H))
      (le_sup_left.trans' (le_inf (hY.1.2.2.1.trans ((opp_le_self 3 Y).trans hYH))
        (hY.1.2.2.1.trans ((opp_le_self 3 Y).trans hY.1.1.1)))))
    have hd := card_dvd_of_le hD₃
    rw [hY.1.2.2.2] at hd
    exact absurd hd (not_dvd_card_I9 H)
  · refine le_antisymm ?_ (sup_le inf_le_left (map_subtype_le _))
    rw [eq_L9_sup_of_hyp91 hY.1]
    exact sup_le (h.trans inf_le_right) le_sup_left

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
