module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsMem
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsAlt5
public import CFSG.Quasithin.Background.A312SporGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.A312Hs

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.HS.Native (hsData)
open CFSG.Quasithin.A312Ru (modO2_psl32_gen)

theorem isExt_of_modO2 {Γ : Type} [Group Γ] {B : Subgroup Γ}
    {PV PY : ∀ (V : Type) [Group V], Prop} (hV : PV ↥(CFSG.pCore 2 ↥B)) (hY : PY (ModO2 B)) :
    IsExt ↥B PV PY :=
  ⟨CFSG.pCore 2 ↥B, inferInstance, hV, hY⟩

section Abstract

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem case_one_abstract {T B Y Y₃ : Subgroup Γ} (hB : B ∈ lFamily T) (hY : B ⊔ T = Y)
    (hle : Y₃ ≤ Y) (hc : Nat.card Y = 2 ^ 9 * 3 * 5) (hc₃ : Nat.card Y₃ = 2 ^ 9 * 3)
    (hP : Nat.card (CFSG.pCore 2 ↥Y) = 2 ^ 6)
    (hq : ∀ (N : Subgroup ↥Y) [N.Normal], IsPGroup 2 (↥Y ⧸ N) → Nat.card (↥Y ⧸ N) ≤ 2)
    (hV : IsZ4StarExtra2 ↥(CFSG.pCore 2 ↥Y)) :
    IsExt ↥B (fun V _ => IsZ4StarExtra2 V) (fun Z _ => IsAlt 5 Z) := by
  obtain ⟨hA, ⟨e⟩⟩ := modO2_alt5_gen hB hY (e := 9) (k := 6) rfl hle hc hc₃ hP hq
  exact isExt_of_modO2 (IsZ4StarExtra2.of_mulEquiv e.symm hV) hA

theorem case_two_abstract {T B Y Y₃ : Subgroup Γ} (hB : B ∈ lFamily T) (hY : B ⊔ T = Y)
    (hle : Y₃ ≤ Y) (hc : Nat.card Y = 2 ^ 9 * 3 * 7) (hc₃ : Nat.card Y₃ = 2 ^ 9 * 3)
    (hP : Nat.card (CFSG.pCore 2 ↥Y) = 2 ^ 6)
    (hq : ∀ (N : Subgroup ↥Y) [N.Normal], IsPGroup 2 (↥Y ⧸ N) → Nat.card (↥Y ⧸ N) ≤ 1)
    (hV : IsZ4Cubed ↥(CFSG.pCore 2 ↥Y)) :
    IsExt ↥B (fun V _ => IsZ4Cubed V) (fun Z _ => IsPSL 3 2 1 Z) := by
  obtain ⟨hA, ⟨e⟩⟩ := modO2_psl32_gen hB hY (e := 9) (k := 6) rfl hle hc hc₃ hP hq
  obtain ⟨f⟩ := hV
  exact isExt_of_modO2 ⟨e.trans f⟩ hA

end Abstract

theorem hs_case_one
    {B : Subgroup (J hsData)}
    (hB : B ∈ lFamily hsCtx.S) (hY : B ⊔ hsCtx.S = hsCtx.Y 1) :
    IsExt ↥B (fun V _ => IsZ4StarExtra2 V) (fun Z _ => IsAlt 5 Z) := by
  have hle : hsCtx.Y 4 ≤ hsCtx.Y 1 := (hs_Y_le_iff (by norm_num) (by norm_num)).mpr (by decide)
  have hc : Nat.card (hsCtx.Y 1) = 2 ^ 9 * 3 * 5 := by
    rw [hs_member_card 1 (by norm_num)]
    rfl
  have hc₄ : Nat.card (hsCtx.Y 4) = 2 ^ 9 * 3 := by
    rw [hs_member_card 4 (by norm_num)]
    rfl
  obtain ⟨hP, hq⟩ := hs_row_one
  exact case_one_abstract hB hY hle hc hc₄ hP hq hs_V1_struct

theorem hs_case_two
    {B : Subgroup (J hsData)}
    (hB : B ∈ lFamily hsCtx.S) (hY : B ⊔ hsCtx.S = hsCtx.Y 2) :
    IsExt ↥B (fun V _ => IsZ4Cubed V) (fun Z _ => IsPSL 3 2 1 Z) := by
  have hle : hsCtx.Y 3 ≤ hsCtx.Y 2 := (hs_Y_le_iff (by norm_num) (by norm_num)).mpr (by decide)
  have hc : Nat.card (hsCtx.Y 2) = 2 ^ 9 * 3 * 7 := by
    rw [hs_member_card 2 (by norm_num)]
    rfl
  have hc₃ : Nat.card (hsCtx.Y 3) = 2 ^ 9 * 3 := by
    rw [hs_member_card 3 (by norm_num)]
    rfl
  exact case_two_abstract hB hY hle hc hc₃ hs_row_two (fun N _ hp => hs_Y2_quot N hp)
    hs_V2_struct

theorem a312For_hs
    (hq : CFSG.IsQuasisimple (J hsData)) : A312For (J hsData) := by
  refine CFSG.Quasithin.A312S.a312For_of_members hq hs_S_sylow (L := #[1, 15, 21, 3, 3])
    (Y := hsCtx.Y) hs_complete ?_
  intro j hj B hB hY
  have hj5 : j < 5 := by simpa using hj
  have hc := hs_member_card j hj5
  have hHS : IsSporadic .HS ↥(⊤ : Subgroup (J hsData)) :=
    ⟨Subgroup.topEquiv.trans (seedEquiv hs_facts.toBaseFacts).symm⟩
  have hsolv : ∀ {a b : ℕ}, Nat.card (hsCtx.Y j) = 2 ^ a * 3 ^ b → False := fun h =>
    CFSG.Quasithin.A312S.not_isSolvable_sup hB
      (hY ▸ CFSG.Quasithin.A312S.isSolvable_of_card_pq Nat.prime_two Nat.prime_three
        (by norm_num) h)
  interval_cases j
  · exact (hsolv (a := 9) (b := 0) (by rw [hc]; rfl)).elim
  · iterate 16 right
    left
    exact ⟨Or.inl (hs_case_one hB hY), hHS⟩
  · iterate 16 right
    left
    exact ⟨Or.inr (hs_case_two hB hY), hHS⟩
  · exact (hsolv (a := 9) (b := 1) (by rw [hc]; rfl)).elim
  · exact (hsolv (a := 9) (b := 1) (by rw [hc]; rfl)).elim

theorem famHs_holds :
    FamHs := by
  intro X _ _ hq hX
  obtain ⟨e⟩ := hX
  have e' : X ≃* J hsData := e.trans (seedEquiv hs_facts.toBaseFacts)
  have hq' : CFSG.IsQuasisimple (J hsData) := CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq
  exact @A312For.of_mulEquiv X (J hsData) _ _ _ _ e' (a312For_hs hq')

end CFSG.Quasithin.A312Hs
