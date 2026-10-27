module

public import CFSG.RankThree.PartTwo.Sec17.Item176StepsProof177
import CFSG.RankThree.PartTwo.Sec17.Item176StepsProofTools
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof
import CFSG.RankThree.PartTwo.Sec17.Item17TailEnd
import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import Certificates.Certificate8166
import Certificates.Certificate8169

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

@[expose] noncomputable def Step177MainB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item1514 A (lB A) c L → Item176 A (lB A) c L →
    omegaA A = {Subgroup.zpowers c} →
    ∀ V : Subgroup G,
      Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 V) V →
      ⁅Y₀, V⁆ = ⊥ → ⁅V, Subgroup.zpowers c⁆ ≠ ⊥ →
      ⁅V, Subgroup.zpowers c⁆ ⊓
          pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) = ⊥ →
      False

namespace Proof17Res

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCoreOf_centralizer_hyperplane_mem_scriptQ {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hA : IsE27 A) {B : Subgroup G} (hB : IsHyperplane A B) :
    pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ∈ scriptQ A LB := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hO
  have hcop : Nat.Coprime 3 (Nat.card O) := coprime_card_pPrimeCoreOf 3 _
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hB.1 hx⟩ ⟨a, ha⟩)
  have hON : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hOB : O ≤ Subgroup.centralizer (B : Set G) := pPrimeCoreOf_le 3 _
  refine mem_scriptQ_iff.mpr ⟨(isPiSubgroup_piCompl_iff Nat.prime_three O).mpr
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop), hAB.trans hON, fun H hH => ?_⟩
  by_cases hHB : H ≤ B
  ·
    have hHeq : H = B := Subgroup.eq_of_le_of_card_ge hHB (by
      have h1 := hH.2
      have h2 := hB.2
      omega)
    subst hHeq
    exact inf_le_left.trans (le_sup_left.trans le_sup_left)
  ·
    obtain ⟨x, hxH, hxB⟩ := Set.not_subset.mp hHB
    have hAle : A ≤ B ⊔ Subgroup.zpowers x := le_sup_zpowers_of_not_mem hA hB (hH.1 hxH) hxB
    have hCA : O ⊓ Subgroup.centralizer (H : Set G) ≤ Subgroup.centralizer (A : Set G) :=
      fun y hy => mem_centralizer_of_le_sup hAle (hOB hy.1)
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxH) hy.2)
    have hCAB : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (B : Set G) :=
      Subgroup.centralizer_le hB.1
    have hle : O ⊓ Subgroup.centralizer (A : Set G) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) :=
      le_pPrimeCoreOf inf_le_right
        (Late.le_normalizer_inf (hCAB.trans hON) Subgroup.le_normalizer)
        (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcop)
    exact (le_inf inf_le_left hCA |>.trans hle).trans (le_sup_right.trans le_sup_left)

theorem pCoreOf_le_pPrimeCoreOf_centralizer {B : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (B : Set G)) :
    CFSG.Open.pCoreOf 2 (normalClosureIn (Subgroup.centralizer (B : Set G)) c) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer (B : Set G) with hC
  set X := normalClosureIn C c with hX
  have hXC : X ≤ C := by
    rw [hX, normalClosureIn, Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    exact mul_mem (mul_mem hm hc) (inv_mem hm)
  have hCX : C ≤ Subgroup.normalizer (X : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hle : X.map (MulAut.conj g).toMonoidHom ≤ X := by
      rw [hX, normalClosureIn, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, ⟨m, hm, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨g * m, mul_mem hg hm, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact hle ⟨x, hx, rfl⟩
  set P := CFSG.Open.pCoreOf 2 X with hP
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hP3 : Nat.Coprime 3 (Nat.card P) := by
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  exact le_pPrimeCoreOf ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXC)
    (hCX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)) hP3

theorem inf_pPrimeCoreOf_le {B U : Subgroup G} {b : G} (hb : b ∈ B)
    (hU : U ≤ Subgroup.centralizer (B : Set G)) :
    U ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ≤
      U ⊓ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBb : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb)
  have hle : pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊓
      Subgroup.centralizer (B : Set G) ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) :=
    le_pPrimeCoreOf inf_le_right
      (Late.le_normalizer_inf (hBb.trans (le_normalizer_pPrimeCoreOf 3 _)) Subgroup.le_normalizer)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf 3 _))
  exact fun x hx => ⟨hx.1, hle ⟨hx.2, hU hx.1⟩⟩

end Proof17Res

open Proof17Res

theorem step177MainB_of_M (hM : Step177MainM) : Step177MainB := by
  intro G _ _ A c L Y₀ h h1514 h176 hΩ V hV hYV hcV hUB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVM, hMV, hVab⟩ := hV.prop
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  set B := A ⊓ L with hBdef
  set X := normalClosureIn (Subgroup.centralizer (B : Set G)) c with hXdef
  set U := ⁅V, Subgroup.zpowers c⁆ with hUdef
  have hYVc : Y₀ ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hYV
  have hVC : V ≤ Subgroup.centralizer (B : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hYVc (h.le_y0 hx.2)) v hv).symm
  have hcM : c ∈ M :=
    h.normalizer_c_le (Subgroup.le_normalizer (Subgroup.mem_zpowers c))
  have hUV : U ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr (hMV hcM))
  have hUb : ∀ b ∈ B, b ≠ 1 → U ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) = ⊥ :=
    fun b hb _ => by
      rw [eq_bot_iff, ← hUB]
      exact inf_pPrimeCoreOf_le hb (hUV.trans hVC)
  have hXM := hM G A c L Y₀ h h1514 h176 hΩ V hV hYV hcV hUb
  have hcX : c ∈ X := Subgroup.subset_closure ⟨1, one_mem _, by group⟩
  have hUX : U ≤ X := by
    rw [hUdef, Subgroup.commutator_le]
    intro v hv y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hvc : v * c * v⁻¹ ∈ X := Subgroup.subset_closure ⟨v, hVC hv, rfl⟩
    rw [commutatorElement_def, show v * c ^ k * v⁻¹ = (v * c * v⁻¹) ^ k by rw [conj_zpow]]
    exact mul_mem (zpow_mem hvc k) (inv_mem (zpow_mem hcX k))
  have hV2 : IsPGroup 2 V := Sec5.isPGroup_of_isElemAbelian hVab
  have hVO : V ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVM hMV hV2
  have hle : X ⊓ CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (le_normalizer_inf Subgroup.le_normalizer
        (hXM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_right)
  have hUO : U ≤ CFSG.Open.pCoreOf 2 X := fun u hu => hle ⟨hUX hu, hVO (hUV hu)⟩
  have hcB : c ∈ Subgroup.centralizer (B : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (h.toSec13Data.commute (h.toSec13Data.mem_A) hx.1).symm
  apply hcV
  rw [eq_bot_iff, ← hUB]
  exact le_inf le_rfl (hUO.trans (pCoreOf_le_pPrimeCoreOf_centralizer hcB))

section Item177

variable {G : Type} [Group G] [Finite G]

open Proof177 in
theorem rank3II_17_7_of_B {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (h310 : Sec6.Item3_10) (h1514 : Item1514 A (lB A) c L) (hMeets : MeetsY4 A (lB A) L Y₀)
    (hAY : Claim1715A) (h176 : Item176 A (lB A) c L) (hmeet : Step177Meet)
    (hmain : Step177MainB) : Item177 A (lB A) := by
  intro Y hY V hV
  obtain rfl : Y = Y₀ := h.eq_of_mem_y0Star hY
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := h.isE27
  have h1 : ⁅Y ⊔ A, V⁆ ≠ ⊥ := rank3II_17_7_one_of h h310 hV
  refine ⟨h1, ?_⟩
  obtain ⟨hVM, hMV, hVab⟩ := hV.prop
  have hAM : A ≤ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer.trans h.normalizer_le
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := hAM.trans hMV
  have hget : ∀ W : Subgroup G, W ≤ V → W ∈ scriptQ A (lB A) → ⁅W, A⁆ ≠ ⊥ →
      ∃ U ∈ fourGroupsMinus A, U ∈ scriptQPi A (lB A) V (piOf 2) := by
    intro W hWV hW hWA
    obtain ⟨U, hU, hUW⟩ := exists_mem_fourGroupsMinus_le hA (Sec5.isElemAbelian_of_le hVab hWV)
      hW.1.2.2 hWA
    exact ⟨U, hU, ⟨mem_scriptQ_of_le hW hUW hU.1.1.2.2, hUW.trans hWV⟩, hU.1.1.2.1⟩
  by_cases hVY : ⁅V, Y⁆ = ⊥
  ·
    have hYV : ⁅Y, V⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hVY
    have hcases := h1514 Y hY hMeets
    have hΩ : omegaA A = {Subgroup.zpowers c} := by
      by_contra hΩ
      rcases hcases with ⟨-, -, hΩ', -⟩ | ⟨hA7, -, htr, -⟩ | ⟨-, -, -, hΩ', -⟩
      · exact hΩ hΩ'
      ·
        have hA10 := h.a10_or_omega.resolve_right hΩ
        have hAY0 := hAY G A c L Y h hA10 hA7 htr
        exact h1 (by rw [sup_eq_left.mpr hAY0]; exact hYV)
      · exact hΩ hΩ'
    have hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) := by
      rcases hcases with ⟨-, -, -, hp, -⟩ | ⟨-, -, htr, -⟩ | ⟨-, -, -, -, hno, -⟩
      · exact hp
      · have h3 := htr.1
        rw [hΩ, Set.ncard_singleton] at h3
        omega
      · exact absurd h.le_y0 (hno Y hY)
    have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
    have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := card_inf_eq_nine_of_prod h hprod
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine h.c_pow_three
      (fun hcB => hcL (Subgroup.mem_inf.mp hcB).2) le_rfl h9
      (fun b hb => hA.1.2 b hb.1) (fun b hb => h.commute_of_mem h.c_mem hb.1)).2
    have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr h.c_mem) inf_le_left
    have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
      (Subgroup.eq_of_le_of_card_ge hle (by rw [hA.2, hcard])).symm
    have hcV : ⁅V, Subgroup.zpowers c⁆ ≠ ⊥ := by
      intro hcV
      apply h1
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      have hYC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hYV
      have hcC : Subgroup.zpowers c ≤ Subgroup.centralizer (V : Set G) := by
        rw [Subgroup.commutator_comm] at hcV
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcV
      refine sup_le hYC ?_
      rw [hAeq]
      exact sup_le hcC ((inf_le_right.trans h.le_y0).trans hYC)
    by_cases hU : ⁅V, Subgroup.zpowers c⁆ ⊓
        pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) = ⊥
    · exact (hmain G A c L Y h h1514 h176 hΩ V hV hYV hcV hU).elim
    ·
      have hB : IsHyperplane A (A ⊓ L) := ⟨inf_le_left, by rw [hA.2, h9]⟩
      set W := ⁅V, Subgroup.zpowers c⁆ ⊓
        pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) with hWdef
      have hcA : c ∈ A := h.c_mem
      have hAc : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun a ha =>
        centralizer_singleton_le_normalizer_zpowers c (Subgroup.mem_centralizer_singleton_iff.mpr
          (h.commute_of_mem ha hcA))
      have hOQ : pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) ∈
          scriptQ A (lB A) := pPrimeCoreOf_centralizer_hyperplane_mem_scriptQ hA hB
      have hAW : A ≤ Subgroup.normalizer (W : Set G) :=
        le_normalizer_inf (le_normalizer_commutator hAV hAc) hOQ.1.2.2
      have hWV : W ≤ V :=
        inf_le_left.trans (Subgroup.le_normalizer_iff_commutator_le_left.mp
          (Subgroup.zpowers_le.mpr (hAV hcA)))
      have hW : W ∈ scriptQ A (lB A) := mem_scriptQ_of_le hOQ inf_le_right hAW
      refine hget W hWV hW fun hWA => hU ?_
      have hWC : W ≤ Subgroup.centralizer (A : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hWA
      have hV2 : IsPGroup 2 V := Sec5.isPGroup_of_isElemAbelian hVab
      have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card V) := by
        obtain ⟨k, hk⟩ := hV2.exists_card_eq
        rw [h.toSec13Data.card_zpowers, hk]
        exact Nat.Coprime.pow_right k (by norm_num)
      have hfit := CFSG.RankThree.Coprime.commutator_inf_centralizer_eq_bot
        (fun x hx y hy => congrArg Subtype.val (hVab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
        (Subgroup.zpowers_le.mpr (hAV hcA)) hcop
      rw [Subgroup.commutator_comm] at hfit
      rw [eq_bot_iff, ← hfit]
      refine le_inf inf_le_left (hWC.trans (Subgroup.centralizer_le ?_))
      exact SetLike.coe_subset_coe.mpr (Subgroup.zpowers_le.mpr hcA)
  ·
    obtain ⟨hW, hWA⟩ := hmeet G A c L Y h V hV hVY
    exact hget (V ⊓ Y) inf_le_left hW hWA

theorem item177S17_of_B (h310 : Sec6.Item3_10) (h1514 : Item1514S17) (hMeets : Claim1715Meets)
    (hAY : Claim1715A) (h176 : Item176R) (hmeet : Step177Meet) (hmain : Step177MainB) :
    Item177S17 :=
  fun G _ _ A c L Y₀ h => rank3II_17_7_of_B h h310 (h1514 G A c L Y₀ h) (hMeets G A c L Y₀ h) hAY
    (h176 G A c L h.toSec15R) hmeet hmain

end Item177

end CFSG.RankThree.PartTwo.Sec17
