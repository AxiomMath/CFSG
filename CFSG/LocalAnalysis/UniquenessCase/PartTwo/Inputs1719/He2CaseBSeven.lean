module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.He2CaseA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HeOuterParabolicsProof
public import CFSG.Quasithin.Background.HZ82Base
public import TauCeti.GroupTheory.SemidirectProduct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenOuterPGL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB
open CFSG.Quasithin.ModH CFSG.Quasithin.ModH.He1 CFSG.Quasithin.ModH.He2
open CFSG.Quasithin.RonanE114.HeOver CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Ch1.SporLat.He (heIncl)
open CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

theorem he_Y3_inf_Y7 {J : Type} [Group J] [Finite J] (hl : HeLat J) :
    hl.Y 3 ⊓ hl.Y 7 = hl.Y 8 := by
  refine le_antisymm ?_ (le_inf (Y_le hl (by norm_num) (by norm_num) (by decide))
    (Y_le hl (by norm_num) (by norm_num) (by decide)))
  have hS : hl.S ≤ hl.Y 3 ⊓ hl.Y 7 := le_inf (hl.S_le_Y 3) (hl.S_le_Y 7)
  rcases hl.complete _ hS with ⟨j, hj, hjeq⟩ | htop
  · have h8le : hl.Y 8 ≤ hl.Y 3 ⊓ hl.Y 7 := le_inf
      (Y_le hl (by norm_num) (by norm_num) (by decide))
      (Y_le hl (by norm_num) (by norm_num) (by decide))
    have h8j : hl.Y 8 ≤ hl.Y j := h8le.trans hjeq.le
    have hj8 : j ∈ heIncl[8]! := (hl.le_iff (by norm_num) hj).mp h8j
    have hi3 : 3 ∈ heIncl[j]! := (hl.le_iff hj (by norm_num)).mp (hjeq ▸ inf_le_left)
    have hi7 : 7 ∈ heIncl[j]! := (hl.le_iff hj (by norm_num)).mp (hjeq ▸ inf_le_right)
    have key : ∀ j < 11, j ∈ heIncl[8]! → 3 ∈ heIncl[j]! → 7 ∈ heIncl[j]! → j = 8 := by
      decide
    rw [hjeq, key j hj hj8 hi3 hi7]
  · exfalso
    have h3top : hl.Y 3 = ⊤ := top_le_iff.mp (htop ▸ inf_le_left)
    have h1 := congrArg (fun K : Subgroup J => Nat.card ↥K) h3top
    rw [card_top hl, card_Y_idx hl (by norm_num)] at h1
    norm_num [heIdx] at h1

theorem he_Y4_inf_Y7 {J : Type} [Group J] [Finite J] (hl : HeLat J) :
    hl.Y 4 ⊓ hl.Y 7 = hl.Y 10 := by
  refine le_antisymm ?_ (le_inf (Y_le hl (by norm_num) (by norm_num) (by decide))
    (Y_le hl (by norm_num) (by norm_num) (by decide)))
  have hS : hl.S ≤ hl.Y 4 ⊓ hl.Y 7 := le_inf (hl.S_le_Y 4) (hl.S_le_Y 7)
  rcases hl.complete _ hS with ⟨j, hj, hjeq⟩ | htop
  · have h10le : hl.Y 10 ≤ hl.Y 4 ⊓ hl.Y 7 := le_inf
      (Y_le hl (by norm_num) (by norm_num) (by decide))
      (Y_le hl (by norm_num) (by norm_num) (by decide))
    have h10j : hl.Y 10 ≤ hl.Y j := h10le.trans hjeq.le
    have hj10 : j ∈ heIncl[10]! := (hl.le_iff (by norm_num) hj).mp h10j
    have hi4 : 4 ∈ heIncl[j]! := (hl.le_iff hj (by norm_num)).mp (hjeq ▸ inf_le_left)
    have hi7 : 7 ∈ heIncl[j]! := (hl.le_iff hj (by norm_num)).mp (hjeq ▸ inf_le_right)
    have key : ∀ j < 11, j ∈ heIncl[10]! → 4 ∈ heIncl[j]! → 7 ∈ heIncl[j]! → j = 10 := by
      decide
    rw [hjeq, key j hj hj10 hi4 hi7]
  · exfalso
    have h4top : hl.Y 4 = ⊤ := top_le_iff.mp (htop ▸ inf_le_left)
    have h1 := congrArg (fun K : Subgroup J => Nat.card ↥K) h4top
    rw [card_top hl, card_Y_idx hl (by norm_num)] at h1
    norm_num [heIdx] at h1

theorem he2_caseB_seven
    {Y J : Type} [Group Y] [Finite Y] [Group J] [Finite J]
    {K S : Subgroup Y} [K.Normal] (hl : HeLat J) (e : ↥K ≃* J)
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = hl.S)
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) {s : Y} (hsS : s ∈ S)
    (hswap : (hl.Y 3).map (autK e s).toMonoidHom = hl.Y 4)
    (h128 : Nat.card (CFSG.pCore 2 ↥(hl.Y 7)) = 128) :
    CFSG.LocalAnalysis.WeakClosure81.InFSq 1
      (S ⊔ ((hl.Y 7).map e.symm.toMonoidHom).map K.subtype) := by
  classical
  let P7 : Subgroup Y := ((hl.Y 7).map e.symm.toMonoidHom).map K.subtype
  let N : Subgroup Y := S ⊔ P7
  change CFSG.LocalAnalysis.WeakClosure81.InFSq 1 N
  have hN_comm : P7 ⊔ S = N := by rw [sup_comm]
  have hP7K : P7 ≤ K := pull_le e (hl.Y 7)
  have hSN : S ≤ Subgroup.normalizer (P7 : Set Y) := fun t ht =>
    mem_normalizer_pull e (he_map_Y7_of_normalizes hl (he2_map_S_of_mem hl e he t ht))
  have hSylN : CFSG.QuasithinUnique.IsSylowTwoOf S N :=
    CFSG.Quasithin.B6.isSylowTwoOf_mono hS (show S ≤ N from le_sup_left) le_top
  have hTN : (S ⊓ K) ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 N : Set Y) :=
    ((inf_le_left : S ⊓ K ≤ S).trans (le_sup_left : S ≤ N)).trans
      (le_normalizer_pCoreOf 2 N)
  have hONleS : CFSG.Open.pCoreOf 2 N ≤ S := hSylN.pCoreOf_le
  have hO7eq : CFSG.Open.pCoreOf 2 P7 =
      ((CFSG.Open.pCoreOf 2 (hl.Y 7)).map e.symm.toMonoidHom).map K.subtype := by
    change CFSG.Open.pCoreOf 2 (((hl.Y 7).map e.symm.toMonoidHom).map K.subtype) = _
    rw [CFSG.Quasithin.H.ZTrans.pCoreOf_map_of_injective 2 K.subtype
        K.subtype_injective,
      CFSG.Quasithin.H.ZTrans.pCoreOf_map_of_injective 2 e.symm.toMonoidHom
        e.symm.injective]
  have hO7card : Nat.card (CFSG.Open.pCoreOf 2 P7) = 128 := by
    rw [hO7eq, Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
    exact (Subgroup.card_map_of_injective (hl.Y 7).subtype_injective).trans h128
  have hP7_N : P7 ≤ N := le_sup_right
  have hNnormP7 : N ≤ Subgroup.normalizer (P7 : Set Y) :=
    sup_le hSN Subgroup.le_normalizer
  have hO7leON : CFSG.Open.pCoreOf 2 P7 ≤ CFSG.Open.pCoreOf 2 N :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hP7_N hNnormP7
  have hONnormN : N ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 N : Set Y) :=
    le_normalizer_pCoreOf 2 N
  have hONP7 : CFSG.Open.pCoreOf 2 N ⊓ P7 = CFSG.Open.pCoreOf 2 P7 :=
    le_antisymm ((inf_comm (CFSG.Open.pCoreOf 2 N) P7).trans_le
      (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hP7_N)) (le_inf hO7leON (pCoreOf_le 2 P7))
  have hT_eq : S ⊓ P7 = S ⊓ K := by
    refine le_antisymm (fun z hz => ⟨hz.1, pull_le e (hl.Y 7) hz.2⟩)
      (le_inf inf_le_left ((le_pull_iff e inf_le_right).mpr (he ▸ hl.S_le_Y 7)))
  have hcardS : Nat.card ↥hl.S = 1024 := by
    rw [← Y0_eq_S hl, card_Y_idx hl (by norm_num)]
    rfl
  have hcardT : Nat.card ↥(S ⊓ K) = 1024 := by
    have h1 : Nat.card ↥((S ⊓ K).subgroupOf K) = Nat.card ↥hl.S := by
      rw [← he, Subgroup.card_map_of_injective e.injective]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h1
    rw [h1, hcardS]
  have hcardP7 : Nat.card ↥P7 = 21504 := by
    rw [show P7 = ((hl.Y 7).map e.symm.toMonoidHom).map K.subtype from rfl,
      Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
    exact card_Y7 hl
  have hONinfT : CFSG.Open.pCoreOf 2 N ⊓ (S ⊓ K) = CFSG.Open.pCoreOf 2 P7 := by
    calc CFSG.Open.pCoreOf 2 N ⊓ (S ⊓ K)
        = CFSG.Open.pCoreOf 2 N ⊓ (S ⊓ P7) := by rw [← hT_eq]
      _ = (CFSG.Open.pCoreOf 2 N ⊓ S) ⊓ P7 := by rw [inf_assoc]
      _ = CFSG.Open.pCoreOf 2 N ⊓ P7 := by rw [inf_of_le_left hONleS]
      _ = CFSG.Open.pCoreOf 2 P7 := hONP7
  have hO7leU : CFSG.Open.pCoreOf 2 P7 ≤
      ((hl.Y 3 ⊓ hl.Y 7).map e.symm.toMonoidHom).map K.subtype := by
    rw [hO7eq]
    refine pull_mono e (le_inf ((B6.isSylowTwoOf_mono hl.S_sylow (hl.S_le_Y 7) le_top).pCoreOf_le
      |>.trans (hl.S_le_Y 3)) (pCoreOf_le 2 (hl.Y 7)))
  have hL2odd : IsL2Odd (Bar2 P7) 7 := by
    let eP : ↥P7 ≃* ↥(hl.Y 7) :=
      ((Subgroup.subgroupOfEquivOfLe hP7K).symm.trans
        ((P7.subgroupOf K).equivMapOfInjective e.toMonoidHom e.injective)).trans
        (MulEquiv.subgroupCongr (map_pull e (hl.Y 7)))
    exact CFSG.Blueprint.LieModel.of_mulEquiv
      (QuotientGroup.congr (CFSG.pCore 2 ↥P7) (CFSG.pCore 2 ↥(hl.Y 7)) eP
        (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 eP)).symm
      (he_isL2Odd_bar2_Y7 hl h128)
  have h7P7 : IsL2Over17 (Bar2 P7) 7 :=
    ⟨7, 1, by norm_num, by norm_num, by norm_num, by norm_num, hL2odd⟩
  have hdich := (bar2_sup_data (L := P7) (R := S) hS.2.1 hSN h7P7).2
  rcases hdich with hL2 | hPGL
  · have hL2N : IsL2Over17 (Bar2 N) 7 := hN_comm ▸ hL2
    exfalso
    have hcardBar : Nat.card (Bar2 N) = 168 :=
      card_of_isL2Odd_seven (isL2Odd_seven_of_isL2Over17_seven hL2N)
    have hcardON : Nat.card ↥(CFSG.pCore 2 ↥N) = Nat.card ↥(CFSG.Open.pCoreOf 2 N) :=
      (Subgroup.card_map_of_injective N.subtype_injective).symm
    have hcardN : Nat.card ↥N = 168 * Nat.card ↥(CFSG.Open.pCoreOf 2 N) := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥N)
      rw [show Nat.card (↥N ⧸ CFSG.pCore 2 ↥N) = 168 from hcardBar, hcardON] at h
      exact h
    have hsup :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := S) (K := P7) hSN
    rw [show S ⊔ P7 = N from rfl, hcardN, hT_eq, hcardT, hcardP7] at hsup
    have hcardS_rel : Nat.card ↥S = 8 * Nat.card ↥(CFSG.Open.pCoreOf 2 N) := by omega
    have hcardTsup : Nat.card ↥(S ⊓ K ⊔ CFSG.Open.pCoreOf 2 N) = Nat.card ↥S := by
      have hprod :=
        CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
          (H := S ⊓ K) (K := CFSG.Open.pCoreOf 2 N) hTN
      rw [show (S ⊓ K) ⊓ CFSG.Open.pCoreOf 2 N =
          CFSG.Open.pCoreOf 2 N ⊓ (S ⊓ K) from
            inf_comm (S ⊓ K) (CFSG.Open.pCoreOf 2 N),
        hONinfT, hcardT, hO7card] at hprod
      omega
    have hONsupT : CFSG.Open.pCoreOf 2 N ⊔ (S ⊓ K) = S := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le hONleS inf_le_left) ?_
      rw [sup_comm, hcardTsup]
    have hsin : s ∈ CFSG.Open.pCoreOf 2 N ⊔ (S ⊓ K) := by rwa [hONsupT]
    obtain ⟨x, hxON, u, huT, hxu⟩ :=
      (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
        (H := CFSG.Open.pCoreOf 2 N) (K := S ⊓ K) hTN).mp hsin
    have huK : u ∈ K := huT.2
    have huSimage : e ⟨u, huK⟩ ∈ hl.S := by
      rw [← he]
      exact Subgroup.mem_map_of_mem e.toMonoidHom (Subgroup.mem_subgroupOf.mpr huT)
    have hfix_all_u : ∀ j : ℕ, (hl.Y j).map (autK e u⁻¹).toMonoidHom = hl.Y j := by
      intro j
      rw [autK_of_mem e (K.inv_mem huK)]
      have huinv : e ⟨u⁻¹, K.inv_mem huK⟩ = (e ⟨u, huK⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      rw [huinv]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.le_normalizer (hl.S_le_Y j (hl.S.inv_mem huSimage)))
    have hx_eq : x = s * u⁻¹ := by rw [hxu]; group
    have hUleP7 : ((hl.Y 3 ⊓ hl.Y 7).map e.symm.toMonoidHom).map K.subtype ≤ P7 :=
      pull_mono e inf_le_right
    have hONnormU : CFSG.Open.pCoreOf 2 N ≤ Subgroup.normalizer
        (((hl.Y 3 ⊓ hl.Y 7).map e.symm.toMonoidHom).map K.subtype : Set Y) := by
      rw [Subgroup.le_normalizer_iff_commutator_le_right]
      refine (Subgroup.commutator_mono le_rfl hUleP7).trans ((le_inf ?_ ?_).trans
        (hONP7.le.trans hO7leU))
      · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hP7_N.trans hONnormN)
      · exact Subgroup.le_normalizer_iff_commutator_le_right.mp
          ((pCoreOf_le 2 N).trans hNnormP7)
    have hxnormU : x ∈ Subgroup.normalizer
        (((hl.Y 3 ⊓ hl.Y 7).map e.symm.toMonoidHom).map K.subtype : Set Y) :=
      hONnormU hxON
    have hfixU : (hl.Y 3 ⊓ hl.Y 7).map (autK e x).toMonoidHom = hl.Y 3 ⊓ hl.Y 7 :=
      map_autK_of_mem_normalizer e hxnormU
    have hmapx : (hl.Y 3 ⊓ hl.Y 7).map (autK e x).toMonoidHom = hl.Y 4 ⊓ hl.Y 7 := by
      have hm : (hl.Y 3 ⊓ hl.Y 7).map (autK e s * autK e u⁻¹).toMonoidHom =
          ((hl.Y 3 ⊓ hl.Y 7).map (autK e u⁻¹).toMonoidHom).map
            (autK e s).toMonoidHom := by
        rw [Subgroup.map_map]; rfl
      rw [hx_eq, autK_mul, hm, Subgroup.map_inf_eq _ _ _ (autK e u⁻¹).injective,
        hfix_all_u 3, hfix_all_u 7, Subgroup.map_inf_eq _ _ _ (autK e s).injective, hswap,
        he_map_Y7_of_normalizes hl (he2_map_S_of_mem hl e he s hsS)]
    have hmeet : hl.Y 3 ⊓ hl.Y 7 = hl.Y 4 ⊓ hl.Y 7 := hfixU.symm.trans hmapx
    rw [he_Y3_inf_Y7 hl, he_Y4_inf_Y7 hl] at hmeet
    exact (Y_not_le hl (j := 8) (jj := 10) (by norm_num) (by norm_num) (by decide)) hmeet.le
  · have hPGLN : CFSG.Quasithin.F6.IsPGL2 7 (Bar2 N) := hN_comm ▸ hPGL
    exact inF_one_top_of_isPGL2_seven hPGLN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
