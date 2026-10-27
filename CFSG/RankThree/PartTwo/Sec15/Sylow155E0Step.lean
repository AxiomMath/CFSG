module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155E0
public import CFSG.RankThree.PartTwo.Sec15.Sylow155B3S
public import CFSG.RankThree.PartTwo.Sec15.Sylow155Center
public import CFSG.RankThree.PartTwo.Sec15.Sylow155NO
import CFSG.RankThree.PartTwo.Sec15.Gagen155BXW
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PCases
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiag
import CFSG.RankThree.PartTwo.Sec14.Item14Res7ProofDescFix
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21GenA6
public import CFSG.RankThree.PartTwo.Sec15.Sylow155TwinB

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Sylow155E0

theorem delta_le_n155_of_conj_of_host
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hH : delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) ≤ n155 A K)
    (hconj : ∀ V ∈ scriptQ A (lB A), V ≤ M → ∃ w ∈ n155 A K,
      w ∈ Subgroup.normalizer (A : Set G) ∧ V.map (MulAut.conj w).toMonoidHom ≤
        Subgroup.normalizer
          ((CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X) : Subgroup G) : Set G)) :
    delta A (lB A) M ≤ n155 A K := by
  have hHinv := Sylow155S.sup_mem_invariant hC hE hRP
  have hHU := Sylow155S.sup_le_u155 hE hRP
  have hPH := Sylow155S.p_le_normalizer_sup hE
  refine sSup_le fun V hV => ?_
  obtain ⟨w, hwN, hwA, hVw⟩ := hconj V hV.1 hV.2
  have hVw𝓠 : V.map (MulAut.conj w).toMonoidHom ∈ scriptQ A (lB A) := rank3II_14_4_5_lB hwA hV.1
  have hVwN := Sylow155B1.le_n155_of_le_normalizer_host h h146 hC hE hRP hHinv hHU hPH le_sup_left
    hH hVw𝓠 hVw
  intro v hv
  have hwv : w * v * w⁻¹ ∈ n155 A K := hVwN ⟨v, hv, rfl⟩
  have hv' : v = w⁻¹ * (w * v * w⁻¹) * w := by group
  rw [hv']
  exact (n155 A K).mul_mem ((n155 A K).mul_mem ((n155 A K).inv_mem hwN) hwv) hwN

theorem delta_le_n155_of_w_le_of_host
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hH : delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) ≤ n155 A K)
    (hBXW : b155 A M X ≤ X ⊔ w155 A M X) (hW : w155 A M X ≤ pPrimeCoreOf 3 (u155 A M X)) :
    delta A (lB A) M ≤ n155 A K := by
  have hRU := Sylow155C3.r_le_pPrimeCoreOf_u155 hE hRP hBXW hW
  rw [sup_eq_right.mpr hRU] at hH
  exact Sylow155B1.delta_le_n155_of_delta_host_le h h146 hC hE hRP
    (Sylow155B1.pPrimeCoreOf_u155_mem_invariant hC) (pPrimeCoreOf_le 3 _)
    (normalizer_le_normalizer_pPrimeCoreOf 3 _) hRU hIX hH

open Equiv in
theorem delta_le_n155_of_a5_of_host
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hH : delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) ≤ n155 A K)
    (hf : Proof155Wx.Facts155W A X Y M P)
    (hBXW : b155 A M X ≤ X ⊔ w155 A M X) (hBN : b155 A M X ≤ n155 A K) [(ker148 A M).Normal]
    (hφ : Nonempty (↥(img148 A M (w155 A M X)) ≃* alternatingGroup (Fin 5)))
    (hNO : Sylow155B2.InnerOn A M X) : delta A (lB A) M ≤ n155 A K := by
  haveI : ((pPrimeCoreOf 3 M).subgroupOf (w155 A M X)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Sylow155B2.w155_le_normalizer A M X)
  obtain ⟨ψ⟩ := Sylow155R.nonempty_quot_equiv_img148 (A := A) (Sylow155B2.w155_le_m A M X)
  obtain ⟨φ'⟩ := hφ
  let autE : Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
        (by norm_num))
  exact delta_le_n155_of_conj_of_host h h146 hC hE hRP hH fun V hV hVM =>
    Sylow155B2.exists_conj_le_normalizer (ψ.trans φ') autE (fun _ => rfl) h hC hE hRP hIX hf
      hBXW hBN hNO hV hVM

theorem delta_le_n155_of_tripleCover_of_host
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hH : delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) ≤ n155 A K)
    (hf : Proof155Wx.Facts155W A X Y M P)
    (hBXW : b155 A M X ≤ X ⊔ w155 A M X) (hBN : b155 A M X ≤ n155 A K) [(ker148 A M).Normal]
    (hφ : Sec4.IsTripleCover ↥(img148 A M (w155 A M X)) (alternatingGroup (Fin 6)) ∧
      CFSG.IsQuasisimple ↥(img148 A M (w155 A M X))) :
    delta A (lB A) M ≤ n155 A K := by
  haveI : ((pPrimeCoreOf 3 M).subgroupOf (w155 A M X)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Sylow155B2.w155_le_normalizer A M X)
  obtain ⟨ψ⟩ := Sylow155R.nonempty_quot_equiv_img148 (A := A) (Sylow155B2.w155_le_m A M X)
  have htc := Proof15Res8Diag.isTripleCover_congr ψ.symm hφ.1
  have hcard := Res7DescFix.card_eq_of_isTripleCover_a6 htc
  have hperf : commutator (↥(w155 A M X) ⧸ (pPrimeCoreOf 3 M).subgroupOf (w155 A M X)) = ⊤ := by
    haveI := hφ.2.1
    exact Group.isPerfect_def.mp
      (Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective)
  obtain ⟨hZ, ⟨e⟩⟩ := htc
  obtain ⟨e6⟩ := QuasithinUnique.Out21.A6.exists_psl29_equiv
  exact delta_le_n155_of_conj_of_host h h146 hC hE hRP hH fun V hV hVM =>
    Sylow155B3.exists_conj_le_normalizer6 (e.trans e6.symm) hperf hZ hcard h hC hE hRP hIX hf
      hBXW hBN hV hVM

end Sylow155E0

section Proof

theorem Sylow155E0.delta_le_n155_of_cases_of_host
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h143 : Ronan148Q.Item143Q A (lB A)) (h146 : Item146 A (lB A))
    (h148 : Item148 A (lB A)) (h149 : Item149 A (lB A))
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hBXW : b155 A M X ≤ X ⊔ w155 A M X)
    (hH : delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) ≤ n155 A K)
    (hBN : b155 A M X ≤ n155 A K) :
    delta A (lB A) M ≤ n155 A K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : Proof155Wx.Facts155W A X Y M P := Proof155Wx.facts155W_of h h148 h149 hC hE hRP
  letI : (ker148 A M).Normal := ker148_normal hf.mem_m2.1.2
  by_cases hWO : w155 A M X ≤ pPrimeCoreOf 3 M
  · exact Sylow155E0.delta_le_n155_of_w_le_of_host h h146 hC hE hRP hIX hH hBXW
      (Sylow155C3.w155_le_pPrimeCoreOf_of_coprime (Nat.Coprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le hWO) (coprime_card_pPrimeCoreOf 3 M)))
  · obtain ⟨-, -, -, -, -, hφ | hφ⟩ := Proof155P.cases148_of_not_le h h148 h149 hf hE.mem_x hWO
    · exact Sylow155E0.delta_le_n155_of_a5_of_host h h146 hC hE hRP hIX hH hf hBXW hBN hφ
        (Sylow155NO.innerOn_of_a5 h h134 h48 h143 h148 hf hE.mem_x hIX hφ)
    · exact Sylow155E0.delta_le_n155_of_tripleCover_of_host h h146 hC hE hRP hIX hH hf hBXW hBN
        hφ

theorem step155FrattiniNWP_of_hostE0 (hst : StellmacherKP)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h134 : Item134) (h48 : Sec4.Item4_8)
    (h143 : Ronan148Q.Item143Q A (lB A)) (h146 : Item146 A (lB A)) (h148 : Item148 A (lB A))
    (h149 : Item149 A (lB A)) (hE0 : Step155HostE0W A c L) : Step155FrattiniNWP A c L :=
  fun h X K Y M T P hC hmax hab hE hRP hBN =>
    have hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) :=
      Sylow155T.delta_le_normalizer_x h hC hE
        (Sylow155T.card_center_le_three_of_ctx155 h h148 h134 h48 hC)
    Sylow155E0.delta_le_n155_of_cases_of_host h h134 h48 h143 h146 h148 h149 hC hE hRP hIX
      (step155BXW_of h148 h149 h X K Y M T P hC hmax hab hE)
      (Sylow155E0.delta_sup_le_n155_of_e0 hst h h146 hC hE hRP
        (hE0 h X K Y M T P hC hmax hab hE h146 hRP hIX)) hBN

theorem step155FrattiniNWPR_of_hostE0R (hst : StellmacherKP)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h143 : Ronan148Q.Item143QS14) (h146 : Item146S14)
    (h148 : Item148R) (h149 : Sec16.Item149S14) (hE0 : Step155HostE0WR) :
    Step155FrattiniNWPR := fun G _ _ A c L hR =>
  step155FrattiniNWP_of_hostE0 hst h134 h48 (h143 G A c L hR.toSec14Std)
    (h146 G A c L hR.toSec14Std) (h148 G A c L hR) (h149 G A c L hR.toSec14Std) (hE0 G A c L hR)

end Proof

end CFSG.RankThree.PartTwo.Sec15
