module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155SplitDefs
public import CFSG.RankThree.PartTwo.Sec15.Gagen155INorm
import CFSG.RankThree.PartTwo.Sec15.Gagen155BXWShape
import CFSG.RankThree.PartTwo.Sec15.Gagen155BXWLift
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem step155BXW_of
    {A : Subgroup G} {c : G} {L : Subgroup G} (h148 : Item148 A (lB A))
    (h149 : Item149 A (lB A)) : Step155BXW A c L := by
  intro h X K Y M T P hC hmax hab hE
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hXY : X ≤ Y := hC.res ▸ Sec14.oPrimeResidualOf_le_self 3 Y
  have hMX : M ∈ CFSG.maximalTwoLocalsContaining ((X ⊔ A : Subgroup G) : Set G) := by
    refine ⟨hC.mem_m.1, ?_⟩
    have hAY : (A ⊔ Y : Subgroup G) ≤ M := hC.mem_m.2
    exact fun z hz => (sup_le (hXY.trans (le_sup_right.trans hAY))
      (le_sup_left.trans hAY)) hz
  obtain ⟨hXM, hAM, hM2, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hMX
  letI : (ker148 A M).Normal := ker148_normal hM2.1.2
  set I := delta A (lB A) M with hI
  set I₀ := oPrimeResidualOf 3 I with hI₀
  obtain ⟨heq149, -, -⟩ := h149 M hM2.1
  have hI₀Δ : I₀ ≤ deltaZero A (lB A) M := by
    rw [hI₀, hI, heq149]
    exact (Sec14.oPrimeResidualOf_le_self 3 _).trans (Sec14.inSubgroup_oResidual_le_self 2 _)
  have hXI₀ : X ≤ I₀ := by
    rw [hI₀, hI]
    exact le_oPrimeResidualOf_delta hX4 hXM
  have hI₀M : I₀ ≤ M := by
    rw [hI₀, hI]
    exact (Sec14.oPrimeResidualOf_le_self 3 _).trans (delta_le M)
  have hI₀X : I₀ ≤ Subgroup.normalizer (X : Set G) := by
    rw [hI₀, hI]
    exact Proof155INorm.oPrimeResidualOf_le_normalizer_of_item148 h h148 h149 hMX hX4
      hE.mem_x (delta_le M)
  have hBI₀ : b155 A M X ≤ I₀ := by
    rw [hI₀, hI]
    exact oPrimeResidualOf_mono (p := 3) (K := u155 A M X) inf_le_left
  have hWB : w155 A M X ≤ b155 A M X := Subgroup.map_subtype_le _
  have hWI₀ : w155 A M X ≤ I₀ := hWB.trans hBI₀
  have hWM : w155 A M X ≤ M := hWI₀.trans hI₀M
  have hNC : Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (centralizerSection X (CFSG.Open.pCoreOf 2 X) : Set G) :=
    Proof155w2.le_normalizer_centralizerSection le_rfl
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hI₀u : I₀ ≤ Subgroup.normalizer (u155 A M X : Set G) := by
    refine Late.le_normalizer_inf ?_ ?_
    · exact (Sec14.oPrimeResidualOf_le_self 3 (delta A (lB A) M)).trans Subgroup.le_normalizer
    · exact hI₀X.trans hNC
  have hI₀B : I₀ ≤ Subgroup.normalizer (b155 A M X : Set G) :=
    le_normalizer_oPrimeResidualOf hI₀u
  have hI₀W : I₀ ≤ Subgroup.normalizer (w155 A M X : Set G) :=
    Proof155w2.le_normalizer_inSubgroup_perfectResidual_of hI₀B
  have hI₀XW : I₀ ≤ Subgroup.normalizer ((X ⊔ w155 A M X : Subgroup G) : Set G) :=
    Sec14.le_normalizer_sup hI₀X hI₀W
  set D := img148 A M (deltaZero A (lB A) M) with hD
  set V := (img148 A M X).subgroupOf D with hV
  have hXD : X ≤ deltaZero A (lB A) M := hXI₀.trans hI₀Δ
  have hDX : img148 A M X ≤ D := by
    rw [hD]
    exact img148_mono hXD
  have hVsub : V.IsSubnormal := by
    rw [hV, hD]
    exact Proof153Twin3.isSubnormal_img_subgroupOf hAM hE.mem_x
  obtain ⟨eY⟩ := Proof155INorm.nonempty_quot_equiv_img hAM hE.mem_x hXD
  have hVq : IsQuasisimple ↥V := CFSG.LocalCores.isQuasisimple_of_mulEquiv eY
    (Proof1515.isQuasisimple_quot_pPrimeCore hX4)
  obtain ⟨E, hVE, hEp, hE3, hsup⟩ :=
    Proof155BXW.exists_split_of_item148 h h148 hM2 V hVsub hVq
  set E' := E.map D.subtype with hE'
  have hE'p : Group.IsPerfect ↥E' := by
    rw [hE']
    haveI : Group.IsPerfect ↥E := hEp
    exact Group.IsPerfect.map D.subtype
  have hE'B : E' ≤ img148 A M (b155 A M X) := by
    rw [hE']
    let S : Set ↥D := {x | x ∈ E ∧ ∃ k : ℕ, x ^ 3 ^ k = 1}
    have hES : E = Subgroup.closure S := by
      rw [← hE3]
      exact Sec14.oPrimeResidualOf_eq_closure 3 E
    have hVcent : V ≤ Subgroup.centralizer (E : Set ↥D) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVE
    have hgen : ∀ x ∈ S, (x : ↥(M ⊔ A) ⧸ ker148 A M) ∈ img148 A M (b155 A M X) := by
      intro x hx
      have hcomm : ∀ y ∈ img148 A M X,
          y * (x : ↥(M ⊔ A) ⧸ ker148 A M) =
            (x : ↥(M ⊔ A) ⧸ ker148 A M) * y := by
        intro y hy
        have hyD : y ∈ D := hDX hy
        have hmemV : (⟨y, hyD⟩ : ↥D) ∈ V := by
          rw [hV]
          exact Subgroup.mem_subgroupOf.mpr hy
        have hcent :=
          ((Subgroup.mem_centralizer_iff.mp (hVcent hmemV)) x hx.1).symm
        exact congrArg (fun z : ↥D => (z : ↥(M ⊔ A) ⧸ ker148 A M)) hcent
      rcases hx.2 with ⟨k, hk⟩
      have hek : D.subtype x ^ 3 ^ k = 1 := by
        rw [← map_pow, hk, map_one]
      exact Proof155BXW.mem_img148_b155_of_commute h h148 h149 hMX hX4 hE.mem_x x.2 hek hcomm
    calc E.map D.subtype = (Subgroup.closure S).map D.subtype := by rw [hES]
      _ = Subgroup.closure (D.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := D.subtype) S)
      _ ≤ img148 A M (b155 A M X) := by
        refine (Subgroup.closure_le (K := img148 A M (b155 A M X))).2 ?_
        rintro _ ⟨x, hxS, rfl⟩
        exact hgen x hxS
  have hE'W : E' ≤ img148 A M (w155 A M X) := by
    refine Proof155BXW.le_img148_inSubgroup_perfectResidual (B := b155 A M X)
      (hBI₀.trans (hI₀M.trans le_sup_left)) hE'p hE'B
  have hDsup : img148 A M X ⊔ E' = D := by
    rw [hE']
    have htop : (⊤ : Subgroup ↥D).map D.subtype = D := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have h := congrArg (Subgroup.map D.subtype) hsup
    rw [hV, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hDX, htop] at h
    exact h
  have hDle : D ≤ img148 A M X ⊔ img148 A M (w155 A M X) := by
    rw [← hDsup]
    exact sup_le_sup le_rfl hE'W
  have hle : img148 A M (oPrimeResidualOf 3 (u155 A M X)) ≤
      img148 A M (X ⊔ w155 A M X) := by
    rw [img148_sup (hXM.trans le_sup_left) (hWM.trans le_sup_left)]
    exact (img148_mono (hBI₀.trans hI₀Δ)).trans hDle
  have hXWI₀ : X ⊔ w155 A M X ≤ I₀ := sup_le hXI₀ hWI₀
  exact Proof155BXW.oPrimeResidualOf_le_of_img148_le
    (K := u155 A M X) (H := X ⊔ w155 A M X) (I := I₀)
    hBI₀ hXWI₀ hI₀M hI₀XW hle

theorem step155BXWR_of
    (h148 : Item148R) (h149 : Sec16.Item149S14) : Step155BXWR :=
  fun G _ _ A c L hR => step155BXW_of (h148 G A c L hR) (h149 G A c L hR.toSec14Std)

end CFSG.RankThree.PartTwo.Sec15
