module

import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCFooteBlocks
import CFSG.RankThree.GF2n.Tim78Normal
import CFSG.RankThree.PartTwo.Sec15.Gagen155INorm
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofBFix

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Proof155Wx

theorem le_normalizer_w155 {A M X H : Subgroup G}
    (hHΔ : H ≤ Subgroup.normalizer (delta A (lB A) M : Set G))
    (hHX : H ≤ Subgroup.normalizer (X : Set G)) :
    H ≤ Subgroup.normalizer (w155 A M X : Set G) := by
  have hHO : H ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    hHX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hHC : H ≤ Subgroup.normalizer
      (centralizerSection X (CFSG.Open.pCoreOf 2 X) : Set G) :=
    Proof155w2.le_normalizer_centralizerSection hHX hHO
  have hHu : H ≤ Subgroup.normalizer (u155 A M X : Set G) :=
    Late.le_normalizer_inf hHΔ hHC
  exact Proof155w2.le_normalizer_inSubgroup_perfectResidual_of
    (le_normalizer_oPrimeResidualOf hHu)

theorem w155_le_u155 (A M X : Subgroup G) : w155 A M X ≤ u155 A M X :=
  (Subgroup.map_subtype_le _).trans (Sec14.oPrimeResidualOf_le_self 3 (u155 A M X))

theorem isPerfect_w155 (A M X : Subgroup G) : Group.IsPerfect ↥(w155 A M X) := by
  haveI : Group.IsPerfect ↥(CFSG.perfectResidual (b155 A M X)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect
  exact Group.IsPerfect.map (b155 A M X).subtype

theorem inf_centralizerSection_le_pCoreOf {P X : Subgroup G} (hP : IsPGroup 2 P)
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) :
    P ⊓ centralizerSection X (CFSG.Open.pCoreOf 2 X) ≤ CFSG.Open.pCoreOf 2 (P ⊔ X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 X with hO
  set V := P ⊓ centralizerSection X O with hV
  set D := V ⊔ O with hD
  have hPO : P ≤ Subgroup.normalizer (O : Set G) :=
    hPX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hVO : V ≤ Subgroup.normalizer (O : Set G) := fun _ hv => hv.2.2.1
  have hV2 : IsPGroup 2 V := hP.to_le inf_le_left
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hD2 : IsPGroup 2 D := by
    rw [hD]
    exact IsPGroup.to_sup_of_normal_right' hV2 hO2 hVO
  have hDH : D ≤ P ⊔ X := by
    rw [hD]
    exact sup_le (inf_le_left.trans le_sup_left)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans le_sup_right)
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := by
    rw [hV]
    exact Late.le_normalizer_inf Subgroup.le_normalizer
      (Proof155w2.le_normalizer_centralizerSection hPX hPO)
  have hPD : P ≤ Subgroup.normalizer (D : Set G) := by
    rw [hD]
    exact CFSG.RankThree.PartTwo.Sec14.le_normalizer_sup (A := P) (H := V) (K := O) hPV hPO
  have hXD : X ≤ Subgroup.normalizer (D : Set G) := by
    intro x hx
    refine CFSG.RankThree.PartTwo.Sec13.Item138Proof.mem_normalizer_of_map_le ?_
    rw [hD, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro y ⟨v, hv, rfl⟩
      have hcomm : ⁅x, v⁆ ∈ O := hv.2.2.2 x hx
      have he : (MulAut.conj x).toMonoidHom v = ⁅x, v⁆ * v := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [he]
      have hcommD : ⁅x, v⁆ ∈ D := Subgroup.mem_sup_right hcomm
      have hvV : v ∈ V := ⟨hv.1, hv.2⟩
      have hvD : v ∈ D := Subgroup.mem_sup_left hvV
      exact D.mul_mem hcommD hvD
    · have hmap : O.map (MulAut.conj x).toMonoidHom = O :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) X hx)
      rw [hmap]
      exact le_sup_right
  have hHD : P ⊔ X ≤ Subgroup.normalizer (D : Set G) := sup_le hPD hXD
  exact le_sup_left.trans
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) hDH hHD hD2)

theorem isSubnormal_w155 {A M X I₀ H : Subgroup G}
    (hBU : b155 A M X ≤ u155 A M X ⊓ I₀)
    (hI₀u : I₀ ≤ Subgroup.normalizer (u155 A M X : Set G)) (hI₀H : I₀ ≤ H)
    (hI₀Hn : (I₀.subgroupOf H).Normal) :
    CFSG.Open.IsSubnormal (w155 A M X) H := by
  have hWB : w155 A M X ≤ b155 A M X := Subgroup.map_subtype_le _
  have hBWn : ((w155 A M X).subgroupOf (b155 A M X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWB).mpr
      (Proof155w2.le_normalizer_inSubgroup_perfectResidual_of
        (H := b155 A M X) Subgroup.le_normalizer)
  have hBUIn : ((b155 A M X).subgroupOf (u155 A M X ⊓ I₀)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBU).mpr
      (inf_le_left.trans (le_normalizer_oPrimeResidualOf Subgroup.le_normalizer))
  have hUIn : ((u155 A M X ⊓ I₀).subgroupOf I₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
      (Late.le_normalizer_inf hI₀u Subgroup.le_normalizer)
  exact CFSG.Open.IsSubnormal.step hWB hBWn
    (CFSG.Open.IsSubnormal.step hBU hBUIn
      (CFSG.Open.IsSubnormal.step inf_le_right hUIn
        (CFSG.Open.IsSubnormal.step hI₀H hI₀Hn (CFSG.Open.IsSubnormal.refl H))))

structure Facts155W (A X Y M P : Subgroup G) : Prop where
  mem_x4 : X ∈ scriptY4 A (lB A)
  le_xy : X ≤ Y
  mem_mx : M ∈ CFSG.maximalTwoLocalsContaining ((X ⊔ A : Subgroup G) : Set G)
  le_xm : X ≤ M
  le_am : A ≤ M
  mem_m2 : M ∈ scriptY2 A
  fit_m : generalizedFitting ↥M = CFSG.pCore 2 ↥M
  le_x_i0 : X ≤ oPrimeResidualOf 3 (delta A (lB A) M)
  i0_le_deltaZero : oPrimeResidualOf 3 (delta A (lB A) M) ≤ deltaZero A (lB A) M
  i0_le_normalizer_x : oPrimeResidualOf 3 (delta A (lB A) M) ≤ Subgroup.normalizer (X : Set G)
  normal_i0 : ((oPrimeResidualOf 3 (delta A (lB A) M)).subgroupOf M).Normal
  w_le_i0 : w155 A M X ≤ oPrimeResidualOf 3 (delta A (lB A) M)
  i0_le_normalizer_w :
    oPrimeResidualOf 3 (delta A (lB A) M) ≤ Subgroup.normalizer (w155 A M X : Set G)
  a_le_normalizer_w : A ≤ Subgroup.normalizer (w155 A M X : Set G)
  subnormal_w_m : CFSG.Open.IsSubnormal (w155 A M X) M
  subnormal_w_delta : CFSG.Open.IsSubnormal (w155 A M X) (delta A (lB A) M)
  fit_w : generalizedFitting ↥(w155 A M X) = CFSG.pCore 2 ↥(w155 A M X)
  mem_p : P ∈ scriptQ A (lB A)
  le_p : P ≤ M ⊓ Subgroup.normalizer (X : Set G)
  isPGroup_p : IsPGroup 2 P
  p_le_delta : P ≤ delta A (lB A) M
  p_le_normalizer_w : P ≤ Subgroup.normalizer (w155 A M X : Set G)
  p_le_normalizer_r : P ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)
  inf_sup_eq : P ⊓ (CFSG.Open.pCoreOf 2 Y ⊔ w155 A M X) = CFSG.Open.pCoreOf 2 Y

theorem facts155W_of
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h148 : Item148 A (lB A))
    (h149 : Item149 A (lB A))
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) : Facts155W A X Y M P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hXY : X ≤ Y := hC.res ▸ Sec14.oPrimeResidualOf_le_self 3 Y
  have hMX : M ∈ CFSG.maximalTwoLocalsContaining ((X ⊔ A : Subgroup G) : Set G) := by
    refine ⟨hC.mem_m.1, ?_⟩
    have hAY : (A ⊔ Y : Subgroup G) ≤ M := hC.mem_m.2
    exact fun z hz => (sup_le (hXY.trans (le_sup_right.trans hAY))
      (le_sup_left.trans hAY)) hz
  obtain ⟨hXM, hAM, hM2, hF⟩ := facts_of_mem_maximalTwoLocalsContaining h hMX
  have hMY : M ∈ scriptY A := hM2.1
  set I := delta A (lB A) M with hIdef
  set I₀ := oPrimeResidualOf 3 I with hI₀def
  obtain ⟨heq149, hI₀norm, -, -⟩ := h149 M hMY
  have hI₀Δ : I₀ ≤ deltaZero A (lB A) M := by
    rw [hI₀def, hIdef, heq149]
    exact (Sec14.oPrimeResidualOf_le_self 3 _).trans (Sec14.inSubgroup_oResidual_le_self 2 _)
  have hI₀I : I₀ ≤ I := Sec14.oPrimeResidualOf_le_self 3 I
  have hI₀M : I₀ ≤ M := hI₀I.trans (delta_le M)
  have hXI₀ : X ≤ I₀ := le_oPrimeResidualOf_delta hX4 hXM
  have hI₀X : I₀ ≤ Subgroup.normalizer (X : Set G) := by
    rw [hI₀def, hIdef]
    exact Proof155INorm.oPrimeResidualOf_le_normalizer_of_item148 h h148 h149 hMX hX4
      hE.mem_x (delta_le M)
  have hBI₀ : b155 A M X ≤ I₀ := by
    rw [hI₀def, hIdef]
    exact oPrimeResidualOf_mono (p := 3) (K := u155 A M X) inf_le_left
  have hWB : w155 A M X ≤ b155 A M X := Subgroup.map_subtype_le _
  have hWI₀ : w155 A M X ≤ I₀ := hWB.trans hBI₀
  have hNC : Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (centralizerSection X (CFSG.Open.pCoreOf 2 X) : Set G) :=
    Proof155w2.le_normalizer_centralizerSection le_rfl
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hI₀u : I₀ ≤ Subgroup.normalizer (u155 A M X : Set G) := by
    refine Late.le_normalizer_inf ?_ ?_
    · exact hI₀I.trans Subgroup.le_normalizer
    · exact hI₀X.trans hNC
  have hI₀W : I₀ ≤ Subgroup.normalizer (w155 A M X : Set G) :=
    Proof155w2.le_normalizer_inSubgroup_perfectResidual_of (le_normalizer_oPrimeResidualOf hI₀u)
  have hAW : A ≤ Subgroup.normalizer (w155 A M X : Set G) :=
    le_normalizer_w155 (le_normalizer_delta M) hX4.1.2
  have hI₀Mn : (I₀.subgroupOf M).Normal := by
    rw [hI₀def, hIdef, heq149]
    exact hI₀norm
  have hI₀In : (I₀.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hI₀I).mpr
      (le_normalizer_oPrimeResidualOf Subgroup.le_normalizer)
  have hBUI : b155 A M X ≤ u155 A M X ⊓ I₀ :=
    le_inf (Sec14.oPrimeResidualOf_le_self 3 _) hBI₀
  have hWMsubn : CFSG.Open.IsSubnormal (w155 A M X) M :=
    isSubnormal_w155 hBUI hI₀u hI₀M hI₀Mn
  have hWIsubn : CFSG.Open.IsSubnormal (w155 A M X) I :=
    isSubnormal_w155 hBUI hI₀u hI₀I hI₀In
  have hMchar : M ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) ≤
      CFSG.Open.pCoreOf 2 M :=
    CFSG.RankThree.GF2n.Tim78.inf_centralizer_le_of_generalizedFitting_eq hF
  have hWfit : generalizedFitting ↥(w155 A M X) = CFSG.pCore 2 ↥(w155 A M X) :=
    Sec19.SimsTheoremC.generalizedFitting_eq_pCore_of_isSubnormal_of_charTwo hMchar hWMsubn
  have hP𝓠 : P ∈ scriptQ A (lB A) := hE.mem_p.prop.1.1
  have hPle : P ≤ M ⊓ Subgroup.normalizer (X : Set G) := hE.mem_p.prop.1.2
  have hPM : P ≤ M := hPle.trans inf_le_left
  have hPX : P ≤ Subgroup.normalizer (X : Set G) := hPle.trans inf_le_right
  have hP2 : IsPGroup 2 P := isPGroup_of_mem_scriptQPi Nat.prime_two hE.mem_p.prop
  have hPΔ : P ≤ delta A (lB A) M := le_delta hP𝓠 hPM
  have hPW : P ≤ Subgroup.normalizer (w155 A M X : Set G) :=
    le_normalizer_w155 (hPΔ.trans Subgroup.le_normalizer) hPX
  set R := CFSG.Open.pCoreOf 2 Y with hRdef
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := by
    rw [hRdef, hE.eq_rq]
    exact (le_sup_left : P ≤ P ⊔ X).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) (P ⊔ X))
  have hinfR : P ⊓ (R ⊔ w155 A M X) = R := by
    refine le_antisymm ?_ (le_inf hRP le_sup_left)
    intro x hx
    have hxP : x ∈ P := hx.1
    have hxD : x ∈ ((R ⊔ w155 A M X : Subgroup G) : Set G) := hx.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right R (w155 A M X) (hRP.trans hPW)] at hxD
    obtain ⟨r, hr, w, hw, rfl⟩ := hxD
    have hwP : w ∈ P := by
      have h1 : r⁻¹ * (r * w) ∈ P := P.mul_mem (P.inv_mem (hRP hr)) hxP
      simpa using h1
    have hwU : w ∈ u155 A M X := w155_le_u155 A M X hw
    have hwR : w ∈ R := by
      rw [hRdef, hE.eq_rq]
      exact inf_centralizerSection_le_pCoreOf hP2 hPX ⟨hwP, hwU.2⟩
    exact R.mul_mem hr hwR
  exact ⟨hX4, hXY, hMX, hXM, hAM, hM2, hF, hXI₀, hI₀Δ, hI₀X, hI₀Mn, hWI₀, hI₀W, hAW, hWMsubn,
    hWIsubn, hWfit, hP𝓠, hPle, hP2, hPΔ, hPW, hPR, hinfR⟩

end Proof155Wx

end CFSG.RankThree.PartTwo.Sec15
