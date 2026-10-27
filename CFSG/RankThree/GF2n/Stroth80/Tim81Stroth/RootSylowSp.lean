module

public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.SpMain
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTILocal
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Tim78
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem tiConfig_MbarPrime_sp [(Q.subgroupOf M).Normal]
    (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hElt : ElementwiseNormalizerHyp M Q Z0)
    (hmaxAb : IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q)
    (hF2 : Step85F2Statement)
    (h85 : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))) :
    TIConfig (⊤ : Subgroup (Hbar M Q Z))
      ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      (inSubgroup (pCore 2) (MbarPrime M Q Z Z0)) := by
  haveI hFinH : Finite (Hbar M Q Z) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let V : Subgroup (Hbar M Q Z) := (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))
  let M' : Subgroup (Hbar M Q Z) := MbarPrime M Q Z Z0
  have hE : Assembly.IsElemAbelian 2 V := isElemAbelian_bar_Z0_subgroupOf_sp h51 hA hc hs hZ0
  have hTI : IsTI V := isTI_bar_Z0_sp hc hs hZ0 hElt
  have hNV : M' = Subgroup.normalizer (V : Set (Hbar M Q Z)) :=
    MbarPrime_eq_normalizer_bar_Z0_sp hc hs hZ0
  have hK : NormIn (⊤ : Subgroup (Hbar M Q Z)) V = M' := by
    rw [NormIn, top_inf_eq]
    exact hNV.symm
  have hnormR : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
  have hCNH0 : hc.CN t ≤ H0 M Z := fun y hy => hc.Rt_le_H0 t (Ctx.mem_CN.mp hy).1
  have hCNN : hc.CN t ≤ NormH0 M Z Z0 := fun y hy =>
    Subgroup.mem_inf.mpr ⟨hCNH0 hy, IsCentrePre.mem_normalizer hZ0 hnormR (Ctx.mem_CN.mp hy).1⟩
  have hNbarM' : (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) ≤ M' :=
    Subgroup.subgroupOf_mono _ (Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hCNN))
  refine
    { V_le := le_top
      V_ne_bot := bar_Z0_subgroupOf_ne_bot_sp hc hs hZ0
      V_pgroup := CFSG.Open.IsElemAbelian.isPGroup hE
      V_comm := fun x hx y hy => CFSG.Open.IsElemAbelian.comm hE hx hy
      ti := ?_
      N_le := ?_
      N_normal := ?_
      N_pgroup := (inSubgroup_pCore_two M').1
      pcore_le := ?_
      cent_le := ?_
      VN_comm := ?_
      maxAb := ?_ }
  ·
    intro g x hx hx1 hgx
    have hxconj : x ∈ conjSubgroup g⁻¹ V := by
      rw [mem_conjSubgroup]
      simpa using hgx
    have hne : V ⊓ conjSubgroup g⁻¹ V ≠ ⊥ := by
      intro hbot
      have hmem : x ∈ (⊥ : Subgroup (Hbar M Q Z)) := by
        rw [← hbot]
        exact Subgroup.mem_inf.mpr ⟨hx, hxconj⟩
      exact hx1 (Subgroup.mem_bot.mp hmem)
    rcases hTI g⁻¹ with hbot | heq
    · exact absurd hbot hne
    · have hle : V ≤ conjSubgroup g⁻¹ V := by
        calc V = V ⊓ conjSubgroup g⁻¹ V := heq.symm
          _ ≤ conjSubgroup g⁻¹ V := inf_le_right
      have hEqinv : conjSubgroup g⁻¹ V = V :=
        (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])).symm
      have hEq : conjSubgroup g V = V := by
        calc conjSubgroup g V = conjSubgroup g (conjSubgroup g⁻¹ V) := by rw [hEqinv]
          _ = conjSubgroup (g * g⁻¹) V := conjSubgroup_conjSubgroup g g⁻¹ V
          _ = conjSubgroup (1 : Hbar M Q Z) V := by rw [mul_inv_cancel]
          _ = V := conjSubgroup_one V
      exact (conjSubgroup_eq_self_iff).mp hEq
  ·
    rw [hK]
    exact (inSubgroup_pCore_two M').2.1
  ·
    intro k hk
    rw [hK] at hk
    exact (inSubgroup_pCore_two M').2.2 hk
  ·
    intro P hP hPn hP2
    rw [hK] at hP hPn
    have hPnorm : (P.subgroupOf M').Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hPn
    have hPp : IsPGroup 2 (P.subgroupOf M') := hP2.comap_subtype
    have hle : P.subgroupOf M' ≤ pCore 2 M' :=
      CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hPnorm hPp
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hP hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  ·
    intro k hk hkc
    rw [hK] at hk
    have hFp : generalizedFitting ↥M' = pCore 2 ↥M' :=
      generalizedFitting_MbarPrime_sp hc hs hZ0 hF2
    have hkC : (⟨k, hk⟩ : ↥M') ∈
        Subgroup.centralizer ((pCore 2 ↥M') : Set ↥M') := by
      intro n hn
      have hnk : (n : Hbar M Q Z) ∈ inSubgroup (pCore 2) M' :=
        Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
      exact Subtype.ext (hkc (n : Hbar M Q Z) hnk).symm
    have hkC' : (⟨k, hk⟩ : ↥M') ∈
        Subgroup.centralizer ((generalizedFitting ↥M') : Set ↥M') := by
      rw [hFp]
      exact hkC
    have hmem := CFSG.centralizer_generalizedFitting_le ↥M' hkC'
    rw [hFp] at hmem
    exact Subgroup.mem_map.mpr ⟨⟨k, hk⟩, hmem, rfl⟩
  ·
    intro x hx n hn
    have hpc : pCore 2 M' =
        ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf M' := by
      rw [← generalizedFitting_MbarPrime_sp hc hs hZ0 hF2]
      exact generalizedFitting_MbarPrime_eq_of_fitting (N := hc.CN t) h85
    have hNbar : inSubgroup (pCore 2) M' =
        (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := by
      rw [inSubgroup, hpc, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNbarM']
    rw [hNbar] at hn
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
    obtain ⟨b, hb, hbn⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hn)
    have haZ0 : (a : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp ha
    have hbR : (b : G) ∈ Rt M (LB M Q B) t :=
      (Ctx.mem_CN.mp (Subgroup.mem_subgroupOf.mp hb)).1
    have hcommQ : ⁅(a : G), (b : G)⁆ ∈ Q := ((hZ0 (a : G)).mp haZ0).2 (b : G) hbR
    apply Subtype.ext
    change (x : Mbar M Q) * (n : Mbar M Q) = (n : Mbar M Q) * (x : Mbar M Q)
    rw [← hax, ← hbn]
    have hmem : ⁅a, b⁆ ∈ Q.subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr (by simpa [commutatorElement_def] using hcommQ)
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  ·
    intro A hVA hAK hAn hAab
    rw [hK] at hAK hAn
    have hmax := maxAb_bar_Z0_comm (Z0 := Z0) hmaxAb
      ((isElemAbelian_bar_Z0_sp h51 hA hc hs hZ0).subgroupOf (bar M Q (H0 M Z)))
    have hAV : A ≤ V := hmax.2 ⟨hAK, fun k hk => hAn k hk,
      IsMulCommutative.of_comm
        (fun x y => Subtype.ext (hAab (x : Hbar M Q Z) x.2 (y : Hbar M Q Z) y.2))⟩ hVA
    exact le_antisymm hAV hVA

theorem isMaximalTwoLocal_MbarPrime_sp [(Q.subgroupOf M).Normal]
    (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hElt : ElementwiseNormalizerHyp M Q Z0)
    (hmaxAb : IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q)
    (hF2 : Step85F2Statement)
    (h85 : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))) :
    CFSG.Open.IsMaxTwoLocalSubgroup (MbarPrime M Q Z Z0) := by
  haveI hFinH : Finite (Hbar M Q Z) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let V : Subgroup (Hbar M Q Z) := (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))
  let M' : Subgroup (Hbar M Q Z) := MbarPrime M Q Z Z0
  have hconf : TIConfig (⊤ : Subgroup (Hbar M Q Z)) V (inSubgroup (pCore 2) M') :=
    tiConfig_MbarPrime_sp h51 hA hc hs hZ0 hElt hmaxAb hF2 h85
  have hK : NormIn (⊤ : Subgroup (Hbar M Q Z)) V = M' := by
    rw [NormIn, top_inf_eq]
    exact (MbarPrime_eq_normalizer_bar_Z0_sp hc hs hZ0).symm
  refine ⟨isTwoLocal_MbarPrime_sp h51 hA hc hs hZ0, ?_⟩
  intro K hK2 hM'K
  obtain ⟨D, hDne, hD2, hKD⟩ := hK2
  have hNormD : NormIn (⊤ : Subgroup (Hbar M Q Z)) D = K := by
    rw [NormIn, top_inf_eq]
    exact hKD.symm
  have hle : NormIn (⊤ : Subgroup (Hbar M Q Z)) V ≤
      NormIn (⊤ : Subgroup (Hbar M Q Z)) D := by
    rw [hK, hNormD]
    exact hM'K
  have hle' := TIConfig.maximal_local hconf le_top hDne hD2 hle
  rw [hNormD, hK] at hle'
  exact le_antisymm hle' hM'K

theorem isMaximalTwoLocal_MbarPrime_sp_maxLocal [(Q.subgroupOf M).Normal]
    (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hElt : ElementwiseNormalizerHyp M Q Z0)
    (hmaxAb : IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q)
    (hF2 : Step85F2Statement)
    (h85 : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))) :
    IsMaximalTwoLocal (MbarPrime M Q Z Z0) :=
  isMaximalTwoLocal_of_isMaxTwoLocalSubgroup
    (isMaximalTwoLocal_MbarPrime_sp h51 hA hc hs hZ0 hElt hmaxAb hF2 h85)

end CFSG.RankThree.GF2n.Stroth80
