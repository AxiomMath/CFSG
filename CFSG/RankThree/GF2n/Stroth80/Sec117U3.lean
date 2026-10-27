module

import CFSG.RankThree.GF2n.Stroth80.Sec117U3Field
import CFSG.RankThree.GF2n.Stroth80.Sec117U3Line
import CFSG.RankThree.GF2n.Stroth80.Sec117U3Module
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoTauSetup
public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCentralizer
public import CFSG.RankThree.GF2n.Stroth80.Sec11Module

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem Ctx.normal_isPGroup_two_Xbar_eq_bot [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) (S : Subgroup ↥(Xbar M Q Z B)) [S.Normal]
    (hS : IsPGroup 2 S) : S = ⊥ := by
  haveI : (Xbar M Q Z B).Normal := hc.Xbar_normal
  let P : Subgroup (Mbar M Q) := (CFSG.pCore 2 ↥(Xbar M Q Z B)).map (Xbar M Q Z B).subtype
  haveI : P.Normal := ConjAct.normal_of_characteristic_of_normal
  have hP : IsPGroup 2 P :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(Xbar M Q Z B))).map _
  have hP1 : P = ⊥ := hc.normal_isPGroup_two_Mbar_eq_bot P inferInstance hP
  have hcore : CFSG.pCore 2 ↥(Xbar M Q Z B) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Xbar M Q Z B).subtype_injective).mp hP1
  rw [eq_bot_iff, ← hcore]
  exact le_sSup ⟨inferInstance, hS⟩

theorem Ctx.not_Xbar_le_normalizer_bar_LB_of_isA2 [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) :
    ¬ Xbar M Q Z B ≤ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
  intro hX
  obtain ⟨a, haLB, hA2⟩ := ha2
  have hXa : (QuotientGroup.mk (⟨a, hc.LB_le_M haLB⟩ : ↥M) : Mbar M Q) ∈ Xbar M Q Z B :=
    Subgroup.subset_closure (hc.mk_mem_Ebar haLB hA2)
  have hLa : (QuotientGroup.mk (⟨a, hc.LB_le_M haLB⟩ : ↥M) : Mbar M Q) ∈
      bar M Q (LB M Q B) :=
    Subgroup.mem_map.mpr ⟨⟨a, hc.LB_le_M haLB⟩, Subgroup.mem_subgroupOf.mpr haLB, rfl⟩
  let S : Subgroup ↥(Xbar M Q Z B) := (bar M Q (LB M Q B)).subgroupOf (Xbar M Q Z B)
  haveI hSn : S.Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h := (Subgroup.mem_normalizer_iff.mp (hX g.2) (n : Mbar M Q)).mp hn
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h⟩
  have hS2 : IsPGroup 2 S := by
    intro s
    obtain ⟨k, hk⟩ := hc.isPGroup_bar_LB ⟨((s : ↥(Xbar M Q Z B)) : Mbar M Q), s.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hmem : (⟨_, hXa⟩ : ↥(Xbar M Q Z B)) ∈ S := by
    rw [Subgroup.mem_subgroupOf]
    exact hLa
  rw [hc.normal_isPGroup_two_Xbar_eq_bot S hS2, Subgroup.mem_bot] at hmem
  have h' : (QuotientGroup.mk (⟨a, hc.LB_le_M haLB⟩ : ↥M) : Mbar M Q) = 1 := by
    simpa using congrArg Subtype.val hmem
  exact hA2.2.1
    (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff ⟨a, hc.LB_le_M haLB⟩).mp h'))

theorem Ctx.false_of_Xbar_act_fix_line [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (y : G), y ∈ Q → M₀.π ((m : G) * y * (m : G)⁻¹) = φ m (M₀.π y))
    {b : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hfix : ∀ (g : G) (hg : g ∈ XbarPre M Q Z B), φ ⟨g, XbarPre_le_H0 hc hg⟩ b = b) :
    False := by
  refine hc.not_Xbar_le_normalizer_bar_LB_of_isA2 ha2 fun y hy => ?_
  obtain ⟨⟨g, hgM⟩, rfl⟩ := QuotientGroup.mk_surjective y
  have hg : g ∈ XbarPre M Q Z B := (mem_XbarPre_iff hc hgM).mpr hy
  exact hc.mk_mem_normalizer_bar_LB_of_fix_line hB hgM
    (T := (φ ⟨g, XbarPre_le_H0 hc hg⟩ : M₀.E →ₗ[K] M₀.E))
    (fun y hy => hφπ ⟨g, XbarPre_le_H0 hc hg⟩ y hy) (μ := 1)
    (by rw [one_smul]; exact hfix g hg)

theorem Ctx.not_lieModel_psu3_xbarMod [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {x : ℕ} :
    ¬ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 3 2 x := by
  intro h
  obtain ⟨hn3, hZ⟩ := width_eq_three_and_card_Z_of_psu3 hc hw hn ha2 h
  subst hn3
  obtain ⟨i, hi, hiQ, hiX⟩ := hc.exists_mem_LB_mk_mem_centralizer_Xbar_of_psu3 hw hn h hZ
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨b, -, -, hB, hcent, -⟩ := hc.dictB hD
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp hD
  have hbW := hc.mem_range_act_sub_one_of_mem_LB hD hφπ hφker hφiso hB hcent hi hiQ
  exact hc.false_of_Xbar_act_fix_line ha2 hφπ hB fun g hg =>
    hc.act_eq_self_of_mem_range_of_psu3 hw hZ h hD hφker hi hiX hg hbW

end CFSG.RankThree.GF2n.Stroth80
