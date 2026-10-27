module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Om6
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mBar_le_normalizer_lBar (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) :
    Mbar D.M V₀ V hV ≤
      normalizer ((lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) :
        Set (MulAut (Vtil V₀ V hV))) := by
  intro φ hφ
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hφnot : φ ∉ normalizer
      ((lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) :
        Set (MulAut (Vtil V₀ V hV))) :=
    fun h => hne (Subgroup.mem_normalizer_iff_map_conj_eq.mp h)
  obtain ⟨g, hgM, hφeq⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
  have hgNot : (g : G) ∉ nBar D.M V₀ V hV L := by
    intro hgN
    obtain ⟨-, h, hhn⟩ :=
      (s15_Three_mem_nBar (D := D) (V₀ := V₀) (V := V) (L := L) hV).1 hgN
    have heq : actTil V₀ V hV ⟨(g : G), h⟩ = φ := by
      rw [show (⟨(g : G), h⟩ : stabTil V₀ V) = g from Subtype.ext rfl, hφeq]
    exact hφnot (heq ▸ hhn)
  have hcomm : ⁅barSub V₀ V hV L, barSub V₀ V hV (conjSubgroup L (g : G))⁆ = ⊥ :=
    (hS.setting.hyp151.commute (g : G) hgM hgNot).1
  have hbot : barSub V₀ V hV (conjSubgroup L (g : G)) = ⊥ := by
    rw [← le_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    exact natOmegaMinus_centralizer_eq_one hc.2.1 fun x hx =>
      (s15_Three_mul_comm_of_commutator_eq_bot hcomm x hx y hy).symm
  have hmapbot : (barSub V₀ V hV L).map
      (MulAut.conj (actTil V₀ V hV ⟨(g : G), g.2⟩)⁻¹).toMonoidHom = ⊥ := by
    rw [← s15_Infra_barSub_conjSubgroup V₀ V hV g.2 L]
    exact hbot
  have hLbot : barSub V₀ V hV L = ⊥ := by
    rw [← le_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : (MulAut.conj (actTil V₀ V hV ⟨(g : G), g.2⟩)⁻¹) z ∈
        (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) := by
      rw [← hmapbot]
      exact ⟨z, hz, rfl⟩
    rw [Subgroup.mem_bot] at hz'
    exact (MulAut.conj (actTil V₀ V hV ⟨(g : G), g.2⟩)⁻¹).injective
      (by rw [hz', map_one])
  exact hS.ne_bot hLbot

private theorem s16c1_inf_centralizer_le (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) :
    V ⊓ centralizer (L : Set G) ≤ V₀ := by
  intro x hx
  obtain ⟨hxV, hxc⟩ := Subgroup.mem_inf.1 hx
  have hfix : ∀ φ ∈ barSub V₀ V hV L,
      φ (mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩)) = mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩) := by
    intro φ hφ
    obtain ⟨g, hgL, rfl⟩ := (mem_barSub V₀ V hV L φ).1 hφ
    have hstab : actStab V₀ V hV g (IntMod.mk hV ⟨x, hxV⟩) = IntMod.mk hV ⟨x, hxV⟩ := by
      apply IntMod.val_injective
      rw [actStab_apply_val]
      have hcomm := Subgroup.mem_centralizer_iff.1 hxc (g : G) hgL
      show (g : G) * x * (g : G)⁻¹ = x
      rw [hcomm]
      group
    rw [actTil_mk, hstab]
  have hq1 : mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩) = 1 :=
    natOmegaMinus_fixed_eq_one hc.2.1 hfix
  rw [← map_one (mkTil V₀ V hV), mkTil_eq_iff] at hq1
  rw [IntMod.val_one, inv_one, mul_one] at hq1
  exact hq1

private theorem s16c1_lBar_commutator_eq_self (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) :
    ⁅barSub V₀ V hV L, barSub V₀ V hV L⁆ = barSub V₀ V hV L := by
  haveI : Group.IsPerfect ↥(barSub V₀ V hV L) := by
    obtain ⟨-, K, hKfield, hKfinite, b, c, hcard, hirr, ⟨e⟩⟩ := hc.1
    letI : Field K := hKfield
    letI : Finite K := hKfinite
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Fintype K := Fintype.ofFinite K
    have hcard2 : Fintype.card K = 2 := by
      rw [Fintype.card_eq_nat_card, hcard]
      norm_num
    haveI : CharP K 2 := charP_of_card_eq_prime (p := 2) hcard2
    have hfacts :=
      CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
        (n := 6 / 2) (b := b) (c := c) (Or.inr (by norm_num)) hirr
    haveI : Group.IsPerfect (StatedOmega (StatedQuadMinus (6 / 2) K b c)) :=
      Group.isPerfect_def.2 hfacts.2.1
    haveI : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadMinus (6 / 2) K b c))) :=
      inferInstance
    refine Group.isPerfect_def.2 ?_
    exact CFSG.ComponentClassification.RankTwoClassical.commutator_eq_top_of_mulEquiv e
      Group.IsPerfect.commutator_eq_top
  exact Subgroup.commutator_eq_self

private theorem s16c1_conjSet_lBar (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) :
    conjSet (barSub V₀ V hV L) (s15NBar D V₀ V hV L) = {barSub V₀ V hV L} := by
  have hN : s15NBar D V₀ V hV L = Mbar D.M V₀ V hV := by
    rw [s15NBar, inf_eq_left]
    exact mBar_le_normalizer_lBar D hS hc
  rw [hN]
  ext X
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (mBar_le_normalizer_lBar D hS hc hn)
  · intro hX
    rw [Set.mem_singleton_iff] at hX
    rw [hX]
    exact ⟨1, (Mbar D.M V₀ V hV).one_mem,
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.one_mem (normalizer (barSub V₀ V hV L :
          Set (MulAut (Vtil V₀ V hV)))))).symm⟩

private theorem s16c1_isDirectProdOfConj (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) :
    IsDirectProdOfConj (barSub V₀ V hV L) (barSub V₀ V hV L) (s15NBar D V₀ V hV L) := by
  unfold IsDirectProdOfConj
  rw [s16c1_conjSet_lBar D hS hc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Y hY
    rw [Set.mem_singleton_iff] at hY
    rw [hY]
  · exact iSup_singleton
  · intro Y hY Z hZ hne
    rw [Set.mem_singleton_iff] at hY hZ
    exact absurd (hY.trans hZ.symm) hne
  · intro Y hY
    rw [Set.mem_singleton_iff] at hY
    rw [hY]
    simp

private theorem s16c1_commSub_barSub_conj_eq_top (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L)
    {m : G} (hm : m ∈ D.M) :
    commSub (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV (conjSubgroup L m)) = ⊤ := by
  have hms : D.M ≤ stabTil V₀ V :=
    le_stabTil hS.setting.hyp16.hyp125.pairFacts.le_normalizer
      hS.setting.hyp16.hyp125.pairFacts.le_normalizer₀
  have hmstab : m ∈ stabTil V₀ V := hms hm
  have hμ : actTil V₀ V hV ⟨m, hmstab⟩ ∈ Mbar D.M V₀ V hV :=
    actTil_mem_barSub V₀ V hV hm hmstab
  have hN : actTil V₀ V hV ⟨m, hmstab⟩ ∈
      normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    mBar_le_normalizer_lBar D hS hc hμ
  have hNinv : (actTil V₀ V hV ⟨m, hmstab⟩)⁻¹ ∈
      normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    (normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))).inv_mem hN
  have hmap : (barSub V₀ V hV L).map
      (MulAut.conj (actTil V₀ V hV ⟨m, hmstab⟩)⁻¹).toMonoidHom = barSub V₀ V hV L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hNinv
  rw [s15_Infra_barSub_conjSubgroup V₀ V hV hmstab L, hmap]
  exact natOmegaMinus_commSub_eq_top hc.2.1

theorem v1Sub_eq_of_case167_1 (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) :
    v1Sub D.M V₀ V hV L = V₀ := by
  by_cases h : V₀ = ⊥
  · have hkey := s16c1_inf_centralizer_le D hS hc
    rw [h] at hkey
    have hbot : wSub V₀ V hV L ⊓ centralizer (L : Set G) = ⊥ := by
      rw [← le_bot_iff]
      exact le_trans (inf_le_inf (preTil_le V₀ V hV (wTil V₀ V hV L)) le_rfl) hkey
    rw [v1Sub_of_eq_bot D.M V₀ V hV L h, hbot]
    simp [conjSubgroup, h]
  · exact v1Sub_of_ne_bot D.M V₀ V hV L h

theorem s15KNatPerf_of_case167_1 (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) :
    s15KNatPerf ↥(barSub V₀ V hV L) (barSub (v1Sub D.M V₀ V hV L) V hV L)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV L)) := by
  rw [v1Sub_eq_of_case167_1 D hS hc]
  have hcomm : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV L) = ⊤ :=
    natOmegaMinus_commSub_eq_top hc.2.1
  rw [hcomm]
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨6, le_rfl, hc.1, hc.2.1⟩)))

private theorem s16c1_family_eq_singleton (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) :
    {Z : Subgroup (Vtil V₀ V hV) | ∃ m ∈ D.M,
        Z = commSub ⊤ (barSub V₀ V hV (conjSubgroup L m))} =
      {⊤} := by
  ext Z
  rw [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact s16c1_commSub_barSub_conj_eq_top D hS hc hm
  · intro hZ
    rw [hZ]
    exact ⟨1, D.M.one_mem,
      (s16c1_commSub_barSub_conj_eq_top D hS hc D.M.one_mem).symm⟩

theorem s15Shape_of_case167_1 (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) :
    s15Shape D V₀ V hV L L := by
  let P : Subgroup G → Prop := fun u =>
    L ≤ L ∧ barSub V₀ V hV L ≤ ⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆ ∧
      IsDirectProdOfConj (lBar V₀ V hV L) (barSub V₀ V hV L) (s15NBar D V₀ V hV L) ∧
      s15KNat ↥(barSub V₀ V hV L) (barSub u V hV L) (commSub ⊤ (barSub u V hV L)) ∧
      sSupIndep {Z : Subgroup (Vtil u V hV) | ∃ m ∈ D.M,
        Z = commSub ⊤ (barSub u V hV (conjSubgroup L m))} ∧
      sSup {Z : Subgroup (Vtil u V hV) | ∃ m ∈ D.M,
        Z = commSub ⊤ (barSub u V hV (conjSubgroup L m))} = ⊤
  have hV0 : P V₀ := by
    refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩
    · calc barSub V₀ V hV L = ⁅barSub V₀ V hV L, barSub V₀ V hV L⁆ :=
          (s16c1_lBar_commutator_eq_self D hS hc).symm
        _ ≤ ⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆ :=
          Subgroup.commutator_mono (barSub_mono V₀ V hV hS.setting.hyp151.le)
            (barSub_mono V₀ V hV hS.setting.hyp151.le)
    · exact s16c1_isDirectProdOfConj D hS hc
    · have h3 := s15KNatPerf_of_case167_1 D hS hc
      rw [v1Sub_eq_of_case167_1 D hS hc] at h3
      exact Or.inl h3
    · rw [s16c1_family_eq_singleton D hS hc]
      exact sSupIndep_singleton ⊤
    · rw [s16c1_family_eq_singleton D hS hc]
      exact sSup_singleton
  have hgoal : P (v1Sub D.M V₀ V hV L) :=
    (congrArg P (v1Sub_eq_of_case167_1 D hS hc)).symm ▸ hV0
  unfold s15Shape
  exact hgoal

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
