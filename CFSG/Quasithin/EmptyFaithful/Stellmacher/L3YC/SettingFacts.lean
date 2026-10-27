module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.SBd3L3
public import CFSG.Quasithin.EmptyFaithful.SBd5Label
public import CFSG.Quasithin.EmptyFaithful.SBd7Gen
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.CyclicN0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.L3YC

section Facts

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem YC_le_N0 : YC153 Yp L ≤ N0 L := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hy, -⟩
  obtain ⟨-, hyL, -, hyc⟩ := hy
  refine ⟨hyL, fun l hl => ?_⟩
  have h1 := (pCoreOf 2 L).inv_mem (hyc l hl)
  have e : (l * y * l⁻¹ * y⁻¹)⁻¹ = y * l * y⁻¹ * l⁻¹ := by group
  rwa [e] at h1

omit [Finite G] in
theorem YC_gen : ∀ K : Subgroup G, (∀ y ∈ YC153 Yp L, Odd (orderOf y) → y ∈ K) →
    YC153 Yp L ≤ K := by
  intro K hK
  refine (Subgroup.closure_le K).mpr ?_
  rintro y ⟨hyX, hyodd⟩
  exact hK y (mem_oTwoUpper_of_odd hyX hyodd) hyodd

omit [Finite G] in
theorem YC_le_Yp : YC153 Yp L ≤ Yp :=
  (oTwoUpper_le _).trans (centralizerSection_le_left _ _ _)

theorem setting_facts (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (_ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L) :
    IsPGroup 2 ↥(Sgp153 T V₁) ∧ pCoreOf 2 L ≤ Sgp153 T V₁ ∧
      IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L ∧
      Sgp153 T V₁ ≤ Subgroup.normalizer (YC153 Yp L : Set G) ∧
      padicValNat 3 (Nat.card ↥(YC153 Yp L)) = 1 ∧
      ¬ 2 ∣ (Sgp153 T V₁).relIndex (YC153 Yp L ⊔ Sgp153 T V₁) := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  have hD := hh.decomp
  obtain ⟨hLc, -, -, -, -, -⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hyp.qtfe.sylow.1.to_le inf_le_left
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLle Subgroup.le_normalizer) inf_le_right
  refine ⟨hS2, ?_, hQsyl, ?_, c12.2.2.1, ?_⟩
  ·
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_subgroupOf.mp (pCore_two_le_subgroupOf hQsyl hy)).1
  ·
    have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
      Hyp153.T_le_normalizer_Sgp153 hyp hD
    have hlab := SBd5.l3YLLabel_of_l3 h113 h37 h38 SBd3.l3SolvableOverSylow_holds G T Mc M V₁ V₂ Yp
      I L t c hq c12 hV hYY
    have hSV₁ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₁ : Set G) := inf_le_right
    have hSV₂ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₂ : Set G) :=
      Hyp153.Sgp153_le_normalizer_V₂ hyp hD
    have hSYL : Sgp153 T V₁ ≤ Subgroup.normalizer (YL153 Yp L : Set G) := by
      rcases hlab with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]; exact szN3_S_le_normalizer_oTwoUpper hyp inf_le_left hSV₁
      · rw [h1]; exact szN3_S_le_normalizer_oTwoUpper hyp inf_le_left hSV₂
    intro s hs
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hy' : y ∈ YC153 Yp L := hy
    suffices hkey : s * y * s⁻¹ ∈ YC153 Yp L from hkey
    rw [← hswap, B6.mem_conjSub]
    rw [← hswap, B6.mem_conjSub] at hy'
    have hs' : t'⁻¹ * s * t' ∈ Sgp153 T V₁ := (Subgroup.mem_normalizer_iff''.mp (hTS ht'T) s).mp hs
    have h1 : (t'⁻¹ * s * t') * (t'⁻¹ * y * t') * (t'⁻¹ * s * t')⁻¹ ∈ YL153 Yp L :=
      (Subgroup.mem_normalizer_iff.mp (hSYL hs') _).mp hy'
    have e : t'⁻¹ * (s * y * s⁻¹) * t' =
        (t'⁻¹ * s * t') * (t'⁻¹ * y * t') * (t'⁻¹ * s * t')⁻¹ := by group
    rw [e]; exact h1
  ·
    have hYI : Yp ⊔ Sgp153 T V₁ ≤ I := c.ctx.inH.1.1
    have hYSI : YC153 Yp L ⊔ Sgp153 T V₁ ≤ I :=
      sup_le (YC_le_Yp.trans (le_sup_left.trans hYI)) (le_sup_right.trans hYI)
    have hmul := Subgroup.relIndex_mul_relIndex (Sgp153 T V₁) (YC153 Yp L ⊔ Sgp153 T V₁) I
      le_sup_right hYSI
    intro h2
    apply hSyl.2.2
    show 2 ∣ (Sgp153 T V₁).relIndex I
    rw [← hmul]
    exact h2.mul_right _

end Facts

end Stellmacher.L3YC

end CFSG.Quasithin
