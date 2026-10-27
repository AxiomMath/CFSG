module

public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.EmptyFaithful.T1515Concl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

section Components

variable {X : Type*} [Group X]

theorem open_isSubnormal_top_of_mathlib1516 {H : Subgroup X} (h : H.IsSubnormal) :
    CFSG.Open.IsSubnormal H ⊤ :=
  CFSG.Open.IsSubnormal.of_mathlib h

theorem mem_cComp_top_of_isComponent1516 {C : Subgroup X} (hC : CFSG.IsComponent C) :
    C ∈ cComp (⊤ : Subgroup X) := by
  have hq : CFSG.IsQuasisimple ↥C := hC.1
  have hperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.mp hq.1
  refine ⟨?_, hperf, open_isSubnormal_top_of_mathlib1516 hC.2, ?_⟩
  · intro hb
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot C).mp this hb
  · intro K' hlt hne hperf' hsub
    have hsubK : CFSG.Open.IsSubnormal K' C :=
      Quasithin.A3.subnormal_of_le_of_le hsub hlt.le le_top
    obtain ⟨P, hPK, hPn, hK'P⟩ := Quasithin.A3.subnormal_exists_normal_of_lt hsubK hlt
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hPn with h1 | h1
    · exact absurd (Subgroup.subgroupOf_eq_top.mp h1) (not_le_of_gt hPK)
    · apply hne
      rw [← hperf', Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
      intro x hx
      have hxP : x ∈ P := hK'P hx
      have hxc := Subgroup.mem_center_iff.mp
        (h1 (show (⟨x, hPK.le hxP⟩ : ↥C) ∈ P.subgroupOf C from hxP))
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact congrArg Subtype.val (hxc ⟨y, hlt.le hy⟩)

end Components

section FStar

variable {G : Type} [Group G] [Finite G]

theorem oTwoFstarIn_le_of_components1516 {H K : Subgroup G} (hP : pCoreOf 2 H ≤ K)
    (hF : oTwoFIn H ≤ K)
    (hC : ∀ L : Subgroup G, L ∈ cComp H → CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → L ≤ K) :
    oTwoFstarIn H ≤ K := by
  have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  set K' : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
    (K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) with hK'
  have hFK : CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) ≤ K' := by
    intro f hf
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) f
    have hy : (y : G) ∈ oTwoFIn H := ⟨y, hf, rfl⟩
    exact ⟨y, hF hy, rfl⟩
  have hEK : CFSG.layer (↥H ⧸ CFSG.pCore 2 ↥H) ≤ K' := by
    refine sSup_le fun C hC' => ?_
    have hCc : C ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      mem_cComp_top_of_isComponent1516 hC'
    obtain ⟨L, hL, hLC⟩ := exists_cComp_modO2Image_eq hCc
    obtain ⟨e⟩ := modO2_mulEquiv hL
    have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (e.trans (MulEquiv.subgroupCongr hLC)).symm hC'.1
    have hLK : L ≤ K := hC L hL hq
    rw [← hLC]
    exact Subgroup.map_mono fun a ha => hLK ha
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyK : QuotientGroup.mk' (CFSG.pCore 2 ↥H) y ∈ K' := sup_le hFK hEK hy
  obtain ⟨z, hz, hzy⟩ := hyK
  have hzn : z⁻¹ * y ∈ CFSG.pCore 2 ↥H := by
    have := (QuotientGroup.eq (a := z) (b := y)).mp (by simpa using hzy)
    exact this
  have hnG : ((z⁻¹ * y : ↥H) : G) ∈ pCoreOf 2 H := by
    unfold CFSG.Open.pCoreOf
    exact ⟨z⁻¹ * y, hzn, rfl⟩
  have hzK : (z : G) ∈ K := hz
  have hyz : ((y : ↥H) : G) = (z : G) * ((z⁻¹ * y : ↥H) : G) := by simp
  rw [Subgroup.coe_subtype, hyz]
  exact K.mul_mem hzK (hP hnG)

end FStar

section Six

variable {G : Type} [Group G] [Finite G]

theorem lemma_15_1_19_six_of_three_four {T Mc M Z₁ : Subgroup G}
    (hq : quasithinQTFE14Cat G T Mc) (h18 : Lemma15118Concl T Mc M Z₁)
    (h3 : oTwoFIn (g1_1516 Z₁) ≤ mZ1516 Mc Z₁)
    (h4 : ∀ H : Subgroup G, mZ1516 Mc Z₁ ≤ H → H ≤ g1_1516 Z₁ → oTwoFstarIn H ≤ mZ1516 Mc Z₁ →
      H = mZ1516 Mc Z₁) :
    ∃ L : Subgroup G, L ∈ cComp (g1_1516 Z₁) ∧
      CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧ ¬ L ≤ mZ1516 Mc Z₁ := by
  by_contra hno
  push Not at hno
  have hSM : s1516 T Z₁ ≤ mZ1516 Mc Z₁ :=
    le_inf (s1516_le_g1 T Z₁) ((s1516_le T Z₁).trans hq.t_le_mc)
  have hP : pCoreOf 2 (g1_1516 Z₁) ≤ mZ1516 Mc Z₁ := (CFSG.QuasithinUnique.IsSylowTwoOf.pCoreOf_le h18.four).trans hSM
  have hEq := h4 (g1_1516 Z₁) (mZ1516_le_g1 Mc Z₁) le_rfl
    (oTwoFstarIn_le_of_components1516 hP h3 fun L hL hqL => hno L hL hqL)
  exact h18.two (inf_le_right.trans hEq.le)

end Six

end CFSG.Quasithin
