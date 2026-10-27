module

public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Main
public import CFSG.RankThree.GF2n.Tim81.Sec7.Defs
public import CFSG.RankThree.GF2n.Tim81.FStarSimple
import CFSG.RankThree.GF2n.Tim81.Sec6.RootImages

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim81
open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G} {f m : ℕ}

theorem centralizer_le_M (h : Hyp M V) : cenOf V ≤ M :=
  h.normalizer_eq ▸ Subgroup.centralizer_le_normalizer (V : Set G)

theorem Pc_eq_pCore_cenOf (h : Hyp M V) :
    Pc M V = inSubgroup (pCore 2) (cenOf V) := by
  apply le_antisymm
  ·
    have hPc2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
    refine CFSG.RankThree.GroupTheory.SteinbergBY.le_inSubgroup_pCore hPc2 inf_le_right ?_
    intro c hc
    exact h.le_normalizer_Pc (centralizer_le_M h hc)
  ·
    have hCM : cenOf V ≤ M := centralizer_le_M h
    have hMnormC : M ≤ Subgroup.normalizer (cenOf V : Set G) := fun m hm =>
      mem_normalizer_centralizer (h.le_normalizer hm)
    have hO2C_le_Q : inSubgroup (pCore 2) (cenOf V) ≤ inSubgroup (pCore 2) M :=
      CFSG.RankThree.GroupTheory.SteinbergBY.le_inSubgroup_pCore
        (CFSG.RankThree.GroupTheory.SteinbergBY.isPGroup_inSubgroup_pCore 2 (cenOf V))
        ((CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 (cenOf V)).trans hCM)
        (hMnormC.trans
          (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore
            2 (cenOf V)))
    exact le_inf hO2C_le_Q
      (CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 (cenOf V))

theorem Pc_inf_eq_pCore_of_normal (h : Hyp M V) {X : Subgroup G} (hXn : X.Normal) :
    Pc M V ⊓ X = inSubgroup (pCore 2) (X ⊓ cenOf V) := by
  apply le_antisymm
  ·
    have h2 : IsPGroup 2 ↥(Pc M V ⊓ X) :=
      IsPGroup.to_le (p := 2) (inSubgroup_pCore_two M).1
        (inf_le_left.trans (inf_le_left : Pc M V ≤ inSubgroup (pCore 2) M))
    have hle : Pc M V ⊓ X ≤ X ⊓ cenOf V :=
      le_inf inf_le_right (inf_le_left.trans inf_le_right)
    have hnorm : X ⊓ cenOf V ≤
        Subgroup.normalizer ((Pc M V ⊓ X : Subgroup G) : Set G) := by
      intro y hy
      obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.mp hy
      exact mem_normalizer_inf
        (h.le_normalizer_Pc (centralizer_le_M h hyC))
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hXn]; exact Subgroup.mem_top y)
    exact CFSG.RankThree.GroupTheory.SteinbergBY.le_inSubgroup_pCore h2 hle hnorm
  ·
    have hR2 : IsPGroup 2 ↥(inSubgroup (pCore 2) (X ⊓ cenOf V)) :=
      CFSG.RankThree.GroupTheory.SteinbergBY.isPGroup_inSubgroup_pCore 2 (X ⊓ cenOf V)
    have hR_le_C : inSubgroup (pCore 2) (X ⊓ cenOf V) ≤ cenOf V :=
      (CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 (X ⊓ cenOf V)).trans
        inf_le_right
    have hR_le_X : inSubgroup (pCore 2) (X ⊓ cenOf V) ≤ X :=
      (CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 (X ⊓ cenOf V)).trans
        inf_le_left
    have hC_le_Ninf : cenOf V ≤
        Subgroup.normalizer ((X ⊓ cenOf V : Subgroup G) : Set G) := by
      intro c hc
      exact mem_normalizer_inf
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hXn]; exact Subgroup.mem_top c)
        (Subgroup.le_normalizer hc)
    have hR_le_O2C : inSubgroup (pCore 2) (X ⊓ cenOf V) ≤
        inSubgroup (pCore 2) (cenOf V) :=
      CFSG.RankThree.GroupTheory.SteinbergBY.le_inSubgroup_pCore hR2 hR_le_C
        (hC_le_Ninf.trans
          (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore
            2 (X ⊓ cenOf V)))
    rw [Pc_eq_pCore_cenOf h]
    exact le_inf hR_le_O2C hR_le_X

theorem isQuasisimple_range (hf : 1 ≤ f)
    (Φ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m →* G)
    (hm : 4 ≤ m) (hker : Φ.ker = Subgroup.center _) :
    CFSG.IsQuasisimple ↥Φ.range := by
  let S := Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), mul_comm 2 f, pow_mul]
  have hquasi : IsQuasisimple S :=
    isQuasisimple_SU (p := 2) (f := f) (F := GaloisField 2 (2 * f)) (n := m) hF
      (by omega) (by
        intro h
        exact absurd (congrArg Prod.fst h) (by omega))
  have hker' : Φ.rangeRestrict.ker = Subgroup.center S := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  let e : ↥Φ.range ≃* S ⧸ Subgroup.center S :=
    (QuotientGroup.quotientKerEquivOfSurjective Φ.rangeRestrict
        Φ.rangeRestrict_surjective).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker')
  haveI : IsSimpleGroup (S ⧸ Subgroup.center S) := hquasi.2.1
  have hQ : IsQuasisimple (S ⧸ Subgroup.center S) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hquasi.2.2).1
  exact hQ.of_mulEquiv e

theorem eq_generalizedFitting (h : Hyp M V) (hcard : Nat.card V = 2 ^ f) (hf : 2 ≤ f)
    (Φ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m →* G)
    (hrange : Φ.range = Subgroup.normalClosure (V : Set G))
    (hker : Φ.ker = Subgroup.center _) (hm : 4 ≤ m) :
    Subgroup.normalClosure (V : Set G) = generalizedFitting G := by
  let X : Subgroup G := Subgroup.normalClosure (V : Set G)
  have hXn : X.Normal := Subgroup.normalClosure_normal
  have hrange' : Φ.range = X := hrange
  have hQuasi : CFSG.IsQuasisimple ↥X := by
    rw [← hrange']
    exact isQuasisimple_range (by omega) Φ hm hker
  have hComp : CFSG.IsComponent X := ⟨hQuasi, hXn.isSubnormal⟩
  have hXleF : X ≤ generalizedFitting G :=
    (CFSG.LocalCores.component_le_layer hComp).trans (by
      rw [generalizedFitting.eq_sup]
      exact le_sup_right)
  have h4 : 4 ≤ Nat.card V := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hSimpleF := h.isSimpleGroup_generalizedFitting h4
  haveI : IsSimpleGroup ↥(generalizedFitting G) := hSimpleF.1
  have hVleX : V ≤ X := fun v hv => Subgroup.subset_normalClosure hv
  have hXne : X ≠ ⊥ := by
    intro hbot
    exact h.ne_bot (le_bot_iff.mp (hVleX.trans (le_of_eq hbot)))
  have hXnormal_in : (X.subgroupOf (generalizedFitting G)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hXleF,
      Subgroup.normalizer_eq_top_iff.mpr hXn]
    exact le_top
  have hXtop : X.subgroupOf (generalizedFitting G) = ⊤ := by
    haveI : (X.subgroupOf (generalizedFitting G)).Normal := hXnormal_in
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (X.subgroupOf (generalizedFitting G)) with htop | htop
    · exfalso
      have hXbot : X = ⊥ := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hXleF, htop, Subgroup.map_bot]
      exact hXne hXbot
    · exact htop
  exact le_antisymm hXleF (Subgroup.subgroupOf_eq_top.mp hXtop)

theorem unitaryConclusionPin_holds : UnitaryConclusionPin := by
  intro G _ _ M V f hf m hm Φ hHyp hcard hrange hker hconj
  let X : Subgroup G := Subgroup.normalClosure (V : Set G)
  let Δ : Set (Subgroup G) := {U | ∃ g : G, U = conjSubgroup g V}
  have hXn : X.Normal := Subgroup.normalClosure_normal
  have hrange' : Φ.range = X := hrange
  have hSU : IsSUImage X Δ f m (by omega) (by omega) := by
    refine ⟨Φ, ?_, hrange', ?_⟩
    · rw [hker]
    · intro U
      change (∃ g : G, U = conjSubgroup g V) ↔
        ∃ x, U = (conjSub ((Unitary.rootDatum (card_galoisField_two_mul (by omega : 1 ≤ f))
          m).rootGroup (unitaryLongRoot m (by omega))) x).map Φ
      exact hconj U
  have hVmem : V ∈ Δ := ⟨1, (conjSubgroup_one V).symm⟩
  have hcardR : Nat.card ↥(inSubgroup (pCore 2) (X ⊓ cenOf V)) = (2 ^ f) ^ (2 * m - 3) :=
    hSU.natCard_pCore_cenOf hm hVmem
  have hPc2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hPc_le_C : Pc M V ≤ cenOf V := inf_le_right
  have hNL : X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (Pc M V : Set G) :=
    fun y hy => hHyp.le_normalizer_Pc (hHyp.normalizer_eq ▸ (Subgroup.mem_inf.mp hy).2)
  have hPc_le_sup : Pc M V ≤ inSubgroup (pCore 2) (X ⊓ cenOf V) ⊔ cenOf X :=
    haveI := hXn
    hSU.le_pCore_sup_cenOf hm hVmem hPc2 hPc_le_C hNL
  have hXF : X = generalizedFitting G :=
    eq_generalizedFitting hHyp hcard hf Φ hrange hker hm
  have hCX_le_X : cenOf X ≤ X := by
    rw [hXF]
    exact centralizer_generalizedFitting_le G
  have hRX_le_X : inSubgroup (pCore 2) (X ⊓ cenOf V) ≤ X :=
    (CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 (X ⊓ cenOf V)).trans
      inf_le_left
  have hPc_le_X : Pc M V ≤ X :=
    hPc_le_sup.trans (sup_le hRX_le_X hCX_le_X)
  have hRX_le_Pc : inSubgroup (pCore 2) (X ⊓ cenOf V) ≤ Pc M V := by
    have hR2 : IsPGroup 2 ↥(inSubgroup (pCore 2) (X ⊓ cenOf V)) :=
      CFSG.RankThree.GroupTheory.SteinbergBY.isPGroup_inSubgroup_pCore 2 (X ⊓ cenOf V)
    have hR_le_C : inSubgroup (pCore 2) (X ⊓ cenOf V) ≤ cenOf V :=
      (CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 (X ⊓ cenOf V)).trans
        inf_le_right
    have hC_le_Ninf : cenOf V ≤
        Subgroup.normalizer ((X ⊓ cenOf V : Subgroup G) : Set G) := by
      intro c hc
      exact mem_normalizer_inf
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hXn]; exact Subgroup.mem_top c)
        (Subgroup.le_normalizer hc)
    have hR_le_O2C : inSubgroup (pCore 2) (X ⊓ cenOf V) ≤
        inSubgroup (pCore 2) (cenOf V) :=
      CFSG.RankThree.GroupTheory.SteinbergBY.le_inSubgroup_pCore hR2 hR_le_C
        (hC_le_Ninf.trans
          (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore
            2 (X ⊓ cenOf V)))
    rw [Pc_eq_pCore_cenOf hHyp]
    exact hR_le_O2C
  have hPc_le_RX : Pc M V ≤ inSubgroup (pCore 2) (X ⊓ cenOf V) := by
    have hle : Pc M V ≤ Pc M V ⊓ X := le_inf le_rfl hPc_le_X
    rwa [Pc_inf_eq_pCore_of_normal hHyp hXn] at hle
  have hPcEq : Pc M V = inSubgroup (pCore 2) (X ⊓ cenOf V) :=
    le_antisymm hPc_le_RX hRX_le_Pc
  calc Nat.card ↥(Pc M V) = Nat.card ↥(inSubgroup (pCore 2) (X ⊓ cenOf V)) := by rw [hPcEq]
    _ = (2 ^ f) ^ (2 * m - 3) := hcardR
    _ = Nat.card V ^ (2 * m - 3) := by rw [hcard]

end CFSG.RankThree.GF2n.Stroth80
