module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10
public import CFSG.Holt.TwoGroupsFocal
public import CFSG.RankThree.PartOne.CTP.StrongPFusion
public import CFSG.RankThree.Transfer.Yoshida
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CharacterTheory.Wreathed.QuaternionOvergroupsSupport
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Holt.Basic
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def R6_38 (D : Data G) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → (p ∈ D.sig ∨ IsStronglyPEmbedded p D.M) →
    UC22.F10.OpRes p D.M = D.M

@[expose] def R6_38Sigma (D : Data G) : Prop :=
  ∀ p ∈ D.sig, UC22.F10.OpRes p D.M = D.M

section Residual

theorem opRes_eq_map_oResidual_uc6 {p : ℕ} (hp : p.Prime) (X : Subgroup G) :
    UC22.F10.OpRes p X = (CFSG.GH74.GLS.oResidual p ↥X).map X.subtype := by
  rw [CFSG.GH74.GLS.oResidual, MonoidHom.map_closure, UC22.F10.OpRes]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, hcop⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    show Nat.Coprime (orderOf (⟨x, hx⟩ : ↥X)) p
    rw [Subgroup.orderOf_mk]
    exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hcop)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have hy' : Nat.Coprime (orderOf y) p := hy
    show ¬ p ∣ orderOf (y : G)
    rw [Subgroup.orderOf_coe]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp hy')

theorem eq_top_of_isPGroup_quotient_of_opRes_eq_uc6 {p : ℕ} (hp : p.Prime) {M : Subgroup G}
    (h : UC22.F10.OpRes p M = M) (N : Subgroup ↥M) [N.Normal] (hN : IsPGroup p (↥M ⧸ N)) :
    N = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htop : CFSG.GH74.GLS.oResidual p ↥M = ⊤ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [← opRes_eq_map_oResidual_uc6 hp, h, Subgroup.map_top, Subgroup.range_subtype]
  have := CFSG.RankThree.Transfer.oResidual_le_ker_of_isPGroup (QuotientGroup.mk' N) hN
  rw [htop, QuotientGroup.ker_mk'] at this
  exact top_le_iff.mp this

theorem oResidual_eq_top_of_sylow_le_commutator_uc6 {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (P : Sylow p X) (hP : (P : Subgroup X) ≤ commutator X) :
    CFSG.GH74.GLS.oResidual p X = ⊤ := by
  set L := CFSG.GH74.GLS.oResidual p X with hL
  haveI : L.Normal := CFSG.RankThree.Transfer.oResidual_normal p X
  have hQ : IsPGroup p (X ⧸ L) :=
    CFSG.RankThree.Transfer.isPGroup_quotient_of_oResidual_le L le_rfl
  have hmap := CFSG.RankThree.Transfer.map_mk_eq_top_of_isPGroup P L hQ
  have hcomm : commutator (X ⧸ L) = ⊤ := by
    apply top_unique
    rw [← hmap]
    calc (P : Subgroup X).map (QuotientGroup.mk' L)
        ≤ (commutator X).map (QuotientGroup.mk' L) := Subgroup.map_mono hP
      _ = commutator (X ⧸ L) := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective L)]
  by_contra hne
  have hidx : L.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  haveI : Nontrivial (X ⧸ L) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.card_pos.ne', hidx⟩)
  haveI : Group.IsNilpotent (X ⧸ L) := hQ.isNilpotent
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (X ⧸ L)).ne hcomm

end Residual

section Strong

theorem sylow_le_commutator_map_of_stronglyEmbedded_uc6 (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : IsStronglyPEmbedded p M) :
    ∃ S : Sylow p G, (S : Subgroup G) ≤ M ∧ (S : Subgroup G) ≤ (commutator ↥M).map M.subtype := by
  obtain ⟨P₀, hP₀, hP₀M⟩ := hM.exists_isSylowOf_le
  let S : Sylow p G := hP₀.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hP₀.2.2)
  have hS : (S : Subgroup G) = P₀ := rfl
  have hSM : (S : Subgroup G) ≤ M := hS ▸ hP₀M
  set U : Subgroup G := (S : Subgroup G) ⊓ (commutator ↥M).map M.subtype with hU
  have hfoc : ∀ x ∈ (S : Subgroup G), ∀ g : G, g * x * g⁻¹ ∈ (S : Subgroup G) →
      x⁻¹ * (g * x * g⁻¹) ∈ U := by
    intro x hx g hgx
    by_cases hx1 : x = 1
    · subst hx1
      simp
    · have hgM : g ∈ M := hM.mem_of_fusion S.isPGroup' hSM hx hx1 hgx
      refine ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hx) hgx, ?_⟩
      refine ⟨⁅(⟨x⁻¹, M.inv_mem (hSM hx)⟩ : ↥M), (⟨g, hgM⟩ : ↥M)⁆, ?_, ?_⟩
      · rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      · simp [commutatorElement_def, mul_assoc]
  obtain ⟨N, hN, hNp, hNi, -⟩ := CFSG.Holt.exists_normal_inf_eq_of_focal S inf_le_left hfoc
  haveI := hN
  rcases hG.eq_bot_or_eq_top_of_normal N with hN0 | hN1
  · exfalso
    have hinj : Function.Injective (QuotientGroup.mk' N) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN0]
    have hGp : IsPGroup p G := hNp.of_injective _ hinj
    haveI : Nontrivial G := by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨⟨a, b, fun h => hab (h ▸ rfl)⟩⟩
    have hcn : Nontrivial (Subgroup.center G) := hGp.center_nontrivial
    rcases hG.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
    · exact (Subgroup.nontrivial_iff_ne_bot _).mp hcn hc
    · obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have : a ∈ Subgroup.center G := hc ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp this b).symm
  · have h1 : U.relIndex (S : Subgroup G) = 1 := by
      rw [← hNi, hN1]
      exact Subgroup.index_top
    have hSU : (S : Subgroup G) ≤ U := Subgroup.relIndex_eq_one.mp h1
    exact ⟨S, hSM, hSU.trans inf_le_right⟩

theorem opRes_eq_of_stronglyEmbedded_uc6 (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {p : ℕ} (hp : p.Prime) {M : Subgroup G}
    (hM : IsStronglyPEmbedded p M) : UC22.F10.OpRes p M = M := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSM, hSc⟩ := sylow_le_commutator_map_of_stronglyEmbedded_uc6 hG hnab hM
  let SY : Sylow p ↥M := S.subtype hSM
  have hSY : (SY : Subgroup ↥M) ≤ commutator ↥M := by
    intro y hy
    rw [Sylow.coe_subtype] at hy
    obtain ⟨z, hz, hzy⟩ := hSc hy
    have : z = y := Subtype.ext hzy
    exact this ▸ hz
  have htop := oResidual_eq_top_of_sylow_le_commutator_uc6 SY hSY
  rw [opRes_eq_map_oResidual_uc6 hp, htop, Subgroup.map_top, Subgroup.range_subtype]

theorem r6_38_of_sigma (D : Data G) (h : R6_38Sigma D) : R6_38 D := by
  intro p hp _ hcase
  rcases hcase with hs | hse
  · exact h p hs
  · exact opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hp hse

end Strong

end CFSG.LocalAnalysis.UniquenessCase.UC6
