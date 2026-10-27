module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Open.StatedDefs
public import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge2
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
import CFSG.GroupTheory.LocalCores.Components
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
import CFSG.LocalAnalysis.UniquenessCase.UC22S22b
import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep
import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
import CFSG.RankThree.PartTwo.Sec4.T444.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace P22fin3

theorem opp_le_of_map_eq_top {p : ℕ} (hpP : p.Prime) (hp2 : p ≠ 2) {X N : Subgroup G}
    (hNY : N ≤ Opp p X) (hN : (N.subgroupOf (Opp p X)).Normal)
    (htop : (N.subgroupOf (Opp p X)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Opp p X))) = ⊤) :
    Opp p X ≤ N := by
  refine (Subgroup.closure_le N).2 fun y hy => ?_
  obtain ⟨k, hk⟩ := hy.2
  refine PartTwo.s13_mem_of_barImage_of_pPart hNY hN hpP hp2 (Subgroup.subset_closure hy)
    ⟨k, by rw [← hk, pow_orderOf_eq_one]⟩ ?_
  change _ ∈ (N.subgroupOf (Opp p X)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Opp p X)))
  rw [htop]
  exact Subgroup.mem_top _

theorem not_dvd_card_center_of_equiv {Q : Type*} [Group Q] {p k n : ℕ} (hk : 1 ≤ k)
    (hn : n ≠ 0) (h1 : ¬ 2 ^ n ≡ 1 [MOD p])
    (e : Q ≃* CFSG.Open.StatedSL k (GaloisField 2 n)) : ¬ p ∣ Nat.card (center Q) := by
  intro hp
  have hc : Nat.card (center Q) =
      Nat.card (center (Matrix.SpecialLinearGroup (Fin k) (GaloisField 2 n))) :=
    Nat.card_congr (Subgroup.centerCongr
      (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL _ _).symm)).toEquiv
  have h2 := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd hk (GaloisField 2 n)
  rw [← hc, GaloisField.card 2 n hn] at h2
  exact h1 ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).2
    ((hp.trans h2).trans (Nat.gcd_dvd_right _ _))).symm

theorem opp_mem_calC {M V X : Subgroup G} (hVM : M ≤ normalizer (V : Set G)) (hXM : X ≤ M)
    (hCX : M ⊓ centralizer (V : Set G) ≤ X) {p : ℕ} (hpP : p.Prime) (hp2 : p ≠ 2) {x : G}
    (hx : x ∈ M ⊓ centralizer (V : Set G)) (hxp : orderOf x = p) {m n : ℕ} (hm : 2 < m)
    (hn : 1 < n) (h1 : ¬ 2 ^ n ≡ 1 [MOD p])
    (e : ↥(Opp p (⊤ : Subgroup (Bar2 X))) ≃* CFSG.Open.StatedSL (m - 1) (GaloisField 2 n)) :
    Opp p X ≤ M ⊓ centralizer (V : Set G) ∧ Opp p X ∈ calC (M ⊓ centralizer (V : Set G)) ∧
      Opp p X ∈ calC M ∧
      Nonempty (Bar2 (Opp p X) ≃* CFSG.Open.StatedSL (m - 1) (GaloisField 2 n)) := by
  set C := M ⊓ centralizer (V : Set G) with hC
  set Y := Opp p X with hY
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYX : Y ≤ X := PartTwo.s13_Bar13_opp_le p X
  have hXY : X ≤ normalizer (Y : Set G) := by
    have hc := PartTwo.s13_Bar13_opp_conjInv p (M := X) (X := X)
      fun a ha b hb => X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)
    intro g hg
    refine Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => hc g hg y hy, fun hy => ?_⟩
    have h := hc g⁻¹ (X.inv_mem hg) _ hy
    rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h
  have hCM : C ≤ M := inf_le_left
  have hMC : M ≤ normalizer (C : Set G) := by
    haveI : (C.subgroupOf M).Normal := by
      rw [hC, Subgroup.inf_subgroupOf_left]
      exact kerAct_normal M V hVM
    exact Subgroup.le_normalizer_of_normal_subgroupOf hCM
  have hYC : Y ≤ normalizer (C : Set G) := (hYX.trans hXM).trans hMC
  obtain ⟨e₁, -⟩ := uc22p20d_bar2Equiv hYX
    (.step hYX ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).2 hXY) (.refl X))
  have hbar : (Y.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) =
      Opp p (⊤ : Subgroup (Bar2 X)) := by
    have h := PartTwo.s13_barImage_opp hpP (le_refl X)
    rw [PartTwo.s13_barImage_self] at h
    exact h
  let eY : Bar2 Y ≃* CFSG.Open.StatedSL (m - 1) (GaloisField 2 n) :=
    (e₁.trans (MulEquiv.subgroupCongr hbar)).trans e
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hqC : CFSG.IsQuasisimple (Bar2 Y) :=
    CFSG.IsQuasisimple.of_mulEquiv
      (eY.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL _ _).symm)
      (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple _ _
        (by omega) (Or.inr (by rw [hK]; omega)) (Or.inr (by rw [hK]; omega)))
  have hq : CFSG.Open.IsQuasisimple (Bar2 Y) := ⟨hqC.1.commutator_eq_top, hqC.2.1⟩
  have hπ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y)
  have hperf : ⁅Y, Y⁆ = Y := by
    have hle : ⁅Y, Y⁆ ≤ Y := Subgroup.commutator_le_of_le le_rfl le_rfl
    refine le_antisymm hle (opp_le_of_map_eq_top hpP hp2 hle
      (Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_left Y Y))
      ?_)
    rw [eq_top_iff, ← hqC.1.commutator_eq_top, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨a, rfl⟩ := hπ a
    obtain ⟨b, rfl⟩ := hπ b
    rw [← map_commutatorElement]
    exact Subgroup.mem_map_of_mem _ (Subgroup.commutator_mem_commutator a.2 b.2)
  have hCY : (C.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYC
  have hYleC : Y ≤ C := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hqC (hCY.map _ hπ) with htop | hcen
    · refine (opp_le_of_map_eq_top hpP hp2 (N := C ⊓ Y) inf_le_right ?_ ?_).trans inf_le_left
      · rw [Subgroup.inf_subgroupOf_right]
        exact hCY
      · rw [Subgroup.inf_subgroupOf_right]
        exact htop
    · exfalso
      have hxY : x ∈ Y := Subgroup.subset_closure ⟨hCX hx, 1, by rw [hxp, pow_one]⟩
      have hx' : orderOf (⟨x, hxY⟩ : ↥Y) = p := (Subgroup.orderOf_mk x hxY).trans hxp
      have hord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨x, hxY⟩) = p := by
        have hdvd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨x, hxY⟩) ∣ p :=
          hx' ▸ orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) ⟨x, hxY⟩
        rcases (Nat.dvd_prime hpP).1 hdvd with h | h
        · rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
          obtain ⟨k, hk⟩ := IsPGroup.iff_card.1
            (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥Y))
          have h2 := Subgroup.orderOf_dvd_natCard _ h
          rw [hx', hk] at h2
          exact absurd ((Nat.prime_dvd_prime_iff_eq hpP Nat.prime_two).1
            (hpP.dvd_of_dvd_pow h2)) hp2
        · exact h
      have hmem := hcen (Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
        (show (⟨x, hxY⟩ : ↥Y) ∈ C.subgroupOf Y from hx))
      exact not_dvd_card_center_of_equiv (by omega) (by omega) h1 eY
        (hord ▸ Subgroup.orderOf_dvd_natCard _ hmem)
  have hnYC : (Y.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYleC).2 (hCX.trans hXY)
  have hsubCM : CFSG.Open.IsSubnormal C M :=
    .step hCM ((Subgroup.normal_subgroupOf_iff_le_normalizer hCM).2 hMC) (.refl M)
  exact ⟨hYleC, ⟨.step hYleC hnYC (.refl C), hperf, hq⟩, ⟨.step hYleC hnYC hsubCM, hperf, hq⟩,
    ⟨eY⟩⟩

end P22fin3

end CFSG.LocalAnalysis.UniquenessCase.UC22
