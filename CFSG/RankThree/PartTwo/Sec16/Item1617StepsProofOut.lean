module

public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofLCen
import CFSG.RankThree.PartTwo.KFacts.K72OutL3
import CFSG.RankThree.PartTwo.KFacts.KS6OuterIndexProof
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item136Pair

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

@[expose] def KS1619Perfect : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → Sec4.IsoLThreePi X 2 n →
    ∀ J : Subgroup X, Group.IsPerfect J → ¬ 3 ∣ Nat.card J → J = ⊥

namespace Proof1617

theorem le_range_conj_of_isPerfect_projectiveSL {K : Type} [Field K] [Finite K]
    (J : Subgroup (MulAut (projectiveSL 3 K))) [Group.IsPerfect J] :
    J ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  have h1 : ⁅J, J⁆ ≤ linearAutGroup 3 K := Subgroup.commutator_le.mpr fun σ _ τ _ => by
    rw [commutatorElement_def]
    exact CFSG.LocalAnalysis.ComponentInitial.OuterDerived.commutator_mem_linearAutGroup
      (by norm_num) σ τ
  have hJD : J ≤ linearAutGroup 3 K := by
    rw [← Subgroup.commutator_eq_self (H := J)]
    exact h1
  have h2 : ⁅linearAutGroup 3 K, linearAutGroup 3 K⁆ ≤
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
    refine Subgroup.commutator_le.mpr fun σ hσ τ hτ => ?_
    obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hσ
    obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.mp hτ
    rw [← map_commutatorElement]
    have hcomm : ∀ a b : Kˣ, a * b * a⁻¹ * b⁻¹ = 1 := fun a b => by
      rw [mul_comm a b]
      group
    have hdet : Matrix.GeneralLinearGroup.det ⁅A, B⁆ = 1 := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact hcomm _ _
    set g : Matrix.SpecialLinearGroup (Fin 3) K :=
      ⟨(⁅A, B⁆ : GL (Fin 3) K), by
        rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]⟩ with hg
    have hgA : Matrix.SpecialLinearGroup.toGL g = ⁅A, B⁆ := Units.ext rfl
    rw [← hgA, ← KFacts.conj_proj_eq_conjAut]
    exact ⟨_, rfl⟩
  calc J = ⁅J, J⁆ := (Subgroup.commutator_eq_self (H := J)).symm
    _ ≤ ⁅linearAutGroup 3 K, linearAutGroup 3 K⁆ := Subgroup.commutator_mono hJD hJD
    _ ≤ _ := h2

theorem units_commutator_eq_one {K : Type*} [Field K] (a b : Kˣ) : a * b * a⁻¹ * b⁻¹ = 1 := by
  rw [mul_comm a b]
  group

theorem le_range_conj_of_isPerfect_unitaryPSU {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f)
    (J : Subgroup (MulAut (unitaryPSU h 3))) [Group.IsPerfect J] :
    J ≤ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  have := h.finite
  have h1 : ⁅J, J⁆ ≤ (KFacts.psuConj h).range := Subgroup.commutator_le.mpr fun σ _ τ _ => by
    rw [commutatorElement_def]
    exact KFacts.commutator_mem_psuConj_range h hq2 σ τ
  have hJD : J ≤ (KFacts.psuConj h).range := by
    rw [← Subgroup.commutator_eq_self (H := J)]
    exact h1
  have h2 : ⁅(KFacts.psuConj h).range, (KFacts.psuConj h).range⁆ ≤
      (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
    refine Subgroup.commutator_le.mpr fun σ hσ τ hτ => ?_
    obtain ⟨A, rfl⟩ := hσ
    obtain ⟨B, rfl⟩ := hτ
    rw [← map_commutatorElement]
    refine KFacts.isInnerAut_psuConj_of_det_eq_pow_three h ⁅A, B⁆ (u := 1) ?_ (by rw [one_pow])
    rw [one_pow, commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    exact (units_commutator_eq_one _ _).symm
  calc J = ⁅J, J⁆ := (Subgroup.commutator_eq_self (H := J)).symm
    _ ≤ ⁅(KFacts.psuConj h).range, (KFacts.psuConj h).range⁆ := Subgroup.commutator_mono hJD hJD
    _ ≤ _ := h2

theorem le_range_conj_of_isPerfect {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (hX : Sec4.IsoLThreePi X 2 n) (J : Subgroup (MulAut X)) [Group.IsPerfect J] :
    J ≤ (MulAut.conj : X →* MulAut X).range := by
  have hq2 : 2 < 2 ^ n :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  have key : ∀ {Y : Type} [Group Y] (e : X ≃* Y),
      (∀ (J' : Subgroup (MulAut Y)), Group.IsPerfect J' →
        J' ≤ (MulAut.conj : Y →* MulAut Y).range) →
      J ≤ (MulAut.conj : X →* MulAut X).range := by
    intro Y _ e hY σ hσ
    have hJ' := hY (J.map (MulAut.congr e).toMonoidHom) (Group.IsPerfect.map _)
    have hmem : MulAut.congr e σ ∈ J.map (MulAut.congr e).toMonoidHom := ⟨σ, hσ, rfl⟩
    exact (KFacts.isInnerAut_congr e σ).mp (hJ' hmem)
  rcases hX with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  · obtain ⟨φ⟩ := KFacts.nonempty_projSL_mulEquiv 3 (GaloisField 2 n)
    exact key (e.trans φ) fun J' _ => le_range_conj_of_isPerfect_projectiveSL J'
  · have h : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
      ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
    obtain ⟨φ⟩ := KFacts.nonempty_unitaryPSU_mulEquiv_projSU h
    exact key (e.trans φ.symm) fun J' _ => le_range_conj_of_isPerfect_unitaryPSU h hq2 J'

end Proof1617

theorem ks1619AutPerfect_of (hP : KS1619Perfect) : KS1619AutPerfect := by
  intro X _ _ n hn hX J hJ hJ3
  have hle := Proof1617.le_range_conj_of_isPerfect hn hX J
  have hZ : Subgroup.center X = ⊥ := by
    obtain ⟨π, K, _, hKf, hq, ⟨φ⟩⟩ := exists_projImage_model (by omega) hX
    have hq2 : 2 < 2 ^ n :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
    exact center_eq_bot_of_mulEquiv φ (center_projImage_slPi hKf hq hq2)
  set ι : X →* MulAut X := MulAut.conj with hι
  have hιinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxc : x ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := congrArg (fun σ : MulAut X => σ z) (MonoidHom.mem_ker.mp hx)
      simp only [hι, MulAut.conj_apply, MulAut.one_apply] at h1
      calc z * x = x * z * x⁻¹ * x := by rw [h1]
        _ = x * z := by group
    rw [hZ] at hxc
    exact hxc
  set J' := J.comap ι with hJ'
  have hJ'map : J'.map ι = J := Subgroup.map_comap_eq_self hle
  have e : J' ≃* J :=
    (J'.equivMapOfInjective ι hιinj).trans (MulEquiv.subgroupCongr hJ'map)
  have : Group.IsPerfect J' := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  have h3 : ¬ 3 ∣ Nat.card J' := by rwa [Nat.card_congr e.toEquiv]
  have hJ'bot := hP X n hn hX J' this h3
  rw [← hJ'map, hJ'bot, Subgroup.map_bot]

theorem ks1619LCen_of_perfect (hP : KS1619Perfect) : KS1619LCen :=
  ks1619LCen_of (ks1619AutPerfect_of hP)

end CFSG.RankThree.PartTwo.Sec16
