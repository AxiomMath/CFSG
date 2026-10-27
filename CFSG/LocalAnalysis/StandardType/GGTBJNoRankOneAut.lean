module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.RankThree.PartOne.K133.KillL2
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.RankThree.PartOne.K133.Moving
import CFSG.RankThree.PartOne.K133.SylowKill
import CFSG.RankThree.PartOne.S11.TwoActionWiring
import CFSG.RankThree.PartOne.S12.InputsSec15
import CFSG.RankThree.PartOne.S12.Sec137
import CFSG.RankThree.PartOne.S12.Sec15FA
import CFSG.RankThree.PartOne.S12.Sec15Items
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l48nA_not_inner_iff {X : Type} [Group X] (φ : MulAut X) :
    (¬ ∃ y : X, ∀ r : X, φ r = y * r * y⁻¹) ↔
      φ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
  have key : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X ↔
      ∃ y : X, ∀ r : X, φ r = y * r * y⁻¹ := by
    unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, fun r => by simp [MulAut.conj_apply]⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, MulEquiv.ext fun r => by simp [MulAut.conj_apply, hy r]⟩
  rw [key]

private theorem l48nA_inner_card_le {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) [NeZero (p : K)]
    (E : Subgroup (MulAut (CFSG.GorensteinWalter.PSL2 K)))
    (hE : IsElementaryAbelian p E)
    (hle : E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.GorensteinWalter.PSL2 K)) :
    Nat.card E ≤ p := by
  obtain ⟨A, hA, hAcard⟩ :=
    CFSG.RankThree.PartOne.K133.exists_elemAb_card_eq_of_le_inner
      (CFSG.GorensteinWalter.psl2_center_eq_bot K) hE hle
  rw [← hAcard]
  exact CFSG.RankThree.PartOne.K133.psl2_elemAb_card_le hp hp2 A hA

private theorem l48nA_card_le_sq {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) [NeZero (p : K)]
    (E : Subgroup (MulAut (CFSG.GorensteinWalter.PSL2 K)))
    (hE : IsElementaryAbelian p E) : Nat.card E ≤ p ^ 2 := by
  obtain ⟨E₀, hE₀E, hE₀in, hcard⟩ :=
    CFSG.RankThree.PartOne.K133.exists_inner_core_psl2 hp hp2 E hE
  have hE₀el : IsElementaryAbelian p E₀ := CFSG.IsElementaryAbelian.of_le hE hE₀E
  have hE₀card : Nat.card E₀ ≤ p := l48nA_inner_card_le hp hp2 E₀ hE₀el hE₀in
  calc Nat.card E ≤ p * Nat.card E₀ := hcard
    _ ≤ p * p := Nat.mul_le_mul_left p hE₀card
    _ = p ^ 2 := (pow_two p).symm

private theorem l48nA_psl2 {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (E : Subgroup (MulAut (CFSG.GorensteinWalter.PSL2 K)))
    (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 2 ∧
      (Nat.card E = p ^ 2 → ∃ φ ∈ E,
        ¬ ∃ y : CFSG.GorensteinWalter.PSL2 K, ∀ r : CFSG.GorensteinWalter.PSL2 K,
          φ r = y * r * y⁻¹) := by
  haveI : NeZero (p : K) := ⟨fun h => hp2
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 ((CharP.cast_eq_zero_iff K 2 p).1 h)).symm⟩
  have hEel : IsElementaryAbelian p E := CFSG.Open.IsElemAbelian.isElementaryAbelian hE
  refine ⟨l48nA_card_le_sq hp hp2 E hEel, fun hcard => ?_⟩
  by_contra h
  have hle : E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.GorensteinWalter.PSL2 K) := by
    intro φ hφ
    by_contra hφin
    exact h ⟨φ, hφ, (l48nA_not_inner_iff φ).mpr hφin⟩
  have hbound := l48nA_inner_card_le hp hp2 E hEel hle
  rw [hcard] at hbound
  nlinarith [hbound, hp.two_le]

private theorem l48nA_general {R : Type} [Group R] {n : ℕ} (hn : 2 ≤ n)
    (hR : GGHasLabel (⟨.A, 1, n⟩ : LargeEvenLabel) R) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (MulAut R)) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 2 ∧
      (Nat.card E = p ^ 2 → ∃ φ ∈ E, ¬ ∃ y : R, ∀ r : R, φ r = y * r * y⁻¹) := by
  unfold GGHasLabel at hR
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear] at hR
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e₀⟩⟩ := hR
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hKcard
  let e₁ := TypeA.recipeEquiv 2 K
  let e₂ := QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 K).symm
  let e : R ≃* CFSG.GorensteinWalter.PSL2 K := e₀.trans (e₁.trans e₂.symm)
  let F : Subgroup (MulAut (CFSG.GorensteinWalter.PSL2 K)) :=
    E.map (MulAut.congr e).toMonoidHom
  have hFcard : Nat.card F = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hFelem : IsElemAbelian p F :=
    CFSG.Open.IsElemAbelian.map hE (MulAut.congr e).toMonoidHom
  obtain ⟨hbound, houter⟩ := l48nA_psl2 hp hp2 F hFelem
  refine ⟨by simpa [hFcard] using hbound, fun hcard => ?_⟩
  have hFcard2 : Nat.card F = p ^ 2 := by rw [hFcard, hcard]
  obtain ⟨φ, hφF, hφout⟩ := houter hFcard2
  rw [l48nA_not_inner_iff] at hφout
  obtain ⟨ψ, hψE, hψeq⟩ := Subgroup.mem_map.mp hφF
  have hψeq' : MulAut.congr e ψ = φ := hψeq
  refine ⟨ψ, hψE, ?_⟩
  rw [l48nA_not_inner_iff]
  intro hψin
  apply hφout
  rw [← hψeq', ← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e]
  exact ⟨ψ, hψin, rfl⟩

theorem ggRankOne_aut_rank {R : Type} [Group R] {n : ℕ} (hn : 2 ≤ n)
    (hR : GGHasLabel (⟨.A, 1, n⟩ : LargeEvenLabel) R) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (MulAut R)) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 2 ∧
      (Nat.card E = p ^ 2 → ∃ φ ∈ E, ¬ ∃ y : R, ∀ r : R, φ r = y * r * y⁻¹) :=
  l48nA_general hn hR hp hp2 E hE

end CFSG.StandardType

end
