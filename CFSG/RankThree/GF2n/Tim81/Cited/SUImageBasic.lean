module

public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
public import CFSG.Timmesfeld.LieEmbed.UnitaryForms
import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryPerpCount
import CFSG.Timmesfeld.Transvection.AssembleRel
import CFSG.Timmesfeld.Transvection.ModelSURadical
import CFSG.GroupTheory.OddKernelImage
import CFSG.LocalAnalysis.StandardType.SUCenterOdd

public section

namespace CFSG.RankThree.GF2n.Tim81

open Matrix CFSG CFSG.CGT.Timmesfeld75 CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection
open scoped MatrixGroups commutatorElement

theorem map_sylow_le_normalizer_sylowRoots {K : Type} [Group K] {X₀ : Subgroup K}
    {Δ : Set (Subgroup K)} (hΔ : ∀ A ∈ Δ, ∀ x ∈ X₀, conjSubgroup x A ∈ Δ)
    (S : Sylow 2 ↥X₀) :
    (S : Subgroup ↥X₀).map X₀.subtype ≤
      Subgroup.normalizer (sylowRoots X₀ Δ S : Set K) := by
  intro s hs
  rw [mem_normalizer_iff_conjSubgroup_eq]
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
  let D : Set (Subgroup K) :=
    {A | A ∈ Δ ∧ A ≤ (S : Subgroup ↥X₀).map X₀.subtype}
  have hD : ∀ A ∈ D, conjSubgroup (X₀.subtype t) A ∈ D := by
    intro A hA
    refine ⟨hΔ A hA.1 (X₀.subtype t) t.2, ?_⟩
    calc conjSubgroup (X₀.subtype t) A
        ≤ conjSubgroup (X₀.subtype t) ((S : Subgroup ↥X₀).map X₀.subtype) :=
          Subgroup.map_mono hA.2
      _ = (conjSubgroup t (S : Subgroup ↥X₀)).map X₀.subtype := by
          rw [map_conjSubgroup]
      _ = (S : Subgroup ↥X₀).map X₀.subtype := by
          rw [mem_normalizer_iff_conjSubgroup_eq.mp (Subgroup.le_normalizer ht)]
  have hDinv : ∀ A ∈ D, conjSubgroup (X₀.subtype t⁻¹) A ∈ D := by
    intro A hA
    refine ⟨hΔ A hA.1 (X₀.subtype t⁻¹) (t⁻¹).2, ?_⟩
    calc conjSubgroup (X₀.subtype t⁻¹) A
        ≤ conjSubgroup (X₀.subtype t⁻¹) ((S : Subgroup ↥X₀).map X₀.subtype) :=
          Subgroup.map_mono hA.2
      _ = (conjSubgroup t⁻¹ (S : Subgroup ↥X₀)).map X₀.subtype := by
          rw [map_conjSubgroup]
      _ = (S : Subgroup ↥X₀).map X₀.subtype := by
          rw [mem_normalizer_iff_conjSubgroup_eq.mp
            (Subgroup.le_normalizer ((S : Subgroup ↥X₀).inv_mem ht))]
  have hdef : sylowRoots X₀ Δ S = ⨆ A ∈ D, A := rfl
  have hmap : conjSubgroup (X₀.subtype t) (sylowRoots X₀ Δ S) =
      ⨆ A ∈ D, conjSubgroup (X₀.subtype t) A := by
    rw [hdef]
    simp only [conjSubgroup, Subgroup.map_iSup]
  rw [hmap, hdef]
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun A hA =>
      le_iSup₂_of_le (conjSubgroup (X₀.subtype t) A) (hD A hA) le_rfl
  · refine iSup₂_le fun A hA => ?_
    have hA' := hDinv A hA
    have heq : conjSubgroup (X₀.subtype t) (conjSubgroup (X₀.subtype t⁻¹) A) = A := by
      rw [conjSubgroup_conjSubgroup, ← map_mul, mul_inv_cancel, map_one, conjSubgroup_one]
    rw [← heq]
    exact le_iSup₂_of_le (conjSubgroup (X₀.subtype t⁻¹) A) hA' le_rfl

namespace SUTrans

theorem conjSubgroup_mem_of_mem {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {K : Type*} [Group K] {m : ℕ} {Φ : SU σ m →* K}
    (hm : 2 ≤ m) {Δ : Set (Subgroup K)}
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) x).map Φ)
    {A : Subgroup K} (hA : A ∈ Δ) (y : SU σ m) :
    conjSubgroup (Φ y) A ∈ Δ := by
  obtain ⟨x, rfl⟩ := (hΔ A).1 hA
  change conjSubgroup (Φ y) ((conjSubgroup x
    (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm))).map Φ) ∈ Δ
  refine (hΔ _).2 ⟨y * x, ?_⟩
  change conjSubgroup (Φ y) ((conjSubgroup x
    (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm))).map Φ) =
    (conjSubgroup (y * x) (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm))).map Φ
  calc conjSubgroup (Φ y) ((conjSubgroup x
        (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm))).map Φ)
      = conjSubgroup (Φ y) (conjSubgroup (Φ x)
          ((Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)).map Φ)) := by
        rw [map_conjSubgroup]
    _ = conjSubgroup (Φ (y * x))
          ((Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)).map Φ) := by
        rw [conjSubgroup_conjSubgroup, ← map_mul]
    _ = (conjSubgroup (y * x)
          (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm))).map Φ := by
        rw [map_conjSubgroup]

theorem exists_conjSubgroup_eq_of_mem {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {K : Type*} [Group K] {m : ℕ} {Φ : SU σ m →* K}
    (hm : 2 ≤ m) {Δ : Set (Subgroup K)}
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) x).map Φ)
    {A B : Subgroup K} (hA : A ∈ Δ) (hB : B ∈ Δ) :
    ∃ y : SU σ m, B = conjSubgroup (Φ y) A := by
  obtain ⟨x, rfl⟩ := (hΔ A).1 hA
  obtain ⟨x', rfl⟩ := (hΔ B).1 hB
  refine ⟨x' * x⁻¹, ?_⟩
  change (conjSubgroup x' (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm))).map Φ =
    conjSubgroup (Φ (x' * x⁻¹)) ((conjSubgroup x
      (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm))).map Φ)
  calc (conjSubgroup x' (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm))).map Φ
      = conjSubgroup (Φ x')
          ((Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)).map Φ) := by
        rw [map_conjSubgroup]
    _ = conjSubgroup (Φ (x' * x⁻¹)) ((conjSubgroup x
          (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm))).map Φ) := by
        rw [map_mul, map_inv, map_conjSubgroup, conjSubgroup_conjSubgroup]
        congr 1
        group

theorem mul_self_eq_one_of_mem {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {K : Type*} [Group K] {m : ℕ} {Φ : SU σ m →* K}
    (hm : 2 ≤ m) {Δ : Set (Subgroup K)}
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) x).map Φ)
    [CharP F 2] {A : Subgroup K} (hA : A ∈ Δ) {a : K} (ha : a ∈ A) :
    a * a = 1 := by
  obtain ⟨v, T, hv, hvv, hT, rfl⟩ := exists_eq_map_of_mem hσ hm hΔ hA
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨c, hc, hxmat⟩ := (hT.1 x).1 hx
  have hsq : x * x = 1 := by
    apply suMat_injective σ
    rw [map_mul, hxmat, uTrans_mul_uTrans σ hvv, CharTwo.add_self_eq_zero, uTrans_zero,
      map_one]
  calc Φ x * Φ x = Φ (x * x) := (map_mul Φ x x).symm
    _ = Φ 1 := by rw [hsq]
    _ = 1 := map_one Φ

theorem isPGroup_of_mem {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {K : Type*} [Group K] {m : ℕ} {Φ : SU σ m →* K}
    (hm : 2 ≤ m) {Δ : Set (Subgroup K)}
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) x).map Φ)
    [CharP F 2] {A : Subgroup K} (hA : A ∈ Δ) : IsPGroup 2 A := by
  obtain ⟨v, T, hv, hvv, hT, rfl⟩ := exists_eq_map_of_mem hσ hm hΔ hA
  have hP : IsPGroup 2 T :=
    (ModelRank.isPGroup_uRad (σ := σ) v).of_injective
      (Subgroup.inclusion (ModelRank.le_uRad_of_isUTransGroup hvv hT))
      (Subgroup.inclusion_injective _)
  exact hP.map Φ

theorem natCard_of_mem {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {K : Type*} [Group K] {m : ℕ} {Φ : SU σ m →* K}
    (hm : 2 ≤ m) {Δ : Set (Subgroup K)}
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) x).map Φ)
    [Finite F] [CharP F 2] (hker : Φ.ker ≤ Subgroup.center (SU σ m))
    {A : Subgroup K} (hA : A ∈ Δ) : Nat.card A = Nat.card (traceZero σ) := by
  obtain ⟨v, T, hv, hvv, hT, rfl⟩ := exists_eq_map_of_mem hσ hm hΔ hA
  haveI : Finite (SU σ m) :=
    Finite.of_injective (SUExtras.mat σ m) (SUExtras.mat_injective (σ := σ) (n := m))
  have hP : IsPGroup 2 T :=
    (ModelRank.isPGroup_uRad (σ := σ) v).of_injective
      (Subgroup.inclusion (ModelRank.le_uRad_of_isUTransGroup hvv hT))
      (Subgroup.inclusion_injective _)
  have hodd : Odd (Nat.card Φ.ker) :=
    CFSG.StandardType.odd_natCard_of_le_center_SU σ hker
  rw [CFSG.GroupTheory.natCard_map_of_isPGroup_of_odd (Φ := Φ) hodd hP]
  exact ModelRank.IsUTransGroup.natCard_eq hv hT

theorem commute_of_isRootTypeTI {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {K : Type*} [Group K] {m : ℕ} {Φ : SU σ m →* K}
    (hm : 2 ≤ m) {Δ : Set (Subgroup K)}
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) x).map Φ)
    {W : Subgroup K} (hW : Tim78.IsRootTypeTI W)
    (hWΔ : ∃ k : K, conjSubgroup k W ∈ Δ) {U : Subgroup K} (hU : U ∈ Δ)
    (hne : W ⊓ Subgroup.normalizer (U : Set K) ≠ ⊥) :
    ∀ a ∈ W, ∀ b ∈ U, a * b = b * a := by
  obtain ⟨k, hk⟩ := hWΔ
  obtain ⟨y, hy⟩ := exists_conjSubgroup_eq_of_mem hσ hm hΔ hk hU
  have hUeq : U = conjSubgroup (Φ y * k) W := by
    rw [hy, conjSubgroup_conjSubgroup]
  have hne' : W ⊓ Subgroup.normalizer (conjSubgroup (Φ y * k) W : Set K) ≠ ⊥ := by
    rw [← hUeq]
    exact hne
  intro a ha b hb
  exact hW.2 (Φ y * k) hne' a ha b (by rwa [hUeq] at hb)

end SUTrans

end CFSG.RankThree.GF2n.Tim81
