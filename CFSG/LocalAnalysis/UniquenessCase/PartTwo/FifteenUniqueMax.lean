module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem exists_isMaxTwoLocal_ge {H : Subgroup G} (hH : CFSG.Open.IsTwoLocal H) :
    ∃ N : Subgroup G, CFSG.Open.rankThreeIsMaxTwoLocal N ∧ H ≤ N := by
  classical
  set S : Set (Subgroup G) := {N | CFSG.Open.IsTwoLocal N ∧ H ≤ N} with hS
  obtain ⟨N, ⟨hN, hHN⟩, hmax⟩ :=
    Set.exists_max_image S (fun N => Nat.card N) (Set.toFinite S) ⟨H, hH, le_rfl⟩
  refine ⟨N, ⟨hN, fun K hK hNK => ?_⟩, hHN⟩
  have hKS : K ∈ S := ⟨hK, hHN.trans hNK⟩
  exact (Subgroup.eq_of_le_of_card_ge hNK (hmax K hKS)).symm

theorem uniqueMax_conjSubgroup {K X : Subgroup G} (h : UniqueMax K X) (g : G) :
    UniqueMax (conjSubgroup K g) (conjSubgroup X g) := by
  change calMOf (conjSubgroup X g) = {conjSubgroup K g}
  have hcal : calMOf X = {K} := h
  ext N
  constructor
  · intro hN
    obtain ⟨hNmax, hXN⟩ := hN
    have hN'max : rankThreeIsMaxTwoLocal (conjSubgroup N g⁻¹) :=
      UC6.isMaxTwoLocal_conj (show IsMaxTwoLocalSubgroup N from hNmax) g⁻¹
    have hX_le : X ≤ conjSubgroup N g⁻¹ := by
      have h1 : X = conjSubgroup (conjSubgroup X g) g⁻¹ := by
        rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
      rw [h1]
      exact Subgroup.map_mono hXN
    have hmem : conjSubgroup N g⁻¹ ∈ calMOf X := ⟨hN'max, hX_le⟩
    rw [hcal] at hmem
    have hN'K : conjSubgroup N g⁻¹ = K := Set.mem_singleton_iff.mp hmem
    rw [Set.mem_singleton_iff]
    have hN_eq : N = conjSubgroup (conjSubgroup N g⁻¹) g := by
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    rw [hN_eq, hN'K]
  · intro hN
    rw [Set.mem_singleton_iff] at hN
    rw [hN]
    have hKmem : K ∈ calMOf X := by rw [hcal]; exact Set.mem_singleton K
    exact ⟨UC6.isMaxTwoLocal_conj (show IsMaxTwoLocalSubgroup K from hKmem.1) g,
      Subgroup.map_mono hKmem.2⟩

theorem uniqueMax_conjSubgroup_of_mem {M X : Subgroup G} {g a : G}
    (hX : ∀ w ∈ X, w ≠ 1 → UniqueMax M (M ⊓ centralizer ({w} : Set G)))
    (ha : a ∈ conjSubgroup X g) (ha1 : a ≠ 1) :
    UniqueMax (conjSubgroup M g) (conjSubgroup M g ⊓ centralizer ({a} : Set G)) := by
  have hwX : g * a * g⁻¹ ∈ X := mem_conjSubgroup_iff.mp ha
  have hw1 : g * a * g⁻¹ ≠ 1 := by
    intro h
    apply ha1
    have hconj : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [hconj, h]
    simp
  have hmain := uniqueMax_conjSubgroup (hX (g * a * g⁻¹) hwX hw1) g
  have hinf : conjSubgroup (M ⊓ centralizer ({g * a * g⁻¹} : Set G)) g =
      conjSubgroup M g ⊓ centralizer ({a} : Set G) := by
    ext x
    simp only [mem_conjSubgroup_iff, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hxM, hxw⟩
      refine ⟨hxM, ?_⟩
      have h := congrArg (fun t => g⁻¹ * t * g) hxw
      simpa [mul_assoc] using h
    · rintro ⟨hxM, hxa⟩
      refine ⟨hxM, ?_⟩
      calc g * x * g⁻¹ * (g * a * g⁻¹)
          = g * (x * a) * g⁻¹ := by group
        _ = g * (a * x) * g⁻¹ := by rw [hxa]
        _ = (g * a * g⁻¹) * (g * x * g⁻¹) := by group
  change calMOf (conjSubgroup M g ⊓ centralizer ({a} : Set G)) = {conjSubgroup M g}
  rw [← hinf]
  exact hmain

theorem centralizer_le_of_uniqueMax {K : Subgroup G} (hK : rankThreeIsMaxTwoLocal K) {w : G}
    (hw1 : w ≠ 1) (hw2 : ∃ n : ℕ, w ^ (2 ^ n) = 1)
    (hu : UniqueMax K (K ⊓ centralizer ({w} : Set G))) :
    centralizer ({w} : Set G) ≤ K ∧
      ∀ g : G, g ∉ K → ¬ K ⊓ centralizer ({w} : Set G) ≤ conjSubgroup K g := by
  have hK' : IsMaxTwoLocalSubgroup K := hK
  have huEq : calMOf (K ⊓ centralizer ({w} : Set G)) = {K} := hu
  have hQne : Subgroup.zpowers w ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hw1
  obtain ⟨n, hn⟩ := hw2
  have hQ2 : IsPGroup 2 (Subgroup.zpowers w) :=
    IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hn)
  have hcent_eq : centralizer ({w} : Set G) = centralizer (Subgroup.zpowers w : Set G) := by
    rw [Subgroup.zpowers_eq_closure w, Subgroup.centralizer_closure]
  have hcent_le : centralizer ({w} : Set G) ≤ normalizer (Subgroup.zpowers w : Set G) :=
    (le_of_eq hcent_eq).trans (Subgroup.centralizer_le_normalizer _)
  have hH : CFSG.Open.IsTwoLocal (normalizer (Subgroup.zpowers w : Set G)) :=
    ⟨Subgroup.zpowers w, hQne, hQ2, rfl⟩
  obtain ⟨N, hN, hHN⟩ := exists_isMaxTwoLocal_ge hH
  have hNmem : N ∈ calMOf (K ⊓ centralizer ({w} : Set G)) :=
    ⟨hN, le_trans inf_le_right (hcent_le.trans hHN)⟩
  rw [huEq] at hNmem
  have hNK : N = K := Set.mem_singleton_iff.mp hNmem
  have hcentK : centralizer ({w} : Set G) ≤ K := by
    have hle := hcent_le.trans hHN
    rw [hNK] at hle
    exact hle
  refine ⟨hcentK, fun g hg hle => ?_⟩
  have hKg : rankThreeIsMaxTwoLocal (conjSubgroup K g) :=
    UC6.isMaxTwoLocal_conj hK' g
  have hmem : conjSubgroup K g ∈ calMOf (K ⊓ centralizer ({w} : Set G)) := ⟨hKg, hle⟩
  rw [huEq] at hmem
  have heq : conjSubgroup K g = K := Set.mem_singleton_iff.mp hmem
  have hnorm : g ∈ normalizer (K : Set G) := conjSubgroup_eq_iff_mem_normalizer.mp heq
  rw [UC6.normalizer_eq_of_isMaxTwoLocal hK'] at hnorm
  exact hg hnorm

theorem inf_conjSubgroup_eq_bot_of_uniqueMax {K : Subgroup G} (hK : rankThreeIsMaxTwoLocal K)
    {U₁ U₂ : Subgroup G} (h₁ : IsPGroup 2 U₁) (h₂ : IsPGroup 2 U₂)
    (hU₁ : ∀ w ∈ U₁, w ≠ 1 → UniqueMax K (K ⊓ centralizer ({w} : Set G)))
    (hU₂ : ∀ w ∈ U₂, w ≠ 1 → UniqueMax K (K ⊓ centralizer ({w} : Set G))) {g : G}
    (hg : g ∉ K) : U₁ ⊓ conjSubgroup U₂ g = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  obtain ⟨hxU₁, hxU₂⟩ := Subgroup.mem_inf.mp hx
  have hx2 : ∃ n : ℕ, x ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := h₁ ⟨x, hxU₁⟩
    exact ⟨n, by simpa [Subgroup.coe_pow] using congrArg Subtype.val hn⟩
  obtain ⟨-, hnotle⟩ := centralizer_le_of_uniqueMax hK hx1 hx2 (hU₁ x hxU₁ hx1)
  have hw'U₂ : g * x * g⁻¹ ∈ U₂ := mem_conjSubgroup_iff.mp hxU₂
  have hw'1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have hconj : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [hconj, h]
    simp
  have hw'2 : ∃ n : ℕ, (g * x * g⁻¹) ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := h₂ ⟨g * x * g⁻¹, hw'U₂⟩
    exact ⟨n, by simpa [Subgroup.coe_pow] using congrArg Subtype.val hn⟩
  have hcentw' : centralizer ({g * x * g⁻¹} : Set G) ≤ K :=
    (centralizer_le_of_uniqueMax hK hw'1 hw'2 (hU₂ _ hw'U₂ hw'1)).1
  have hle : K ⊓ centralizer ({x} : Set G) ≤ conjSubgroup K g := by
    intro y hy
    obtain ⟨-, hycent⟩ := Subgroup.mem_inf.mp hy
    have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hycent
    rw [mem_conjSubgroup_iff]
    apply hcentw'
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * y * g⁻¹ * (g * x * g⁻¹)
        = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hyx]
      _ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
  exact hnotle g hg hle

theorem inf_eq_bot_of_not_le_of_uniqueMax {K : Subgroup G} (hK : rankThreeIsMaxTwoLocal K)
    {U X : Subgroup G} (hU2 : IsPGroup 2 U)
    (hU : ∀ w ∈ U, w ≠ 1 → UniqueMax K (K ⊓ centralizer ({w} : Set G)))
    (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hXK : ¬ X ≤ K) : U ⊓ X = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  by_contra hw1
  obtain ⟨hwU, hwX⟩ := Subgroup.mem_inf.mp hw
  have hw2 : ∃ n : ℕ, w ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hU2 ⟨w, hwU⟩
    exact ⟨n, by simpa [Subgroup.coe_pow] using congrArg Subtype.val hn⟩
  have hcentw : centralizer ({w} : Set G) ≤ K :=
    (centralizer_le_of_uniqueMax hK hw1 hw2 (hU w hwU hw1)).1
  exact hXK (le_trans (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (hX x hx w hwX)) hcentw)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
