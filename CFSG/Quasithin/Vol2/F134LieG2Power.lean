module

public import CFSG.RankThree.PartTwo.KFacts.AutG2
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiTwoAAutomorphisms
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.Quasithin.F134.LieG2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem units_map_entrywiseHom_eq_pow {σ : K →+* K} {m : ℕ} (hσ : ∀ c, σ c = c ^ m)
    {g : ModGL τ K} (hg : g ∈ diagonalGroup) : Units.map (entrywiseHom σ) g = g ^ m := by
  refine Units.ext (end_ext_single fun b => ?_)
  obtain ⟨c, hc⟩ := exists_apply_single_of_mem_diagonalGroup hg b
  have hpow : ∀ k : ℕ, ((g ^ k : ModGL τ K) : Module.End K (RootModule τ K))
      (Finsupp.single b 1) = ((c : K) ^ k) • Finsupp.single b 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Units.val_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ,
        mul_comm]
  rw [hpow, Units.coe_map]
  change entrywise σ (g : Module.End K (RootModule τ K)) (Finsupp.single b 1) = _
  rw [entrywise_single, hc, ← hσ]
  ext l
  by_cases hbl : b = l <;> simp [hbl]

end Torus

section Borel

variable {τ : Tag} {K : Type} [Field K]

theorem commutator_mem_posUnipotent {b c : ModGL τ K} (hb : b ∈ borelGroup τ K)
    (hc : c ∈ borelGroup τ K) : b * c * b⁻¹ * c⁻¹ ∈ posUnipotent τ K := by
  obtain ⟨hHab, -, hHN, -, hHU, -⟩ := triangular_borel_structure.{0, 0} τ K
  have hb' : b ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← hHU]
    exact hb
  have hc' : c ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← hHU]
    exact hc
  obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := hb'
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := hc'
  have hconj : ∀ h ∈ torusGroup τ K, ∀ u ∈ posUnipotent τ K, h * u * h⁻¹ ∈ posUnipotent τ K :=
    fun h hh u hu => (Subgroup.mem_normalizer_iff.1 (hHN hh) u).1 hu
  have h12 : h₁ * h₂ * h₁⁻¹ = h₂ := by rw [hHab h₁ hh₁ h₂ hh₂, mul_inv_cancel_right]
  have e : h₁ * u₁ * (h₂ * u₂) * (h₁ * u₁)⁻¹ * (h₂ * u₂)⁻¹ =
      (h₁ * u₁ * h₁⁻¹) * ((h₁ * h₂) * (u₂ * u₁⁻¹) * (h₁ * h₂)⁻¹) *
        (h₁ * h₂ * h₁⁻¹ * u₂⁻¹ * h₂⁻¹) := by
    group
  rw [e, h12]
  exact mul_mem (mul_mem (hconj _ hh₁ _ hu₁)
    (hconj _ (mul_mem hh₁ hh₂) _ (mul_mem hu₂ (inv_mem hu₁)))) (hconj _ hh₂ _ (inv_mem hu₂))

theorem inv_pow_mul_pow_mem_posUnipotent {h u : ModGL τ K} (hh : h ∈ torusGroup τ K)
    (hu : u ∈ posUnipotent τ K) (m : ℕ) : (h ^ m)⁻¹ * (h * u) ^ m ∈ posUnipotent τ K := by
  obtain ⟨-, -, hHN, -⟩ := triangular_borel_structure.{0, 0} τ K
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (h ^ (m + 1))⁻¹ * (h * u) ^ (m + 1) =
        h⁻¹ * ((h ^ m)⁻¹ * (h * u) ^ m) * h⁻¹⁻¹ * u := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hHN (inv_mem hh)) _).1 ih) hu


theorem inv_conj_entrywise_mul_pow_mem {σ : K ≃+* K} {m : ℕ} (hσ : ∀ c, σ c = c ^ m)
    {g b : ModGL τ K} (hg : g ∈ borelGroup τ K) (hb : b ∈ borelGroup τ K) :
    (g * Units.map (entrywiseHom σ.toRingHom) b * g⁻¹)⁻¹ * b ^ m ∈ posUnipotent τ K := by
  obtain ⟨-, -, -, -, hHU, -⟩ := triangular_borel_structure.{0, 0} τ K
  have hb' : b ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← hHU]
    exact hb
  obtain ⟨h, hh, u, hu, rfl⟩ := hb'
  have hUσ : (posUnipotent τ K).map (Units.map (entrywiseHom σ.toRingHom)) =
      posUnipotent τ K :=
    map_rootSpan_of_forall fun α _ => map_entrywise_rootSubgroup σ α
  have hσU : Units.map (entrywiseHom σ.toRingHom) u ∈ posUnipotent τ K := by
    rw [← hUσ]
    exact Subgroup.mem_map_of_mem _ hu
  have hσh : Units.map (entrywiseHom σ.toRingHom) h = h ^ m :=
    units_map_entrywiseHom_eq_pow hσ (torusGroup_le_diagonalGroup hh)
  rw [map_mul, hσh]
  set v := Units.map (entrywiseHom σ.toRingHom) u with hv
  have hc : h ^ m * v ∈ borelGroup τ K :=
    mul_mem (torusGroup_le_borelGroup (pow_mem hh m)) (Subgroup.mem_sup_right hσU)
  have e : (g * (h ^ m * v) * g⁻¹)⁻¹ * (h * u) ^ m =
      (g * (h ^ m * v)⁻¹ * g⁻¹ * (h ^ m * v)⁻¹⁻¹) * (v⁻¹ * ((h ^ m)⁻¹ * (h * u) ^ m)) := by
    group
  rw [e]
  exact mul_mem (commutator_mem_posUnipotent hg (inv_mem hc))
    (mul_mem (inv_mem hσU) (inv_pow_mul_pow_mem_posUnipotent hh hu m))

end Borel

section G2


variable {K : Type} [Field K]

theorem exists_pow_of_map_posUnipotent [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (α : MulAut (adjointGroup .G2 K))
    (hα : ((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)).map α.toMonoidHom =
      (posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)) :
    ∃ s : ℕ, ∀ b : adjointGroup .G2 K, (b : ModGL .G2 K) ∈ borelGroup .G2 K →
      (((α b)⁻¹ * b ^ 2 ^ s : adjointGroup .G2 K) : ModGL .G2 K) ∈ posUnipotent .G2 K := by
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have : Finite (ModGL .G2 K) := finite_modGL
  have hBC : borelGroup .G2 K ≤ adjointGroup .G2 K :=
    ((triangular_borel_structure.{0, 0} .G2 K).2.2.2.2.2.2.2.2.2.2.2 K).1
  have hUC : posUnipotent .G2 K ≤ adjointGroup .G2 K := le_sup_right.trans hBC
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    norm_num
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨hdec, -⟩ := CFSG.RankThree.PartTwo.KFacts.g2_automorphism_normal_form hK3 hK4
  obtain ⟨g, σ, rfl⟩ := hdec α
  obtain ⟨s, -, hσ, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_frobenius_pow_eq (by omega : 1 ≤ n) hK σ
  have hUσ : (posUnipotent .G2 K).map (Units.map (entrywiseHom σ.toRingHom)) =
      posUnipotent .G2 K :=
    map_rootSpan_of_forall fun β _ => map_entrywise_rootSubgroup σ β
  have hφ : ((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)).map
      (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ).toMonoidHom =
      (posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      have hu' : (u : ModGL .G2 K) ∈ posUnipotent .G2 K := hu
      show ((CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ u : adjointGroup .G2 K) :
        ModGL .G2 K) ∈ posUnipotent .G2 K
      rw [CFSG.RankThree.PartTwo.KFacts.coe_g2FieldHom, ← hUσ]
      exact Subgroup.mem_map_of_mem _ hu'
    · rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
  have hg : ((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)).map
      (MulAut.conj g).toMonoidHom = (posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K) := by
    rwa [map_mulAut_mul, hφ] at hα
  have hgN : (g : ModGL .G2 K) ∈
      Subgroup.normalizer (posUnipotent .G2 K : Set (ModGL .G2 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom
        (show (⟨x, hUC hx⟩ : adjointGroup .G2 K) ∈
          (posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K) from hx)
      rw [hg] at h1
      exact h1
    · intro hx
      have hxC : x ∈ adjointGroup .G2 K := by
        have e : x = (g : ModGL .G2 K)⁻¹ * (g * x * (g : ModGL .G2 K)⁻¹) * g := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem g.2) (hUC hx)) g.2
      have h1 : (⟨g * x * (g : ModGL .G2 K)⁻¹, hUC hx⟩ : adjointGroup .G2 K) ∈
          ((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)).map
            (MulAut.conj g).toMonoidHom := by
        rw [hg]
        exact hx
      obtain ⟨y, hy, hyx⟩ := h1
      have hyx' : y = ⟨x, hxC⟩ := by
        have h2 := congrArg Subtype.val hyx
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
          Subgroup.coe_inv] at h2
        exact Subtype.ext (mul_right_cancel (mul_left_cancel h2))
      rw [hyx'] at hy
      exact hy
  have hgB : (g : ModGL .G2 K) ∈ borelGroup .G2 K := by
    rw [← (borel_self_normalizers .G2 K).1]
    exact ⟨g.2, hgN⟩
  refine ⟨s, fun b hb => ?_⟩
  have hαb : ((MulAut.conj g * CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ) b : ModGL .G2 K) =
      (g : ModGL .G2 K) * Units.map (entrywiseHom σ.toRingHom) (b : ModGL .G2 K) *
        (g : ModGL .G2 K)⁻¹ := by
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      CFSG.RankThree.PartTwo.KFacts.coe_g2FieldHom, Subgroup.coe_inv]
  rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hαb]
  exact inv_conj_entrywise_mul_pow_mem hσ hgB hb

end G2

end CFSG.Quasithin.F134.LieG2
