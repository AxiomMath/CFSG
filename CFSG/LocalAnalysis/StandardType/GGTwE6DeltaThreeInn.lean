module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGSmallKGInputsTwE6
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6Torus

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.SmallKG

section Counting

theorem card_le_three_mul_inf {G : Type*} [Group G] {Y N : Subgroup G} [Finite Y] {y₂ : G}
    (hy₂ : y₂ ∈ Y) (h3 : y₂ ^ 3 ∈ N) (hcyc : ∀ y ∈ Y, ∃ k : ℕ, y * (y₂ ^ k)⁻¹ ∈ N) :
    Nat.card Y ≤ 3 * Nat.card (Y ⊓ N : Subgroup G) := by
  haveI : Finite (Y ⊓ N : Subgroup G) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : (Y ⊓ N : Subgroup G) ≤ Y))
      (Subgroup.inclusion_injective _)
  let g : (Y ⊓ N : Subgroup G) × Fin 3 → Y := fun p =>
    ⟨(p.1 : G) * y₂ ^ (p.2 : ℕ), mul_mem (Subgroup.mem_inf.1 p.1.2).1 (pow_mem hy₂ _)⟩
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := hcyc y hy
    have hk' : y₂ ^ k = (y₂ ^ 3) ^ (k / 3) * y₂ ^ (k % 3) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have hk3 : y * (y₂ ^ (k % 3))⁻¹ ∈ N := by
      have e : y * (y₂ ^ (k % 3))⁻¹ = y * (y₂ ^ k)⁻¹ * (y₂ ^ 3) ^ (k / 3) := by
        rw [hk', mul_inv_rev]
        simp [mul_assoc]
      rw [e]
      exact mul_mem hk (pow_mem h3 _)
    refine ⟨(⟨y * (y₂ ^ (k % 3))⁻¹, Subgroup.mem_inf.2
      ⟨mul_mem hy (inv_mem (pow_mem hy₂ _)), hk3⟩⟩, ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    apply Subtype.ext
    simp [g]
  have h := Nat.card_le_card_of_surjective g hg
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h
  linarith

end Counting

section MLevel


variable {K : Type} [Field K]

theorem pow_mem_mul_rootDiagUnit {σ : K →+* K} {h : ModGL TwistTag.E6.tag K}
    (hh : h ∈ graphFixedRootGroup TwistTag.E6 K σ) {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : b ∈ compatParam K σ) (k : ℕ) :
    ∃ c ∈ graphFixedRootGroup TwistTag.E6 K σ,
      (h * rootDiagUnit TwistTag.E6.tag b) ^ k = c * rootDiagUnit TwistTag.E6.tag (b ^ k) := by
  induction k with
  | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, rootDiagUnit_one, mul_one]⟩
  | succ k ih =>
    obtain ⟨c, hc, hck⟩ := ih
    have hbk : b ^ k ∈ compatParam K σ := pow_mem hb k
    refine ⟨c * (rootDiagUnit TwistTag.E6.tag (b ^ k) * h *
      (rootDiagUnit TwistTag.E6.tag (b ^ k))⁻¹), mul_mem hc
        ((Subgroup.mem_normalizer_iff.1
          (rootDiagUnit_mem_normalizer_graphFixedRootGroup (t := TwistTag.E6) hbk) h).1 hh), ?_⟩
    rw [pow_succ, hck, pow_succ, rootDiagUnit_mul]
    group

theorem exists_mul_inv_pow_mem_graphFixedRootGroup [Finite K] {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ q)
    {x x₂ : ModGL TwistTag.E6.tag K} (hx : x ∈ compatHat K σ) (hx₂ : x₂ ∈ compatHat K σ)
    (hn : x₂ ∉ graphFixedRootGroup TwistTag.E6 K σ) :
    ∃ k : ℕ, x * (x₂ ^ k)⁻¹ ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  obtain ⟨h, hh, b, hb, rfl⟩ := hx
  obtain ⟨h₂, hh₂, b₂, hb₂, rfl⟩ := hx₂
  have hn' : rootDiagUnit TwistTag.E6.tag b₂ ∉ graphFixedRootGroup TwistTag.E6 K σ :=
    fun hd => hn (mul_mem hh₂ hd)
  have hnorm : ∀ {c : Fin TwistTag.E6.tag.rank → Kˣ}, c ∈ compatParam K σ →
      ∀ g ∈ graphFixedRootGroup TwistTag.E6 K σ, rootDiagUnit TwistTag.E6.tag c * g *
        (rootDiagUnit TwistTag.E6.tag c)⁻¹ ∈ graphFixedRootGroup TwistTag.E6 K σ :=
    fun hc g hg => (Subgroup.mem_normalizer_iff.1
      (rootDiagUnit_mem_normalizer_graphFixedRootGroup (t := TwistTag.E6) hc) g).1 hg
  obtain ⟨k, hk⟩ := TableB.TwE6.twE6_rootDiag_cyclic hq hK hσ (hnorm hb) (hnorm hb₂) hn'
  refine ⟨k, ?_⟩
  obtain ⟨c, hc, hck⟩ := pow_mem_mul_rootDiagUnit hh₂ hb₂ k
  have e : h * rootDiagUnit TwistTag.E6.tag b * (c * rootDiagUnit TwistTag.E6.tag (b₂ ^ k))⁻¹ =
      h * rootDiagUnit TwistTag.E6.tag (b * (b₂ ^ k)⁻¹) * c⁻¹ := by
    rw [rootDiagUnit_mul, ← rootDiagUnit_inv]
    group
  rw [hck, e]
  exact mul_mem (mul_mem hh hk) (inv_mem hc)

section Transport

variable {n : ℕ} {σ : K →+* K}
  (T : ↥(graphFixedRootGroup TwistTag.E6 K σ) ≃* ↥(twH K n))
  (hZ : Subgroup.center ↥(twH K n) = ⊥)

theorem recipeKappa_of_mem (g : ↥(graphFixedRootGroup TwistTag.E6 K σ))
    (hg : (g : ModGL TwistTag.E6.tag K) ∈ compatHat K σ) :
    recipeKappa T hZ ⟨g, hg⟩ = MulAut.conj (recipeEquiv T hZ g) := by
  ext r'
  obtain ⟨g', rfl⟩ := (recipeEquiv T hZ).surjective r'
  rw [recipeKappa_apply, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  rfl

end Transport

theorem recipe_cyc [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {φ φ₂ : MulAut (twR K n)}
    (hφ : φ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan K (twH K n))
    (hφ₂ : φ₂ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan K (twH K n))
    (hn₂ : φ₂ ∉ (MulAut.conj : twR K n →* MulAut (twR K n)).range) :
    ∃ k : ℕ, φ * (φ₂ ^ k)⁻¹ ∈ (MulAut.conj : twR K n →* MulAut (twR K n)).range := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ : K →+* K := iterateFrobenius K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨e, T₀, hT₀, he⟩ := InnerDiagTwE6.exists_twistedTransport (K := K) n σ hσ
  have hΓ := (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ hσ).2.2.1
  have hZ : Subgroup.center ↥(twH K n) = ⊥ := TwE6Delta.center_recipeH_eq_bot hn hK
  set T : ↥(graphFixedRootGroup TwistTag.E6 K σ) ≃* ↥(twH K n) :=
    (MulEquiv.subgroupCongr hΓ.symm).trans T₀ with hTdef
  have hT : ∀ g : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      ((T g : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
          Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
        e ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) :=
    fun g => hT₀ _
  obtain ⟨x, rfl⟩ := recipeI_subset_range T hZ e hT he hφ
  obtain ⟨x₂, rfl⟩ := recipeI_subset_range T hZ e hT he hφ₂
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hx₂ : (x₂ : ModGL TwistTag.E6.tag K) ∉ graphFixedRootGroup TwistTag.E6 K σ := fun hmem =>
    hn₂ ⟨_, (recipeKappa_of_mem T hZ ⟨_, hmem⟩ x₂.2).symm⟩
  obtain ⟨k, hk⟩ := exists_mul_inv_pow_mem_graphFixedRootGroup hq hK hσ x.2 x₂.2 hx₂
  refine ⟨k, ?_⟩
  rw [← map_pow, ← map_inv, ← map_mul]
  exact ⟨_, (recipeKappa_of_mem T hZ ⟨_, hk⟩ (x * (x₂ ^ k)⁻¹).2).symm⟩

theorem recipe_inn_index [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {Y : Subgroup (MulAut (TwE6Delta.RecipeR K n))}
    (hYI : (Y : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n) :
    Nat.card Y ≤ 3 * Nat.card (Y ⊓
      (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range :
      Subgroup (MulAut (TwE6Delta.RecipeR K n))) := by
  haveI := TwE6Delta.finite_mulAut_recipeR hK
  by_cases hYN : Y ≤
      (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range
  · rw [inf_eq_left.2 hYN]
    omega
  · obtain ⟨y₂, hy₂, hy₂n⟩ := SetLike.not_le_iff_exists.1 hYN
    exact card_le_three_mul_inf hy₂ (TwE6Delta.pow_three_mem_inn hn hK (hYI hy₂))
      (fun y hy => recipe_cyc hn hK (hYI hy) (hYI hy₂) hy₂n)

end MLevel

end CFSG.StandardType.TwE6D3
