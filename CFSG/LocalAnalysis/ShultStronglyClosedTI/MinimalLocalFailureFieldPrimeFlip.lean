module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeSetup

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

universe u

variable {G : Type u} [Group G]

theorem rightPairFlipFiber_swap [Finite G] {H : Subgroup G} {z : G} (hz : orderOf z = 2)
    {beta : rightCosetSpace H} {s : G} (hs : s ∈ rightPairFlipFiber H z beta) :
    rightCosetTranslate H beta s = rightCosetMk H 1 := by
  have hss : s * s = 1 :=
    mul_self_eq_one_of_orderOf_eq_two (order_two_of_mem_pointClass hz hs.1)
  rw [← hs.2, rightCosetTranslate_mul, hss, rightCosetTranslate_one]

theorem rightPairFlipFiber_not_mem {H : Subgroup G} {z : G} {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) {s : G} (hs : s ∈ rightPairFlipFiber H z beta) :
    s ∉ H := by
  intro hsH
  apply hbeta
  rw [← hs.2]
  exact (translate_base_iff H s).mpr hsH

theorem exists_centralizing_flip [Finite G] {H : Subgroup G} {z : G} (hz : orderOf z = 2)
    {beta : rightCosetSpace H} {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    {X : Subgroup G} (hfiber : rightPairFlipFiber H z beta = (fun x => t * x) '' (X : Set G))
    {y : G} (hyB : y ∈ pairPointStabilizer H beta) {p : ℕ} (hyp : y ^ p = 1)
    (hH1 : ∀ c ∈ X, (y * c) ^ p = 1 → ∃ x ∈ X, x⁻¹ * (y * c) * x = y) :
    ∃ ty ∈ (fun x => t * x) '' (X : Set G), Commute ty y ∧
      ty ∈ rightPairFlipFiber H z beta ∧ rightCosetTranslate H beta ty = rightCosetMk H 1 := by
  have hmem : y⁻¹ * t * y ∈ (fun x => t * x) '' (X : Set G) := by
    rw [← hfiber]
    exact conj_mem_rightPairFlipFiber ht hyB
  obtain ⟨d, hdX, hd⟩ := hmem
  have hd' : t * d = y⁻¹ * t * y := hd
  have hconj : t⁻¹ * y * t = y * d⁻¹ := by
    have hdt : d = t⁻¹ * (y⁻¹ * t * y) := by rw [← hd']; group
    rw [hdt]
    group
  have hpow : (y * d⁻¹) ^ p = 1 := by
    rw [← hconj, show t⁻¹ * y * t = t⁻¹ * y * t⁻¹⁻¹ by rw [inv_inv], conj_pow, hyp, mul_one,
      mul_inv_cancel]
  obtain ⟨x, hxX, hx⟩ := hH1 d⁻¹ (X.inv_mem hdX) hpow
  have hty : t * x ∈ rightPairFlipFiber H z beta := by
    rw [hfiber]
    exact ⟨x, hxX, rfl⟩
  refine ⟨t * x, ⟨x, hxX, rfl⟩, ?_, hty, rightPairFlipFiber_swap hz hty⟩
  have hcent : (t * x)⁻¹ * y * (t * x) = y :=
    calc (t * x)⁻¹ * y * (t * x) = x⁻¹ * (t⁻¹ * y * t) * x := by group
      _ = x⁻¹ * (y * d⁻¹) * x := by rw [hconj]
      _ = y := hx
  change t * x * y = y * (t * x)
  calc t * x * y = (t * x) * ((t * x)⁻¹ * y * (t * x)) := by rw [hcent]
    _ = y * (t * x) := by group

theorem centralizer_lt_top_and_escape (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {H : Subgroup G} {y w : G} (hy : y ≠ 1)
    (hw : Commute w y) (hwH : w ∉ H) :
    Subgroup.centralizer ({y} : Set G) < ⊤ ∧ ¬ Subgroup.centralizer ({y} : Set G) ≤ H := by
  refine ⟨lt_top_iff_ne_top.mpr ?_,
    fun hle => hwH (hle (Subgroup.mem_centralizer_singleton_iff.mpr hw.eq))⟩
  intro htop
  have hcenter : y ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    have hg : g ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [htop]
      exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (self := hsimple) (Subgroup.center G)
    with hbot | htop'
  · rw [hbot, Subgroup.mem_bot] at hcenter
    exact hy hcenter
  · obtain ⟨a, b, hab⟩ := hnonab
    have hb : b ∈ Subgroup.center G := by
      rw [htop']
      exact Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
