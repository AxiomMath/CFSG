module

public import CFSG.RankThree.PartTwo.Census.QuotientWitness
public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuasisimpleCore

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

private theorem conj_mem_centralizer_aux {H : Type} [Group H] (N : Subgroup H) [N.Normal]
    (hNc : N ≤ Subgroup.center H) {t g k : H} (hg : g * t * g⁻¹ * t⁻¹ ∈ N)
    (hk : k * t = t * k) : g * k * g⁻¹ * t = t * (g * k * g⁻¹) := by
  have hw : g⁻¹ * t * g * t⁻¹ ∈ N := by
    have h1 := N.inv_mem ((inferInstance : N.Normal).conj_mem _ hg g⁻¹)
    convert h1 using 1
    group
  set w := g⁻¹ * t * g * t⁻¹ with hw_def
  have hwc := Subgroup.mem_center_iff.mp (hNc hw)
  have hcomm : k * (g⁻¹ * t * g) = (g⁻¹ * t * g) * k := by
    have e1 : g⁻¹ * t * g = w * t := by rw [hw_def]; group
    rw [e1]
    calc k * (w * t) = (k * w) * t := (mul_assoc _ _ _).symm
      _ = (w * k) * t := by rw [hwc k]
      _ = w * (k * t) := mul_assoc _ _ _
      _ = w * (t * k) := by rw [hk]
      _ = (w * t) * k := (mul_assoc _ _ _).symm
  calc g * k * g⁻¹ * t = g * (k * (g⁻¹ * t * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * t * g) * k) * g⁻¹ := by rw [hcomm]
    _ = t * (g * k * g⁻¹) := by group

theorem not_isCharTwoType_quotient_of_quasisimple {H : Type} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hNc : N ≤ Subgroup.center H) {t : H} (htN : t ∉ N)
    (ht2 : t ^ 2 ∈ N) {J : Subgroup H} (hJt : ∀ j ∈ J, j * t = t * j)
    (hJn : ∀ g : H, g * t = t * g → ∀ j ∈ J, g * j * g⁻¹ ∈ J) (hJN : J ⊓ N = ⊥)
    (hq : CFSG.Open.IsQuasisimple ↥J) : ¬ CFSG.Open.IsCharTwoType (H ⧸ N) := by
  have hpJ : Group.IsPerfect ↥J := ⟨hq.1⟩
  have hperf : ⁅J, J⁆ = J := by
    have hJtop : (⊤ : Subgroup J).map J.subtype = J := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    conv_lhs => rw [← hJtop]
    rw [← Subgroup.map_commutator, ← commutator_def, hpJ.commutator_eq_top, hJtop]
  have hJ2 : ∀ M : Subgroup H, M ≤ J → (∀ g ∈ J, ∀ m ∈ M, g * m * g⁻¹ ∈ M) →
      IsPGroup 2 M → M ≤ Subgroup.centralizer (J : Set H) := by
    intro M hMJ hMn hM2
    have hnormal : (M.subgroupOf J).Normal := ⟨fun a ha g => hMn g g.2 a ha⟩
    have hpM : IsPGroup 2 (M.subgroupOf J) := by
      intro x
      obtain ⟨k, hk⟩ := hM2 ⟨((x : J) : H), x.2⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hk
      simpa using this
    have hcenter :=
      CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_center_of_quasisimple
        hq 2 Nat.prime_two (M.subgroupOf J) hnormal hpM
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcx := hcenter (show (⟨x, hMJ hx⟩ : J) ∈ M.subgroupOf J from hx)
    have hc := Subgroup.mem_center_iff.mp hcx ⟨y, hy⟩
    exact congrArg Subtype.val hc
  refine CFSG.RankThree.PartTwo.Census.not_isCharTwoType_quotient N htN ht2
    (K := Subgroup.centralizer {t}) (J := J)
    (fun k hk => ?_) (fun g hg k hk => ?_) (fun j hj => ?_) (fun g hg j hj => ?_) hJN hperf hJ2
    (CFSG.RankThreeEvenClassification.Helpers.quasisimple_not_isPGroup ↥J hq 2 Nat.prime_two)
  · rw [Subgroup.mem_centralizer_singleton_iff] at hk
    rw [hk, mul_inv_cancel_right, mul_inv_cancel]
    exact N.one_mem
  · rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
    exact conj_mem_centralizer_aux N hNc hg hk
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact hJt j hj
  · rw [Subgroup.mem_centralizer_singleton_iff] at hg
    exact hJn g hg j hj

end CFSG.LocalAnalysis.UniqueFourCatalog
