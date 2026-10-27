module

public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlock
public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherSpTools
import CFSG.OddTranspositions.PartFour.SpLineCount
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsC

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther CFSG.LocalAnalysis.WeakClosure81
  CFSG.LocalAnalysis.WeakClosure81.SevenK

section SpModel

variable {k : ℕ} {F : Type} [Field F]

theorem exists_spForm_eq_zero_ne_zero {u w : Fin k ⊕ Fin k → F} (hw : w ≠ 0)
    (huw : ∀ a : F, u ≠ a • w) : ∃ x, spForm k F x w = 0 ∧ spForm k F x u ≠ 0 := by
  have hnd : ∀ y : Fin k ⊕ Fin k → F, (∀ z, spForm k F z y = 0) → y = 0 := fun y hy =>
    spForm_nondegenerate.2 y hy
  by_contra h
  push Not at h
  obtain ⟨z, hz⟩ : ∃ z, spForm k F z w ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hw (hnd w h')
  refine huw (spForm k F z u / spForm k F z w) (sub_eq_zero.mp (hnd _ fun y => ?_))
  have hy := h (y - (spForm k F y w / spForm k F z w) • z) (by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    field_simp
    ring)
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hy ⊢
  field_simp at hy ⊢
  linear_combination hy

theorem isSpCenter_of_perp {H : Subgroup (StatedSp k F)} {u u' : Fin k ⊕ Fin k → F}
    (huu' : spForm k F u u' ≠ 0) (hu : ∀ v, spForm k F v u = 0 → IsSpCenter H v)
    (hu' : ∀ v, spForm k F v u' = 0 → IsSpCenter H v) (v : Fin k ⊕ Fin k → F) :
    IsSpCenter H v := by
  by_cases h1 : spForm k F v u = 0
  · exact hu v h1
  by_cases h2 : spForm k F v u' = 0
  · exact hu' v h2
  set l := spForm k F v u' / spForm k F u u' with hl
  have hl0 : l ≠ 0 := div_ne_zero h2 huu'
  have ha : IsSpCenter H (l • u) := hu _ (by simp [spForm_isAlt u])
  have hb : IsSpCenter H (v - l • u) := hu' _ (by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hl]
    field_simp
    ring)
  have hab : spForm k F (l • u) (v - l • u) ≠ 0 := by
    simp only [map_sub, map_smul, LinearMap.smul_apply, smul_eq_mul,
      spForm_isAlt u, mul_zero, sub_zero]
    rw [← spForm_isAlt.neg_eq v u]
    exact mul_ne_zero hl0 (neg_ne_zero.mpr h1)
  have := ha.add hb hab
  rwa [add_sub_cancel] at this

theorem subset_rootBlock_and_ne_of_isSymplecticTransvection {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (h : IsSymplecticTransvection X m f s) :
    (∀ β, IsBlock E β → s ∈ β → β ⊆ rootBlock E s) ∧ rootBlock E s ≠ E := by
  classical
  obtain ⟨k, -, F, _, _, -, e, hrank⟩ := h
  set ψ : X →* StatedSp k F := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
    with hψdef
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : QuotientGroup.mk' (Subgroup.center X) a = QuotientGroup.mk' (Subgroup.center X) b :=
      e.injective hab
    rw [QuotientGroup.mk'_eq_mk'] at h1
    obtain ⟨z, hz, hzb⟩ := h1
    rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, mul_one] at hzb
    exact hzb
  have hψsurj : Function.Surjective ψ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨u, c, hu, hc, hψs⟩ := borel86_spn_eq_spTransvection hrank
  change ψ s = spTransvection u c at hψs
  have hcomm : ∀ x y : X, Commute x y ↔ Commute (ψ x) (ψ y) := fun x y =>
    ⟨fun h => h.map ψ, fun h => hψinj (by rw [map_mul, map_mul]; exact h.eq)⟩
  have hEs : ∀ x, x ∈ E ↔ IsConj s x := by
    obtain ⟨d₀, rfl⟩ := hcls
    intro x
    exact ⟨fun hx => (isConj_comm.mp hs).trans hx, fun hx => (show IsConj d₀ s from hs).trans hx⟩
  have hconjE : ∀ g x, x ∈ E → g * x * g⁻¹ ∈ E := fun g x hx =>
    (hEs _).mpr (((hEs x).mp hx).trans (isConj_iff.mpr ⟨g, rfl⟩))
  have hEtr : ∀ x ∈ E, ∃ v, v ≠ 0 ∧ ψ x = spTransvection v c := by
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp ((hEs x).mp hx)
    refine ⟨spEnd (ψ g) u, fun h0 => hu ?_, ?_⟩
    · rw [← spEnd_spEnd_inv_apply (ψ g)⁻¹ u, inv_inv, h0, map_zero]
    · rw [map_mul, map_mul, map_inv, hψs, conj_spTransvection]
  have hroot : ∀ t ∈ E, ∀ c' : F, c' ≠ 0 → ψ t = spTransvection u c' → t ∈ rootBlock E s := by
    intro t ht c' hc' htc
    refine ⟨ht, fun y hy => ?_⟩
    obtain ⟨v, -, hyv⟩ := hEtr y hy
    rw [hcomm, hcomm, hyv, htc, hψs, commute_spTransvection_iff hc hc',
      commute_spTransvection_iff hc hc]
  have hne : rootBlock E s ≠ E := by
    intro hEq
    obtain ⟨z, hz⟩ : ∃ z, spForm k F u z ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hu (spForm_nondegenerate.1 u h')
    obtain ⟨g, hg⟩ := hψsurj (spTransvection z 1)
    have hx : g * s * g⁻¹ ∈ E := hconjE g s hs
    rw [← hEq] at hx
    have h1 := (hx.2 s hs).mpr (Commute.refl s)
    rw [hcomm, map_mul, map_mul, map_inv, hψs, hg, conj_spTransvection,
      commute_spTransvection_iff hc hc, spEnd_spTransvection] at h1
    simp only [map_add, map_smul, smul_eq_mul,
      spForm_isAlt u, one_mul, zero_add] at h1
    exact mul_ne_zero hz hz h1
  refine ⟨fun β hβ hsβ t htβ => ?_, hne⟩
  have htE := hβ.1 htβ
  obtain ⟨w, hw, htw⟩ := hEtr t htE
  by_cases hprop : ∃ a : F, w = a • u
  · obtain ⟨a, rfl⟩ := hprop
    have ha : a ≠ 0 := by
      rintro rfl
      exact hw (zero_smul _ _)
    exact hroot t htE (a * a * c) (mul_ne_zero (mul_ne_zero ha ha) hc)
      (by rw [htw, spTransvection_smul_eq])
  exfalso
  push Not at hprop
  have hCN : ∀ x ∈ β, ∀ g : X, Commute g x → g ∈ Subgroup.normalizer β := by
    intro x hx g hg
    by_contra hgN
    refine Set.disjoint_left.mp (hβ.2.2.2 g hgN) hx ⟨x, hx, ?_⟩
    change g * x * g⁻¹ = x
    rw [hg.eq, mul_inv_cancel_right]
  have hNmem : ∀ g ∈ Subgroup.normalizer β, ∀ x ∈ β, g * x * g⁻¹ ∈ β := by
    intro g hg x hx
    have h1 := Subgroup.mem_normalizer_iff_conj_image_eq.mp hg
    rw [← h1]
    exact ⟨x, hx, rfl⟩
  set H : Subgroup (StatedSp k F) := (Subgroup.normalizer β).map ψ with hHdef
  have hcen : ∀ x ∈ β, ∀ v, ψ x = spTransvection v c → ∀ z, spForm k F z v = 0 →
      IsSpCenter H z := by
    intro x hx v hxv z hz t'
    obtain ⟨g, hg⟩ := hψsurj (spTransvection z t')
    refine ⟨g, hCN x hx g ?_, hg⟩
    rw [hcomm, hxv, hg]
    exact kFacts_spTransvection_comm_of_spForm_eq_zero hz t' c
  have hall : ∀ z, IsSpCenter H z := by
    by_cases huw : spForm k F u w = 0
    · have hwu : ∀ a : F, u ≠ a • w := by
        intro a hua
        have ha : a ≠ 0 := by
          rintro rfl
          exact hu (by rw [hua, zero_smul])
        exact hprop a⁻¹ (by rw [hua, smul_smul, inv_mul_cancel₀ ha, one_smul])
      obtain ⟨x, hxw, hxu⟩ := exists_spForm_eq_zero_ne_zero hw hwu
      obtain ⟨g, hgN, hg⟩ := hcen t htβ w htw x hxw 1
      have hψt' : ψ (g * s * g⁻¹) = spTransvection (spEnd (spTransvection x 1) u) c := by
        rw [map_mul, map_mul, map_inv, hg, hψs, conj_spTransvection]
      have hB : spForm k F u (spEnd (spTransvection x 1) u) ≠ 0 := by
        rw [spEnd_spTransvection]
        simp only [map_add, map_smul, smul_eq_mul, spForm_isAlt u, one_mul, zero_add]
        rw [← spForm_isAlt.neg_eq x u]
        exact mul_ne_zero (neg_ne_zero.mpr hxu) (neg_ne_zero.mpr hxu)
      exact isSpCenter_of_perp hB (hcen s hsβ u hψs) (hcen _ (hNmem g hgN s hsβ) _ hψt')
    · exact isSpCenter_of_perp huw (hcen s hsβ u hψs) (hcen t htβ w htw)
  have hHtop : H = ⊤ := eq_top_of_isSpCenter hall
  have hN : ∀ g : X, g ∈ Subgroup.normalizer β := fun g => by
    have hg : ψ g ∈ H := hHtop ▸ Subgroup.mem_top _
    obtain ⟨g', hg'N, hg'⟩ := hg
    rwa [← hψinj hg']
  refine hβ.2.2.1 (hβ.1.antisymm fun x hx => ?_)
  obtain ⟨g, rfl⟩ := isConj_iff.mp ((hEs x).mp hx)
  exact hNmem g (hN g) s hsβ

end SpModel

end CFSG.OddTranspositions.PartFour
