module

public import CFSG.Monster.GMS.S365Normal
public import CFSG.Monster.GMS.S365One
public import CFSG.Monster.GMS.S365Three

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

@[expose] def EightGroupLinesFour {G : Type*} [Group G] (a z₀ : G) : Prop :=
  ∀ x y t x' y' t' : G, IsLineTriple a x y → IsEightExt x y t → IsLineTriple a x' y' →
    IsEightExt x' y' t' → twoBCount z₀ x y t = 4 → twoBCount z₀ x' y' t' = 4 →
      ∃ g : G, g * x * g⁻¹ = x' ∧ g * y * g⁻¹ = y' ∧
        g * t * g⁻¹ ∈ ({t', t' * x', t' * y', t' * x' * y'} : Set G)

namespace S365

variable {G : Type} [Group G] {d₀ : B} {a z₀ : G}

theorem mem_leechQ_conj_iff' {w w' g₀ : G} (hg₀ : g₀ * w * g₀⁻¹ = w') (x : G) :
    g₀ * x * g₀⁻¹ ∈ leechQ w' ↔ x ∈ leechQ w := by
  rw [← hg₀, mem_leechQ_conj_iff, show g₀⁻¹ * (g₀ * x * g₀⁻¹) * g₀ = x by group]

theorem conj_comm {g₀ x w : G} (h : x * w = w * x) :
    g₀ * x * g₀⁻¹ * (g₀ * w * g₀⁻¹) = g₀ * w * g₀⁻¹ * (g₀ * x * g₀⁻¹) := by
  calc g₀ * x * g₀⁻¹ * (g₀ * w * g₀⁻¹) = g₀ * (x * w) * g₀⁻¹ := by group
    _ = g₀ * (w * x) * g₀⁻¹ := by rw [h]
    _ = g₀ * w * g₀⁻¹ * (g₀ * x * g₀⁻¹) := by group

theorem conj_of_pivot {x y t x' y' t' w w' g₀ h : G} (hK : IsKlein x y) (hK' : IsKlein x' y')
    (hw : w ∈ cosetSet x y t) (hw' : w' ∈ cosetSet x' y' t') (hg₀ : g₀ * w * g₀⁻¹ = w')
    (hh : h ∈ Subgroup.centralizer ({w'} : Set G)) (hx : h * (g₀ * x * g₀⁻¹) * h⁻¹ = x')
    (hy : h * (g₀ * y * g₀⁻¹) * h⁻¹ = y') :
    ∃ g : G, g * x * g⁻¹ = x' ∧ g * y * g⁻¹ = y' ∧
      g * t * g⁻¹ ∈ ({t', t' * x', t' * y', t' * x' * y'} : Set G) := by
  have hhw : h * w' * h⁻¹ = w' := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hh
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  refine ⟨h * g₀, ?_, ?_, ?_⟩
  · rw [← hx]
    group
  · rw [← hy]
    group
  · refine conj_mem_cosetSet_of_conj hK hK' hw hw' (g := h * g₀) ?_ ?_ ?_
    · calc h * g₀ * w * (h * g₀)⁻¹ = h * (g₀ * w * g₀⁻¹) * h⁻¹ := by group
        _ = w' := by rw [hg₀, hhw]
    · rw [← hx]
      group
    · rw [← hy]
      group

theorem eightGroupLines_of_four
    [Finite G] (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hFour : EightGroupLinesFour a z₀) : EightGroupLines a z₀ := by
  refine ⟨twoBCount_cases I hG, ?_⟩
  intro x y t x' y' t' hl he hl' he' hc
  have hK := isKlein_of_isLineTriple hG.1.1 hl
  have hK' := isKlein_of_isLineTriple hG.1.1 hl'
  rcases twoBCount_cases I hG x y t hl he with h1 | h3 | h4
  · have h1' : twoBCount z₀ x' y' t' = 1 := by rw [← hc]; exact h1
    obtain ⟨w, hw, hwc, hxw, hyw, hxQ, hyQ⟩ := exists_pivot_one I hG hl he h1
    obtain ⟨w', hw', hwc', hxw', hyw', hxQ', hyQ'⟩ := exists_pivot_one I hG hl' he' h1'
    obtain ⟨g₀, hg₀⟩ := isConj_iff.1 (hw.symm.trans hw')
    obtain ⟨h, hh, hhx, hhy⟩ := exists_conj_one I hG hw' (isLineTriple_conj hl g₀) hl'
      ((mem_leechQ_conj_iff' hg₀ x).2 hxQ) ((mem_leechQ_conj_iff' hg₀ y).2 hyQ) hxQ' hyQ'
    exact conj_of_pivot hK hK' hwc hwc' hg₀ hh hhx hhy
  · have h3' : twoBCount z₀ x' y' t' = 3 := by rw [← hc]; exact h3
    obtain ⟨w, hw, hwc, hxw, hyw, hxQ, hyQ⟩ := exists_pivot_three I hG hl he h3
    obtain ⟨w', hw', hwc', hxw', hyw', hxQ', hyQ'⟩ := exists_pivot_three I hG hl' he' h3'
    obtain ⟨g₀, hg₀⟩ := isConj_iff.1 (hw.symm.trans hw')
    have hy₁C : g₀ * y * g₀⁻¹ ∈ Subgroup.centralizer ({w'} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hg₀]
      exact conj_comm hyw
    have hy'C : y' ∈ Subgroup.centralizer ({w'} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hyw'
    have hxy₁ : g₀ * x * g₀⁻¹ * (g₀ * y * g₀⁻¹) = g₀ * y * g₀⁻¹ * (g₀ * x * g₀⁻¹) := by
      calc g₀ * x * g₀⁻¹ * (g₀ * y * g₀⁻¹) = g₀ * (x * y) * g₀⁻¹ := by group
        _ = g₀ * (y * x) * g₀⁻¹ := by rw [hK.comm]
        _ = g₀ * y * g₀⁻¹ * (g₀ * x * g₀⁻¹) := by group
    obtain ⟨h, hh, hhx, hhy⟩ := exists_conj_three I hG co1RootTransitive hw'
      (isLineTriple_conj hl g₀) hl' ((mem_leechQ_conj_iff' hg₀ x).2 hxQ) hy₁C
      (fun hq => hyQ ((mem_leechQ_conj_iff' hg₀ y).1 hq)) hxy₁ hxQ' hy'C hyQ' hK'.comm
    exact conj_of_pivot hK hK' hwc hwc' hg₀ hh hhx hhy
  · have h4' : twoBCount z₀ x' y' t' = 4 := by rw [← hc]; exact h4
    exact hFour x y t x' y' t' hl he hl' he' h4 h4'

end S365

end CFSG.Monster.GMS
