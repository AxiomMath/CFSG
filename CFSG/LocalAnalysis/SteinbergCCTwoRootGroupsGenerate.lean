module

public import CFSG.LocalAnalysis.SteinbergCCConjugateRootGroupDatum
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Data.Set.Card

public section

namespace CFSG.LocalAnalysis

namespace TwoRootGroups

variable {G Ω : Type*} [Group G] [MulAction G Ω] {U : Ω → Subgroup G}

theorem exists_root_mem_smul (hD : IsFiniteConjugateRootGroupDatum G Ω U) {x y z : Ω}
    (hy : y ≠ x) (hz : z ≠ x) : ∃ u ∈ U x, u • y = z := by
  obtain ⟨u, hu, -⟩ := hD.regular x y z hy hz
  exact ⟨u, u.2, hu⟩

theorem conj_mem (hD : IsFiniteConjugateRootGroupDatum G Ω U) (g : G) {x : Ω} {u : G}
    (hu : u ∈ U x) : g * u * g⁻¹ ∈ U (g • x) := by
  rw [← hD.conj g x]
  exact ⟨u, hu, rfl⟩

theorem root_le_of_transitive (hD : IsFiniteConjugateRootGroupDatum G Ω U) {L : Subgroup G}
    {a : Ω} (haL : U a ≤ L) (htr : ∀ x : Ω, ∃ l ∈ L, l • a = x) (x : Ω) : U x ≤ L := by
  obtain ⟨l, hl, rfl⟩ := htr x
  intro v hv
  have h1 : l⁻¹ * v * l⁻¹⁻¹ ∈ U (l⁻¹ • l • a) := conj_mem hD l⁻¹ hv
  rw [inv_smul_smul, inv_inv] at h1
  have h2 : l * (l⁻¹ * v * l) * l⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem hl (haL h1)) (L.inv_mem hl)
  simpa [mul_assoc] using h2

end TwoRootGroups

open TwoRootGroups in
theorem two_root_groups_generate_normal_subgroup {G Ω : Type*} [Group G] [MulAction G Ω]
    {U : Ω → Subgroup G} (hD : IsFiniteConjugateRootGroupDatum G Ω U) {a b : Ω} (hab : a ≠ b) :
    U a ⊔ U b = ⨆ x, U x ∧ (U a ⊔ U b).Normal ∧
      (∀ x y x' y' : Ω, x ≠ y → x' ≠ y' →
        ∃ l ∈ U a ⊔ U b, l • x = x' ∧ l • y = y') ∧
      (∀ g : G, ∃ l ∈ U a ⊔ U b, ∃ s ∈ rootPointStabilizer G a, g = l * s) ∧
      (IsSimpleGroup G → U a ⊔ U b = ⊤) := by
  set L := U a ⊔ U b with hL
  have haL : U a ≤ L := le_sup_left
  have hbL : U b ≤ L := le_sup_right
  have hfin := hD.finite_set
  have h3 := hD.three_le_card
  obtain ⟨c, hca, hcb⟩ : ∃ c : Ω, c ≠ a ∧ c ≠ b := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set Ω) ⊆ {a, b} := fun x _ => by
      by_cases hxa : x = a
      · exact Or.inl hxa
      · exact Or.inr (hcon x hxa)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ] at this
    have h2 := Set.ncard_pair hab
    omega
  have htr : ∀ x : Ω, ∃ l ∈ L, l • a = x := by
    intro x
    by_cases hxa : x = a
    · exact ⟨1, L.one_mem, by rw [one_smul, hxa]⟩
    obtain ⟨v, hv, hva⟩ := exists_root_mem_smul hD hab hcb
    obtain ⟨u, hu, huc⟩ := exists_root_mem_smul hD hca hxa
    exact ⟨u * v, L.mul_mem (haL hu) (hbL hv), by rw [mul_smul, hva, huc]⟩
  have hroot : ∀ x, U x ≤ L := root_le_of_transitive hD haL htr
  have hiSup : L = ⨆ x, U x :=
    le_antisymm (sup_le (le_iSup U a) (le_iSup U b)) (iSup_le hroot)
  have hLn : L.Normal := ⟨fun n hn g => by
    have hmap : L.map (MulAut.conj g).toMonoidHom ≤ L := by
      rw [hL, Subgroup.map_sup, hD.conj g a, hD.conj g b]
      exact sup_le (hroot _) (hroot _)
    exact hmap ⟨n, hn, rfl⟩⟩
  refine ⟨hiSup, hLn, ?_, ?_, ?_⟩
  ·
    have hpair : ∀ x y : Ω, x ≠ y → ∀ y' : Ω, y' ≠ a →
        ∃ l ∈ L, l • x = a ∧ l • y = y' := by
      intro x y hxy y' hy'
      obtain ⟨l₁, hl₁, hl₁a⟩ := htr x
      have hya : l₁⁻¹ • y ≠ a := by
        intro h
        apply hxy
        rw [← hl₁a, ← h, smul_inv_smul]
      obtain ⟨u, hu, huy⟩ := exists_root_mem_smul hD hya hy'
      refine ⟨u * l₁⁻¹, L.mul_mem (haL hu) (L.inv_mem hl₁), ?_, ?_⟩
      · rw [mul_smul, ← hl₁a, inv_smul_smul]
        exact hD.fixes a u hu
      · rw [mul_smul, huy]
    intro x y x' y' hxy hxy'
    obtain ⟨l₂, hl₂, hl₂a⟩ := htr x'
    have hy'a : l₂⁻¹ • y' ≠ a := by
      intro h
      apply hxy'
      rw [← hl₂a, ← h, smul_inv_smul]
    obtain ⟨l, hl, hlx, hly⟩ := hpair x y hxy _ hy'a
    refine ⟨l₂ * l, L.mul_mem hl₂ hl, ?_, ?_⟩
    · rw [mul_smul, hlx, hl₂a]
    · rw [mul_smul, hly, smul_inv_smul]
  ·
    intro g
    obtain ⟨l, hl, hla⟩ := htr (g • a)
    refine ⟨l, hl, l⁻¹ * g, ?_, by rw [mul_inv_cancel_left]⟩
    rw [mem_rootPointStabilizer_iff, mul_smul, ← hla, inv_smul_smul]
  ·
    intro hsimple
    rcases hLn.eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨u, hu, hub⟩ := exists_root_mem_smul hD hab.symm hca
      have hu1 : u = 1 := by
        have hmem : u ∈ L := haL hu
        rw [h] at hmem
        exact Subgroup.mem_bot.mp hmem
      rw [hu1, one_smul] at hub
      exact hcb hub.symm
    · exact h

end CFSG.LocalAnalysis
