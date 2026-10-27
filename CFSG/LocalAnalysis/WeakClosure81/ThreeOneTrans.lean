module

public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneElems
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv

namespace ThreeOne

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {σ : Perm Ω}

private lemma exists_apply_ne_notMem {s : Finset Ω}
    (hs : s.card < (Finset.univ.filter fun x => σ x ≠ x).card) :
    ∃ r, σ r ≠ r ∧ r ∉ s := by
  obtain ⟨r, hr, hrs⟩ := Finset.exists_mem_notMem_of_card_lt_card hs
  exact ⟨r, (Finset.mem_filter.mp hr).2, hrs⟩

private lemma card_filter_apply_ne_of_forall (hfix : ∀ x, σ x ≠ x) :
    (Finset.univ.filter fun x => σ x ≠ x).card = Fintype.card Ω := by
  rw [Finset.filter_true_of_mem (fun x _ => hfix x), Finset.card_univ]

private lemma filter_apply_ne_of_fix {α : Ω} (hα : σ α = α)
    (hfix : ∀ x, x ≠ α → σ x ≠ x) :
    (Finset.univ.filter fun x => σ x ≠ x) = Finset.univ.erase α := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  exact ⟨fun hx => ⟨fun h => hx (h ▸ hα), trivial⟩, fun hx => hfix x hx.1⟩

private lemma apply_apply_eq_of_mem_centralizer {g : Perm Ω}
    (hg : g ∈ Subgroup.centralizer {σ}) (a : Ω) : g (σ a) = σ (g a) := by
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hg
  calc g (σ a) = (g * σ) a := rfl
    _ = (σ * g) a := by rw [hcomm]
    _ = σ (g a) := rfl

private lemma isMultiplyPretransitive_two_of_transitive {K : Subgroup (Perm Ω)}
    (htrans : ∀ a b : Ω, ∃ g ∈ K, g a = b)
    (hstab : ∀ a b d : Ω, b ≠ a → d ≠ a → ∃ g ∈ K, g a = a ∧ g b = d) :
    MulAction.IsMultiplyPretransitive K Ω 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨g₁, hg₁K, hg₁a⟩ := htrans a c
  have hb : g₁ b ≠ c := fun h => hab (g₁.injective (by rw [h, hg₁a]))
  obtain ⟨g₂, hg₂K, hg₂c, hg₂b⟩ := hstab c (g₁ b) d hb hcd.symm
  refine ⟨⟨g₂ * g₁, K.mul_mem hg₂K hg₁K⟩, ?_, ?_⟩
  · rw [Subgroup.smul_def, Equiv.Perm.smul_def]
    show g₂ (g₁ a) = c
    rw [hg₁a, hg₂c]
  · rw [Subgroup.smul_def, Equiv.Perm.smul_def]
    show g₂ (g₁ b) = d
    rw [hg₂b]

theorem isMultiplyPretransitive_of_not_le_centralizer (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x ≠ x) (h6 : 6 ≤ Fintype.card Ω) {H K : Subgroup (Perm Ω)}
    (hA : alternatingGroup Ω ≤ H) (hXK : H ⊓ Subgroup.centralizer {σ} ≤ K)
    (hK : ¬ K ≤ Subgroup.centralizer {σ}) : MulAction.IsMultiplyPretransitive K Ω 2 := by
  have hcard : (Finset.univ.filter fun x => σ x ≠ x).card = Fintype.card Ω :=
    card_filter_apply_ne_of_forall hfix
  have htransX : ∀ a b : Ω, ∃ g : Perm Ω, g ∈ H ⊓ Subgroup.centralizer {σ} ∧ g a = b := by
    intro a b
    have hs : ({a, σ a} : Finset Ω).card <
        (Finset.univ.filter fun x => σ x ≠ x).card := by
      rw [hcard]
      have h2 := Finset.card_le_two (a := a) (b := σ a)
      omega
    obtain ⟨r, hrσ, hr⟩ := exists_apply_ne_notMem hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    exact exists_mem_inf_apply_eq hσ hA (hfix a) (hfix b) ⟨r, hrσ, hr.1, hr.2⟩
  obtain ⟨k, hkK, hkC⟩ := Set.not_subset.mp hK
  have hkC' : ¬ k * σ = σ * k := fun h => hkC (Subgroup.mem_centralizer_singleton_iff.mpr h)
  obtain ⟨x, hx⟩ : ∃ x, k (σ x) ≠ σ (k x) := by
    by_contra h
    push Not at h
    exact hkC' (by ext y; exact h y)
  have hmoves : ∀ a : Ω, ∃ u : Perm Ω,
      u ∈ K ∧ u a = a ∧ u (σ a) ≠ a ∧ u (σ a) ≠ σ a := by
    intro a
    obtain ⟨h, hhX, hha⟩ := htransX a x
    obtain ⟨h', hh'X, hh'⟩ := htransX (k x) a
    have hhσ : h (σ a) = σ x := by
      rw [apply_apply_eq_of_mem_centralizer (Subgroup.mem_inf.mp hhX).2 a, hha]
    have hkc := (Subgroup.mem_inf.mp hh'X).2
    refine ⟨h' * k * h, K.mul_mem (K.mul_mem (hXK hh'X) hkK) (hXK hhX), ?_, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hha, hh']
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hhσ]
      intro hcon
      exact hfix x (k.injective (h'.injective (by rw [hcon, hh'])))
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hhσ]
      intro hcon
      exact hx (h'.injective (by
        rw [hcon, apply_apply_eq_of_mem_centralizer hkc (k x), hh']))
  have hstab : ∀ a b d : Ω, b ≠ a → d ≠ a →
      ∃ g : Perm Ω, g ∈ K ∧ g a = a ∧ g b = d := by
    intro a b d hba hda
    obtain ⟨u, huK, hua, huσa_a, huσa_σa⟩ := hmoves a
    have hXstab : ∀ {b' d' : Ω}, b' ≠ a → b' ≠ σ a → d' ≠ a → d' ≠ σ a →
        ∃ g : Perm Ω, g ∈ H ⊓ Subgroup.centralizer {σ} ∧ g a = a ∧ g b' = d' := by
      intro b' d' hb'a hb'σa hd'a hd'σa
      have hs : ({a, σ a, b', σ b'} : Finset Ω).card <
          (Finset.univ.filter fun x => σ x ≠ x).card := by
        rw [hcard]
        have h4 := Finset.card_le_four (a := a) (b := σ a) (c := b') (d := σ b')
        omega
      obtain ⟨r, hrσ, hr⟩ := exists_apply_ne_notMem hs
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
      exact exists_mem_inf_apply_eq_of_apply_eq hσ hA (hfix b') (hfix d') hb'a hb'σa hd'a hd'σa
        ⟨r, hrσ, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2⟩
    by_cases hbσa : b = σ a
    · by_cases hdσa : d = σ a
      · exact ⟨1, one_mem K, Equiv.Perm.one_apply a,
          by rw [hbσa, hdσa, Equiv.Perm.one_apply]⟩
      · obtain ⟨v, hvX, hva, hvb⟩ := hXstab huσa_a huσa_σa hda hdσa
        refine ⟨v * u, K.mul_mem (hXK hvX) huK, ?_, ?_⟩
        · rw [Equiv.Perm.mul_apply, hua, hva]
        · rw [Equiv.Perm.mul_apply, hbσa, hvb]
    · by_cases hdσa : d = σ a
      · obtain ⟨v, hvX, hva, hvb⟩ := hXstab hba hbσa huσa_a huσa_σa
        have hua' : u⁻¹ a = a := by
          rw [Equiv.Perm.inv_eq_iff_eq]
          exact hua.symm
        refine ⟨u⁻¹ * v, K.mul_mem (K.inv_mem huK) (hXK hvX), ?_, ?_⟩
        · rw [Equiv.Perm.mul_apply, hva, hua']
        · rw [Equiv.Perm.mul_apply, hvb, hdσa]
          simp
      · obtain ⟨v, hvX, hva, hvb⟩ := hXstab hba hbσa hda hdσa
        exact ⟨v, hXK hvX, hva, hvb⟩
  have htrans : ∀ a b : Ω, ∃ g : Perm Ω, g ∈ K ∧ g a = b := fun a b => by
    obtain ⟨g, hgX, hg⟩ := htransX a b
    exact ⟨g, hXK hgX, hg⟩
  exact isMultiplyPretransitive_two_of_transitive htrans hstab

theorem isMultiplyPretransitive_of_apply_ne (hσ : ∀ x, σ (σ x) = x) {α : Ω} (hα : σ α = α)
    (hfix : ∀ x, x ≠ α → σ x ≠ x) (h5 : 5 ≤ Fintype.card Ω) {H K : Subgroup (Perm Ω)}
    (hA : alternatingGroup Ω ≤ H) (hXK : H ⊓ Subgroup.centralizer {σ} ≤ K) {k : Perm Ω}
    (hk : k ∈ K) (hkα : k α ≠ α) : MulAction.IsMultiplyPretransitive K Ω 2 := by
  have hM : (Finset.univ.filter fun x => σ x ≠ x) = Finset.univ.erase α :=
    filter_apply_ne_of_fix hα hfix
  have hXfix : ∀ {g : Perm Ω}, g ∈ H ⊓ Subgroup.centralizer {σ} → g α = α :=
    fun hg => apply_eq_of_mem_centralizer hα hfix (Subgroup.mem_inf.mp hg).2
  have htransX : ∀ x y : Ω, x ≠ α → y ≠ α →
      ∃ g : Perm Ω, g ∈ H ⊓ Subgroup.centralizer {σ} ∧ g x = y := by
    intro x y hxα hyα
    have hs : ({x, σ x} : Finset Ω).card <
        (Finset.univ.filter fun z => σ z ≠ z).card := by
      rw [hM, Finset.card_erase_of_mem (Finset.mem_univ α), Finset.card_univ]
      have h2 := Finset.card_le_two (a := x) (b := σ x)
      omega
    obtain ⟨r, hrσ, hr⟩ := exists_apply_ne_notMem hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    exact exists_mem_inf_apply_eq hσ hA (hfix x hxα) (hfix y hyα) ⟨r, hrσ, hr.1, hr.2⟩
  have hKtrans : ∀ a b : Ω, ∃ g : Perm Ω, g ∈ K ∧ g a = b := by
    have horbit : ∀ b : Ω, ∃ g : Perm Ω, g ∈ K ∧ g α = b := by
      intro b
      by_cases hbα : b = α
      · exact ⟨1, one_mem K, by rw [hbα, Equiv.Perm.one_apply]⟩
      · obtain ⟨h, hhX, hh⟩ := htransX (k α) b hkα hbα
        exact ⟨h * k, K.mul_mem (hXK hhX) hk, by rw [Equiv.Perm.mul_apply, hh]⟩
    intro a b
    obtain ⟨ga, hgaK, hga⟩ := horbit a
    obtain ⟨gb, hgbK, hgb⟩ := horbit b
    have hga' : ga⁻¹ a = α := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hga.symm
    exact ⟨gb * ga⁻¹, K.mul_mem hgbK (K.inv_mem hgaK),
      by rw [Equiv.Perm.mul_apply, hga', hgb]⟩
  have hstab : ∀ a b d : Ω, b ≠ a → d ≠ a →
      ∃ g : Perm Ω, g ∈ K ∧ g a = a ∧ g b = d := by
    intro a b d hba hda
    by_cases haα : a = α
    · subst haα
      obtain ⟨h, hhX, hh⟩ := htransX b d hba hda
      exact ⟨h, hXK hhX, hXfix hhX, hh⟩
    · obtain ⟨g, hgK, hga⟩ := hKtrans a α
      have hga' : g⁻¹ α = a := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact hga.symm
      have hgbα : g b ≠ α := fun h => hba (g.injective (by rw [h, hga]))
      have hgdα : g d ≠ α := fun h => hda (g.injective (by rw [h, hga]))
      obtain ⟨h, hhX, hh⟩ := htransX (g b) (g d) hgbα hgdα
      refine ⟨g⁻¹ * h * g, K.mul_mem (K.mul_mem (K.inv_mem hgK) (hXK hhX)) hgK, ?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hga, hXfix hhX, hga']
      · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hh]
        simp
  exact isMultiplyPretransitive_two_of_transitive hKtrans hstab

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end
