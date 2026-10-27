module

public import CFSG.RankThree.GF2n.Tim79Local

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement

open CFSG CFSG.CGT.Timmesfeld75 CFSG.GH74.GLS.Bg.TwoGroups

variable {G : Type} [Group G]

private theorem Hyp79.central [Finite G] {M V Q : Subgroup G}
    (H : Hyp79 M V Q) : ∀ v ∈ V, ∀ y ∈ Q, v * y = y * v := by
  obtain ⟨-, hZ, -⟩ := H.special
  intro v hv y hy
  have : v ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := hZ ▸ hv
  exact (Subgroup.mem_centralizer_iff.mp this.2 y hy).symm

theorem Hyp79.exists_noncomm [Finite G] {M V Q : Subgroup G}
    (H : Hyp79 M V Q) :
    ∃ g₁ g₂ : G, conjSubgroup g₁ V ≠ V ∧ conjSubgroup g₁ V ≤ Q ∧ conjSubgroup g₂ V ≠ V ∧
      conjSubgroup g₂ V ≤ Q ∧ ∃ a ∈ conjSubgroup g₁ V, ∃ b ∈ conjSubgroup g₂ V, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hQ', -, -⟩ := H.special
  have hVc := H.central
  have hgen : ∀ g g' : G, conjSubgroup g V ≤ Q → conjSubgroup g' V ≤ Q →
      ∀ x ∈ conjSubgroup g V, ∀ y ∈ conjSubgroup g' V, x * y = y * x := by
    intro g g' hg hg' x hx y hy
    by_cases h1 : conjSubgroup g V = V
    · rw [h1] at hx
      exact hVc x hx y (hg' hy)
    by_cases h2 : conjSubgroup g' V = V
    · rw [h2] at hy
      exact (hVc y hy x (hg hx)).symm
    exact hcon g g' h1 hg h2 hg' x hx y hy
  have hQc1 : ∀ u, (∃ g, conjSubgroup g V ≤ Q ∧ u ∈ conjSubgroup g V) →
      Q ≤ Subgroup.centralizer ({u} : Set G) := by
    rintro u ⟨g, hg, hu⟩
    refine H.gen.le.trans (iSup₂_le fun g' hg' x hx => ?_)
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact hgen g g' hg hg' u hu x hx
  have hQc2 : Q ≤ Subgroup.centralizer (Q : Set G) := by
    refine H.gen.le.trans (iSup₂_le fun g hg u hu => ?_)
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
      have := Subgroup.mem_centralizer_iff.mp (hQc1 u ⟨g, hg, hu⟩ hx) u rfl
      exact this.symm
  have hbot : ⁅Q, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hQc2
  have hV1 : V = ⊥ := by rw [← hQ', hbot]
  have h4 := H.q4
  rw [hV1, Subgroup.card_bot] at h4
  omega

theorem Hyp79.nonempty_mulEquiv_ut3_of_card [Finite G]
    {M V Q : Subgroup G} (H : Hyp79 M V Q) (hQ3 : Nat.card Q = Nat.card V ^ 3) :
    ∃ n : ℕ, Nat.card V = 2 ^ n ∧ Nonempty (↥Q ≃* UT3 (GaloisField 2 n)) := by
  obtain ⟨g₁, g₂, h₁V, h₁Q, h₂V, h₂Q, hnc⟩ := H.exists_noncomm
  obtain ⟨n₁, hn₁, ⟨D₁⟩⟩ := H.exists_mulData h₁V h₁Q
  obtain ⟨n₂, hn₂, ⟨D₂⟩⟩ := H.exists_mulData h₂V h₂Q
  have hn : n₁ = n₂ := Nat.pow_right_injective (le_refl 2) (hn₁.symm.trans hn₂)
  subst hn
  have hn0 : n₁ ≠ 0 := by
    rintro rfl
    have := H.q4
    rw [hn₁] at this
    omega
  obtain ⟨e⟩ := MulData.unitri_of_noncomm H.central h₁Q h₂Q D₁ D₂ hnc
  have hcard : Nat.card ↥(conjSubgroup g₁ V ⊔ conjSubgroup g₂ V) = Nat.card Q := by
    rw [Nat.card_congr e.toEquiv, card_ut3, GaloisField.card 2 n₁ hn0, hQ3, hn₁]
  have hsup : conjSubgroup g₁ V ⊔ conjSubgroup g₂ V = Q :=
    Subgroup.eq_of_le_of_card_ge (sup_le h₁Q h₂Q) hcard.ge
  refine ⟨n₁, hn₁, ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr hsup.symm).trans e

theorem Hyp79.isCentralProductOfL3_of_card [Finite G]
    {M V Q : Subgroup G} (H : Hyp79 M V Q) (hQ3 : Nat.card Q = Nat.card V ^ 3) :
    ∃ n : ℕ, Nat.card V = 2 ^ n ∧ IsCentralProductOfL3 Q V n 1 := by
  obtain ⟨n, hn, ⟨e⟩⟩ := H.nonempty_mulEquiv_ut3_of_card hQ3
  obtain ⟨-, hZ, -⟩ := H.special
  refine ⟨n, hn, Nat.one_pos, fun _ => Q, fun _ => le_rfl, fun _ => ⟨e⟩, fun _ => ?_,
    fun i j hij => absurd (Subsingleton.elim i j) hij, by simp⟩
  rw [← hZ]
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have := Subgroup.mem_center_iff.mp hz ⟨q, hq⟩
    exact congrArg Subtype.val this
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun q => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc q.1 q.2)

end CFSG.RankThree.GF2n.Tim79
