module

public import CFSG.RankThree.GF2n.Tim79aSec23Statements

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

theorem commutator_eq_top_of_four_le (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (h4 : 4 ≤ qBar V H) : commutator (Xbar V H) = ⊤ := by
  obtain ⟨a, b, ha1, hb1, hab⟩ := exists_two_ne (α := ↥(barOf V H V)) (by
    have : 4 ≤ Nat.card (barOf V H V) := h4
    omega) 1
  have hmem : ∀ x : Hbar V H, x ∈ barOf V H V → x ≠ 1 →
      ∃ y : Xbar V H, y ∈ Dy V H ∧ (y : Hbar V H) = x :=
    fun x hx hx1 => ⟨⟨x, barOf_V_le V H hx⟩, hc.barOf_V_subset_dbarOf hx hx1, rfl⟩
  obtain ⟨a', ha'D, ha'⟩ := hmem a.1 a.2 (fun h => ha1 (Subtype.ext h))
  obtain ⟨b', hb'D, hb'⟩ := hmem b.1 b.2 (fun h => hb1 (Subtype.ext h))
  have hb2 : b.1 * b.1 = 1 := by
    have := hc.barOf_V_sq b.2
    rwa [pow_two] at this
  have hab2 : a.1 * b.1 ≠ 1 := by
    intro h
    have : b.1⁻¹ = b.1 := inv_eq_of_mul_eq_one_right hb2
    exact hab (Subtype.ext ((eq_inv_of_mul_eq_one_left h).trans this))
  obtain ⟨e', he'D, he'⟩ := hmem (a.1 * b.1) ((barOf V H V).mul_mem a.2 b.2) hab2
  have he : e' = a' * b' := by
    apply Subtype.ext
    simp [ha', hb', he']
  obtain ⟨d₀, hd₀⟩ := hd.isClass
  have hb'K : b' ∈ commutator (Xbar V H) := by
    have hconj : IsConj a' e' := by
      rw [hd₀] at ha'D he'D
      exact ha'D.symm.trans he'D
    obtain ⟨c, hc'⟩ := isConj_iff.1 hconj
    have : a'⁻¹ * e' = ⁅a'⁻¹, c⁆ := by
      rw [← hc']
      simp only [commutatorElement_def]
      group
    have hb'eq : b' = a'⁻¹ * e' := by rw [he]; group
    rw [hb'eq, this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hDK : ∀ d ∈ Dy V H, d ∈ commutator (Xbar V H) := by
    intro d hdD
    have hconj : IsConj b' d := by
      rw [hd₀] at hb'D hdD
      exact hb'D.symm.trans hdD
    obtain ⟨c, hc'⟩ := isConj_iff.1 hconj
    rw [← hc']
    have : (c * b' * c⁻¹) = ⁅c, b'⁆ * b' := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
      (Subgroup.mem_top _)) hb'K
  rw [eq_top_iff, ← hd.gen]
  exact (Subgroup.closure_le _).2 hDK

theorem centreClause_of_four_le (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (h4 : 4 ≤ qBar V H) : CentreClause V H := by
  unfold CentreClause
  rw [hc.commutator_eq_top_of_four_le hd h4]
  exact le_top

end MinCex

end CFSG.RankThree.GF2n.Tim79a
