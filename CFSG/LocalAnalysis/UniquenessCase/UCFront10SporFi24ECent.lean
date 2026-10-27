module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24ECard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi24K

open CFSG.Sporadic.Th CFSG.Sporadic.Fi24

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] rAction

theorem ne_add_one_and_two : ∀ i : Fin 24, i ≠ i + 1 ∧ i ≠ i + 2 ∧ i + 1 ≠ i + 2 := by decide

theorem exists_bbarPt_of_fix
    {q : Fin 306936}
    (hq : ∀ i : Fin 24, (bbar 0 * bbar i) • q = q) : ∃ k, bbarPt k = q :=
  Certificates.certificate10510.fixPairs q hq

section Conj

theorem bbar_smul_bbarPt (i j : Fin 24) : bbar i • bbarPt j = bbarPt j := by
  apply cls_injective
  rw [cls_smul_R]
  change bbar i * bbar j * (bbar i)⁻¹ = bbar j
  rw [bbar_comm i j, mul_inv_cancel_right]

theorem bbar_mul_bbar_eq {a b c d : Fin 24} (hab : a ≠ b) (h : bbar a * bbar b = bbar c * bbar d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  by_cases hcd : c = d
  · subst hcd
    rw [bbar_sq] at h
    have e : bbar a = bbar b :=
      calc bbar a = bbar a * (bbar b * bbar b) := by rw [bbar_sq, mul_one]
        _ = 1 * bbar b := by rw [← mul_assoc, h]
        _ = bbar b := one_mul _
    exact absurd (bbar_injective e) hab
  by_cases hac : a = c
  · subst hac
    exact Or.inl ⟨rfl, bbar_injective (mul_left_cancel h)⟩
  by_cases had : a = d
  · subst had
    rw [bbar_comm c] at h
    exact Or.inr ⟨rfl, bbar_injective (mul_left_cancel h)⟩
  by_cases hbc : b = c
  · subst hbc
    rw [bbar_comm b] at h
    exact absurd (bbar_injective (mul_right_cancel h)) had
  by_cases hbd : b = d
  · subst hbd
    exact absurd (bbar_injective (mul_right_cancel h)) hac
  exact absurd h (bbar_pair a b c d hab hcd hac had hbc hbd)

theorem exists_conj_bbar {h : R} (hc : ∀ i, h * (bbar 0 * bbar i) = bbar 0 * bbar i * h)
    (j : Fin 24) : ∃ k, h * bbar j * h⁻¹ = bbar k := by
  obtain ⟨k, hk⟩ := exists_bbarPt_of_fix (q := h • bbarPt j) fun i => by
    rw [smul_smul, ← hc, mul_smul, mul_smul, bbar_smul_bbarPt, bbar_smul_bbarPt]
  exact ⟨k, by rw [bbar, bbar, hk, cls_smul_R]⟩

theorem comm_bbar_of_comm_pairs {h : R} (hc : ∀ a b, h * (bbar a * bbar b) = bbar a * bbar b * h)
    (i : Fin 24) : h * bbar i = bbar i * h := by
  choose σ hσ using exists_conj_bbar (fun i => hc 0 i)
  have hp : ∀ a b, a ≠ b → (a = σ a ∧ b = σ b) ∨ (a = σ b ∧ b = σ a) := by
    intro a b hab
    refine bbar_mul_bbar_eq hab ?_
    rw [← hσ, ← hσ]
    calc bbar a * bbar b = h * (bbar a * bbar b) * h⁻¹ := by rw [hc, mul_inv_cancel_right]
      _ = h * bbar a * h⁻¹ * (h * bbar b * h⁻¹) := by group
  obtain ⟨h1, h2, h12⟩ := ne_add_one_and_two i
  have hi : σ i = i := by
    rcases hp i (i + 1) h1 with ⟨e, -⟩ | ⟨-, e1⟩
    · exact e.symm
    rcases hp i (i + 2) h2 with ⟨e, -⟩ | ⟨-, e2⟩
    · exact e.symm
    exact absurd (e1.trans e2.symm) h12
  have e := hσ i
  rw [hi] at e
  calc h * bbar i = h * bbar i * h⁻¹ * h := by group
    _ = bbar i * h := by rw [e]

end Conj

section Cent

theorem mem_fi24EB_of_comm_pairs {h : R}
    (hc : ∀ a b, h * (bbar a * bbar b) = bbar a * bbar b * h) : h ∈ fi24EB :=
  mem_fi24EB_of_comm (comm_bbar_of_comm_pairs hc)

theorem bbar_mul_bbar_mem_fi24E (a b : Fin 24) : ∃ e ∈ fi24E, jR e = bbar a * bbar b := by
  have hJ : bbar a * bbar b ∈ JR := by
    rw [Subgroup.mul_mem_iff_of_index_two index_JR]
    exact iff_of_false (bbar_not_mem_JR a) (bbar_not_mem_JR b)
  rw [← range_jR] at hJ
  obtain ⟨e, he⟩ := hJ
  refine ⟨e, ?_, he⟩
  rw [mem_fi24E_iff, he]
  exact mul_mem (Subgroup.subset_closure ⟨a, rfl⟩) (Subgroup.subset_closure ⟨b, rfl⟩)

theorem centralizer_fi24E : Subgroup.centralizer (fi24E : Set CFSG.Sporadic.Fi24.J) = fi24E := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg
    refine mem_fi24E_iff.2 (mem_fi24EB_of_comm_pairs fun a b => ?_)
    obtain ⟨e, heE, he⟩ := bbar_mul_bbar_mem_fi24E a b
    rw [← he, ← map_mul, ← map_mul, hg e heE]
  · intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    apply jR_injective
    rw [map_mul, map_mul]
    exact fi24EB_mul_comm hf he

end Cent

end Fi24K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
