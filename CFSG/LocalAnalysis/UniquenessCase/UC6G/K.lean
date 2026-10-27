module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6K

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem hr : m.r.Prime := m.d.prime

theorem Z_le_K : m.Z ≤ m.K := fun z hz =>
  subset_closure ⟨1, m.M.one_mem, z, hz, by simp⟩

theorem Z_le_M : m.Z ≤ m.M := fun z hz => m.R_le_M (m.hZ.le hz)

theorem K_le_M : m.K ≤ m.M := by
  refine (closure_le _).2 ?_
  rintro _ ⟨g, hg, z, hz, rfl⟩
  exact m.M.mul_mem (m.M.mul_mem hg (m.Z_le_M hz)) (m.M.inv_mem hg)

theorem card_Z : Nat.card m.Z = m.r := m.hZ.card

theorem Z_ne_bot : m.Z ≠ ⊥ := by
  intro h
  have : m.r = 1 := by rw [← m.card_Z, h]; exact Subgroup.card_bot
  exact m.hr.ne_one this

theorem pow_r_eq_one_of_mem {x : G} (hx : x ∈ {x | ∃ g ∈ m.M, ∃ z ∈ m.Z, x = g * z * g⁻¹}) :
    x ^ m.r = 1 := by
  obtain ⟨g, -, z, hz, rfl⟩ := hx
  have h1 : (⟨z, hz⟩ : m.Z) ^ Nat.card m.Z = 1 := pow_card_eq_one'
  have h2 : z ^ m.r = 1 := by
    have := congrArg Subtype.val h1
    rw [m.card_Z] at this
    simpa using this
  rw [conj_pow, h2]
  simp

theorem K_no_pgroup_quotient (h629 : m.C629) {q : ℕ} (hq : q.Prime) (N : Subgroup ↥m.K)
    [N.Normal] (hN : IsPGroup q (↥m.K ⧸ N)) : N = ⊤ := by
  refine no_pgroup_quotient_of_generated_by_r_elements m.hr (S := (((↑) : m.K → G)) ⁻¹'
    {x | ∃ g ∈ m.M, ∃ z ∈ m.Z, x = g * z * g⁻¹}) ?_ ?_ h629.1 h629.2 hq N hN
  · exact Subgroup.closure_closure_coe_preimage
  · intro s hs
    apply Subtype.ext
    simpa using m.pow_r_eq_one_of_mem hs

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
