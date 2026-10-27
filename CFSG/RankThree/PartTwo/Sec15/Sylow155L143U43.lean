module

public import CFSG.Open.PGLModelDefs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143Abs
import CFSG.RankThree.PartTwo.Sec15.Sylow155L143RowCrit
import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofE81U43
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Check

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

open CFSG.RankThree.PartTwo.Sec4.Item434RemU43
open CFSG.RankThree.PartTwo.Sec6.Res611Res4
open CFSG.PGLModel (projSU)

private theorem conj_mem_R (d : U43.Data) (hsyl : uSylCheck = true) {s r : SUg} (hs : s ∈ sylS)
    (hr : r ∈ d.R) : s * r * s⁻¹ ∈ d.R := by
  have hB : d.R.map (MulAut.conj s).toMonoidHom = d.R := by
    refine d.eq_R_of_le hsyl ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact sylS.mul_mem (sylS.mul_mem hs (d.hRS hx)) (sylS.inv_mem hs)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, d.R_comm hx hy]
    · exact ((Subgroup.card_map_of_injective (MulAut.conj s).injective).trans d.card_R).ge
  have hmem : s * r * s⁻¹ ∈ d.R.map (MulAut.conj s).toMonoidHom :=
    ⟨r, hr, by simp [MulAut.conj_apply]⟩
  rwa [hB] at hmem

private theorem l143Rows_UX (d : U43.Data) (hsyl : uSylCheck = true) : L143Rows UX := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine L143Rows.of_normal (Sylow.ofCard sylX (card_sylX hsyl)) (d.R.map piU) ?_ ?_ ?_ ?_
  · intro g hg a ha
    obtain ⟨s, hs, rfl⟩ : g ∈ sylS.map piU := hg
    obtain ⟨r, hr, rfl⟩ := ha
    exact ⟨s * r * s⁻¹, conj_mem_R d hsyl hs hr, by simp [map_mul, map_inv]⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, d.R_comm hx hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, d.hRe.2 x hx, map_one]
  · exact ((card_map_piU_of_le hsyl d.hRS).trans d.card_R).ge

theorem l143Rows_U43 :
    L143Rows (projSU 4 3 1) :=
  L143Rows.of_mulEquiv projSUEquivUX
    (l143Rows_UX (U43.data uSylCheck_true (uClassCheck_parts uClassCheck_true).1) uSylCheck_true)

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143
