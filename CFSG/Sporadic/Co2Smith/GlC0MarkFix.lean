module

public import CFSG.Sporadic.Co2Smith.GlC0Fix
public import CFSG.Sporadic.Co2Smith.GlC0MarkCheck

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Fix

theorem glMkFix_parts :
    Native.glMkFixIs Native.glZ 284 = true ∧
    (∀ y ∈ Native.glMkDcRows, mulRows 22 y y = idRows 22 → y ≠ idRows 22 → y ≠ Native.glZ →
      Native.glPermOK y (Native.glPermArr y) = true ∧
        (Native.glMkFixCount (Native.glPermArr y) ≠ 284 ∨ Native.glMkT.contains y = true ∨
          Native.glMkFixIs (mulRows 22 y Native.glZ) 52 = true)) ∧
    (∀ b ∈ Native.glMkDcRows, mulRows 22 b b ≠ idRows 22 →
      mulRows 22 (mulRows 22 b b) (mulRows 22 b b) = idRows 22 →
        Native.glMkFixIs (mulRows 22 b b) 140 = true) ∧
    Native.glMkA0OK = true := by
  have h := glMkFix_check
  simp only [Native.glMkFixOK, Native.glMkFixAllOK, Bool.and_eq_true, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun y hy e1 e2 e3 => ?_, fun b hb e1 e2 => ?_, h4⟩
  · rcases h2 y hy with h | h
    · simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
      rcases h with (h | h) | h
      · exact absurd e1 h
      · exact absurd e2 (by simpa using h)
      · exact absurd e3 (by simpa using h)
    · obtain ⟨hp, hc⟩ := h
      refine ⟨hp, ?_⟩
      rcases hc with (hc | hc) | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr hc)
  · rcases h3 b hb with h | h
    · simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq, beq_eq_false_iff_ne] at h
      rcases h with h | h
      · exact absurd h e1
      · exact absurd e2 h
    · exact h

theorem fixK_z0 : fixK z0 = 284 :=
  fixK_of_fixIs z0_val' glMkFix_parts.1

end Fix

end CFSG.Sporadic.Co2Smith
