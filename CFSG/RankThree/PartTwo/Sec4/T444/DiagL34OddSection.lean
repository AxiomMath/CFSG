module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagL34OddSL3
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec4.L34Odd

open CFSG.GorensteinWalter

theorem not_hasSection_of_le_range_toPGL {K : Type*} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (X : Subgroup (Matrix.ProjGenLinGroup (Fin 3) K))
    (hX : X ≤ (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K).range)
    {L : Type*} [Group L] (E : Subgroup L) (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE : 8 < Nat.card E) :
    ¬ HasSection X L := by
  rintro ⟨A, N, hN, ⟨φ⟩⟩
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  let H : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
    X.comap (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K)
  let f : H →* X := ((Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K).comp
      H.subtype).codRestrict X (fun h => h.2)
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg⟩ := hX hx
    exact ⟨⟨g, show (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K) g ∈ X by
        rw [hg]; exact hx⟩, Subtype.ext hg⟩
  have h0 : TwoQuot 2 L E := TwoQuot.of_isPGroup E (isPGroup_two_of_sq_eq_one E hE2)
  have h1 : TwoQuot 2 (A ⧸ N) E := TwoQuot.of_surjective φ.toMonoidHom φ.surjective h0
  have h2 : TwoQuot 2 A E :=
    TwoQuot.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) h1
  have h3 : TwoQuot 2 X E := TwoQuot.of_subgroup A h2
  have h4 : TwoQuot 2 H E := TwoQuot.of_surjective f hf h3
  obtain ⟨S, hS, ρ, hρ⟩ := h4
  have hτ : Function.Injective (H.subtype.comp S.subtype) :=
    H.subtype_injective.comp S.subtype_injective
  obtain ⟨B, hBc, hBi, hB2⟩ := gl2Type_of_injective_sl3 hK hS (H.subtype.comp S.subtype) hτ
  have hEsq : ∀ x : E, x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hE2 x x.2)
  have := card_le_eight_of_quotient B hBc hBi hB2 hEsq ρ hρ
  omega

end CFSG.RankThree.PartTwo.Sec4.L34Odd

end
