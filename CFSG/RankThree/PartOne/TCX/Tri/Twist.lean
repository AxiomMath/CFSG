module

public import CFSG.RankThree.PartOne.KE.E6TwFourFamily

public section

namespace CFSG.RankThree.PartOne.TCX

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.KE

section Twist

variable {τ : Tag} {L : Type} [Field L]

@[expose] noncomputable def twPhi (Q : ModGL τ L) (Fr : L →+* L) : ModGL τ L →* ModGL τ L :=
  (MulAut.conj Q).toMonoidHom.comp (Units.map (entrywiseHom Fr))

theorem twPhi_apply (Q : ModGL τ L) (Fr : L →+* L) (u : ModGL τ L) :
    twPhi Q Fr u = Q * Units.map (entrywiseHom Fr) u * Q⁻¹ := by
  simp [twPhi, MulAut.conj_apply]

theorem mem_twistedFixedPoints_twPhi_iff (N Q : ModGL τ L) (Fr : L →+* L) (u : ModGL τ L) :
    u ∈ twistedFixedPoints N (twPhi Q Fr) ↔
      u ∈ twistedFixedPoints (N * Q) (Units.map (entrywiseHom Fr)) := by
  rw [mem_twistedFixedPoints, mem_twistedFixedPoints, twPhi_apply]
  have : (N * Q) * Units.map (entrywiseHom Fr) u * (N * Q)⁻¹ =
      N * (Q * Units.map (entrywiseHom Fr) u * Q⁻¹) * N⁻¹ := by group
  rw [this]

theorem twistedFixedPoints_twPhi (N Q : ModGL τ L) (Fr : L →+* L) :
    twistedFixedPoints N (twPhi Q Fr) =
      twistedFixedPoints (N * Q) (Units.map (entrywiseHom Fr)) :=
  Subgroup.ext (mem_twistedFixedPoints_twPhi_iff N Q Fr)


theorem twistedTorusOf_twPhi (N Q : ModGL τ L) (Fr : L →+* L) :
    twistedTorusOf N (twPhi Q Fr) =
      twistedTorusOf (N * Q) (Units.map (entrywiseHom Fr)) := by
  ext y
  rw [mem_twistedTorusOf, mem_twistedTorusOf, twPhi_apply]
  have : (N * Q) * Units.map (entrywiseHom Fr) y * (N * Q)⁻¹ =
      N * (Q * Units.map (entrywiseHom Fr) y * Q⁻¹) * N⁻¹ := by group
  rw [this]

theorem subtorusSigma_twPhi (N Q : ModGL τ L) (Fr : L →+* L) (S : Set (Fin τ.rank → ℤ)) :
    subtorusSigma N (twPhi Q Fr) S =
      subtorusSigma (N * Q) (Units.map (entrywiseHom Fr)) S := by
  unfold subtorusSigma
  rw [twistedTorusOf_twPhi]

theorem isSigmaFamilyΦ_twPhi {ι' : Type} (N Q : ModGL τ L) (Fr : L →+* L)
    (S : Set (Fin τ.rank → ℤ)) (P : ι' → Subgroup (ModGL τ L))
    (h : IsSigmaFamily (N * Q) Fr S P) : IsSigmaFamilyΦ N (twPhi Q Fr) S P := by
  unfold IsSigmaFamilyΦ
  simp only [twistedFixedPoints_twPhi, subtorusSigma_twPhi]
  exact h

end Twist

end CFSG.RankThree.PartOne.TCX
