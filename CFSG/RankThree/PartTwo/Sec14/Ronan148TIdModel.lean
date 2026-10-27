module

import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.Adapters.RankTwoModelTransports
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG.RankThree.PartTwo.Sec4 (ModThree PiField slPi piCard)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedSL glCongr_statedSU
  glCongr_statedScalars statedProjCongr statedProjEquivProjImage)

theorem isoLThreePi_of_model {X : Type} [Group X] {π : Bool} {p f : ℕ} [Fact p.Prime]
    {F : Type} [Field F] (hF : PiField π p f F) (hq : ModThree π (p ^ f))
    (φ : X ≃* projImage (slPi π 3 (p ^ f) F)) :
    CFSG.RankThree.PartTwo.Sec4.IsoLThreePi X p f := by
  haveI : Finite F := hF.finite
  have hf : 0 < f := by
    have := hF.one_le
    omega
  unfold CFSG.RankThree.PartTwo.Sec4.IsoLThreePi
  cases π with
  | false =>
    have hK : Nat.card F = p ^ (2 * f) := by
      rw [hF.card, piCard, Bool.cond_false, ← pow_mul, mul_comm]
    let ψ : F ≃+* GaloisField p (2 * f) :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField F p (2 * f) (by omega) hK
    have e' : projImage (slPi false 3 (p ^ f) F) ≃*
        projImage (slPi false 3 (p ^ f) (GaloisField p (2 * f))) :=
      (statedProjEquivProjImage (slPi false 3 (p ^ f) F) rfl).symm.trans
        ((statedProjCongr (ι := Fin 3) (glCongr ψ) (glCongr_statedSU ψ 3 (p ^ f))
          (glCongr_statedScalars (ι := Fin 3) ψ)).trans
          (statedProjEquivProjImage _ rfl))
    exact Or.inr ⟨hq, ⟨φ.trans (e'.trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Sec4.projSU_eq_projImage p f).symm))⟩⟩
  | true =>
    have hK : Nat.card F = p ^ f := by
      rw [hF.card, piCard, Bool.cond_true]
    let ψ : F ≃+* GaloisField p f :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField F p f hf hK
    have e' : projImage (slPi true 3 (p ^ f) F) ≃*
        projImage (slPi true 3 (p ^ f) (GaloisField p f)) :=
      (statedProjEquivProjImage (slPi true 3 (p ^ f) F) rfl).symm.trans
        ((statedProjCongr (ι := Fin 3) (glCongr ψ) (glCongr_statedSL ψ 3)
          (glCongr_statedScalars (ι := Fin 3) ψ)).trans
          (statedProjEquivProjImage _ rfl))
    exact Or.inl ⟨hq, ⟨φ.trans (e'.trans
      (MulEquiv.subgroupCongr
        (CFSG.RankThree.PartTwo.Sec4.projSL_eq_projImage (p ^ f) (GaloisField p f)).symm))⟩⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
