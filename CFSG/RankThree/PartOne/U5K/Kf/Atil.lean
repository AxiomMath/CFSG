module

public import CFSG.RankThree.PartOne.U5K.Kf.Comb
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.U5K.Kf.Frame

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ} [Fact p.Prime]

theorem ZetaData.dgU_zero (Z : ZetaData h p) : Z.dgU 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [ZetaData.dgU_val, Subgroup.coe_one, Units.val_one, ← diagonal_one]
  congr 1
  funext s
  exact zp_zero Z.ζ

@[expose] noncomputable def ZetaData.parHom (Z : ZetaData h p)
    (P : primeFormUnitary h (idGram K 5)) : VM p →* MulAut (primeFormP h (idGram K 5)) where
  toFun a := Z.par P (Multiplicative.toAdd a)
  map_one' := by
    show Z.par P 0 = 1
    unfold ZetaData.par ZetaData.Y
    rw [Z.dgU_zero]
    simp
  map_mul' a b := by
    show Z.par P (Multiplicative.toAdd a + Multiplicative.toAdd b) = _
    exact Z.par_add P _ _

theorem ZetaData.ker_parHom (Z : ZetaData h p) (P : primeFormUnitary h (idGram K 5)) :
    (Z.parHom P).ker = constSub p := by
  ext a
  rw [MonoidHom.mem_ker]
  change Z.par P (Multiplicative.toAdd a) = 1 ↔ _
  rw [Z.par_eq_one_iff]
  rfl

@[expose] noncomputable def ZetaData.Atil (Z : ZetaData h p) (P : primeFormUnitary h (idGram K 5))
    (Ab : Subgroup (MulAut (primeFormP h (idGram K 5)))) : Subgroup (VM p) :=
  Ab.comap (Z.parHom P)

theorem ZetaData.mem_Atil (Z : ZetaData h p) (P : primeFormUnitary h (idGram K 5))
    (Ab : Subgroup (MulAut (primeFormP h (idGram K 5)))) (a : Fin 5 → ZMod p) :
    Multiplicative.ofAdd a ∈ Z.Atil P Ab ↔ Z.par P a ∈ Ab := Iff.rfl

theorem ZetaData.le_range_parHom (Z : ZetaData h p) (P : primeFormUnitary h (idGram K 5))
    {Ab : Subgroup (MulAut (primeFormP h (idGram K 5)))} (hel : IsElementaryAbelian p ↥Ab)
    (hD : Ab ≤ primeFormD h (idGram K 5))
    (hP : ∀ x : primeFormUnitary h (idGram K 5), primeFormConjHom h (idGram K 5) x ∈ Ab →
      (((P⁻¹ * x * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K).IsDiag) :
    Ab ≤ (Z.parHom P).range := by
  intro α hα
  obtain ⟨x, rfl⟩ := hD hα
  have hdiag := hP x hα
  obtain ⟨a, ha⟩ := Z.exists_par_eq P x _ (Matrix.IsDiag.diagonal_diag hdiag).symm
    (CFSG.elemPow_eq_one_of_isElementaryAbelian _ hα)
  exact ⟨Multiplicative.ofAdd a, ha.symm⟩

theorem ZetaData.card_Atil (Z : ZetaData h p) (P : primeFormUnitary h (idGram K 5))
    {Ab : Subgroup (MulAut (primeFormP h (idGram K 5)))} (hel : IsElementaryAbelian p ↥Ab)
    (hD : Ab ≤ primeFormD h (idGram K 5))
    (hP : ∀ x : primeFormUnitary h (idGram K 5), primeFormConjHom h (idGram K 5) x ∈ Ab →
      (((P⁻¹ * x * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K).IsDiag) :
    Nat.card (Z.Atil P Ab) = Nat.card Ab * p := by
  unfold ZetaData.Atil
  rw [card_comap_eq _ _ (Z.le_range_parHom P hel hD hP), Z.ker_parHom, card_constSub]

end CFSG.RankThree.PartOne.U5K.Kf
