module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExcArith
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDescent
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSQTK
public import CFSG.Quasithin.Background.JonesParshallBasic
public import CFSG.Quasithin.Background.SmithB45L2Pair
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall
open CFSG.QuasithinUnique.Setup.Layer
open scoped MatrixGroups

@[expose] def SixtyFourDescent {F : Type} [Field F] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) SL(2, F) W)
    [Fact ρ.IsIrreducible] : Prop :=
  Nat.card (EndRing ρ) = 4 ∧
    ∀ b : Module.Basis (Fin (Module.finrank (EndRing ρ) W)) (EndRing ρ) W,
      ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (ιF : F →+* E)
        (ιD : EndRing ρ →+* E) (J : Finset ℕ), (J = {0, 2, 4} ∨ J = {1, 3, 5}) ∧
        (letI := ιF.toAlgebra
         Nonempty ((matRepE b ιD).Equiv (frobTensor F E J)))

private theorem finrank_zmod2_eq_mul_card {F : Type} [Field F] [Fintype F] [CharP F 2]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible] {d : ℕ}
    (hD : Nat.card (EndRing ρ) = 2 ^ d) :
    Module.finrank (ZMod 2) W = d * Module.finrank (EndRing ρ) W := by
  have hDfin : Nat.card (EndRing ρ) =
      2 ^ Module.finrank (ZMod 2) (EndRing ρ) := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := EndRing ρ))
  have hd : Module.finrank (ZMod 2) (EndRing ρ) = d :=
    Nat.pow_right_injective (by norm_num) (hDfin.symm.trans hD)
  have hmul := Module.finrank_mul_finrank (ZMod 2) (EndRing ρ) W
  rw [hd] at hmul
  exact hmul.symm.trans (by rw [mul_comm])

theorem sixtyFourDescent_of_finrank {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hF : Fintype.card F = 2 ^ n) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) SL(2, F) W)
    [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1)
    (hdim : Module.finrank (ZMod 2) W = 2 * n + 4) : n = 6 ∧ SixtyFourDescent ρ := by
  classical
  obtain ⟨d, -, hDcard, hdesc⟩ :=
    binary_SL2_irreducible_Frobenius_descent (n := n) (by omega) hF ρ hnt
  have hfinD : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  obtain ⟨E, hE, hEfin, hEchar, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdimJ⟩ :=
    hdesc (Module.finBasis (EndRing ρ) W)
  have hw : Module.finrank (ZMod 2) W = d * 2 ^ J.card := by
    rw [finrank_zmod2_eq_mul_card ρ hDcard, hdimJ]
  have hd : d * 2 ^ J.card = 2 * n + 4 := by rw [← hw, hdim]
  obtain ⟨hn6, hd2, hJeq⟩ := exc_arith hn hJne hJn hshift hd
  refine ⟨hn6, ?_, fun b => ?_⟩
  · rw [hDcard, hd2]
    norm_num
  · obtain ⟨E', hE', hEfin', hEchar', ιF', ιD', J', hJne', hJn', ⟨Φ'⟩, hshift', hdimJ'⟩ :=
      hdesc b
    have hw' : Module.finrank (ZMod 2) W = d * 2 ^ J'.card := by
      rw [finrank_zmod2_eq_mul_card ρ hDcard, hdimJ']
    have hd' : d * 2 ^ J'.card = 2 * n + 4 := by rw [← hw', hdim]
    obtain ⟨-, -, hJeq'⟩ := exc_arith hn hJne' hJn' hshift' hd'
    exact ⟨E', hE', hEfin', hEchar', ιF', ιD', J', hJeq', ⟨Φ'⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
