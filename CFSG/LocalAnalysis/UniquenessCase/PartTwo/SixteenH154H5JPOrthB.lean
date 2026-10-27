module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.Milestones.ASVolI.I1Cohomology
import CFSG.Quasithin.Vol2.Ch5ModulesOrth
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.Quasithin.Background.JonesParshallHermitian

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Quasithin.JonesParshall
open scoped MatrixGroups Matrix

variable {W : Type} [CommGroup W]

private lemma s16jp_hermAct_twistAct {F : Type} [Field F] [CharP F 2] {a : ℕ}
    (hσ : ∀ x : F, sig a (sig a x) = x) (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (X : ↥(hermA a F)) :
    Multiplicative.ofAdd ((hermAct a hσ g X : ↥(hermA a F)) : Matrix (Fin 2) (Fin 2) F) =
      twistAct a (StatedSL 2 F)
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F g)
        (Multiplicative.ofAdd (X : Matrix (Fin 2) (Fin 2) F)) := by
  simp only [twistAct, toAdd_ofAdd, hermAct_coe,
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]

private lemma s16jp_hermEquiv_symm_coe {F : Type} [Field F] [CharP F 2] {a : ℕ}
    (X : ↥(hermA a F)) :
    ((Additive.toMul ((hermEquiv a F).symm X) : ↥(hermSub a (Fin 2) F)) :
        Multiplicative (Matrix (Fin 2) (Fin 2) F)) =
      Multiplicative.ofAdd (X : Matrix (Fin 2) (Fin 2) F) := rfl

theorem s16jp_natOmegaMinus_binaryOrthogonalFour {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    {m : ℕ} (hm : 1 ≤ m) (h : NatOmegaMinus H U Z 4 m) : BinaryOrthogonalFour H U Z m := by
  obtain ⟨-, K, hKfield, hKfin, b, c, hKcard, hirr, hR⟩ := h
  rw [show 4 / 2 = 2 by norm_num] at hR
  letI : Field K := hKfield
  letI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hKcard
  have hK' : Fintype.card K = 2 ^ m := by
    rw [Fintype.card_eq_nat_card]
    exact hKcard
  obtain ⟨F, hFfield, hFalg, ω, hrank, hω⟩ :=
    CFSG.ASVolI.burnsideI16h_exists_quad_ext (K := K) (b := b) (c := c) hirr
  letI : Field F := hFfield
  letI : Algebra K F := hFalg
  haveI : Module.Finite K F := Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  haveI : Finite F := Module.finite_of_finite K
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_injective_algebraMap (algebraMap K F).injective 2
  let S : CFSG.ASVolI.burnsideI16h_Setup K F :=
    ⟨m, b, c, hm, hK', ω, hω, hirr, hrank⟩
  have hFcard : Fintype.card F = 2 ^ (2 * m) := CFSG.ASVolI.burnsideI16h_hF S
  have hFnat : Nat.card F = 2 ^ (2 * m) := by
    rw [← Fintype.card_eq_nat_card]
    exact hFcard
  let D₁ := FFModel.nat (StatedOmega (StatedQuadMinus 2 K b c))
  let D₂ := FFModel.twistTensor m (StatedSL 2 F)
  obtain ⟨π, hπ⟩ := hR
  let e : D₂.Gam ≃* D₁.Gam :=
    ((CFSG.ASVolI.burnsideI16h_θ S).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)).symm
  let βm : Multiplicative (CFSG.ASVolI.burnsideI16h_OI → K) ≃* ↥(hermSub m (Fin 2) F) :=
    (AddEquiv.toMultiplicative (CFSG.ASVolI.burnsideI16h_β S)).trans
      (AddEquiv.toMultiplicativeLeft (hermEquiv m F).symm)
  let θs : ↥D₁.sec ≃* ↥D₂.sec := (Subgroup.topEquiv).trans βm
  have hAct : D₂.IsActionModel :=
    FFModel.twistTensor_isActionModel m (StatedSL 2 F) hFnat
  refine ⟨F, inferInstance, inferInstance, inferInstance, hFnat, ?_⟩
  refine ⟨π.comp e.toMonoidHom,
    CFSG.Quasithin.H13.OrthFour.realizesVia_transfer (D := D₂) (D' := D₁) hπ e θs
      ?_ ?_ hAct.ker_le hAct.sec_inv hAct.ker_inv ?_⟩
  · rw [show D₁.ker = (⊥ : Subgroup D₁.Amb) from rfl, Subgroup.bot_subgroupOf]
  · rw [show D₂.ker = (⊥ : Subgroup D₂.Amb) from rfl, Subgroup.bot_subgroupOf]
  · intro γ m' _
    have hθm : ∀ x : ↥D₁.sec, θs x = βm (x : D₁.Amb) := fun _ => rfl
    rw [hθm]
    apply Subtype.ext
    change (βm (D₁.act (e γ) (m' : D₁.Amb)) : Multiplicative (Matrix (Fin 2) (Fin 2) F)) =
      twistAct m (StatedSL 2 F) γ
        ((βm (m' : D₁.Amb) : ↥(hermSub m (Fin 2) F)) :
          Multiplicative (Matrix (Fin 2) (Fin 2) F))
    have hβm : ∀ x : D₁.Amb,
        ((βm x : ↥(hermSub m (Fin 2) F)) :
            Multiplicative (Matrix (Fin 2) (Fin 2) F)) =
          Multiplicative.ofAdd
            ((CFSG.ASVolI.burnsideI16h_β S (Multiplicative.toAdd x) : ↥(hermA m F)) :
              Matrix (Fin 2) (Fin 2) F) := fun x => s16jp_hermEquiv_symm_coe _
    rw [hβm, hβm]
    have hnat : Multiplicative.toAdd (D₁.act (e γ) (m' : D₁.Amb)) =
        (CFSG.ASVolI.burnsideI16h_Θ S (CFSG.ASVolI.burnsideI16h_θ S (e γ)))
          (Multiplicative.toAdd (m' : D₁.Amb)) := by
      have h1 : CFSG.ASVolI.burnsideI16h_ΘEquiv S
          (CFSG.ASVolI.burnsideI16h_θ S (e γ)) =
          CFSG.ASVolI.burnsideI16h_gammaEquiv S (e γ) :=
        (CFSG.ASVolI.burnsideI16h_ΘEquiv S).apply_symm_apply _
      have h2 : CFSG.ASVolI.burnsideI16h_Θ S (CFSG.ASVolI.burnsideI16h_θ S (e γ)) =
          CFSG.ClassicalGroups.Orthogonal.toLinEquiv CFSG.ASVolI.burnsideI16h_OI K
            (e γ).1 :=
        congrArg Subtype.val h1
      rw [h2, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
      rfl
    have hleft : CFSG.ASVolI.burnsideI16h_β S
        (Multiplicative.toAdd (D₁.act (e γ) (m' : D₁.Amb))) =
        CFSG.ASVolI.burnsideI16h_β S
          ((CFSG.ASVolI.burnsideI16h_Θ S (CFSG.ASVolI.burnsideI16h_θ S (e γ)))
            (Multiplicative.toAdd (m' : D₁.Amb))) :=
      congrArg (fun z => CFSG.ASVolI.burnsideI16h_β S z) hnat
    rw [hleft, CFSG.ASVolI.burnsideI16h_β_Θ]
    have heγ : CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F
        (CFSG.ASVolI.burnsideI16h_θ S (e γ)) = γ := by
      change ((CFSG.ASVolI.burnsideI16h_θ S).trans
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F))
          (((CFSG.ASVolI.burnsideI16h_θ S).trans
            (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)).symm γ) = γ
      exact MulEquiv.apply_symm_apply _ γ
    rw [s16jp_hermAct_twistAct (CFSG.ASVolI.burnsideI16h_hσ S)
      (CFSG.ASVolI.burnsideI16h_θ S (e γ))
      (CFSG.ASVolI.burnsideI16h_β S (Multiplicative.toAdd (m' : D₁.Amb))), heγ]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
