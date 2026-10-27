module

public import CFSG.StronglyEmbedded.BenderBorelRegularRoot
public import CFSG.StronglyEmbedded.BenderUnitaryCenter
public import CFSG.StronglyEmbedded.BenderBinaryHermitian
public import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.Open

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open scoped Matrix LinearAlgebra.Projectivization

noncomputable section

theorem bender_projectiveSpecialUnitary_borel
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    fusionBenderBorel (ProjectiveSpecialUnitaryMatrixGroup J) (2 ^ f) 3 := by
  let q := 2 ^ f
  let P := ℙ K (Fin 3 → K)
  let A : Set P := {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
    x = Projectivization.mk K v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Ω := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Finite G := Finite.of_injective
    (fun x : G => (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  rcases External.huppert_II_10_12 J q hKcard hfixed hJ with
    ⟨hΩcard, rho, a, _hinj, _hnatural, _hUcard,
      ⟨R, D, hRle, hDle, hN, hinf, hsup, hcyc, hRcard,
        hcomm, hcommcard, hDcard, hreg, ⟨coord, hcoord⟩,
        _hDcoord, _hDsurj⟩, htwo, _hGcard, _hthree⟩
  let : MulAction G Ω := MulAction.compHom Ω rho
  have hstab : (MulAction.stabilizer (Equiv.Perm Ω) a).comap rho =
      MulAction.stabilizer G a := by
    ext g
    rfl
  have hRle' : R ≤ MulAction.stabilizer G a := hstab ▸ hRle
  have hDle' : D ≤ MulAction.stabilizer G a := hstab ▸ hDle
  have hN' : MulAction.stabilizer G a ≤ Subgroup.normalizer (R : Set G) :=
    hstab ▸ hN
  have hsup' : R ⊔ D = MulAction.stabilizer G a := hsup.trans hstab
  have hqpos : 0 < q := by positivity
  have hqeven : Even q := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hDodd : Odd (Nat.card D) := by
    rw [hDcard]
    have hdiv : Nat.gcd (q + 1) 3 ∣ q ^ 2 - 1 := by
      rw [show q ^ 2 - 1 = (q - 1) * (q + 1) by
        simpa [mul_comm] using Nat.sq_sub_sq q 1]
      exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (q + 1) 3) _
    exact Odd.of_dvd_nat
      (Nat.Even.sub_odd (pow_pos hqpos 2)
        (hqeven.pow_of_ne_zero (by norm_num)) odd_one)
      (Nat.div_dvd_of_dvd hdiv)
  let : MulAction.IsMultiplyPretransitive G Ω 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro b c d e hbc hde
    exact htwo b c d e hbc hde
  let : MulAction.IsPretransitive G Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hΩcard]
    exact Nat.lt_add_of_pos_left (pow_pos hqpos 3))
  have hmove : ∃ g : G, g • a ≠ a := by
    obtain ⟨b, hb⟩ := exists_ne a
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a b
    exact ⟨g, hg ▸ hb⟩
  apply fusionBenderBorel_of_regular_root a R D q 3
    hRle' hDle' hN' hinf hsup' hcyc hDodd
    (IsPGroup.of_card (n := f * 3) (by simpa only [q, ← pow_mul] using hRcard))
    (hRcard ▸ hqeven.pow_of_ne_zero (by norm_num)) hmove hreg
  · exact External.hermitianRoot_center_pow_two_of_coordinates J hJ R hcomm
      coord hcoord
  · rw [← hcomm]
    exact hcommcard
  · exact hRcard

theorem bender_psu3_borel_full (f : ℕ) (hf : 2 ≤ f) :
    fusionBenderBorel (PSU3 2 f) (2 ^ f) 3 := by
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  let : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_injective
    (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
      (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  have hB := bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ
  let e := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some
  have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  let e' := e.trans (MulEquiv.subgroupCongr hmodel)
  let : Finite (PSU3 2 f) := Finite.of_surjective e' e'.surjective
  exact hB.map_mulEquiv e'

end

end CFSG.Open
