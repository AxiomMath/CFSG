module

public import CFSG.Open.Catalog
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith
import CFSG.Models.BenderSuzuki
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.SignalizerFunctorTheorem.McBride.NearSolvable
open scoped Matrix LinearAlgebra.Projectivization

universe u

private theorem exists_sylow_card_normalizer_psu {K : Type u} [Field K] [Finite K]
    (J : HermitianForm 3 K) (n : ℕ) (hn : 2 ≤ n)
    (hKcard : Nat.card K = (2 ^ n) ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = 2 ^ n)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
    haveI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_injective (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
        (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
    ∃ S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      Nat.card (Subgroup.normalizer ((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
        Set (ProjectiveSpecialUnitaryMatrixGroup J))) =
        (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) / Nat.gcd (2 ^ n + 1) 3 := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
      (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  let q := 2 ^ n
  let P := ℙ K (Fin 3 → K)
  let A : Set P :=
    {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
      x = Projectivization.mk K v hv ∧
        dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Omega := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  rcases External.huppert_II_10_12 J q (by simpa [q] using hKcard)
      (by simpa [q] using hfixed_card) hJstandard with
    ⟨_hOmegaCard, rho, pinf, _hrho, _hnatural, hUcard, hroot, _htwo, _hGcard, _hthree⟩
  rcases hroot with
    ⟨R, H, hR_le_U, hH_le_U, hU_le_normalizer_R,
      hR_disjoint_H, hR_sup_H, _hH_cyclic, hRcard,
      _hcommutator_center, _hcommutator_card, hHcard,
      hRregular, _hcoordR, _hHcoord, _hHcoord_surjective⟩
  have hRpower : Nat.card R = 2 ^ (n * 3) := by
    simpa [q, pow_mul] using hRcard
  have hRp : IsPGroup 2 R := IsPGroup.of_card hRpower
  have hq_even : Even q := by
    dsimp [q]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hq_sq_even : Even (q ^ 2) :=
    hq_even.pow_of_ne_zero (by norm_num)
  have hq_sq_pos : 0 < q ^ 2 :=
    pow_pos (by dsimp [q]; positivity) 2
  have hq_sq_sub_one_odd : Odd (q ^ 2 - 1) :=
    Nat.Even.sub_odd hq_sq_pos hq_sq_even odd_one
  have hgcd_dvd : Nat.gcd (q + 1) 3 ∣ q ^ 2 - 1 := by
    have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq q 1
    rw [hfactor]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (q + 1) 3) _
  have hHodd : Odd (Nat.card H) := by
    rw [hHcard]
    exact Odd.of_dvd_nat hq_sq_sub_one_odd
      (Nat.div_dvd_of_dvd hgcd_dvd)
  have hHnot : ¬ 2 ∣ Nat.card H := by
    intro htwo_dvd
    exact (Nat.not_even_iff_odd.mpr hHodd)
      (even_iff_two_dvd.mpr htwo_dvd)
  obtain ⟨PU, hPU⟩ :=
    exists_sylow_map_eq_of_normal_complement
      hR_le_U hH_le_U hU_le_normalizer_R
      hR_disjoint_H hR_sup_H hRp hHnot
  let : MulAction G Omega := MulAction.compHom Omega rho
  have hR_ne : R ≠ ⊥ := by
    intro hRbot
    have hRcard_one : Nat.card R = 1 := by rw [hRbot]; simp
    have hqcube_one : q ^ 3 = 1 := hRcard.symm.trans hRcard_one
    have hq_one : q = 1 :=
      (pow_eq_one_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp hqcube_one
    have : 1 < q := by
      dsimp [q]
      exact one_lt_pow₀ (by norm_num) (by omega)
    omega
  have hnormalizer :
      Subgroup.normalizer (R : Set G) = MulAction.stabilizer G pinf :=
    normalizer_eq_stabilizer_of_regular_compl R pinf hR_le_U hR_ne
      hRregular hU_le_normalizer_R
  have hstab :
      (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho =
        MulAction.stabilizer G pinf := by
    ext g
    change (rho g) pinf = pinf ↔ (rho g) pinf = pinf
    rfl
  have hnormalizer_le :
      Subgroup.normalizer
          (((PU : Subgroup _).map
            ((MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho).subtype :
              Subgroup G) : Set G) ≤
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho := by
    rw [hPU, hstab]
    exact hnormalizer.le
  obtain ⟨S, hSmap⟩ :=
    exists_sylow_map_eq_of_normalizer_le PU hnormalizer_le
  have hSR : (S : Subgroup G) = R := hSmap.trans hPU
  refine ⟨S, ?_⟩
  rw [hSR, hnormalizer, ← hstab]
  exact hUcard

theorem card_normalizer_sylow_two_psu3 {f : ℕ} (hf : 2 ≤ f) (Q : Sylow 2 (PSU3 2 f)) :
    Nat.card (Subgroup.normalizer ((Q : Subgroup (PSU3 2 f)) : Set (PSU3 2 f))) =
      (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) / Nat.gcd (2 ^ f + 1) 3 := by
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
  obtain ⟨S, hS⟩ := exists_sylow_card_normalizer_psu J f hf hKcard hfixed hJ
  let e := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some
  have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  let e' := e.trans (MulEquiv.subgroupCongr hmodel)
  let : Finite (PSU3 2 f) := Finite.of_surjective e' e'.surjective
  let S' : Sylow 2 (PSU3 2 f) := S.mapSurjective (f := e'.toMonoidHom) e'.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSU3 2 f) S' Q
  have hmap : (S' : Subgroup (PSU3 2 f)).map (MulAut.conj g).toMonoidHom = Q := by
    change (g • S' : Sylow 2 (PSU3 2 f)).toSubgroup = Q.toSubgroup
    rw [hg]
  have hS' : (S' : Subgroup (PSU3 2 f)) = (S : Subgroup _).map e'.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  rw [← hmap, hS', ← Subgroup.map_equiv_normalizer_eq _ (MulAut.conj g),
    ← Subgroup.map_equiv_normalizer_eq _ e',
    Subgroup.card_map_of_injective (MulAut.conj g).injective,
    Subgroup.card_map_of_injective e'.injective]
  exact hS

theorem not_three_dvd_normalizer_card {q : ℕ} (h : q % 9 = 2 ∨ q % 9 = 5) :
    ¬ 3 ∣ q ^ 3 * (q ^ 2 - 1) / Nat.gcd (q + 1) 3 := by
  have hq3 : q % 3 = 2 := by omega
  have h3 : 3 ∣ q + 1 := by omega
  rw [Nat.gcd_eq_right h3]
  have h3' : 3 ∣ q ^ 2 - 1 := three_dvd_sq_sub_one hq3
  rw [Nat.mul_div_assoc _ h3']
  intro hd
  have hq2 : q ^ 2 % 9 = 4 ∨ q ^ 2 % 9 = 7 := by
    rcases h with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq3' : q ^ 3 % 3 = 2 := by rw [Nat.pow_mod, hq3]
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with hd | hd
  · omega
  · obtain ⟨m, hm⟩ := h3'
    obtain ⟨k, hk⟩ := hd
    rw [hm, Nat.mul_div_cancel_left _ (by norm_num)] at hk
    omega

theorem not_three_dvd_card_normalizer_sylow_two {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (Q : Sylow 2 (PSU3 2 p)) :
    ¬ 3 ∣ Nat.card (Subgroup.normalizer ((Q : Subgroup (PSU3 2 p)) : Set (PSU3 2 p))) := by
  rw [card_normalizer_sylow_two_psu3 hp.two_le Q]
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have h9 := two_pow_mod_nine (prime_mod_six hp hp2 hp3)
  exact not_three_dvd_normalizer_card h9

theorem not_three_dvd_orderOf_of_commute_involution {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    {x t : PSU3 2 p} (ht : orderOf t = 2) (hx : x * t = t * x) : ¬ 3 ∣ orderOf x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have htQ : t ∈ (Q : Subgroup (PSU3 2 p)) := hQ (Subgroup.mem_zpowers t)
  set B : Subgroup (PSU3 2 p) := Subgroup.normalizer ((Q : Subgroup (PSU3 2 p)) : Set _) with hB
  have htB : t ∈ B := Subgroup.le_normalizer htQ
  have hSE := (bender_psu3_borel_full p hp.two_le Q).1
  have hxB : x ∈ B := by
    by_contra hxB
    have hodd := hSE.2.2 x hxB
    have hmem : t ∈ B ⊓ B.map (MulAut.conj x⁻¹).toMonoidHom := by
      refine ⟨htB, Subgroup.mem_map.mpr ⟨t, htB, ?_⟩⟩
      have : x⁻¹ * t * x = t := by
        rw [mul_assoc, ← hx, inv_mul_cancel_left]
      simpa [MulAut.conj_apply] using this
    have hdvd : orderOf t ∣ Nat.card ↥(B ⊓ B.map (MulAut.conj x⁻¹).toMonoidHom) :=
      Subgroup.orderOf_dvd_natCard _ hmem
    rw [ht] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  intro h3
  exact not_three_dvd_card_normalizer_sylow_two hp h5 Q
    (h3.trans (Subgroup.orderOf_dvd_natCard _ hxB))

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame
