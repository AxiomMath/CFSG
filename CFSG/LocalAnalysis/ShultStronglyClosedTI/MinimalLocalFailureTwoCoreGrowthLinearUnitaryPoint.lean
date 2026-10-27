module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearUnitaryLine

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open Matrix CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization

universe u

variable {K : Type u} [Field K]

abbrev unitaryIsotropicPoints (J : HermitianForm 3 K) :=
  {x : ℙ K (Fin 3 → K) // ∃ (v : Fin 3 → K) (hv : v ≠ 0),
    x = Projectivization.mk K v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}

theorem unitary_outer_coordinate_isotropic (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (i : Fin 3) (hi : i ≠ 1) :
    ∃ (v : Fin 3 → K) (hv : v ≠ 0),
      unitaryCoordinatePoint (K := K) i = Projectivization.mk K v hv ∧
        dotProduct (fun k => J.conj (v k)) (J.form.mulVec v) = 0 := by
  refine ⟨Pi.single i 1, Pi.single_ne_zero_iff.mpr one_ne_zero, rfl, ?_⟩
  rw [hJ]
  fin_cases i
  · simp [dotProduct, Matrix.mulVec, Pi.single_apply]
  · exact (hi rfl).elim
  · simp [dotProduct, Matrix.mulVec, Pi.single_apply]

@[expose] def unitaryOuterIsotropicPoint (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (i : Fin 3) (hi : i ≠ 1) : unitaryIsotropicPoints J :=
  ⟨unitaryCoordinatePoint i, unitary_outer_coordinate_isotropic J hJ i hi⟩

@[expose] def unitaryCoordinateStabilizer (J : HermitianForm 3 K) (i : Fin 3) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (MulAction.stabilizer (ProjGenLinGroup (Fin 3) K)
    (unitaryCoordinatePoint (K := K) i)).comap
      (ProjectiveSpecialUnitaryMatrixGroup J).subtype

theorem unitary_linear_projective_action (A : GL (Fin 3) K)
    (x : ℙ K (Fin 3 → K)) :
    (GeneralLinearGroup.toLin A).toLinearEquiv • x = ProjGenLinGroup.mk A • x := by
  induction x using Projectivization.ind with
  | _ v hv => rfl

theorem unitary_entire_root_fixes_first_coordinate (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (hermitianUnipotentPSU J hJ).range ≤ unitaryCoordinateStabilizer J 0 := by
  rintro g ⟨z, rfl⟩
  change ProjGenLinGroup.mk (hermitianUnipotentGL J z) •
    unitaryCoordinatePoint (K := K) 0 = unitaryCoordinatePoint (K := K) 0
  rw [unitary_projective_coordinate_maps_iff]
  intro k hk
  fin_cases k
  · exact (hk rfl).elim
  · simp [hermitianUnipotentGL_val, hermitianUnipotentMatrix]
  · simp [hermitianUnipotentGL_val, hermitianUnipotentMatrix]

theorem unitary_full_coordinate_range (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (coord : hermitianUnipotentCoord J ≃ R)
    (hcoord : ∀ z : hermitianUnipotentCoord J,
      ∃ M : GL (Fin 3) K,
        (M : Matrix (Fin 3) (Fin 3) K) =
          !![1, z.1.1, z.1.2; 0, 1, -J.conj z.1.1; 0, 0, 1] ∧
        (((coord z : R) : ProjectiveSpecialUnitaryMatrixGroup J) :
          ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M) :
    (hermitianUnipotentPSU J hJ).range = R := by
  have hmatch (z : hermitianUnipotentCoord J) :
      (coord z : ProjectiveSpecialUnitaryMatrixGroup J) =
        hermitianUnipotentPSU J hJ z := by
    obtain ⟨M, hM, hproj⟩ := hcoord z
    have hMeq : M = hermitianUnipotentGL J z := by
      apply GeneralLinearGroup.ext
      intro i j
      rw [hM, hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq]
    apply Subtype.ext
    simpa only [hermitianUnipotentPSU_val, hMeq] using hproj
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    rw [← hmatch]
    exact (coord z).property
  · intro hg
    obtain ⟨z, hz⟩ := coord.surjective ⟨g, hg⟩
    exact ⟨z, (hmatch z).symm.trans (congrArg Subtype.val hz)⟩

theorem unitary_entire_root_point_structure [Finite K] (J : HermitianForm 3 K)
    (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    let G := ProjectiveSpecialUnitaryMatrixGroup J
    let Ω := unitaryIsotropicPoints J
    let a := unitaryOuterIsotropicPoint J hJ 0 (by decide)
    let R := (hermitianUnipotentPSU J hJ).range
    let U := unitaryCoordinateStabilizer J 0
    ∃ (rho : G →* Equiv.Perm Ω) (S : Sylow 2 G) (D : Subgroup G),
      Function.Injective rho ∧
      (∀ g : G, ∀ p : Ω,
        ((rho g p : Ω) : ℙ K (Fin 3 → K)) =
          (g : ProjGenLinGroup (Fin 3) K) • (p : ℙ K (Fin 3 → K))) ∧
      (S : Subgroup G) = R ∧ Nat.card S = (2 ^ f) ^ 3 ∧
      Subgroup.normalizer (R : Set G) = U ∧
      (MulAction.stabilizer (Equiv.Perm Ω) a).comap rho = U ∧
      (R.subgroupOf U).Normal ∧ D ≤ U ∧ IsCyclic D ∧ Odd (Nat.card D) ∧
      Nat.card D = ((2 ^ f) ^ 2 - 1) / Nat.gcd (2 ^ f + 1) 3 ∧
      R ⊓ D = ⊥ ∧ R ⊔ D = U ∧
      (∀ b c : Ω, b ≠ a → c ≠ a → ∃! r : R, rho (r : G) b = c) ∧
      (∀ b c d e : Ω, b ≠ c → d ≠ e →
        ∃ g : G, rho g b = d ∧ rho g c = e) := by
  let q := 2 ^ f
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let Ω := unitaryIsotropicPoints J
  let a := unitaryOuterIsotropicPoint J hJ 0 (by decide)
  let : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let : Finite G := Finite.of_injective
    (fun g : G => (g : ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases huppert_II_10_12 J q hcard hfixed hJ with
    ⟨_hΩcard, rho, pinf, hrho, hnatural, _hUcard,
      ⟨R, D, hRle, hDle, hN, hinf, hsup, hcyc, hRcard,
        _hcomm, _hcommcard, hDcard, hreg, ⟨coord, hcoord⟩,
        _hDcoord, _hDsurj⟩, htwo, _hGcard, _hthree⟩
  change G →* Equiv.Perm Ω at rho
  change Ω at pinf
  have hnative (g : G) (p : Ω) :
      ((rho g p : Ω) : ℙ K (Fin 3 → K)) =
        (g : ProjGenLinGroup (Fin 3) K) • (p : ℙ K (Fin 3 → K)) := by
    obtain ⟨M, hM, hMg⟩ := g.property
    exact (hnatural g p ⟨M, hM⟩ hMg).trans
      (by rw [← hMg]; exact unitary_linear_projective_action M p.val)
  have hrange : (hermitianUnipotentPSU J hJ).range = R :=
    unitary_full_coordinate_range J hJ R coord hcoord
  have hq : 1 < q := one_lt_pow₀ (by norm_num) (by omega)
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hone : q ^ 3 = 1 := hRcard.symm.trans (by rw [hbot]; simp)
    have hqone : q = 1 :=
      (pow_eq_one_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp hone
    omega
  have hfix (r : R) : rho (r : G) a = a := by
    apply Subtype.ext
    rw [hnative]
    have hr : (r : G) ∈ (hermitianUnipotentPSU J hJ).range := by
      rw [hrange]
      exact r.property
    exact unitary_entire_root_fixes_first_coordinate J hJ hr
  have hpoint : pinf = a := by
    by_contra hne
    obtain ⟨r, hrne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
    obtain ⟨r0, _hr0, huniq⟩ := hreg a a (Ne.symm hne) (Ne.symm hne)
    exact hrne ((huniq r (hfix r)).trans (huniq 1 (by simp)).symm)
  rw [hpoint] at hRle hDle hN hsup hreg
  let U := unitaryCoordinateStabilizer J 0
  have hstab : (MulAction.stabilizer (Equiv.Perm Ω) a).comap rho = U := by
    ext g
    change rho g a = a ↔
      (g : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 0 = _
    rw [← Subtype.coe_inj, hnative]
    rfl
  change R ≤ (MulAction.stabilizer (Equiv.Perm Ω) a).comap rho at hRle
  change D ≤ (MulAction.stabilizer (Equiv.Perm Ω) a).comap rho at hDle
  change (MulAction.stabilizer (Equiv.Perm Ω) a).comap rho ≤
    Subgroup.normalizer (R : Set G) at hN
  change R ⊔ D = (MulAction.stabilizer (Equiv.Perm Ω) a).comap rho at hsup
  rw [hstab] at hRle hDle hN hsup
  have hqpos : 0 < q := by omega
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
  have hRp : IsPGroup 2 R :=
    IsPGroup.of_card (n := f * 3) (by simpa only [q, ← pow_mul] using hRcard)
  obtain ⟨P, hP⟩ := exists_sylow_map_eq_of_normal_complement
    hRle hDle hN hinf hsup hRp hDodd.not_two_dvd_nat
  let : MulAction G Ω := MulAction.compHom Ω rho
  have hstab' : MulAction.stabilizer G a = U := by
    calc
      MulAction.stabilizer G a =
          (MulAction.stabilizer (Equiv.Perm Ω) a).comap rho := by
        ext g
        rfl
      _ = U := hstab
  have hreg' : ∀ b c : Ω, b ≠ a → c ≠ a →
      ∃! r : R, (r : G) • b = c := by
    intro b c hb hc
    exact hreg b c hb hc
  have hnormalizer : Subgroup.normalizer (R : Set G) = U := by
    rw [← hstab']
    exact normalizer_eq_stabilizer_of_regular_compl R a
      (hstab'.symm ▸ hRle) hRne hreg' (hstab'.symm ▸ hN)
  obtain ⟨S, hS⟩ := exists_sylow_map_eq_of_normalizer_le P (by
    rw [hP, hnormalizer])
  have hSR : (S : Subgroup G) = R := hS.trans hP
  have hScard : Nat.card S = q ^ 3 := by
    rw [hSR]
    exact hRcard
  have hnormal : (R.subgroupOf U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hN
  refine ⟨rho, S, D, hrho, hnative, hSR.trans hrange.symm, hScard,
    ?_, hstab, ?_, hDle, hcyc, hDodd, hDcard, ?_, ?_, ?_, htwo⟩
  · rw [hrange]
    exact hnormalizer
  · rw [hrange]
    exact hnormal
  · rw [hrange]
    exact hinf
  · rw [hrange]
    exact hsup
  · rw [hrange]
    exact hreg

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
