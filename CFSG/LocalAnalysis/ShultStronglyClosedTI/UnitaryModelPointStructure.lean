module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructureRoot
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.Models.BenderSuzuki
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryModel

open Matrix CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open scoped LinearAlgebra.Projectivization

theorem unitaryCoordinatePoint_two_ne_zero {K : Type*} [Field K] :
    unitaryCoordinatePoint (K := K) 2 ≠ unitaryCoordinatePoint (K := K) 0 := by
  rw [Ne, unitaryCoordinatePoint, unitaryCoordinatePoint, Projectivization.mk_eq_mk_iff']
  rintro ⟨a, ha⟩
  simpa using congrFun ha 2

theorem special_mk_eq_one_iff {K : Type*} [Field K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {A : GL (Fin 3) K}
    (hA : A ∈ J.specialSubgroup) :
    ProjGenLinGroup.mk A = 1 ↔
      ∃ c : K, (A : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c ∧
        c * J.conj c = 1 ∧ c ^ 3 = 1 := by
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨hgram, hdet⟩ := (J.mem_specialSubgroup_iff A).mp hA
    rw [← hc] at hgram
    refine ⟨c, hc.symm, ?_, ?_⟩
    · have h : J.conj c * c = 1 := by
        simpa [hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
          Matrix.scalar_apply, Matrix.diagonal_apply] using congrArg (fun B => B 0 2) hgram
      exact (mul_comm _ _).trans h
    · have h := congrArg Units.val hdet
      rw [GeneralLinearGroup.val_det_apply, Units.val_one, ← hc, Matrix.det_fin_three] at h
      simpa [Matrix.scalar_apply, Matrix.diagonal_apply, pow_succ] using h
  · rintro ⟨c, hc, -, -⟩
    exact ⟨c, hc.symm⟩

theorem nonempty_mulEquiv_standardUnitary {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃*
      GLAProj (GLASUGroup (Fin 3) K (2 ^ f))) := by
  obtain ⟨e⟩ := projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hcard hfixed
  have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  have hcard' : Nat.card K = 2 ^ (2 * f) := by rw [hcard, ← pow_mul, mul_comm]
  exact ⟨(e.trans (MulEquiv.subgroupCongr hmodel)).trans (glaSU3EquivNative f hf hcard').symm⟩

theorem comap_stabilizer_two {K : Type*} [Field K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm (unitaryIsotropicPoints J))
    (hnative : ∀ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ p : unitaryIsotropicPoints J,
      ((rho g p : unitaryIsotropicPoints J) : ℙ K (Fin 3 → K)) =
        (g : ProjGenLinGroup (Fin 3) K) • (p : ℙ K (Fin 3 → K))) :
    (MulAction.stabilizer (Equiv.Perm (unitaryIsotropicPoints J))
        (unitaryOuterIsotropicPoint J hJ 2 (by decide))).comap rho =
      unitaryCoordinateStabilizer J 2 := by
  ext g
  change rho g _ = _ ↔
    (g : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 2 = _
  rw [← Subtype.coe_inj, hnative]
  rfl

theorem root_sup_torus {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K) (f : ℕ)
    (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (hermitianUnipotentPSU J hJ).range ⊔ (torusPSU J hJ).range =
      unitaryCoordinateStabilizer J 0 := by
  obtain ⟨rho, -, -, -, hnative, -, -, -, hstab, -, -, -, -, -, -, -, hreg, -⟩ :=
    unitary_entire_root_point_structure J f hf hcard hfixed hJ
  have hstabβ := comap_stabilizer_two J hJ rho hnative
  set α := unitaryOuterIsotropicPoint J hJ 0 (by decide)
  set β := unitaryOuterIsotropicPoint J hJ 2 (by decide)
  set B := unitaryCoordinateStabilizer J 0
  have hTeq := range_torusPSU_eq_inf J hJ
  have hUB : (hermitianUnipotentPSU J hJ).range ≤ B :=
    unitary_entire_root_fixes_first_coordinate J hJ
  have hβα : β ≠ α := fun h => unitaryCoordinatePoint_two_ne_zero (congrArg Subtype.val h)
  apply le_antisymm (sup_le hUB (hTeq ▸ inf_le_left))
  intro b hb
  have hbα : rho b α = α := by
    rw [← hstab] at hb
    exact hb
  have hbβ : rho b β ≠ α := by
    intro h
    apply hβα
    apply (rho b).injective
    rw [h, hbα]
  obtain ⟨u, hu, -⟩ := hreg β (rho b β) hβα hbβ
  have hmem : ((u : ProjectiveSpecialUnitaryMatrixGroup J))⁻¹ * b ∈ (torusPSU J hJ).range := by
    rw [hTeq]
    refine ⟨B.mul_mem (B.inv_mem (hUB u.2)) hb, ?_⟩
    rw [← hstabβ]
    change rho (((u : ProjectiveSpecialUnitaryMatrixGroup J))⁻¹ * b) β = β
    rw [map_mul, map_inv, Equiv.Perm.mul_apply, ← hu]
    exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
  rw [← mul_inv_cancel_left (u : ProjectiveSpecialUnitaryMatrixGroup J) b]
  exact Subgroup.mul_mem_sup u.2 hmem

theorem fusionStronglyEmbedded_point_stabilizer {K : Type*} [Field K] [Finite K]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    fusionStronglyEmbedded (unitaryCoordinateStabilizer J 0) := by
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  obtain ⟨-, S, -, -, -, hSR, -, hnormalizer, -⟩ :=
    unitary_entire_root_point_structure J f hf hcard hfixed hJ
  have h := (bender_projectiveSpecialUnitary_borel J f hf hcard hfixed hJ S).1
  rw [hSR, hnormalizer] at h
  exact h

theorem unitary_three_point_structure {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    let q := 2 ^ f
    let G := ProjectiveSpecialUnitaryMatrixGroup J
    let Ω := unitaryIsotropicPoints J
    let α := unitaryOuterIsotropicPoint J hJ 0 (by decide)
    let β := unitaryOuterIsotropicPoint J hJ 2 (by decide)
    let U := (hermitianUnipotentPSU J hJ).range
    let T := (torusPSU J hJ).range
    let B := unitaryCoordinateStabilizer J 0
    (∀ c : K, J.conj c = c ^ q) ∧
    (∀ A : GL (Fin 3) K, A ∈ J.specialSubgroup →
      (ProjGenLinGroup.mk A = 1 ↔
        ∃ c : K, (A : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c ∧
          c * J.conj c = 1 ∧ c ^ 3 = 1)) ∧
    Nonempty (G ≃* GLAProj (GLASUGroup (Fin 3) K q)) ∧
    (∀ g : G, g ∈ U ↔
      ∃ (a b : K) (M : GL (Fin 3) K), a * J.conj a + (b + J.conj b) = 0 ∧
        (M : Matrix (Fin 3) (Fin 3) K) = !![1, -J.conj a, b; 0, 1, a; 0, 0, 1] ∧
        (g : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M) ∧
    (∀ c : Kˣ, ∃ M : GL (Fin 3) K,
      (M : Matrix (Fin 3) (Fin 3) K) =
          !![(c : K), 0, 0; 0, J.conj (c : K) / c, 0; 0, 0, (J.conj (c : K))⁻¹] ∧
        ((torusPSU J hJ c : G) : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M) ∧
    ∃ rho : G →* Equiv.Perm Ω,
      Function.Injective rho ∧
      (∀ g : G, ∀ p : Ω, ((rho g p : Ω) : ℙ K (Fin 3 → K)) =
        (g : ProjGenLinGroup (Fin 3) K) • (p : ℙ K (Fin 3 → K))) ∧
      Nat.card Ω = q ^ 3 + 1 ∧
      (∀ b c d e : Ω, b ≠ c → d ≠ e → ∃ g : G, rho g b = d ∧ rho g c = e) ∧
      (MulAction.stabilizer (Equiv.Perm Ω) α).comap rho = B ∧
      (MulAction.stabilizer (Equiv.Perm Ω) β).comap rho = unitaryCoordinateStabilizer J 2 ∧
      (U.subgroupOf B).Normal ∧ U ⊓ T = ⊥ ∧ U ⊔ T = B ∧
      T = B ⊓ unitaryCoordinateStabilizer J 2 ∧
      IsCyclic T ∧ Nat.card T = (q ^ 2 - 1) / Nat.gcd 3 (q + 1) ∧
      (∃ S : Sylow 2 G, (S : Subgroup G) = U) ∧ Nat.card U = q ^ 3 ∧
      (∀ b c : Ω, b ≠ α → c ≠ α → ∃! u : U, rho u b = c) ∧
      fusionStronglyEmbedded B ∧ 2 ≤ twoRank G ∧
      (∀ g : G, (g ∈ B ∧ orderOf g = 2) ↔
        ∃ (b : K) (M : GL (Fin 3) K), b + J.conj b = 0 ∧ b ≠ 0 ∧
          (M : Matrix (Fin 3) (Fin 3) K) = !![1, 0, b; 0, 1, 0; 0, 0, 1] ∧
          (g : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M) ∧
      (∀ g ∈ B, orderOf g = 2 → g ∈ U ∧ ∀ u ∈ U, u * g = g * u) ∧
      (∃ w : G, orderOf w = 2 ∧ rho w α = β ∧ rho w β = α) ∧
      ∀ w : G, rho w α = β → rho w β = α →
        (∀ c : Kˣ, w⁻¹ * torusPSU J hJ c * w = torusPSU J hJ (c ^ q)⁻¹) ∧
        ∃ C : Subgroup G, (C : Set G) = {x | x ∈ T ∧ w⁻¹ * x * w = x⁻¹} ∧
          IsCyclic C ∧ Nat.card C = q - 1 := by
  intro q G Ω α β U T B
  obtain ⟨rho, S, -, hrho, hnative, hSR, hScard, -, hstab, hnormal, -, -, -, -, -, -,
    hreg, htwo⟩ := unitary_entire_root_point_structure J f hf hcard hfixed hJ
  have hTeq : T = B ⊓ unitaryCoordinateStabilizer J 2 := range_torusPSU_eq_inf J hJ
  have hUT : U ⊓ T = ⊥ := by
    rw [eq_bot_iff, ← root_inf_stabilizer_two J hJ]
    exact inf_le_inf_left _ (hTeq ▸ inf_le_right)
  obtain ⟨hTcard, hTcyc⟩ := range_torusPSU_card_isCyclic J q hcard hfixed hJ
  have hUcard : Nat.card U = q ^ 3 := by
    change Nat.card (hermitianUnipotentPSU J hJ).range = q ^ 3
    rw [← hSR]
    exact hScard
  have hswap {w : G} (hw : rho w α = β) :
      (w : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 0 =
        unitaryCoordinatePoint (K := K) 2 := by
    have h := congrArg Subtype.val hw
    rwa [hnative] at h
  have hswap' {w : G} (hw : rho w β = α) :
      (w : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 2 =
        unitaryCoordinatePoint (K := K) 0 := by
    have h := congrArg Subtype.val hw
    rwa [hnative] at h
  refine ⟨huppert_II_10_4_conj_eq_frobenius J q hcard hfixed,
    fun A hA => special_mk_eq_one_iff J hJ hA,
    nonempty_mulEquiv_standardUnitary J f hf hcard hfixed hJ,
    mem_root_iff J hJ, fun c => ⟨torusGL J c, torusGL_val J c, rfl⟩,
    rho, hrho, hnative, (huppert_II_10_12 J q hcard hfixed hJ).1, htwo, hstab,
    comap_stabilizer_two J hJ rho hnative, hnormal, hUT, root_sup_torus J f hf hcard hfixed hJ,
    hTeq, hTcyc, hTcard, ⟨S, hSR⟩, hUcard, hreg,
    fusionStronglyEmbedded_point_stabilizer J f hf hcard hfixed hJ,
    two_le_twoRank J f hf hcard hfixed hJ, ?_,
    fun g hg horder => point_involution_mem_center J f hf hcard hfixed hJ hg horder,
    ⟨hermitianWeylPSU J hJ, orderOf_hermitianWeylPSU J hJ,
      Subtype.ext ((hnative _ _).trans (hermitianWeylPSU_smul_zero J hJ)),
      Subtype.ext ((hnative _ _).trans (hermitianWeylPSU_smul_two J hJ))⟩,
    fun w hwα hwβ => ⟨fun c => ?_, swap_inverted_torus J f hcard hfixed hJ (hswap hwα)
      (hswap' hwβ)⟩⟩
  · intro g
    rw [point_involution_iff J f hf hcard hfixed hJ g]
    simp only [heisenbergMatrix, map_zero, neg_zero]
  · rw [swap_conj_torusPSU J hJ (hswap hwα) (hswap' hwβ),
      torusParam_eq_inv_pow J q hcard hfixed]

end CFSG.ShultStronglyClosedTI.UnitaryModel
