module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStructLin
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

open scoped commutatorElement

variable {K : Type} [Field K]

private noncomputable def p9uLift_phi (m : ℕ) (K : Type) [Field K] :
    GL (Fin m) K →* ((Fin m → K) ≃ₗ[K] (Fin m → K)) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin m → K)).toMonoidHom).comp
    ((Matrix.GeneralLinearGroup.toLin (n := Fin m) (R := K)).toMonoidHom)

private theorem p9uLift_phi_apply (m : ℕ) (g : GL (Fin m) K) (v : Fin m → K) :
    p9uLift_phi m K g v = Matrix.mulVec (g : Matrix (Fin m) (Fin m) K) v := rfl

private theorem p9uLift_phi_injective (m : ℕ) : Function.Injective (p9uLift_phi m K) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin m → K)).injective.comp
    (Matrix.GeneralLinearGroup.toLin (n := Fin m) (R := K)).injective

private theorem p9uLift_unit_pow_three (h : UnitaryFieldData 2 1 K) (c : Kˣ) :
    c ^ 3 = 1 := by
  have hK4 : Nat.card K = 4 := by rw [h.card]; norm_num
  have hcard : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK4]
  have := pow_card_eq_one' (G := Kˣ) (x := c)
  rwa [hcard] at this

private theorem p9uLift_scalar_mem (h : UnitaryFieldData 2 1 K) {m : ℕ}
    (C : Matrix (Fin m) (Fin m) K) (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin m) c ∈ primeFormUnitary h C := by
  rw [mem_primeFormUnitary, Matrix.GeneralLinearGroup.coe_scalar,
    scalar_barTranspose_mul_mul, h.norm_eq_pow, show 2 ^ 1 + 1 = 3 by norm_num,
    ← Units.val_pow_eq_pow_val, p9uLift_unit_pow_three h c, Units.val_one, one_smul]

private theorem p9uLift_mem_scalars_of_mem_ker (h : UnitaryFieldData 2 1 K) {m : ℕ}
    (C : Matrix (Fin m) (Fin m) K) {x : ↥(primeFormUnitary h C)}
    (hker : LargeEvenProjMk (primeFormUnitary h C) x = 1) :
    p9uLift_phi m K (x : GL (Fin m) K) ∈ scalars K (Fin m → K) := by
  have hmem : (x : GL (Fin m) K) ∈ LargeEvenScalars (Fin m) K := by
    have h1 : x ∈ (LargeEvenScalars (Fin m) K).subgroupOf (primeFormUnitary h C) :=
      (QuotientGroup.eq_one_iff x).1 hker
    rwa [Subgroup.mem_subgroupOf] at h1
  rw [largeEvenScalars_def, MonoidHom.mem_range] at hmem
  obtain ⟨c, hc⟩ := hmem
  rw [mem_scalars_iff]
  refine ⟨c, fun v => ?_⟩
  rw [← hc, p9uLift_phi_apply, Matrix.GeneralLinearGroup.coe_scalar]
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

private theorem p9uLift_scalars_subgroupOf_card (h : UnitaryFieldData 2 1 K) {m : ℕ}
    (hm : 1 ≤ m) (C : Matrix (Fin m) (Fin m) K) :
    Nat.card ((LargeEvenScalars (Fin m) K).subgroupOf (primeFormUnitary h C)) = 3 := by
  have hK4 : Nat.card K = 4 := by rw [h.card]; norm_num
  have hcard_units : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK4]
  rw [← hcard_units]
  let f : Kˣ → ↥((LargeEvenScalars (Fin m) K).subgroupOf (primeFormUnitary h C)) :=
    fun c => ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin m) c, p9uLift_scalar_mem h C c⟩,
      by rw [Subgroup.mem_subgroupOf, largeEvenScalars_def]; exact ⟨c, rfl⟩⟩
  refine Nat.card_congr (Equiv.ofBijective f ?_).symm
  constructor
  · intro c c' hcc
    have h1 : (Matrix.GeneralLinearGroup.scalar (Fin m) c : GL (Fin m) K) =
        Matrix.GeneralLinearGroup.scalar (Fin m) c' :=
      congrArg Subtype.val (congrArg Subtype.val hcc)
    refine Units.ext ?_
    have h3 : (Matrix.GeneralLinearGroup.scalar (Fin m) c : Matrix (Fin m) (Fin m) K)
        ⟨0, hm⟩ ⟨0, hm⟩ =
        (Matrix.GeneralLinearGroup.scalar (Fin m) c' : Matrix (Fin m) (Fin m) K)
        ⟨0, hm⟩ ⟨0, hm⟩ :=
      congrArg (fun A : GL (Fin m) K => (A : Matrix (Fin m) (Fin m) K) ⟨0, hm⟩ ⟨0, hm⟩) h1
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h3
  · rintro ⟨x, hx⟩
    have hx' : (x : GL (Fin m) K) ∈ LargeEvenScalars (Fin m) K := by
      rwa [Subgroup.mem_subgroupOf] at hx
    rw [largeEvenScalars_def, MonoidHom.mem_range] at hx'
    obtain ⟨c, hc⟩ := hx'
    refine ⟨c, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hc

theorem exists_isGoodIn_mulEquiv_preimage (h : UnitaryFieldData 2 1 K) {m : ℕ} (hm : 1 ≤ m)
    (C : Matrix (Fin m) (Fin m) K) {A : Subgroup (LargeEvenProj (primeFormUnitary h C))}
    (hA : IsElemAbelian 3 A) :
    ∃ Q : Subgroup ((Fin m → K) ≃ₗ[K] (Fin m → K)),
      IsGoodIn (scalars K (Fin m → K)) Q ∧
      Nonempty (↥(A.comap (LargeEvenProjMk (primeFormUnitary h C))) ≃* ↥Q) ∧
      Nat.card Q = 3 * Nat.card A := by
  classical
  let GU : Subgroup (GL (Fin m) K) := primeFormUnitary h C
  let E : Subgroup ↥GU := A.comap (LargeEvenProjMk GU)
  let ψ : ↥E →* ((Fin m → K) ≃ₗ[K] (Fin m → K)) :=
    (p9uLift_phi m K).comp (GU.subtype.comp E.subtype)
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : GU.subtype (E.subtype x) = GU.subtype (E.subtype y) :=
      p9uLift_phi_injective m hxy
    exact E.subtype_injective (GU.subtype_injective h1)
  have hQgood : IsGoodIn (scalars K (Fin m → K)) ψ.range := by
    constructor
    · rintro x ⟨g, rfl⟩ y ⟨g', rfl⟩
      rw [← map_commutatorElement]
      have hsc := p9uLift_mem_scalars_of_mem_ker h C (x := ((⁅g, g'⁆ : ↥E) : ↥GU)) (by
        show LargeEvenProjMk GU (((⁅g, g'⁆ : ↥E) : ↥GU)) = 1
        rw [show ((⁅g, g'⁆ : ↥E) : ↥GU) = ⁅(g : ↥GU), (g' : ↥GU)⁆ from
          map_commutatorElement (Subgroup.subtype E) g g', map_commutatorElement]
        have hgA : LargeEvenProjMk GU (g : ↥GU) ∈ A := Subgroup.mem_comap.1 g.2
        have hgA' : LargeEvenProjMk GU (g' : ↥GU) ∈ A := Subgroup.mem_comap.1 g'.2
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (congrArg Subtype.val (hA.1.is_comm.comm ⟨_, hgA⟩ ⟨_, hgA'⟩)))
      exact hsc
    · rintro x ⟨g, rfl⟩
      rw [← map_pow]
      have hsc := p9uLift_mem_scalars_of_mem_ker h C (x := ((g ^ 3 : ↥E) : ↥GU)) (by
        show LargeEvenProjMk GU (((g ^ 3 : ↥E) : ↥GU)) = 1
        rw [show ((g ^ 3 : ↥E) : ↥GU) = (g : ↥GU) ^ 3 from
          map_pow (Subgroup.subtype E) g 3, map_pow (LargeEvenProjMk GU),
          hA.2 _ (Subgroup.mem_comap.1 g.2)])
      exact hsc
  refine ⟨ψ.range, hQgood, ⟨MonoidHom.ofInjective hψinj⟩, ?_⟩
  have hQcard : Nat.card ψ.range = Nat.card ↥E := by
    change Nat.card (Set.range ψ) = Nat.card ↥E
    exact Nat.card_range_of_injective hψinj
  have hEcard : Nat.card ↥E =
      Nat.card ((LargeEvenScalars (Fin m) K).subgroupOf GU) * Nat.card A := by
    have h := QuotientGroup.card_preimage_mk ((LargeEvenScalars (Fin m) K).subgroupOf GU)
      (A : Set (LargeEvenProj GU))
    exact h
  rw [hQcard, hEcard, p9uLift_scalars_subgroupOf_card h hm C]

end CFSG.StandardType.FrameRoute

end
