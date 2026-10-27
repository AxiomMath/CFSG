module

public import CFSG.LocalAnalysis.StandardType.GGL45TGSU
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestUnitary
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitarySemi
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdPair

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open Matrix
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

private theorem cu_of_unitary {K : Type} [Field K] {d n : ℕ} (h : UnitaryFieldData 2 n K)
    {B : GL (Fin d) K} (hB : B ∈ primeFormUnitary h (idGram K d)) :
    B ∈ GGL45TG.SU.CU h d := by
  refine ⟨1, ?_⟩
  have hA := mem_primeFormUnitary.mp hB
  change (((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * 1 *
    ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 at hA
  rw [Matrix.mul_one] at hA
  rw [one_smul]
  exact hA

private theorem scalars_subgroupOf_le_center {K : Type} [Field K] {d : ℕ}
    (H : Subgroup (GL (Fin d) K)) :
    (LargeEvenScalars (Fin d) K).subgroupOf H ≤ Subgroup.center H := by
  intro z hz
  apply Subgroup.comap_center_le_center (f := Subgroup.subtype H) (Subtype.coe_injective)
  change (z : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, ← largeEvenScalars_def]
  exact hz

private theorem glAut_eq_map {K : Type} [Field K] {d : ℕ} (σ : K ≃+* K) (x : GL (Fin d) K) :
    glAut σ x = Matrix.GeneralLinearGroup.map σ.toRingHom x :=
  Units.ext rfl

private theorem exists_comp_eq_of_model {K : Type} [Field K] [Finite K] {d n : ℕ}
    (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2))
    {φ : ↥(unitarySU 2 n K d) →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    (hM : UnitTB.Model φ) :
    ∃ α₀ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))),
      ∀ u, φ u = α₀ (InndiagSU.projU n d K u) := by
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun h => hq (Prod.ext_iff.mp h)
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊥ :=
    TableBUE.center_proj_eq_bot hM.field.card_eq_sq hd hdq
  have hkerπ : (InndiagSU.projU n d K).ker =
      (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSUGroup (Fin d) K (2 ^ n)) := by
    change (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))).ker =
      (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSUGroup (Fin d) K (2 ^ n))
    rw [LargeEvenProjMk, QuotientGroup.ker_mk']
  have hle_phi_pi : φ.ker ≤ (InndiagSU.projU n d K).ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have hc : u ∈ Subgroup.center ↥(unitarySU 2 n K d) := by
      obtain ⟨c, hc⟩ := hM.ker u hu
      exact SmallU.mem_center_of_scalar hc
    have hcent : InndiagSU.projU n d K u ∈
        Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
      Subgroup.map_center_le_center (f := InndiagSU.projU n d K) (InndiagSU.projU_surjective)
        ⟨u, hc, rfl⟩
    rwa [hZ, Subgroup.mem_bot] at hcent
  have hle_pi_phi : (InndiagSU.projU n d K).ker ≤ φ.ker := by
    intro u hu
    rw [MonoidHom.mem_ker]
    have huS : u ∈ (LargeEvenScalars (Fin d) K).subgroupOf
        (LargeEvenSUGroup (Fin d) K (2 ^ n)) := by
      rwa [← hkerπ]
    have hc : u ∈ Subgroup.center ↥(LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
      scalars_subgroupOf_le_center _ huS
    have hcent : φ u ∈
        Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
      Subgroup.map_center_le_center (f := φ) hM.surj ⟨u, hc, rfl⟩
    rwa [hZ, Subgroup.mem_bot] at hcent
  let eπ : (↥(unitarySU 2 n K d) ⧸ (InndiagSU.projU n d K).ker) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    QuotientGroup.liftEquiv (N := (InndiagSU.projU n d K).ker)
      (φ := InndiagSU.projU n d K) InndiagSU.projU_surjective rfl
  have heπ : ∀ u, eπ (QuotientGroup.mk' (InndiagSU.projU n d K).ker u) =
      InndiagSU.projU n d K u :=
    fun u => QuotientGroup.liftEquiv_mk (N := (InndiagSU.projU n d K).ker)
      (φ := InndiagSU.projU n d K) InndiagSU.projU_surjective rfl u
  let ψ : (↥(unitarySU 2 n K d) ⧸ (InndiagSU.projU n d K).ker) →*
      LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    QuotientGroup.lift (InndiagSU.projU n d K).ker φ hle_pi_phi
  have hψ' : ∀ u, ψ (QuotientGroup.mk' (InndiagSU.projU n d K).ker u) = φ u :=
    fun u => QuotientGroup.lift_mk' (N := (InndiagSU.projU n d K).ker) (φ := φ) hle_pi_phi u
  have hψsurj : Function.Surjective ψ := by
    intro r
    obtain ⟨u, rfl⟩ := hM.surj r
    exact ⟨QuotientGroup.mk' (InndiagSU.projU n d K).ker u, hψ' u⟩
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    rw [MonoidHom.mem_ker] at hr
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (InndiagSU.projU n d K).ker r
    rw [Subgroup.mem_bot]
    have hu : φ u = 1 := by rw [← hψ' u, hr]
    exact (QuotientGroup.eq_one_iff u).mpr (hle_phi_pi (MonoidHom.mem_ker.mpr hu))
  refine ⟨eπ.symm.trans (MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩), fun u => ?_⟩
  change φ u = (eπ.symm.trans (MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩))
    (InndiagSU.projU n d K u)
  rw [MulEquiv.trans_apply]
  change φ u = ψ (eπ.symm (InndiagSU.projU n d K u))
  rw [← heπ u, MulEquiv.symm_apply_apply, hψ' u]

theorem exists_semilin_through_model {d n p : ℕ} {K : Type} [Field K] [Finite K] (hd : 3 ≤ d)
    (hq : ¬(d = 3 ∧ 2 ^ n = 2))
    {φ : ↥(unitarySU 2 n K d) →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    (hM : UnitTB.Model φ)
    {a : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))} (ha : GGL45IsPElt p a) :
    ∃ g ∈ GGL45TG.SU.CU hM.field d, ∃ (σ : K ≃+* K) (m : ℕ), σ ^ p ^ m = 1 ∧
      ∀ x y : ↥(unitarySU 2 n K d),
        (y : GL (Fin d) K) = g * Matrix.GeneralLinearGroup.map σ.toRingHom x * g⁻¹ →
          a (φ x) = φ y := by
  obtain ⟨α₀, hα₀⟩ := exists_comp_eq_of_model hd hq hM
  let a' : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
    MulAut.conj α₀.symm a
  obtain ⟨B, hBunit, hBsem⟩ := InndiagSU.exists_isSemilin hM.field hd hq a'
  obtain ⟨m, hm⟩ := ha
  refine ⟨B, cu_of_unitary hM.field hBunit, InndiagSU.fieldFactorU hM.field hd hq a', m, ?_, ?_⟩
  · have ha' : a' ^ p ^ m = 1 := by
      have h1 := map_pow (MulAut.conj α₀.symm) a (p ^ m)
      rw [hm, map_one] at h1
      exact h1.symm
    have h2 : ((InndiagSU.fieldFactorU hM.field hd hq) a') ^ p ^ m = 1 := by
      rw [← map_pow, ha', map_one]
    exact h2
  · intro x y hy
    have hy' : (y : GL (Fin d) K) =
        B * glAut (InndiagSU.fieldFactorU hM.field hd hq a') (x : GL (Fin d) K) * B⁻¹ := by
      rw [glAut_eq_map (InndiagSU.fieldFactorU hM.field hd hq a') (x : GL (Fin d) K)]
      exact hy
    have hsem := hBsem x y hy'
    have ha'apply : ∀ z, α₀ (a' z) = a (α₀ z) := by
      intro z
      show α₀ ((MulAut.conj α₀.symm a) z) = a (α₀ z)
      rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_def,
        MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
    calc a (φ x) = a (α₀ (InndiagSU.projU n d K x)) := by rw [hα₀ x]
      _ = α₀ (a' (InndiagSU.projU n d K x)) := (ha'apply _).symm
      _ = α₀ (InndiagSU.projU n d K y) := by rw [hsem]
      _ = φ y := (hα₀ y).symm

end CFSG.StandardType
