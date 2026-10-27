module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1RLevel
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGE0PSUFrame
import CFSG.LocalAnalysis.StandardType.GGTCJDivLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.SemisimpleCentralizers CFSG.StandardType.S2MathAs51642Interfaces


section Helpers

private theorem l02qu3_projMk_eq_iff {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) (x y : ↥H) :
    LargeEvenProjMk H x = LargeEvenProjMk H y ↔
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c = (x : GL ι K)⁻¹ * (y : GL ι K) := by
  rw [LargeEvenProjMk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  exact MonoidHom.mem_range

private theorem l02qu3_ker_projMk_le_center {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) : (LargeEvenProjMk H).ker ≤ Subgroup.center ↥H := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : LargeEvenProjMk H x = LargeEvenProjMk H 1 := by rw [hx, map_one]
  obtain ⟨c, hc⟩ := (l02qu3_projMk_eq_iff H x 1).mp hx'
  have hxG : (x : GL ι K) = Matrix.GeneralLinearGroup.scalar ι c⁻¹ := by
    have : (x : GL ι K)⁻¹ = Matrix.GeneralLinearGroup.scalar ι c := by simpa using hc.symm
    rw [map_inv, ← this, inv_inv]
  have hxZ : (x : GL ι K) ∈ Subgroup.center (GL ι K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c⁻¹, hxG.symm⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact Subgroup.mem_center_iff.1 hxZ (y : GL ι K)

private theorem l02qu3_SU_eq_heldGU_inf_ker_det {d m : ℕ} {K : Type} [Field K]
    (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ 2 ^ m) :
    LargeEvenSUGroup (Fin d) K (2 ^ m) =
      Held.heldGU d K τ hτ ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin d) K →* Kˣ).ker := by
  have h1 : LargeEvenSUGroup (Fin d) K (2 ^ m) = CFSG.Open.StatedSU d (2 ^ m) K := rfl
  have h2 : CFSG.Open.StatedSU d (2 ^ m) K = Held.heldSU d K τ hτ :=
    (Held.hct_heldSU_eq_statedSU (a := d) (Q := 2 ^ m) (τ := τ) (hτ := hτ) hτQ).symm
  have h3 : Held.heldSU d K τ hτ =
      Held.heldGU d K τ hτ ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin d) K →* Kˣ).ker := by
    rw [Held.heldSU, CFSG.Open.StatedAPI.statedSL_eq_ker_det]
  rw [h1, h2, h3]

private theorem l02qu3_mem_fixSubgroup_normalizerMonoidHom {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] (H : Subgroup (GL ι K))
    (A : Subgroup.normalizer (H : Set (GL ι K))) (x : ↥H) :
    x ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (H.normalizerMonoidHom A) ↔
      (A : GL ι K) * (x : GL ι K) = (x : GL ι K) * (A : GL ι K) := by
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
  constructor
  · intro h
    have h' := congrArg (fun z : ↥H => (z : GL ι K)) h
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h'
    calc (A : GL ι K) * (x : GL ι K)
        = (A : GL ι K) * (x : GL ι K) * (A : GL ι K)⁻¹ * (A : GL ι K) := by group
      _ = (x : GL ι K) * (A : GL ι K) := by rw [h']
  · intro h
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    calc (A : GL ι K) * (x : GL ι K) * (A : GL ι K)⁻¹
        = (x : GL ι K) * (A : GL ι K) * (A : GL ι K)⁻¹ := by rw [h]
      _ = (x : GL ι K) := by group

private theorem l02qu3_map_fixSubgroup_normalizerMonoidHom {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] (H : Subgroup (GL ι K))
    (A : Subgroup.normalizer (H : Set (GL ι K))) :
    (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (H.normalizerMonoidHom A)).map
        H.subtype =
      Subgroup.centralizer ({(A : GL ι K)} : Set (GL ι K)) ⊓ H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, x.2⟩
    show (x : GL ι K) ∈ Subgroup.centralizer ({(A : GL ι K)} : Set (GL ι K))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((l02qu3_mem_fixSubgroup_normalizerMonoidHom H A x).1 hx).symm
  · rintro ⟨hy, hx⟩
    have hy' : y ∈ Subgroup.centralizer ({(A : GL ι K)} : Set (GL ι K)) := hy
    exact ⟨⟨y, hx⟩, (l02qu3_mem_fixSubgroup_normalizerMonoidHom H A ⟨y, hx⟩).mpr
      ((Subgroup.mem_centralizer_singleton_iff.1 hy').symm), rfl⟩

private theorem l02qu3_component_lift_heldGU {n : ℕ} {K : Type} [Field K]
    (SU GU : Subgroup (GL (Fin n) K))
    (hSUeq : SU = GU ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker)
    (g : GL (Fin n) K) (hgN : g ∈ Subgroup.normalizer (SU : Set (GL (Fin n) K)))
    (J : Subgroup ↥SU)
    (hJ : CFSG.Assembly.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (SU.normalizerMonoidHom ⟨g, hgN⟩))) :
    CFSG.Assembly.IsComponentOf (J.map SU.subtype)
      (Subgroup.centralizer ({g} : Set (GL (Fin n) K)) ⊓ GU) := by
  have hmap := l02qu3_map_fixSubgroup_normalizerMonoidHom SU ⟨g, hgN⟩
  have hCcompN : CFSG.Assembly.IsComponentOf (J.map SU.subtype)
      ((CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (SU.normalizerMonoidHom ⟨g, hgN⟩)).map SU.subtype) :=
    ⟨Subgroup.map_mono hJ.1, hJ.2.1.map _, CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective J _ Subtype.val_injective).symm hJ.2.2⟩
  rw [hmap] at hCcompN
  have hSUle : SU ≤ GU := by rw [hSUeq]; exact inf_le_left
  have hnormal : ((Subgroup.centralizer ({g} : Set (GL (Fin n) K)) ⊓ SU).subgroupOf
      (Subgroup.centralizer ({g} : Set (GL (Fin n) K)) ⊓ GU)).Normal := by
    have hSU' : Subgroup.centralizer ({g} : Set (GL (Fin n) K)) ⊓ SU =
        (Subgroup.centralizer ({g} : Set (GL (Fin n) K)) ⊓ GU) ⊓
          (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
      rw [hSUeq]
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [hSU']
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro a b ha hb
    obtain ⟨haH, haK⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨hbH, hbG⟩ := Subgroup.mem_inf.mp hb
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (Subgroup.centralizer ({g} : Set (GL (Fin n) K))).mul_mem
        ((Subgroup.centralizer ({g} : Set (GL (Fin n) K))).mul_mem hbH haH.1)
        ((Subgroup.centralizer ({g} : Set (GL (Fin n) K))).inv_mem hbH)
    · exact GU.mul_mem (GU.mul_mem hbG haH.2) (GU.inv_mem hbG)
    · rw [MonoidHom.mem_ker] at haK ⊢
      rw [map_mul, map_mul, map_inv, haK]
      group
  have hsub : CFSG.Assembly.IsSubnormal
      (Subgroup.centralizer ({g} : Set (GL (Fin n) K)) ⊓ SU)
      (Subgroup.centralizer ({g} : Set (GL (Fin n) K)) ⊓ GU) :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf (inf_le_inf le_rfl hSUle)).mpr hnormal.isSubnormal
  exact ⟨hCcompN.1.trans (inf_le_inf le_rfl hSUle), hCcompN.2.1.trans hsub, hCcompN.2.2⟩

end Helpers

theorem q1TorUni_component_lift {d m : ℕ} {K : Type} [Field K] [Finite K]
    (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ 2 ^ m)
    (s : GL (Fin d) K) (hs : s ∈ Held.heldGU d K τ hτ)
    (hsN : s ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K)))
    (J₀ : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m))))
    (hJ₀ : CFSG.Open.IsComponentOf J₀
      (ggAutFixedSubgroup (TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩))) :
    ∃ C : Subgroup (GL (Fin d) K),
      CFSG.Assembly.IsComponentOf C
        (Subgroup.centralizer ({s} : Set (GL (Fin d) K)) ⊓ Held.heldGU d K τ hτ) ∧
      C ≤ LargeEvenSUGroup (Fin d) K (2 ^ m) ∧
      J₀ = (C.subgroupOf (LargeEvenSUGroup (Fin d) K (2 ^ m))).map
        (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m))) := by
  have hSUeq : LargeEvenSUGroup (Fin d) K (2 ^ m) =
      Held.heldGU d K τ hτ ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin d) K →* Kˣ).ker :=
    l02qu3_SU_eq_heldGU_inf_ker_det τ hτ hτQ
  have hαβ : ∀ k : ↥(LargeEvenSUGroup (Fin d) K (2 ^ m)),
      LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m))
        ((LargeEvenSUGroup (Fin d) K (2 ^ m)).normalizerMonoidHom ⟨s, hsN⟩ k) =
      TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩
        (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m)) k) :=
    fun k => (TableB.projConj_mk _ ⟨s, hsN⟩ k).symm
  have hJ₀_asm : CFSG.Assembly.IsComponentOf J₀
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩)) := by
    rw [CFSG.Assembly.isComponentOf_iff_open]
    exact hJ₀
  obtain ⟨J, hJcomp, hJmap⟩ :=
    TCJ.tcjLin_component_lift
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m)))
      (QuotientGroup.mk'_surjective _)
      (l02qu3_ker_projMk_le_center _)
      ((LargeEvenSUGroup (Fin d) K (2 ^ m)).normalizerMonoidHom ⟨s, hsN⟩)
      (TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩)
      hαβ hJ₀_asm
  refine ⟨J.map (LargeEvenSUGroup (Fin d) K (2 ^ m)).subtype,
    l02qu3_component_lift_heldGU (LargeEvenSUGroup (Fin d) K (2 ^ m))
      (Held.heldGU d K τ hτ) hSUeq s hsN J hJcomp, ?_, ?_⟩
  · rintro _ ⟨j, -, rfl⟩
    exact j.2
  · have hsub : (J.map (LargeEvenSUGroup (Fin d) K (2 ^ m)).subtype).subgroupOf
        (LargeEvenSUGroup (Fin d) K (2 ^ m)) = J := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hx
        obtain ⟨j, hj, hjx⟩ := hx
        rw [← Subtype.ext hjx]
        exact hj
      · intro hx
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
        exact ⟨x, hx, rfl⟩
    rw [hsub]
    exact hJmap.symm

end CFSG.StandardType
