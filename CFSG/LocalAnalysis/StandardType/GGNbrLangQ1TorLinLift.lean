module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
import CFSG.LocalAnalysis.StandardType.GGTCJDivLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Helpers

private theorem l02qt3_projMk_eq_iff {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) (x y : ↥H) :
    LargeEvenProjMk H x = LargeEvenProjMk H y ↔
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c = (x : GL ι K)⁻¹ * (y : GL ι K) := by
  rw [LargeEvenProjMk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  exact MonoidHom.mem_range

private theorem l02qt3_ker_projMk_le_center {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) : (LargeEvenProjMk H).ker ≤ Subgroup.center ↥H := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : LargeEvenProjMk H x = LargeEvenProjMk H 1 := by rw [hx, map_one]
  obtain ⟨c, hc⟩ := (l02qt3_projMk_eq_iff H x 1).mp hx'
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

private noncomputable def l02qt3_conjSL {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (A : GL ι K) : MulAut ↥(LargeEvenSLGroup ι K) where
  toFun h := ⟨A * (h : GL ι K) * A⁻¹,
    (inferInstance : (LargeEvenSLGroup ι K).Normal).conj_mem h.1 h.2 A⟩
  invFun h := ⟨A⁻¹ * (h : GL ι K) * A⁻¹⁻¹,
    (inferInstance : (LargeEvenSLGroup ι K).Normal).conj_mem h.1 h.2 A⁻¹⟩
  left_inv h := by apply Subtype.ext; simp [mul_assoc]
  right_inv h := by apply Subtype.ext; simp [mul_assoc]
  map_mul' x y := by apply Subtype.ext; simp [mul_assoc]

@[simp] private theorem l02qt3_conjSL_apply_val {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (A : GL ι K) (h : ↥(LargeEvenSLGroup ι K)) :
    ((l02qt3_conjSL A h : ↥(LargeEvenSLGroup ι K)) : GL ι K) = A * (h : GL ι K) * A⁻¹ :=
  rfl

private theorem l02qt3_map_fixSubgroup_conjSL {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] (A : GL ι K) :
    (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (l02qt3_conjSL A)).map
        (LargeEvenSLGroup ι K).subtype =
      Subgroup.centralizer ({A} : Set (GL ι K)) ⊓ LargeEvenSLGroup ι K := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf,
    CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := congrArg (fun z : ↥(LargeEvenSLGroup ι K) => (z : GL ι K)) hy
    rw [l02qt3_conjSL_apply_val] at h
    have h' : A * (y : GL ι K) * A⁻¹ * A = (y : GL ι K) * A := by rw [h]
    refine ⟨?_, y.2⟩
    simpa [mul_assoc] using h'.symm
  · rintro ⟨hc, hx⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    apply Subtype.ext
    rw [l02qt3_conjSL_apply_val]
    show A * x * A⁻¹ = x
    rw [hc.symm]
    group

private theorem l02qt3_component_lift_gl {N : ℕ} {K : Type} [Field K] [Finite K]
    (g : GL (Fin N) K) (J : Subgroup ↥(LargeEvenSLGroup (Fin N) K))
    (hJ : CFSG.Assembly.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (l02qt3_conjSL g))) :
    CFSG.Assembly.IsComponentOf (J.map (LargeEvenSLGroup (Fin N) K).subtype)
      (Subgroup.centralizer ({g} : Set (GL (Fin N) K))) := by
  have hNeq := l02qt3_map_fixSubgroup_conjSL (ι := Fin N) (K := K) g
  have hCcompN : CFSG.Assembly.IsComponentOf (J.map (LargeEvenSLGroup (Fin N) K).subtype)
      ((CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (l02qt3_conjSL g)).map
        (LargeEvenSLGroup (Fin N) K).subtype) :=
    ⟨Subgroup.map_mono hJ.1, hJ.2.1.map _, CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective J _ Subtype.val_injective).symm hJ.2.2⟩
  rw [hNeq] at hCcompN
  have hnormal : (((Subgroup.centralizer ({g} : Set (GL (Fin N) K))) ⊓
      LargeEvenSLGroup (Fin N) K).subgroupOf
        (Subgroup.centralizer ({g} : Set (GL (Fin N) K)))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro n k hn hk
    obtain ⟨hnH₀, hnSL⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.centralizer ({g} : Set (GL (Fin N) K))).mul_mem
        ((Subgroup.centralizer ({g} : Set (GL (Fin N) K))).mul_mem hk hnH₀)
        ((Subgroup.centralizer ({g} : Set (GL (Fin N) K))).inv_mem hk)
    · exact (inferInstance : (LargeEvenSLGroup (Fin N) K).Normal).conj_mem n hnSL k
  have hsub : CFSG.Assembly.IsSubnormal
      ((Subgroup.centralizer ({g} : Set (GL (Fin N) K))) ⊓ LargeEvenSLGroup (Fin N) K)
      (Subgroup.centralizer ({g} : Set (GL (Fin N) K))) :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf inf_le_left).mpr hnormal.isSubnormal
  exact ⟨hCcompN.1.trans inf_le_left, hCcompN.2.1.trans hsub, hCcompN.2.2⟩

end Helpers

theorem q1TorLin_component_lift {N : ℕ} (hN : 2 ≤ N) {K : Type} [Field K] [Finite K]
    (g : GL (Fin N) K) (J₀ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) K)))
    (hJ₀ : CFSG.Open.IsComponentOf J₀
      (ggAutFixedSubgroup (TableB.linConjAut (Fin N) K g))) :
    ∃ C : Subgroup (GL (Fin N) K),
      CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({g} : Set (GL (Fin N) K))) ∧
      C ≤ LargeEvenSLGroup (Fin N) K ∧
      J₀ = (C.subgroupOf (LargeEvenSLGroup (Fin N) K)).map
        (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) := by
  have hJ₀_asm : CFSG.Assembly.IsComponentOf J₀
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (TableB.linConjAut (Fin N) K g)) := by
    rw [CFSG.Assembly.isComponentOf_iff_open]
    exact hJ₀
  have hαβ : ∀ k : ↥(LargeEvenSLGroup (Fin N) K),
      LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) (l02qt3_conjSL g k) =
        TableB.linConjAut (Fin N) K g
          (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) k) := by
    intro k
    simp only [LargeEvenProjMk, QuotientGroup.mk'_apply]
    rw [TableB.linConjAut_mk]
    exact congrArg QuotientGroup.mk
      (Subtype.ext (by rw [l02qt3_conjSL_apply_val, MulAut.conjNormal_apply]))
  obtain ⟨J, hJcomp, hJmap⟩ :=
    TCJ.tcjLin_component_lift (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
      (QuotientGroup.mk'_surjective _) (l02qt3_ker_projMk_le_center _)
      (l02qt3_conjSL g) (TableB.linConjAut (Fin N) K g) hαβ hJ₀_asm
  refine ⟨J.map (LargeEvenSLGroup (Fin N) K).subtype,
    l02qt3_component_lift_gl g J hJcomp, ?_, ?_⟩
  · rintro _ ⟨j, -, rfl⟩
    exact j.2
  · have hsub : (J.map (LargeEvenSLGroup (Fin N) K).subtype).subgroupOf
        (LargeEvenSLGroup (Fin N) K) = J := by
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

end
