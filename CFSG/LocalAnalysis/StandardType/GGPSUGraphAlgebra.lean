module

public import CFSG.LocalAnalysis.StandardType.GGPSUGraphLayer0
public import CFSG.LocalAnalysis.StandardType.GGGraphNonePrimFamily
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.StandardType.ClassicalPosition.Geo

private theorem psuCPF_dag_mem {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    ∀ a ∈ psuAlg B, psuDag h a ∈ psuAlg B := by
  intro a ha
  have hJ : IsUnit (psuJ n K) := (AutPSU.gramJ n).isUnit
  have hG : IsUnit (psuJ n K).det := (Matrix.isUnit_iff_isUnit_det (psuJ n K)).mp hJ
  exact formAdj_mem_adjoin h.bar (G := psuJ n K) hG (S := ({B} : Set (GL (Fin n) K)))
    (fun s hs => by
      rw [Set.mem_singleton_iff] at hs
      subst hs
      exact (mem_primeFormUnitary).mp S.B_mem) ha

private theorem psuCPF_theta_mem {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    ∀ a ∈ psuAlg B, psuTheta h X a ∈ psuAlg B := by
  intro a ha
  refine Algebra.adjoin_induction (p := fun x _ => psuTheta h X x ∈ psuAlg B)
    ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    have hB : (B : Matrix (Fin n) (Fin n) K) ∈ psuAlg B :=
      Algebra.subset_adjoin ⟨B, rfl, rfl⟩
    obtain ⟨c, hc⟩ := S.theta_B
    rw [hc]
    exact Subalgebra.smul_mem _ hB c
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, psuTheta_smul, psuTheta_one]
    exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) (h.bar r)
  · intro x y hx hy hpx hpy
    rw [psuTheta_add]
    exact Subalgebra.add_mem _ hpx hpy
  · intro x y hx hy hpx hpy
    rw [psuTheta_mul]
    exact Subalgebra.mul_mem _ hpx hpy

private theorem psuCPF_psi_mem {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    ∀ a ∈ psuAlg B, psuPsi h X a ∈ psuAlg B := by
  intro a ha
  have hpsi : psuPsi h X a = psuTheta h X (psuDag h a) := by
    unfold psuPsi
    rfl
  rw [hpsi]
  exact psuCPF_theta_mem S (psuDag h a) (psuCPF_dag_mem S a ha)

private theorem psuCPF_comm {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∀ a ∈ psuAlg B, ∀ b ∈ psuAlg B, a * b = b * a := by
  have hgen : ∀ a ∈ psuAlg B, a * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * a := by
    intro a ha
    refine Algebra.adjoin_induction
      (p := fun x _ => x * (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) * x) ?_ ?_ ?_ ?_ ha
    · rintro x ⟨s, hs, rfl⟩
      rw [Set.mem_singleton_iff] at hs
      subst hs
      rfl
    · intro r
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one]
    · intro x y hx hy hpx hpy
      rw [add_mul, mul_add, hpx, hpy]
    · intro x y hx hy hpx hpy
      rw [Matrix.mul_assoc x y (B : Matrix (Fin n) (Fin n) K), hpy,
        ← Matrix.mul_assoc x (B : Matrix (Fin n) (Fin n) K) y, hpx,
        Matrix.mul_assoc (B : Matrix (Fin n) (Fin n) K) x y]
  intro a ha b hb
  refine Algebra.adjoin_induction (p := fun x _ => a * x = x * a) ?_ ?_ ?_ ?_ hb
  · rintro x ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hgen a ha
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  · intro x y hx hy hpx hpy
    rw [mul_add, add_mul, hpx, hpy]
  · intro x y hx hy hpx hpy
    rw [← Matrix.mul_assoc a x y, hpx, Matrix.mul_assoc x a y, hpy,
      ← Matrix.mul_assoc x y a]

theorem psuGraph_star_mem {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    ∀ a ∈ psuAlg B, psuDag h a ∈ psuAlg B ∧ psuPsi h X a ∈ psuAlg B := by
  intro a ha
  exact ⟨psuCPF_dag_mem S a ha, psuCPF_psi_mem S a ha⟩

theorem psuGraph_primFamily {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    ∃ P : Finset (Matrix (Fin n) (Fin n) K), PrimFamily (psuAlg B) P ∧
      ∀ e ∈ P, psuDag h e ∈ P ∧ psuPsi h X e ∈ P := by
  classical
  obtain ⟨P, hP⟩ := exists_primFamily_adjoin B
  refine ⟨P, hP, fun e he => ⟨?_, ?_⟩⟩
  · exact primFamily_map_mem hP (psuDag h) (psuDag_add h) (psuDag_mul h)
      (psuCPF_dag_mem S) (fun a _ => psuDag_dag h a) (psuCPF_comm B) e he
  · exact primFamily_map_mem hP (psuPsi h X) (psuPsi_add h X) (psuPsi_mul h X)
      (psuCPF_psi_mem S) (fun a _ => psuPsi_psi h X S.X_mem S.X_sq a) (psuCPF_comm B) e he

end CFSG.StandardType
