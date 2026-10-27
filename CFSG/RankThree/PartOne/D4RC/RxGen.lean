module

public import CFSG.RankThree.PartOne.D4RC.RxA0Def
import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearBasic
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.RankThree.Classical2
open scoped MatrixGroups

variable {L : Type} [Field L]

theorem rclg_map_transvection {k L : Type} [Field k] [Field L] [Algebra k L] {i j : Fin 3}
    (hij : i ≠ j) (t : k) :
    Matrix.SpecialLinearGroup.map (algebraMap k L) (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection hij (algebraMap k L t) := by
  ext a b
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  simp only [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, RingHom.mapMatrix_apply,
    Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem rcl_exists_perm_01 :
    ∀ i j : Fin 3, i ≠ j → ∃ w : Equiv.Perm (Fin 3), w 0 = i ∧ w 1 = j := by
  decide

theorem rcl_normalClosure_T12 {k : Type} [Field k] [CharP k 2] :
    Subgroup.normalClosure {X : SL(3, k) | ∃ t : k,
      X = Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t} = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  obtain ⟨w, hw0, hw1⟩ := rcl_exists_perm_01 i j hij
  have h := CFSG.QuasithinUnique.K1.signedPermutation_conj_transvection (K := k) w
    (show (0 : Fin 3) ≠ 1 by decide) c
  rw [CFSG.QuasithinUnique.K1.transvection_congr _ hij hw0 hw1] at h
  have hT : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈
      Subgroup.normalClosure {X : SL(3, k) | ∃ t : k,
        X = Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t} :=
    Subgroup.subset_normalClosure ⟨c, rfl⟩
  rw [SetLike.mem_coe, ← h]
  exact Subgroup.normalClosure_normal.conj_mem _ hT _


theorem rcl_commute_of_closure {G : Type*} [Group G] {S T : Set G}
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure T, a * b = b * a := by
  intro a ha b hb
  have h1 : Subgroup.closure T ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro t ht
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro s hs
    exact h s hs t ht
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure T : Set G) := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro t ht
    exact ((Subgroup.mem_centralizer_iff.1 (h1 ht)) s hs).symm
  exact ((Subgroup.mem_centralizer_iff.1 (h2 ha)) b hb).symm

theorem rcl_gen_split {k : Type} [Field k] [Finite k] [Algebra k L] (h2 : (2 : k) = 0)
    (Φ' : SL(3, L) ≃* SL(3, L)) (H : SL(3, L))
    (hH : ∀ X : SL(3, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y : SL(3, k), X = H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹) :
    Subgroup.normalClosure (((rclA0AlgOf L k H).subgroupOf (fixSubgroup Φ') :
      Subgroup (fixSubgroup Φ')) : Set (fixSubgroup Φ')) = ⊤ := by
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  let φ0 : SL(3, k) →* SL(3, L) :=
    (MulAut.conj H).toMonoidHom.comp (Matrix.SpecialLinearGroup.map (algebraMap k L))
  have hφ0 : ∀ Y, φ0 Y ∈ fixSubgroup Φ' := fun Y => (hH _).2 ⟨Y, rfl⟩
  let ψ : SL(3, k) →* fixSubgroup Φ' := φ0.codRestrict _ hφ0
  have hψ : Function.Surjective ψ := by
    rintro ⟨X, hX⟩
    obtain ⟨Y, rfl⟩ := (hH X).1 hX
    exact ⟨Y, rfl⟩
  have key := Subgroup.map_normalClosure {X : SL(3, k) | ∃ t : k,
      X = Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t} ψ hψ
  rw [rcl_normalClosure_T12, Subgroup.map_top_of_surjective _ hψ] at key
  rw [eq_top_iff, key]
  apply Subgroup.normalClosure_mono
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
  apply Subgroup.subset_closure
  refine ⟨t, ?_⟩
  show H * Matrix.SpecialLinearGroup.map (algebraMap k L) _ * H⁻¹ = _
  rw [rclg_map_transvection]

theorem rcl_T12_T13_comm {K : Type} [Field K] (a b : K) :
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) a *
        Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) b =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) b *
        Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) a := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem rcl_T12_T32_comm {K : Type} [Field K] (a b : K) :
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) a *
        Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) b =
      Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) b *
        Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) a := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem rcl_T13_T32_ne {K : Type} [Field K] :
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : K) *
        Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : K) ≠
      Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : K) *
        Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : K) := by
  intro h
  have h01 := congrArg (fun X : SL(3, K) => (X : Matrix (Fin 3) (Fin 3) K) 0 1) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h01
  simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply] at h01

theorem rcl_conj_commute {G : Type*} [Group G] (H x y : G) (h : x * y = y * x) :
    H * x * H⁻¹ * (H * y * H⁻¹) = H * y * H⁻¹ * (H * x * H⁻¹) := by
  calc H * x * H⁻¹ * (H * y * H⁻¹) = H * (x * y) * H⁻¹ := by group
    _ = H * (y * x) * H⁻¹ := by rw [h]
    _ = H * y * H⁻¹ * (H * x * H⁻¹) := by group

theorem rcl_conj_gen {k : Type} [Field k] [Algebra k L] (H : SL(3, L)) (P : SL(3, k))
    {i j : Fin 3} (hij : i ≠ j) (t : k)
    (hP : P * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t * P⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij t) :
    (MulAut.conj (H * Matrix.SpecialLinearGroup.map (algebraMap k L) P * H⁻¹))
        (H * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide)
          (algebraMap k L t) * H⁻¹) =
      H * Matrix.SpecialLinearGroup.transvection hij (algebraMap k L t) * H⁻¹ := by
  rw [MulAut.conj_apply, ← rclg_map_transvection, ← rclg_map_transvection, ← hP, map_mul, map_mul,
    map_inv]
  group

theorem rcl_map_conj_A0 {k : Type} [Field k] [Algebra k L] (H : SL(3, L)) (P : SL(3, k))
    {i j : Fin 3} (hij : i ≠ j)
    (hP : ∀ t : k,
      P * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t * P⁻¹ =
        Matrix.SpecialLinearGroup.transvection hij t) :
    (rclA0AlgOf L k H).map
        (MulAut.conj (H * Matrix.SpecialLinearGroup.map (algebraMap k L) P * H⁻¹)).toMonoidHom =
      Subgroup.closure {X | ∃ t : k,
        X = H * Matrix.SpecialLinearGroup.transvection hij (algebraMap k L t) * H⁻¹} := by
  rw [rclA0AlgOf, MonoidHom.map_closure]
  congr 1
  ext X
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, rcl_conj_gen H P hij t (hP t)⟩
  · rintro ⟨t, rfl⟩
    exact ⟨_, ⟨t, rfl⟩, rcl_conj_gen H P hij t (hP t)⟩

theorem rcl_phi3_split {k : Type} [Field k] [Finite k] [Algebra k L] (h2 : (2 : k) = 0)
    (Φ' : SL(3, L) ≃* SL(3, L)) (H : SL(3, L))
    (hH : ∀ X : SL(3, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y : SL(3, k), X = H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹) :
    ∃ g₁ ∈ fixSubgroup Φ', ∃ g₂ ∈ fixSubgroup Φ',
      (∀ a ∈ rclA0AlgOf L k H, ∀ b ∈ (rclA0AlgOf L k H).map (MulAut.conj g₁).toMonoidHom,
        a * b = b * a) ∧
      (∀ a ∈ rclA0AlgOf L k H, ∀ b ∈ (rclA0AlgOf L k H).map (MulAut.conj g₂).toMonoidHom,
        a * b = b * a) ∧
      ∃ b₁ ∈ (rclA0AlgOf L k H).map (MulAut.conj g₁).toMonoidHom,
        ∃ b₂ ∈ (rclA0AlgOf L k H).map (MulAut.conj g₂).toMonoidHom, b₁ * b₂ ≠ b₂ * b₁ := by
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  set P₁ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.signedPermutation 3 k (Equiv.swap 1 2)
  set P₂ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.signedPermutation 3 k (Equiv.swap 0 2)
  have hP₁ : ∀ t : k,
      P₁ * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t * P₁⁻¹ =
        Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t := fun t => by
    rw [CFSG.QuasithinUnique.K1.signedPermutation_conj_transvection]
    exact CFSG.QuasithinUnique.K1.transvection_congr _ _ (by decide) (by decide) t
  have hP₂ : ∀ t : k,
      P₂ * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t * P₂⁻¹ =
        Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t := fun t => by
    rw [CFSG.QuasithinUnique.K1.signedPermutation_conj_transvection]
    exact CFSG.QuasithinUnique.K1.transvection_congr _ _ (by decide) (by decide) t
  refine ⟨H * Matrix.SpecialLinearGroup.map (algebraMap k L) P₁ * H⁻¹, (hH _).2 ⟨P₁, rfl⟩,
    H * Matrix.SpecialLinearGroup.map (algebraMap k L) P₂ * H⁻¹, (hH _).2 ⟨P₂, rfl⟩, ?_, ?_, ?_⟩
  · rw [rcl_map_conj_A0 H P₁ _ hP₁]
    apply rcl_commute_of_closure
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact rcl_conj_commute H _ _ (rcl_T12_T13_comm (algebraMap k L a) (algebraMap k L b))
  · rw [rcl_map_conj_A0 H P₂ _ hP₂]
    apply rcl_commute_of_closure
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact rcl_conj_commute H _ _ (rcl_T12_T32_comm (algebraMap k L a) (algebraMap k L b))
  · rw [rcl_map_conj_A0 H P₁ _ hP₁, rcl_map_conj_A0 H P₂ _ hP₂]
    refine ⟨H * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide)
      (algebraMap k L 1) * H⁻¹, Subgroup.subset_closure ⟨1, rfl⟩,
      H * Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide)
      (algebraMap k L 1) * H⁻¹, Subgroup.subset_closure ⟨1, rfl⟩, ?_⟩
    rw [map_one]
    intro h
    apply rcl_T13_T32_ne (K := L)
    have h' := congrArg (fun X => H⁻¹ * X * H) h
    simpa [mul_assoc] using h'

end CFSG.RankThree.PartOne.D4RC
