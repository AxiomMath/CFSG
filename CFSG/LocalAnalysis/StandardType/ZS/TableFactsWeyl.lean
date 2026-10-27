module

public import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix
public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsForms
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4WeylMem
import CFSG.LocalAnalysis.StandardType.ZS.MonomialCard
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtEta
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.BlockSucc
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtMatrices
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.MonomialStab

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.TableFacts

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

private def tfwe_f4P : Matrix (Fin 4) (Fin 4) (ZMod p) :=
  !![0, 0, 0, 2; -1, -1, -1, 3; 0, -1, -1, 2; 0, 0, -1, 1]

private def tfwe_f4Pinv : Matrix (Fin 4) (Fin 4) (ZMod p) :=
  !![1/2, -1, 1, 0; 1/2, 0, -1, 1; 1/2, 0, 0, -1; 1/2, 0, 0, 0]

private theorem tfwe_f4P_mul_inv (hp : p ≠ 2) :
    (tfwe_f4P * tfwe_f4Pinv : Matrix (Fin 4) (Fin 4) (ZMod p)) = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [tfwe_f4P, tfwe_f4Pinv, Matrix.mul_apply, Fin.sum_univ_four, div_eq_mul_inv] <;>
    (try field_simp [h2]) <;> ring

private def tfwe_f4M (i : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod p) :=
  1 - Matrix.vecMulVec (Pi.single i 1) (fun j => (CartanMatrix.F₄ i j : ZMod p))

private def tfwe_f4N (i : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod p) :=
  (![halfOnesMat 4, diagSignMat 0, pijMat 0 1 1, pijMat 1 2 1] :
    Fin 4 → Matrix (Fin 4) (Fin 4) (ZMod p)) i

private theorem tfwe_f4M_mul_P (hp : p ≠ 2) (i : Fin 4) :
    (tfwe_f4M i * tfwe_f4P : Matrix (Fin 4) (Fin 4) (ZMod p)) =
      tfwe_f4P * tfwe_f4N i := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  fin_cases i <;>
    ext a b <;>
    fin_cases a <;> fin_cases b <;>
    simp [tfwe_f4M, tfwe_f4N, tfwe_f4P, halfOnesMat, pijMat, diagSignMat, Matrix.mul_apply,
      Matrix.vecMulVec_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.of_apply, Fin.sum_univ_four, CartanMatrix.F₄] <;>
    (try field_simp [h2]) <;> ring_nf

private theorem tfwe_f4N_mem (i : Fin 4) :
    (tfwe_f4N i : Matrix (Fin 4) (Fin 4) (ZMod p)) ∈ weylF4Mats := by
  fin_cases i <;> simp [tfwe_f4N, weylF4Mats]

private theorem tfwe_exists_f4N_eq {M : Matrix (Fin 4) (Fin 4) (ZMod p)} (hM : M ∈ weylF4Mats) :
    ∃ i, M = tfwe_f4N i := by
  rw [weylF4Mats, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨0, rfl⟩

private theorem tfwe_linearIndependent_cartanF4 {u : Fin 4 → V}
    {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) : LinearIndependent (ZMod p) u := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let F := (Int.castRingHom (ZMod p)).mapMatrix CartanMatrix.F₄
  have hdet : F.det ≠ 0 := by
    rw [← RingHom.map_det, CartanMatrix.F₄_det, map_one]
    exact one_ne_zero
  have hF : F.mulVec c = 0 := by
    funext i
    have h := congrArg (φ i) hc
    simp only [map_sum, map_smul, hK, smul_eq_mul, map_zero] at h
    simp only [F, Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply,
      eq_intCast, Pi.zero_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hc0 := Matrix.mulVec_injective_of_det_ne_zero hdet (hF.trans (Matrix.mulVec_zero F).symm)
  exact fun i => congrFun hc0 i

private theorem tfwe_toMatrix_reflection_cartanF4 {u : Fin 4 → V}
    {φ : Fin 4 → Module.Dual (ZMod p) V} (hφ : ∀ i, φ i (u i) = 2)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p))
    (b : Module.Basis (Fin 4) (ZMod p) V) (hb : ∀ i, b i = u i) (i : Fin 4) :
    LinearMap.toMatrix b b (Module.reflection (hφ i) : V →ₗ[ZMod p] V) = tfwe_f4M i := by
  rw [toMatrix_reflection b (hφ i), tfwe_f4M]
  congr 2
  · funext a
    rw [← hb i, Module.Basis.repr_self, Finsupp.single_eq_pi_single]
  · funext j
    rw [hb j, hK i j]

private theorem tfwe_toMatrix_eq_f4N (hp : p ≠ 2) (b f : Module.Basis (Fin 4) (ZMod p) V)
    (hP : b.toMatrix f = tfwe_f4P) {g : V →ₗ[ZMod p] V} {i : Fin 4}
    (hg : LinearMap.toMatrix b b g = tfwe_f4M i) : LinearMap.toMatrix f f g = tfwe_f4N i := by
  rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b' := b) (c' := b), hg, hP,
    Matrix.mul_assoc, tfwe_f4M_mul_P hp, ← Matrix.mul_assoc, ← hP,
    Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.one_mul]

theorem exists_basis_eq_basisClosure_weylF4 (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hA : IsCartanModel p CartanMatrix.F₄ J) :
    ∃ f : Module.Basis (Fin 4) (ZMod p) V, J = basisClosure f weylF4Mats := by
  obtain ⟨u, φ, hφ, hK, hspan, -, hJ⟩ := hA
  let b : Module.Basis (Fin 4) (ZMod p) V :=
    Module.Basis.mk (tfwe_linearIndependent_cartanF4 hK) hspan.ge
  have hb : ∀ i, b i = u i := fun i => Module.Basis.mk_apply _ _ i
  have hdet : IsUnit (tfwe_f4P : Matrix (Fin 4) (Fin 4) (ZMod p)).det :=
    Matrix.isUnit_det_of_right_inverse (tfwe_f4P_mul_inv hp)
  let f : Module.Basis (Fin 4) (ZMod p) V := b.map (Matrix.toLinearEquiv b tfwe_f4P hdet)
  have hP : b.toMatrix f = tfwe_f4P := by
    ext a j
    rw [Module.Basis.toMatrix_apply, Module.Basis.map_apply]
    change b.repr (Matrix.toLin b b tfwe_f4P (b j)) a = _
    rw [← LinearMap.toMatrix_apply, LinearMap.toMatrix_toLin]
  have hmat (i : Fin 4) :
      LinearMap.toMatrix f f (Module.reflection (hφ i) : V →ₗ[ZMod p] V) = tfwe_f4N i :=
    tfwe_toMatrix_eq_f4N hp b f hP (tfwe_toMatrix_reflection_cartanF4 hφ hK b hb i)
  refine ⟨f, ?_⟩
  rw [hJ, basisClosure]
  congr 1
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    change LinearMap.toMatrix f f _ ∈ weylF4Mats
    rw [hmat i]
    exact tfwe_f4N_mem i
  · intro hg
    obtain ⟨i, hi⟩ := tfwe_exists_f4N_eq hg
    exact ⟨i, eq_of_toMatrix_eq f (by rw [hmat i, hi])⟩

theorem weylF4Mats_orthogonal (hp : p ≠ 2) :
    ∀ M ∈ (weylF4Mats : Set (Matrix (Fin 4) (Fin 4) (ZMod p))),
      M.transpose * Matrix.diagonal 1 * M = Matrix.diagonal 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  intro M hM
  rw [weylF4Mats, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, diagSignMat, Matrix.diagonal_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat]
  · change (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)).transpose *
        (Matrix.diagonal fun _ : Fin 4 => (1 : ZMod p)) * halfOnesMat 4 =
      Matrix.diagonal (fun _ : Fin 4 => (1 : ZMod p))
    have hsym : (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)).transpose = halfOnesMat 4 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [halfOnesMat]
    rw [Matrix.diagonal_one, hsym]
    simpa using CFSG.StandardType.ZS.halfOnesMat_mul_self h2

@[expose] def weylF4Frame (k : Fin 3) : Set (Fin 4 → ZMod p) :=
  ![{x | ∃ i : Fin 4, x = Pi.single i 1 ∨ x = -Pi.single i 1},
    {x | ∃ ε : Fin 4 → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∏ i, ε i = 1 ∧
      x = (2 : ZMod p)⁻¹ • ε},
    {x | ∃ ε : Fin 4 → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∏ i, ε i = -1 ∧
      x = (2 : ZMod p)⁻¹ • ε}] k

private def tfwe_halfFrame (s : ZMod p) : Set (Fin 4 → ZMod p) :=
  {x | ∃ ε : Fin 4 → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∏ i, ε i = s ∧
    x = (2 : ZMod p)⁻¹ • ε}

private theorem tfwe_mem_frame0_iff {x : Fin 4 → ZMod p} :
    x ∈ (weylF4Frame 0 : Set (Fin 4 → ZMod p)) ↔
      ∃ i : Fin 4, x = Pi.single i 1 ∨ x = -Pi.single i 1 :=
  Iff.rfl

private theorem tfwe_single_mem_frame0 :
    (Pi.single 0 1 : Fin 4 → ZMod p) ∈ (weylF4Frame 0 : Set (Fin 4 → ZMod p)) :=
  tfwe_mem_frame0_iff.mpr ⟨0, Or.inl rfl⟩

private theorem tfwe_neg_mem_frame {k : Fin 3} {x : Fin 4 → ZMod p}
    (hx : x ∈ (weylF4Frame k : Set (Fin 4 → ZMod p))) : -x ∈ (weylF4Frame k : Set _) := by
  fin_cases k
  · obtain ⟨i, rfl | rfl⟩ := tfwe_mem_frame0_iff.mp hx
    · exact tfwe_mem_frame0_iff.mpr ⟨i, Or.inr rfl⟩
    · exact tfwe_mem_frame0_iff.mpr ⟨i, Or.inl (neg_neg _)⟩
  all_goals
    obtain ⟨ε, hε, hprod, rfl⟩ := hx
    refine ⟨-ε, fun i => ?_, ?_, (smul_neg _ _).symm⟩
    · rcases hε i with h | h <;> simp [h]
    · simp only [Pi.neg_apply]
      rw [Finset.prod_neg, hprod, Finset.card_univ, Fintype.card_fin]
      norm_num

private theorem tfwe_not_mem_halfFrame_of_frame0 (hp : p ≠ 2) {x : Fin 4 → ZMod p}
    {s : ZMod p} (h0 : x ∈ (weylF4Frame 0 : Set (Fin 4 → ZMod p))) : x ∉ tfwe_halfFrame s := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rintro ⟨ε, hε, -, rfl⟩
  obtain ⟨i, hi⟩ := tfwe_mem_frame0_iff.mp h0
  obtain ⟨j, hj⟩ : ∃ j : Fin 4, j ≠ i := ⟨i + 1, by fin_cases i <;> decide⟩
  have hx : ((2 : ZMod p)⁻¹ • ε) j = 0 := by
    rcases hi with hi | hi <;> rw [hi] <;> simp [hj]
  rw [Pi.smul_apply, smul_eq_mul, mul_eq_zero, inv_eq_zero] at hx
  rcases hx with hx | hx
  · exact h2 hx
  · rcases hε j with h | h <;> rw [h] at hx <;> simp at hx

private theorem tfwe_eq_of_mem_halfFrame (hp : p ≠ 2) {x : Fin 4 → ZMod p} {s t : ZMod p}
    (hs : x ∈ tfwe_halfFrame s) (ht : x ∈ tfwe_halfFrame t) : s = t := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨ε, -, rfl, rfl⟩ := hs
  obtain ⟨ε', -, rfl, he⟩ := ht
  rw [smul_right_injective _ (inv_ne_zero h2) he]

private theorem tfwe_frame_eq_of_mem (hp : p ≠ 2) {x : Fin 4 → ZMod p} {k k' : Fin 3}
    (hk : x ∈ (weylF4Frame k : Set (Fin 4 → ZMod p))) (hk' : x ∈ (weylF4Frame k' : Set _)) :
    k = k' := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hne : (1 : ZMod p) ≠ -1 := fun h => h2 (by linear_combination h)
  fin_cases k <;> fin_cases k'
  · rfl
  · exact absurd hk' (tfwe_not_mem_halfFrame_of_frame0 (s := 1) hp hk)
  · exact absurd hk' (tfwe_not_mem_halfFrame_of_frame0 (s := -1) hp hk)
  · exact absurd hk (tfwe_not_mem_halfFrame_of_frame0 (s := 1) hp hk')
  · rfl
  · exact absurd (tfwe_eq_of_mem_halfFrame (s := 1) (t := -1) hp hk hk') hne
  · exact absurd hk (tfwe_not_mem_halfFrame_of_frame0 (s := -1) hp hk')
  · exact absurd (tfwe_eq_of_mem_halfFrame (s := -1) (t := 1) hp hk hk') hne.symm
  · rfl

private theorem tfwe_pijMat01_mulVec (x : Fin 4 → ZMod p) :
    (pijMat 0 1 1 : Matrix (Fin 4) (Fin 4) (ZMod p)).mulVec x = x ∘ Equiv.swap 0 1 := by
  funext r
  fin_cases r <;>
    simp [Matrix.mulVec, dotProduct, pijMat, Equiv.swap_apply_def]

private theorem tfwe_pijMat12_mulVec (x : Fin 4 → ZMod p) :
    (pijMat 1 2 1 : Matrix (Fin 4) (Fin 4) (ZMod p)).mulVec x = x ∘ Equiv.swap 1 2 := by
  funext r
  fin_cases r <;>
    simp [Matrix.mulVec, dotProduct, pijMat, Equiv.swap_apply_def]

private theorem tfwe_comp_perm_mem_frame (σ : Equiv.Perm (Fin 4)) {k : Fin 3}
    {x : Fin 4 → ZMod p} (hx : x ∈ (weylF4Frame k : Set (Fin 4 → ZMod p))) :
    x ∘ σ ∈ (weylF4Frame k : Set _) := by
  have hs (i : Fin 4) : (Pi.single i 1 : Fin 4 → ZMod p) ∘ σ = Pi.single (σ.symm i) 1 := by
    funext j
    simp only [Function.comp_apply, Pi.single_apply, Equiv.apply_eq_iff_eq_symm_apply]
  fin_cases k
  · obtain ⟨i, rfl | rfl⟩ := tfwe_mem_frame0_iff.mp hx
    · exact tfwe_mem_frame0_iff.mpr ⟨σ.symm i, Or.inl (hs i)⟩
    · exact tfwe_mem_frame0_iff.mpr ⟨σ.symm i, Or.inr (by rw [← hs i]; rfl)⟩
  all_goals
    obtain ⟨ε, hε, hprod, rfl⟩ := hx
    exact ⟨ε ∘ σ, fun i => hε (σ i), (Equiv.prod_comp σ ε).trans hprod, rfl⟩

private theorem tfwe_diagSign_mulVec (x : Fin 4 → ZMod p) :
    (diagSignMat 0 : Matrix (Fin 4) (Fin 4) (ZMod p)).mulVec x =
      fun j => (if j = 0 then -1 else 1) * x j := by
  funext j
  rw [diagSignMat, Matrix.mulVec_diagonal]

private theorem tfwe_diagSign_frame0 {x : Fin 4 → ZMod p}
    (hx : x ∈ (weylF4Frame 0 : Set (Fin 4 → ZMod p))) :
    (diagSignMat 0 : Matrix (Fin 4) (Fin 4) (ZMod p)).mulVec x ∈ (weylF4Frame 0 : Set _) := by
  have key (i : Fin 4) : (diagSignMat 0 : Matrix (Fin 4) (Fin 4) (ZMod p)).mulVec
      (Pi.single i 1) ∈ (weylF4Frame 0 : Set _) := by
    refine tfwe_mem_frame0_iff.mpr ⟨i, ?_⟩
    rw [tfwe_diagSign_mulVec]
    by_cases hi : i = 0
    · subst hi
      right
      funext j
      by_cases hj : j = 0 <;> simp [hj]
    · left
      funext j
      by_cases hj : j = i
      · subst hj
        simp [hi]
      · simp [hj]
  obtain ⟨i, rfl | rfl⟩ := tfwe_mem_frame0_iff.mp hx
  · exact key i
  · rw [Matrix.mulVec_neg]
    exact tfwe_neg_mem_frame (key i)

private theorem tfwe_diagSign_halfFrame {s : ZMod p} {x : Fin 4 → ZMod p}
    (hx : x ∈ tfwe_halfFrame s) :
    (diagSignMat 0 : Matrix (Fin 4) (Fin 4) (ZMod p)).mulVec x ∈ tfwe_halfFrame (-s) := by
  obtain ⟨ε, hε, hprod, rfl⟩ := hx
  refine ⟨fun j => (if j = 0 then -1 else 1) * ε j, fun j => ?_, ?_, ?_⟩
  · by_cases hj : j = 0 <;> rcases hε j with h | h <;> simp only [h] <;> simp [hj]
  · rw [Finset.prod_mul_distrib, hprod, Fin.prod_univ_four]
    simp
  · rw [tfwe_diagSign_mulVec]
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

private theorem tfwe_halfOnes_mulVec (x : Fin 4 → ZMod p) :
    (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)).mulVec x =
      fun j => x j - (2 : ZMod p)⁻¹ * ∑ i, x i := by
  funext j
  rw [halfOnesMat, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp [Matrix.mulVec, dotProduct]

private theorem tfwe_halfOnes_frame0 (hp : p ≠ 2) {x : Fin 4 → ZMod p}
    (hx : x ∈ (weylF4Frame 0 : Set (Fin 4 → ZMod p))) :
    (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)).mulVec x ∈ (weylF4Frame 2 : Set _) := by
  have ht : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ (ZMod.prime_ne_zero p 2 hp)
  have key (m : Fin 4) : (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)).mulVec
      (Pi.single m 1) ∈ (weylF4Frame 2 : Set _) := by
    refine ⟨fun j => if j = m then 1 else -1, fun j => ?_, ?_, ?_⟩
    · by_cases hj : j = m <;> simp [hj]
    · fin_cases m <;> simp [Fin.prod_univ_four]
    · have hsum : ∑ i, (Pi.single m 1 : Fin 4 → ZMod p) i = 1 := by simp
      rw [tfwe_halfOnes_mulVec, hsum]
      funext j
      by_cases hj : j = m
      · subst hj
        simp only [Pi.single_eq_same, Pi.smul_apply, if_pos, smul_eq_mul]
        linear_combination -ht
      · simp [hj]
  obtain ⟨m, rfl | rfl⟩ := tfwe_mem_frame0_iff.mp hx
  · exact key m
  · rw [Matrix.mulVec_neg]
    exact tfwe_neg_mem_frame (key m)

private theorem tfwe_even_cases (hp : p ≠ 2) {ε : Fin 4 → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hprod : ∏ i, ε i = 1) :
    (∀ j, ε j = ε 0) ∨ ∑ i, ε i = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rw [Fin.prod_univ_four] at hprod
  rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2' | h2' <;>
    rcases hε 3 with h3 | h3 <;> rw [h0, h1, h2', h3] at hprod <;>
    first
    | exact absurd (show (2 : ZMod p) = 0 by linear_combination -hprod) h2
    | exact Or.inr (by rw [Fin.sum_univ_four, h0, h1, h2', h3]; ring1)
    | exact Or.inl fun j => by fin_cases j <;> simp [h0, h1, h2', h3]

private theorem tfwe_odd_cases (hp : p ≠ 2) {ε : Fin 4 → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hprod : ∏ i, ε i = -1) :
    ∃ m : Fin 4, ε = (fun j => if j = m then -1 else 1) ∨
      ε = -(fun j => if j = m then -1 else 1) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rw [Fin.prod_univ_four] at hprod
  rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2' | h2' <;>
    rcases hε 3 with h3 | h3 <;> rw [h0, h1, h2', h3] at hprod <;>
    try exact absurd (show (2 : ZMod p) = 0 by linear_combination hprod) h2
  · exact ⟨3, Or.inl (funext fun j => by fin_cases j <;> simp [h0, h1, h2', h3])⟩
  · exact ⟨2, Or.inl (funext fun j => by fin_cases j <;> simp [h0, h1, h2', h3])⟩
  · exact ⟨1, Or.inl (funext fun j => by fin_cases j <;> simp [h0, h1, h2', h3])⟩
  · exact ⟨0, Or.inr (funext fun j => by fin_cases j <;> simp [h0, h1, h2', h3])⟩
  · exact ⟨0, Or.inl (funext fun j => by fin_cases j <;> simp [h0, h1, h2', h3])⟩
  · exact ⟨1, Or.inr (funext fun j => by fin_cases j <;> simp [h0, h1, h2', h3])⟩
  · exact ⟨2, Or.inr (funext fun j => by fin_cases j <;> simp [h0, h1, h2', h3])⟩
  · exact ⟨3, Or.inr (funext fun j => by fin_cases j <;> simp [h0, h1, h2', h3])⟩

private theorem tfwe_halfOnes_const (hp : p ≠ 2) {x : Fin 4 → ZMod p} (hx : ∀ j, x j = x 0) :
    (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)).mulVec x = -x := by
  have ht : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ (ZMod.prime_ne_zero p 2 hp)
  rw [tfwe_halfOnes_mulVec, Fin.sum_univ_four, hx 1, hx 2, hx 3]
  funext j
  rw [Pi.neg_apply, hx j]
  linear_combination (-2 * x 0) * ht

private theorem tfwe_halfOnes_odd (hp : p ≠ 2) (m : Fin 4) :
    (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)).mulVec
      ((2 : ZMod p)⁻¹ • fun j => if j = m then -1 else 1) = -Pi.single m 1 := by
  have ht : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ (ZMod.prime_ne_zero p 2 hp)
  have hsum : ∑ i, ((2 : ZMod p)⁻¹ • fun j : Fin 4 => if j = m then (-1 : ZMod p) else 1) i =
      1 := by
    fin_cases m <;> simp only [Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul] <;> simp <;>
      linear_combination ht
  rw [tfwe_halfOnes_mulVec, hsum]
  funext j
  by_cases hj : j = m
  · subst hj
    simp only [Pi.smul_apply, smul_eq_mul, if_pos, Pi.neg_apply, Pi.single_eq_same]
    linear_combination -ht
  · simp [hj]

private theorem tfwe_halfOnes_frame1 (hp : p ≠ 2) {x : Fin 4 → ZMod p}
    (hx : x ∈ (weylF4Frame 1 : Set (Fin 4 → ZMod p))) :
    (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)).mulVec x ∈ (weylF4Frame 1 : Set _) := by
  obtain ⟨ε, hε, hprod, rfl⟩ := hx
  rcases tfwe_even_cases hp hε hprod with hc | hsum
  · rw [tfwe_halfOnes_const hp fun j => by rw [Pi.smul_apply, Pi.smul_apply, hc j]]
    exact tfwe_neg_mem_frame (k := 1) ⟨ε, hε, hprod, rfl⟩
  · have hfix : (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)).mulVec
        ((2 : ZMod p)⁻¹ • ε) = (2 : ZMod p)⁻¹ • ε := by
      rw [tfwe_halfOnes_mulVec]
      funext j
      simp [← Finset.mul_sum, hsum]
    rw [hfix]
    exact ⟨ε, hε, hprod, rfl⟩

private theorem tfwe_halfOnes_frame2 (hp : p ≠ 2) {x : Fin 4 → ZMod p}
    (hx : x ∈ (weylF4Frame 2 : Set (Fin 4 → ZMod p))) :
    (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)).mulVec x ∈ (weylF4Frame 0 : Set _) := by
  obtain ⟨ε, hε, hprod, rfl⟩ := hx
  obtain ⟨m, rfl | rfl⟩ := tfwe_odd_cases hp hε hprod
  · rw [tfwe_halfOnes_odd hp m]
    exact tfwe_mem_frame0_iff.mpr ⟨m, Or.inr rfl⟩
  · rw [smul_neg, Matrix.mulVec_neg, tfwe_halfOnes_odd hp m, neg_neg]
    exact tfwe_mem_frame0_iff.mpr ⟨m, Or.inl rfl⟩

private theorem tfwe_frame_image_of_mem_weylF4Mats (hp : p ≠ 2)
    {M : Matrix (Fin 4) (Fin 4) (ZMod p)} (hM : M ∈ weylF4Mats) (k : Fin 3) :
    ∃ k' : Fin 3, ∀ x ∈ (weylF4Frame k : Set (Fin 4 → ZMod p)),
      M.mulVec x ∈ (weylF4Frame k' : Set _) := by
  rw [weylF4Mats, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · fin_cases k
    · exact ⟨0, fun x hx => tfwe_diagSign_frame0 hx⟩
    · exact ⟨2, fun x hx => tfwe_diagSign_halfFrame (s := 1) hx⟩
    · refine ⟨1, fun x hx => ?_⟩
      have h := tfwe_diagSign_halfFrame (s := -1) hx
      rw [neg_neg] at h
      exact h
  · exact ⟨k, fun x hx => by rw [tfwe_pijMat01_mulVec]; exact tfwe_comp_perm_mem_frame _ hx⟩
  · exact ⟨k, fun x hx => by rw [tfwe_pijMat12_mulVec]; exact tfwe_comp_perm_mem_frame _ hx⟩
  · fin_cases k
    · exact ⟨2, fun x hx => tfwe_halfOnes_frame0 hp hx⟩
    · exact ⟨1, fun x hx => tfwe_halfOnes_frame1 hp hx⟩
    · exact ⟨0, fun x hx => tfwe_halfOnes_frame2 hp hx⟩

private theorem tfwe_mul_self_of_mem (hp : p ≠ 2) {M : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hM : M ∈ weylF4Mats) : M * M = 1 := by
  rw [weylF4Mats, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · exact diagSignMat_mul_self 0
  · exact pijMat_mul_self (by decide) one_ne_zero
  · exact pijMat_mul_self (by decide) one_ne_zero
  · exact halfOnesMat_mul_self (ZMod.prime_ne_zero p 2 hp)

private theorem tfwe_toMatrix_inv_of_mem (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) V)
    {x : V ≃ₗ[ZMod p] V} (hx : LinearMap.toMatrix f f (x : V →ₗ[ZMod p] V) ∈ weylF4Mats) :
    LinearMap.toMatrix f f (↑x⁻¹ : V →ₗ[ZMod p] V) =
      LinearMap.toMatrix f f (x : V →ₗ[ZMod p] V) := by
  have h1 : LinearMap.toMatrix f f (↑x⁻¹ : V →ₗ[ZMod p] V) *
      LinearMap.toMatrix f f (x : V →ₗ[ZMod p] V) = 1 := by
    rw [← toMatrix_coe_mul, inv_mul_cancel]
    simp
  calc LinearMap.toMatrix f f (↑x⁻¹ : V →ₗ[ZMod p] V)
      = LinearMap.toMatrix f f (↑x⁻¹ : V →ₗ[ZMod p] V) *
          (LinearMap.toMatrix f f (x : V →ₗ[ZMod p] V) *
            LinearMap.toMatrix f f (x : V →ₗ[ZMod p] V)) := by
        rw [tfwe_mul_self_of_mem hp hx, mul_one]
    _ = LinearMap.toMatrix f f (x : V →ₗ[ZMod p] V) := by
        rw [← mul_assoc, h1, one_mul]

theorem exists_frame_image_of_mem_weylF4 (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) V)
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ basisClosure f weylF4Mats) (k : Fin 3) :
    ∃ k' : Fin 3, ∀ x ∈ (weylF4Frame k : Set (Fin 4 → ZMod p)),
      (LinearMap.toMatrix f f (g : V →ₗ[ZMod p] V)).mulVec x ∈ (weylF4Frame k' : Set _) := by
  rw [basisClosure] at hg
  induction hg using Subgroup.closure_induction'' generalizing k with
  | mem x hx => exact tfwe_frame_image_of_mem_weylF4Mats hp hx k
  | inv_mem x hx =>
      rw [tfwe_toMatrix_inv_of_mem hp f hx]
      exact tfwe_frame_image_of_mem_weylF4Mats hp hx k
  | one => exact ⟨k, fun x hx => by simpa using hx⟩
  | mul x y _ _ hx hy =>
      obtain ⟨k₁, h₁⟩ := hy k
      obtain ⟨k₂, h₂⟩ := hx k₁
      exact ⟨k₂, fun v hv => by
        rw [toMatrix_coe_mul, ← Matrix.mulVec_mulVec]
        exact h₂ _ (h₁ v hv)⟩

private theorem tfwe_signChange_mem_g2mmn (f : Module.Basis (Fin 4) (ZMod p) V) (k : Fin 4) :
    diagMap p f (fun j : Fin 4 => if j = k then (-1 : (ZMod p)ˣ) else 1) ∈
      g2mmn p f 0 1 1 := by
  have h0 : diagMap p f (fun j : Fin 4 => if j = 0 then (-1 : (ZMod p)ˣ) else 1) ∈
      g2mmn p f 0 1 1 :=
    Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hper : permMap p f (Equiv.swap 0 k) ∈ g2mmn p f 0 1 1 :=
    Subgroup.subset_closure (Or.inl ⟨Equiv.swap 0 k, rfl⟩)
  have hconj : permMap p f (Equiv.swap 0 k) *
      diagMap p f (fun j : Fin 4 => if j = 0 then (-1 : (ZMod p)ˣ) else 1) *
      (permMap p f (Equiv.swap 0 k))⁻¹ ∈ g2mmn p f 0 1 1 :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hper h0) (Subgroup.inv_mem _ hper)
  have heq : permMap p f (Equiv.swap 0 k) *
      diagMap p f (fun j : Fin 4 => if j = 0 then (-1 : (ZMod p)ˣ) else 1) *
      (permMap p f (Equiv.swap 0 k))⁻¹ =
      diagMap p f (fun j : Fin 4 => if j = k then (-1 : (ZMod p)ˣ) else 1) := by
    rw [permMap_mul_diagMap_mul_inv]
    congr 1
    funext j
    rw [Function.comp_apply]
    by_cases hj : j = k
    · subst hj
      rw [Equiv.symm_swap, Equiv.swap_apply_right, if_pos rfl, if_pos rfl]
    · rw [if_neg hj]
      have hσ : (Equiv.swap (0 : Fin 4) k).symm j ≠ 0 := by
        intro hz
        have hz' : j = k := by
          have := (Equiv.symm_apply_eq (Equiv.swap (0 : Fin 4) k)).mp hz
          rwa [Equiv.swap_apply_left] at this
        exact hj hz'
      rw [if_neg hσ]
  rwa [heq] at hconj

private theorem tfwe_diagMap_signs_mem_g2mmn (f : Module.Basis (Fin 4) (ZMod p) V)
    {d : Fin 4 → (ZMod p)ˣ} (hd : ∀ k, d k = 1 ∨ d k = -1) :
    diagMap p f d ∈ g2mmn p f 0 1 1 := by
  classical
  have hkey : ∀ s : Finset (Fin 4),
      diagMap p f (∏ k ∈ s, (fun j : Fin 4 => if j = k then (-1 : (ZMod p)ˣ) else 1)) ∈
        g2mmn p f 0 1 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [diagMap_one]
    | insert k s hk ih =>
        rw [Finset.prod_insert hk, ← diagMap_mul]
        exact Subgroup.mul_mem _ (tfwe_signChange_mem_g2mmn f k) ih
  let s : Finset (Fin 4) := Finset.univ.filter (fun k => d k = -1)
  have hdecomp : d = ∏ k ∈ s, (fun j : Fin 4 => if j = k then (-1 : (ZMod p)ˣ) else 1) := by
    funext j
    rw [Finset.prod_apply]
    by_cases hj : d j = -1
    · rw [Finset.prod_eq_single j]
      · simp [hj]
      · intro k _ hkj
        rw [if_neg (Ne.symm hkj)]
      · intro hjnot
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) hjnot
    · have h1 : d j = 1 := (hd j).resolve_right hj
      rw [h1, Finset.prod_eq_one]
      intro k hk
      have hkj : j ≠ k := by
        intro h
        exact hj (by rw [h]; exact (Finset.mem_filter.mp hk).2)
      simp [hkj]
  rw [hdecomp]
  exact hkey s

private theorem tfwe_col_of_mapsTo_weylF4Frame_zero
    {M : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hg : ∀ x ∈ (weylF4Frame 0 : Set (Fin 4 → ZMod p)),
      M.mulVec x ∈ (weylF4Frame 0 : Set _)) (j : Fin 4) :
    ∃ (i : Fin 4) (c : (ZMod p)ˣ), (c = 1 ∨ c = -1) ∧
      M.mulVec (Pi.single j 1) = (c : ZMod p) • Pi.single i 1 := by
  have hmem : (Pi.single j 1 : Fin 4 → ZMod p) ∈ (weylF4Frame 0 : Set _) := by
    change Pi.single j 1 ∈ {x : Fin 4 → ZMod p |
      ∃ i : Fin 4, x = Pi.single i 1 ∨ x = -Pi.single i 1}
    exact ⟨j, Or.inl rfl⟩
  have h := hg (Pi.single j 1) hmem
  change M.mulVec (Pi.single j 1) ∈ {x : Fin 4 → ZMod p |
    ∃ i : Fin 4, x = Pi.single i 1 ∨ x = -Pi.single i 1} at h
  obtain ⟨i, hi | hi⟩ := h
  · exact ⟨i, 1, Or.inl rfl, by rw [hi]; simp⟩
  · exact ⟨i, -1, Or.inr rfl, by rw [hi]; simp⟩

private theorem tfwe_exists_sigma0_of_mapsTo_weylF4Frame_zero
    (f : Module.Basis (Fin 4) (ZMod p) V) {g : V ≃ₗ[ZMod p] V}
    (hg : ∀ x ∈ (weylF4Frame 0 : Set (Fin 4 → ZMod p)),
      (LinearMap.toMatrix f f (g : V →ₗ[ZMod p] V)).mulVec x ∈ (weylF4Frame 0 : Set _)) :
    ∃ (σ0 : Fin 4 → Fin 4) (c0 : Fin 4 → (ZMod p)ˣ),
      (∀ j, c0 j = 1 ∨ c0 j = -1) ∧
      (∀ j, (LinearMap.toMatrix f f (g : V →ₗ[ZMod p] V)).mulVec (Pi.single j 1) =
        (c0 j : ZMod p) • Pi.single (σ0 j) 1) ∧
      (∀ j, g (f j) = (c0 j : ZMod p) • f (σ0 j)) := by
  let M := LinearMap.toMatrix f f (g : V →ₗ[ZMod p] V)
  have hcol (j : Fin 4) : ∃ (i : Fin 4) (c : (ZMod p)ˣ), (c = 1 ∨ c = -1) ∧
      M.mulVec (Pi.single j 1) = (c : ZMod p) • Pi.single i 1 :=
    tfwe_col_of_mapsTo_weylF4Frame_zero (M := M) hg j
  let σ0 : Fin 4 → Fin 4 := fun j => (hcol j).choose
  let c0 : Fin 4 → (ZMod p)ˣ := fun j => (hcol j).choose_spec.choose
  have hc_unit : ∀ j, c0 j = 1 ∨ c0 j = -1 :=
    fun j => ((hcol j).choose_spec.choose_spec).1
  have hc : ∀ j, M.mulVec (Pi.single j 1) = (c0 j : ZMod p) • Pi.single (σ0 j) 1 :=
    fun j => ((hcol j).choose_spec.choose_spec).2
  have hgcol : ∀ j, g (f j) = ∑ i, M i j • f i := by
    intro j
    have h := Matrix.toLin_self f f (LinearMap.toMatrix f f (g : V →ₗ[ZMod p] V)) j
    rw [Matrix.toLin_toMatrix] at h
    exact h
  have hcolfun : ∀ j i, (M.mulVec (Pi.single j 1)) i = M i j := by
    intro j i; rw [Matrix.mulVec_single_one]; rfl
  have hgc : ∀ j, g (f j) = (c0 j : ZMod p) • f (σ0 j) := by
    intro j
    calc g (f j) = ∑ i, M i j • f i := hgcol j
      _ = ∑ i, ((c0 j : ZMod p) • Pi.single (σ0 j) 1) i • f i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [← hcolfun j i, hc j]
      _ = (c0 j : ZMod p) • f (σ0 j) := by
            rw [Finset.sum_eq_single (σ0 j)]
            · simp
            · intro i _ hi
              rw [Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero, zero_smul]
            · intro h; exact absurd (Finset.mem_univ _) h
  exact ⟨σ0, c0, hc_unit, hc, hgc⟩

private theorem tfwe_sigma0_injective_of_col_eq
    {M : Matrix (Fin 4) (Fin 4) (ZMod p)} (hMunit : IsUnit M.det)
    {σ0 : Fin 4 → Fin 4} {c0 : Fin 4 → (ZMod p)ˣ}
    (hc : ∀ j, M.mulVec (Pi.single j 1) = (c0 j : ZMod p) • Pi.single (σ0 j) 1) :
    Function.Injective σ0 := by
  intro i₁ i₂ hij
  by_contra hne
  have hvec : M.mulVec (Pi.single i₁ 1 -
      (((c0 i₁ * (c0 i₂)⁻¹ : (ZMod p)ˣ)) : ZMod p) • Pi.single i₂ 1) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hc i₁, hc i₂, hij, smul_smul]
    rw [show (((c0 i₁ * (c0 i₂)⁻¹ : (ZMod p)ˣ)) : ZMod p) * (c0 i₂ : ZMod p) =
      (c0 i₁ : ZMod p) from by
      rw [← Units.val_mul]
      congr 1
      group]
    rw [sub_self]
  have hx : Pi.single i₁ 1 -
      (((c0 i₁ * (c0 i₂)⁻¹ : (ZMod p)ˣ)) : ZMod p) • Pi.single i₂ 1 = 0 :=
    Matrix.mulVec_injective_of_det_ne_zero hMunit.ne_zero
      (by rw [hvec]; exact (Matrix.mulVec_zero M).symm)
  have hcoeff := congrFun hx i₁
  have hsingle : (Pi.single (i₂ : Fin 4) (1 : ZMod p) : Fin 4 → ZMod p) i₁ = 0 := by
    simp [Ne.symm hne]
  rw [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, hsingle, smul_zero, sub_zero,
    Pi.zero_apply] at hcoeff
  exact one_ne_zero hcoeff

private theorem tfwe_isUnit_det_toMatrix (f : Module.Basis (Fin 4) (ZMod p) V)
    (g : V ≃ₗ[ZMod p] V) :
    IsUnit (LinearMap.toMatrix f f (g : V →ₗ[ZMod p] V)).det := by
  have h1 : LinearMap.toMatrix f f (g : V →ₗ[ZMod p] V) *
      LinearMap.toMatrix f f (↑g⁻¹ : V →ₗ[ZMod p] V) = 1 := by
    rw [← toMatrix_coe_mul f g g⁻¹, mul_inv_cancel]
    simp
  exact Matrix.isUnit_det_of_right_inverse h1

theorem mem_g2mmn_of_mapsTo_weylF4Frame_zero (_hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) V)
    {g : V ≃ₗ[ZMod p] V}
    (hg : ∀ x ∈ (weylF4Frame 0 : Set (Fin 4 → ZMod p)),
      (LinearMap.toMatrix f f (g : V →ₗ[ZMod p] V)).mulVec x ∈ (weylF4Frame 0 : Set _)) :
    g ∈ g2mmn p f 0 1 1 := by
  obtain ⟨σ0, c0, hc_unit, hc, hgc⟩ :=
    tfwe_exists_sigma0_of_mapsTo_weylF4Frame_zero (f := f) hg
  have hinj := tfwe_sigma0_injective_of_col_eq (tfwe_isUnit_det_toMatrix f g) hc
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective σ0 (Finite.injective_iff_bijective.mp hinj)
  have hgeq : g = diagMap p f (c0 ∘ σ.symm) * permMap p f σ := by
    refine eq_diagMap_mul_permMap f σ c0 ?_
    intro j
    change g (f j) = (c0 j) • f (σ j)
    rw [show σ j = σ0 j from rfl]
    exact hgc j
  rw [hgeq]
  exact Subgroup.mul_mem _ (tfwe_diagMap_signs_mem_g2mmn f (fun k => hc_unit (σ.symm k)))
    (Subgroup.subset_closure (Or.inl ⟨σ, rfl⟩))

private noncomputable def tfwe_permHom (f : Module.Basis (Fin 4) (ZMod p) V) :
    Equiv.Perm (Fin 4) →* (V ≃ₗ[ZMod p] V) where
  toFun := permMap p f
  map_one' := permMap_one f
  map_mul' := fun σ τ => (permMap_mul f σ τ).symm

private theorem tfwe_toMatrix_permMap_swap01 (f : Module.Basis (Fin 4) (ZMod p) V) :
    LinearMap.toMatrix f f (permMap p f (Equiv.swap 0 1) : V →ₗ[ZMod p] V) =
      pijMat 0 1 1 := by
  ext a b
  rw [LinearMap.toMatrix_apply]
  change f.repr (permMap p f (Equiv.swap 0 1) (f b)) a = pijMat 0 1 1 a b
  rw [permMap_apply_basis]
  fin_cases a <;> fin_cases b <;>
    simp [Module.Basis.repr_self, pijMat, Equiv.swap_apply_def, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne]

private theorem tfwe_toMatrix_permMap_swap12 (f : Module.Basis (Fin 4) (ZMod p) V) :
    LinearMap.toMatrix f f (permMap p f (Equiv.swap 1 2) : V →ₗ[ZMod p] V) =
      pijMat 1 2 1 := by
  ext a b
  rw [LinearMap.toMatrix_apply]
  change f.repr (permMap p f (Equiv.swap 1 2) (f b)) a = pijMat 1 2 1 a b
  rw [permMap_apply_basis]
  fin_cases a <;> fin_cases b <;>
    simp [Module.Basis.repr_self, pijMat, Equiv.swap_apply_def, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne]

private theorem tfwe_toMatrix_diagMap_sign (f : Module.Basis (Fin 4) (ZMod p) V) :
    LinearMap.toMatrix f f (diagMap p f (fun i : Fin 4 => if i = 0 then -1 else 1) :
      V →ₗ[ZMod p] V) = diagSignMat 0 := by
  ext a b
  rw [LinearMap.toMatrix_apply]
  change f.repr (diagMap p f (fun i : Fin 4 => if i = 0 then -1 else 1) (f b)) a =
    diagSignMat 0 a b
  rw [diagMap_apply_basis, map_smul]
  fin_cases a <;> fin_cases b <;>
    simp [Module.Basis.repr_self, diagSignMat, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne]

private theorem tfwe_permMap_swap23_mem (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) V) :
    permMap p f (Equiv.swap 2 3) ∈ basisClosure f weylF4Mats := by
  obtain ⟨k, hk, hkmat⟩ := CFSG.StandardType.ZS.FFourCoord.exists_mem_weylF4_swapRefl hp f 2
  have hk' : k = permMap p f (Equiv.swap 2 3) := by
    apply eq_of_toMatrix_eq f
    rw [hkmat]
    ext a b
    rw [LinearMap.toMatrix_apply]
    change (1 - Matrix.vecMulVec (Pi.single (Fin.castSucc (2 : Fin 3)) 1 -
        Pi.single (3 : Fin 4) 1) (Pi.single (Fin.castSucc (2 : Fin 3)) 1 -
        Pi.single (3 : Fin 4) 1) : Matrix (Fin 4) (Fin 4) (ZMod p)) a b =
      f.repr (permMap p f (Equiv.swap 2 3) (f b)) a
    rw [permMap_apply_basis, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
    fin_cases a <;> fin_cases b <;>
      simp [Module.Basis.repr_self, Pi.single_eq_same, Pi.single_eq_of_ne, Equiv.swap_apply_def,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne]
  rwa [hk'] at hk

private theorem tfwe_permMap_mem_basisClosure_weylF4 (hp : p ≠ 2)
    (f : Module.Basis (Fin 4) (ZMod p) V) (σ : Equiv.Perm (Fin 4)) :
    permMap p f σ ∈ basisClosure f weylF4Mats := by
  have h01 : permMap p f (Equiv.swap 0 1) ∈ basisClosure f weylF4Mats :=
    Subgroup.subset_closure (by
      change LinearMap.toMatrix f f (permMap p f (Equiv.swap 0 1) : V →ₗ[ZMod p] V) ∈ weylF4Mats
      rw [tfwe_toMatrix_permMap_swap01]
      simp [weylF4Mats])
  have h12 : permMap p f (Equiv.swap 1 2) ∈ basisClosure f weylF4Mats :=
    Subgroup.subset_closure (by
      change LinearMap.toMatrix f f (permMap p f (Equiv.swap 1 2) : V →ₗ[ZMod p] V) ∈ weylF4Mats
      rw [tfwe_toMatrix_permMap_swap12]
      simp [weylF4Mats])
  have h23 : permMap p f (Equiv.swap 2 3) ∈ basisClosure f weylF4Mats :=
    tfwe_permMap_swap23_mem hp f
  have htop : Subgroup.closure (Set.range (fun i : Fin 3 =>
      Equiv.swap i.castSucc i.succ)) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 3)
  have hcomap : Subgroup.closure (Set.range (fun i : Fin 3 =>
      Equiv.swap i.castSucc i.succ)) ≤
      Subgroup.comap (tfwe_permHom f) (basisClosure f weylF4Mats) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h01
    · exact h12
    · exact h23
  exact hcomap (by rw [htop]; trivial)

theorem g2mmn_le_basisClosure_weylF4 (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) V) :
    g2mmn p f 0 1 1 ≤ basisClosure f weylF4Mats := by
  have hsign : diagMap p f (fun i : Fin 4 => if i = 0 then -1 else 1) ∈
      basisClosure f weylF4Mats :=
    Subgroup.subset_closure (by
      change LinearMap.toMatrix f f
        (diagMap p f (fun i : Fin 4 => if i = 0 then -1 else 1) : V →ₗ[ZMod p] V) ∈ weylF4Mats
      rw [tfwe_toMatrix_diagMap_sign]
      simp [weylF4Mats])
  have hpair : diagMap p f (pairUnit p 0 1 1) ∈ basisClosure f weylF4Mats := by
    have h : pairUnit p (0 : Fin 4) 1 1 = 1 := by
      funext i
      by_cases h0 : i = 0
      · subst h0; simp [pairUnit]
      · by_cases h1 : i = 1
        · subst h1; simp [pairUnit, h0]
        · simp [pairUnit, h0, h1]
    rw [h, diagMap_one]
    exact Subgroup.one_mem _
  rw [g2mmn, Subgroup.closure_le]
  rintro x (hx | hx)
  · rcases hx with ⟨σ, rfl⟩
    exact tfwe_permMap_mem_basisClosure_weylF4 hp f σ
  · rcases hx with rfl | rfl
    · exact hsign
    · exact hpair

private theorem tfwe_sign_of_mem_closure {u : (ZMod p)ˣ}
    (hu : u ∈ Subgroup.closure ({1, -1} : Set (ZMod p)ˣ)) : u = 1 ∨ u = -1 := by
  induction hu using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy => rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp
  | inv x _ hx => rcases hx with rfl | rfl <;> simp

private theorem tfwe_mulVec_single (f : Module.Basis (Fin 4) (ZMod p) V)
    (g : V →ₗ[ZMod p] V) (j : Fin 4) :
    (LinearMap.toMatrix f f g).mulVec (Pi.single j 1) = ⇑(f.repr (g (f j))) := by
  funext i
  rw [Matrix.mulVec_single_one]
  exact LinearMap.toMatrix_apply f f g i j

private theorem tfwe_mapsTo_frame0_of_mem_g2mmn (f : Module.Basis (Fin 4) (ZMod p) V)
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ g2mmn p f 0 1 1) {x : Fin 4 → ZMod p}
    (hx : x ∈ (weylF4Frame 0 : Set (Fin 4 → ZMod p))) :
    (LinearMap.toMatrix f f (g : V →ₗ[ZMod p] V)).mulVec x ∈ (weylF4Frame 0 : Set _) := by
  obtain ⟨d, σ, hd, -, rfl⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn f (by decide) hg
  have hcol (j : Fin 4) : (LinearMap.toMatrix f f
      ((diagMap p f d * permMap p f σ : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V)).mulVec
        (Pi.single j 1) ∈ (weylF4Frame 0 : Set (Fin 4 → ZMod p)) := by
    rw [tfwe_mulVec_single, LinearEquiv.coe_coe, LinearEquiv.mul_apply, permMap_apply_basis,
      diagMap_apply_basis, map_smul, f.repr_self, Finsupp.coe_smul, Finsupp.single_eq_pi_single]
    rcases tfwe_sign_of_mem_closure (hd (σ j)) with h | h <;> rw [h]
    · exact tfwe_mem_frame0_iff.mpr ⟨σ j, Or.inl (by simp)⟩
    · exact tfwe_mem_frame0_iff.mpr ⟨σ j, Or.inr (by simp)⟩
  obtain ⟨i, rfl | rfl⟩ := tfwe_mem_frame0_iff.mp hx
  · exact hcol i
  · rw [Matrix.mulVec_neg]
    exact tfwe_neg_mem_frame (hcol i)

private theorem tfwe_inv_mulVec_mulVec (f : Module.Basis (Fin 4) (ZMod p) V)
    (a : V ≃ₗ[ZMod p] V) (x : Fin 4 → ZMod p) :
    (LinearMap.toMatrix f f (↑a⁻¹ : V →ₗ[ZMod p] V)).mulVec
      ((LinearMap.toMatrix f f (a : V →ₗ[ZMod p] V)).mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, ← toMatrix_coe_mul, inv_mul_cancel]
  simp

private theorem tfwe_exists_gen (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) V)
    {M : Matrix (Fin 4) (Fin 4) (ZMod p)} (hM : M ∈ weylF4Mats) :
    ∃ g ∈ basisClosure f weylF4Mats, LinearMap.toMatrix f f (g : V →ₗ[ZMod p] V) = M :=
  exists_mem_basisClosure_toMatrix_eq f hM
    (Matrix.isUnit_det_of_right_inverse (tfwe_mul_self_of_mem hp hM))

private theorem tfwe_exists_from_frame0 (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) V)
    (k : Fin 3) : ∃ w ∈ basisClosure f weylF4Mats,
      (LinearMap.toMatrix f f (w : V →ₗ[ZMod p] V)).mulVec (Pi.single 0 1) ∈
        (weylF4Frame k : Set (Fin 4 → ZMod p)) := by
  obtain ⟨d, hd, hdM⟩ := tfwe_exists_gen hp f (M := halfOnesMat 4) (by simp [weylF4Mats])
  obtain ⟨a, ha, haM⟩ := tfwe_exists_gen hp f (M := diagSignMat 0) (by simp [weylF4Mats])
  have h2 : (halfOnesMat 4).mulVec (Pi.single 0 1) ∈ (weylF4Frame 2 : Set (Fin 4 → ZMod p)) :=
    tfwe_halfOnes_frame0 hp tfwe_single_mem_frame0
  fin_cases k
  · refine ⟨1, one_mem _, ?_⟩
    rw [show ((1 : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = LinearMap.id from rfl,
      LinearMap.toMatrix_id, Matrix.one_mulVec]
    exact tfwe_single_mem_frame0
  · refine ⟨a * d, mul_mem ha hd, ?_⟩
    rw [toMatrix_coe_mul, ← Matrix.mulVec_mulVec, haM, hdM]
    have h := tfwe_diagSign_halfFrame (s := -1) h2
    rw [neg_neg] at h
    exact h
  · exact ⟨d, hd, by rw [hdM]; exact h2⟩

private theorem tfwe_frame_eq_iff (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) V)
    {a b : V ≃ₗ[ZMod p] V} (ha : a ∈ basisClosure f weylF4Mats) {k k' : Fin 3}
    (hak : ∀ x ∈ (weylF4Frame 0 : Set (Fin 4 → ZMod p)),
      (LinearMap.toMatrix f f (a : V →ₗ[ZMod p] V)).mulVec x ∈ (weylF4Frame k : Set _))
    (hbk : ∀ x ∈ (weylF4Frame 0 : Set (Fin 4 → ZMod p)),
      (LinearMap.toMatrix f f (b : V →ₗ[ZMod p] V)).mulVec x ∈ (weylF4Frame k' : Set _)) :
    k = k' ↔ a⁻¹ * b ∈ g2mmn p f 0 1 1 := by
  constructor
  · intro hkk
    rw [← hkk] at hbk
    obtain ⟨k'', hk''⟩ := exists_frame_image_of_mem_weylF4 hp f (inv_mem ha) k
    have h0 := hk'' _ (hak _ tfwe_single_mem_frame0)
    rw [tfwe_inv_mulVec_mulVec] at h0
    rw [tfwe_frame_eq_of_mem hp h0 tfwe_single_mem_frame0] at hk''
    refine mem_g2mmn_of_mapsTo_weylF4Frame_zero hp f fun x hx => ?_
    rw [toMatrix_coe_mul, ← Matrix.mulVec_mulVec]
    exact hk'' _ (hbk x hx)
  · intro h
    have h1 := hbk _ tfwe_single_mem_frame0
    rw [← mul_inv_cancel_left a b, toMatrix_coe_mul, ← Matrix.mulVec_mulVec] at h1
    exact tfwe_frame_eq_of_mem hp
      (hak _ (tfwe_mapsTo_frame0_of_mem_g2mmn f h tfwe_single_mem_frame0)) h1

private theorem tfwe_index_g2mmn (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) V) :
    ((g2mmn p f 0 1 1).subgroupOf (basisClosure f weylF4Mats)).index = 3 := by
  choose φ hφ using fun w : basisClosure f weylF4Mats =>
    exists_frame_image_of_mem_weylF4 hp f w.2 0
  have hK (a b : basisClosure f weylF4Mats) :
      φ a = φ b ↔ a⁻¹ * b ∈ (g2mmn p f 0 1 1).subgroupOf (basisClosure f weylF4Mats) := by
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact tfwe_frame_eq_iff hp f a.2 (hφ a) (hφ b)
  have hrep (k : Fin 3) : ∃ w : basisClosure f weylF4Mats, φ w = k := by
    obtain ⟨w, hw, hwk⟩ := tfwe_exists_from_frame0 hp f k
    exact ⟨⟨w, hw⟩, tfwe_frame_eq_of_mem hp (hφ ⟨w, hw⟩ _ tfwe_single_mem_frame0) hwk⟩
  choose r hr using hrep
  have hbij : Function.Bijective fun k : Fin 3 =>
      (QuotientGroup.mk (r k) : basisClosure f weylF4Mats ⧸
        (g2mmn p f 0 1 1).subgroupOf (basisClosure f weylF4Mats)) := by
    refine ⟨fun i j hij => ?_, fun q => ?_⟩
    · rw [← hr i, ← hr j]
      exact (hK _ _).mpr (QuotientGroup.eq.mp hij)
    · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨φ a, QuotientGroup.eq.mpr ((hK _ _).mp (hr (φ a)))⟩
  rw [Subgroup.index, ← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem card_basisClosure_weylF4 (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) V) :
    Nat.card (basisClosure f weylF4Mats) = 1152 := by
  have hH : Nat.card ((g2mmn p f 0 1 1).subgroupOf (basisClosure f weylF4Mats)) = 384 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (g2mmn_le_basisClosure_weylF4 hp f)).toEquiv,
      card_g2mmn hp (by norm_num) f (show (0 : Fin 4) ≠ 1 by decide) 1, orderOf_one,
      Nat.lcm_one_right]
    rfl
  rw [← Subgroup.card_mul_index ((g2mmn p f 0 1 1).subgroupOf (basisClosure f weylF4Mats)), hH,
    tfwe_index_g2mmn hp f]

theorem orderOf_ne_of_mem_basisClosure_weylF4 (hp5 : 5 ≤ p) (f : Module.Basis (Fin 4) (ZMod p) V)
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ basisClosure f weylF4Mats) : orderOf g ≠ p := by
  intro h
  have hp2 : p ≠ 2 := by omega
  have hdvd : orderOf g ∣ Nat.card (basisClosure f weylF4Mats) :=
    (basisClosure f weylF4Mats).orderOf_dvd_natCard hg
  rw [card_basisClosure_weylF4 hp2 f] at hdvd
  have hp_dvd : p ∣ 2 ^ 7 * 3 ^ 2 := by
    rw [show (1152 : ℕ) = 2 ^ 7 * 3 ^ 2 by norm_num] at hdvd
    rwa [h] at hdvd
  rcases (Fact.out : p.Prime).dvd_mul.mp hp_dvd with h2 | h3
  · have hp2' : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
        ((Fact.out : p.Prime).dvd_of_dvd_pow h2)
    omega
  · have hp3' : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp
        ((Fact.out : p.Prime).dvd_of_dvd_pow h3)
    omega

private theorem tfwe_exists_to_frame0 (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) V)
    (k : Fin 3) : ∃ w ∈ basisClosure f weylF4Mats,
      ∀ x ∈ (weylF4Frame k : Set (Fin 4 → ZMod p)),
        (LinearMap.toMatrix f f (w : V →ₗ[ZMod p] V)).mulVec x ∈ (weylF4Frame 0 : Set _) := by
  obtain ⟨u, hu, huk⟩ := tfwe_exists_from_frame0 hp f k
  obtain ⟨k'', hk''⟩ := exists_frame_image_of_mem_weylF4 hp f (inv_mem hu) k
  have h0 := hk'' _ huk
  rw [tfwe_inv_mulVec_mulVec] at h0
  rw [tfwe_frame_eq_of_mem hp h0 tfwe_single_mem_frame0] at hk''
  exact ⟨u⁻¹, inv_mem hu, hk''⟩

private theorem tfwe_basisDiagForm_one_apply (f : Module.Basis (Fin 4) (ZMod p) V) (v : V) :
    basisDiagForm f 1 v = dotProduct ⇑(f.repr v) ⇑(f.repr v) := by
  simp only [basisDiagForm, QuadraticMap.comp_apply, QuadraticMap.weightedSumSquares_apply,
    Pi.one_apply, one_smul, dotProduct]
  apply Fintype.sum_congr
  intro m
  have h : f.equivFun v m = f.repr v m := congrFun (Module.Basis.equivFun_apply f v) m
  exact congrArg (fun x => x * x) h

private theorem tfwe_dot_self_mulVec (f : Module.Basis (Fin 4) (ZMod p) V)
    {g : V ≃ₗ[ZMod p] V} (hg : IsIsom p (basisDiagForm f 1) g) (x : Fin 4 → ZMod p) :
    dotProduct ((LinearMap.toMatrix f f (g : V →ₗ[ZMod p] V)).mulVec x)
      ((LinearMap.toMatrix f f (g : V →ₗ[ZMod p] V)).mulVec x) = dotProduct x x := by
  have hv : ⇑(f.repr (f.equivFun.symm x)) = x := by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hM := LinearMap.toMatrix_mulVec_repr f f (g : V →ₗ[ZMod p] V) (f.equivFun.symm x)
  rw [hv] at hM
  have h := hg (f.equivFun.symm x)
  rw [tfwe_basisDiagForm_one_apply, tfwe_basisDiagForm_one_apply, hv] at h
  rw [hM]
  exact h

private theorem tfwe_dot_mulVec (hp : p ≠ 2) {M : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hM : ∀ x, dotProduct (M.mulVec x) (M.mulVec x) = dotProduct x x) (u v : Fin 4 → ZMod p) :
    dotProduct (M.mulVec u) (M.mulVec v) = dotProduct u v := by
  have h := hM (u + v)
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, hM u, hM v] at h
  have c1 := dotProduct_comm (M.mulVec v) (M.mulVec u)
  have c2 := dotProduct_comm v u
  apply mul_left_cancel₀ (ZMod.prime_ne_zero p 2 hp)
  linear_combination h - c1 + c2

private theorem tfwe_normOne_three :
    ∀ x : Fin 4 → ZMod 3, dotProduct x x = 1 →
      (∃ i, x = Pi.single i 1 ∨ x = -Pi.single i 1) ∨
        ((∀ i, x i = 1 ∨ x i = -1) ∧ (∏ i, x i = 1 ∨ ∏ i, x i = -1)) := by
  decide +kernel

private theorem tfwe_normOne_zero_three :
    ∀ x : Fin 4 → ZMod 3, dotProduct x x = 1 → ∀ m, x m = 0 →
      ∃ i, x = Pi.single i 1 ∨ x = -Pi.single i 1 := by
  decide +kernel

private theorem tfwe_two_mul_neg_one_three : (2 : ZMod 3) * -1 = 1 := by
  decide +kernel

private theorem tfwe_exists_frame_of_normOne_three (hp3 : p = 3) {x : Fin 4 → ZMod p}
    (hx : dotProduct x x = 1) : ∃ k : Fin 3, x ∈ (weylF4Frame k : Set (Fin 4 → ZMod p)) := by
  subst hp3
  rcases tfwe_normOne_three x hx with h | ⟨hε, hprod⟩
  · exact ⟨0, tfwe_mem_frame0_iff.mpr h⟩
  have hx2 : (2 : ZMod 3)⁻¹ • x = -x := by
    rw [inv_eq_of_mul_eq_one_right tfwe_two_mul_neg_one_three, neg_one_smul]
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, (2 : ZMod 3)⁻¹ • x ∈ (weylF4Frame k : Set (Fin 4 → ZMod 3)) := by
    rcases hprod with hprod | hprod
    exacts [⟨1, x, hε, hprod, rfl⟩, ⟨2, x, hε, hprod, rfl⟩]
  rw [hx2] at hk
  have h2 := tfwe_neg_mem_frame hk
  rw [neg_neg] at h2
  exact ⟨k, h2⟩

private theorem tfwe_col_mem_frame0_three (hp3 : p = 3) {M : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hM : ∀ x, dotProduct (M.mulVec x) (M.mulVec x) = dotProduct x x)
    (h0 : M.mulVec (Pi.single 0 1) ∈ (weylF4Frame 0 : Set (Fin 4 → ZMod p))) (j : Fin 4) :
    M.mulVec (Pi.single j 1) ∈ (weylF4Frame 0 : Set (Fin 4 → ZMod p)) := by
  subst hp3
  by_cases hj : j = 0
  · subst hj
    exact h0
  have hnorm : dotProduct (M.mulVec (Pi.single j 1)) (M.mulVec (Pi.single j 1)) = 1 := by
    rw [hM, single_one_dotProduct, Pi.single_eq_same]
  have he : dotProduct (Pi.single 0 1 : Fin 4 → ZMod 3) (Pi.single j 1) = 0 := by
    rw [single_one_dotProduct]
    simp [Ne.symm hj]
  have horth := tfwe_dot_mulVec (by decide) hM (Pi.single 0 1) (Pi.single j 1)
  rw [he] at horth
  obtain ⟨m, hm | hm⟩ := tfwe_mem_frame0_iff.mp h0
  · rw [hm, single_one_dotProduct] at horth
    exact tfwe_mem_frame0_iff.mpr (tfwe_normOne_zero_three _ hnorm m horth)
  · rw [hm, neg_dotProduct, single_one_dotProduct, neg_eq_zero] at horth
    exact tfwe_mem_frame0_iff.mpr (tfwe_normOne_zero_three _ hnorm m horth)

private theorem tfwe_mem_g2mmn_of_isIsom_three (hp3 : p = 3)
    (f : Module.Basis (Fin 4) (ZMod p) V) {g : V ≃ₗ[ZMod p] V}
    (hg : IsIsom p (basisDiagForm f 1) g)
    (h0 : (LinearMap.toMatrix f f (g : V →ₗ[ZMod p] V)).mulVec (Pi.single 0 1) ∈
      (weylF4Frame 0 : Set (Fin 4 → ZMod p))) : g ∈ g2mmn p f 0 1 1 := by
  have hp : p ≠ 2 := by omega
  refine mem_g2mmn_of_mapsTo_weylF4Frame_zero hp f fun x hx => ?_
  obtain ⟨j, rfl | rfl⟩ := tfwe_mem_frame0_iff.mp hx
  · exact tfwe_col_mem_frame0_three hp3 (tfwe_dot_self_mulVec f hg) h0 j
  · rw [Matrix.mulVec_neg]
    exact tfwe_neg_mem_frame (tfwe_col_mem_frame0_three hp3 (tfwe_dot_self_mulVec f hg) h0 j)

private theorem tfwe_mem_of_isIsom_three (hp3 : p = 3) (f : Module.Basis (Fin 4) (ZMod p) V)
    {g : V ≃ₗ[ZMod p] V} (hg : IsIsom p (basisDiagForm f 1) g) :
    g ∈ basisClosure f weylF4Mats := by
  have hp : p ≠ 2 := by omega
  have hnorm := tfwe_dot_self_mulVec f hg (Pi.single 0 1)
  rw [single_one_dotProduct, Pi.single_eq_same] at hnorm
  obtain ⟨k, hk⟩ := tfwe_exists_frame_of_normOne_three hp3 hnorm
  obtain ⟨w, hw, hwk⟩ := tfwe_exists_to_frame0 hp f k
  have hwg : IsIsom p (basisDiagForm f 1) (w * g) := by
    intro v
    rw [LinearEquiv.mul_apply, isIsom_basisDiagForm_of_mem_basisClosure f 1
      (weylF4Mats_orthogonal hp) hw (g v), hg v]
  have h0 : (LinearMap.toMatrix f f ((w * g : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V)).mulVec
      (Pi.single 0 1) ∈ (weylF4Frame 0 : Set (Fin 4 → ZMod p)) := by
    rw [toMatrix_coe_mul, ← Matrix.mulVec_mulVec]
    exact hwk _ hk
  have h := mul_mem (inv_mem hw)
    (g2mmn_le_basisClosure_weylF4 hp f (tfwe_mem_g2mmn_of_isIsom_three hp3 f hwg h0))
  rwa [inv_mul_cancel_left] at h

theorem isOrthType_basisClosure_weylF4_three (hp3 : p = 3) (f : Module.Basis (Fin 4) (ZMod p) V) :
    IsOrthType p (basisClosure f weylF4Mats) := by
  have hp : p ≠ 2 := by omega
  refine ⟨basisDiagForm f 1, basisDiagForm_nondegenerate hp f fun _ => one_ne_zero,
    Or.inl fun g => ⟨fun hg => ?_, tfwe_mem_of_isIsom_three hp3 f⟩⟩
  exact isIsom_basisDiagForm_of_mem_basisClosure f 1 (weylF4Mats_orthogonal hp) hg

private noncomputable def tfwe_toMatrixMonoidHom {n : ℕ} (g : Module.Basis (Fin n) (ZMod p) V) :
    (V →ₗ[ZMod p] V) →* Matrix (Fin n) (Fin n) (ZMod p) where
  toFun := LinearMap.toMatrix g g
  map_one' := LinearMap.toMatrix_one g
  map_mul' := LinearMap.toMatrix_mul g

private noncomputable def tfwe_glHom {n : ℕ} (g : Module.Basis (Fin n) (ZMod p) V) :
    (V ≃ₗ[ZMod p] V) →* Matrix.GeneralLinearGroup (Fin n) (ZMod p) :=
  (Units.map (tfwe_toMatrixMonoidHom g)).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) V).symm.toMonoidHom

private theorem tfwe_glHom_coe {n : ℕ} (g : Module.Basis (Fin n) (ZMod p) V)
    (h : V ≃ₗ[ZMod p] V) :
    ((tfwe_glHom g h : Matrix.GeneralLinearGroup (Fin n) (ZMod p)) :
      Matrix (Fin n) (Fin n) (ZMod p)) = LinearMap.toMatrix g g (h : V →ₗ[ZMod p] V) := by
  rw [tfwe_glHom, MonoidHom.comp_apply, Units.coe_map, tfwe_toMatrixMonoidHom]
  rfl

private theorem tfwe_glHom_injective {n : ℕ} (g : Module.Basis (Fin n) (ZMod p) V) :
    Function.Injective (tfwe_glHom g) := by
  intro x y hxy
  have hmat := congrArg (fun u : Matrix.GeneralLinearGroup (Fin n) (ZMod p) =>
    (u : Matrix (Fin n) (Fin n) (ZMod p))) hxy
  rw [tfwe_glHom_coe, tfwe_glHom_coe] at hmat
  exact LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix g g).injective hmat)

private theorem tfwe_glHom_surjective {n : ℕ} (g : Module.Basis (Fin n) (ZMod p) V) :
    Function.Surjective (tfwe_glHom g) := by
  intro A
  have hunit : IsUnit ((A : Matrix (Fin n) (Fin n) (ZMod p)).det) := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (A.det).isUnit
  refine ⟨Matrix.toLinearEquiv g (A : Matrix (Fin n) (Fin n) (ZMod p)) hunit, ?_⟩
  apply Units.ext
  rw [tfwe_glHom_coe]
  show LinearMap.toMatrix g g
    ((Matrix.toLinearEquiv g (A : Matrix (Fin n) (Fin n) (ZMod p)) hunit :
      V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = (A : Matrix (Fin n) (Fin n) (ZMod p))
  rw [show ((Matrix.toLinearEquiv g (A : Matrix (Fin n) (Fin n) (ZMod p)) hunit :
      V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = Matrix.toLin g g
        (A : Matrix (Fin n) (Fin n) (ZMod p)) from rfl, LinearMap.toMatrix_toLin]

private theorem tfwe_card_basisClosure_eq_card_closure {n : ℕ}
    (g : Module.Basis (Fin n) (ZMod p) V)
    (S : Set (Matrix (Fin n) (Fin n) (ZMod p))) :
    Nat.card (basisClosure g S) = Nat.card (Subgroup.closure
      {A : Matrix.GeneralLinearGroup (Fin n) (ZMod p) |
        (A : Matrix (Fin n) (Fin n) (ZMod p)) ∈ S}) := by
  have hmap : (basisClosure g S).map (tfwe_glHom g) = Subgroup.closure
      {A : Matrix.GeneralLinearGroup (Fin n) (ZMod p) |
        (A : Matrix (Fin n) (Fin n) (ZMod p)) ∈ S} := by
    rw [basisClosure, MonoidHom.map_closure]
    congr 1
    ext A
    constructor
    · rintro ⟨h, hh, rfl⟩
      simpa only [Set.mem_setOf_eq, tfwe_glHom_coe] using hh
    · intro hA
      obtain ⟨h, rfl⟩ := tfwe_glHom_surjective g A
      exact ⟨h, by simpa only [Set.mem_setOf_eq, tfwe_glHom_coe] using hA, rfl⟩
  rw [← hmap]
  exact (Subgroup.card_map_of_injective (tfwe_glHom_injective g)).symm

theorem card_basisClosure_blockSucc {W : Type} [AddCommGroup W] [Module (ZMod p) W] {n : ℕ}
    (f : Module.Basis (Fin (n + 1)) (ZMod p) W) (g : Module.Basis (Fin n) (ZMod p) V)
    (S : Set (Matrix (Fin n) (Fin n) (ZMod p))) :
    Nat.card (basisClosure f (Matrix.blockSucc '' S)) = Nat.card (basisClosure g S) := by
  let T : Set (Matrix.GeneralLinearGroup (Fin n) (ZMod p)) :=
    {A | (A : Matrix (Fin n) (Fin n) (ZMod p)) ∈ S}
  let T' : Set (Matrix.GeneralLinearGroup (Fin (n + 1)) (ZMod p)) :=
    {B | (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod p)) ∈ Matrix.blockSucc '' S}
  rw [tfwe_card_basisClosure_eq_card_closure g S,
    tfwe_card_basisClosure_eq_card_closure f (Matrix.blockSucc '' S)]
  change Nat.card (Subgroup.closure T') = Nat.card (Subgroup.closure T)
  have hT' : T' = TauCeti.glBlockSucc (ZMod p) n '' T := by
    ext B
    constructor
    · intro hB
      obtain ⟨A, hA, hAB⟩ := hB
      have hunit : IsUnit A.det := by
        rw [← Matrix.det_blockSucc A, hAB, ← Matrix.GeneralLinearGroup.val_det_apply]
        exact (B.det).isUnit
      refine ⟨Matrix.GeneralLinearGroup.mk'' A hunit, ?_, ?_⟩
      · change A ∈ S
        exact hA
      · apply Units.ext
        rw [TauCeti.coe_glBlockSucc]
        exact hAB
    · rintro ⟨A, hA, rfl⟩
      show ((TauCeti.glBlockSucc (ZMod p) n A : Matrix.GeneralLinearGroup (Fin (n + 1))
        (ZMod p)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod p)) ∈ Matrix.blockSucc '' S
      rw [TauCeti.coe_glBlockSucc]
      exact Set.mem_image_of_mem Matrix.blockSucc hA
  rw [hT', ← MonoidHom.map_closure]
  exact Subgroup.card_map_of_injective (TauCeti.glBlockSucc_injective (ZMod p) n)

theorem card_basisClosure_f4ExtMats (hp : p ≠ 2) {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (f : Module.Basis (Fin 5) (ZMod p) W) : Nat.card (basisClosure f f4ExtMats) = 1152 := by
  change Nat.card (basisClosure f (Matrix.blockSucc '' weylF4Mats)) = 1152
  rw [card_basisClosure_blockSucc f (Pi.basisFun (ZMod p) (Fin 4)) weylF4Mats]
  exact card_basisClosure_weylF4 hp (Pi.basisFun (ZMod p) (Fin 4))

end CFSG.StandardType.ZS.TableFacts

end
