
module

public import CFSG.Sporadic.Co1.Module.FormsBase1

public import CFSG.Sporadic.Co1.Module.Orbits
public import CFSG.Sporadic.Co1.Module.FormsInputs
public import Certificates.Certificate10069
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import Certificates.Data.CFSGNative.Co1.Data

public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

section Generic

variable {D : VecData} (hD : BaseFacts D)
include hD

end Generic

theorem q₀_eq_one_iff_mem_orbit
    (v : Vec24) : q₀ v = 1 ↔ v ∈ MulAction.orbit Jmat v₃ := by
  by_cases hv : v = 0
  · subst hv
    rw [q₀_zero]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (zero_not_mem_orbit v₃_ne_zero)⟩
  · rcases orbit_trichotomy hv with ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩
    · obtain ⟨g, rfl⟩ := h2
      rw [q₀_smul, q₀_v₂]
      exact ⟨fun h => absurd h (by decide), fun h => absurd h h3⟩
    · obtain ⟨g, rfl⟩ := h3
      rw [q₀_smul, q₀_v₃]
      exact ⟨fun _ => ⟨g, rfl⟩, fun _ => rfl⟩
    · obtain ⟨g, rfl⟩ := h4
      rw [q₀_smul, q₀_v₄]
      exact ⟨fun h => absurd h (by decide), fun h => absurd h h3⟩

theorem singular_eq_union :
    {v : Vec24 | q₀ v = 0 ∧ v ≠ 0} =
    MulAction.orbit Jmat v₂ ∪ MulAction.orbit Jmat v₄ := by
  ext v
  constructor
  · rintro ⟨h0, hv⟩
    rcases orbit_trichotomy hv with ⟨h2, -, -⟩ | ⟨-, h3, -⟩ | ⟨-, -, h4⟩
    · exact Or.inl h2
    · exact absurd ((q₀_eq_one_iff_mem_orbit v).2 h3) (by rw [h0]; decide)
    · exact Or.inr h4
  · intro h
    have hne : ∀ {w : Vec24}, w ≠ 0 → v ∈ MulAction.orbit Jmat w → v ≠ 0 := by
      rintro w hw hvw rfl
      exact zero_not_mem_orbit hw hvw
    rcases h with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact ⟨by rw [q₀_smul, q₀_v₂], hne v₂_ne_zero ⟨g, rfl⟩⟩
    · exact ⟨by rw [q₀_smul, q₀_v₄], hne v₄_ne_zero ⟨g, rfl⟩⟩

theorem co1_q₀_eq_one_iff
    (v : Vec24) :
    q₀ v = 1 ↔ v ∈ Set.range (fun g : NativeSporadic.Co1 => co1Act g v₃) := by
  rw [range_co1Act]
  exact q₀_eq_one_iff_mem_orbit v

theorem orbit_v₂_eq :
    MulAction.orbit Jmat v₂ = orbitVec 2 98280 '' {i | i < 98280} := by
  have := (orbit_spec orbitCheck_v₂).1
  rwa [toVecD_v₂] at this

theorem basis_row_mem_orbit
    (t : Fin 24) :
    (fun k => rowsMatrix 24 (basisRows dat) t k) ∈ MulAction.orbit Jmat v₂ := by
  have hlt : dat.basis[t.val]! < 98280 :=
    co1BaseFacts.basis_lt t.val (by rw [co1BaseFacts.basis_size]; exact t.isLt)
  rw [orbit_v₂_eq]
  refine ⟨dat.basis[t.val]!, hlt, ?_⟩
  funext k
  exact (basis_rowsMatrix co1BaseFacts t k).symm

theorem commutant_matrix
    {N : Matrix (Fin 24) (Fin 24) (ZMod 2)} (hA : matA * N = N * matA)
    (hB : matB * N = N * matB) : N = 0 ∨ N = 1 := by
  have hw1 : wordMat stabWord₁ *ᵥ (N *ᵥ v₂) = N *ᵥ v₂ := by
    rw [Matrix.mulVec_mulVec, commute_wordMat hA hB, ← Matrix.mulVec_mulVec, wordMat₁_mulVec]
  have hw2 : wordMat stabWord₂ *ᵥ (N *ᵥ v₂) = N *ᵥ v₂ := by
    rw [Matrix.mulVec_mulVec, commute_wordMat hA hB, ← Matrix.mulVec_mulVec, wordMat₂_mulVec]
  have hc := fixed_col hw1 hw2
  set c : ZMod 2 := (N *ᵥ v₂) 1 with hcdef
  have hJ : ∀ g : Jmat, N *ᵥ (g • v₂) = c • (g • v₂) := by
    intro g
    rw [smul_eq_mulVec, Matrix.mulVec_mulVec, ← commute_Jmat hA hB g.2, ← Matrix.mulVec_mulVec,
      hc, Matrix.mulVec_smul]
  have hP : N * (rowsMatrix 24 (basisRows dat))ᵀ = c • (rowsMatrix 24 (basisRows dat))ᵀ := by
    ext j t
    obtain ⟨g, hg⟩ := basis_row_mem_orbit t
    have := congrFun (hJ g) j
    rw [show g • v₂ = _ from hg] at this
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  have hinvT : (rowsMatrix 24 (basisRows dat))ᵀ * (rowsMatrix 24 dat.basisInv)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, basis_inv_mul, Matrix.transpose_one]
  have hN : N = c • 1 := by
    calc N = N * ((rowsMatrix 24 (basisRows dat))ᵀ * (rowsMatrix 24 dat.basisInv)ᵀ) := by
          rw [hinvT, Matrix.mul_one]
      _ = (N * (rowsMatrix 24 (basisRows dat))ᵀ) * (rowsMatrix 24 dat.basisInv)ᵀ := by
          rw [Matrix.mul_assoc]
      _ = c • 1 := by rw [hP, Matrix.smul_mul, hinvT]
  rcases zmod2_cases c with h | h
  · left
    rw [hN, h, zero_smul]
  · right
    rw [hN, h, one_smul]

theorem commutant_linearMap
    {f : Vec24 →ₗ[ZMod 2] Vec24}
    (hA : ∀ v, f (matA *ᵥ v) = matA *ᵥ f v) (hB : ∀ v, f (matB *ᵥ v) = matB *ᵥ f v) :
    f = 0 ∨ f = LinearMap.id := by
  have hN : ∀ M : Matrix (Fin 24) (Fin 24) (ZMod 2), (∀ v, f (M *ᵥ v) = M *ᵥ f v) →
      M * LinearMap.toMatrix' f = LinearMap.toMatrix' f * M := by
    intro M hM
    apply matrix_ext_mulVec
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec,
      LinearMap.toMatrix'_mulVec, hM]
  rcases commutant_matrix (hN _ hA) (hN _ hB) with h | h
  · left
    rw [← Matrix.toLin'_toMatrix' f, h, map_zero]
  · right
    rw [← Matrix.toLin'_toMatrix' f, h, Matrix.toLin'_one]

theorem invariant_form_matrix
    (F : Matrix (Fin 24) (Fin 24) (ZMod 2)) :
    (matAᵀ * F * matA = F ∧ matBᵀ * F * matB = F) ↔ (F = 0 ∨ F = F₀) := by
  constructor
  · rintro ⟨hFA, hFB⟩
    have hMA : matA * (F₀inv * F) = (F₀inv * F) * matA :=
      commute_of_inv (S := matA) (S' := matA) matA_mul_self F₀_invariant_A hFA F₀inv_mul
        F₀_mul_inv
    have hMB' : (matB * matB) * (F₀inv * F) = (F₀inv * F) * (matB * matB) :=
      commute_of_inv (S := matB) (S' := matB * matB) matB_mul_mul F₀_invariant_B hFB F₀inv_mul
        F₀_mul_inv
    have hB3 : matB * matB * matB = 1 := by
      rw [Matrix.mul_assoc]
      exact matB_mul_mul
    have hB4 : (matB * matB) * (matB * matB) = matB := by
      rw [← Matrix.mul_assoc, hB3, Matrix.one_mul]
    have hMB : matB * (F₀inv * F) = (F₀inv * F) * matB := by
      calc matB * (F₀inv * F) = ((matB * matB) * (matB * matB)) * (F₀inv * F) := by rw [hB4]
        _ = (matB * matB) * ((matB * matB) * (F₀inv * F)) := by rw [Matrix.mul_assoc]
        _ = (matB * matB) * ((F₀inv * F) * (matB * matB)) := by rw [hMB']
        _ = ((matB * matB) * (F₀inv * F)) * (matB * matB) := (Matrix.mul_assoc _ _ _).symm
        _ = ((F₀inv * F) * (matB * matB)) * (matB * matB) := by rw [hMB']
        _ = (F₀inv * F) * ((matB * matB) * (matB * matB)) := by rw [Matrix.mul_assoc]
        _ = (F₀inv * F) * matB := by rw [hB4]
    have hF : F = F₀ * (F₀inv * F) := by
      rw [← Matrix.mul_assoc, F₀_mul_inv, Matrix.one_mul]
    rcases commutant_matrix hMA hMB with h | h
    · left
      rw [hF, h, Matrix.mul_zero]
    · right
      rw [hF, h, Matrix.mul_one]
  · rintro (rfl | rfl)
    · simp
    · exact ⟨F₀_invariant_A, F₀_invariant_B⟩

theorem invariant_biadditive
    {B : Vec24 → Vec24 → ZMod 2}
    (h1 : ∀ u u' v, B (u + u') v = B u v + B u' v) (h2 : ∀ u v v', B u (v + v') = B u v + B u v')
    (hA : ∀ u v, B (matA *ᵥ u) (matA *ᵥ v) = B u v)
    (hB : ∀ u v, B (matB *ᵥ u) (matB *ᵥ v) = B u v) : B = 0 ∨ B = bil₀ := by
  set F : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
    Matrix.of fun i j => B (Pi.single i 1) (Pi.single j 1) with hF
  have hexp : ∀ u v, B u v = u ⬝ᵥ (F *ᵥ v) := by
    intro u v
    rw [biadditive_expand h1 h2 u v]
    simp only [dotProduct, Matrix.mulVec, hF, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hinv : ∀ M : Matrix (Fin 24) (Fin 24) (ZMod 2),
      (∀ u v, B (M *ᵥ u) (M *ᵥ v) = B u v) → Mᵀ * F * M = F := by
    intro M hM
    ext i j
    have h := hM (Pi.single i 1) (Pi.single j 1)
    rw [hexp, hexp, dot_conj, single_dot_mulVec_single] at h
    rw [h]
    simp [hF]
  rcases (invariant_form_matrix F).1 ⟨hinv _ hA, hinv _ hB⟩ with h | h
  · left
    funext u v
    rw [hexp, h]
    simp
  · right
    funext u v
    rw [hexp, h]
    rfl

theorem invariant_bilinForm
    {B : LinearMap.BilinForm (ZMod 2) Vec24}
    (hA : ∀ u v, B (matA *ᵥ u) (matA *ᵥ v) = B u v)
    (hB : ∀ u v, B (matB *ᵥ u) (matB *ᵥ v) = B u v) : B = 0 ∨ B = Matrix.toBilin' F₀ := by
  rcases invariant_biadditive (B := fun u v => B u v) (fun u u' v => by simp)
    (fun u v v' => by simp) hA hB with h | h
  · left
    refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
    exact congrFun (congrFun h u) v
  · right
    refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
    rw [Matrix.toBilin'_apply']
    exact congrFun (congrFun h u) v

theorem invariant_biadditive_Jmat
    {B : Vec24 → Vec24 → ZMod 2}
    (h1 : ∀ u u' v, B (u + u') v = B u v + B u' v) (h2 : ∀ u v v', B u (v + v') = B u v + B u v')
    (hinv : ∀ (g : Jmat) (u v : Vec24), B (g • u) (g • v) = B u v) : B = 0 ∨ B = bil₀ := by
  have hA : ∀ u v, B (matA *ᵥ u) (matA *ᵥ v) = B u v := by
    intro u v
    have := hinv genA u v
    rwa [smul_eq_mulVec, smul_eq_mulVec, genA_val] at this
  have hB : ∀ u v, B (matB *ᵥ u) (matB *ᵥ v) = B u v := by
    intro u v
    have := hinv genB u v
    rwa [smul_eq_mulVec, smul_eq_mulVec, genB_val] at this
  exact invariant_biadditive h1 h2 hA hB

theorem co1_invariant_biadditive
    {B : Vec24 → Vec24 → ZMod 2}
    (h1 : ∀ u u' v, B (u + u') v = B u v + B u' v) (h2 : ∀ u v v', B u (v + v') = B u v + B u v')
    (hinv : ∀ (g : NativeSporadic.Co1) (u v : Vec24), B (co1Act g u) (co1Act g v) = B u v) :
    B = 0 ∨ B = bil₀ := by
  obtain ⟨a, ha⟩ := exists_co1_matA
  obtain ⟨b, hb⟩ := exists_co1_matB
  refine invariant_biadditive h1 h2 (fun u v => ?_) (fun u v => ?_)
  · have := hinv a u v
    rwa [co1Act, co1Act, ha] at this
  · have := hinv b u v
    rwa [co1Act, co1Act, hb] at this

theorem invariant_quadratic
    {q : Vec24 → ZMod 2}
    (hbil : ∀ u u' v, polar q (u + u') v = polar q u v + polar q u' v)
    (hA : ∀ v, q (matA *ᵥ v) = q v) (hB : ∀ v, q (matB *ᵥ v) = q v) : q = 0 ∨ q = q₀ := by
  have h2 : ∀ u v v', polar q u (v + v') = polar q u v + polar q u v' := by
    intro u v v'
    rw [polar_comm q u (v + v'), hbil, polar_comm q v u, polar_comm q v' u]
  have hinv : ∀ M : Matrix (Fin 24) (Fin 24) (ZMod 2), (∀ v, q (M *ᵥ v) = q v) →
      ∀ u v, polar q (M *ᵥ u) (M *ᵥ v) = polar q u v := by
    intro M hM u v
    simp only [polar, ← Matrix.mulVec_add, hM]
  rcases invariant_biadditive hbil h2 (hinv _ hA) (hinv _ hB) with h | h
  · left
    have hadd : ∀ u v, q (u + v) = q u + q v := by
      intro u v
      have := congrFun (congrFun h u) v
      simp only [polar, Pi.zero_apply] at this
      linear_combination this
    exact invariant_additive_zero hadd hA hB
  · right
    have hadd : ∀ u v, (q + q₀) (u + v) = (q + q₀) u + (q + q₀) v := by
      intro u v
      have h1 := congrFun (congrFun h u) v
      simp only [polar] at h1
      have h3 : bil₀ u v + bil₀ u v = 0 := CharTwo.add_self_eq_zero _
      simp only [Pi.add_apply]
      rw [q₀_add]
      linear_combination h1 + h3
    have h0 := invariant_additive_zero (r := q + q₀) hadd
      (fun v => by simp only [Pi.add_apply, hA, q₀_invariant_A])
      (fun v => by simp only [Pi.add_apply, hB, q₀_invariant_B])
    funext v
    have := congrFun h0 v
    simp only [Pi.add_apply, Pi.zero_apply] at this
    have h4 : q v = - q₀ v := eq_neg_of_add_eq_zero_left this
    rw [h4]
    exact CharTwo.neg_eq _

theorem invariant_quadraticForm
    {Q : QuadraticForm (ZMod 2) (Fin 24 → ZMod 2)}
    (hA : ∀ v, Q (matA *ᵥ v) = Q v) (hB : ∀ v, Q (matB *ᵥ v) = Q v) : Q = 0 ∨ Q = q₀Form := by
  rcases invariant_quadratic (q := fun x => Q x) (polar_add_left_form Q) hA hB with h | h
  · left
    ext v
    exact congrFun h v
  · right
    ext v
    rw [q₀Form_apply]
    exact congrFun h v

theorem invariant_quadratic_Jmat
    {q : Vec24 → ZMod 2}
    (hbil : ∀ u u' v, polar q (u + u') v = polar q u v + polar q u' v)
    (hinv : ∀ (g : Jmat) (v : Vec24), q (g • v) = q v) : q = 0 ∨ q = q₀ :=
  invariant_quadratic hbil (invariant_gen_of_Jmat hinv).1 (invariant_gen_of_Jmat hinv).2

theorem co1_invariant_quadratic
    {q : Vec24 → ZMod 2}
    (hbil : ∀ u u' v, polar q (u + u') v = polar q u v + polar q u' v)
    (hinv : ∀ (g : NativeSporadic.Co1) (v : Vec24), q (co1Act g v) = q v) : q = 0 ∨ q = q₀ :=
  invariant_quadratic hbil (invariant_gen_of_Co1 hinv).1 (invariant_gen_of_Co1 hinv).2

section Generic

variable {D : VecData} (hD : BaseFacts D)
include hD

end Generic

theorem ncard_q₀_eq_one :
    {v : Vec24 | q₀ v = 1}.ncard = 8386560 := by
  have h : {v : Vec24 | q₀ v = 1} = MulAction.orbit Jmat v₃ := Set.ext q₀_eq_one_iff_mem_orbit
  rw [h]
  exact orbit_ncard_v₃

theorem ncard_singular :
    {v : Vec24 | q₀ v = 0 ∧ v ≠ 0}.ncard = 8390655 := by
  rw [singular_eq_union, Set.ncard_union_eq disjoint_orbit_v₂_v₄, orbit_ncard_v₂, orbit_ncard_v₄]

theorem commutant_Jmat_matrix
    {N : Matrix (Fin 24) (Fin 24) (ZMod 2)}
    (h : ∀ g : Jmat, ((g : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) * N =
      N * ((g : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2))) : N = 0 ∨ N = 1 := by
  refine commutant_matrix ?_ ?_
  · have := h genA
    rwa [genA_val] at this
  · have := h genB
    rwa [genB_val] at this

theorem co1_commutant_matrix
    {N : Matrix (Fin 24) (Fin 24) (ZMod 2)}
    (h : ∀ g : NativeSporadic.Co1, (g.val.val : Matrix (Fin 24) (Fin 24) (ZMod 2)) * N =
      N * (g.val.val : Matrix (Fin 24) (Fin 24) (ZMod 2))) : N = 0 ∨ N = 1 := by
  obtain ⟨a, ha⟩ := exists_co1_matA
  obtain ⟨b, hb⟩ := exists_co1_matB
  refine commutant_matrix ?_ ?_
  · have := h a
    rwa [ha] at this
  · have := h b
    rwa [hb] at this

end CFSG.Sporadic.Co1.Module
