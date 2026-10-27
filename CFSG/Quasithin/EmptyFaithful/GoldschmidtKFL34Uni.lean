module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldFourFixed

public section

namespace CFSG.Quasithin.SBd19F

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
open scoped commutatorElement

variable {k : Type} [Field k]

@[expose] noncomputable def wPHom (k : Type) [Field k] : Multiplicative k →* projectiveSL 3 k where
  toFun c := wP (Multiplicative.toAdd c)
  map_one' := (wP_eq_one_iff 0).mpr rfl
  map_mul' _ _ := wP_add _ _

@[expose] noncomputable def wSub (k : Type) [Field k] : Subgroup (projectiveSL 3 k) :=
  (wPHom k).range

theorem mem_wSub_iff {z : projectiveSL 3 k} : z ∈ wSub k ↔ ∃ c : k, z = wP c := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.toAdd c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, rfl⟩

theorem wP_mem_wSub (c : k) : wP c ∈ wSub k := mem_wSub_iff.mpr ⟨c, rfl⟩

theorem card_wSub : Nat.card (wSub k) = Nat.card k := by
  have hinj : Function.Injective (wPHom k) := fun a b hab => by
    have h : wP (Multiplicative.toAdd (a * b⁻¹)) = 1 := by
      change wPHom k (a * b⁻¹) = 1
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have := (wP_eq_one_iff _).mp h
    rw [toAdd_mul, toAdd_inv, add_neg_eq_zero] at this
    exact Multiplicative.toAdd.injective this
  rw [wSub, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

theorem xMat_mem_unitriangular (a : k) : xMat a ∈ unitriangular 3 k := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [xMat, xM]
  · fin_cases i <;> simp [xMat, xM]

theorem yMat_mem_unitriangular (b : k) : yMat b ∈ unitriangular 3 k := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [yMat, yM]
  · fin_cases i <;> simp [yMat, yM]

theorem wMat_mem_unitriangular (c : k) : wMat c ∈ unitriangular 3 k := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [wMat, wM]
  · fin_cases i <;> simp [wMat, wM]

theorem xP_mem (a : k) : xP a ∈ projUnitriangular 3 k :=
  Subgroup.mem_map_of_mem _ (xMat_mem_unitriangular a)

theorem yP_mem (b : k) : yP b ∈ projUnitriangular 3 k :=
  Subgroup.mem_map_of_mem _ (yMat_mem_unitriangular b)

theorem exists_comm_of_mem_wSub {z : projectiveSL 3 k} (hz : z ∈ wSub k) :
    ∃ a ∈ projUnitriangular 3 k, ∃ b ∈ projUnitriangular 3 k, z = a * b * a⁻¹ * b⁻¹ := by
  obtain ⟨c, rfl⟩ := mem_wSub_iff.mp hz
  refine ⟨xP c, xP_mem c, yP 1, yP_mem 1, ?_⟩
  have h := commutatorElement_xP_yP c 1
  rw [mul_one] at h
  rw [← h, commutatorElement_def]

theorem wP_one_comm {s : projectiveSL 3 k} (hs : s ∈ projUnitriangular 3 k) :
    s * wP 1 = wP 1 * s := by
  obtain ⟨A, hA, rfl⟩ := hs
  rw [wP, ← map_mul, ← map_mul, wMat_one_mul_comm hA]

theorem unitriangular_sq [CharP k 2] {A : SpecialLinearGroup (Fin 3) k}
    (hA : A ∈ unitriangular 3 k) :
    A * A = wMat ((A : Matrix (Fin 3) (Fin 3) k) 0 1 * (A : Matrix (Fin 3) (Fin 3) k) 1 2) := by
  obtain ⟨hlow, hdiag⟩ := hA
  have h10 := hlow 1 0 (by decide)
  have h20 := hlow 2 0 (by decide)
  have h21 := hlow 2 1 (by decide)
  have h00 := hdiag 0
  have h11 := hdiag 1
  have h22 := hdiag 2
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  change (A : Matrix (Fin 3) (Fin 3) k) * (A : Matrix (Fin 3) (Fin 3) k) = wM _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, wM, h10, h20, h21, h00, h11, h22] <;>
    first
      | linear_combination (A : Matrix (Fin 3) (Fin 3) k) 0 1 * h2
      | linear_combination (A : Matrix (Fin 3) (Fin 3) k) 0 2 * h2
      | linear_combination (A : Matrix (Fin 3) (Fin 3) k) 1 2 * h2

theorem sq_mem_wSub [CharP k 2] {s : projectiveSL 3 k} (hs : s ∈ projUnitriangular 3 k) :
    s * s ∈ wSub k := by
  obtain ⟨A, hA, rfl⟩ := hs
  rw [← map_mul, unitriangular_sq hA]
  exact wP_mem_wSub _

theorem exists_lift_of_mem_not_mem {s : projectiveSL 3 k} (hs : s ∈ projUnitriangular 3 k)
    (hsZ : s ∉ wSub k) :
    ∃ A ∈ unitriangular 3 k, proj 3 k A = s ∧
      ¬ ((A : Matrix (Fin 3) (Fin 3) k) 0 1 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) k) 1 2 = 0) := by
  obtain ⟨A, hA, rfl⟩ := hs
  refine ⟨A, hA, rfl, fun ⟨h01, h12⟩ => hsZ ?_⟩
  obtain ⟨hlow, hdiag⟩ := hA
  have h10 := hlow 1 0 (by decide)
  have h20 := hlow 2 0 (by decide)
  have h21 := hlow 2 1 (by decide)
  have h00 := hdiag 0
  have h11 := hdiag 1
  have h22 := hdiag 2
  have : A = wMat ((A : Matrix (Fin 3) (Fin 3) k) 0 2) := by
    apply Subtype.ext
    change (A : Matrix (Fin 3) (Fin 3) k) = wM _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [wM, h10, h20, h21, h00, h11, h22, h01, h12]
  rw [this]
  exact wP_mem_wSub _

end CFSG.Quasithin.SBd19F
