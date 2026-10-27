module

public import CFSG.Quasithin.Background.RonanH43Trv
public import CFSG.Quasithin.Background.RonanH43Fin

public section

namespace CFSG.Quasithin.RonanH43

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SL3Pair CFSG.Quasithin.H.SL3One CFSG.Open
  CFSG.Assembly.LowTwoRank Matrix

theorem exists_gl_mulVec_eq {c : Fin 3 → ZMod 2} (hc : c ≠ 0) :
    ∃ k : GL (Fin 3) (ZMod 2), (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ c = e0 := by
  obtain ⟨M, hM, hMc⟩ := exists_mulVec_eq_single c hc
  have hinj : Function.Injective M.mulVec := by
    intro v w h
    have : M *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub, sub_eq_zero]; exact h
    exact sub_eq_zero.mp (hM _ this)
  have hu : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact ⟨hu.unit, by rw [IsUnit.unit_spec]; exact hMc⟩

theorem conj_trv (k γ : GL (Fin 3) (ZMod 2)) {c φ : Fin 3 → ZMod 2} (hφc : φ ⬝ᵥ c = 0)
    (hγ : (γ : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec c φ)
    (hk : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ c = e0) :
    ∃ (ψ : Fin 3 → ZMod 2) (h : ψ 0 = 0), pairHom (k * γ * k⁻¹) = trv0 ψ h := by
  have hk' : ((k⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e0 = c := by
    rw [← hk, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hψ : (φ ᵥ* ((k⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) 0 = 0 := by
    have : (φ ᵥ* ((k⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) ⬝ᵥ e0 = 0 := by
      rw [← Matrix.dotProduct_mulVec, hk', hφc]
    rwa [dotProduct_single, mul_one] at this
  refine ⟨φ ᵥ* ((k⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)), hψ, ?_⟩
  unfold trv0
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hγ, coe_trvGL, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hk]

theorem reduce2 {M A : Subgroup (MulAut PV)} (hLM : pairSL (ZMod 2) ≤ M)
    (hsM : swapAut (ZMod 2) ∈ M) (hA2 : IsElemAbelian2 A) (hA4 : Nat.card A = 4)
    (hAL : A ≤ pairSL (ZMod 2)) :
    ∃ g ∈ M, Nat.card (conjR g A) = 4 ∧
      ∀ y ∈ conjR g A, ∃ φ : Fin 3 → ZMod 2, ∃ h : φ 0 = 0, y = trv0 φ h := by
  classical
  set E₀ : Subgroup (GL (Fin 3) (ZMod 2)) := A.comap pairHom with hE₀def
  have hrange : A ≤ pairHom.range := fun x hx => by
    obtain ⟨γ, -, hγ⟩ := hAL hx
    exact ⟨γ, hγ⟩
  have hE₀card : Nat.card E₀ = 4 := by
    have h1 : E₀.map pairHom = A := Subgroup.map_comap_eq_self hrange
    have h2 := Subgroup.card_map_of_injective (K := E₀) (pairHom_injective (K := ZMod 2))
    rw [h1, hA4] at h2
    exact h2.symm
  have hsq : ∀ A' ∈ E₀, A' * A' = 1 := fun A' hA' => pairHom_injective (by
    rw [map_mul, map_one, ← sq]
    exact hA2.2 _ hA')
  have hcomm : ∀ A' ∈ E₀, ∀ B' ∈ E₀, A' * B' = B' * A' := fun A' hA' B' hB' =>
    pairHom_injective (by
      rw [map_mul, map_mul]
      exact hA2.1 _ hA' _ hB')
  have hcard : ∀ g : MulAut PV, Nat.card (conjR g A) = 4 := fun g => by
    rw [conjR, Subgroup.card_map_of_injective (MulAut.conj g).injective, hA4]
  have hmem : ∀ {y : MulAut PV} {g : MulAut PV}, y ∈ conjR g A →
      ∃ γ ∈ E₀, y = g * pairHom γ * g⁻¹ := by
    intro y g hy
    obtain ⟨x, hxA, rfl⟩ := mem_conjR.mp hy
    obtain ⟨γ, -, rfl⟩ := hAL hxA
    exact ⟨γ, hxA, rfl⟩
  rcases center_or_axis E₀ hsq hcomm (by rw [card_zmod_two, hE₀card]; norm_num) with
    ⟨c, hc, hcen⟩ | ⟨ψ, hψ, hax⟩
  ·
    obtain ⟨k, hk⟩ := exists_gl_mulVec_eq hc
    refine ⟨pairHom k, hLM (pairHom_mem_pairSL k), hcard _, fun y hy => ?_⟩
    obtain ⟨γ, hγ, rfl⟩ := hmem hy
    obtain ⟨φ, hφc, hγe⟩ := hcen γ hγ
    obtain ⟨ψ, hψ0, he⟩ := conj_trv k γ hφc hγe hk
    refine ⟨ψ, hψ0, ?_⟩
    rw [← he, map_mul, map_mul, map_inv]
  ·
    obtain ⟨k, hk⟩ := exists_gl_mulVec_eq hψ
    refine ⟨pairHom k * swapAut (ZMod 2), Subgroup.mul_mem _ (hLM (pairHom_mem_pairSL k)) hsM,
      hcard _, fun y hy => ?_⟩
    obtain ⟨γ, hγ, rfl⟩ := hmem hy
    obtain ⟨w, hwψ, hγe⟩ := hax γ hγ
    have hγinv : γ⁻¹ = γ := inv_eq_of_mul_eq_one_right (hsq γ hγ)
    have hdγ : ((dualGL γ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        1 + vecMulVec ψ w := by
      rw [coe_dualGL, hγinv, hγe, Matrix.transpose_add, Matrix.transpose_one,
        Matrix.transpose_vecMulVec]
    obtain ⟨ψ', hψ0, he⟩ := conj_trv k (dualGL γ) (by rw [dotProduct_comm]; exact hwψ) hdγ hk
    refine ⟨ψ', hψ0, ?_⟩
    have e := swapAut_conj (K := ZMod 2) γ
    rw [← he, map_mul, map_mul, map_inv, ← e]
    simp only [_root_.mul_inv_rev, swapAut_inv, mul_assoc]

end CFSG.Quasithin.RonanH43
