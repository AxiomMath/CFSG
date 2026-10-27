module

public import CFSG.Quasithin.Background.FLcModel

public section

namespace CFSG.Quasithin.FLc

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem proj_injective_two (n : ℕ) : Function.Injective (proj n (ZMod 2)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj,
    CFSG.LieType.SteinbergBR.BinaryLinear.scalars_eq_bot (Nat.card_zmod 2)]

theorem mem_map_mulEquiv_iff {G : Type*} [Group G] (f : G ≃* G) (K : Subgroup G) (x : G) :
    x ∈ K.map (f : G →* G) ↔ f.symm x ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨f.symm x, h, by simp⟩

theorem mem_Ut_of_conj {n : ℕ} (a : SLt n) (φ : SLt n ≃* SLt n)
    (hφ : (Ut n).map φ.toMonoidHom = Ut n) (hconj : ∀ g, φ g = a * g * a⁻¹) : a ∈ Ut n := by
  have hN : a ∈ Subgroup.normalizer ((Ut n : Subgroup (SLt n)) : Set (SLt n)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 : φ h ∈ (Ut n).map φ.toMonoidHom := Subgroup.mem_map_of_mem _ hh
      rw [hφ, hconj] at h1
      exact h1
    · intro hh
      have h1 : a * h * a⁻¹ ∈ (Ut n).map φ.toMonoidHom := by
        rw [hφ]
        exact hh
      obtain ⟨v, hv, hvh⟩ := h1
      have h2 : a * v * a⁻¹ = a * h * a⁻¹ := by
        rw [← hconj]
        exact hvh
      have h3 : v = h := mul_left_cancel (mul_right_cancel h2)
      rw [← h3]
      exact hv
  have hN' := hN
  rw [normalizer_unitriangular, upperTriangular_eq_Ut] at hN'
  exact hN'

theorem aut_dichotomy {n : ℕ} (hn : 3 ≤ n) (φ : SLt n ≃* SLt n)
    (hφ : (Ut n).map φ.toMonoidHom = Ut n) :
    (∃ b ∈ Ut n, ∀ g, φ g = b * g * b⁻¹) ∨
      ∀ d, 1 ≤ d → d < n → (stabilizer (flagSpace n (ZMod 2) d)).map φ.toMonoidHom =
        stabilizer (flagSpace n (ZMod 2) (n - d)) := by
  classical
  let φ' : MulAut (projectiveSL n (ZMod 2)) := descendAut n (ZMod 2) φ
  have hφ'proj : ∀ g, φ' (proj n (ZMod 2) g) = proj n (ZMod 2) (φ g) := fun g =>
    descendAut_proj n (ZMod 2) φ g
  obtain ⟨A, σ, ε, hε, hA⟩ := (automorphism_generation (K := ZMod 2) hn).2 φ'
  have hσ : σ = 1 := Subsingleton.elim _ _
  rw [hσ, map_one, mul_one] at hA
  obtain ⟨A', hA'⟩ : ∃ A' : SLt n, Matrix.SpecialLinearGroup.toGL A' = A :=
    ⟨(slEquivGLt n).symm A, (slEquivGLt n).apply_symm_apply A⟩
  interval_cases ε
  ·
    left
    rw [pow_zero, mul_one] at hA
    have hconj : ∀ g, φ g = A' * g * A'⁻¹ := by
      intro g
      apply proj_injective_two n
      rw [← hφ'proj, hA, ← hA', conjAut_toGL, MulAut.conj_apply, map_mul, map_mul, map_inv]
    exact ⟨A', mem_Ut_of_conj A' φ hφ hconj, hconj⟩
  ·
    right
    intro d hd1 hdn
    rw [pow_one] at hA
    obtain ⟨-, -, -, -, -, -, hconjT, -, hdualT, -⟩ :=
      standard_automorphism_transport (K := ZMod 2) (n := n)
    set W : Submodule (ZMod 2) (Fin n → ZMod 2) :=
      (dotOrth (flagSpace n (ZMod 2) d)).map (mulVecLin (A : Matrix (Fin n) (Fin n) (ZMod 2)))
      with hW
    have hmapP : (projStabilizer (flagSpace n (ZMod 2) d)).map (φ' : projectiveSL n (ZMod 2) →*
        projectiveSL n (ZMod 2)) = projStabilizer W := by
      have h1 : (φ' : projectiveSL n (ZMod 2) →* projectiveSL n (ZMod 2)) =
          (conjAut n (ZMod 2) A : projectiveSL n (ZMod 2) →* projectiveSL n (ZMod 2)).comp
            (dualAut n (ZMod 2) : projectiveSL n (ZMod 2) →* projectiveSL n (ZMod 2)) := by
        rw [hA]
        rfl
      rw [h1, ← Subgroup.map_map, hdualT, hconjT]
    have hmapU : (projUnitriangular n (ZMod 2)).map (φ' : projectiveSL n (ZMod 2) →*
        projectiveSL n (ZMod 2)) = projUnitriangular n (ZMod 2) := by
      rw [projUnitriangular, Subgroup.map_map]
      have h1 : (φ' : projectiveSL n (ZMod 2) →* projectiveSL n (ZMod 2)).comp
          (proj n (ZMod 2)) = (proj n (ZMod 2)).comp φ.toMonoidHom := by
        ext g
        exact hφ'proj g
      rw [h1, ← Subgroup.map_map, hφ]
    have hUle : projUnitriangular n (ZMod 2) ≤ projStabilizer (flagSpace n (ZMod 2) d) := by
      rw [projUnitriangular, projStabilizer]
      exact Subgroup.map_mono
        ((unitriangular_le_upperTriangular n (ZMod 2)).trans
          (upperTriangular_le_stabilizer_flagSpace d))
    have hUW : projUnitriangular n (ZMod 2) ≤ projStabilizer W := by
      rw [← hmapP, ← hmapU]
      exact Subgroup.map_mono hUle
    have hinv : ∀ u ∈ unitriangular n (ZMod 2), ∀ v ∈ W,
        (u : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v ∈ W := by
      intro u hu v hv
      have h1 : proj n (ZMod 2) u ∈ projStabilizer W := hUW ⟨u, hu, rfl⟩
      have h2 : u ∈ stabilizer W := by
        rw [← comap_projStabilizer]
        exact h1
      have h3 := mem_stabilizer.1 h2
      rw [← h3]
      exact ⟨v, hv, rfl⟩
    obtain ⟨m, hm, hWm⟩ := eq_flagSpace_of_invariant hinv
    have hdim : finrank (ZMod 2) W = n - d := by
      have h1 : finrank (ZMod 2) W = finrank (ZMod 2) (dotOrth (flagSpace n (ZMod 2) d)) := by
        have : (A : Matrix (Fin n) (Fin n) (ZMod 2)) = mat A' := by
          rw [← hA']
          rfl
        rw [hW, this]
        exact finrank_map_mulVecLin A' _
      rw [h1, finrank_dotOrth, finrank_flagSpace hdn.le]
    have hmn : m = n - d := by
      have := hdim
      rw [hWm, finrank_flagSpace hm] at this
      exact this
    have hmapP' : (projStabilizer (flagSpace n (ZMod 2) d)).map (φ' : projectiveSL n (ZMod 2) →*
        projectiveSL n (ZMod 2)) = projStabilizer (flagSpace n (ZMod 2) (n - d)) := by
      rw [hmapP, hWm, hmn]
    ext g
    rw [Subgroup.mem_map_equiv]
    have hsymm : φ'.symm (proj n (ZMod 2) g) = proj n (ZMod 2) (φ.symm g) := by
      rw [MulEquiv.symm_apply_eq, hφ'proj, MulEquiv.apply_symm_apply]
    have hiff : ∀ (e : ℕ) (x : SLt n), x ∈ stabilizer (flagSpace n (ZMod 2) e) ↔
        proj n (ZMod 2) x ∈ projStabilizer (flagSpace n (ZMod 2) e) := fun e x => by
      rw [← comap_projStabilizer, Subgroup.mem_comap]
    rw [hiff (n - d) g, ← hmapP', mem_map_mulEquiv_iff, hiff d, ← hsymm]

end CFSG.Quasithin.FLc
