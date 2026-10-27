module

public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Std
public import CFSG.Quasithin.H13.A5S136sp3

public section

namespace CFSG.Quasithin.H13.A5.SpBorel

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauAut tauAut_proj tauMat_apply)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K]

@[expose] def zC (c₁ c₂ : K) : Matrix (Fin 2) (Fin 2) K := !![c₁, c₂; c₂, 0]

theorem zC_symm (c₁ c₂ : K) : (zC c₁ c₂)ᵀ = zC c₁ c₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] noncomputable def zElt (c₁ c₂ : K) : StatedSp 2 K :=
  blockElt (A := 1) (by rw [det_one]; exact isUnit_one) (zC_symm c₁ c₂)

theorem coe_zElt (c₁ c₂ : K) :
    (((zElt c₁ c₂ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks 1 (zC c₁ c₂) 0 1 := by
  rw [zElt, coe_blockElt, blockMat]
  simp

theorem zElt_mem_unipotent (c₁ c₂ : K) : zElt c₁ c₂ ∈ unipotent 2 K :=
  ⟨1, zC c₁ c₂, isUnitriangular_one, zC_symm c₁ c₂, by rw [zElt, coe_blockElt]⟩

theorem zElt_inj {c₁ c₂ d₁ d₂ : K} (h : zElt c₁ c₂ = zElt d₁ d₂) : c₁ = d₁ ∧ c₂ = d₂ := by
  have h' := congrArg (fun g : StatedSp 2 K => ((g : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
  simp only [coe_zElt] at h'
  have h1 := congrFun (congrFun h' (Sum.inl 0)) (Sum.inr 0)
  have h2 := congrFun (congrFun h' (Sum.inl 0)) (Sum.inr 1)
  simp [zC] at h1 h2
  exact ⟨h1, h2⟩

theorem unitriangular_conj_zC [CharP K 2] {A : Matrix (Fin 2) (Fin 2) K}
    (hA : IsUnitriangular A) (c₁ c₂ : K) : A * zC c₁ c₂ * Aᵀ = zC c₁ c₂ := by
  obtain ⟨hU, hD⟩ := hA
  have h10 : A 1 0 = 0 := hU (by decide)
  have h00 := hD 0
  have h11 := hD 1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, zC, h10, h00, h11]
  linear_combination (A 0 1 * c₂) * h2

theorem zElt_comm [CharP K 2] (c₁ c₂ : K) {v : StatedSp 2 K} (hv : v ∈ unipotent 2 K) :
    zElt c₁ c₂ * v = v * zElt c₁ c₂ := by
  obtain ⟨A, D, hA, hD, hv⟩ := hv
  apply SymplecticTorusWeyl.statedSp_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hv, zElt, coe_blockElt,
    blockMat_mul hA.isUnit_det, blockMat_mul (by rw [det_one]; exact isUnit_one), one_mul,
    mul_one, inv_one, transpose_one, Matrix.mul_one, Matrix.one_mul]
  congr 1
  have hA' := unitriangular_conj_zC hA c₁ c₂
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA.isUnit_det
  have hinvT : Aᵀ * A⁻¹ᵀ = 1 := by
    rw [← transpose_mul, hinv, transpose_one]
  calc D + A⁻¹ * zC c₁ c₂ * A⁻¹ᵀ = D + A⁻¹ * (A * zC c₁ c₂ * Aᵀ) * A⁻¹ᵀ := by rw [hA']
    _ = D + (A⁻¹ * A) * zC c₁ c₂ * (Aᵀ * A⁻¹ᵀ) := by
      simp only [Matrix.mul_assoc]
    _ = zC c₁ c₂ + D := by rw [hinv, hinvT, Matrix.one_mul, Matrix.mul_one, add_comm]

theorem zElt_sq [CharP K 2] (c₁ c₂ : K) : zElt c₁ c₂ ^ 2 = 1 := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [pow_two, Subgroup.coe_mul, Units.val_mul, coe_zElt, fromBlocks_multiply, Subgroup.coe_one,
    Units.val_one, ← fromBlocks_one]
  simp [CharTwo.add_self_eq_zero]

theorem torusHom_conj_zElt (s : Fin 2 → Kˣ) (c₁ c₂ : K) :
    SymplecticTorusWeyl.torusHom s * zElt c₁ c₂ * (SymplecticTorusWeyl.torusHom s)⁻¹ =
      zElt ((s 0 : K) ^ 2 * c₁) ((s 0 : K) * s 1 * c₂) := by
  rw [← map_inv]
  apply SymplecticTorusWeyl.statedSp_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_zElt, coe_zElt,
    SymplecticTorusWeyl.coe_torusHom, SymplecticTorusWeyl.coe_torusHom]
  ext r c
  rcases r with r | r <;> rcases c with c | c <;> fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, zC, fromBlocks, Matrix.diagonal_apply] <;> ring

theorem fieldSp_zElt (σ : K ≃+* K) (c₁ c₂ : K) :
    fieldSp 2 K σ (zElt c₁ c₂) = zElt (σ c₁) (σ c₂) := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_fieldSp, coe_zElt, coe_zElt]
  ext r c
  rcases r with r | r <;> rcases c with c | c <;> fin_cases r <;> fin_cases c <;>
    simp [zC, fromBlocks]

theorem tauSp_zElt [CharP K 2] (c₁ c₂ : K) : tauSp (zElt c₁ c₂) = zElt (c₂ ^ 2) c₁ := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_tauSp, coe_zElt, coe_zElt]
  ext r c
  rcases r with r | r <;> rcases c with c | c <;> fin_cases r <;> fin_cases c <;>
    simp [tauMat_apply, CFSG.QuasithinUnique.Lin2.Five.tauPair, zC, fromBlocks,
      CharTwo.neg_eq, pow_two]

theorem proj_zElt_mem_omegaOneCenter [CharP K 2] (c₁ c₂ : K) :
    proj 2 K (zElt c₁ c₂) ∈ omegaOneCenterOf (projUnipotent 2 K) := by
  refine Subgroup.subset_closure
    ⟨Subgroup.mem_inf.mpr ⟨⟨_, zElt_mem_unipotent c₁ c₂, rfl⟩, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul, (zElt_comm c₁ c₂ hv).symm]
  · rw [← map_pow, zElt_sq, map_one]

theorem model1 [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {α : MulAut (StatedProj (StatedSp 2 K))}
    (hα : ∀ x, α x ∈ projUnipotent 2 K ↔ x ∈ projUnipotent 2 K)
    (hfixU : ∀ z ∈ omegaOneCenterOf (projUnipotent 2 K), α z = z) :
    α ∈ inner (StatedProj (StatedSp 2 K)) := by
  obtain ⟨σ, u, s, ε, hu, rfl⟩ := Sp4.exists_standard_form hn hK hα
  have hinj := proj_injective (f := n) (r := 2) hn (by norm_num) hK
  set g := u * SymplecticTorusWeyl.torusHom s with hg
  have hgz : ∀ c₁ c₂ : K, g * zElt c₁ c₂ * g⁻¹ =
      zElt ((s 0 : K) ^ 2 * c₁) ((s 0 : K) * s 1 * c₂) := by
    intro c₁ c₂
    rw [hg, show u * SymplecticTorusWeyl.torusHom s * zElt c₁ c₂ *
        (u * SymplecticTorusWeyl.torusHom s)⁻¹ = u * (SymplecticTorusWeyl.torusHom s *
          zElt c₁ c₂ * (SymplecticTorusWeyl.torusHom s)⁻¹) * u⁻¹ by group, torusHom_conj_zElt,
      ← zElt_comm _ _ hu, mul_inv_cancel_right]
  have hfix : ∀ c₁ c₂ : K,
      proj 2 K (g * fieldSp 2 K σ ((if ε then tauSp else MonoidHom.id _) (zElt c₁ c₂)) * g⁻¹) =
        proj 2 K (zElt c₁ c₂) := by
    intro c₁ c₂
    have h1 := hfixU _ (proj_zElt_mem_omegaOneCenter c₁ c₂)
    rw [← h1, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    congr 2
    cases ε
    · simp [fieldAut_proj]
    · simp [fieldAut_proj, tauAut_proj]
  cases ε
  · by_cases hσ : σ = RingEquiv.refl K
    · subst hσ
      refine ⟨proj 2 K g, ?_⟩
      have h1 : fieldAut 2 K (RingEquiv.refl K) = 1 := map_one (fieldAut 2 K)
      simp [h1]
    · exfalso
      obtain ⟨c, hc⟩ : ∃ c, σ c ≠ c := by
        by_contra h
        push Not at h
        exact hσ (RingEquiv.ext h)
      have h1 := hinj (hfix 1 0)
      have h2 := hinj (hfix c 0)
      simp only [Bool.false_eq_true, ↓reduceIte, MonoidHom.id_apply] at h1 h2
      rw [fieldSp_zElt, map_one, map_zero, hgz] at h1
      rw [fieldSp_zElt, map_zero, hgz] at h2
      have e1 := (zElt_inj h1).1
      have e2 := (zElt_inj h2).1
      rw [mul_one] at e1
      rw [e1, one_mul] at e2
      exact hc e2
  · exfalso
    have h1 := hinj (hfix 1 0)
    simp only [↓reduceIte] at h1
    rw [tauSp_zElt, fieldSp_zElt, hgz] at h1
    have e1 := (zElt_inj h1).1
    simp at e1

theorem clause1 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (hX : StatedClassicalModel X .PSp 2 2 f) (P : Sylow 2 X) (α : MulAut X)
    (hαP : ∀ x ∈ (P : Subgroup X), α x ∈ (P : Subgroup X))
    (hαU : ∀ u ∈ omegaOneCenterOf (P : Subgroup X), α u = u) : α ∈ inner X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have : CharP K 2 := charP_two_of_card hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ := exists_sylow_projUnipotent (r := 2) (K := K) 2 (by norm_num)
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_sylow e P U
  rw [hU] at hφ
  have hαP' : ∀ x, α x ∈ (P : Subgroup X) ↔ x ∈ (P : Subgroup X) :=
    Sp4.mem_iff_of_forall_mem α _ hαP
  set α' := MulAut.congr φ α with hα'
  have hα'app : ∀ y, α' y = φ (α (φ.symm y)) := fun _ => rfl
  have hα'U : ∀ y, α' y ∈ projUnipotent 2 K ↔ y ∈ projUnipotent 2 K := by
    intro y
    rw [hα'app, ← hφ, hαP', hφ, MulEquiv.apply_symm_apply]
  have hΩ : ∀ z ∈ omegaOneCenterOf (projUnipotent 2 K), φ.symm z ∈ omegaOneCenterOf
      (P : Subgroup X) := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.mp hx.1
      refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · rw [hφ, MulEquiv.apply_symm_apply]
        exact hxU
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        apply φ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact Subgroup.mem_centralizer_iff.mp hxC _ ((hφ y).mp hy)
      · rw [← map_pow, hx.2, map_one]
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx
  have hα'fix : ∀ z ∈ omegaOneCenterOf (projUnipotent 2 K), α' z = z := by
    intro z hz
    rw [hα'app, hαU _ (hΩ z hz), MulEquiv.apply_symm_apply]
  obtain ⟨y, hy⟩ := model1 (n := f) (by omega) hK hα'U hα'fix
  refine ⟨φ.symm y, MulEquiv.ext fun x => ?_⟩
  have h1 := DFunLike.congr_fun hy (φ x)
  rw [hα'app, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
  rw [MulAut.conj_apply]
  apply φ.injective
  rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end CFSG.Quasithin.H13.A5.SpBorel
