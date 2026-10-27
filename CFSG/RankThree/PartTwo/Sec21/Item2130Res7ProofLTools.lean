module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res6ProofThree
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res7ProofMat

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130Res7Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup GeneralLinearGroup diagonal transvection)
open Item211Proof Item2130Res6Proof

section Matrices

variable {K : Type} [Field K]

theorem ActsVia.of_mk_eq {G : Type} [Group G] [Finite G] {Y : Subgroup G}
    {ε : lBar Y →* ProjGenLinGroup (Fin 3) K} {g : G} {y y' : GL (Fin 3) K}
    (h : ActsVia Y ε g y) (hy : ProjGenLinGroup.mk y = ProjGenLinGroup.mk y') :
    ActsVia Y ε g y' := by
  obtain ⟨hg, h⟩ := h
  exact ⟨hg, fun z => by rw [h z, hy]⟩

theorem mk_scalar_mul (l : Kˣ) (y : GL (Fin 3) K) :
    ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 3) l * y) = ProjGenLinGroup.mk y := by
  rw [map_mul, mk_eq_one_iff_mem_statedScalars.mpr ⟨l, rfl⟩, one_mul]

theorem isDiag_of_commMod (h2 : (2 : K) = 0) {σ : Kˣ} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    {M : GL (Fin 3) K}
    (h₁ : M * diagUnits 1 σ σ * M⁻¹ * (diagUnits 1 σ σ)⁻¹ ∈ StatedScalars (Fin 3) K)
    (h₂ : M * diagUnits 1 σ (σ ^ 2) * M⁻¹ * (diagUnits 1 σ (σ ^ 2))⁻¹ ∈
      StatedScalars (Fin 3) K) :
    (M : Matrix (Fin 3) (Fin 3) K).IsDiag := by
  have hσ1' : (σ : K) ≠ 1 := fun h => hσ1 (Units.ext h)
  have hσσ2 : (σ : K) ≠ (σ : K) ^ 2 := by
    intro h
    apply hσ1'
    have hσ0 : (σ : K) ≠ 0 := σ.ne_zero
    have : (σ : K) * 1 = σ * σ := by rw [mul_one, ← sq, ← h]
    exact (mul_left_cancel₀ hσ0 this).symm
  have hσ2 : (σ : K) ^ 2 ≠ 1 := by
    intro h
    apply hσ1'
    have h3 : (σ : K) ^ 3 = 1 := by
      have := congrArg Units.val hσ3
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
    calc (σ : K) = σ ^ 3 / σ ^ 2 := by field_simp
      _ = 1 := by rw [h3, h, div_one]
  obtain ⟨μ, hμ⟩ := h₁
  have hc1 : M * diagUnits 1 σ σ * M⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * diagUnits 1 σ σ := by
    rw [hμ]
    group
  have htr := trace_inv_conj M⁻¹ (diagUnits 1 σ σ)
  rw [inv_inv, hc1, scalar_mul_comm, trace_mul_scalar, coe_diagUnits, Matrix.trace_diagonal,
    Fin.sum_univ_three] at htr
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Units.val_one] at htr
  have hsum : (1 : K) + σ + σ = 1 := by linear_combination (σ : K) * h2
  rw [hsum, mul_one] at htr
  have hμ1 : μ = 1 := Units.ext htr
  rw [hμ1, map_one, one_mul] at hc1
  have hcomm1 : (M : Matrix (Fin 3) (Fin 3) K) * diagonal ![1, (σ : K), σ] =
      diagonal ![1, (σ : K), σ] * M := by
    have : M * diagUnits 1 σ σ = diagUnits 1 σ σ * M := by
      calc M * diagUnits 1 σ σ = M * diagUnits 1 σ σ * M⁻¹ * M := by group
        _ = diagUnits 1 σ σ * M := by rw [hc1]
    have h' := congrArg (fun N : GL (Fin 3) K => (N : Matrix (Fin 3) (Fin 3) K)) this
    simpa only [Units.val_mul, coe_diagUnits, Units.val_one] using h'
  have z01 : (M : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 :=
    Item2130Res6Proof.entry_eq_zero_of_commute_diagonal hcomm1 (by simpa using hσ1'.symm)
  have z02 : (M : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 :=
    Item2130Res6Proof.entry_eq_zero_of_commute_diagonal hcomm1 (by simpa using hσ1'.symm)
  have h00 : (M : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h0
    have hdet := (M.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
    apply hdet
    change (M : Matrix (Fin 3) (Fin 3) K).det = 0
    rw [Matrix.det_fin_three, h0, z01, z02]
    ring
  obtain ⟨ν, hν⟩ := h₂
  have hc2 : M * diagUnits 1 σ (σ ^ 2) =
      GeneralLinearGroup.scalar (Fin 3) ν * diagUnits 1 σ (σ ^ 2) * M := by
    calc M * diagUnits 1 σ (σ ^ 2) =
        (M * diagUnits 1 σ (σ ^ 2) * M⁻¹ * (diagUnits 1 σ (σ ^ 2))⁻¹) * diagUnits 1 σ (σ ^ 2) *
          M := by group
      _ = _ := by rw [← hν]
  have hc2m := congrArg (fun N : GL (Fin 3) K => (N : Matrix (Fin 3) (Fin 3) K) 0 0) hc2
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_diagUnits, Matrix.scalar_apply,
    Matrix.diagonal_mul_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at hc2m
  simp only [Matrix.cons_val_zero, Units.val_one, mul_one] at hc2m
  have hν1 : ν = 1 := by
    apply Units.ext
    have : (M : Matrix (Fin 3) (Fin 3) K) 0 0 * (1 - (ν : K)) = 0 := by linear_combination hc2m
    have h1 := (mul_eq_zero.mp this).resolve_left h00
    rw [Units.val_one]
    linear_combination -h1
  rw [hν1, map_one, one_mul] at hc2
  have hcomm2 : (M : Matrix (Fin 3) (Fin 3) K) * diagonal ![1, (σ : K), (σ : K) ^ 2] =
      diagonal ![1, (σ : K), (σ : K) ^ 2] * M := by
    have h' := congrArg (fun N : GL (Fin 3) K => (N : Matrix (Fin 3) (Fin 3) K)) hc2
    simpa only [Units.val_mul, coe_diagUnits, Units.val_one, Units.val_pow_eq_pow_val] using h'
  intro r s hrs
  refine Item2130Res6Proof.entry_eq_zero_of_commute_diagonal hcomm2 ?_
  have cover : ∀ r : Fin 3, r = 0 ∨ r = 1 ∨ r = 2 := by decide
  rcases cover r with rfl | rfl | rfl <;> rcases cover s with rfl | rfl | rfl <;>
    first | exact absurd rfl hrs | simp [hσ1', hσ1'.symm, hσ2, hσ2.symm, hσσ2, hσσ2.symm]

theorem exists_diag_of_cube {M : GL (Fin 3) K} (hM : (M : Matrix (Fin 3) (Fin 3) K).IsDiag)
    (h3 : M ^ 3 ∈ StatedScalars (Fin 3) K) :
    ∃ l s t : Kˣ, s ∈ rootsOfUnity 3 K ∧ t ∈ rootsOfUnity 3 K ∧
      M = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t := by
  have hdiag : (M : Matrix (Fin 3) (Fin 3) K) = diagonal (fun i => (M : Matrix _ _ K) i i) :=
    ((Matrix.isDiag_iff_diagonal_diag _).mp hM).symm
  have hne : ∀ i, (M : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
    intro i h0
    have hdet := (M.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
    apply hdet
    change (M : Matrix (Fin 3) (Fin 3) K).det = 0
    rw [hdiag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  set m : Fin 3 → Kˣ := fun i => Units.mk0 _ (hne i) with hm
  obtain ⟨μ, hμ⟩ := h3
  have hcube : ∀ i, (m i) ^ 3 = μ := by
    intro i
    apply Units.ext
    have h1 := congrArg (fun N : GL (Fin 3) K => (N : Matrix (Fin 3) (Fin 3) K) i i) hμ
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_pow_eq_pow_val] at h1
    rw [hdiag, Matrix.diagonal_pow, Matrix.diagonal_apply_eq] at h1
    rw [Units.val_pow_eq_pow_val]
    exact h1.symm
  refine ⟨m 0, m 1 * (m 0)⁻¹, m 2 * (m 0)⁻¹, ?_, ?_, ?_⟩
  · rw [mem_rootsOfUnity, mul_pow, inv_pow, hcube, hcube, mul_inv_cancel]
  · rw [mem_rootsOfUnity, mul_pow, inv_pow, hcube, hcube, mul_inv_cancel]
  · apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_diagUnits, Matrix.scalar_apply,
      Matrix.diagonal_mul_diagonal, hdiag]
    congr 1
    funext i
    have h0 := hne 0
    fin_cases i <;> simp [hm] <;> field_simp

theorem cycThree_pow_three : (cycThree : GL (Fin 3) K) ^ 3 = 1 :=
  CFSG.RankThree.PartTwo.Sec4.cycThree_pow_three

theorem cycThree_conj_diag_sigma {σ : Kˣ} (hσ3 : σ ^ 3 = 1) :
    cycThree * diagUnits 1 σ (σ ^ 2) * cycThree⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (σ ^ 2) * diagUnits 1 σ (σ ^ 2) := by
  rw [cycThree_conj_diagUnits, scalar_mul_diagUnits_eq]
  change diagUnits (σ ^ 2) 1 σ = diagUnits (σ ^ 2) (σ ^ 2 * σ) (σ ^ 2 * σ ^ 2)
  rw [← pow_succ, hσ3, ← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, hσ3, one_mul, pow_one]

theorem negSwap_conj_diag_sigma {σ : Kˣ} (hσ3 : σ ^ 3 = 1) :
    negSwap * diagUnits 1 σ (σ ^ 2) * negSwap⁻¹ = (diagUnits 1 σ (σ ^ 2))⁻¹ := by
  rw [negSwap_conj_diagUnits, diagUnits_inv, inv_one]
  have h1 : σ⁻¹ = σ ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hσ3]
  have h2 : (σ ^ 2)⁻¹ = σ := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ, hσ3]
  rw [h1, h2]

theorem diag_sigma_conj_cycThree {σ : Kˣ} (hσ3 : σ ^ 3 = 1) :
    diagUnits 1 σ (σ ^ 2) * cycThree * (diagUnits 1 σ (σ ^ 2))⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) σ * cycThree := by
  have hσ' : (σ : K) ^ 3 = 1 := by
    have := congrArg Units.val hσ3
    simpa using this
  have h1 : σ⁻¹ = σ ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hσ3]
  have h2 : (σ ^ 2)⁻¹ = σ := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ, hσ3]
  rw [diagUnits_inv, inv_one, h1, h2]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_diagUnits, coe_diagUnits, coe_cycThree,
    GeneralLinearGroup.coe_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.scalar_apply]
  linear_combination (σ : K) * hσ'

theorem cycThree_inv_mul_diagUnits_not_mem (u v w : Kˣ) :
    cycThree⁻¹ * diagUnits u v w ∉ StatedScalars (Fin 3) K := by
  rintro ⟨l, hl⟩
  have h := congrArg (fun N : GL (Fin 3) K => (N : Matrix (Fin 3) (Fin 3) K) 0 0) hl
  have hP : ((cycThree⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 1, 0; 0, 0, 1; 1, 0, 0] := rfl
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Units.val_mul, hP, coe_diagUnits, Matrix.mul_diagonal] at h
  simp at h

end Matrices

section Center

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem eq_one_of_commute_of_mulEquiv {X : Type*} [Group X] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    (e : X ≃* projImage (slPi π 3 (p ^ f) K)) {z : X} (hz : ∀ u : X, z * u = u * z) : z = 1 := by
  have hc : e z ∈ Subgroup.center (projImage (slPi π 3 (p ^ f) K)) := by
    rw [Subgroup.mem_center_iff]
    intro m
    obtain ⟨u, rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul, hz u]
  rw [center_projImage_eq_bot hK hq, Subgroup.mem_bot] at hc
  exact e.map_eq_one_iff.mp hc

end Center

section Root

variable {K : Type} [Field K] [CharP K 2]

theorem exists_two_subgroup_of_frame {X : Type*} [Group X] {q : ℕ}
    (e : X ≃* projImage (slPi true 3 q K)) (g : GL (Fin 3) K) :
    ∃ V : Subgroup X, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ (φ : MulAut X) (D : GL (Fin 3) K),
      (∀ i j, i ≠ j → (D : Matrix (Fin 3) (Fin 3) K) i j = 0) →
      (∀ z : X, ((e (φ z) : ProjGenLinGroup (Fin 3) K)) =
        ProjGenLinGroup.mk (g * D * g⁻¹) * (e z : ProjGenLinGroup (Fin 3) K) *
          (ProjGenLinGroup.mk (g * D * g⁻¹))⁻¹) → ∀ v ∈ V, φ v ∈ V := by
  set R : Subgroup (GL (Fin 3) K) := (rootGL K).map (MulAut.conj g).toMonoidHom with hR
  have hRS : R ≤ slPi true 3 q K := by
    rintro _ ⟨M, hM, rfl⟩
    have hMS := rootGL_le_slPi q hM
    rw [mem_slPi_true] at hMS ⊢
    change ((g * M * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hMS, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  set V₀ : Subgroup (projImage (slPi true 3 q K)) :=
    (R.map ProjGenLinGroup.mk).subgroupOf (projImage (slPi true 3 q K)) with hV₀
  have hmemV₀ : ∀ v : projImage (slPi true 3 q K), v ∈ V₀ ↔ ∃ M ∈ rootGL K,
      ProjGenLinGroup.mk (g * M * g⁻¹) = (v : ProjGenLinGroup (Fin 3) K) := by
    intro v
    rw [hV₀, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨_, ⟨M, hM, rfl⟩, hv⟩
      exact ⟨M, hM, hv⟩
    · rintro ⟨M, hM, hv⟩
      exact ⟨g * M * g⁻¹, ⟨M, hM, rfl⟩, hv⟩
  have hmemS : ∀ M ∈ rootGL K,
      ProjGenLinGroup.mk (g * M * g⁻¹) ∈ projImage (slPi true 3 q K) :=
    fun M hM => ⟨g * M * g⁻¹, hRS ⟨M, hM, rfl⟩, rfl⟩
  refine ⟨V₀.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  ·
    obtain ⟨⟨M, hM⟩, hM1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (rootGL_ne_bot (K := K))
    have hM1' : M ≠ 1 := fun h => hM1 (Subtype.ext h)
    obtain ⟨a, ha⟩ := hM
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply hM1'
      exact Units.ext (by rw [ha, Matrix.transvection_zero, Units.val_one])
    intro hbot
    have hv : (⟨ProjGenLinGroup.mk (g * M * g⁻¹), hmemS M ⟨a, ha⟩⟩ :
        projImage (slPi true 3 q K)) ∈ V₀ := (hmemV₀ _).mpr ⟨M, ⟨a, ha⟩, rfl⟩
    have hv' : e.symm ⟨ProjGenLinGroup.mk (g * M * g⁻¹), hmemS M ⟨a, ha⟩⟩ ∈
        V₀.map e.symm.toMonoidHom := ⟨_, hv, rfl⟩
    rw [hbot, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hv'
    have h1 : ProjGenLinGroup.mk (g * M * g⁻¹) = 1 := congrArg Subtype.val hv'
    rw [mk_eq_one_iff_mem_statedScalars] at h1
    have hMs : M ∈ StatedScalars (Fin 3) K := by
      rw [← inv_conj_mem_statedScalars_iff g⁻¹]
      simpa using h1
    obtain ⟨u, hu⟩ := hMs
    have h01 := congrArg (fun N : GL (Fin 3) K => (N : Matrix (Fin 3) (Fin 3) K) 0 1) hu
    simp only [ha, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h01
    simp [Matrix.transvection] at h01
    exact ha0 h01.symm
  ·
    intro v
    obtain ⟨_, ⟨w, hw, rfl⟩⟩ := v
    obtain ⟨M, hM, hMw⟩ := (hmemV₀ w).mp hw
    refine ⟨1, Subtype.ext ?_⟩
    have hM2 : M ^ 2 = 1 := rootGL_sq hM
    have hw2 : w ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hMw, ← map_pow]
      have : (g * M * g⁻¹) ^ 2 = 1 := by
        rw [conj_pow, hM2, mul_one, mul_inv_cancel]
      rw [this, map_one, Subgroup.coe_one]
    change (e.symm.toMonoidHom w) ^ 2 ^ 1 = 1
    rw [pow_one, ← map_pow, hw2, map_one]
  ·
    intro φ D hD hφ v hv
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨M, hM, hMw⟩ := (hmemV₀ w).mp hw
    have hM' : D * M * D⁻¹ ∈ rootGL K := conj_mem_rootGL_of_diag hD hM
    refine ⟨e (φ (e.symm.toMonoidHom w)), (hmemV₀ _).mpr ⟨D * M * D⁻¹, hM', ?_⟩, ?_⟩
    · rw [hφ, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, ← hMw, ← map_inv, ← map_mul,
        ← map_mul]
      congr 1
      group
    · simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

end Root

theorem modNine_of_eq_three_mul {f f₀ : ℕ} (hq : ModThree true (2 ^ f)) (hf : f = 3 * f₀) :
    ModNine true (2 ^ f) := by
  change 2 ^ f % 9 = 1
  change 2 ^ f % 3 = 1 at hq
  subst hf
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' f₀
  · rw [show 3 * (2 * m) = 6 * m by ring, pow_mul, Nat.pow_mod]
    norm_num
  · exfalso
    rw [show 3 * (2 * m + 1) = 6 * m + 3 by ring, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
      at hq
    norm_num at hq

section Dichotomy


theorem actsVia_or_field {G : Type} [Group G] [Finite G] {Y : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (Y : Set G)) (hx3 : x ^ 3 = 1) {π : Bool} {p f : ℕ}
    {K : Type} [Field K] (hK : PiField π p f K) (hq2 : 2 < p ^ f)
    (e : lBar Y ≃* projImage (slPi π 3 (p ^ f) K)) :
    (∃ y ∈ glPi π 3 (p ^ f) K,
      ActsVia Y ((projImage (slPi π 3 (p ^ f) K)).subtype.comp e.toMonoidHom) x y) ∨
      ∃ f₀ : ℕ, f = 3 * f₀ := by
  have hxA : Subgroup.zpowers x ≤ Subgroup.normalizer (Y : Set G) :=
    Subgroup.zpowers_le.mpr hxN
  obtain ⟨Φ₀, hΦ₀⟩ := exists_lEquiv hxA
  rcases pslAct_pgl_or_field hK hq2 (theta_lOne_eq_bot Φ₀) (Φ₀.symm.trans e) _
      (piX_pow_three hxA (Subgroup.mem_zpowers x) hx3) with ⟨y, hy, hys⟩ | ⟨-, f₀, hf, -⟩
  · refine Or.inl ⟨y, hy, hxN, fun z => ?_⟩
    have h1 := hys (e z)
    rw [slAct_trans_apply hxA hΦ₀ e (Subgroup.mem_zpowers x) z] at h1
    exact h1
  · exact Or.inr ⟨f₀, hf⟩

end Dichotomy

end CFSG.RankThree.PartTwo.Sec21.Item2130Res7Proof
