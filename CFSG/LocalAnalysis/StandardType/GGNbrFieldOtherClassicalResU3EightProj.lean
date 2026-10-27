module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3EightDescent
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3Three

public section

namespace CFSG.StandardType

namespace ResU3Eight

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.FQ CFSG.LocalAnalysis.GLTheoremA.T156.Uni
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective)
open CFSG.RankThree.Classical (permGL)
open ResU3Three

section Mat

variable {F : Type} [Field F]

theorem conj_scalar_mul_U3Eight (U X : GL (Fin 3) F) (c : Fˣ) :
    U * (Matrix.GeneralLinearGroup.scalar (Fin 3) c * X) * U⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c * (U * X * U⁻¹) := by
  calc U * (Matrix.GeneralLinearGroup.scalar (Fin 3) c * X) * U⁻¹
      = (U * Matrix.GeneralLinearGroup.scalar (Fin 3) c * U⁻¹) * (U * X * U⁻¹) := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin 3) c * (U * X * U⁻¹) := by
      rw [← scalar_mul_comm_U3Three c U, mul_inv_cancel_right]

theorem regU3Three_conj_U3Eight {M : Matrix (Fin 3) (Fin 3) F} (hM : RegU3Three M)
    (U : GL (Fin 3) F) :
    RegU3Three ((U : Matrix (Fin 3) (Fin 3) F) * M * ((U⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F)) := by
  obtain ⟨Q, d, hd, hMQ⟩ := hM
  refine ⟨U * Q, d, hd, ?_⟩
  have hUU : ((U⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (U : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Units.val_mul]
  calc (U : Matrix (Fin 3) (Fin 3) F) * M * ((U⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((U : Matrix (Fin 3) (Fin 3) F) * (Q : Matrix (Fin 3) (Fin 3) F))
      = (U : Matrix (Fin 3) (Fin 3) F) * M *
          (((U⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (U : Matrix (Fin 3) (Fin 3) F)) *
          (Q : Matrix (Fin 3) (Fin 3) F) := by simp only [Matrix.mul_assoc]
    _ = (U : Matrix (Fin 3) (Fin 3) F) * (M * (Q : Matrix (Fin 3) (Fin 3) F)) := by
        rw [hUU, Matrix.mul_one, Matrix.mul_assoc]
    _ = (U : Matrix (Fin 3) (Fin 3) F) * (Q : Matrix (Fin 3) (Fin 3) F) * diagonal d := by
        rw [hMQ, Matrix.mul_assoc]

variable {k : Type} [Field k]

theorem map_scalar_U3Eight (ι : k →+* F) (c : kˣ) :
    Matrix.GeneralLinearGroup.map ι (Matrix.GeneralLinearGroup.scalar (Fin 3) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map ι.toMonoidHom c) := by
  apply Units.ext
  change ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) k) :
    Matrix (Fin 3) (Fin 3) k).map ι = _
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero ι)]
  rfl

theorem exists_scalar_of_map_U3Eight (ι : k →+* F) {Z : GL (Fin 3) k} {c : Fˣ}
    (h : Matrix.GeneralLinearGroup.map ι Z = Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
    ∃ c' : kˣ, Z = Matrix.GeneralLinearGroup.scalar (Fin 3) c' := by
  have hent : ∀ a b : Fin 3, ι ((Z : Matrix (Fin 3) (Fin 3) k) a b) =
      if a = b then (c : F) else 0 := by
    intro a b
    have h1 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) a b) h
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply] at h1
    exact h1
  have h00 : ι ((Z : Matrix (Fin 3) (Fin 3) k) 0 0) = c := by rw [hent, if_pos rfl]
  have hne : (Z : Matrix (Fin 3) (Fin 3) k) 0 0 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h00
    exact c.ne_zero h00.symm
  refine ⟨Units.mk0 _ hne, Units.ext ?_⟩
  ext a b
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0]
  apply ι.injective
  rw [hent]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, Matrix.diagonal_apply_eq, h00]
  · rw [if_neg hab, Matrix.diagonal_apply_ne _ hab, map_zero]

end Mat

section Proj

variable {K : Type} [Field K] [Finite K]

local notation "H₈" => LargeEvenSUGroup (Fin 3) K (2 ^ 3)
local notation "N₈" => Subgroup.normalizer (LargeEvenSUGroup (Fin 3) K (2 ^ 3) : Set (GL (Fin 3) K))
local notation "ρ₈" => TableB.projConj (LargeEvenSUGroup (Fin 3) K (2 ^ 3))
local notation "π₈" => LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ 3))

theorem reg_or_frame_proj_U3Eight (hK : Nat.card K = (2 ^ 3) ^ 2) {σ : K ≃+* K}
    (hσ3 : orderOf σ = 3) {f : MulAut (LargeEvenProj H₈)} (hf : Induced (2 ^ 3) σ f) (U : N₈)
    (hU : (U : GL (Fin 3) K) ∈ LargeEvenGUSet (Fin 3) K (2 ^ 3))
    {Ab : Subgroup (MulAut (LargeEvenProj H₈))} (hAb : IsElemAbelian 3 Ab)
    (hAbI : ∀ φ ∈ Ab, φ ∈ LargeEvenMatConjImage π₈ (LargeEvenGUSet (Fin 3) K (2 ^ 3)))
    (hAbx : ∀ φ ∈ Ab, φ * (ρ₈ U * f * (ρ₈ U)⁻¹) = (ρ₈ U * f * (ρ₈ U)⁻¹) * φ)
    {φ₀ : MulAut (LargeEvenProj H₈)} (hφ₀ : φ₀ ∈ Ab) (hφ₀1 : φ₀ ≠ 1) :
    Group.IsSolvable (ggFix φ₀) ∨
      ∃ (Q : GL (Fin 3) K) (u v : Fin 3) (hw : Q * permGL (Equiv.swap u v) * Q⁻¹ ∈ H₈),
        (ρ₈ U * f * (ρ₈ U)⁻¹) (π₈ ⟨_, hw⟩) = π₈ ⟨_, hw⟩ ∧
        (∀ φ ∈ Ab, ∃ B : N₈, (B : GL (Fin 3) K) ∈ LargeEvenGUSet (Fin 3) K (2 ^ 3) ∧
          φ = ρ₈ B ∧ ∃ D : Fin 3 → Kˣ, Q⁻¹ * (B : GL (Fin 3) K) * Q = diagHom 3 D) ∧
        ∃ (B₀ : N₈) (σ₀ : Fin 3 → Kˣ), φ₀ = ρ₈ B₀ ∧
          Q⁻¹ * (B₀ : GL (Fin 3) K) * Q = diagHom 3 σ₀ ∧ ¬ Function.Injective σ₀ ∧
          σ₀ u ≠ σ₀ v := by
  classical
  have h₀K : UnitaryFieldData 2 3 K := TableBU.unitaryFieldData_of_card hK (by norm_num)
  haveI : CharP K 2 := h₀K.charP
  have hNK := TableBUE.gu_subset_normalizer (d := 3) h₀K
  have hσodd : Odd (orderOf σ) := by rw [hσ3]; decide
  obtain ⟨-, hm1, hk⟩ := fixF_data (by norm_num : 1 ≤ 3) hK σ hσodd
  haveI : CharP (fixF σ) 2 := charP_fixF (by norm_num) hK σ hσodd
  have hm : 3 / orderOf σ = 1 := by rw [hσ3]
  have h₀ : UnitaryFieldData 2 (3 / orderOf σ) (fixF σ) :=
    TableBU.unitaryFieldData_of_card hk hm1
  have h3 : 3 ∣ 2 ^ (3 / orderOf σ) + 1 := by rw [hm]; norm_num
  obtain ⟨ω, hω⟩ := exists_omega_U3Three h₀ h3
  set ι : fixF σ →+* K := (fixF σ).subtype with hιdef
  have hdK : ((3 : ℕ), 2 ^ 3) ≠ (3, 2) := by decide
  have hdesc : ∀ φ ∈ Ab, ∃ (B : GL (Fin 3) K) (hB : B ∈ LargeEvenGUSet (Fin 3) K (2 ^ 3))
      (μ : Kˣ) (B' : GL (Fin 3) (fixF σ)), φ = ρ₈ ⟨B, hNK hB⟩ ∧
      B' ∈ LargeEvenGUSet (Fin 3) (fixF σ) (2 ^ (3 / orderOf σ)) ∧
      Matrix.GeneralLinearGroup.map ι B' =
        Matrix.GeneralLinearGroup.scalar (Fin 3) μ * ((U : GL (Fin 3) K)⁻¹ * B * U) := by
    intro φ hφ
    obtain ⟨B, hB, rfl⟩ := TableB.exists_eq_projConj hNK (hAbI φ hφ)
    have hc := ggConj_commute_line (hAbx _ hφ)
    have he : (ρ₈ U)⁻¹ * ρ₈ ⟨B, hNK hB⟩ * ρ₈ U = ρ₈ (U⁻¹ * ⟨B, hNK hB⟩ * U) := by
      rw [map_mul, map_mul, map_inv]
    rw [he] at hc
    have hgu : ((U⁻¹ * ⟨B, hNK hB⟩ * U : N₈) : GL (Fin 3) K) ∈
        LargeEvenGUSet (Fin 3) K (2 ^ 3) := guSet_conj_mem_U3Eight hK hU hB
    have key := exists_descend_of_commute_U3Eight (d := 3) (j := 3) (K := K) (σ := σ) (f := f)
      (by norm_num) (by norm_num) hK hdK hσodd hf
    have key2 := key (U⁻¹ * ⟨B, hNK hB⟩ * U)
    have key3 := key2 hgu
    obtain ⟨μ, B', hB', hB'eq⟩ := key3 hc
    exact ⟨B, hB, μ, B', rfl, hB', hB'eq⟩
  let S : Subgroup (GL (Fin 3) (fixF σ)) :=
    ((Ab.comap ρ₈).map (Subgroup.subtype N₈)).comap
      ((MulAut.conj (U : GL (Fin 3) K)).toMonoidHom.comp (Matrix.GeneralLinearGroup.map ι))
  have hmemS : ∀ B' : GL (Fin 3) (fixF σ), B' ∈ S ↔ ∃ y : N₈, ρ₈ y ∈ Ab ∧
      (y : GL (Fin 3) K) =
        (U : GL (Fin 3) K) * Matrix.GeneralLinearGroup.map ι B' * (U : GL (Fin 3) K)⁻¹ := by
    intro B'
    simp only [S, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
  have hconjS : ∀ (B' : GL (Fin 3) (fixF σ)) (y : N₈),
      (y : GL (Fin 3) K) =
        (U : GL (Fin 3) K) * Matrix.GeneralLinearGroup.map ι B' * (U : GL (Fin 3) K)⁻¹ →
      ∀ c : Kˣ, (y : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c →
        ∃ c' : (fixF σ)ˣ, B' = Matrix.GeneralLinearGroup.scalar (Fin 3) c' := by
    intro B' y hy c hc
    rw [hy] at hc
    refine exists_scalar_of_map_U3Eight ι (c := c) ?_
    have h1 := eq_scalar_of_conj_U3Three (P := (U : GL (Fin 3) K)⁻¹) (by rw [inv_inv]; exact hc)
    exact h1
  have hSz : ∀ c : (fixF σ)ˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ S := by
    intro c
    rw [hmemS]
    have hz : Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map ι.toMonoidHom c) ∈
        LargeEvenScalars (Fin 3) K := ⟨_, rfl⟩
    refine ⟨⟨_, TableB.scalar_mem_normalizer _ hz⟩, ?_, ?_⟩
    · rw [TableB.projConj_of_scalar _ hz]
      exact Ab.one_mem
    · change Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map ι.toMonoidHom c) = _
      rw [map_scalar_U3Eight, mul_assoc, scalar_mul_comm_U3Three, ← mul_assoc, mul_inv_cancel,
        one_mul]
  have hSc : ∀ x ∈ S, ∀ y ∈ S, ∃ c : (fixF σ)ˣ,
      x * y = Matrix.GeneralLinearGroup.scalar (Fin 3) c * (y * x) := by
    intro x hx y hy
    obtain ⟨y₁, h₁, hy₁⟩ := (hmemS x).mp hx
    obtain ⟨y₂, h₂, hy₂⟩ := (hmemS y).mp hy
    obtain ⟨c, hc⟩ := exists_comm_scalar_U3Three hK (by norm_num) (by norm_num) (M := y₁)
      (M' := y₂) (TableB.IsElemAbelian.comm hAb h₁ h₂)
    have hcomm : (U : GL (Fin 3) K) * Matrix.GeneralLinearGroup.map ι (x * y * (y * x)⁻¹) *
        (U : GL (Fin 3) K)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      simp only [map_mul, map_inv]
      calc (U : GL (Fin 3) K) * (Matrix.GeneralLinearGroup.map ι x *
            Matrix.GeneralLinearGroup.map ι y * (Matrix.GeneralLinearGroup.map ι y *
            Matrix.GeneralLinearGroup.map ι x)⁻¹) * (U : GL (Fin 3) K)⁻¹
          = ((y₁ : GL (Fin 3) K) * y₂) * ((y₂ : GL (Fin 3) K) * y₁)⁻¹ := by
            rw [hy₁, hy₂]; group
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by rw [hc, mul_inv_cancel_right]
    obtain ⟨c', hc'⟩ := exists_scalar_of_map_U3Eight ι (c := c)
      (eq_scalar_of_conj_U3Three (P := (U : GL (Fin 3) K)⁻¹) (by rw [inv_inv]; exact hcomm))
    refine ⟨c', ?_⟩
    rw [← hc', inv_mul_cancel_right]
  have hS3 : ∀ x ∈ S, ∃ c : (fixF σ)ˣ, x ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    intro x hx
    obtain ⟨y₁, h₁, hy₁⟩ := (hmemS x).mp hx
    obtain ⟨c, hc⟩ := exists_cube_scalar_U3Three hK (by norm_num) (by norm_num) (M := y₁)
      (hAb.2 _ h₁)
    have hcube : (U : GL (Fin 3) K) * Matrix.GeneralLinearGroup.map ι (x ^ 3) *
        (U : GL (Fin 3) K)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      rw [← hc, map_pow, hy₁, conj_pow]
    exact exists_scalar_of_map_U3Eight ι (c := c)
      (eq_scalar_of_conj_U3Three (P := (U : GL (Fin 3) K)⁻¹) (by rw [inv_inv]; exact hcube))
  have hdescS : ∀ (B : GL (Fin 3) K) (hB : B ∈ LargeEvenGUSet (Fin 3) K (2 ^ 3)) (μ : Kˣ)
      (B' : GL (Fin 3) (fixF σ)), ρ₈ ⟨B, hNK hB⟩ ∈ Ab →
      Matrix.GeneralLinearGroup.map ι B' =
        Matrix.GeneralLinearGroup.scalar (Fin 3) μ * ((U : GL (Fin 3) K)⁻¹ * B * U) →
      B' ∈ S := by
    intro B hB μ B' hBA hB'eq
    rw [hmemS]
    have hz : Matrix.GeneralLinearGroup.scalar (Fin 3) μ ∈ LargeEvenScalars (Fin 3) K := ⟨_, rfl⟩
    have hμB : Matrix.GeneralLinearGroup.scalar (Fin 3) μ * B ∈ N₈ :=
      Subgroup.mul_mem _ (TableB.scalar_mem_normalizer _ hz) (hNK hB)
    refine ⟨⟨_, hμB⟩, ?_, ?_⟩
    · rw [projConj_scalar_mul_U3Three μ (hNK hB) hμB]
      exact hBA
    · change Matrix.GeneralLinearGroup.scalar (Fin 3) μ * B = _
      rw [hB'eq]
      rw [conj_scalar_mul_U3Eight]
      group
  obtain ⟨B₀K, hB₀K, μ₀, B₀, rfl, hB₀gu, hB₀eq⟩ := hdesc φ₀ hφ₀
  have hB₀S : B₀ ∈ S := hdescS B₀K hB₀K μ₀ B₀ hφ₀ hB₀eq
  have hB₀s : ∀ c : (fixF σ)ˣ, B₀ ≠ Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    intro c hc
    apply hφ₀1
    have h1 : (U : GL (Fin 3) K)⁻¹ * B₀K * U =
        Matrix.GeneralLinearGroup.scalar (Fin 3) (μ₀⁻¹ * Units.map ι.toMonoidHom c) := by
      have h2 : Matrix.GeneralLinearGroup.scalar (Fin 3) μ₀ * ((U : GL (Fin 3) K)⁻¹ * B₀K * U) =
          Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map ι.toMonoidHom c) := by
        rw [← hB₀eq, hc, map_scalar_U3Eight]
      rw [map_mul, ← h2, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    have h3 : B₀K = Matrix.GeneralLinearGroup.scalar (Fin 3) (μ₀⁻¹ * Units.map ι.toMonoidHom c) :=
      eq_scalar_of_conj_U3Three h1
    have hz : B₀K ∈ LargeEvenScalars (Fin 3) K := ⟨_, h3.symm⟩
    exact TableB.projConj_of_scalar _ hz
  obtain ⟨s₀, hs₀⟩ := hS3 B₀ hB₀S
  have hsolv_of_reg : RegU3Three ((B₀ : Matrix (Fin 3) (Fin 3) (fixF σ)).map ι) →
      Group.IsSolvable (ggFix (ρ₈ ⟨B₀K, hNK hB₀K⟩)) := by
    intro hreg
    apply isSolvable_ggFix_projConj_of_reg
    have hB₀K' : B₀K = Matrix.GeneralLinearGroup.scalar (Fin 3) μ₀⁻¹ *
        ((U : GL (Fin 3) K) * Matrix.GeneralLinearGroup.map ι B₀ * (U : GL (Fin 3) K)⁻¹) := by
      rw [hB₀eq, conj_scalar_mul_U3Eight, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one,
        one_mul]
      group
    change RegU3Three (B₀K : Matrix (Fin 3) (Fin 3) K)
    rw [hB₀K', coe_scalar_mul_U3Three, Units.val_mul, Units.val_mul]
    exact (regU3Three_conj_U3Eight hreg (U : GL (Fin 3) K)).smul (Units.ne_zero _)
  have hk4 : Nat.card (fixF σ) = 4 := by rw [hk, hm]; norm_num
  have hK64 : Nat.card K = 4 ^ 3 := by rw [hK]; norm_num
  by_cases hcub : ∃ e₀ : (fixF σ)ˣ, e₀ ^ 3 = s₀
  swap
  ·
    left
    apply hsolv_of_reg
    push Not at hcub
    obtain ⟨e, he⟩ := exists_cube_root_U3Three ι hk4 hK64 (by norm_num) (s₀ : fixF σ)
    refine regU3Three_of_not_cube ι hω (s := (s₀ : fixF σ)) ?_ (fun e' he' => ?_) he
    · have h1 := congrArg Units.val hs₀
      rwa [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal] at h1
    · have he'0 : e' ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num)] at he'
        exact s₀.ne_zero he'.symm
      exact hcub (Units.mk0 e' he'0) (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0,
        he']))
  obtain ⟨e₀, he₀⟩ := hcub
  have he₀' : B₀ ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (e₀ ^ 3) := by
    rw [he₀]
    exact hs₀
  by_cases hpart : ∃ B ∈ S, B * B₀ ≠ B₀ * B
  ·
    left
    obtain ⟨B, hBS, hBne⟩ := hpart
    obtain ⟨ζ, hζ⟩ := hSc B hBS B₀ hB₀S
    have hζ1 : ζ ≠ 1 := fun h => hBne (by rw [hζ, h, map_one, one_mul])
    exact hsolv_of_reg ((regU3Three_of_partner_GL hω he₀' hζ hζ1).map ι)
  push Not at hpart
  rcases reg_or_frame_U3Eight h₀ h3 hSc hS3 hSz hB₀gu hB₀S hB₀s he₀'
      (fun B hB _ => hpart B hB) with hreg | ⟨P, σ', u, v, hPU, hdiagS, hσ', hninj, huv⟩
  · left
    exact hsolv_of_reg (hreg.map ι)
  right
  set Pι : GL (Fin 3) K := Matrix.GeneralLinearGroup.map ι P with hPιdef
  set Q : GL (Fin 3) K := (U : GL (Fin 3) K) * Pι with hQdef
  set τ : Equiv.Perm (Fin 3) := Equiv.swap u v with hτ
  have hτmem : permGL τ ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (3 / orderOf σ) (fixF σ) 3 :=
    permGL_mem_su τ
  set w₀ : LargeEvenSUGroup (Fin 3) (fixF σ) (2 ^ (3 / orderOf σ)) :=
    (TableBUE.conjSU h₀ P hPU).symm ⟨permGL τ, hτmem⟩ with hw₀def
  have hw₀ : (w₀ : GL (Fin 3) (fixF σ)) = P * permGL τ * P⁻¹ := rfl
  set w₁ : H₈ := subfieldInclusion (d := 3) (j := 3) (by norm_num) hK σ hσodd w₀ with hw₁def
  have hw₁ : (w₁ : GL (Fin 3) K) = Pι * permGL τ * Pι⁻¹ := by
    rw [hw₁def, coe_subfieldInclusion, hw₀, map_mul, map_mul, map_inv, map_permGL]
  have hw : Q * permGL τ * Q⁻¹ ∈ H₈ := by
    have h1 := conj_mem_su hU w₁.2
    rw [hw₁] at h1
    convert h1 using 1
    rw [hQdef, _root_.mul_inv_rev]
    group
  refine ⟨Q, u, v, hw, ?_, ?_, ⟨B₀K, hNK hB₀K⟩,
    fun i => μ₀⁻¹ * Units.map ι.toMonoidHom (σ' i), rfl, ?_, ?_, ?_⟩
  ·
    have h1 : (ρ₈ U)⁻¹ (π₈ ⟨_, hw⟩) = π₈ w₁ := by
      rw [← map_inv]
      change ρ₈ U⁻¹ ((⟨_, hw⟩ : H₈) : LargeEvenProj H₈) = (w₁ : LargeEvenProj H₈)
      rw [TableB.projConj_mk]
      congr 1
      apply Subtype.ext
      change (U : GL (Fin 3) K)⁻¹ * (Q * permGL τ * Q⁻¹) * (U : GL (Fin 3) K)⁻¹⁻¹ =
        (w₁ : GL (Fin 3) K)
      rw [hw₁, hQdef, _root_.mul_inv_rev]
      group
    have h2 : f (π₈ w₁) = π₈ w₁ := by
      change f (QuotientGroup.mk w₁) = QuotientGroup.mk w₁
      rw [hf w₁]
      congr 1
      apply Subtype.ext
      rw [matAct_coe, hw₁def, coe_subfieldInclusion]
      exact glMap_subtype_fixed σ w₀.1
    have h3 : ρ₈ U (π₈ w₁) = π₈ ⟨_, hw⟩ := by
      change ρ₈ U (w₁ : LargeEvenProj H₈) = ((⟨_, hw⟩ : H₈) : LargeEvenProj H₈)
      rw [TableB.projConj_mk]
      congr 1
      apply Subtype.ext
      change (U : GL (Fin 3) K) * (w₁ : GL (Fin 3) K) * (U : GL (Fin 3) K)⁻¹ = Q * permGL τ * Q⁻¹
      rw [hw₁, hQdef, _root_.mul_inv_rev]
      group
    rw [MulAut.mul_apply, MulAut.mul_apply, h1, h2, h3]
  ·
    intro φ hφ
    obtain ⟨B, hB, μ, B', rfl, hB'gu, hB'eq⟩ := hdesc φ hφ
    obtain ⟨D', hD'⟩ := hdiagS B' (hdescS B hB μ B' hφ hB'eq) hB'gu
    refine ⟨⟨B, hNK hB⟩, hB, rfl, fun i => μ⁻¹ * Units.map ι.toMonoidHom (D' i), ?_⟩
    have hUBU : (U : GL (Fin 3) K)⁻¹ * B * U =
        Matrix.GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * Matrix.GeneralLinearGroup.map ι B' := by
      rw [hB'eq, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    change Q⁻¹ * B * Q = _
    calc Q⁻¹ * B * Q = Pι⁻¹ * ((U : GL (Fin 3) K)⁻¹ * B * U) * Pι := by
          rw [hQdef, _root_.mul_inv_rev]
          group
      _ = (Pι⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * Pι) *
            (Pι⁻¹ * Matrix.GeneralLinearGroup.map ι B' * Pι) := by
          rw [hUBU]
          group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) μ⁻¹ *
            Matrix.GeneralLinearGroup.map ι (P⁻¹ * B' * P) := by
          rw [conj_scalar_U3Three, hPιdef, map_mul, map_mul,
            map_inv (Matrix.GeneralLinearGroup.map ι) P]
      _ = _ := by
          rw [hD', map_diagHom, scalar_eq_diagHom_U3Three, ← map_mul]
          rfl
  ·
    have hUBU : (U : GL (Fin 3) K)⁻¹ * B₀K * U =
        Matrix.GeneralLinearGroup.scalar (Fin 3) μ₀⁻¹ * Matrix.GeneralLinearGroup.map ι B₀ := by
      rw [hB₀eq, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    change Q⁻¹ * B₀K * Q = _
    calc Q⁻¹ * B₀K * Q = Pι⁻¹ * ((U : GL (Fin 3) K)⁻¹ * B₀K * U) * Pι := by
          rw [hQdef, _root_.mul_inv_rev]
          group
      _ = (Pι⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) μ₀⁻¹ * Pι) *
            (Pι⁻¹ * Matrix.GeneralLinearGroup.map ι B₀ * Pι) := by
          rw [hUBU]
          group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) μ₀⁻¹ *
            Matrix.GeneralLinearGroup.map ι (P⁻¹ * B₀ * P) := by
          rw [conj_scalar_U3Three, hPιdef, map_mul, map_mul,
            map_inv (Matrix.GeneralLinearGroup.map ι) P]
      _ = _ := by
          rw [hσ', map_diagHom, scalar_eq_diagHom_U3Three, ← map_mul]
          rfl
  ·
    intro hinj0
    apply hninj
    intro a b hab
    apply hinj0
    simp only [hab]
  · intro h
    apply huv
    have h1 : Units.map ι.toMonoidHom (σ' u) = Units.map ι.toMonoidHom (σ' v) :=
      mul_left_cancel h
    exact Units.ext (ι.injective (congrArg Units.val h1))

end Proj

end ResU3Eight

end CFSG.StandardType

end
