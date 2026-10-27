module

public import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofKFact
public import CFSG.RankThree.PartTwo.KFacts.KS18OuterZ3
public import CFSG.RankThree.PartTwo.KFacts.KS18OuterHeis
public import CFSG.RankThree.PartTwo.KFacts.L34Automizer
public import CFSG.RankThree.PartTwo.KFacts.L34TwoElements
public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item181ThreeProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix
open CFSG.Assembly.RankThreeEven (projSL)

section Matrices

variable {k : Type} [Field k] [CharP k 2]

@[expose] def x5M : Matrix (Fin 3) (Fin 3) k := !![0, 1, 1; 1, 1, 1; 1, 0, 1]

@[expose] def x5 : SpecialLinearGroup (Fin 3) k :=
  ⟨x5M, by simp only [x5M, det_fin_three]; simp [CharTwo.neg_eq]⟩

@[expose] def x7M : Matrix (Fin 3) (Fin 3) k := !![0, 0, 1; 0, 1, 1; 1, 1, 0]

@[expose] def x7 : SpecialLinearGroup (Fin 3) k :=
  ⟨x7M, by simp only [x7M, det_fin_three]; simp [CharTwo.neg_eq]⟩

@[expose] def y7M : Matrix (Fin 3) (Fin 3) k := !![1, 1, 0; 1, 0, 1; 0, 1, 0]

@[expose] def y7 : SpecialLinearGroup (Fin 3) k :=
  ⟨y7M, by simp only [y7M, det_fin_three]; simp [CharTwo.neg_eq]⟩

theorem x5_inv_transpose :
    ((x5 : SpecialLinearGroup (Fin 3) k)⁻¹).transpose = LinearFieldFourKernel.jMat * x5 := by
  apply Subtype.ext
  change (adjugate x5M).transpose = LinearFieldFourKernel.jM * x5M
  rw [adjugate_fin_three]
  simp only [x5M, LinearFieldFourKernel.jM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq, CharTwo.add_self_eq_zero]

theorem x7_inv_transpose :
    ((x7 : SpecialLinearGroup (Fin 3) k)⁻¹).transpose = x7⁻¹ := by
  apply Subtype.ext
  change (adjugate x7M).transpose = adjugate x7M
  rw [adjugate_fin_three]
  simp only [x7M]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq, CharTwo.add_self_eq_zero]

theorem x7_mul_x7 : (x7 : SpecialLinearGroup (Fin 3) k) * x7 = y7 := by
  apply Subtype.ext
  change x7M * x7M = y7M
  simp only [x7M, y7M, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

theorem y7_pow_seven : (y7 : SpecialLinearGroup (Fin 3) k) ^ 7 = 1 := by
  have h : (y7 : SpecialLinearGroup (Fin 3) k) ^ 7 = y7 * y7 * y7 * y7 * y7 * y7 * y7 := by
    simp only [pow_succ, pow_zero, one_mul]
  rw [h]
  apply Subtype.ext
  change y7M * y7M * y7M * y7M * y7M * y7M * y7M = 1
  simp only [y7M, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

theorem y7_not_mem_scalars : (y7 : SpecialLinearGroup (Fin 3) k) ∉ scalars 3 k := by
  intro h
  obtain ⟨c, -, hc⟩ := mem_scalars.mp h
  have h01 := congrFun (congrFun hc 0) 1
  change y7M 0 1 = _ at h01
  simp [y7M, Matrix.scalar_apply] at h01

theorem map_x5 (σ : k ≃+* k) :
    SpecialLinearGroup.map σ.toRingHom (x5 : SpecialLinearGroup (Fin 3) k) = x5 := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe]
  change σ.toRingHom.mapMatrix x5M = x5M
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x5M]

theorem map_x7 (σ : k ≃+* k) :
    SpecialLinearGroup.map σ.toRingHom (x7 : SpecialLinearGroup (Fin 3) k) = x7 := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe]
  change σ.toRingHom.mapMatrix x7M = x7M
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x7M]

theorem map_jMat (σ : k ≃+* k) :
    SpecialLinearGroup.map σ.toRingHom (LinearFieldFourKernel.jMat : SpecialLinearGroup (Fin 3) k) =
      LinearFieldFourKernel.jMat := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe]
  change σ.toRingHom.mapMatrix LinearFieldFourKernel.jM = LinearFieldFourKernel.jM
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearFieldFourKernel.jM]

end Matrices

theorem conj_mul_mulAut_mul_inv {P : Type*} [Group P] (α : MulAut P) (g : P) :
    MulAut.conj g * α * (MulAut.conj g)⁻¹ = MulAut.conj (g * (α g)⁻¹) * α := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply, map_mul, map_inv]

section Beta

variable {k : Type} [Field k] [CharP k 2] {σ : k ≃+* k}

omit [CharP k 2] in
theorem betaAut_proj (g : SpecialLinearGroup (Fin 3) k) :
    L34.betaAut σ (proj 3 k g) =
      proj 3 k (SpecialLinearGroup.map σ.toRingHom (g⁻¹).transpose) := by
  rw [L34.betaAut, MulAut.mul_apply, dualAut_proj, fieldAut_proj]

theorem betaAut_proj_x5 :
    L34.betaAut σ (proj 3 k x5) = proj 3 k LinearFieldFourKernel.jMat * proj 3 k x5 := by
  rw [betaAut_proj, x5_inv_transpose, map_mul, map_jMat, map_x5, map_mul]

theorem betaAut_proj_x7 : L34.betaAut σ (proj 3 k x7) = (proj 3 k x7)⁻¹ := by
  rw [betaAut_proj, x7_inv_transpose, map_inv, map_x7, map_inv]

omit [CharP k 2] in
theorem conj_mul_betaAut_mul_inv (g : projectiveSL 3 k) :
    MulAut.conj g * L34.betaAut σ * (MulAut.conj g)⁻¹ =
      MulAut.conj (g * (L34.betaAut σ g)⁻¹) * L34.betaAut σ :=
  conj_mul_mulAut_mul_inv _ g

theorem conj_x5_mul_betaAut :
    MulAut.conj (proj 3 k x5) * L34.betaAut σ * (MulAut.conj (proj 3 k x5))⁻¹ =
      MulAut.conj (proj 3 k LinearFieldFourKernel.jMat) * L34.betaAut σ := by
  rw [conj_mul_betaAut_mul_inv, betaAut_proj_x5]
  congr 2
  have hj : proj 3 k LinearFieldFourKernel.jMat * proj 3 k LinearFieldFourKernel.jMat =
      (1 : projectiveSL 3 k) := by
    rw [← map_mul, LinearFieldFourKernel.jMat_mul_self, map_one]
  calc proj 3 k x5 * (proj 3 k LinearFieldFourKernel.jMat * proj 3 k x5)⁻¹ =
        (proj 3 k LinearFieldFourKernel.jMat)⁻¹ := by group
    _ = proj 3 k LinearFieldFourKernel.jMat := inv_eq_of_mul_eq_one_right hj

theorem conj_x7_mul_beta (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2) :
    MulAut.conj (proj 3 k x7) * L34.betaAut σ * (MulAut.conj (proj 3 k x7))⁻¹ *
        L34.betaAut σ = MulAut.conj (proj 3 k y7) := by
  rw [conj_mul_betaAut_mul_inv, betaAut_proj_x7, mul_assoc, L34.betaAut_mul_self hk hσ,
    mul_one, inv_inv, ← map_mul, x7_mul_x7]

theorem proj_jMat_conj (hk : Nat.card k = 4) {x : projectiveSL 3 k} (hx : x ∈ L34.eZero k) :
    proj 3 k LinearFieldFourKernel.jMat * x * (proj 3 k LinearFieldFourKernel.jMat)⁻¹ = x⁻¹ := by
  obtain ⟨u, hu⟩ := L34.exists_units_ne_one hk
  set t := proj 3 k LinearFieldFourKernel.jMat with htdef
  have htt : t * t = 1 := by rw [← map_mul, LinearFieldFourKernel.jMat_mul_self, map_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have ha : t * L34.aP u * t⁻¹ = (L34.aP u)⁻¹ := by
    rw [htinv, L34.aP, ← map_mul, ← map_mul, L34.jMat_mul_hSL_mul_jMat hk hu, map_inv]
  have hb : t * L34.bP * t⁻¹ = L34.bP⁻¹ := by
    rw [htinv, L34.bP, ← map_mul, ← map_mul, L34.jMat_mul_rSL_mul_jMat, map_inv]
  obtain ⟨i, j, -, -, rfl⟩ := L34.exists_eq_aP_pow_mul_bP_pow hk hu hx
  have hab : Commute (L34.aP u) L34.bP :=
    L34.commute_of_mem_eZero hk L34.aP_mem_eZero L34.bP_mem_eZero
  calc t * (L34.aP u ^ i * L34.bP ^ j) * t⁻¹ =
        (t * L34.aP u * t⁻¹) ^ i * (t * L34.bP * t⁻¹) ^ j := by
        rw [← MulAut.conj_apply, map_mul, map_pow, map_pow, MulAut.conj_apply, MulAut.conj_apply]
    _ = (L34.aP u ^ i * L34.bP ^ j)⁻¹ := by
        rw [ha, hb, inv_pow, inv_pow, _root_.mul_inv_rev, ((hab.pow_pow i j).inv_inv).eq]

theorem conj_jMat_mul_betaAut_apply (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2)
    {x : projectiveSL 3 k} (hx : x ∈ L34.eZero k) :
    (MulAut.conj (proj 3 k LinearFieldFourKernel.jMat) * L34.betaAut σ) x = x⁻¹ := by
  rw [MulAut.mul_apply, L34.betaAut_fixed hk hσ hx, MulAut.conj_apply, proj_jMat_conj hk hx]

theorem orderOf_proj_y7 : orderOf (proj 3 k (y7 : SpecialLinearGroup (Fin 3) k)) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, y7_pow_seven, map_one]
  · rw [Ne, proj_eq_one_iff]
    exact y7_not_mem_scalars

end Beta

section Transvections

variable {V : Type*} [CommGroup V] [Finite V]

theorem exists_pow_eq_one_of_card_range_le_two (hV2 : ∀ v : V, v * v = 1) {τ₁ τ₂ : MulAut V}
    (h₁ : Nat.card (Sec3.commHom τ₁).range ≤ 2) (h₂ : Nat.card (Sec3.commHom τ₂).range ≤ 2) :
    ∃ n : ℕ, ¬ 7 ∣ n ∧ (τ₁ * τ₂) ^ n = 1 := by
  classical
  set R₁ := (Sec3.commHom τ₁).range with hR₁
  set R₂ := (Sec3.commHom τ₂).range with hR₂
  set W := R₁ ⊔ R₂ with hW
  have hW4 : Nat.card W ≤ 4 := by
    have h := Sec3.card_sup_mul_card_inf_of_commute (K := R₁) (L := R₂)
      (fun a _ b _ => mul_comm a b)
    have hpos : 0 < Nat.card ↥(R₁ ⊓ R₂) := Nat.card_pos
    nlinarith
  set good : MulAut V → Prop := fun φ => ∀ v, v⁻¹ * φ v ∈ W with hgood
  have hgood1 : good τ₁ := fun v => Subgroup.mem_sup_left ⟨v, rfl⟩
  have hgood2 : good τ₂ := fun v => Subgroup.mem_sup_right ⟨v, rfl⟩
  have hgood_mul : ∀ φ ψ, good φ → good ψ → good (φ * ψ) := by
    intro φ ψ hφ hψ v
    rw [MulAut.mul_apply]
    have e : v⁻¹ * φ (ψ v) = (v⁻¹ * ψ v) * ((ψ v)⁻¹ * φ (ψ v)) := by group
    rw [e]
    exact W.mul_mem (hψ v) (hφ (ψ v))
  have hgood_pow : ∀ φ, good φ → ∀ n : ℕ, good (φ ^ n) := by
    intro φ hφ n
    induction n with
    | zero => intro v; rw [pow_zero, MulAut.one_apply, inv_mul_cancel]; exact W.one_mem
    | succ n ih => rw [pow_succ]; exact hgood_mul _ _ ih hφ
  have hgood_inv : ∀ φ, good φ → good φ⁻¹ := by
    intro φ hφ v
    have h := W.inv_mem (hφ (φ⁻¹ v))
    have e : φ (φ⁻¹ v) = v := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    rw [e] at h
    simpa using h
  have hmapsW : ∀ φ, good φ → ∀ w ∈ W, φ w ∈ W := fun φ hφ w hw => by
    have := W.mul_mem hw (hφ w)
    simpa using this
  set g := τ₁ * τ₂ with hgdef
  have hg : good g := hgood_mul _ _ hgood1 hgood2
  have hg' : good g⁻¹ := hgood_inv g hg
  let π : Equiv.Perm W :=
    { toFun := fun w => ⟨g w, hmapsW g hg w w.2⟩
      invFun := fun w => ⟨g⁻¹ w, hmapsW _ hg' w w.2⟩
      left_inv := fun w => Subtype.ext (by
        change g⁻¹ (g w) = w
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply])
      right_inv := fun w => Subtype.ext (by
        change g (g⁻¹ w) = w
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]) }
  have hπpow : ∀ n : ℕ, ∀ w : W, ((π ^ n) w : V) = (g ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, MulAut.mul_apply]
      rfl
  set N := Nat.card (Equiv.Perm W) with hN
  have hfix : ∀ w ∈ W, (g ^ N) w = w := by
    intro w hw
    have h := hπpow N ⟨w, hw⟩
    rw [pow_card_eq_one'] at h
    exact h.symm
  have hsq : g ^ N * g ^ N = 1 := by
    ext v
    rw [MulAut.mul_apply, MulAut.one_apply]
    set f := v⁻¹ * (g ^ N) v with hfdef
    have hf : f ∈ W := hgood_pow g hg N v
    have e : (g ^ N) v = v * f := by rw [hfdef]; group
    rw [e, map_mul, hfix f hf, e, mul_assoc, hV2, mul_one]
  refine ⟨2 * N, ?_, ?_⟩
  · rw [hN, Nat.card_perm]
    intro h7
    have h7' : 7 ∣ (Nat.card W).factorial :=
      (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h7)
    have := (Nat.Prime.dvd_factorial (by norm_num)).mp h7'
    omega
  · rw [mul_comm, pow_mul, sq, hsq]

omit [Finite V] in
theorem card_range_commHom_conj (φ τ : MulAut V) :
    Nat.card (Sec3.commHom (φ * τ * φ⁻¹)).range = Nat.card (Sec3.commHom τ).range := by
  have h : (Sec3.commHom (φ * τ * φ⁻¹)).range = (Sec3.commHom τ).range.map φ.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨Sec3.commHom τ (φ⁻¹ v), ⟨φ⁻¹ v, rfl⟩, ?_⟩
      have e : φ (φ⁻¹ v) = v := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      simp only [MulEquiv.coe_toMonoidHom, Sec3.commHom_apply, map_mul, map_inv, e,
        MulAut.mul_apply]
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      refine ⟨φ v, ?_⟩
      have e : φ⁻¹ (φ v) = v := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      simp only [MulEquiv.coe_toMonoidHom, Sec3.commHom_apply, map_mul, map_inv, e,
        MulAut.mul_apply]
  rw [h, Subgroup.card_map_of_injective φ.injective]

theorem card_range_le_two_of_lt_four (hV2 : ∀ v : V, v * v = 1) {τ : MulAut V}
    (h : Nat.card (Sec3.commHom τ).range < 4) : Nat.card (Sec3.commHom τ).range ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : IsPGroup 2 V := fun v => ⟨1, by rw [pow_one, pow_two]; exact hV2 v⟩
  obtain ⟨j, hj⟩ := (hV.to_subgroup (Sec3.commHom τ).range).exists_card_eq
  rw [hj] at h ⊢
  have hj1 : j ≤ 1 := by
    by_contra hj1
    push Not at hj1
    have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
    omega
  calc 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
    _ = 2 := by norm_num

end Transvections

theorem forall_eq_one_of_mem_ker {Y : Type*} [Group Y] {L : Subgroup Y} [L.Normal]
    (hL : commutator L = ⊤) {P : Type*} [Group P] [IsSimpleGroup P]
    (ψ : L ⧸ Subgroup.center L ≃* P) {M : Type*} [Group M] (ρ : Y →* M) {x : L}
    (hx : ψ (x : L ⧸ Subgroup.center L) ≠ 1) (hρx : ρ x = 1) : ∀ l ∈ L, ρ l = 1 := by
  set K : Subgroup L := (ρ.comp L.subtype).ker with hK
  have hKn : K.Normal := MonoidHom.normal_ker _
  set K' : Subgroup P := (K.map (QuotientGroup.mk' (Subgroup.center L))).map ψ.toMonoidHom
    with hK'
  have hK'n : K'.Normal :=
    (hKn.map _ (QuotientGroup.mk'_surjective _)).map _ ψ.surjective
  have hK'top : K' = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K' with h | h
    · exfalso
      apply hx
      have hmem : ψ (x : L ⧸ Subgroup.center L) ∈ K' := ⟨_, ⟨x, hρx, rfl⟩, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    · exact h
  have hdec : ∀ l : L, ∃ k ∈ K, k⁻¹ * l ∈ Subgroup.center L := by
    intro l
    have hmem : ψ (l : L ⧸ Subgroup.center L) ∈ K' := hK'top ▸ Subgroup.mem_top _
    obtain ⟨_, ⟨k, hk, rfl⟩, hkl⟩ := hmem
    exact ⟨k, hk, QuotientGroup.eq.mp (ψ.injective hkl)⟩
  have hmk : ∀ l : L, ∃ z ∈ Subgroup.center L, (l : L ⧸ K) = (z : L ⧸ K) := by
    intro l
    obtain ⟨k, hk, hz⟩ := hdec l
    refine ⟨k⁻¹ * l, hz, QuotientGroup.eq.mpr ?_⟩
    have : l⁻¹ * (k⁻¹ * l) = l⁻¹ * k⁻¹ * l⁻¹⁻¹ := by group
    rw [this]
    exact hKn.conj_mem _ (K.inv_mem hk) _
  have : IsMulCommutative (L ⧸ K) := ⟨⟨by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
    obtain ⟨z₁, hz₁, h₁⟩ := hmk a
    obtain ⟨z₂, hz₂, h₂⟩ := hmk b
    rw [h₁, h₂, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      (Subgroup.mem_center_iff.mp hz₁ z₂)]⟩⟩
  have hle : commutator L ≤ K := by
    have := Abelianization.commutator_subset_ker (QuotientGroup.mk' K)
    rwa [QuotientGroup.ker_mk'] at this
  intro l hl
  have hlK : (⟨l, hl⟩ : L) ∈ K := hle (hL ▸ Subgroup.mem_top _)
  exact hlK


section Core

open KS18

variable {Y : Type} [Group Y] [Finite Y]

theorem isSimpleGroup_projectiveSL_three (k : Type) [Field k] :
    IsSimpleGroup (projectiveSL 3 k) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := k) (n := 3) (by omega)
    (Or.inl le_rfl)).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k).symm.isSimpleGroup

theorem conj_mul_mul_inv_apply {P : Type*} [Group P] (h : P) (α₀ : MulAut P) (x : P) :
    (MulAut.conj h * α₀ * (MulAut.conj h)⁻¹) (h * x * h⁻¹) = h * α₀ x * h⁻¹ := by
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply,
    show h⁻¹ * (h * x * h⁻¹) * h = x by group, MulAut.conj_apply]

theorem core_bound {k : Type} [Field k] (hk : Nat.card k = 4) (hO : CFSG.pCore 2 Y = ⊥)
    {X L E : Subgroup Y} {t : Y} [L.Normal] (hX : X.Normal) (hL : commutator L = ⊤)
    (ψ : L ⧸ Subgroup.center L ≃* projectiveSL 3 k)
    (hXLC : ∀ x ∈ X, ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), x = l * c)
    (hCX : IsPGroup 3 ↥(X ⊓ Subgroup.centralizer (L : Set Y)))
    (hEC : Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Y)) ≤ 3)
    (hKX : ∀ R : Subgroup Y, IsPGroup 2 R → R ≤ Subgroup.centralizer (L : Set Y) →
      R ≤ Subgroup.centralizer (E : Set Y) → R ≤ Subgroup.centralizer (X : Set Y))
    (htX : t ∉ X) (hYt : X ⊔ Subgroup.zpowers t = ⊤) (ht2 : IsPGroup 2 (Subgroup.zpowers t))
    (hEX : E ≤ X) (hE3 : IsPGroup 3 E) (hE27 : Nat.card E = 27)
    (hEt : E ≤ Subgroup.centralizer ({t} : Set Y)) (hres : perfectResidual Y ≤ L)
    (V : Type) [CommGroup V] [Finite V] (hV2 : ∀ v : V, v * v = 1) (ρ : Y →* MulAut V)
    (hρ : ∃ y ∈ perfectResidual Y, ρ y ≠ 1) :
    4 ≤ Nat.card (Sec3.commHom (ρ t)).range ∧
      (Subgroup.center L = ⊥ → 16 ≤ Nat.card (Sec3.commHom (ρ t)).range) := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  have := isSimpleGroup_projectiveSL_three k
  have := hX
  set σ := frobeniusEquiv k 2 with hσdef
  set β := L34.betaAut σ with hβdef
  have h7 : MulAut.conj (proj 3 k x7) * β * (MulAut.conj (proj 3 k x7))⁻¹ * β =
      MulAut.conj (proj 3 k y7) := conj_x7_mul_beta hk hσ
  have h5 : MulAut.conj (proj 3 k x5) * β * (MulAut.conj (proj 3 k x5))⁻¹ =
      MulAut.conj (proj 3 k LinearFieldFourKernel.jMat) * β := conj_x5_mul_betaAut
  have hj : ∀ x ∈ L34.eZero k, (MulAut.conj (proj 3 k LinearFieldFourKernel.jMat) * β) x = x⁻¹ :=
    fun x hx => conj_jMat_mul_betaAut_apply hk hσ hx
  set α := actOn L ψ with hα
  have ht : t ^ 2 = 1 := (outer_involution_of_inner hk hO hX hL ψ hXLC hCX hEC hKX htX hYt ht2
    hEX hE3 hE27 hEt).1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ht)
  have hαt : α t ≠ 1 := by
    intro h1
    have htL := mem_centralizer_of_actOn_eq_one hL ψ h1
    have htE : Subgroup.zpowers t ≤ Subgroup.centralizer (E : Set Y) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro e he
      exact Subgroup.mem_centralizer_singleton_iff.mp (hEt he)
    have hbot := eq_bot_of_le_centralizer_of_sup hO hYt ht2
      (hKX _ ht2 (Subgroup.zpowers_le.mpr htL) htE)
    rw [Subgroup.zpowers_eq_bot] at hbot
    exact htX (hbot ▸ X.one_mem)
  obtain ⟨E9, hE9c, hE9⟩ := exists_E9 ψ hk hL hXLC hEX hE3 hE27 hEC
  have hfix : ∀ g ∈ E9, α t g = g := by
    intro g hg
    obtain ⟨e, he, hαe⟩ := hE9 g hg
    have hte : t * e * t⁻¹ = e := by
      rw [(Subgroup.mem_centralizer_singleton_iff.mp (hEt he)).symm, mul_inv_cancel_right]
    have h1 : α t * MulAut.conj g * (α t)⁻¹ = MulAut.conj g := by
      rw [← hαe, ← map_inv, ← map_mul, ← map_mul, hte]
    rw [KFacts.mul_mulAutConj_mul_inv] at h1
    exact L34.conj_injective hk h1
  obtain ⟨h, rfl⟩ := L34.exists_eq_map_conj_eZero hk hE9c
  have hαtβ : α t = MulAut.conj h * β * (MulAut.conj h)⁻¹ := by
    set α' := (MulAut.conj h)⁻¹ * α t * MulAut.conj h with hα'
    have hfix' : ∀ x ∈ L34.eZero k, α' x = x := by
      intro x hx
      have h2 := hfix (h * x * h⁻¹) ⟨x, hx, rfl⟩
      rw [hα', MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, h2, MulAut.conj_inv_apply]
      group
    have hsq : α' * α' = 1 := by
      have : α t * α t = 1 := by rw [← map_mul, ← pow_two, ht, map_one]
      rw [hα']
      calc (MulAut.conj h)⁻¹ * α t * MulAut.conj h * ((MulAut.conj h)⁻¹ * α t * MulAut.conj h)
          = (MulAut.conj h)⁻¹ * (α t * α t) * MulAut.conj h := by group
        _ = 1 := by rw [this]; group
    have h3 : ¬ 3 ∣ orderOf α' := by
      intro h3
      have h2 : orderOf α' ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
      have := Nat.le_of_dvd (by norm_num) (h3.trans h2)
      omega
    rcases L34.eq_one_or_eq_betaAut hk hσ hfix' h3 with h1 | h1
    · exfalso
      apply hαt
      calc α t = MulAut.conj h * α' * (MulAut.conj h)⁻¹ := by rw [hα']; group
        _ = 1 := by rw [h1]; group
    · calc α t = MulAut.conj h * α' * (MulAut.conj h)⁻¹ := by rw [hα']; group
        _ = MulAut.conj h * β * (MulAut.conj h)⁻¹ := by rw [h1]
  have hlift : ∀ p : projectiveSL 3 k, ∃ l : L, ψ (l : L ⧸ Subgroup.center L) = p := by
    intro p
    obtain ⟨q, hq⟩ := ψ.surjective p
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, hq⟩
  have hαl : ∀ l : L, α l = MulAut.conj (ψ (l : L ⧸ Subgroup.center L)) := fun l => by
    rw [hα, actOn_of_mem L ψ l.2]
  have hρL : ¬ ∀ l ∈ L, ρ l = 1 := by
    intro hall
    obtain ⟨y, hy, hρy⟩ := hρ
    exact hρy (hall y (hres hy))
  have hconj : ∀ g : projectiveSL 3 k, MulAut.conj (h * g * h⁻¹) =
      MulAut.conj h * MulAut.conj g * (MulAut.conj h)⁻¹ := fun g => by
    rw [map_mul, map_mul, map_inv]
  constructor
  ·
    by_contra h4
    push Not at h4
    have h2 := card_range_le_two_of_lt_four hV2 h4
    obtain ⟨y, hy⟩ := hlift (h * proj 3 k x7 * h⁻¹)
    set x : Y := (y : Y) * t * (y : Y)⁻¹ * t with hxdef
    have hxL : x ∈ L := by
      have e : x = (y : Y) * (t * (y : Y)⁻¹ * t⁻¹) := by rw [hxdef, htinv]; group
      rw [e]
      exact L.mul_mem y.2 (Subgroup.Normal.conj_mem inferInstance _ (L.inv_mem y.2) t)
    have hαx : α x = MulAut.conj (h * proj 3 k y7 * h⁻¹) := by
      rw [hxdef, map_mul, map_mul, map_mul, map_inv, hαl y, hy, hαtβ, hconj, hconj, ← h7]
      group
    have hψx : ψ ((⟨x, hxL⟩ : L) : L ⧸ Subgroup.center L) = h * proj 3 k y7 * h⁻¹ := by
      apply L34.conj_injective hk
      rw [← hαx]
      exact (hαl ⟨x, hxL⟩).symm
    have hord : orderOf (h * proj 3 k y7 * h⁻¹) = 7 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_proj_y7]
    have hcard1 : Nat.card (Sec3.commHom (ρ y * ρ t * (ρ y)⁻¹)).range ≤ 2 := by
      rw [card_range_commHom_conj]
      exact h2
    obtain ⟨n, hn7, hn⟩ := exists_pow_eq_one_of_card_range_le_two hV2 hcard1 h2
    have hρx : ρ x = ρ y * ρ t * (ρ y)⁻¹ * ρ t := by
      rw [hxdef, map_mul, map_mul, map_mul, map_inv]
    apply hρL
    refine forall_eq_one_of_mem_ker hL ψ ρ (x := (⟨x, hxL⟩ : L) ^ n) ?_ ?_
    · rw [QuotientGroup.mk_pow, map_pow, hψx]
      intro h1
      exact hn7 (hord ▸ orderOf_dvd_of_pow_eq_one h1)
    · rw [Subgroup.coe_pow, map_pow, hρx]
      exact hn
  ·
    intro hZ
    set φ : L →* projectiveSL 3 k := ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
      with hφ
    have hφinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro l hl
      have h1 : (l : L ⧸ Subgroup.center L) = 1 := ψ.injective (by rw [map_one]; exact hl)
      rw [QuotientGroup.eq_one_iff, hZ, Subgroup.mem_bot] at h1
      exact h1
    have hφsurj : Function.Surjective φ := fun p => by
      obtain ⟨l, hl⟩ := hlift p
      exact ⟨l, hl⟩
    set φe : L ≃* projectiveSL 3 k := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩ with hφe
    have hφe_apply : ∀ l : L, φe l = ψ (l : L ⧸ Subgroup.center L) := fun l => rfl
    set Bp : Subgroup (projectiveSL 3 k) := (L34.eZero k).map (MulAut.conj h).toMonoidHom
      with hBp
    obtain ⟨y, hy⟩ := hlift (h * proj 3 k x5 * h⁻¹)
    set t₅ : Y := (y : Y) * t * (y : Y)⁻¹ with ht₅
    have hαt₅ : α t₅ = MulAut.conj h *
        (MulAut.conj (proj 3 k LinearFieldFourKernel.jMat) * β) * (MulAut.conj h)⁻¹ := by
      rw [ht₅, map_mul, map_mul, map_inv, hαl y, hy, hαtβ, hconj, ← h5]
      group
    have hinvP : ∀ b ∈ Bp, α t₅ b = b⁻¹ := by
      rintro _ ⟨e₀, he₀, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hαt₅, conj_mul_mul_inv_apply, hj e₀ he₀]
      group
    have hinvY : ∀ b ∈ Bp, t₅ * (φe.symm b : Y) * t₅⁻¹ = ((φe.symm b : L) : Y)⁻¹ := by
      intro b hb
      have h1 := actOn_apply L ψ t₅ (φe.symm b)
      have h2 : ψ ((φe.symm b : L) : L ⧸ Subgroup.center L) = b := by
        rw [← hφe_apply, MulEquiv.apply_symm_apply]
      rw [← hα, h2, hinvP b hb] at h1
      have h3 : φe (MulAut.conjNormal t₅ (φe.symm b)) = φe (φe.symm b)⁻¹ := by
        rw [hφe_apply, ← h1, map_inv, MulEquiv.apply_symm_apply]
      have h4 := congrArg Subtype.val (φe.injective h3)
      rw [MulAut.conjNormal_apply] at h4
      rw [h4, Subgroup.coe_inv]
    have hBc : Nat.card Bp = 9 := hE9c
    have hBab := L34.isElementaryAbelian_of_card_eq_nine hk hBc
    let _ : CommGroup Bp := { (inferInstance : Group Bp) with
      mul_comm := fun a b => hBab.toIsMulCommutative.is_comm.comm a b }
    let _ : Fintype Bp := Fintype.ofFinite Bp
    set βB : Bp →* MulAut V :=
      (ρ.comp L.subtype).comp (φe.symm.toMonoidHom.comp Bp.subtype) with hβB
    have hβB_apply : ∀ b : Bp, βB b = ρ ((φe.symm b : L) : Y) := fun b => rfl
    have h3 : ∀ b : Bp, b ^ 3 = 1 := fun b => by
      have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (CFSG.IsElementaryAbelian.exponent_dvd_p 3 Bp) b
      exact this
    have hβ : ∃ b v, βB b v ≠ v := by
      by_contra hcon
      push Not at hcon
      have : Nontrivial Bp := Finite.one_lt_card_iff_nontrivial.mp (by rw [hBc]; norm_num)
      obtain ⟨b, hb1⟩ := exists_ne (1 : Bp)
      apply hρL
      refine forall_eq_one_of_mem_ker hL ψ ρ (x := φe.symm b) ?_ ?_
      · rw [← hφe_apply, MulEquiv.apply_symm_apply]
        intro h1
        exact hb1 (Subtype.ext h1)
      · ext v
        rw [MulAut.one_apply, ← hβB_apply]
        exact hcon b v
    have htr : ∀ d d' : Bp, d ≠ 1 → d' ≠ 1 → ∃ (ν : MulAut V) (σ' : MulAut Bp),
        σ' d = d' ∧ ∀ b, ν * βB b * ν⁻¹ = βB (σ' b) := by
      intro d d' hd hd'
      obtain ⟨n, hn, hnd⟩ := L34.exists_mem_normalizer_conj_eq_of_card_eq_nine hk hBc d.2
        (fun h1 => hd (Subtype.ext h1)) d'.2 (fun h1 => hd' (Subtype.ext h1))
      refine ⟨ρ ((φe.symm n : L) : Y), Bp.normalizerMonoidHom ⟨n, hn⟩, Subtype.ext ?_,
        fun b => ?_⟩
      · rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        exact hnd
      · rw [hβB_apply, hβB_apply, ← map_inv, ← map_mul, ← map_mul]
        congr 1
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe, map_mul, map_mul, map_inv]
        rfl
    have hτ : ∀ b v, ρ t₅ (βB b v) = βB b⁻¹ (ρ t₅ v) := by
      intro b v
      have h1 := hinvY b b.2
      set g : Y := ((φe.symm b : L) : Y) with hg
      have h2 : ρ t₅ * βB b = (βB b)⁻¹ * ρ t₅ := by
        rw [hβB_apply, ← hg, ← map_mul, ← map_inv, ← map_mul]
        congr 1
        calc t₅ * g = t₅ * g * t₅⁻¹ * t₅ := by group
          _ = g⁻¹ * t₅ := by rw [h1]
      rw [map_inv]
      change (ρ t₅ * βB b) v = ((βB b)⁻¹ * ρ t₅) v
      rw [h2]
    have h16 := Sec3.sixteen_le_card_range_commHom hV2 h3 hBc βB hβ htr hτ
    have hρt₅ : ρ t₅ = ρ y * ρ t * (ρ y)⁻¹ := by rw [ht₅, map_mul, map_mul, map_inv]
    rwa [hρt₅, card_range_commHom_conj] at h16

end Core


section Setups

open KS18
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

theorem bound_Z3_of {k : Type} [Field k] (hk : Nat.card k = 4) (hO : CFSG.pCore 2 Y = ⊥)
    {X : Subgroup Y} (e : X ≃* Multiplicative (ZMod 3) × projectiveSL 3 k) (hX : X.Normal)
    {L : Subgroup Y} [L.Normal] (hLeq : L = (inrY e).range) {t : Y} {E : Subgroup Y}
    (htX : t ∉ X) (hYt : X ⊔ Subgroup.zpowers t = ⊤) (ht2 : IsPGroup 2 (Subgroup.zpowers t))
    (hEX : E ≤ X) (hE3 : IsPGroup 3 E) (hE27 : Nat.card E = 27)
    (hEt : E ≤ Subgroup.centralizer ({t} : Set Y)) (hres : perfectResidual Y ≤ L)
    (V : Type) [CommGroup V] [Finite V] (hV2 : ∀ v : V, v * v = 1) (ρ : Y →* MulAut V)
    (hρ : ∃ y ∈ perfectResidual Y, ρ y ≠ 1) :
    4 ≤ Nat.card (Sec3.commHom (ρ t)).range ∧ 16 ≤ Nat.card (Sec3.commHom (ρ t)).range := by
  let φ : L ≃* projectiveSL 3 k :=
    (MulEquiv.subgroupCongr hLeq).trans (MonoidHom.ofInjective (inrY_injective e)).symm
  have hZ : Subgroup.center L = ⊥ := by
    have h := Subgroup.map_center_eq φ
    rw [LinearThreeFourOuter.center_projectiveSL_three_eq_bot hk] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h
  let ψ : L ⧸ Subgroup.center L ≃* projectiveSL 3 k :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans φ)
  have hL : commutator L = ⊤ := by
    have := isPerfect_projectiveSL k
    have : Group.IsPerfect L :=
      Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hXLC : ∀ x ∈ X, ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), x = l * c := by
    intro x hx
    obtain ⟨p, z, rfl⟩ := exists_eq_inrY_mul_inlY e hx
    exact ⟨inrY e p, hLeq ▸ ⟨p, rfl⟩, inlY e z, hLeq ▸ inlY_mem_centralizer e z, rfl⟩
  have hXC : X ⊓ Subgroup.centralizer (L : Set Y) ≤ (inlY e).range := by
    rintro x ⟨hx, hc⟩
    rw [hLeq] at hc
    exact mem_range_inlY_of_mem_centralizer e hk hx hc
  have hCX : IsPGroup 3 ↥(X ⊓ Subgroup.centralizer (L : Set Y)) :=
    (IsPGroup.of_card (n := 1) (by rw [card_range_inlY, pow_one])).to_le hXC
  have hEXC : E ⊓ Subgroup.centralizer (L : Set Y) ≤ (inlY e).range :=
    (inf_le_inf_right _ hEX).trans hXC
  have hEC : Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Y)) ≤ 3 := by
    rw [← card_range_inlY e]
    exact Subgroup.card_le_of_le hEXC
  have hKX : ∀ R : Subgroup Y, IsPGroup 2 R → R ≤ Subgroup.centralizer (L : Set Y) →
      R ≤ Subgroup.centralizer (E : Set Y) → R ≤ Subgroup.centralizer (X : Set Y) := by
    have h3 := three_le_card_inf_centralizer ψ hk hL hXLC hEX hE3 hE27
    have hEq : E ⊓ Subgroup.centralizer (L : Set Y) = (inlY e).range :=
      Subgroup.eq_of_le_of_card_ge hEXC (by rw [card_range_inlY]; exact h3)
    intro R _ hRL hRE r hr
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨p, z, rfl⟩ := exists_eq_inrY_mul_inlY e hx
    have h1 : inrY e p * r = r * inrY e p :=
      Subgroup.mem_centralizer_iff.mp (hRL hr) _ (hLeq ▸ ⟨p, rfl⟩)
    have hzE : inlY e z ∈ E := by
      have : inlY e z ∈ E ⊓ Subgroup.centralizer (L : Set Y) := hEq ▸ ⟨z, rfl⟩
      exact this.1
    have h2 : inlY e z * r = r * inlY e z := Subgroup.mem_centralizer_iff.mp (hRE hr) _ hzE
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  have hcore := core_bound hk hO hX hL ψ hXLC hCX hEC hKX htX hYt ht2 hEX hE3 hE27 hEt hres V
    hV2 ρ hρ
  exact ⟨hcore.1, hcore.2 hZ⟩

theorem bound_heis_of (hO : CFSG.pCore 2 Y = ⊥) {X : Subgroup Y}
    (hX : X.Normal) {U W₀ : Subgroup X} (hsup : U ⊔ W₀ = ⊤)
    (hUV : ∀ u ∈ U, ∀ v ∈ W₀, u * v = v * u) (hU : Sec4.IsHeisThree U)
    (eV : W₀ ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    (h3 : Nat.card (U ⊓ W₀ : Subgroup X) = 3) {L : Subgroup Y} [L.Normal]
    (hLV : L = W₀.map X.subtype) (hLX : ⁅X, X⁆ = L) {t : Y} {E : Subgroup Y} (htX : t ∉ X)
    (hYt : X ⊔ Subgroup.zpowers t = ⊤) (ht2 : IsPGroup 2 (Subgroup.zpowers t)) (hEX : E ≤ X)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEt : E ≤ Subgroup.centralizer ({t} : Set Y))
    (hB : ∀ B : Subgroup Y, B ≤ E → Nat.card B = 9 →
      ¬ CFSG.perfectResidual Y ≤ Subgroup.centralizer (B : Set Y))
    (V : Type) [CommGroup V] [Finite V] (hV2 : ∀ v : V, v * v = 1) (ρ : Y →* MulAut V)
    (hρ : ∃ y ∈ perfectResidual Y, ρ y ≠ 1) :
    4 ≤ Nat.card (Sec3.commHom (ρ t)).range := by
  have := hX
  have hk : Nat.card (GaloisField 2 2) = 4 := L34.card_galoisField_two_two
  let φ : L ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) :=
    (MulEquiv.subgroupCongr hLV).trans
      ((W₀.equivMapOfInjective X.subtype X.subtype_injective).symm.trans eV)
  let ψ : L ⧸ Subgroup.center L ≃* projectiveSL 3 (GaloisField 2 2) :=
    QuotientGroup.congr (Subgroup.center L) (scalars 3 (GaloisField 2 2)) φ
      ((Subgroup.map_center_eq φ).trans (scalars_eq_center 3 (GaloisField 2 2)).symm)
  have hL : commutator L = ⊤ := by
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
      CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
    have : Group.IsPerfect L :=
      Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hCLn : (Subgroup.centralizer (L : Set Y)).Normal := Subgroup.normal_centralizer
  have hUL : ∀ u ∈ U.map X.subtype, ∀ l ∈ L, u * l = l * u := by
    rintro _ ⟨u, hu, rfl⟩ l hl
    rw [hLV] at hl
    obtain ⟨v, hv, rfl⟩ := hl
    exact congrArg Subtype.val (hUV u hu v hv)
  have hU'C : U.map X.subtype ≤ Subgroup.centralizer (L : Set Y) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun l hl => (hUL u hu l hl).symm
  have hXC : X ⊓ Subgroup.centralizer (L : Set Y) ≤ U.map X.subtype := by
    rintro y ⟨hy, hc⟩
    have : (⟨y, hy⟩ : X) ∈ Subgroup.centralizer (W₀ : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      apply Subtype.ext
      refine Subgroup.mem_centralizer_iff.mp hc (v : Y) ?_
      rw [hLV]
      exact ⟨v, hv, rfl⟩
    rw [L34.centralizer_eq_of_isHeisSL hsup hUV ⟨eV⟩ h3] at this
    exact ⟨⟨y, hy⟩, this, rfl⟩
  have hdec : ∀ x ∈ X, ∃ l ∈ L, ∃ u ∈ U.map X.subtype, x = l * u := by
    intro x hx
    obtain ⟨u, hu, v, hv, huv⟩ := L34.exists_mul_eq_of_sup_eq_top hsup hUV ⟨x, hx⟩
    refine ⟨v, by rw [hLV]; exact ⟨v, hv, rfl⟩, u, ⟨u, hu, rfl⟩, ?_⟩
    have h1 : x = (u : Y) * (v : Y) := (congrArg Subtype.val huv).symm
    have h2 : (u : Y) * (v : Y) = (v : Y) * (u : Y) := congrArg Subtype.val (hUV u hu v hv)
    rw [h1, h2]
  have hXLC : ∀ x ∈ X, ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), x = l * c := by
    intro x hx
    obtain ⟨l, hl, u, hu, rfl⟩ := hdec x hx
    exact ⟨l, hl, u, hU'C hu, rfl⟩
  have hU'3 : IsPGroup 3 (U.map X.subtype) := hU.1.1.map X.subtype
  have hCX : IsPGroup 3 ↥(X ⊓ Subgroup.centralizer (L : Set Y)) := hU'3.to_le hXC
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hE.2 _ x.2)⟩
  have hres : CFSG.perfectResidual Y ≤ L := hLX ▸ perfectResidual_le_commutator hYt
  have hEC : Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Y)) ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := (hE3.to_le (inf_le_left :
      E ⊓ Subgroup.centralizer (L : Set Y) ≤ E)).exists_card_eq
    have hn2 : 2 ≤ n := by
      by_contra h
      interval_cases n <;> simp_all
    have hdvd : 3 ^ 2 ∣ Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Y)) :=
      hn ▸ pow_dvd_pow 3 hn2
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
    refine hB (K.map (E ⊓ Subgroup.centralizer (L : Set Y)).subtype)
      ((Subgroup.map_subtype_le K).trans inf_le_left) ?_ ?_
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
      norm_num
    · refine hres.trans ?_
      rw [Subgroup.le_centralizer_iff]
      exact (Subgroup.map_subtype_le K).trans inf_le_right
  have hU27 : Nat.card (U.map X.subtype) = 27 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact hU.2.1
  have hUL3 : Nat.card ↥(U.map X.subtype ⊓ L) = 3 := by
    rw [hLV, ← Subgroup.map_inf_eq _ _ _ X.subtype_injective,
      Subgroup.card_map_of_injective X.subtype_injective]
    exact h3
  have hEL : Nat.card ↥(E ⊓ L) ≤ 9 := by
    refine card_inf_le_nine hE ?_
    rw [CFSG.RankThree.Asc83Table.pRank_congr φ, L34.pRank_three_specialLinearGroup hk]
  have hW9 := nine_le_card_inf_sup hEL hE27 hUL3 (fun e he => hdec e (hEX he))
  have hcommU : ∀ a ∈ U.map X.subtype, ∀ b ∈ U.map X.subtype,
      ⁅a, b⁆ ∈ U.map X.subtype ⊓ L := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : ⁅a, b⁆ ∈ ⁅U, U⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [← Subgroup.map_subtype_commutator, hU.1.2.1,
      ← L34.inf_eq_map_center_left hUV hU h3] at h1
    rw [← map_commutatorElement, hLV, ← Subgroup.map_inf_eq _ _ _ X.subtype_injective]
    exact ⟨_, h1, rfl⟩
  have hKX : ∀ R : Subgroup Y, IsPGroup 2 R → R ≤ Subgroup.centralizer (L : Set Y) →
      R ≤ Subgroup.centralizer (E : Set Y) → R ≤ Subgroup.centralizer (X : Set Y) := by
    intro R hR hRL hRE r hr
    have hrEL : ∀ x ∈ E ⊔ L, r * x = x * r := by
      intro x hx
      have hle : E ⊔ L ≤ Subgroup.centralizer ({r} : Set Y) := by
        refine sup_le (fun e he => ?_) (fun l hl => ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp (hRE hr) e he)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp (hRL hr) l hl)
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm
    have hrU : ∀ u ∈ U.map X.subtype, r * u * r⁻¹ ∈ U.map X.subtype := fun u hu =>
      hXC ⟨hX.conj_mem u (Subgroup.map_subtype_le U hu) r, hCLn.conj_mem u (hU'C hu) r⟩
    have hrU' : ∀ u ∈ U.map X.subtype, r * u = u * r := by
      obtain ⟨m, hm⟩ := hR ⟨r, hr⟩
      have hm' : r ^ 2 ^ m = 1 := congrArg Subtype.val hm
      have hWU : U.map X.subtype ⊓ (E ⊔ L) ≤ U.map X.subtype := inf_le_left
      have hZW : U.map X.subtype ⊓ L ≤ U.map X.subtype ⊓ (E ⊔ L) :=
        inf_le_inf_left _ le_sup_right
      have hrW : ∀ x ∈ U.map X.subtype ⊓ (E ⊔ L), r * x = x * r := fun x hx => hrEL x hx.2
      have hdvd : Nat.card ↥(U.map X.subtype ⊓ (E ⊔ L)) ∣ 3 ^ 3 := by
        rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hU27]
        exact Subgroup.card_dvd_of_le hWU
      obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      interval_cases i
      · rw [hci] at hW9; norm_num at hW9
      · rw [hci] at hW9; norm_num at hW9
      · have hW9' : Nat.card ↥(U.map X.subtype ⊓ (E ⊔ L)) = 9 := by rw [hci]; norm_num
        have hlt : U.map X.subtype ⊓ L < U.map X.subtype ⊓ (E ⊔ L) := by
          refine lt_of_le_of_ne hZW fun h => ?_
          rw [← h, hUL3] at hW9'
          norm_num at hW9'
        obtain ⟨w, hwW, hwZ⟩ := IsConcreteLE.exists_of_lt hlt
        have hwnc : ∃ x ∈ U.map X.subtype, x * w ≠ w * x := by
          by_contra hcon
          push Not at hcon
          apply hwZ
          obtain ⟨w₀, hw₀, rfl⟩ := hWU hwW
          have hc : (⟨w₀, hw₀⟩ : U) ∈ Subgroup.center U := by
            rw [Subgroup.mem_center_iff]
            intro g
            apply Subtype.ext
            apply Subtype.ext
            exact hcon _ ⟨g, g.2, rfl⟩
          have : w₀ ∈ U ⊓ W₀ := by
            rw [L34.inf_eq_map_center_left hUV hU h3]
            exact ⟨_, hc, rfl⟩
          rw [hLV, ← Subgroup.map_inf_eq _ _ _ X.subtype_injective]
          exact ⟨w₀, this, rfl⟩
        intro u hu
        refine commute_of_heis hWU hwW ?_ ?_ ?_ hrU hrW hm' hu
        · intro a ha b hb
          exact ⟨hZW (hcommU a ha b hb), fun c hc => (hUL c hc _ (hcommU a ha b hb).2).symm⟩
        · exact fun x hx hxw => mem_of_commute_of_card hU27 hW9' hWU hwW hwnc hx hxw
        · intro x hx hx2
          obtain ⟨n, hn⟩ := hU'3 ⟨x, hWU hx⟩
          exact eq_one_of_pow_two_of_pow_three hx2 (congrArg Subtype.val hn)
      · have hWeq : U.map X.subtype ⊓ (E ⊔ L) = U.map X.subtype :=
          Subgroup.eq_of_le_of_card_ge hWU (by rw [hU27, hci]; norm_num)
        intro u hu
        exact hrW u (by rw [hWeq]; exact hu)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨l, hl, u, hu, rfl⟩ := hdec x hx
    have h1 : l * r = r * l := Subgroup.mem_centralizer_iff.mp (hRL hr) l hl
    have h2 : u * r = r * u := (hrU' u hu).symm
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  exact (core_bound hk hO hX hL ψ hXLC hCX hEC hKX htX hYt ht2 hEX hE3 hE27 hEt hres V hV2 ρ
    hρ).1

end Setups


theorem le_perfectResidual_of_commutator_eq {Y : Type*} [Group Y] {L : Subgroup Y}
    (h : ⁅L, L⁆ = L) : L ≤ perfectResidual Y := by
  have key : ∀ n : ℕ, L ≤ derivedSeries Y n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ, ← h]
      exact Subgroup.commutator_mono ih ih
  rw [CFSG.perfectResidual]
  exact le_iInf key

theorem ks181GraphFieldModule : KFacts.KS181GraphFieldModule := by
  intro Y _ _ X t E hO hXn hXiso htX hYt ht2 hEX hE hE27 hEt hB V _ _ hV2 ρ hρ
  have := hXn
  have hk : Nat.card (GaloisField 2 2) = 4 := L34.card_galoisField_two_two
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hE.2 _ x.2)⟩
  have hres : perfectResidual Y ≤ ⁅X, X⁆ := KS18.perfectResidual_le_commutator hYt
  rcases hXiso with he | hXH
  · obtain ⟨e₀⟩ := he
    set e := e₀.trans (MulEquiv.prodCongr (MulEquiv.refl _)
      (L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))) with hedef
    have h := bound_Z3_of hk hO e hXn (KS18.commutator_eq_range e) htX hYt ht2 hEX hE3 hE27
      hEt hres V hV2 ρ hρ
    exact ⟨h.1, fun _ => h.2⟩
  · obtain ⟨U, W₀, hsup, hUV, hU, ⟨eV⟩, h3⟩ := hXH
    have hLV : ⁅X, X⁆ = W₀.map X.subtype := by
      rw [← Subgroup.map_subtype_commutator, KS18.commutator_eq_of_isHeisSL hsup hUV hU ⟨eV⟩ h3]
    refine ⟨bound_heis_of hO hXn hsup hUV hU eV h3 hLV rfl htX hYt ht2 hEX hE hE27 hEt hB V hV2
      ρ hρ, ?_⟩
    rintro ⟨e⟩
    exfalso
    have hW₀ : ⁅W₀, W₀⁆ = W₀ := by
      have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
        CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
      have : Group.IsPerfect W₀ :=
        Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective
      rw [← Subgroup.map_subtype_commutator, Group.IsPerfect.commutator_eq_top,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hLL : ⁅⁅X, X⁆, ⁅X, X⁆⁆ = ⁅X, X⁆ := by
      rw [hLV, ← Subgroup.map_commutator, hW₀]
    have heq : perfectResidual Y = ⁅X, X⁆ :=
      le_antisymm hres (le_perfectResidual_of_commutator_eq hLL)
    have hc1 : Nat.card (perfectResidual Y) = 60480 := by
      rw [heq, hLV, Subgroup.card_map_of_injective X.subtype_injective,
        Nat.card_congr eV.toEquiv, L34.card_specialLinearGroup hk]
    have hc2 := Nat.card_congr e.toEquiv
    rw [hc1, L34.card_projSL] at hc2
    norm_num at hc2

end CFSG.RankThree.PartTwo.Sec18.Item181ThreeProof
