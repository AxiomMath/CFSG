module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Field
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Hyper
public import CFSG.RankThree.PartTwo.Sec4.Item413AutL3

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res6L364

open CFSG CFSG.LieType.Seitz CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

abbrev Y64 : Type := projectiveSL 3 K64

theorem three_ne_zero' : (3 : K64) ≠ 0 := by
  have : (3 : K64) = 1 := by
    rw [show (3 : K64) = 2 + 1 by norm_num, two_eq_zero, zero_add]
  rw [this]; exact one_ne_zero

theorem card_le_three_mul_inf {E : Subgroup (MulAut Y64)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    Nat.card E ≤ 3 * Nat.card (E ⊓ linearAutGroup 3 K64 : Subgroup _) := by
  obtain ⟨p, -, f, hp, hK⟩ := FiniteField.card' K64
  have hcycK := (card_ringAut_and_isCyclic hp K64 (by rw [Nat.card_eq_fintype_card, hK])).2
  have hcyc : IsCyclic (fieldAut 3 K64).range :=
    isCyclic_of_surjective (fieldAut 3 K64).rangeRestrict (fieldAut 3 K64).rangeRestrict_surjective
  have hCN : (fieldAut 3 K64).range ≤
      Subgroup.normalizer
        ((linearAutGroup 3 K64 : Subgroup _) : Set (MulAut Y64)) := by
    rintro _ ⟨σ, rfl⟩
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    rw [linearAutGroup_three_eq_range] at hx ⊢
    obtain ⟨A, rfl⟩ := hx
    refine ⟨Matrix.GeneralLinearGroup.map (σ : K64 →+* K64) A, ?_⟩
    rw [fieldAut_mul_conjAut, mul_inv_cancel_right]
  have hBNC : ∀ b ∈ E, ∃ n ∈ linearAutGroup 3 K64, ∃ c ∈ (fieldAut 3 K64).range, b = n * c := by
    intro b hb
    by_cases hbN : b ∈ linearAutGroup 3 K64
    · exact ⟨b, hbN, 1, one_mem _, (mul_one b).symm⟩
    · obtain ⟨σ, -, H, hH⟩ :=
        KFacts.linear_order_three_field_descent (by norm_num) b (hE.2 b hb) hbN
      refine ⟨conjAut 3 K64 H * conjAut 3 K64 (Matrix.GeneralLinearGroup.map (σ : K64 →+* K64) H⁻¹),
        ?_, fieldAut 3 K64 σ, ⟨σ, rfl⟩, ?_⟩
      · rw [linearAutGroup_three_eq_range]
        exact ⟨_, map_mul _ _ _⟩
      · rw [hH, ← map_inv, mul_assoc, fieldAut_mul_conjAut, ← mul_assoc]
  exact card_le_three_mul_card_inf hE hcyc hCN hBNC

theorem card_inf_linearAutGroup_eq_nine {E : Subgroup (MulAut Y64)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h27 : Nat.card E = 27) :
    Nat.card (E ⊓ linearAutGroup 3 K64 : Subgroup _) = 9 := by
  have h1 := card_le_three_mul_inf hE
  have h2 : Nat.card (E ⊓ linearAutGroup 3 K64 : Subgroup (MulAut Y64)) ≤ 9 :=
    card_inf_linearAutGroup_three_le three_ne_zero' hE
  rw [h27] at h1
  omega

theorem exists_not_mem_linearAutGroup {E : Subgroup (MulAut Y64)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h27 : Nat.card E = 27) :
    ∃ e ∈ E, e ∉ linearAutGroup 3 K64 := by
  by_contra h
  push Not at h
  have hle : E ≤ E ⊓ linearAutGroup 3 K64 := fun e he => ⟨he, h e he⟩
  have := Subgroup.card_le_of_le hle
  rw [card_inf_linearAutGroup_eq_nine hE h27, h27] at this
  omega

theorem fieldAut_σ4_inv : (fieldAut 3 K64 σ4)⁻¹ = fieldAut 3 K64 (σ4 * σ4) := by
  rw [← map_inv]
  congr 1
  rw [inv_eq_iff_mul_eq_one, ← pow_three, σ4_cube]

theorem exists_conj_fieldAut_mem {E : Subgroup (MulAut Y64)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h27 : Nat.card E = 27) :
    ∃ H : GL (Fin 3) K64, conjAut 3 K64 H * fieldAut 3 K64 σ4 * (conjAut 3 K64 H)⁻¹ ∈ E := by
  obtain ⟨e, he, heD⟩ := exists_not_mem_linearAutGroup hE h27
  obtain ⟨τ, hτ, H, rfl⟩ :=
    KFacts.linear_order_three_field_descent (by norm_num) e (hE.2 e he) heD
  refine ⟨H, ?_⟩
  rcases eq_σ4_or_sq hτ with rfl | rfl
  · exact he
  · have hinv := inv_mem he
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← mul_assoc] at hinv
    have h1 : (fieldAut 3 K64 (σ4 * σ4))⁻¹ = fieldAut 3 K64 σ4 := by
      rw [← fieldAut_σ4_inv, inv_inv]
    rw [h1] at hinv
    exact hinv

theorem seitzHyperGamma_eq_top_of_field
    (main : ∀ E : Subgroup (MulAut Y64), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      fieldAut 3 K64 σ4 ∈ E → seitzHyperGamma 3 E = ⊤)
    {E : Subgroup (MulAut Y64)} (hE : CFSG.Assembly.IsElemAbelian 3 E) (h27 : Nat.card E = 27) :
    seitzHyperGamma 3 E = ⊤ := by
  obtain ⟨H, hH⟩ := exists_conj_fieldAut_mem hE h27
  set ψ : MulAut Y64 := (conjAut 3 K64 H)⁻¹ with hψ
  set φ : MulAut Y64 →* MulAut Y64 := (MulAut.conj ψ).toMonoidHom with hφ
  have hφi : Function.Injective φ := (MulAut.conj ψ).injective
  refine seitzHyperGamma_eq_top_of_map ψ φ (fun a x => ?_) hφi (main (E.map φ) ?_ ?_ ?_)
  · simp [hφ, MulAut.conj_apply]
  · refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
      obtain ⟨_, ⟨b, hb, rfl⟩⟩ := y
      have := congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      simp only [Subgroup.coe_mul] at this ⊢
      rw [← map_mul, ← map_mul, this]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hE.2 a ha, map_one]
  · rw [Subgroup.card_map_of_injective hφi, h27]
  · refine ⟨_, hH, ?_⟩
    simp [hφ, hψ, mul_assoc]

theorem exists_scalar_of_conjAut_eq {A B : GL (Fin 3) K64}
    (h : conjAut 3 K64 A = conjAut 3 K64 B) :
    ∃ u : K64ˣ, A = Matrix.GeneralLinearGroup.scalar (Fin 3) u * B := by
  have hk : A * B⁻¹ ∈ (conjAut 3 K64).ker := by
    rw [MonoidHom.mem_ker, map_mul, h, map_inv, mul_inv_cancel]
  rw [ker_conjAut_three] at hk
  obtain ⟨u, hu⟩ := hk
  exact ⟨u, by rw [hu, inv_mul_cancel_right]⟩

noncomputable abbrev mapσ : GL (Fin 3) K64 →* GL (Fin 3) K64 :=
  Matrix.GeneralLinearGroup.map (σ4 : K64 →+* K64)

theorem mapσ_scalar (u : K64ˣ) :
    mapσ (Matrix.GeneralLinearGroup.scalar (Fin 3) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (σ4 : K64 →* K64) u) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem exists_σ_fixed_lift {E : Subgroup (MulAut Y64)} (hEc : IsMulCommutative E)
    (hf : fieldAut 3 K64 σ4 ∈ E) {a : MulAut Y64} (ha : a ∈ E ⊓ linearAutGroup 3 K64) :
    ∃ A : GL (Fin 3) K64, mapσ A = A ∧ a = conjAut 3 K64 A := by
  have ha2 := ha.2
  rw [linearAutGroup_three_eq_range] at ha2
  obtain ⟨A₀, rfl⟩ := ha2
  have hcomm : fieldAut 3 K64 σ4 * conjAut 3 K64 A₀ = conjAut 3 K64 A₀ * fieldAut 3 K64 σ4 :=
    congrArg Subtype.val (hEc.is_comm.comm ⟨_, hf⟩ ⟨_, ha.1⟩)
  rw [fieldAut_mul_conjAut] at hcomm
  have hc : conjAut 3 K64 (mapσ A₀) = conjAut 3 K64 A₀ := mul_right_cancel hcomm
  obtain ⟨l, hl⟩ := exists_scalar_of_conjAut_eq hc
  have hmat : ((mapσ A₀ : GL (Fin 3) K64) : Matrix (Fin 3) (Fin 3) K64) =
      (l : K64) • (A₀ : Matrix (Fin 3) (Fin 3) K64) := by
    rw [hl]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_eq_diagonal_mul]
  have hmap : ∀ M : Matrix (Fin 3) (Fin 3) K64, (M.map σ4).map σ4 = M.map (σ4 * σ4) := by
    intro M; ext i j; rfl
  have h3 : (((A₀ : Matrix (Fin 3) (Fin 3) K64).map σ4).map σ4).map σ4 =
      (A₀ : Matrix (Fin 3) (Fin 3) K64) := by
    ext i j
    simp only [Matrix.map_apply]
    have := congrArg (fun τ : K64 ≃+* K64 => τ ((A₀ : Matrix (Fin 3) (Fin 3) K64) i j)) σ4_cube
    simpa [pow_three, RingAut.mul_apply] using this
  have hA₀ : ((A₀ : GL (Fin 3) K64) : Matrix (Fin 3) (Fin 3) K64).map σ4 =
      (l : K64) • (A₀ : Matrix (Fin 3) (Fin 3) K64) := hmat
  have h21 : (l : K64) ^ 21 = 1 := by
    have e1 : (((A₀ : Matrix (Fin 3) (Fin 3) K64).map σ4).map σ4).map σ4 =
        ((l : K64) * σ4 l * σ4 (σ4 l)) • (A₀ : Matrix (Fin 3) (Fin 3) K64) := by
      have hs : ∀ (c : K64) (M : Matrix (Fin 3) (Fin 3) K64), (c • M).map σ4 = σ4 c • M.map σ4 :=
        fun c M => by ext i j; simp
      rw [hA₀, hs, hA₀, smul_smul, hs, hA₀, smul_smul, map_mul]
      congr 1; ring
    rw [h3] at e1
    have hA0ne : (A₀ : Matrix (Fin 3) (Fin 3) K64) ≠ 0 := by
      intro h0
      have hu : IsUnit (A₀ : Matrix (Fin 3) (Fin 3) K64).det := Matrix.isUnits_det_units A₀
      rw [h0, Matrix.det_zero] at hu
      exact not_isUnit_zero hu
    obtain ⟨i, j, hij⟩ : ∃ i j, (A₀ : Matrix (Fin 3) (Fin 3) K64) i j ≠ 0 := by
      by_contra hall; push Not at hall
      exact hA0ne (Matrix.ext hall)
    have e2 := congrFun (congrFun e1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e2
    have e3 : (l : K64) * σ4 l * σ4 (σ4 l) = 1 := by
      have := mul_right_cancel₀ hij (e2.symm.trans (one_mul _).symm)
      exact this
    rw [σ4_apply, σ4_apply, ← pow_mul] at e3
    linear_combination e3
  have hl21 : ((l : K64)⁻¹) ^ 21 = 1 := by rw [inv_pow, h21, inv_one]
  obtain ⟨μ, hμ⟩ := exists_cube_root hl21
  have hμ0 : μ ≠ 0 := by
    intro h; rw [h] at hμ; simp at hμ; exact (Units.ne_zero l) hμ.symm
  set m : K64ˣ := Units.mk0 μ hμ0 with hm
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) m * A₀, ?_, ?_⟩
  · rw [map_mul, mapσ_scalar, hl, ← mul_assoc, ← map_mul]
    congr 2
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, hm, Units.val_mk0]
    change σ4 μ * (l : K64) = μ
    rw [σ4_apply, show μ ^ 4 = μ ^ 3 * μ by ring, hμ]
    field_simp
  · rw [map_mul, conjAut_scalar, one_mul]

end CFSG.RankThree.PartTwo.Sec4.Res6L364
