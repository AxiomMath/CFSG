module

public import CFSG.RankThree.PartTwo.Sec8.Groups
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.RankThree.PartTwo.KFacts.K71OddChar
import CFSG.RankThree.PartTwo.KFacts.K71OddCharArith
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofL3
import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofOrders
import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofTransport
import CFSG.Timmesfeld.Orders.ExceptionalTwisted
import CFSG.RankThree.SteinbergR3ELargeReeOrder
import CFSG.RankThree.PartTwo.Census.Suzuki
import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCross
import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3AutLin
public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd
public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck159

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage projSU projSL)

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec17.Proof17Res7 (cSL linearModelEquiv coe_linearModelEquiv_proj
  toGL_cSL)


private theorem isPGroup_three_zpowers {Γ : Type*} [Group Γ] {g : Γ} (hg : g ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers g) := fun h => by
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h.2
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hm, ← _root_.zpow_natCast,
    ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, _root_.zpow_natCast, hg, one_zpow]

private theorem zpowers_le_normalizer_zpowers {Γ : Type*} [Group Γ] {a b : Γ}
    (h : Commute a b) :
    Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set Γ) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact (h.symm.zpow_left m).eq

private theorem isPGroup_closure_pair {Γ : Type*} [Group Γ] {x y : Γ} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) (h₁₂ : Commute x (y * x * y⁻¹)) (h₁₃ : Commute x (y⁻¹ * x * y))
    (h₂₃ : Commute (y * x * y⁻¹) (y⁻¹ * x * y)) :
    IsPGroup 3 (Subgroup.closure {x, y} : Subgroup Γ) := by
  set x₂ : Γ := y * x * y⁻¹ with hx₂
  set x₃ : Γ := y⁻¹ * x * y with hx₃
  have hx₂3 : x₂ ^ 3 = 1 := by rw [hx₂, conj_pow, hx, mul_one, mul_inv_cancel]
  have hx₃3 : x₃ ^ 3 = 1 := by
    rw [hx₃, show y⁻¹ * x * y = y⁻¹ * x * y⁻¹⁻¹ by rw [inv_inv], conj_pow, hx, mul_one,
      mul_inv_cancel]
  set E : Subgroup Γ := Subgroup.zpowers x ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ with hE
  have hE3 : IsPGroup 3 E := by
    have h12 : IsPGroup 3 (Subgroup.zpowers x ⊔ Subgroup.zpowers x₂ : Subgroup Γ) :=
      (isPGroup_three_zpowers hx).to_sup_of_normal_right' (isPGroup_three_zpowers hx₂3)
        (zpowers_le_normalizer_zpowers h₁₂)
    exact h12.to_sup_of_normal_right' (isPGroup_three_zpowers hx₃3)
      (sup_le (zpowers_le_normalizer_zpowers h₁₃) (zpowers_le_normalizer_zpowers h₂₃))
  have hy' : y * y * y = 1 := by rw [← pow_three']; exact hy
  have hy2 : y⁻¹ = y * y := by
    rw [inv_eq_iff_mul_eq_one]
    simpa [mul_assoc] using hy'
  have hxE : x ∈ E := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hx₂E : x₂ ∈ E := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂))
  have hx₃E : x₃ ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers x₃)
  have hmap : ∀ g ∈ E, y * g * y⁻¹ ∈ E := by
    intro g hg
    have hle : E ≤ E.comap (MulAut.conj y).toMonoidHom := by
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [Subgroup.zpowers_le]
        show y * x * y⁻¹ ∈ E
        exact hx₂E
      · rw [Subgroup.zpowers_le]
        show y * x₂ * y⁻¹ ∈ E
        have : y * x₂ * y⁻¹ = x₃ := by
          rw [hx₂, hx₃, show y * (y * x * y⁻¹) * y⁻¹ = (y * y) * x * (y * y)⁻¹ by group, ← hy2,
            inv_inv]
        rw [this]
        exact hx₃E
      · rw [Subgroup.zpowers_le]
        show y * x₃ * y⁻¹ ∈ E
        have : y * x₃ * y⁻¹ = x := by
          rw [hx₃]
          group
        rw [this]
        exact hxE
    exact hle hg
  have hyN : y ∈ Subgroup.normalizer (E : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hmap g, fun hg => ?_⟩
    have h2 := hmap _ (hmap _ hg)
    have e : y * (y * (y * g * y⁻¹) * y⁻¹) * y⁻¹ = g := by
      calc y * (y * (y * g * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * g * (y * y * y)⁻¹ := by group
        _ = g := by rw [hy']; group
    rwa [e] at h2
  have hM : IsPGroup 3 (Subgroup.zpowers y ⊔ E : Subgroup Γ) :=
    (isPGroup_three_zpowers hy).to_sup_of_normal_right' hE3 (Subgroup.zpowers_le.mpr hyN)
  refine hM.to_le ((Subgroup.closure_le _).mpr ?_)
  intro g hg
  rcases hg with rfl | rfl
  · exact Subgroup.mem_sup_right hxE
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

theorem exists_isPGroup_pair_map {A B : Type*} [Group A] [Group B] (ι : A →* B)
    (hι : Function.Injective ι) {T : Subgroup A}
    (h : ∃ Q : Subgroup A, Q ≤ T ∧ IsPGroup 3 Q ∧ ∃ x ∈ Q, ∃ y ∈ Q, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧
      x * y ≠ y * x) :
    ∃ Q : Subgroup B, Q ≤ T.map ι ∧ IsPGroup 3 Q ∧ ∃ x ∈ Q, ∃ y ∈ Q, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧
      x * y ≠ y * x := by
  obtain ⟨Q, hQT, hQ, x, hx, y, hy, hx3, hy3, hxy⟩ := h
  refine ⟨Q.map ι, Subgroup.map_mono hQT, hQ.map ι, ι x, Subgroup.mem_map_of_mem ι hx, ι y,
    Subgroup.mem_map_of_mem ι hy, ?_, ?_, ?_⟩
  · rw [← map_pow, hx3, map_one]
  · rw [← map_pow, hy3, map_one]
  · intro hc
    apply hxy
    apply hι
    rw [map_mul, map_mul, hc]

section PGL

variable {K : Type} [Field K]

private theorem diagUnits_inv_one (τ : Kˣ) :
    (diagUnits τ 1 1 : GL (Fin 3) K)⁻¹ = diagUnits τ⁻¹ 1 1 := by
  have h : (diagHom (K := K) (τ, 1, 1))⁻¹ = diagHom (K := K) (τ, 1, 1)⁻¹ := (map_inv _ _).symm
  rw [Prod.inv_mk, Prod.inv_mk, inv_one] at h
  exact h

private theorem heis_projGL (τ : Kˣ) (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    (Matrix.ProjGenLinGroup.mk (diagUnits τ 1 1 : GL (Fin 3) K)) ^ 3 = 1 ∧
    (Matrix.ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)) ^ 3 = 1 ∧
    Matrix.ProjGenLinGroup.mk (diagUnits τ 1 1 : GL (Fin 3) K) *
        Matrix.ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) ≠
      Matrix.ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) *
        Matrix.ProjGenLinGroup.mk (diagUnits τ 1 1 : GL (Fin 3) K) := by
  set D : GL (Fin 3) K := diagUnits τ 1 1 with hD
  set C : GL (Fin 3) K := cycThree with hC
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_pow]
    have : D ^ 3 = 1 := by
      have h := congrArg (diagHom (K := K)) (show ((τ, 1, 1) : Kˣ × Kˣ × Kˣ) ^ 3 = 1 by
        rw [Prod.pow_mk, Prod.pow_mk, hτ3, one_pow]; rfl)
      rwa [map_pow, map_one] at h
    rw [this, map_one]
  · rw [← map_pow, hC, cycThree_pow_three, map_one]
  · intro h
    have h1 : Matrix.ProjGenLinGroup.mk (D * C * D⁻¹ * C⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
      group
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    obtain ⟨u, hu⟩ := h1
    have h2 : D * C * D⁻¹ * C⁻¹ = diagUnits τ τ⁻¹ 1 := by
      rw [hD, diagUnits_inv_one, mul_assoc, mul_assoc,
        show C * (diagUnits τ⁻¹ 1 1 * C⁻¹) = diagUnits 1 τ⁻¹ 1 by
          rw [← mul_assoc, hC, cycThree_conj_diagUnits], diagUnits_mul]
      simp
    rw [h2] at hu
    have e0 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hu
    have e2 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 2 2) hu
    simp only [coe_diagUnits, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at e0 e2
    simp at e0 e2
    exact hτ1 ((Units.ext e0).symm.trans e2)

private theorem commute_mk_diagUnits (a b c a' b' c' : Kˣ) :
    Commute (Matrix.ProjGenLinGroup.mk (diagUnits a b c : GL (Fin 3) K))
      (Matrix.ProjGenLinGroup.mk (diagUnits a' b' c' : GL (Fin 3) K)) := by
  show _ * _ = _ * _
  rw [← map_mul, ← map_mul, diagUnits_mul, diagUnits_mul, mul_comm a a', mul_comm b b',
    mul_comm c c']

private theorem isPGroup_closure_heis_projGL (τ : Kˣ) (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    IsPGroup 3 (Subgroup.closure {Matrix.ProjGenLinGroup.mk (diagUnits τ 1 1 : GL (Fin 3) K),
      Matrix.ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)} :
        Subgroup (Matrix.ProjGenLinGroup (Fin 3) K)) := by
  obtain ⟨hx, hy, -⟩ := heis_projGL (K := K) τ hτ3 hτ1
  have h2 : Matrix.ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) *
      Matrix.ProjGenLinGroup.mk (diagUnits τ 1 1 : GL (Fin 3) K) *
        (Matrix.ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))⁻¹ =
      Matrix.ProjGenLinGroup.mk (diagUnits 1 τ 1 : GL (Fin 3) K) := by
    rw [← map_inv, ← map_mul, ← map_mul, cycThree_conj_diagUnits]
  have h3 : (Matrix.ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))⁻¹ *
      Matrix.ProjGenLinGroup.mk (diagUnits τ 1 1 : GL (Fin 3) K) *
        Matrix.ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) =
      Matrix.ProjGenLinGroup.mk (diagUnits 1 1 τ : GL (Fin 3) K) := by
    rw [← map_inv, ← map_mul, ← map_mul, cycThree_inv_conj_diagUnits]
  refine isPGroup_closure_pair hx hy ?_ ?_ ?_
  · rw [h2]
    exact commute_mk_diagUnits _ _ _ _ _ _
  · rw [h3]
    exact commute_mk_diagUnits _ _ _ _ _ _
  · rw [h2, h3]
    exact commute_mk_diagUnits _ _ _ _ _ _

end PGL

section Linear

variable {F : Type} [Field F]

private theorem scalar_eq_diagUnits (u : Fˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) F) = diagUnits u u u := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagUnits]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem mk_diagUnits_scale (μ τ : Fˣ) :
    Matrix.ProjGenLinGroup.mk (diagUnits (μ⁻¹ * τ) μ⁻¹ μ⁻¹ : GL (Fin 3) F) =
      Matrix.ProjGenLinGroup.mk (diagUnits τ 1 1 : GL (Fin 3) F) := by
  have h : (diagUnits (μ⁻¹ * τ) μ⁻¹ μ⁻¹ : GL (Fin 3) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * diagUnits τ 1 1 := by
    rw [scalar_eq_diagUnits, diagUnits_mul, mul_one]
  rw [h, map_mul]
  have : Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.scalar (Fin 3) μ⁻¹ : GL (Fin 3) F) = 1 := by
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨μ⁻¹, rfl⟩
  rw [this, one_mul]

private noncomputable def dLam (lam τ : Fˣ) (h : lam ^ 3 = τ) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨((diagUnits (lam⁻¹ * τ) lam⁻¹ lam⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), by
    rw [coe_diagUnits, Matrix.det_diagonal, Fin.prod_univ_three]
    have h1 : (lam⁻¹ * τ) * lam⁻¹ * lam⁻¹ = (1 : Fˣ) := by rw [← h]; group
    have h2 := congrArg Units.val h1
    simpa using h2⟩

private theorem toGL_dLam (lam τ : Fˣ) (h : lam ^ 3 = τ) :
    Matrix.SpecialLinearGroup.toGL (dLam lam τ h) =
      (diagUnits (lam⁻¹ * τ) lam⁻¹ lam⁻¹ : GL (Fin 3) F) :=
  Units.ext rfl

private theorem toGL_map_dLam {σ : F ≃+* F} (lam τ : Fˣ) (h : lam ^ 3 = τ)
    (hστ : σ (τ : F) = τ) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map σ.toRingHom (dLam lam τ h)) =
      (diagUnits ((Units.map (σ : F →* F) lam)⁻¹ * τ) (Units.map (σ : F →* F) lam)⁻¹
        (Units.map (σ : F →* F) lam)⁻¹ : GL (Fin 3) F) := by
  apply Units.ext
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dLam, coe_diagUnits, hστ]

private theorem fieldAut_proj_dLam {σ : F ≃+* F} (lam τ : Fˣ) (h : lam ^ 3 = τ)
    (hστ : σ (τ : F) = τ) :
    fieldAut 3 F σ (proj 3 F (dLam lam τ h)) = proj 3 F (dLam lam τ h) := by
  rw [fieldAut_proj]
  apply (linearModelEquiv (K := F) 2).injective
  apply Subtype.ext
  rw [coe_linearModelEquiv_proj, coe_linearModelEquiv_proj, toGL_map_dLam lam τ h hστ, toGL_dLam,
    mk_diagUnits_scale, mk_diagUnits_scale]

private theorem fieldAut_proj_cSL (σ : F ≃+* F) :
    fieldAut 3 F σ (proj 3 F (cSL : Matrix.SpecialLinearGroup (Fin 3) F)) =
      proj 3 F (cSL : Matrix.SpecialLinearGroup (Fin 3) F) := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cSL, coe_cycThree]

private theorem exists_orderOf_nine [Finite F] (h9 : 9 ∣ Nat.card Fˣ) :
    ∃ lam : Fˣ, orderOf lam = 9 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  refine ⟨g ^ (Nat.card Fˣ / 9), ?_⟩
  have h0 : orderOf g ≠ 0 := by rw [hord]; exact Nat.card_pos.ne'
  have := orderOf_pow_orderOf_div h0 (n := 9) (by rwa [hord])
  rwa [hord] at this

private theorem apply_eq_of_pow_three_eq_one {σ : F ≃+* F} (hσ : σ ^ 3 = 1) {τ : F}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) : σ τ = τ := by
  have h0 : τ ^ 2 + τ + 1 = 0 := by
    have h : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hτ1)
  have ha : (σ τ) ^ 2 + σ τ + 1 = 0 := by
    have := congrArg σ h0
    simpa [map_add, map_pow] using this
  have h : (σ τ - τ) * (σ τ - τ ^ 2) = 0 := by linear_combination ha - σ τ * h0 + hτ
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have h2 : σ τ = τ ^ 2 := sub_eq_zero.mp h
    have h3 : σ (σ τ) = τ := by
      rw [h2, map_pow, h2, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hτ, one_mul,
        pow_one]
    have h4 : σ (σ (σ τ)) = τ := by
      have := congrArg (fun f : F ≃+* F => f τ) hσ
      simpa [pow_succ, RingAut.mul_apply] using this
    rw [h3, h2] at h4
    apply hτ1
    have hτ0 : τ ≠ 0 := by
      rintro rfl
      simp at hτ
    have : τ * (τ - 1) = 0 := by linear_combination h4
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hτ0)

private theorem exists_pair_fixed_fieldAut [Finite F] {σ : F ≃+* F} (hσ : orderOf σ = 3)
    (h9 : 9 ∣ Nat.card Fˣ) :
    ∃ Q : Subgroup (projectiveSL 3 F),
      Q ≤ (fieldAut 3 F σ).toMonoidHom.eqLocus (MonoidHom.id _) ∧ IsPGroup 3 Q ∧
        ∃ x ∈ Q, ∃ y ∈ Q, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  obtain ⟨lam, hlam⟩ := exists_orderOf_nine h9
  set τ : Fˣ := lam ^ 3 with hτ
  have hl9 : lam ^ 9 = 1 := by rw [← hlam]; exact pow_orderOf_eq_one lam
  have hτ3 : τ ^ 3 = 1 := by rw [hτ, ← pow_mul]; exact hl9
  have hτ1 : τ ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have hτF3 : ((τ : Fˣ) : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hτ3, Units.val_one]
  have hτF1 : ((τ : Fˣ) : F) ≠ 1 := fun he => hτ1 (Units.ext (by simpa using he))
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hστ := apply_eq_of_pow_three_eq_one hσ3 hτF3 hτF1
  set x : projectiveSL 3 F := proj 3 F (dLam lam τ rfl) with hx
  set y : projectiveSL 3 F := proj 3 F (cSL : Matrix.SpecialLinearGroup (Fin 3) F) with hy
  let φ : projectiveSL 3 F →* Matrix.ProjGenLinGroup (Fin 3) F :=
    (projImage (slPi true 3 2 F)).subtype.comp (linearModelEquiv (K := F) 2).toMonoidHom
  have hφinj : Function.Injective φ :=
    Subtype.val_injective.comp (linearModelEquiv (K := F) 2).injective
  have hφx : φ x = Matrix.ProjGenLinGroup.mk (diagUnits τ 1 1 : GL (Fin 3) F) := by
    show ((linearModelEquiv (K := F) 2 (proj 3 F (dLam lam τ rfl)) :
      projImage (slPi true 3 2 F)) : Matrix.ProjGenLinGroup (Fin 3) F) = _
    rw [coe_linearModelEquiv_proj, toGL_dLam, mk_diagUnits_scale]
  have hφy : φ y = Matrix.ProjGenLinGroup.mk (cycThree : GL (Fin 3) F) := by
    show ((linearModelEquiv (K := F) 2
      (proj 3 F (cSL : Matrix.SpecialLinearGroup (Fin 3) F)) :
        projImage (slPi true 3 2 F)) : Matrix.ProjGenLinGroup (Fin 3) F) = _
    rw [coe_linearModelEquiv_proj, toGL_cSL]
  obtain ⟨hx3, hy3, hxy⟩ := heis_projGL τ hτ3 hτ1
  have hQ0 := isPGroup_closure_heis_projGL (K := F) τ hτ3 hτ1
  set X0 : Matrix.ProjGenLinGroup (Fin 3) F :=
    Matrix.ProjGenLinGroup.mk (diagUnits τ 1 1 : GL (Fin 3) F) with hX0
  set Y0 : Matrix.ProjGenLinGroup (Fin 3) F :=
    Matrix.ProjGenLinGroup.mk (cycThree : GL (Fin 3) F) with hY0
  have hQ' : IsPGroup 3 ((Subgroup.closure {X0, Y0}).comap φ) :=
    hQ0.comap_of_injective φ hφinj
  have hxE : x ∈ (fieldAut 3 F σ).toMonoidHom.eqLocus (MonoidHom.id _) :=
    fieldAut_proj_dLam lam τ rfl hστ
  have hyE : y ∈ (fieldAut 3 F σ).toMonoidHom.eqLocus (MonoidHom.id _) :=
    fieldAut_proj_cSL σ
  have hxQ : x ∈ (Subgroup.closure {X0, Y0}).comap φ := by
    rw [Subgroup.mem_comap, hφx]
    exact Subgroup.subset_closure (Or.inl rfl)
  have hyQ : y ∈ (Subgroup.closure {X0, Y0}).comap φ := by
    rw [Subgroup.mem_comap, hφy]
    exact Subgroup.subset_closure (Or.inr rfl)
  refine ⟨Subgroup.closure {x, y}, (Subgroup.closure_le _).mpr
    (Set.insert_subset_iff.mpr ⟨hxE, Set.singleton_subset_iff.mpr hyE⟩),
    hQ'.to_le ((Subgroup.closure_le _).mpr (Set.insert_subset_iff.mpr
      ⟨hxQ, Set.singleton_subset_iff.mpr hyQ⟩)),
    x, Subgroup.subset_closure (Or.inl rfl), y, Subgroup.subset_closure (Or.inr rfl), ?_, ?_, ?_⟩
  · apply hφinj
    rw [map_pow, hφx, hx3, map_one]
  · apply hφinj
    rw [map_pow, hφy, hy3, map_one]
  · intro hc
    have := congrArg φ hc
    rw [map_mul, map_mul, hφx, hφy] at this
    exact hxy this

end Linear

private theorem exists_pair_projImage_glPi_false {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : ModThree false (p ^ f)) :
    ∃ Q : Subgroup (projImage (glPi false 3 (p ^ f) K)), Q ≤ ⊤ ∧ IsPGroup 3 Q ∧
      ∃ x ∈ Q, ∃ y ∈ Q, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  have hK : PiField false p f K := ⟨h.prime, h.one_le, by
    rw [h.card, piCard, cond, ← pow_mul, mul_comm]⟩
  obtain ⟨τ, hτ3, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ3
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hτu3 : τu ^ 3 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ3, Units.val_one])
  have hτu1 : τu ≠ 1 := fun he => hτ1 (by rw [← Units.val_mk0 hτ0, ← hτu, he, Units.val_one])
  have hτr : τu ∈ rootsOfUnity 3 K := (mem_rootsOfUnity _ _).mpr hτu3
  have hD : (diagUnits τu 1 1 : GL (Fin 3) K) ∈ glPi false 3 (p ^ f) K :=
    diagUnits_mem_glPi hK (cube_root_mem_qSubPi hq hτr) (one_mem _) (one_mem _)
  have hπ : false = false → UnitaryFieldData p f K := fun _ => h
  have hC : (cycThree : GL (Fin 3) K) ∈ glPi false 3 (p ^ f) K :=
    slPi_le_glPi hπ (cycThree_mem_slPi hπ)
  obtain ⟨hx3, hy3, hxy⟩ := heis_projGL (K := K) τu hτu3 hτu1
  have hQ0 := isPGroup_closure_heis_projGL (K := K) τu hτu3 hτu1
  set P := projImage (glPi false 3 (p ^ f) K) with hP
  let x : P := ⟨Matrix.ProjGenLinGroup.mk (diagUnits τu 1 1 : GL (Fin 3) K), ⟨_, hD, rfl⟩⟩
  let y : P := ⟨Matrix.ProjGenLinGroup.mk (cycThree : GL (Fin 3) K), ⟨_, hC, rfl⟩⟩
  refine ⟨(Subgroup.closure {Matrix.ProjGenLinGroup.mk (diagUnits τu 1 1 : GL (Fin 3) K),
    Matrix.ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)}).subgroupOf P, le_top,
    hQ0.comap_subtype, x, ?_, y, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure (Or.inl rfl))
  · exact Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure (Or.inr rfl))
  · exact Subtype.ext hx3
  · exact Subtype.ext hy3
  · intro hc
    exact hxy (congrArg Subtype.val hc)

section Certs


private theorem exists_pair_barCentralizer_unitary {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {n : ℕ} (hn : Odd n)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 (3 * n)) {a : G} (ha3 : a ^ 3 = 1)
    (hk : KFacts.InducesStdKind L a .field) :
    ∃ Q : Subgroup (L ⧸ aschbacherSolvableCore 3 L),
      Q ≤ Sec8.barCentralizer (Subgroup.zpowers a) L ∧ IsPGroup 3 Q ∧
        ∃ x ∈ Q, ∃ y ∈ Q, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := hn.pos
  have h3m : 1 ≤ 3 * n := by omega
  have hU := unitaryFieldData_galoisField 2 (3 * n) h3m
  have hq2 : 2 < 2 ^ (3 * n) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
  have hmo3 : Odd (3 * n) := Nat.odd_mul.mpr ⟨by decide, hn⟩
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_fwd (e₁.trans (projSUEquivUnitaryPSU 2 (3 * n) hU)).symm
      (KFacts.center_unitaryPSU_three_eq_bot hU hq2)
  have hcard : Nat.card (L ⧸ aschbacherSolvableCore 3 L) =
      CFSG.Open.ordTwistedA 2 (2 ^ (3 * n)) :=
    (Nat.card_congr e₁.toEquiv).trans (KFacts.card_projSU_three_two h3m)
  have hodd := KFacts.not_oddCharStdModel_of_mulEquiv_projSU (by omega : 2 ≤ 3 * n) e₁
  rcases KFacts.inducesKindPSU3_or_oddCharStdModel hmo3 hcard hZ hk with
    ⟨K, _, hK, hq, hkK⟩ | hO
  · obtain ⟨σ, -, f₀, hf₀, h₀, ⟨Φ⟩⟩ := KFacts.exists_barCentralizer_mulEquiv_pgu3 hq ha3 hkK
    obtain rfl : f₀ = n := by omega
    have hmod : ModThree false (2 ^ f₀) := by
      show 2 ^ f₀ % 3 = 2
      exact two_pow_mod_three_of_odd hn
    obtain ⟨Q, hQ⟩ := exists_pair_projImage_glPi_false h₀ hmod
    obtain ⟨Q', hQ'le, hQ'⟩ := exists_isPGroup_pair_map
      ((Sec8.barCentralizer (Subgroup.zpowers a) L).subtype.comp Φ.symm.toMonoidHom)
      (Subtype.val_injective.comp Φ.symm.injective) ⟨Q, hQ⟩
    refine ⟨Q', hQ'le.trans ?_, hQ'⟩
    rintro _ ⟨q, -, rfl⟩
    exact (Φ.symm q).2
  · exact (hodd hO).elim

section KindPSL

open Matrix CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.KFacts.OddChar
open CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.Open (ordA ordTwistedA ordBC ordG2 ordTrialityD4 ordSuzuki ordTwistedF4)

open CFSG.RankThree.PartTwo.Sec8.Item8ModelProof

private theorem exists_inducesKindPSL_of_inducesStdKind {G : Type} [Group G] [Finite G]
    (L : Subgroup G) (x : G) (n : ℕ) (k : KFacts.AutKind) (hn : Even n) (hn3 : 3 ≤ n)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n)))
    (hx : KFacts.InducesStdKind L x k) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      KFacts.InducesKindPSL 3 K L x k := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨eL⟩ := hL
  have hcardX : Nat.card (L ⧸ aschbacherSolvableCore 3 L) = ordA 2 (2 ^ n) :=
    (Nat.card_congr eL.toEquiv).trans (card_projSL_three_galois (by omega))
  have hM : ∀ {M : Type} [Group M], (L ⧸ aschbacherSolvableCore 3 L ≃* M) →
      Nat.card M = ordA 2 (2 ^ n) := fun e => (Nat.card_congr e.toEquiv).symm.trans hcardX
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    center_eq_bot_of_mulEquiv_fwd (eL.trans (Sec4.projSLEquivProjectiveSL 3 _)).symm
      (Sec21.Item223CensusResProof.center_projectiveSL_three _)
  have hodd := not_oddCharStdModel_of_mulEquiv_projSL hn2 eL
  have h3 : 3 ∣ 2 ^ n - 1 := three_dvd_two_pow_sub_one hn
  cases hx with
  | psl2 K h =>
    obtain ⟨e, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have h1 := hM e
      rw [card_psl_eq_ordA (by norm_num) hKf] at h1
      rcases eq_of_ordA_eq_ordA_two (by norm_num) hf hn2 h1 with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    · exact (hodd ⟨K, inferInstance, inferInstance, hK2, Or.inl ⟨e⟩⟩).elim
  | psl m K hm h =>
    obtain ⟨e, -⟩ := id h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have h1 := hM e
      rw [← Nat.card_congr (LinearCover.projectiveSpecialLinearEquivProjectiveSL m K).toEquiv,
        card_psl_eq_ordA (by omega) hKf] at h1
      rcases eq_of_ordA_eq_ordA_two (by omega) hf hn2 h1 with ⟨hm3, rfl⟩ | ⟨hm4, -, hn⟩
      · obtain rfl : m = 3 := by omega
        exact ⟨K, inferInstance, inferInstance, hKf, h⟩
      · omega
    · exact (hodd ⟨K, inferInstance, inferInstance, hK2, Or.inr (Or.inl ⟨m, hm, ⟨e⟩⟩)⟩).elim
  | sl m K hm h =>
    obtain ⟨e, -, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have hZ' : Subgroup.center (SpecialLinearGroup (Fin m) K) = ⊥ :=
        center_eq_bot_of_mulEquiv_fwd e hZ
      have hc1 : Nat.card (Subgroup.center (SpecialLinearGroup (Fin m) K)) = 1 := by
        rw [hZ', Subgroup.card_bot]
      have h1 := hM e
      have h2 : Nat.card (SpecialLinearGroup (Fin m) K) =
          Nat.card (ProjectiveSpecialLinearGroup (Fin m) K) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
          (Subgroup.center (SpecialLinearGroup (Fin m) K)), hc1, mul_one]
      rw [h2, card_psl_eq_ordA (by omega) hKf] at h1
      rcases eq_of_ordA_eq_ordA_two (by omega) hf hn2 h1 with ⟨hm3, rfl⟩ | ⟨hm4, -, hn⟩
      · obtain rfl : m = 3 := by omega
        exact (Sec21.Item223CensusResProof.center_SL_three_ne_bot (by rw [hKf]; exact h3)
          hZ').elim
      · omega
    · exact (hodd ⟨K, inferInstance, inferInstance, hK2,
        Or.inr (Or.inr (Or.inl ⟨m, hm, ⟨e⟩⟩))⟩).elim
  | @psu3 p f K _ hK hq h =>
    obtain ⟨e, -⟩ := id h
    by_cases hp : p = 2
    · subst hp
      have h1 := hM e
      rw [card_unitaryPSU_three_eq hK] at h1
      exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (by norm_num) (by omega) le_rfl
        hK.one_le h1.symm).elim
    · have := hK.finite
      have : CharP K p := hK.charP
      exact (hodd ⟨K, inferInstance, inferInstance, by rw [ringChar.eq K p]; exact hp,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, f, hK, Or.inl ⟨e⟩⟩))))⟩).elim
  | @su3 p f K _ hK hq h =>
    obtain ⟨e, -, -⟩ := h
    by_cases hp : p = 2
    · subst hp
      have hZ' : Subgroup.center (unitarySU 2 f K 3) = ⊥ := center_eq_bot_of_mulEquiv_fwd e hZ
      by_cases h3' : 3 ∣ 2 ^ f + 1
      · obtain ⟨z, hz, hz1, -⟩ := exists_mem_center_statedSU_ne_one hK h3'
        rw [hZ', Subgroup.mem_bot] at hz
        exact (hz1 hz).elim
      · have hsc : Nat.card (unitaryScalars hK 3) = 1 := by
          rw [card_unitaryScalars hK (by norm_num)]
          exact Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3')
        have h1 := hM e
        have h2 : Nat.card (unitarySU 2 f K 3) = ordTwistedA 2 (2 ^ f) := by
          rw [← card_unitaryPSU_three_eq hK,
            (unitaryScalars hK 3).card_eq_card_quotient_mul_card_subgroup, hsc, mul_one]
        rw [h2] at h1
        exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (by norm_num) (by omega) le_rfl
          hK.one_le h1.symm).elim
    · have := hK.finite
      have : CharP K p := hK.charP
      exact (hodd ⟨K, inferInstance, inferInstance, by rw [ringChar.eq K p]; exact hp,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, f, hK, Or.inr ⟨e⟩⟩))))⟩).elim
  | psp r K hr h =>
    obtain ⟨e, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · have hr3 : 3 ≤ r := by
        rcases hr with hr | ⟨-, hc⟩
        · exact hr
        · exact (hc hK2).elim
      obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have : CharP K 2 := ringChar.of_eq hK2
      have h1 := hM e
      rw [card_statedProj_statedSp_eq_ordBC hf hKf] at h1
      exact (ordBC_ne_ordA_two hr3 hf (by omega) h1).elim
    · have hr2 : 2 ≤ r := by rcases hr with hr | ⟨rfl, -⟩ <;> omega
      exact (hodd ⟨K, inferInstance, inferInstance, hK2,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr2, ⟨e⟩⟩)))⟩).elim
  | psp4even F h =>
    obtain ⟨e, -⟩ := h
    obtain ⟨f, hf, hFf⟩ := exists_card_eq_two_pow (ringChar.eq F 2)
    have h1 := hM e
    rw [card_statedProj_statedSp_eq_ordBC hf hFf] at h1
    exact (CFSG.Timmesfeld.Orders.ordA_ne_ordBC_two (by norm_num) (by omega) hf h1.symm).elim
  | g2 K hK3 hK4 h =>
    obtain ⟨e, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have h1 := hM e
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hKf] at h1
      exact (ordG2_ne_ordA_two hf (by omega) h1).elim
    · exact (hodd ⟨K, inferInstance, inferInstance, hK2,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))⟩).elim
  | sz a K ha hK h =>
    obtain ⟨e, -⟩ := h
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have h1 := hM e
    rw [Nat.card_congr
        (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).toEquiv,
      CFSG.RankThree.PartTwo.Census.card_suzukiMatrixGroup (by omega), suzuki_eq_ordSuzuki] at h1
    exact (ordSuzuki_ne_ordA_two (by omega) (by omega) h1).elim
  | triality f hf K hK σ hσ h =>
    obtain ⟨e, -, -⟩ := h
    have h1 := hM e
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_D4_two hf hK σ.toRingHom
      hσ] at h1
    exact (ordTrialityD4_ne_ordA_two hf (by omega) h1).elim
  | largeRee a ha K hK h =>
    obtain ⟨e, -⟩ := h
    have h1 := hM e
    rw [(CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
      a K hK).1, ree_native_eq_ordTwistedF4 Nat.one_le_two_pow] at h1
    exact (ordTwistedF4_ne_ordA_two (by omega) (by omega) h1).elim

private theorem inducesKindPSL_galoisField {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x : G} {n : ℕ} {k : KFacts.AutKind} (hn : Even n) (hn3 : 3 ≤ n)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n))
    (hx : KFacts.InducesStdKind L x k) : KFacts.InducesKindPSL 3 (GaloisField 2 n) L x k := by
  obtain ⟨K, _, _, hK, hkK⟩ := exists_inducesKindPSL_of_inducesStdKind L x n k hn hn3 ⟨φ⟩ hx
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 n) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 n (by omega)]
  exact inducesKindPSL_of_ringEquiv (FiniteField.ringEquivOfCardEq hcard) 3 hkK

end KindPSL

private theorem exists_pair_barCentralizer_linear {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {n : ℕ} (hn : Even n) (hn1 : 1 ≤ n)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 (3 * n))) {a : G}
    (ha3 : a ^ 3 = 1) (hk : KFacts.InducesStdKind L a .field) :
    ∃ Q : Subgroup (L ⧸ aschbacherSolvableCore 3 L),
      Q ≤ Sec8.barCentralizer (Subgroup.zpowers a) L ∧ IsPGroup 3 Q ∧
        ∃ x ∈ Q, ∃ y ∈ Q, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm : 1 ≤ 3 * n := by omega
  have he : Even (3 * n) := hn.mul_left 3
  have h1 := inducesKindPSL_galoisField (k := .field) he (by omega) φ hk
  set F := GaloisField 2 (3 * n) with hF
  set e' : L ⧸ aschbacherSolvableCore 3 L ≃* projectiveSL 3 F :=
    φ.trans (Sec4.projSLEquivProjectiveSL 3 F) with he'
  obtain ⟨hx, hkind⟩ := (KFacts.inducesKindPSL_iff L le_rfl e' a .field).mp h1
  set β := KFacts.inducedAutHom L e' ⟨a, hx⟩ with hβ
  have hβ3 : β ^ 3 = 1 := KFacts.inducedAutHom_pow_eq_one L e' hx ha3
  have hD : β ∉ linearAutGroup 3 F :=
    (KFacts.stdPinnedPSL_separated (K := F) (n := 3) le_rfl).not_mem_inndiag_of_hasKind hkind
      (by decide) (by decide)
  obtain ⟨σ, hσ, H, hβH⟩ := KFacts.linear_order_three_field_descent le_rfl β hβ3 hD
  have hFfin : Finite F := inferInstance
  have h9 : 9 ∣ Nat.card Fˣ := by
    have hcard : Nat.card F = 2 ^ (3 * n) := GaloisField.card 2 (3 * n) (by omega)
    rw [Nat.card_units, hcard]
    have h6 : 6 ∣ 3 * n := by
      obtain ⟨k, hk2⟩ := hn
      exact ⟨k, by omega⟩
    exact (show 9 ∣ 2 ^ 6 - 1 by norm_num).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 h6)
  obtain ⟨Q₀, hQ₀le, hQ₀, hxy⟩ := exists_pair_fixed_fieldAut hσ h9
  obtain ⟨Q, hQle, hQ⟩ := exists_isPGroup_pair_map
    ((e'.symm : projectiveSL 3 F ≃* L ⧸ aschbacherSolvableCore 3 L).toMonoidHom.comp
      (conjAut 3 F H : projectiveSL 3 F ≃* projectiveSL 3 F).toMonoidHom)
    (e'.symm.injective.comp (conjAut 3 F H).injective)
    (T := (fieldAut 3 F σ).toMonoidHom.eqLocus (MonoidHom.id _)) ⟨Q₀, hQ₀le, hQ₀, hxy⟩
  refine ⟨Q, hQle.trans ?_, hQ⟩
  rintro _ ⟨t, ht, rfl⟩
  have ht' : fieldAut 3 F σ t = t := ht
  rw [Sec4.barCentralizer_zpowers_eq_autFix hx]
  have hθ : β = MulAut.congr e' (thetaQuotMulAut L (compAction L ⟨a, hx⟩)) :=
    KFacts.inducedAutHom_apply L e' _
  have hβc : β (conjAut 3 F H t) = conjAut 3 F H t := by
    rw [hβH, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, ht']
  have hc : e' (thetaQuotMulAut L (compAction L ⟨a, hx⟩) (e'.symm (conjAut 3 F H t))) =
      conjAut 3 F H t := by
    have := hβc
    rw [hθ] at this
    exact this
  show thetaQuotMulAut L (compAction L ⟨a, hx⟩) (e'.symm (conjAut 3 F H t)) =
    e'.symm (conjAut 3 F H t)
  apply e'.injective
  rw [hc]
  exact (MulEquiv.apply_symm_apply _ _).symm

theorem exists_noncomm_isPGroup_barCentralizer_of_field {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (hL : Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) 2 (3 * n)) {a : G}
    (ha3 : a ^ 3 = 1) (ha : KFacts.InducesStdKind L a .field) :
    ∃ Q : Subgroup (L ⧸ aschbacherSolvableCore 3 L),
      Q ≤ Sec8.barCentralizer (Subgroup.zpowers a) L ∧ IsPGroup 3 Q ∧
        ∃ x ∈ Q, ∃ y ∈ Q, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  rcases hL with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
  · have hne : Even n := by
      rcases Nat.even_or_odd (3 * n) with h | h
      · exact (Nat.even_mul.mp h).resolve_left (by decide)
      · have := two_pow_mod_three_of_odd h
        omega
    exact exists_pair_barCentralizer_linear hne hn φ ha3 ha
  · have hno : Odd n := by
      rcases Nat.even_or_odd (3 * n) with h | h
      · have := two_pow_mod_three_of_even h
        omega
      · exact (Nat.odd_mul.mp h).2
    exact exists_pair_barCentralizer_unitary hno ψ ha3 ha

end Certs

end CFSG.RankThree.PartTwo.Sec15.Liebeck159
