module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofTools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherUTools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)
open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

namespace Item424Res2

theorem normalizerMonoidHom_pow_four_of_conj {Y : Type*} [Group Y] {F : Subgroup Y} {r : Y}
    (hr : r ∈ Subgroup.normalizer (F : Set Y)) (h4 : ∀ y ∈ F, r ^ 4 * y * (r ^ 4)⁻¹ = y)
    {x : Y} (hx : x ∈ F) (h2 : r ^ 2 * x * (r ^ 2)⁻¹ ≠ x) :
    F.normalizerMonoidHom ⟨r, hr⟩ ∈ autIn (⊤ : Subgroup Y) F ∧
      F.normalizerMonoidHom ⟨r, hr⟩ ^ 4 = 1 ∧ F.normalizerMonoidHom ⟨r, hr⟩ ^ 2 ≠ 1 := by
  refine ⟨mem_autIn_iff.mpr ⟨r, hr, Subgroup.mem_top r, rfl⟩, ?_, ?_⟩
  · refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [← map_pow, MulAut.one_apply, Sec4.normalizerMonoidHom_apply_coe]
    exact h4 y y.2
  · intro h
    apply h2
    have h1 := congrArg (fun σ : MulAut F => ((σ ⟨x, hx⟩ : F) : Y)) h
    simp only [MulAut.one_apply] at h1
    rw [← map_pow, Sec4.normalizerMonoidHom_apply_coe] at h1
    exact h1

namespace U54

open Item434SmallTwoOther.UTools

local notation "uTorus" => Item434SmallTwoOther.UTools.torusHom

section General

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem torusHom_smul_eq {n : ℕ} (hσ : ∀ c, σ (σ c) = c) (Q : HypQuad σ n) (Z : Subgroup Kˣ)
    (hZ : ∀ a ∈ Z, σ (a : K) = a) (p : Z × Z) (y : Fin n → K) :
    uTorus hσ Q Z hZ p • y = y + ((((p.1 : Kˣ) : K) - 1) * herm σ Q.P₁.f y) • Q.P₁.e +
      ((((p.1 : Kˣ) : K)⁻¹ - 1) * herm σ Q.P₁.e y) • Q.P₁.f +
      ((((p.2 : Kˣ) : K) - 1) * herm σ Q.P₂.f y) • Q.P₂.e +
      ((((p.2 : Kˣ) : K)⁻¹ - 1) * herm σ Q.P₂.e y) • Q.P₂.f := by
  rw [Item434SmallTwoOther.UTools.torusHom_apply, mul_smul,
    Item434SmallTwoOther.UTools.planeHom_apply, Item434SmallTwoOther.UTools.planeHom_apply,
    Item434SmallTwoOther.UTools.planeElt_smul, Item434SmallTwoOther.UTools.planeElt_smul]
  simp only [herm_add_right, herm_smul_right, Q.he₁e₂, Q.he₁f₂, Q.hf₁e₂, Q.hf₁f₂, mul_zero,
    add_zero]
  abel

theorem mul_torusHom_of_smul {n : ℕ} (hσ : ∀ c, σ (σ c) = c) (Q : HypQuad σ n)
    (Z : Subgroup Kˣ) (hZ : ∀ a ∈ Z, σ (a : K) = a) {g : SUid σ n} {l l' : K}
    (h₁ : g • Q.P₂.e = Q.P₁.e) (h₂ : g • Q.P₂.f = Q.P₁.f) (h₃ : g • Q.P₁.e = l • Q.P₂.f)
    (h₄ : g • Q.P₁.f = l' • Q.P₂.e) (hl : σ l * l' = 1) (p : Z × Z) :
    g * uTorus hσ Q Z hZ p = uTorus hσ Q Z hZ (p.2, p.1⁻¹) * g := by
  have hl' : σ l' * l = 1 := by
    have h := congrArg σ hl
    rw [map_mul, hσ, map_one] at h
    rw [mul_comm]
    exact h
  apply ext_smul
  intro y
  have hA : herm σ Q.P₁.f (g • y) = herm σ Q.P₂.f y := by rw [← h₂, herm_smul_smul]
  have hB : herm σ Q.P₁.e (g • y) = herm σ Q.P₂.e y := by rw [← h₁, herm_smul_smul]
  have hC : herm σ Q.P₂.f (g • y) = l' * herm σ Q.P₁.e y := by
    have h := herm_smul_smul σ g Q.P₁.e y
    rw [h₃, herm_smul_left] at h
    calc herm σ Q.P₂.f (g • y) = (σ l * l') * herm σ Q.P₂.f (g • y) := by rw [hl, one_mul]
      _ = l' * (σ l * herm σ Q.P₂.f (g • y)) := by ring
      _ = l' * herm σ Q.P₁.e y := by rw [h]
  have hD : herm σ Q.P₂.e (g • y) = l * herm σ Q.P₁.f y := by
    have h := herm_smul_smul σ g Q.P₁.f y
    rw [h₄, herm_smul_left] at h
    calc herm σ Q.P₂.e (g • y) = (σ l' * l) * herm σ Q.P₂.e (g • y) := by rw [hl', one_mul]
      _ = l * (σ l' * herm σ Q.P₂.e (g • y)) := by ring
      _ = l * herm σ Q.P₁.f y := by rw [h]
  rw [mul_smul, mul_smul, torusHom_smul_eq hσ Q Z hZ p y, torusHom_smul_eq hσ Q Z hZ _ (g • y),
    hA, hB, hC, hD, smul_add, smul_add, smul_add, smul_add, smul_comm g _ Q.P₁.e,
    smul_comm g _ Q.P₁.f, smul_comm g _ Q.P₂.e, smul_comm g _ Q.P₂.f, h₁, h₂, h₃, h₄]
  simp only [Subgroup.coe_inv, Units.val_inv_eq_inv_val, inv_inv]
  generalize g • y = z
  module

@[expose] def tau5 : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 3

theorem tau5_apply : tau5 0 = 2 ∧ tau5 1 = 3 ∧ tau5 2 = 1 ∧ tau5 3 = 0 ∧ tau5 4 = 4 := by
  decide +kernel

theorem sign_tau5 : Equiv.Perm.sign tau5 = -1 := by decide +kernel

@[expose] def wAlpha (W : WittData σ) : K := W.u ^ 2 * W.ω

theorem norm_wAlpha (W : WittData σ) : σ (wAlpha W) * wAlpha W = 1 := by
  rw [wAlpha, map_mul, map_pow]
  calc σ W.u ^ 2 * σ W.ω * (W.u ^ 2 * W.ω) = (σ W.u * W.u) ^ 2 * (σ W.ω * W.ω) := by ring
    _ = 1 := by rw [W.hu, W.hω]; ring

theorem wAlpha_ne_zero (W : WittData σ) : wAlpha W ≠ 0 := fun h => by
  have := norm_wAlpha W
  rw [h, mul_zero] at this
  exact zero_ne_one this

@[expose] def rDiag (W : WittData σ) : Fin 5 → K := ![wAlpha W, 1, 1, 1, (wAlpha W)⁻¹]

theorem norm_rDiag (W : WittData σ) (i : Fin 5) : σ (rDiag W i) * rDiag W i = 1 := by
  fin_cases i
  · exact norm_wAlpha W
  · simp [rDiag]
  · simp [rDiag]
  · simp [rDiag]
  · change σ (wAlpha W)⁻¹ * (wAlpha W)⁻¹ = 1
    rw [map_inv₀, ← mul_inv, norm_wAlpha W, inv_one]

@[expose] def rMat (W : WittData σ) : Matrix (Fin 5) (Fin 5) K :=
  tau5.permMatrix K * Matrix.diagonal (rDiag W)

theorem rMat_mulVec (W : WittData σ) (v : Fin 5 → K) :
    rMat W *ᵥ v = fun i => rDiag W (tau5 i) * v (tau5 i) := by
  rw [rMat, ← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec]
  ext i
  simp [Matrix.mulVec_diagonal]

theorem rMat_det (h2 : (2 : K) = 0) (W : WittData σ) : (rMat W).det = 1 := by
  have hα := wAlpha_ne_zero W
  rw [rMat, Matrix.det_mul, Matrix.det_permutation, sign_tau5, Matrix.det_diagonal,
    Fin.prod_univ_five]
  simp [rDiag, hα]
  linear_combination -h2

theorem rMat_iso (W : WittData σ) (x y : Fin 5 → K) :
    herm σ (rMat W *ᵥ x) (rMat W *ᵥ y) = herm σ x y := by
  rw [rMat_mulVec, rMat_mulVec]
  simp only [herm_def]
  have h : ∀ i, σ (rDiag W (tau5 i) * x (tau5 i)) * (rDiag W (tau5 i) * y (tau5 i)) =
      σ (x (tau5 i)) * y (tau5 i) := fun i => by
    rw [map_mul]
    calc σ (rDiag W (tau5 i)) * σ (x (tau5 i)) * (rDiag W (tau5 i) * y (tau5 i)) =
        (σ (rDiag W (tau5 i)) * rDiag W (tau5 i)) * (σ (x (tau5 i)) * y (tau5 i)) := by ring
      _ = σ (x (tau5 i)) * y (tau5 i) := by rw [norm_rDiag, one_mul]
  simp only [h]
  exact Equiv.sum_comp tau5 fun j => σ (x j) * y j

@[expose] noncomputable def rSU (h2 : (2 : K) = 0) (W : WittData σ) : SUid σ 5 :=
  mkSU σ (rMat W) (rMat_det h2 W) (rMat_iso W)

theorem rSU_smul (h2 : (2 : K) = 0) (W : WittData σ) (v : Fin 5 → K) :
    rSU h2 W • v = fun i => rDiag W (tau5 i) * v (tau5 i) := by
  rw [rSU, mkSU_smul, rMat_mulVec]

@[expose] def wLam (W : WittData σ) : K := W.u * (1 - W.ω)

@[expose] noncomputable def wLam' (W : WittData σ) : K := (1 - W.ω)⁻¹ * (W.u * W.ω)

theorem sigma_wLam_mul (W : WittData σ) : σ (wLam W) * wLam' W = 1 := by
  have h1 : (1 - W.ω) ≠ 0 := W.one_sub_ω_ne_zero
  rw [wLam, wLam', map_mul, map_sub, map_one]
  calc σ W.u * (1 - σ W.ω) * ((1 - W.ω)⁻¹ * (W.u * W.ω)) =
      (σ W.u * W.u) * (W.ω - σ W.ω * W.ω) * (1 - W.ω)⁻¹ := by ring
    _ = (1 - W.ω) * (1 - W.ω)⁻¹ := by rw [W.hu, W.hω]; ring
    _ = 1 := mul_inv_cancel₀ h1

theorem four_le_five : 4 ≤ 5 := by norm_num

theorem rSU_smul_e₂ (h2 : (2 : K) = 0) (W : WittData σ) :
    rSU h2 W • (stdQuad W four_le_five).P₂.e = (stdQuad W four_le_five).P₁.e := by
  obtain ⟨t0, t1, t2, t3, t4⟩ := tau5_apply
  rw [rSU_smul]
  funext i
  fin_cases i <;> simp [stdQuad, coordPair, t0, t1, t2, t3, t4, rDiag]

theorem rSU_smul_f₂ (h2 : (2 : K) = 0) (W : WittData σ) :
    rSU h2 W • (stdQuad W four_le_five).P₂.f = (stdQuad W four_le_five).P₁.f := by
  obtain ⟨t0, t1, t2, t3, t4⟩ := tau5_apply
  rw [rSU_smul]
  funext i
  fin_cases i <;> simp [stdQuad, coordPair, t0, t1, t2, t3, t4, rDiag]

theorem rSU_smul_e₁ (h2 : (2 : K) = 0) (W : WittData σ) :
    rSU h2 W • (stdQuad W four_le_five).P₁.e = wLam W • (stdQuad W four_le_five).P₂.f := by
  have h1 : (1 - W.ω) ≠ 0 := W.one_sub_ω_ne_zero
  obtain ⟨t0, t1, t2, t3, t4⟩ := tau5_apply
  rw [rSU_smul]
  funext i
  fin_cases i <;> simp [stdQuad, coordPair, t0, t1, t2, t3, t4, rDiag, wLam, wAlpha] <;>
    field_simp

theorem rSU_smul_f₁ (h2 : (2 : K) = 0) (W : WittData σ) :
    rSU h2 W • (stdQuad W four_le_five).P₁.f = wLam' W • (stdQuad W four_le_five).P₂.e := by
  obtain ⟨t0, t1, t2, t3, t4⟩ := tau5_apply
  rw [rSU_smul]
  funext i
  fin_cases i <;> simp [stdQuad, coordPair, t0, t1, t2, t3, t4, rDiag, wLam', wAlpha]
  ring

theorem rSU_mul_torusHom (h2 : (2 : K) = 0) (W : WittData σ) (hσ : ∀ c, σ (σ c) = c)
    (Z : Subgroup Kˣ) (hZ : ∀ a ∈ Z, σ (a : K) = a) (p : Z × Z) :
    rSU h2 W * uTorus hσ (stdQuad W four_le_five) Z hZ p =
      uTorus hσ (stdQuad W four_le_five) Z hZ (p.2, p.1⁻¹) * rSU h2 W :=
  mul_torusHom_of_smul hσ _ Z hZ (rSU_smul_e₂ h2 W) (rSU_smul_f₂ h2 W) (rSU_smul_e₁ h2 W)
    (rSU_smul_f₁ h2 W) (sigma_wLam_mul W) p

end General

section GF16

local notation "r₁₆" => rSU two_eq_zero_gf16 W₁₆

local notation "d₁₆" => uTorus isUnitaryInvolution_gf16.invol (stdQuad W₁₆ four_le_five) Z₃ fix_Z₃

theorem piSU_r_conj (p : Z₃ × Z₃) :
    piSU 5 r₁₆ * piSU 5 (d₁₆ p) * (piSU 5 r₁₆)⁻¹ = piSU 5 (d₁₆ (p.2, p.1⁻¹)) := by
  rw [← map_inv, ← map_mul, ← map_mul, rSU_mul_torusHom, mul_inv_cancel_right]

theorem piSU_r_sq_conj (p : Z₃ × Z₃) :
    piSU 5 r₁₆ ^ 2 * piSU 5 (d₁₆ p) * (piSU 5 r₁₆ ^ 2)⁻¹ = piSU 5 (d₁₆ (p.1⁻¹, p.2⁻¹)) := by
  have e : piSU 5 r₁₆ ^ 2 * piSU 5 (d₁₆ p) * (piSU 5 r₁₆ ^ 2)⁻¹ =
      piSU 5 r₁₆ * (piSU 5 r₁₆ * piSU 5 (d₁₆ p) * (piSU 5 r₁₆)⁻¹) * (piSU 5 r₁₆)⁻¹ := by
    simp only [sq, _root_.mul_inv_rev, mul_assoc]
  rw [e, piSU_r_conj, piSU_r_conj]

theorem piSU_r_pow_four_conj (p : Z₃ × Z₃) :
    piSU 5 r₁₆ ^ 4 * piSU 5 (d₁₆ p) * (piSU 5 r₁₆ ^ 4)⁻¹ = piSU 5 (d₁₆ p) := by
  have e : piSU 5 r₁₆ ^ 4 * piSU 5 (d₁₆ p) * (piSU 5 r₁₆ ^ 4)⁻¹ =
      piSU 5 r₁₆ ^ 2 * (piSU 5 r₁₆ ^ 2 * piSU 5 (d₁₆ p) * (piSU 5 r₁₆ ^ 2)⁻¹) *
        (piSU 5 r₁₆ ^ 2)⁻¹ := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, _root_.mul_inv_rev]
    simp only [mul_assoc]
  rw [e, piSU_r_sq_conj, piSU_r_sq_conj]
  simp only [inv_inv, Prod.mk.eta]

theorem piSU_r_mem_normalizer :
    piSU 5 r₁₆ ∈ Subgroup.normalizer (P₀U 5 four_le_five : Set (projSU 5 2 2)) := by
  have := finite_projSU_gf16 5
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  rw [SetLike.mem_coe, P₀U, MonoidHom.mem_range] at hx
  obtain ⟨p, rfl⟩ := hx
  rw [SetLike.mem_coe, P₀U, MonoidHom.mem_range]
  exact ⟨(p.2, p.1⁻¹), (piSU_r_conj p).symm⟩

theorem exists_pow_four_P₀U :
    ∃ ρ ∈ autIn (⊤ : Subgroup (projSU 5 2 2)) (P₀U 5 four_le_five), ρ ^ 4 = 1 ∧ ρ ^ 2 ≠ 1 := by
  set ω' : Z₃ := ⟨ω₁₆, Subgroup.mem_zpowers ω₁₆⟩
  have hx : piSU 5 (d₁₆ (ω', 1)) ∈ P₀U 5 four_le_five := ⟨(ω', 1), rfl⟩
  have h4 : ∀ y ∈ P₀U 5 four_le_five, piSU 5 r₁₆ ^ 4 * y * (piSU 5 r₁₆ ^ 4)⁻¹ = y := by
    rintro y ⟨p, rfl⟩
    exact piSU_r_pow_four_conj p
  have h2 : piSU 5 r₁₆ ^ 2 * piSU 5 (d₁₆ (ω', 1)) * (piSU 5 r₁₆ ^ 2)⁻¹ ≠
      piSU 5 (d₁₆ (ω', 1)) := by
    rw [piSU_r_sq_conj]
    intro h
    have hinj := injective_comp_torusHom isUnitaryInvolution_gf16 two_eq_zero_gf16
      (stdQuad W₁₆ four_le_five) fix_Z₃ (piSU 5) piSU_eq_one
    have hp : (((ω', 1) : Z₃ × Z₃).1⁻¹, ((ω', 1) : Z₃ × Z₃).2⁻¹) = ((ω', 1) : Z₃ × Z₃) :=
      hinj h
    have h1 : ω'⁻¹ = ω' := congrArg Prod.fst hp
    have h1' : ω₁₆⁻¹ = ω₁₆ := congrArg Subtype.val h1
    have h3 : ω₁₆ ^ 2 = 1 := by
      calc ω₁₆ ^ 2 = ω₁₆⁻¹ * ω₁₆ := by rw [sq, h1']
        _ = 1 := inv_mul_cancel ω₁₆
    have h32 := orderOf_dvd_of_pow_eq_one h3
    rw [orderOf_ω₁₆] at h32
    norm_num at h32
  obtain ⟨hm, h4', h2'⟩ := normalizerMonoidHom_pow_four_of_conj piSU_r_mem_normalizer h4 hx h2
  exact ⟨_, hm, h4', h2'⟩

end GF16

end U54

open U54 Item434SmallTwoOther.UTools

theorem census424_of_u54 {X : Type} [Group X] [Finite X] (e : X ≃* projSU 5 2 2) :
    Census424 X := by
  have := finite_projSU_gf16 5
  intro D c d K h
  obtain ⟨ρ, hρ, h4, h2⟩ := exists_pow_four_P₀U
  exact (false_of_pow_four h (exists_pow_four_of_conj e
    Item434SmallTwoOther.U54.factorization_card_U54 (card_P₀U four_le_five) hρ h4 h2
    h.card_eq)).elim

end Item424Res2

end CFSG.RankThree.PartTwo.Sec4
