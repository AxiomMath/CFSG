module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeU3Tools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL33Tools
public import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434CharThree

open CFSG Matrix
open CFSG.SectionRank.OddCover (u3Mat)
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Mat

variable {K : Type} [Field K]

theorem mat_ut_of_commute_z {W : Matrix (Fin 3) (Fin 3) K} {c : K} (hc : c ≠ 0)
    (h : W * u3Mat 0 0 c = u3Mat 0 0 c * W) :
    W 1 0 = 0 ∧ W 2 0 = 0 ∧ W 2 1 = 0 ∧ W 0 0 = W 2 2 := by
  have e12 := congrFun (congrFun h 1) 2
  have e22 := congrFun (congrFun h 2) 2
  have e01 := congrFun (congrFun h 0) 1
  have e02 := congrFun (congrFun h 0) 2
  rw [(mul_u3Mat_apply W 0 0 c 1).2.2, (u3Mat_mul_apply W 0 0 c 2).2.1] at e12
  rw [(mul_u3Mat_apply W 0 0 c 2).2.2, (u3Mat_mul_apply W 0 0 c 2).2.2] at e22
  rw [(mul_u3Mat_apply W 0 0 c 0).2.1, (u3Mat_mul_apply W 0 0 c 1).1] at e01
  rw [(mul_u3Mat_apply W 0 0 c 0).2.2, (u3Mat_mul_apply W 0 0 c 2).1] at e02
  have h10 : W 1 0 = 0 := by
    have : W 1 0 * c = 0 := by linear_combination e12
    exact (mul_eq_zero.mp this).resolve_right hc
  have h20 : W 2 0 = 0 := by
    have : W 2 0 * c = 0 := by linear_combination e22
    exact (mul_eq_zero.mp this).resolve_right hc
  have h21 : W 2 1 = 0 := by
    have : c * W 2 1 = 0 := by linear_combination -e01
    exact (mul_eq_zero.mp this).resolve_left hc
  have h0022 : W 0 0 = W 2 2 := by
    have : c * (W 0 0 - W 2 2) = 0 := by linear_combination e02
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc)
  exact ⟨h10, h20, h21, h0022⟩

theorem mat_ut_of_commute_regular {W : Matrix (Fin 3) (Fin 3) K} {a b c : K} (ha : a ≠ 0)
    (hb : b ≠ 0) (h : W * u3Mat a b c = u3Mat a b c * W) :
    W 1 0 = 0 ∧ W 2 0 = 0 ∧ W 2 1 = 0 := by
  have e21 := congrFun (congrFun h 2) 1
  have e22 := congrFun (congrFun h 2) 2
  have e11 := congrFun (congrFun h 1) 1
  rw [(mul_u3Mat_apply W a b c 2).2.1, (u3Mat_mul_apply W a b c 1).2.2] at e21
  rw [(mul_u3Mat_apply W a b c 2).2.2, (u3Mat_mul_apply W a b c 2).2.2] at e22
  rw [(mul_u3Mat_apply W a b c 1).2.1, (u3Mat_mul_apply W a b c 1).2.1] at e11
  have h20 : W 2 0 = 0 := by
    have : W 2 0 * a = 0 := by linear_combination e21
    exact (mul_eq_zero.mp this).resolve_right ha
  have h21 : W 2 1 = 0 := by
    have : W 2 1 * b = 0 := by linear_combination e22 - c * h20
    exact (mul_eq_zero.mp this).resolve_right hb
  have h10 : W 1 0 = 0 := by
    have : W 1 0 * a = 0 := by linear_combination e11 + b * h21
    exact (mul_eq_zero.mp this).resolve_right ha
  exact ⟨h10, h20, h21⟩

theorem mat_eq_u3Mat_of_mul_eq_of_ut {M W : Matrix (Fin 3) (Fin 3) K} {a b c : K}
    (hW10 : W 1 0 = 0) (hW20 : W 2 0 = 0) (hW21 : W 2 1 = 0) (hdet : W.det ≠ 0)
    (h : M * W = W * u3Mat a b c) : M = u3Mat (M 0 1) (M 1 2) (M 0 2) := by
  rw [Matrix.det_fin_three, hW10, hW20, hW21] at hdet
  have hd : W 0 0 * W 1 1 * W 2 2 ≠ 0 := by
    intro h0
    apply hdet
    linear_combination h0
  have h0 : W 0 0 ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hd)
  have h1 : W 1 1 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hd)
  have h2 : W 2 2 ≠ 0 := right_ne_zero_of_mul hd
  have e : ∀ i j, M i 0 * W 0 j + M i 1 * W 1 j + M i 2 * W 2 j = (W * u3Mat a b c) i j :=
    fun i j => by rw [← mul_apply_three, h]
  have e00 := e 0 0
  have e10 := e 1 0
  have e20 := e 2 0
  have e11 := e 1 1
  have e21 := e 2 1
  have e22 := e 2 2
  rw [(mul_u3Mat_apply W a b c 0).1] at e00
  rw [(mul_u3Mat_apply W a b c 1).1] at e10
  rw [(mul_u3Mat_apply W a b c 2).1] at e20
  rw [(mul_u3Mat_apply W a b c 1).2.1] at e11
  rw [(mul_u3Mat_apply W a b c 2).2.1] at e21
  rw [(mul_u3Mat_apply W a b c 2).2.2] at e22
  have m00 : M 0 0 = 1 := by
    have : (M 0 0 - 1) * W 0 0 = 0 := by
      linear_combination e00 - M 0 1 * hW10 - M 0 2 * hW20
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h0)
  have m10 : M 1 0 = 0 := by
    have : M 1 0 * W 0 0 = 0 := by
      linear_combination e10 - M 1 1 * hW10 - M 1 2 * hW20 + hW10
    exact (mul_eq_zero.mp this).resolve_right h0
  have m20 : M 2 0 = 0 := by
    have : M 2 0 * W 0 0 = 0 := by
      linear_combination e20 - M 2 1 * hW10 - M 2 2 * hW20 + hW20
    exact (mul_eq_zero.mp this).resolve_right h0
  have m11 : M 1 1 = 1 := by
    have : (M 1 1 - 1) * W 1 1 = 0 := by
      linear_combination e11 - W 0 1 * m10 - M 1 2 * hW21 + a * hW10
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h1)
  have m21 : M 2 1 = 0 := by
    have : M 2 1 * W 1 1 = 0 := by
      linear_combination e21 - W 0 1 * m20 - M 2 2 * hW21 + a * hW20 + hW21
    exact (mul_eq_zero.mp this).resolve_right h1
  have m22 : M 2 2 = 1 := by
    have : (M 2 2 - 1) * W 2 2 = 0 := by
      linear_combination e22 - W 0 2 * m20 - W 1 2 * m21 + c * hW20 + b * hW21
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h2)
  exact eq_u3Mat_of_entries m00 m10 m20 m11 m21 m22

theorem u3Mat_pow_three [CharP K 3] (a b c : K) : u3Mat a b c ^ 3 = 1 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  rw [pow_three, CFSG.SectionRank.OddCover.u3Mat_mul, CFSG.SectionRank.OddCover.u3Mat_mul,
    ← CFSG.SectionRank.OddCover.u3Mat_zero]
  have e1 : a + (a + a) = 0 := by linear_combination a * h3
  have e2 : b + (b + b) = 0 := by linear_combination b * h3
  have e3 : c + (c + c + a * b) + a * (b + b) = 0 := by linear_combination (c + a * b) * h3
  rw [e1, e2, e3]

theorem mat_scalar_unitri_of_commute {W : Matrix (Fin 3) (Fin 3) K} {a₀ b₀ b c : K}
    (ha₀ : a₀ ≠ 0) (hb₀ : b₀ ≠ 0) (hz : W * u3Mat 0 0 b₀ = u3Mat 0 0 b₀ * W)
    (hx : W * u3Mat a₀ b c = u3Mat a₀ b c * W) :
    W 1 0 = 0 ∧ W 2 0 = 0 ∧ W 2 1 = 0 ∧ W 1 1 = W 0 0 ∧ W 2 2 = W 0 0 := by
  obtain ⟨h10, h20, h21, h0022⟩ := mat_ut_of_commute_z hb₀ hz
  have e01 := congrFun (congrFun hx 0) 1
  rw [(mul_u3Mat_apply W a₀ b c 0).2.1, (u3Mat_mul_apply W a₀ b c 1).1] at e01
  have h11 : W 1 1 = W 0 0 := by
    have : a₀ * (W 0 0 - W 1 1) = 0 := by linear_combination e01 + c * h21
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha₀)).symm
  exact ⟨h10, h20, h21, h11, h0022.symm⟩

theorem u3Mat_map (τ : K ≃+* K) (a b c : K) :
    (u3Mat a b c).map τ = u3Mat (τ a) (τ b) (τ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u3Mat]

end Mat

section SU

variable {F : Type} [Field F] {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c}

omit [Field F] in
theorem heisenbergMatrix_eq_u3Mat {F : Type} [Field F] (σ : F ≃+* F) (a b : F) :
    heisenbergMatrix σ (0 : Fin 3) 1 a b = u3Mat a (-σ a) b := by
  rw [CFSG.LieType.Steinberg.heisenbergMatrix_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u3Mat]

theorem exists_coe_eq_u3Mat_of_mem_heisU {g : SU σ 3} (hg : g ∈ heisU hσ) :
    ∃ b : F, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      u3Mat (ent01 g) (-σ (ent01 g)) b := by
  obtain ⟨a, b, -, hm⟩ := hg
  have ha : ent01 g = a := by rw [ent01, hm, heisenbergMatrix_apply01]
  exact ⟨b, by rw [hm, ha, heisenbergMatrix_eq_u3Mat]⟩

theorem pow_three_eq_one_of_coe_eq_u3Mat [CharP F 3] {g : SU σ 3} {a b c : F}
    (h : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = u3Mat a b c) : g ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, h, u3Mat_pow_three]
  rfl

theorem coe_mul_eq_u3Mat {g g' : SU σ 3} {a b c a' b' c' : F}
    (hg : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = u3Mat a b c)
    (hg' : ((g' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = u3Mat a' b' c') :
    (((g * g' : SU σ 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      u3Mat (a + a') (b + b') (c + c' + a * b') := by
  rw [Subgroup.coe_mul, Units.val_mul, hg, hg', CFSG.SectionRank.OddCover.u3Mat_mul]

theorem det_coe_SU (g : SU σ 3) : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
  g.2.1

theorem coe_mul_comm_of_commute {g g' : SU σ 3} (h : g * g' = g' * g) :
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((g' : GL (Fin 3) F) : Matrix _ _ F) =
      ((g' : GL (Fin 3) F) : Matrix _ _ F) * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have := congrArg (fun k : SU σ 3 => ((k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
  simpa using this

theorem commutator_pow_three_heisU [CharP F 3] {v w r : SU σ 3} (hv : v ∈ heisU hσ)
    (hv1 : v ≠ 1) (hwv : w * v = v * w) (hr : r ∈ heisU hσ) :
    (r * w * r⁻¹ * w⁻¹) ^ 3 = 1 := by
  obtain ⟨b, hvm⟩ := exists_coe_eq_u3Mat_of_mem_heisU hv
  have hcomm := coe_mul_comm_of_commute hwv
  rw [hvm] at hcomm
  have hut : ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
    by_cases ha : ent01 v = 0
    · rw [ha, map_zero, neg_zero] at hcomm
      have hb : b ≠ 0 := by
        rintro rfl
        apply hv1
        apply Subtype.ext
        apply Units.ext
        rw [hvm, ha, map_zero, neg_zero, CFSG.SectionRank.OddCover.u3Mat_zero]
        rfl
      obtain ⟨h10, h20, h21, -⟩ := mat_ut_of_commute_z hb hcomm
      exact ⟨h10, h20, h21⟩
    · have hσa : -σ (ent01 v) ≠ 0 := neg_ne_zero.mpr ((map_ne_zero σ).mpr ha)
      exact mat_ut_of_commute_regular ha hσa hcomm
  obtain ⟨h10, h20, h21⟩ := hut
  have hrinv : r⁻¹ ∈ heisU hσ := (heisU hσ).inv_mem hr
  obtain ⟨b', hrm⟩ := exists_coe_eq_u3Mat_of_mem_heisU hrinv
  obtain ⟨b'', hrm'⟩ := exists_coe_eq_u3Mat_of_mem_heisU hr
  have hM : ((w * r⁻¹ * w⁻¹ : SU σ 3) : GL (Fin 3) F) * (w : GL (Fin 3) F) =
      (w : GL (Fin 3) F) * (r⁻¹ : SU σ 3) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
    congr 1
    group
  have hM' := congrArg (fun k : GL (Fin 3) F => (k : Matrix (Fin 3) (Fin 3) F)) hM
  simp only [Units.val_mul] at hM'
  rw [hrm] at hM'
  have hMu := mat_eq_u3Mat_of_mul_eq_of_ut h10 h20 h21
    (by rw [det_coe_SU]; exact one_ne_zero) hM'
  have hcm := coe_mul_eq_u3Mat hrm' hMu
  rw [show r * w * r⁻¹ * w⁻¹ = r * (w * r⁻¹ * w⁻¹) by group]
  exact pow_three_eq_one_of_coe_eq_u3Mat hcm

end SU

section Finite

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 3] (hF : Nat.card F = (3 ^ f) ^ 2)

include hF

theorem exists_z_x_mem_lineU {a₀ : F} :
    ∃ (z x : SU (unitaryInvolution F 3 f) 3) (b₀ b₁ : F),
      z ∈ lineU (unitaryInvolution_involutive hF) a₀ ∧
      x ∈ lineU (unitaryInvolution_involutive hF) a₀ ∧ b₀ ≠ 0 ∧
      ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = u3Mat 0 0 b₀ ∧
      ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        u3Mat a₀ (-unitaryInvolution F 3 f a₀) b₁ ∧
      unitaryInvolution F 3 f b₀ = -b₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set σ := unitaryInvolution F 3 f with hσdef
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hζ' : (ζ : F) + σ ζ = 0 := (mem_traceZero σ).mp ζ.2
  obtain ⟨c, hc⟩ := exists_add_unitaryInvolution_eq hF (a := -(σ a₀ * a₀))
    (by rw [map_neg, map_mul, hσ, mul_comm])
  have hz0 : (ζ : F) + σ ζ + σ 0 * 0 = 0 := by rw [mul_zero, add_zero]; exact hζ'
  have hx0 : c + σ c + σ a₀ * a₀ = 0 := by rw [hc]; ring
  refine ⟨CFSG.SectionRank.OddCover.heisSU hσ 0 ζ hz0,
    CFSG.SectionRank.OddCover.heisSU hσ a₀ c hx0, ζ, c, ⟨⟨_, _, hz0, rfl⟩, 0, map_zero σ, ?_⟩,
    ⟨⟨_, _, hx0, rfl⟩, 1, map_one σ, ?_⟩, hζ, ?_, ?_, by linear_combination hζ'⟩
  · rw [ent01, CFSG.SectionRank.OddCover.coe_heisSU, heisenbergMatrix_apply01, zero_mul]
  · rw [ent01, CFSG.SectionRank.OddCover.coe_heisSU, heisenbergMatrix_apply01, one_mul]
  · rw [CFSG.SectionRank.OddCover.coe_heisSU, heisenbergMatrix_eq_u3Mat, map_zero, neg_zero]
  · rw [CFSG.SectionRank.OddCover.coe_heisSU, heisenbergMatrix_eq_u3Mat]

theorem card_lineU_le {a₀ : F} (ha₀ : a₀ ≠ 0) :
    Nat.card (lineU (unitaryInvolution_involutive hF) a₀) ≤ (3 ^ f) ^ 2 := by
  have hσ : ∀ c, unitaryInvolution F 3 f (unitaryInvolution F 3 f c) = c :=
    unitaryInvolution_involutive hF
  have htr : ∀ a : F, ∃ c : F,
      c + unitaryInvolution F 3 f c = -(unitaryInvolution F 3 f a * a) := fun a =>
    exists_add_unitaryInvolution_eq hF (by rw [map_neg, map_mul, hσ, mul_comm])
  choose c hc using htr
  have hab : ∀ g : lineU (unitaryInvolution_involutive hF) a₀, ∃ a b : F,
      b + unitaryInvolution F 3 f b + unitaryInvolution F 3 f a * a = 0 ∧
      ent01 (g : SU (unitaryInvolution F 3 f) 3) = a ∧
      (((g : SU (unitaryInvolution F 3 f) 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2 = b ∧
      (((g : SU (unitaryInvolution F 3 f) 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        heisenbergMatrix (unitaryInvolution F 3 f) (0 : Fin 3) 1 a b := by
    rintro ⟨g, ⟨a, b, hab, hm⟩, -⟩
    refine ⟨a, b, hab, ?_, ?_, hm⟩
    · rw [ent01, hm, heisenbergMatrix_apply01]
    · rw [hm, heisenbergMatrix_apply02]
  have hfix : ∀ g : lineU (unitaryInvolution_involutive hF) a₀,
      ent01 (g : SU (unitaryInvolution F 3 f) 3) / a₀ ∈
        CFSG.LieType.Steinberg.fixedSubfield F 3 f := by
    rintro ⟨g, -, s, hs, hgs⟩
    rw [CFSG.LieType.Steinberg.mem_fixedSubfield]
    change unitaryInvolution F 3 f (ent01 g / a₀) = ent01 g / a₀
    rw [hgs, mul_div_cancel_right₀ _ ha₀, hs]
  have htz : ∀ g : lineU (unitaryInvolution_involutive hF) a₀,
      (((g : SU (unitaryInvolution F 3 f) 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2 -
        c (ent01 (g : SU (unitaryInvolution F 3 f) 3)) ∈ traceZero (unitaryInvolution F 3 f) := by
    intro g
    obtain ⟨a, b, hab', ha, hb, -⟩ := hab g
    rw [mem_traceZero, ha, hb, map_sub]
    linear_combination hab' - hc a
  let φ : lineU (unitaryInvolution_involutive hF) a₀ →
      CFSG.LieType.Steinberg.fixedSubfield F 3 f × traceZero (unitaryInvolution F 3 f) :=
    fun g => (⟨_, hfix g⟩, ⟨_, htz g⟩)
  have hφ : Function.Injective φ := by
    intro g g' hgg
    obtain ⟨a, b, -, ha, hb, hm⟩ := hab g
    obtain ⟨a', b', -, ha', hb', hm'⟩ := hab g'
    have h1 := congrArg (fun v => ((v.1 : CFSG.LieType.Steinberg.fixedSubfield F 3 f) : F)) hgg
    have h2 := congrArg (fun v => ((v.2 : traceZero (unitaryInvolution F 3 f)) : F)) hgg
    simp only [φ] at h1 h2
    rw [ha, ha', div_left_inj' ha₀] at h1
    subst h1
    rw [ha, ha', hb, hb', sub_left_inj] at h2
    subst h2
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [hm, hm']
  have h := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_prod, CFSG.LieType.Steinberg.card_fixedSubfield hF,
    CFSG.LieType.Steinberg.card_traceZero hF, ← sq] at h

theorem pow_three_eq_one_of_forall_commute_lineU {a₀ : F} (ha₀ : a₀ ≠ 0)
    {w : SU (unitaryInvolution F 3 f) 3}
    (hw : ∀ r ∈ lineU (unitaryInvolution_involutive hF) a₀, w * r = r * w) : w ^ 3 = 1 := by
  obtain ⟨z, x, b₀, b₁, hzR, hxR, hb₀, hzm, hxm, -⟩ := exists_z_x_mem_lineU hF (a₀ := a₀)
  have hz := coe_mul_comm_of_commute (hw z hzR)
  have hx := coe_mul_comm_of_commute (hw x hxR)
  rw [hzm] at hz
  rw [hxm] at hx
  obtain ⟨h10, h20, h21, h11, h22⟩ := mat_scalar_unitri_of_commute ha₀ hb₀ hz hx
  set W := ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hW
  have hdet : W.det = 1 := det_coe_SU w
  rw [Matrix.det_fin_three, h10, h20, h21, h11, h22] at hdet
  have h00 : W 0 0 = 1 := eq_one_of_pow_three_eq_one (by linear_combination hdet)
  exact pow_three_eq_one_of_coe_eq_u3Mat
    (eq_u3Mat_of_entries h00 h10 h20 (h11.trans h00) h21 (h22.trans h00))

theorem eq_bot_of_le_normalizer_lineU {a₀ : F} (ha₀ : a₀ ≠ 0)
    {W : Subgroup (SU (unitaryInvolution F 3 f) 3)} (hW3 : ¬ 3 ∣ Nat.card W)
    (hRW : lineU (unitaryInvolution_involutive hF) a₀ ≤
      Subgroup.normalizer (W : Set (SU (unitaryInvolution F 3 f) 3))) : W = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (SU (unitaryInvolution F 3 f) 3) := Finite.of_injective _ Subtype.val_injective
  have hcop : Nat.Coprime 3 (Nat.card W) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hW3
  have hW1 : ∀ w ∈ W, w ^ 3 = 1 → w = 1 := by
    intro w hw hw3
    have hd1 : orderOf (⟨w, hw⟩ : W) ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact Subtype.ext (by rw [Subgroup.coe_pow, hw3, Subgroup.coe_one])
    have h1 : orderOf (⟨w, hw⟩ : W) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hd1 (orderOf_dvd_natCard _)
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  have hf : f ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := F)
    rw [hF] at this
    norm_num at this
  have h9 : 3 ^ 2 ≤ Nat.card (lineU (unitaryInvolution_involutive hF) a₀) := by
    refine le_trans ?_ (card_lineU_ge hF ha₀)
    exact Nat.pow_le_pow_left (Nat.le_self_pow hf 3) 2
  rw [eq_bot_iff]
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three (isElemAbelian_lineU a₀) h9 hRW
    hcop fun v hvR hv1 => ?_
  rintro w ⟨hwW, hwv⟩
  have hwv' : w * v = v * w := Subgroup.mem_centralizer_singleton_iff.mp hwv
  have hcomm : ∀ r ∈ lineU (unitaryInvolution_involutive hF) a₀, w * r = r * w := by
    intro r hr
    have h3 := commutator_pow_three_heisU hvR.1 hv1 hwv' hr.1
    have hW' : r * w * r⁻¹ * w⁻¹ ∈ W :=
      W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRW hr) w).mp hwW) (W.inv_mem hwW)
    have h1 := hW1 _ hW' h3
    have key : w * r = (r * w * r⁻¹ * w⁻¹)⁻¹ * (r * w) := by group
    rw [key, h1, inv_one, one_mul]
  exact Subgroup.mem_bot.mpr (hW1 w hwW (pow_three_eq_one_of_forall_commute_lineU hF ha₀ hcomm))

end Finite


section Nine

variable {F : Type} [Field F] [Finite F] [CharP F 3] (hF : Nat.card F = (3 ^ 1) ^ 2)

include hF

theorem exists_matrix_normal_form (y : MulAut (SU (unitaryInvolution F 3 1) 3)) :
    ∃ (C : GL (Fin 3) F) (τ : F ≃+* F), ∀ g : SU (unitaryInvolution F 3 1) 3,
      (((y g : SU (unitaryInvolution F 3 1) 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (C : Matrix (Fin 3) (Fin 3) F) * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map τ *
          ((C⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 1 F :=
    ⟨Nat.prime_three, le_rfl, by rw [hF]; norm_num⟩
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 3
  let ψ : SU (unitaryInvolution F 3 1) 3 ≃* CFSG.ClassicalGroups.UnitaryFlag.unitarySU 3 1 F 3 :=
    (conjEquiv P hP).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hF 3))
  have hψg : ∀ k, ((ψ k : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 3 1 F 3) : GL (Fin 3) F) =
      P * k * P⁻¹ := by
    intro k
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, coe_conjEquiv]
  obtain ⟨B, δ, hBδ⟩ := CFSG.RankThree.PartTwo.KFacts.exists_suConj_mul_suField hU
    (by norm_num) (MulAut.congr ψ y)
  refine ⟨P⁻¹ * B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut δ P, δ, fun g => ?_⟩
  have hβψ : MulAut.congr ψ y (ψ g) = ψ (y g) := by
    rw [MulAut.congr_apply]
    change ψ (y (ψ.symm (ψ g))) = ψ (y g)
    rw [MulEquiv.symm_apply_apply]
  have hBg : ((MulAut.congr ψ y (ψ g) : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 3 1 F 3) :
      GL (Fin 3) F) =
      (B : GL (Fin 3) F) * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut δ
        ((ψ g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 3 1 F 3) : GL (Fin 3) F) *
        (B : GL (Fin 3) F)⁻¹ := by
    rw [hBδ, MulAut.mul_apply, CFSG.RankThree.PartTwo.KFacts.coe_suConj,
      CFSG.RankThree.PartTwo.KFacts.coe_suField]
    rfl
  rw [hβψ, hψg, hψg] at hBg
  have key : ((y g : SU (unitaryInvolution F 3 1) 3) : GL (Fin 3) F) =
      (P⁻¹ * B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut δ P) *
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut δ (g : GL (Fin 3) F) *
        (P⁻¹ * B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut δ P)⁻¹ := by
    have h1 : ((y g : SU (unitaryInvolution F 3 1) 3) : GL (Fin 3) F) =
        P⁻¹ * (P * (y g : SU (unitaryInvolution F 3 1) 3) * P⁻¹) * P := by group
    rw [h1, hBg, map_mul, map_mul, map_inv]
    group
  rw [key, Units.val_mul, Units.val_mul,
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut]

theorem ringAut_nine (τ : F ≃+* F) : τ = 1 ∨ τ = unitaryInvolution F 3 1 := by
  have hcard := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_three F
    (by rw [hF]; norm_num : Nat.card F = 3 ^ 2)).1
  have hσ1 : unitaryInvolution F 3 1 ≠ 1 := by
    obtain ⟨a, ha⟩ := exists_unitaryInvolution_ne hF
    intro h
    exact ha (by rw [h]; rfl)
  obtain ⟨x, hx⟩ := (Nat.card_eq_two_iff' (1 : RingAut F)).mp hcard
  by_cases h1 : τ = 1
  · exact Or.inl h1
  · right
    exact (hx.2 τ h1).trans (hx.2 _ hσ1).symm

theorem eq_one_of_fix_of_coprime {y : MulAut (SU (unitaryInvolution F 3 1) 3)}
    (hy3 : Nat.Coprime (orderOf y) 3) {a₀ : F} (ha₀ : a₀ ≠ 0)
    (hfix : ∀ r ∈ lineU (unitaryInvolution_involutive hF) a₀, y r = r) : y = 1 := by
  have hσ : ∀ c, unitaryInvolution F 3 1 (unitaryInvolution F 3 1 c) = c :=
    unitaryInvolution_involutive hF
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F 3] at h'
    norm_num at h'
  obtain ⟨z, x, b₀, b₁, hzR, hxR, hb₀, hzm, hxm, hσb₀⟩ := exists_z_x_mem_lineU hF (a₀ := a₀)
  obtain ⟨C, τ, hC⟩ := exists_matrix_normal_form hF y
  have hCinv : ((C⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (C : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hfixm : ∀ r ∈ lineU (unitaryInvolution_involutive hF) a₀,
      (C : Matrix (Fin 3) (Fin 3) F) * ((r : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map τ =
        ((r : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (C : Matrix (Fin 3) (Fin 3) F) := by
    intro r hr
    have h1 := hC r
    rw [hfix r hr] at h1
    calc (C : Matrix (Fin 3) (Fin 3) F) * ((r : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map τ =
        (C : Matrix (Fin 3) (Fin 3) F) * ((r : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map τ *
          (((C⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (C : Matrix (Fin 3) (Fin 3) F)) := by
          rw [hCinv, Matrix.mul_one]
      _ = ((r : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (C : Matrix (Fin 3) (Fin 3) F) := by
          rw [← Matrix.mul_assoc, ← h1]
  have hz := hfixm z hzR
  have hx := hfixm x hxR
  rw [hzm] at hz
  rw [hxm] at hx
  have hCdet : (C : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact (GeneralLinearGroup.det C).ne_zero
  obtain ⟨Cm, hCm⟩ : ∃ Cm : Matrix (Fin 3) (Fin 3) F, (C : Matrix (Fin 3) (Fin 3) F) = Cm :=
    ⟨_, rfl⟩
  rw [hCm] at hz hx hCdet
  rcases ringAut_nine hF τ with rfl | rfl
  ·
    have hmap : ∀ M : Matrix (Fin 3) (Fin 3) F, M.map (1 : F ≃+* F) = M := fun M => by
      ext i j
      rfl
    rw [hmap] at hz hx
    obtain ⟨h10, h20, h21, h11, h22⟩ := mat_scalar_unitri_of_commute ha₀ hb₀ hz hx
    have hα : Cm 0 0 ≠ 0 := by
      intro h0
      apply hCdet
      rw [Matrix.det_fin_three, h10, h20, h21, h11, h22, h0]
      ring
    have hUe : ∀ i j, ((Cm 0 0)⁻¹ • Cm) i j = (Cm 0 0)⁻¹ * Cm i j := fun i j => rfl
    have hU3 : ((Cm 0 0)⁻¹ • Cm) ^ 3 = 1 := by
      rw [eq_u3Mat_of_entries (M := (Cm 0 0)⁻¹ • Cm) (by rw [hUe, inv_mul_cancel₀ hα])
        (by rw [hUe, h10, mul_zero]) (by rw [hUe, h20, mul_zero])
        (by rw [hUe, h11, inv_mul_cancel₀ hα]) (by rw [hUe, h21, mul_zero])
        (by rw [hUe, h22, inv_mul_cancel₀ hα]), u3Mat_pow_three]
    have hCU : Cm = Cm 0 0 • ((Cm 0 0)⁻¹ • Cm) := by
      rw [smul_smul, mul_inv_cancel₀ hα, one_smul]
    have hCG : ∀ g : SU (unitaryInvolution F 3 1) 3,
        ((y g : SU (unitaryInvolution F 3 1) 3) : GL (Fin 3) F) = C * (g : GL (Fin 3) F) * C⁻¹ := by
      intro g
      apply Units.ext
      rw [hC g, hmap, Units.val_mul, Units.val_mul]
    have hC3 : ∀ N : GL (Fin 3) F, C ^ 3 * N = N * C ^ 3 := by
      intro N
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, hCm, hCU, smul_pow, hU3,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    have hy3' : y ^ 3 = 1 := by
      refine MulEquiv.ext fun g => ?_
      apply Subtype.ext
      rw [MulAut.one_apply, pow_three, MulAut.mul_apply, MulAut.mul_apply, hCG, hCG, hCG]
      calc C * (C * (C * (g : GL (Fin 3) F) * C⁻¹) * C⁻¹) * C⁻¹ =
          C ^ 3 * (g : GL (Fin 3) F) * (C ^ 3)⁻¹ := by rw [pow_three']; group
        _ = (g : GL (Fin 3) F) := by rw [hC3, mul_inv_cancel_right]
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hy3 (orderOf_dvd_of_pow_eq_one hy3'))
  ·
    exfalso
    simp only [u3Mat_map, map_zero, hσb₀] at hz
    simp only [u3Mat_map, map_neg, hσ] at hx
    have z12 := congrFun (congrFun hz 1) 2
    have z22 := congrFun (congrFun hz 2) 2
    have z01 := congrFun (congrFun hz 0) 1
    have z02 := congrFun (congrFun hz 0) 2
    rw [(mul_u3Mat_apply Cm 0 0 (-b₀) 1).2.2, (u3Mat_mul_apply Cm 0 0 b₀ 2).2.1] at z12
    rw [(mul_u3Mat_apply Cm 0 0 (-b₀) 2).2.2, (u3Mat_mul_apply Cm 0 0 b₀ 2).2.2] at z22
    rw [(mul_u3Mat_apply Cm 0 0 (-b₀) 0).2.1, (u3Mat_mul_apply Cm 0 0 b₀ 1).1] at z01
    rw [(mul_u3Mat_apply Cm 0 0 (-b₀) 0).2.2, (u3Mat_mul_apply Cm 0 0 b₀ 2).1] at z02
    have h10 : Cm 1 0 = 0 := by
      have : b₀ * Cm 1 0 = 0 := by linear_combination -z12
      exact (mul_eq_zero.mp this).resolve_left hb₀
    have h20 : Cm 2 0 = 0 := by
      have : b₀ * Cm 2 0 = 0 := by linear_combination -z22
      exact (mul_eq_zero.mp this).resolve_left hb₀
    have h21 : Cm 2 1 = 0 := by
      have : b₀ * Cm 2 1 = 0 := by linear_combination -z01
      exact (mul_eq_zero.mp this).resolve_left hb₀
    have h22 : Cm 2 2 = -Cm 0 0 := by
      have : b₀ * (Cm 2 2 + Cm 0 0) = 0 := by linear_combination -z02
      linear_combination (mul_eq_zero.mp this).resolve_left hb₀
    have x01 := congrFun (congrFun hx 0) 1
    have x12 := congrFun (congrFun hx 1) 2
    rw [(mul_u3Mat_apply Cm _ _ _ 0).2.1, (u3Mat_mul_apply Cm _ _ _ 1).1] at x01
    rw [(mul_u3Mat_apply Cm _ _ _ 1).2.2, (u3Mat_mul_apply Cm _ _ _ 2).2.1] at x12
    have e1 : Cm 0 0 * unitaryInvolution F 3 1 a₀ = a₀ * Cm 1 1 := by
      linear_combination x01 + b₁ * h21
    have e2 : -(a₀ * Cm 1 1) = unitaryInvolution F 3 1 a₀ * Cm 0 0 := by
      linear_combination x12 - unitaryInvolution F 3 1 b₁ * h10 -
        unitaryInvolution F 3 1 a₀ * h22
    have hα : Cm 0 0 ≠ 0 := by
      intro h0
      apply hCdet
      rw [Matrix.det_fin_three, h10, h20, h21, h22, h0]
      ring
    have hσa : unitaryInvolution F 3 1 a₀ ≠ 0 := (map_ne_zero _).mpr ha₀
    have : 2 * (unitaryInvolution F 3 1 a₀ * Cm 0 0) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h | h
    · exact h2 h
    · exact (mul_ne_zero hσa hα) h

theorem eq_bot_of_le_normalizer_unitary_three
    (hinj : Function.Injective
      (MulAut.conj : SU (unitaryInvolution F 3 1) 3 →* MulAut (SU (unitaryInvolution F 3 1) 3)))
    {a₀ : F} (ha₀ : a₀ ≠ 0) {Y : Subgroup (MulAut (SU (unitaryInvolution F 3 1) 3))}
    (hY3 : ¬ 3 ∣ Nat.card Y)
    (hRY : (lineU (unitaryInvolution_involutive hF) a₀).map
        (MulAut.conj : SU (unitaryInvolution F 3 1) 3 →* MulAut (SU (unitaryInvolution F 3 1) 3)) ≤
      Subgroup.normalizer (Y : Set (MulAut (SU (unitaryInvolution F 3 1) 3)))) : Y = ⊥ := by
  set I := inner (SU (unitaryInvolution F 3 1) 3) with hI
  set W : Subgroup (SU (unitaryInvolution F 3 1) 3) := (Y ⊓ I).comap MulAut.conj with hW
  have hWmap : W.map MulAut.conj = Y ⊓ I := Subgroup.map_comap_eq_self inf_le_right
  have hWcard : Nat.card W = Nat.card (Y ⊓ I : Subgroup _) := by
    rw [← hWmap, Subgroup.card_map_of_injective hinj]
  have hW3 : ¬ 3 ∣ Nat.card W := by
    rw [hWcard]
    exact fun h3 => hY3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hconjR : ∀ r ∈ lineU (unitaryInvolution_involutive hF) a₀, ∀ w ∈ W,
      r * w * r⁻¹ ∈ W := by
    intro r hr w hw
    have hY : MulAut.conj r * MulAut.conj w * (MulAut.conj r)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hRY ⟨r, hr, rfl⟩) _).mp hw.1
    change MulAut.conj (r * w * r⁻¹) ∈ Y ⊓ I
    rw [map_mul, map_mul, map_inv]
    exact ⟨hY, ⟨r * w * r⁻¹, by rw [map_mul, map_mul, map_inv]⟩⟩
  have hRW : lineU (unitaryInvolution_involutive hF) a₀ ≤
      Subgroup.normalizer (W : Set (SU (unitaryInvolution F 3 1) 3)) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hconjR r hr w, fun hw => ?_⟩
    have h1 := hconjR r⁻¹ ((lineU (unitaryInvolution_involutive hF) a₀).inv_mem hr) _ hw
    rwa [show r⁻¹ * (r * w * r⁻¹) * r⁻¹⁻¹ = w by group] at h1
  have hWbot := eq_bot_of_le_normalizer_lineU hF ha₀ hW3 hRW
  have hYI : Y ⊓ I = ⊥ := by rw [← hWmap, hWbot, Subgroup.map_bot]
  rw [eq_bot_iff]
  intro y hy
  have hfix : ∀ r ∈ lineU (unitaryInvolution_involutive hF) a₀, y r = r := by
    intro r hr
    have hcR := hRY ⟨r, hr, rfl⟩
    have hmemY : MulAut.conj r * y * (MulAut.conj r)⁻¹ * y⁻¹ ∈ Y :=
      Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hcR y).mp hy) (Y.inv_mem hy)
    have hmemI : MulAut.conj r * y * (MulAut.conj r)⁻¹ * y⁻¹ ∈ I := by
      have e : MulAut.conj r * y * (MulAut.conj r)⁻¹ * y⁻¹ =
          MulAut.conj r * (y * MulAut.conj r⁻¹ * y⁻¹) := by rw [map_inv]; group
      rw [e, mulAut_mul_conj_mul_inv]
      exact I.mul_mem ⟨r, rfl⟩ ⟨y r⁻¹, rfl⟩
    have h1 : MulAut.conj r * y * (MulAut.conj r)⁻¹ * y⁻¹ = 1 := by
      have hmem : MulAut.conj r * y * (MulAut.conj r)⁻¹ * y⁻¹ ∈ Y ⊓ I := ⟨hmemY, hmemI⟩
      rwa [hYI, Subgroup.mem_bot] at hmem
    have h2 : y * MulAut.conj r * y⁻¹ = MulAut.conj r := by
      have e : y * MulAut.conj r * y⁻¹ =
          (MulAut.conj r * y * (MulAut.conj r)⁻¹ * y⁻¹)⁻¹ * MulAut.conj r := by group
      rw [e, h1, inv_one, one_mul]
    rw [mulAut_mul_conj_mul_inv] at h2
    exact hinj h2
  have hy3 : Nat.Coprime (orderOf y) 3 := by
    have hd : orderOf y ∣ Nat.card Y := by
      rw [show orderOf y = orderOf (⟨y, hy⟩ : Y) from Subgroup.orderOf_coe ⟨y, hy⟩]
      exact orderOf_dvd_natCard _
    exact Nat.Coprime.coprime_dvd_left hd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3).symm
  exact Subgroup.mem_bot.mpr (eq_one_of_fix_of_coprime hF hy3 ha₀ hfix)

end Nine

end CFSG.RankThree.PartTwo.Sec4.Item434CharThree
