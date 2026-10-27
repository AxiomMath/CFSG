module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldFour

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projImage)
open CFSG.Open (StatedScalars)
open Matrix (ProjGenLinGroup)

namespace Hering129KN4

variable {K : Type} [Field K]

theorem exists_ne_zero_of_row (T : GL (Fin 3) K) (i : Fin 3) :
    ∃ j, (T : Matrix (Fin 3) (Fin 3) K) i j ≠ 0 := by
  by_contra h
  push Not at h
  have h0 := Matrix.det_eq_zero_of_row_eq_zero i h
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit T)).ne_zero h0

theorem exists_mul_mul_eq_scalar {T X : GL (Fin 3) K}
    (h : ProjGenLinGroup.mk T * ProjGenLinGroup.mk X * (ProjGenLinGroup.mk T)⁻¹ =
      (ProjGenLinGroup.mk X)⁻¹) :
    ∃ u : Kˣ, X * T * X = Matrix.GeneralLinearGroup.scalar (Fin 3) u * T := by
  have h' : ProjGenLinGroup.mk (T * X * T⁻¹) = ProjGenLinGroup.mk X⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv]
    exact h
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h'
  refine ⟨u⁻¹, ?_⟩
  calc X * T * X = X * (T * X * T⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) u) *
        (Matrix.GeneralLinearGroup.scalar (Fin 3) u)⁻¹ * T := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin 3) u⁻¹ * T := by rw [hu, map_inv]; group

theorem mul_eq_of_ne_zero {T X : GL (Fin 3) K} {x : Fin 3 → K}
    (hX : (X : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal x) {u : Kˣ}
    (h : X * T * X = Matrix.GeneralLinearGroup.scalar (Fin 3) u * T) {i j : Fin 3}
    (hT : (T : Matrix (Fin 3) (Fin 3) K) i j ≠ 0) : x i * x j = u := by
  have e := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) i j) h
  simp only [Units.val_mul, hX, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal] at e
  exact mul_right_cancel₀ hT (by linear_combination e)

theorem pairing_cases {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {j : Fin 3 → Fin 3} {u : K}
    (h : ∀ i, ![τ, τ ^ 2, 1] i * ![τ, τ ^ 2, 1] (j i) = u) :
    (j 0 = 1 ∧ j 2 = 2) ∨ (j 1 = 1 ∧ j 2 = 0) ∨ (j 0 = 0 ∧ j 2 = 1) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h2
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h2, div_one]
  have hττ : τ ^ 2 ≠ τ := by
    intro h2
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, h2, mul_one]
    exact mul_left_cancel₀ hτ0 this
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  generalize j 0 = a at h0 ⊢
  generalize j 1 = b at h1 ⊢
  generalize j 2 = c at h2 ⊢
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp at h0 h1 h2 ⊢ <;> grind

theorem exists_pow_of_pairing {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {a b c : K} (hc : c ≠ 0)
    (ha : a ^ 3 = c ^ 3) (hb : b ^ 3 = c ^ 3)
    (h : a * b = c * c ∨ a * c = b * b ∨ b * c = a * a) :
    ∃ m : ℕ, a = c * τ ^ m ∧ b = c * (τ ^ 2) ^ m := by
  have hroot : ∀ x : K, x ^ 3 = c ^ 3 → x = c ∨ x = c * τ ∨ x = c * τ ^ 2 := by
    intro x hx
    have h1 : (x / c) ^ 3 = 1 := by rw [div_pow, hx, div_self (pow_ne_zero 3 hc)]
    rcases Sec4.eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 h1 with h | h | h
    · left
      rw [div_eq_iff hc] at h
      linear_combination h
    · right; left
      rw [div_eq_iff hc] at h
      linear_combination h
    · right; right
      rw [div_eq_iff hc] at h
      linear_combination h
  rcases h with h | h | h
  · rcases hroot a ha with rfl | rfl | rfl
    · exact ⟨0, by ring, mul_left_cancel₀ hc (by linear_combination h)⟩
    · exact ⟨1, by ring, mul_left_cancel₀ hc (by linear_combination τ ^ 2 * h - c * b * hτ)⟩
    · exact ⟨2, by ring,
        mul_left_cancel₀ hc (by linear_combination τ * h - (c * b + c ^ 2 * τ) * hτ)⟩
  · rcases hroot b hb with rfl | rfl | rfl
    · exact ⟨0, mul_right_cancel₀ hc (by linear_combination h), by ring⟩
    · exact ⟨2, mul_right_cancel₀ hc (by linear_combination h),
        by linear_combination (-c * τ) * hτ⟩
    · exact ⟨1, mul_right_cancel₀ hc (by linear_combination h + c ^ 2 * τ * hτ), by ring⟩
  · rcases hroot a ha with rfl | rfl | rfl
    · exact ⟨0, by ring, mul_right_cancel₀ hc (by linear_combination h)⟩
    · exact ⟨1, by ring, mul_right_cancel₀ hc (by linear_combination h)⟩
    · exact ⟨2, by ring, mul_right_cancel₀ hc (by linear_combination h)⟩

theorem mem_zpowers_of_commute {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {y₂ T : GL (Fin 3) K}
    (hc : Sec4.diagTau hτ * y₂ = y₂ * Sec4.diagTau hτ) (h3 : ProjGenLinGroup.mk y₂ ^ 3 = 1)
    (htd : ProjGenLinGroup.mk T * ProjGenLinGroup.mk (Sec4.diagTau hτ) *
      (ProjGenLinGroup.mk T)⁻¹ = (ProjGenLinGroup.mk (Sec4.diagTau hτ))⁻¹)
    (hty : ProjGenLinGroup.mk T * ProjGenLinGroup.mk y₂ * (ProjGenLinGroup.mk T)⁻¹ =
      (ProjGenLinGroup.mk y₂)⁻¹) :
    ProjGenLinGroup.mk y₂ ∈ Subgroup.zpowers (ProjGenLinGroup.mk (Sec4.diagTau hτ)) := by
  set d := Sec4.diagTau hτ with hd
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hdv : (d : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![τ, τ ^ 2, 1] :=
    Sec4.coe_diagTau_eq_diagonal hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h2
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h2, div_one]
  have hττ : τ ≠ τ ^ 2 := by
    intro h2
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h2, mul_one]
    exact mul_left_cancel₀ hτ0 this
  have hdist : ∀ i j : Fin 3, i ≠ j → ![τ, τ ^ 2, 1] i ≠ ![τ, τ ^ 2, 1] j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> grind
  set x : Fin 3 → K := fun i => (y₂ : Matrix (Fin 3) (Fin 3) K) i i with hx
  have hy : (y₂ : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal x := by
    have hc' : (y₂ : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal ![τ, τ ^ 2, 1] =
        Matrix.diagonal ![τ, τ ^ 2, 1] * (y₂ : Matrix (Fin 3) (Fin 3) K) := by
      rw [← hdv, ← Units.val_mul, ← Units.val_mul, hc]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hx]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact Sec4.entry_eq_zero_of_commute_diagonal hc' (hdist i j hij)
  obtain ⟨s, hs⟩ : ∃ s : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) s = y₂ ^ 3 :=
    Sec4.mk_eq_one_iff_mem_statedScalars.mp (by rw [map_pow]; exact h3)
  have hcube : ∀ i, x i ^ 3 = s := by
    intro i
    have e := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) i i) hs
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Units.val_pow_eq_pow_val, hy, Matrix.diagonal_pow,
      Pi.pow_apply] at e
    exact e.symm
  have hx2 : x 2 ≠ 0 := by
    intro h0
    have h := hcube 2
    rw [h0] at h
    exact s.ne_zero (by rw [← h]; ring)
  obtain ⟨u₁, hu₁⟩ := exists_mul_mul_eq_scalar htd
  obtain ⟨u₂, hu₂⟩ := exists_mul_mul_eq_scalar hty
  choose j hj using exists_ne_zero_of_row T
  have hdj : ∀ i, ![τ, τ ^ 2, 1] i * ![τ, τ ^ 2, 1] (j i) = u₁ := fun i =>
    mul_eq_of_ne_zero hdv hu₁ (hj i)
  have hxj : ∀ i, x i * x (j i) = u₂ := fun i => mul_eq_of_ne_zero hy hu₂ (hj i)
  have hpair : x 0 * x 1 = x 2 * x 2 ∨ x 0 * x 2 = x 1 * x 1 ∨ x 1 * x 2 = x 0 * x 0 := by
    have e0 := hxj 0
    have e1 := hxj 1
    have e2 := hxj 2
    rcases pairing_cases hτ hτ1 hdj with ⟨h0, h2⟩ | ⟨h1, h2⟩ | ⟨h0, h2⟩
    · rw [h0] at e0
      rw [h2] at e2
      exact Or.inl (e0.trans e2.symm)
    · rw [h1] at e1
      rw [h2] at e2
      exact Or.inr (Or.inl ((mul_comm _ _).trans (e2.trans e1.symm)))
    · rw [h0] at e0
      rw [h2] at e2
      exact Or.inr (Or.inr ((mul_comm _ _).trans (e2.trans e0.symm)))
  obtain ⟨m, hm0, hm1⟩ := exists_pow_of_pairing hτ hτ1 hx2 (by rw [hcube, hcube])
    (by rw [hcube, hcube]) hpair
  have hym : (y₂ : Matrix (Fin 3) (Fin 3) K) =
      x 2 • ((d ^ m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hy, Units.val_pow_eq_pow_val, hdv, Matrix.diagonal_pow]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Matrix.diagonal_apply, hm0, hm1]
  rw [Sec4.mk_eq_of_coe_eq_smul hym, map_pow]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m

end Hering129KN4


theorem transitive_of_inverted {K : Type} [Field K] {p f : ℕ} {π : Bool}
    (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {V : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hVL : V ≤ projImage (Sec4.slPi π 3 (p ^ f) K)) (hV : CFSG.Assembly.IsElemAbelian 3 V)
    (hV9 : Nat.card V = 9) (hd : ProjGenLinGroup.mk (Sec4.diagTau hτ) ∈ V)
    {t : ProjGenLinGroup (Fin 3) K} (ht : ∀ v ∈ V, t * v * t⁻¹ = v⁻¹) :
    ∀ v ∈ V, v ≠ 1 → ∀ w ∈ V, w ≠ 1 →
      ∃ n ∈ projImage (Sec4.slPi π 3 (p ^ f) K) ⊓
        Subgroup.normalizer (V : Set (ProjGenLinGroup (Fin 3) K)), n * v * n⁻¹ = w := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite K := hK.finite
  haveI : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) ProjGenLinGroup.mk_surjective
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hmd1 : ProjGenLinGroup.mk (Sec4.diagTau hτ) ≠ 1 := fun h =>
    Sec4.diagTau_not_mem_statedScalars hτ hτ1 (Sec4.mk_eq_one_iff_mem_statedScalars.mp h)
  have hord : orderOf (ProjGenLinGroup.mk (Sec4.diagTau hτ)) = 3 :=
    orderOf_eq_prime (hV.2 _ hd) hmd1
  obtain ⟨v, hvV, hvnot⟩ :
      ∃ v ∈ V, v ∉ Subgroup.zpowers (ProjGenLinGroup.mk (Sec4.diagTau hτ)) := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (show V ≤ Subgroup.zpowers _ from fun x hx => hall x hx)
    rw [hV9, Nat.card_zpowers, hord] at this
    omega
  have hVeq : Subgroup.zpowers (ProjGenLinGroup.mk (Sec4.diagTau hτ)) ⊔ Subgroup.zpowers v = V :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr hd) (Subgroup.zpowers_le.mpr hvV))
      (by rw [hV9, Sec4.card_zpowers_sup_zpowers (hV.2 v hvV) hord hvnot (hcomm v hvV _ hd)])
  obtain ⟨y₂, hy₂S, rfl⟩ := Subgroup.mem_map.mp (hVL hvV)
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Kˣ, Sec4.diagTau hτ * y₂ * (Sec4.diagTau hτ)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * y₂ := by
    have h : ProjGenLinGroup.mk (Sec4.diagTau hτ * y₂ * (Sec4.diagTau hτ)⁻¹) =
        ProjGenLinGroup.mk y₂ := by
      rw [map_mul, map_mul, map_inv, hcomm _ hd _ hvV, mul_inv_cancel_right]
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
    refine ⟨u⁻¹, ?_⟩
    calc Sec4.diagTau hτ * y₂ * (Sec4.diagTau hτ)⁻¹ =
        (Matrix.GeneralLinearGroup.scalar (Fin 3) u)⁻¹ *
          (Sec4.diagTau hτ * y₂ * (Sec4.diagTau hτ)⁻¹ *
            Matrix.GeneralLinearGroup.scalar (Fin 3) u) := by
          rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u
            (Sec4.diagTau hτ * y₂ * (Sec4.diagTau hτ)⁻¹)).eq]
          group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) u⁻¹ * y₂ := by rw [hu, map_inv]
  by_cases hζ1 : ζ = 1
  ·
    exfalso
    apply hvnot
    obtain ⟨T, rfl⟩ := ProjGenLinGroup.mk_surjective t
    refine Hering129KN4.mem_zpowers_of_commute hτ hτ1 ?_ (hV.2 _ hvV) (ht _ hd) (ht _ hvV)
    rw [hζ1, map_one, one_mul] at hζ
    calc Sec4.diagTau hτ * y₂ = Sec4.diagTau hτ * y₂ * (Sec4.diagTau hτ)⁻¹ * Sec4.diagTau hτ := by
          group
      _ = y₂ * Sec4.diagTau hτ := by rw [hζ]
  ·
    have key := Sec4.transitive_of_heis_pair (G := ProjGenLinGroup (Fin 3) K)
      (L := projImage (Sec4.slPi π 3 (p ^ f) K)) hK hq (MulEquiv.refl _) (hVL hd) (hVL hvV)
      rfl rfl ⟨τ, hτ, hτ1, 1, one_mem _, 1, one_mem _, by simp⟩ hy₂S hζ1 hζ
    rw [hVeq] at key
    exact key

end CFSG.RankThree.PartTwo.Sec12
