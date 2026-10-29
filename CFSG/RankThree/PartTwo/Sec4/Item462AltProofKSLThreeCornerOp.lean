module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG.RankThree.PartTwo.Sec4

open Matrix

@[instance_reducible]
def cornerOpAct {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (N : Subgroup (slPi π 3 (p ^ f) K)) : MulAction N (Fin 3 → K) where
  smul g v := Matrix.mulVec ((((g : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) :
    Matrix (Fin 3) (Fin 3) K) v
  one_smul v := by simp
  mul_smul g h v := by
    change Matrix.mulVec ((((g * h : N) : slPi π 3 (p ^ f) K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) v = Matrix.mulVec
          ((((g : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)
          (Matrix.mulVec ((((h : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) :
            Matrix (Fin 3) (Fin 3) K) v)
    simp [Matrix.mulVec_mulVec]

def cornerOpFixed {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (N : Subgroup (slPi π 3 (p ^ f) K)) (v : Fin 3 → K) : Prop :=
  ∀ x ∈ N, Matrix.mulVec ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) v = v

theorem cornerOpFixed_add {π : Bool} {p f : ℕ} {K : Type} [Field K]
    {N : Subgroup (slPi π 3 (p ^ f) K)} {u v : Fin 3 → K}
    (hu : cornerOpFixed N u) (hv : cornerOpFixed N v) : cornerOpFixed N (u + v) := by
  intro x hx
  rw [Matrix.mulVec_add, hu x hx, hv x hx]

theorem cornerOpFixed_sub {π : Bool} {p f : ℕ} {K : Type} [Field K]
    {N : Subgroup (slPi π 3 (p ^ f) K)} {u v : Fin 3 → K}
    (hu : cornerOpFixed N u) (hv : cornerOpFixed N v) : cornerOpFixed N (u - v) := by
  intro x hx
  rw [Matrix.mulVec_sub, hu x hx, hv x hx]

theorem cornerOpFixed_smul {π : Bool} {p f : ℕ} {K : Type} [Field K]
    {N : Subgroup (slPi π 3 (p ^ f) K)} {u : Fin 3 → K} (c : K)
    (hu : cornerOpFixed N u) : cornerOpFixed N (c • u) := by
  intro x hx
  rw [Matrix.mulVec_smul, hu x hx]

theorem cornerOpFixed_of_eq_smul {π : Bool} {p f : ℕ} {K : Type} [Field K]
    {N : Subgroup (slPi π 3 (p ^ f) K)} {v w : Fin 3 → K} {c : K}
    (hv : cornerOpFixed N v) (hc : c ≠ 0) (h : v = c • w) : cornerOpFixed N w := by
  have hw : w = c⁻¹ • v := by rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hw]
  exact cornerOpFixed_smul c⁻¹ hv

theorem exists_cornerOpFixed_ne_zero {π : Bool} {p f : ℕ} {K : Type} [Field K] [Finite K]
    [Fact p.Prime] (hpK : p ∣ Nat.card K) (N : Subgroup (slPi π 3 (p ^ f) K))
    (hN : IsPGroup p N) : ∃ u : Fin 3 → K, u ≠ 0 ∧ cornerOpFixed N u := by
  letI : MulAction N (Fin 3 → K) := cornerOpAct N
  have hdvd : p ∣ Nat.card (Fin 3 → K) := by
    rw [Nat.card_fun]
    exact dvd_pow hpK (by simp [Nat.card_eq_fintype_card])
  have h0 : (0 : Fin 3 → K) ∈ MulAction.fixedPoints N (Fin 3 → K) := by
    rw [MulAction.mem_fixedPoints]
    intro m
    exact Matrix.mulVec_zero _
  obtain ⟨b, hb, hab⟩ :=
    hN.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 3 → K) hdvd h0
  refine ⟨b, fun hb0 => hab hb0.symm, ?_⟩
  intro x hx
  exact MulAction.mem_fixedPoints.1 hb ⟨x, hx⟩

theorem cornerOpFixed_mulVec {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (N : Subgroup (slPi π 3 (p ^ f) K)) [N.Normal] {g : GL (Fin 3) K}
    (hg : g ∈ slPi π 3 (p ^ f) K) {u : Fin 3 → K} (hu : cornerOpFixed N u) :
    cornerOpFixed N (Matrix.mulVec ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) u) := by
  obtain ⟨gS, rfl⟩ : ∃ gS : slPi π 3 (p ^ f) K, (gS : GL (Fin 3) K) = g := ⟨⟨g, hg⟩, rfl⟩
  intro x hx
  obtain ⟨y, hydef⟩ : ∃ y : slPi π 3 (p ^ f) K, y = gS⁻¹ * x * gS := ⟨_, rfl⟩
  have hy : y ∈ N := by
    rw [hydef]
    simpa using Subgroup.Normal.conj_mem ‹N.Normal› x hx gS⁻¹
  have hxg : x * gS = gS * y := by
    rw [hydef]
    group
  have hM' : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((gS : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((gS : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have hM := congrArg (fun z : slPi π 3 (p ^ f) K =>
      ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hxg
    simpa only [Subgroup.coe_mul, Units.val_mul] using hM
  rw [Matrix.mulVec_mulVec, hM', ← Matrix.mulVec_mulVec, hu y hy]

theorem cornerOp_combo {K : Type} [Field K] (τ a b : K) (u : Fin 3 → K) :
    Matrix.mulVec !![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1]
        (Matrix.mulVec !![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1] u)
      - (a + b) • Matrix.mulVec !![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1] u + (a * b) • u
      = ![(τ - a) * (τ - b) * u 0, (τ ^ 2 - a) * (τ ^ 2 - b) * u 1,
          (1 - a) * (1 - b) * u 2] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem cornerOp_facts {K : Type} [Field K] {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    τ - τ ^ 2 ≠ 0 ∧ τ ^ 2 - τ ≠ 0 ∧ τ ^ 2 - 1 ≠ 0 ∧ 1 - τ ≠ 0 ∧ 1 - τ ^ 2 ≠ 0 ∧
      τ - 1 ≠ 0 := by
  have h0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have h1 : 1 - τ ≠ 0 := sub_ne_zero.2 (Ne.symm hτ1)
  have h2 : τ - 1 ≠ 0 := sub_ne_zero.2 hτ1
  have h3 : τ ^ 2 - 1 ≠ 0 := by
    intro h
    apply hτ1
    linear_combination (-τ) * h + hτ
  have h4 : τ ^ 2 - τ ≠ 0 := by
    have e : τ ^ 2 - τ = τ * (τ - 1) := by ring
    rw [e]
    exact mul_ne_zero h0 h2
  have h5 : τ - τ ^ 2 ≠ 0 := by
    have e : τ - τ ^ 2 = τ * (1 - τ) := by ring
    rw [e]
    exact mul_ne_zero h0 h1
  have h6 : 1 - τ ^ 2 ≠ 0 := by
    intro h
    apply h3
    linear_combination -h
  exact ⟨h5, h4, h3, h1, h6, h2⟩

theorem cornerOp_basis {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (N : Subgroup (slPi π 3 (p ^ f) K)) [N.Normal] {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hD : (diagTau hτ : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K) {u : Fin 3 → K}
    (hu : cornerOpFixed N u) :
    (u 0 ≠ 0 → cornerOpFixed N (Pi.single 0 1)) ∧
      (u 1 ≠ 0 → cornerOpFixed N (Pi.single 1 1)) ∧
      (u 2 ≠ 0 → cornerOpFixed N (Pi.single 2 1)) := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := cornerOp_facts hτ hτ1
  have hDf : ∀ v, cornerOpFixed N v →
      cornerOpFixed N (Matrix.mulVec !![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1] v) := by
    intro v hv
    rw [← coe_diagTau hτ]
    exact cornerOpFixed_mulVec N hD hv
  have hDu := hDf u hu
  have hDDu := hDf _ hDu
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_⟩
  · have hv := cornerOpFixed_add
      (cornerOpFixed_sub hDDu (cornerOpFixed_smul (τ ^ 2 + 1) hDu))
      (cornerOpFixed_smul (τ ^ 2 * 1) hu)
    refine cornerOpFixed_of_eq_smul hv (mul_ne_zero (mul_ne_zero n1 n6) h0) ?_
    rw [cornerOp_combo]
    ext i
    fin_cases i <;> simp <;> ring
  · have hv := cornerOpFixed_add
      (cornerOpFixed_sub hDDu (cornerOpFixed_smul (τ + 1) hDu))
      (cornerOpFixed_smul (τ * 1) hu)
    refine cornerOpFixed_of_eq_smul hv (mul_ne_zero (mul_ne_zero n2 n3) h1) ?_
    rw [cornerOp_combo]
    ext i
    fin_cases i <;> simp <;> ring
  · have hv := cornerOpFixed_add
      (cornerOpFixed_sub hDDu (cornerOpFixed_smul (τ + τ ^ 2) hDu))
      (cornerOpFixed_smul (τ * τ ^ 2) hu)
    refine cornerOpFixed_of_eq_smul hv (mul_ne_zero (mul_ne_zero n4 n5) h2) ?_
    rw [cornerOp_combo]
    ext i
    fin_cases i <;> simp <;> ring

theorem cornerOp_cycle {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (N : Subgroup (slPi π 3 (p ^ f) K)) [N.Normal]
    (hc : (cycThree : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K) :
    (cornerOpFixed N (Pi.single 0 1) → cornerOpFixed N (Pi.single 1 1)) ∧
      (cornerOpFixed N (Pi.single 1 1) → cornerOpFixed N (Pi.single 2 1)) ∧
      (cornerOpFixed N (Pi.single 2 1) → cornerOpFixed N (Pi.single 0 1)) := by
  have hC : ∀ v, cornerOpFixed N v →
      cornerOpFixed N (Matrix.mulVec !![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0] v) := by
    intro v hv
    rw [← coe_cycThree]
    exact cornerOpFixed_mulVec N hc hv
  have e01 : Matrix.mulVec !![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0] (Pi.single 0 1)
      = Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.vecHead,
      Matrix.vecTail, Function.comp_apply, Pi.single_apply]
  have e12 : Matrix.mulVec !![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0] (Pi.single 1 1)
      = Pi.single 2 1 := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.vecHead,
      Matrix.vecTail, Function.comp_apply, Pi.single_apply]
  have e20 : Matrix.mulVec !![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0] (Pi.single 2 1)
      = Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.vecHead,
      Matrix.vecTail, Function.comp_apply, Pi.single_apply]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := hC _ h
    rwa [e01] at this
  · have := hC _ h
    rwa [e12] at this
  · have := hC _ h
    rwa [e20] at this

theorem cornerOp_eq_one {π : Bool} {p f : ℕ} {K : Type} [Field K]
    {N : Subgroup (slPi π 3 (p ^ f) K)}
    (hall : ∀ j : Fin 3, cornerOpFixed N (Pi.single j 1)) {x : slPi π 3 (p ^ f) K}
    (hx : x ∈ N) : x = 1 := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  have h1 : ((((1 : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    simp
  rw [h1, Matrix.one_mulVec]
  exact hall j x hx

theorem eq_bot_of_normal_isPGroup {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (N : Subgroup (slPi π 3 (p ^ f) K))
    [N.Normal] (hN : IsPGroup p N) : N = ⊥ := by
  haveI : Fact p.Prime := ⟨hK.prime⟩
  haveI : Finite K := hK.finite
  have hpK : p ∣ Nat.card K := by
    have hf : f ≠ 0 := by
      have := hK.one_le
      omega
    have hp1 : p ∣ p ^ f := dvd_pow_self p hf
    have key : ∀ b : Bool, p ∣ piCard b (p ^ f) := by
      intro b
      cases b
      · show p ∣ (p ^ f) ^ 2
        exact dvd_trans hp1 (dvd_pow_self (p ^ f) two_ne_zero)
      · exact hp1
    rw [hK.card]
    exact key π
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hπU : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K := fun h => by
    subst h
    exact hK.unitary
  have hqF : π = false → ModThree false (p ^ f) := fun h => by
    subst h
    exact hq
  have hD : (diagTau hτ : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K :=
    diagTau_mem_slPi hπU hqF hτ
  have hC : (cycThree : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K :=
    cycThree_mem_slPi hπU
  obtain ⟨u, hu0, hu⟩ := exists_cornerOpFixed_ne_zero hpK N hN
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (funext h)
  obtain ⟨b0, b1, b2⟩ := cornerOp_basis N hτ hτ1 hD hu
  obtain ⟨c01, c12, c20⟩ := cornerOp_cycle N hC
  have hall0 : cornerOpFixed N (Pi.single 0 1) ∧ cornerOpFixed N (Pi.single 1 1) ∧
      cornerOpFixed N (Pi.single 2 1) := by
    fin_cases i
    · have e0 := b0 hi
      exact ⟨e0, c01 e0, c12 (c01 e0)⟩
    · have e1 := b1 hi
      exact ⟨c20 (c12 e1), e1, c12 e1⟩
    · have e2 := b2 hi
      exact ⟨c20 e2, c01 (c20 e2), e2⟩
  have hall : ∀ j : Fin 3, cornerOpFixed N (Pi.single j 1) := by
    intro j
    fin_cases j
    · exact hall0.1
    · exact hall0.2.1
    · exact hall0.2.2
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  exact cornerOp_eq_one hall hx

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
