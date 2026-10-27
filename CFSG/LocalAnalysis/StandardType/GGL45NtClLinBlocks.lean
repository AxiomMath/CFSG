module

public import CFSG.LocalAnalysis.StandardType.GGL45NtClBlocks

public section

namespace CFSG.HardMathSupport.C14Cl

open Matrix CFSG.Open

structure LinSetting (K ι : Type) [Field K] [Fintype ι] [DecidableEq ι] where
  p : ℕ
  hp : p.Prime
  hp2 : p ≠ 2
  σ₀ : K ≃+* K
  hσ₀ : orderOf σ₀ = p
  E₀ : Subgroup (GL ι K)
  hE : IsElemAbelian p E₀
  hEfix : ∀ e ∈ E₀, (e : Matrix ι ι K).map σ₀ = e

namespace LinSetting


@[expose] def σ {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) : Matrix ι ι K ≃+* Matrix ι ι K := S.σ₀.mapMatrix

@[expose] def σGL {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) : GL ι K →* GL ι K := Units.map S.σ.toRingHom.toMonoidHom

abbrev A {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) : Submodule K (Matrix ι ι K) := spanE K S.E₀

def IsMinIdem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) (ε : Matrix ι ι K) : Prop :=
  ε ∈ S.A ∧ ε * ε = ε ∧ ε ≠ 0 ∧ ∀ δ ∈ S.A, δ * δ = δ → δ * ε = δ → δ = 0 ∨ δ = ε

theorem mem_A_of_mem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) {e : GL ι K} (he : e ∈ S.E₀) : (e : Matrix ι ι K) ∈ S.A :=
  Submodule.subset_span ⟨⟨e, he⟩, rfl⟩

theorem one_mem_A {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) : (1 : Matrix ι ι K) ∈ S.A := by
  simpa using S.mem_A_of_mem S.E₀.one_mem

theorem mul_mem_A {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) {M N : Matrix ι ι K} (hM : M ∈ S.A) (hN : N ∈ S.A) : M * N ∈ S.A :=
  spanE_mul_mem S.E₀ hM hN

theorem pow_mem_A {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) {M : Matrix ι ι K} (hM : M ∈ S.A) (n : ℕ) : M ^ n ∈ S.A := by
  induction n with
  | zero => rw [pow_zero]; exact S.one_mem_A
  | succ n ih => rw [pow_succ]; exact S.mul_mem_A ih hM

theorem comm_A {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) {M N : Matrix ι ι K} (hM : M ∈ S.A) (hN : N ∈ S.A) : M * N = N * M :=
  spanE_commute S.E₀ S.hE.1 hM hN

theorem cent_inv {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) {y : GL ι K} (hy : ∀ e ∈ S.E₀, y * e = e * y) :
    ∀ e ∈ S.E₀, y⁻¹ * e = e * y⁻¹ := by
  intro e he
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hy e he, mul_assoc, mul_inv_cancel, mul_one]

theorem comm_of_cent {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) {y : GL ι K} (hy : ∀ e ∈ S.E₀, y * e = e * y) {M : Matrix ι ι K}
    (hM : M ∈ S.A) : (y : Matrix ι ι K) * M = M * y :=
  commute_of_mem_spanE S.E₀ (fun e he => by
    have := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) (hy e he); simpa using this) hM

theorem sigma_apply {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) (M : Matrix ι ι K) : S.σ M = M.map S.σ₀ := rfl

theorem sigma_mem_A {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) {M : Matrix ι ι K} (hM : M ∈ S.A) : S.σ M ∈ S.A := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨e, he⟩, rfl⟩ := hx
    have : S.σ (e : Matrix ι ι K) = e := S.hEfix e he
    simp only
    rw [this]; exact S.mem_A_of_mem he
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have : S.σ (c • x) = S.σ₀ c • S.σ x := by
      ext i j; simp [σ, RingEquiv.mapMatrix_apply, Matrix.map_apply]
    rw [this]; exact Submodule.smul_mem _ _ hx


theorem sigma_idempotent {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) [Fintype K] [CharP K 2] {ε : Matrix ι ι K} (hε : ε ∈ S.A) (hεε : ε * ε = ε) : S.σ ε = ε := by
  obtain ⟨a, ha⟩ := exists_pow_two_of_ringEquiv S.σ₀
  haveI := Fact.mk S.hp
  have hiter : ∀ k (c : K), (S.σ₀ ^ k) c = c ^ 2 ^ (a * k) := by
    intro k
    induction k with
    | zero => intro c; simp
    | succ k ih =>
      intro c
      rw [pow_succ']
      change S.σ₀ ((S.σ₀ ^ k) c) = _
      rw [ih, map_pow, ha, ← pow_mul, ← pow_add, Nat.mul_succ, add_comm]
  have hm : ∀ c : K, c ^ 2 ^ (a * S.p) = c := by
    intro c; rw [← hiter, ← S.hσ₀, pow_orderOf_eq_one]; rfl
  have hmod : 2 ^ (a * S.p) ≡ 2 ^ a [MOD S.p] := by
    rw [← ZMod.natCast_eq_natCast_iff, pow_mul, Nat.cast_pow, ZMod.pow_card]
  have h := semilinear_pow_eq S.E₀ S.hE.1 S.hE.2 S.σ S.σ₀
    (fun c M => by ext i j; simp [σ, RingEquiv.mapMatrix_apply, Matrix.map_apply])
    (fun e he => S.hEfix e he) ha hm hmod ε hε
  have hid : ∀ n : ℕ, 0 < n → ∀ x : Matrix ι ι K, x * x = x → x ^ n = x := by
    intro n hn x hx
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn'
      · simp
      · rw [pow_succ, ih hn', hx]
  have hσε : S.σ ε * S.σ ε = S.σ ε := by rw [← map_mul, hεε]
  rw [hid _ (by positivity) _ hσε, hid _ (by positivity) _ hεε] at h
  exact h

theorem exists_frob_exp {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) [Fintype K] [CharP K 2] : ∃ Q : ℕ, 2 ≤ Q ∧ (∀ M ∈ S.A, M ^ Q = M) ∧ S.p ∣ Q - 1 := by
  haveI := Fact.mk S.hp
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have h2 : ¬ S.p ∣ 2 := fun h => S.hp2 ((Nat.prime_dvd_prime_iff_eq S.hp Nat.prime_two).1 h)
  have h2' : (2 : ZMod S.p) ≠ 0 := by
    have : ((2 : ℕ) : ZMod S.p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact h2
    simpa using this
  have hp3 : 3 ≤ S.p := by have := S.hp.two_le; have := S.hp2; omega
  have hm : ∀ c : K, c ^ 2 ^ ((S.p - 1) * n) = c := by
    intro c; rw [mul_comm, pow_mul, ← hn]; exact FiniteField.pow_card_pow _ c
  have hmod : 2 ^ ((S.p - 1) * n) ≡ 1 [MOD S.p] := by
    rw [← ZMod.natCast_eq_natCast_iff]; push_cast
    rw [pow_mul, ZMod.pow_card_sub_one_eq_one h2', one_pow]
  have hb : 1 ≤ (S.p - 1) * n := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) n.ne_zero)
  refine ⟨2 ^ ((S.p - 1) * n), ?_, pow_eq_self_of_mem_spanE S.E₀ S.hE.1 S.hE.2 hm hmod,
    (Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 hmod.symm⟩
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ ((S.p - 1) * n) := Nat.pow_le_pow_right (by norm_num) hb

theorem minIdem_inv {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) [Fintype K] [CharP K 2] {ε : Matrix ι ι K} (hε : S.IsMinIdem ε)
    {a : Matrix ι ι K} (ha : a ∈ S.A) (h0 : a * ε ≠ 0) : ∃ a' ∈ S.A, a' * (a * ε) = ε := by
  obtain ⟨hεA, hεε, -, hmin⟩ := hε
  obtain ⟨Q, hQ2, hQA, -⟩ := S.exists_frob_exp
  set x := a * ε with hx
  have hxA : x ∈ S.A := S.mul_mem_A ha hεA
  have hxQ : x ^ Q = x := hQA x hxA
  have hxε : x * ε = x := by rw [hx, mul_assoc, hεε]
  set e := x ^ (Q - 1) with he
  have hee : e * e = e := by
    rw [he, ← pow_add, show Q - 1 + (Q - 1) = Q + (Q - 2) by omega, pow_add, hxQ, ← pow_succ',
      show Q - 2 + 1 = Q - 1 by omega]
  have heε : e * ε = e := by
    rw [he, show Q - 1 = Q - 2 + 1 by omega, pow_succ, mul_assoc, hxε]
  rcases hmin e (S.pow_mem_A hxA _) hee heε with h | h
  · exfalso; apply h0
    rw [← hxQ, show Q = Q - 1 + 1 by omega, pow_succ, ← he, h, zero_mul]
  · refine ⟨x ^ (Q - 2), S.pow_mem_A hxA _, ?_⟩
    rw [← pow_succ, show Q - 2 + 1 = Q - 1 by omega, ← he, h]

theorem mul_mem_A_of_cyclic {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) [Fintype K] [CharP K 2] {ε' c : Matrix ι ι K} (hε'A : ε' ∈ S.A) (hε' : ε' * ε' = ε')
    (hc : ∀ e ∈ S.E₀, c * (e : Matrix ι ι K) = e * c) {v : ι → K} (hv : ε' *ᵥ v = v)
    (hcyc : ∀ x, ε' *ᵥ x = x → ∃ a ∈ S.A, x = a *ᵥ v) : c * ε' ∈ S.A := by
  have hcA : ∀ M ∈ S.A, c * M = M * c := fun M hM => commute_of_mem_spanE S.E₀ hc hM
  obtain ⟨a₀, ha₀A, ha₀⟩ := hcyc ((c * ε') *ᵥ v) (by
    rw [Matrix.mulVec_mulVec, ← mul_assoc, ← hcA ε' hε'A, mul_assoc, hε'])
  have heq : c * ε' = a₀ * ε' := by
    refine Matrix.ext_iff_mulVec.2 fun x => ?_
    obtain ⟨a, haA, hax⟩ := hcyc (ε' *ᵥ x) (by rw [Matrix.mulVec_mulVec, hε'])
    calc (c * ε') *ᵥ x = (c * ε') *ᵥ (ε' *ᵥ x) := by rw [Matrix.mulVec_mulVec, mul_assoc, hε']
      _ = (c * ε') *ᵥ (a *ᵥ v) := by rw [← hax]
      _ = a *ᵥ ((c * ε') *ᵥ v) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
          congr 1
          rw [mul_assoc, S.comm_A hε'A haA, ← mul_assoc, hcA a haA, mul_assoc]
      _ = a *ᵥ (a₀ *ᵥ v) := by rw [← ha₀]
      _ = a₀ *ᵥ (a *ᵥ v) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, S.comm_A haA ha₀A]
      _ = (a₀ * ε') *ᵥ x := by rw [← hax, Matrix.mulVec_mulVec]
  rw [heq]; exact S.mul_mem_A ha₀A hε'A

theorem map_pow_of_sigma {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) [Fintype K] [CharP K 2] {M : Matrix ι ι K} (hM : S.σ M = M) (i : ℕ) :
    M.map ⇑(S.σ₀ ^ i) = M := by
  induction i with
  | zero => ext a b; rfl
  | succ i ih =>
    ext a b
    have h1 := congrFun (congrFun ih a) b
    have h2 := congrFun (congrFun hM a) b
    rw [S.sigma_apply, Matrix.map_apply] at h2
    simp only [Matrix.map_apply] at h1 ⊢
    rw [pow_succ']
    change S.σ₀ ((S.σ₀ ^ i) (M a b)) = M a b
    rw [h1]; exact h2

theorem vec_descent {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) [Fintype K] [CharP K 2] {ε' : Matrix ι ι K} (hσ : S.σ ε' = ε') {x : ι → K}
    (hx : ε' *ᵥ x = x) :
    ∃ (c : K → K) (T : K → ι → K), (∀ l, S.σ₀ ∘ T l = T l ∧ ε' *ᵥ T l = T l) ∧
      x = ∑ l, c l • T l := by
  obtain ⟨c, hc⟩ := exists_trace_coeffs S.σ₀
  let T : K → ι → K := fun l => ∑ i ∈ Finset.range (orderOf S.σ₀), (S.σ₀ ^ i) ∘ (l • x)
  have hTa : ∀ l a, T l a = ∑ i ∈ Finset.range (orderOf S.σ₀), (S.σ₀ ^ i) (l * x a) := by
    intro l a; simp [T, Finset.sum_apply]
  refine ⟨c, T, fun l => ⟨?_, ?_⟩, ?_⟩
  · funext a
    simp only [Function.comp_apply]
    rw [hTa]; exact trace_fixed S.σ₀ _
  · simp only [T, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := ClSetting.comp_mulVec (S.σ₀ ^ i) ε' (l • x)
    rw [S.map_pow_of_sigma hσ, Matrix.mulVec_smul, hx] at this
    exact this.symm
  · funext a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hTa]
    exact trace_descent_scalar S.σ₀ c hc (x a)

theorem exists_fixed_vec {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) [Fintype K] [CharP K 2] {ε : Matrix ι ι K} (hεA : ε ∈ S.A) (hεε : ε * ε = ε) (hε0 : ε ≠ 0) :
    ∃ u : ι → K, S.σ₀ ∘ u = u ∧ ε *ᵥ u = u ∧ u ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, ε *ᵥ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hε0 (Matrix.ext_iff_mulVec.2 fun x => by rw [h x, Matrix.zero_mulVec])
  obtain ⟨c, T, hT, hsum⟩ := S.vec_descent (S.sigma_idempotent hεA hεε)
    (x := ε *ᵥ x) (by rw [Matrix.mulVec_mulVec, hεε])
  by_contra h
  push Not at h
  apply hx
  rw [hsum]
  exact Finset.sum_eq_zero fun l _ => by
    rw [h (T l) (hT l).1 (hT l).2, smul_zero]

def IsProj {K : Type} [Field K] {ι : Type} [Fintype ι] (W : Submodule K (ι → K)) (P : Matrix ι ι K) : Prop :=
  (∀ w ∈ W, P *ᵥ w = w) ∧ ∀ v, P *ᵥ v ∈ W

theorem isProj_idem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {W : Submodule K (ι → K)} {P : Matrix ι ι K} (h : IsProj W P) :
    P * P = P :=
  Matrix.ext_iff_mulVec.2 fun v => by rw [← Matrix.mulVec_mulVec, h.1 _ (h.2 v)]

theorem finsum_mulVec {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type*} (s : Finset α) (M : α → Matrix ι ι K) (v : ι → K) :
    (∑ i ∈ s, M i) *ᵥ v = ∑ i ∈ s, M i *ᵥ v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ih]

theorem isProj_sum {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type*} {W : Submodule K (ι → K)} (s : Finset α) (c : α → K)
    (P : α → Matrix ι ι K) (hP : ∀ i ∈ s, IsProj W (P i)) (hc : ∑ i ∈ s, c i = 1) :
    IsProj W (∑ i ∈ s, c i • P i) := by
  refine ⟨fun w hw => ?_, fun v => ?_⟩
  · rw [finsum_mulVec, Finset.sum_congr rfl fun i hi => by
      rw [Matrix.smul_mulVec, (hP i hi).1 w hw], ← Finset.sum_smul, hc, one_smul]
  · rw [finsum_mulVec]
    exact Submodule.sum_mem _ fun i hi => by
      rw [Matrix.smul_mulVec]; exact W.smul_mem _ ((hP i hi).2 v)

theorem isProj_conj {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {W : Submodule K (ι → K)} {P : Matrix ι ι K} (h : IsProj W P) (g : GL ι K)
    (hg : ∀ w ∈ W, (g : Matrix ι ι K) *ᵥ w ∈ W)
    (hg' : ∀ w ∈ W, ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w ∈ W) :
    IsProj W ((g : Matrix ι ι K) * P * ((g⁻¹ : GL ι K) : Matrix ι ι K)) := by
  refine ⟨fun w hw => ?_, fun v => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h.1 _ (hg' w hw), Matrix.mulVec_mulVec,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hg _ (h.2 _)

theorem sigma_pow_mem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) {W : Submodule K (ι → K)} (hWσ : ∀ w ∈ W, S.σ₀ ∘ w ∈ W) :
    ∀ (k : ℕ), ∀ w ∈ W, ⇑(S.σ₀ ^ k) ∘ w ∈ W := by
  intro k
  induction k with
  | zero => intro w hw; exact hw
  | succ k ih =>
    intro w hw
    have : ⇑(S.σ₀ ^ (k + 1)) ∘ w = S.σ₀ ∘ (⇑(S.σ₀ ^ k) ∘ w) := by
      funext a; rw [pow_succ']; rfl
    rw [this]; exact hWσ _ (ih w hw)

theorem sigma_surj {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) (w : ι → K) :
    S.σ₀ ∘ (⇑(S.σ₀ ^ (S.p - 1)) ∘ w) = w := by
  have hσp : S.σ₀ ^ S.p = 1 := S.hσ₀ ▸ pow_orderOf_eq_one S.σ₀
  have h1 : 1 ≤ S.p := S.hp.one_lt.le
  funext a
  change (S.σ₀ * S.σ₀ ^ (S.p - 1)) (w a) = w a
  rw [← pow_succ', Nat.sub_add_cancel h1, hσp]; rfl

theorem isProj_sigma {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) [Fintype K] [CharP K 2] {W : Submodule K (ι → K)} (hWσ : ∀ w ∈ W, S.σ₀ ∘ w ∈ W)
    {P : Matrix ι ι K} (h : IsProj W P) : IsProj W (S.σ P) := by
  refine ⟨fun w hw => ?_, fun v => ?_⟩
  · have hw' := S.sigma_pow_mem hWσ (S.p - 1) w hw
    rw [← S.sigma_surj w, S.sigma_apply, ← ClSetting.comp_mulVec, h.1 _ hw']
  · rw [← S.sigma_surj v, S.sigma_apply, ← ClSetting.comp_mulVec]
    exact hWσ _ (h.2 _)

theorem exists_fixed_idem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) [Fintype K] [CharP K 2] {ε : Matrix ι ι K} (hε : S.IsMinIdem ε)
    (hC : ∃ c : Matrix ι ι K, (∀ e ∈ S.E₀, c * (e : Matrix ι ι K) = e * c) ∧ c * ε ∉ S.A) :
    ∃ f : Matrix ι ι K, (∀ e ∈ S.E₀, f * (e : Matrix ι ι K) = e * f) ∧ f * f = f ∧
      S.σ f = f ∧ f * ε = f ∧ f ∉ S.A := by
  classical
  obtain ⟨hεA, hεε, hε0, hmin⟩ := hε
  obtain ⟨u, huσ, huε, hu0⟩ := S.exists_fixed_vec hεA hεε hε0
  let app : Matrix ι ι K →ₗ[K] (ι → K) :=
    { toFun := fun M => M *ᵥ u
      map_add' := fun M N => Matrix.add_mulVec M N u
      map_smul' := fun c M => Matrix.smul_mulVec c M u }
  set W : Submodule K (ι → K) := S.A.map app with hW
  have hmemW : ∀ w, w ∈ W ↔ ∃ a ∈ S.A, a *ᵥ u = w := fun w => Submodule.mem_map
  have hWA : ∀ a ∈ S.A, ∀ w ∈ W, a *ᵥ w ∈ W := by
    intro a ha w hw
    obtain ⟨b, hb, rfl⟩ := (hmemW w).1 hw
    exact (hmemW _).2 ⟨a * b, S.mul_mem_A ha hb, by rw [Matrix.mulVec_mulVec]⟩
  have hWσ : ∀ w ∈ W, S.σ₀ ∘ w ∈ W := by
    intro w hw
    obtain ⟨b, hb, rfl⟩ := (hmemW w).1 hw
    exact (hmemW _).2 ⟨S.σ b, S.sigma_mem_A hb, by
      rw [ClSetting.comp_mulVec, huσ]; rfl⟩
  have huW : u ∈ W := (hmemW u).2 ⟨1, S.one_mem_A, Matrix.one_mulVec u⟩
  obtain ⟨Cc, hCc⟩ := Submodule.exists_isCompl W
  let π := Submodule.linearProjOfIsCompl W Cc hCc
  set P₀ : Matrix ι ι K := LinearMap.toMatrix' (W.subtype ∘ₗ π) with hP₀def
  have hP₀ : IsProj W P₀ := by
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · rw [hP₀def, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply]
      exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hCc ⟨w, hw⟩)
    · rw [hP₀def, LinearMap.toMatrix'_mulVec]
      exact (π v).2
  haveI : Finite (GL ι K) :=
    Finite.of_injective (fun u : GL ι K => (u : Matrix ι ι K)) fun _ _ h => Units.ext h
  haveI : Fintype S.E₀ := Fintype.ofFinite _
  set N := Fintype.card S.E₀ with hNdef
  have hN : (N : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := S.E₀) 2 h2
    have hxp : x ^ S.p = 1 := Subtype.ext (S.hE.2 x x.2)
    have := orderOf_dvd_of_pow_eq_one hxp
    rw [hx] at this
    exact S.hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two S.hp).1 this).symm
  let Pc : S.E₀ → Matrix ι ι K := fun e =>
    ((e : GL ι K) : Matrix ι ι K) * P₀ * (((e : GL ι K)⁻¹ : GL ι K) : Matrix ι ι K)
  set P₁ : Matrix ι ι K := ∑ e : S.E₀, (N : K)⁻¹ • Pc e with hP₁def
  have hP₁ : IsProj W P₁ := by
    refine isProj_sum _ _ _ (fun e _ => isProj_conj hP₀ _ (fun w hw => hWA _
      (S.mem_A_of_mem e.2) w hw) (fun w hw => hWA _ (S.mem_A_of_mem (S.E₀.inv_mem e.2)) w hw)) ?_
    rw [Finset.sum_const, Finset.card_univ, ← hNdef, nsmul_eq_mul, mul_inv_cancel₀ hN]
  have hP₁c : ∀ g ∈ S.E₀, P₁ * (g : Matrix ι ι K) = g * P₁ := by
    intro g hg
    rw [hP₁def, Finset.mul_sum, Finset.sum_mul]
    refine (Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : S.E₀)) _ _ fun e => ?_).symm
    simp only [Pc, Equiv.coe_mulLeft, Subgroup.coe_mul, _root_.mul_inv_rev, Units.val_mul, smul_mul_assoc,
      mul_smul_comm, mul_assoc, Units.inv_mul, mul_one]
  have hσp : S.σ₀ ^ S.p = 1 := S.hσ₀ ▸ pow_orderOf_eq_one S.σ₀
  have hp0 : (S.p : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    intro h2
    exact S.hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two S.hp).1 h2).symm
  let Pi : ℕ → Matrix ι ι K := fun i => P₁.map ⇑(S.σ₀ ^ i)
  have hPi_succ : ∀ i, Pi (i + 1) = S.σ (Pi i) := by
    intro i; ext a b
    simp only [Pi, S.sigma_apply, Matrix.map_apply]
    rw [pow_succ']; rfl
  have hPi : ∀ i, IsProj W (Pi i) := by
    intro i
    induction i with
    | zero => simpa [Pi] using hP₁
    | succ i ih => rw [hPi_succ]; exact S.isProj_sigma hWσ ih
  have hPic : ∀ i, ∀ g ∈ S.E₀, Pi i * (g : Matrix ι ι K) = g * Pi i := by
    intro i g hg
    have hgi : (g : Matrix ι ι K).map ⇑(S.σ₀ ^ i) = g := S.map_pow_of_sigma (S.hEfix g hg) i
    have h1 := congrArg ((S.σ₀ ^ i).mapMatrix) (hP₁c g hg)
    rw [map_mul, map_mul] at h1
    simp only [RingEquiv.mapMatrix_apply] at h1
    rw [hgi] at h1
    exact h1
  set P₂ : Matrix ι ι K := ∑ i ∈ Finset.range S.p, (S.p : K)⁻¹ • Pi i with hP₂def
  have hP₂ : IsProj W P₂ := by
    refine isProj_sum _ _ _ (fun i _ => hPi i) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_inv_cancel₀ hp0]
  have hP₂c : ∀ g ∈ S.E₀, P₂ * (g : Matrix ι ι K) = g * P₂ := by
    intro g hg
    rw [hP₂def, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_mul_assoc, mul_smul_comm, hPic i g hg]
  have hP₂σ : S.σ P₂ = P₂ := by
    have hc : S.σ₀ ((S.p : K)⁻¹) = (S.p : K)⁻¹ := by rw [map_inv₀, map_natCast]
    have hsm : ∀ (c : K) (M : Matrix ι ι K), S.σ (c • M) = S.σ₀ c • S.σ M := by
      intro c M; ext i j; simp [σ, RingEquiv.mapMatrix_apply, Matrix.map_apply]
    rw [hP₂def, map_sum]
    simp_rw [hsm, hc, ← hPi_succ]
    have e1 := Finset.sum_range_succ' (fun i => (S.p : K)⁻¹ • Pi i) S.p
    have e2 := Finset.sum_range_succ (fun i => (S.p : K)⁻¹ • Pi i) S.p
    have hPp : Pi S.p = Pi 0 := by
      simp only [Pi, hσp, pow_zero]
    rw [hPp] at e2
    exact add_right_cancel (e1.symm.trans e2)
  have hP₂ε : P₂ * ε = ε * P₂ := commute_of_mem_spanE S.E₀ hP₂c hεA
  have hP₂P₂ := isProj_idem hP₂
  refine ⟨P₂ * ε, fun e he => ?_, ?_, ?_, by rw [mul_assoc, hεε], fun hf => ?_⟩
  · rw [mul_assoc, S.comm_A hεA (S.mem_A_of_mem he), ← mul_assoc, hP₂c e he, mul_assoc]
  · rw [mul_assoc, ← mul_assoc ε, ← hP₂ε, mul_assoc, hεε, ← mul_assoc, hP₂P₂]
  · rw [map_mul, hP₂σ, S.sigma_idempotent hεA hεε]
  · have hfu : (P₂ * ε) *ᵥ u = u := by rw [← Matrix.mulVec_mulVec, huε, hP₂.1 u huW]
    have hff : P₂ * ε * (P₂ * ε) = P₂ * ε := by
      rw [mul_assoc, ← mul_assoc ε, ← hP₂ε, mul_assoc, hεε, ← mul_assoc, hP₂P₂]
    rcases hmin _ hf hff (by rw [mul_assoc, hεε]) with h0 | hfε
    · apply hu0; rw [← hfu, h0, Matrix.zero_mulVec]
    · obtain ⟨c, hc, hcε⟩ := hC
      apply hcε
      refine S.mul_mem_A_of_cyclic hεA hεε hc huε fun x hx => ?_
      have hxW : x ∈ W := by
        rw [← hx, ← hfε, ← Matrix.mulVec_mulVec]
        exact hP₂.2 _
      obtain ⟨a, ha, hax⟩ := (hmemW x).1 hxW
      exact ⟨a, ha, hax.symm⟩

theorem exists_inv_sub_one {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) [Fintype K] [CharP K 2] {ε : Matrix ι ι K} (hε : S.IsMinIdem ε) {t : GL ι K}
    (htA : (t : Matrix ι ι K) ∈ S.A) (ht1 : t ≠ 1) (hts : SuppOn ε t) :
    ∃ w ∈ S.A, w * (((t : Matrix ι ι K) - 1) * ε) = ε := by
  refine S.minIdem_inv hε (Submodule.sub_mem _ htA S.one_mem_A) fun h0 => ht1 (Units.ext ?_)
  have hts' : (t : Matrix ι ι K) * (1 - ε) = 1 - ε := hts
  have h1 : (t : Matrix ι ι K) * ε = ε := by rw [sub_mul, one_mul, sub_eq_zero] at h0; exact h0
  calc (t : Matrix ι ι K) = t * ε + t * (1 - ε) := by noncomm_ring
    _ = 1 := by rw [h1, hts']; noncomm_ring

theorem exists_orderP_not_mem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) [Fintype K] [CharP K 2] {ε : Matrix ι ι K} (hε : S.IsMinIdem ε) {t : GL ι K}
    (htA : (t : Matrix ι ι K) ∈ S.A) (htp : t ^ S.p = 1) (ht1 : t ≠ 1)
    (hts : SuppOn ε t) (htσ : S.σGL t = t) {f : Matrix ι ι K}
    (hfc : ∀ e ∈ S.E₀, f * (e : Matrix ι ι K) = e * f) (hff : f * f = f)
    (hfσ : S.σ f = f) (hfε : f * ε = f) (hfA : f ∉ S.A) :
    ∃ t' : GL ι K, (∀ e ∈ S.E₀, t' * e = e * t') ∧ t' ^ S.p = 1 ∧
      S.σGL t' = t' ∧ SuppOn ε t' ∧ (t' : Matrix ι ι K) ∉ S.A := by
  have hεA := hε.1
  obtain ⟨w, hwA, hw⟩ := S.exists_inv_sub_one hε htA ht1 hts
  have htf : (t : Matrix ι ι K) * f = f * t := (commute_of_mem_spanE S.E₀ hfc htA).symm
  have htinv : t⁻¹ = t ^ (S.p - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel S.hp.one_lt.le, htp]
  have htif : ((t⁻¹ : GL ι K) : Matrix ι ι K) * f = f * ((t⁻¹ : GL ι K) : Matrix ι ι K) := by
    have hmem : ((t⁻¹ : GL ι K) : Matrix ι ι K) ∈ S.A := by
      rw [htinv, Units.val_pow_eq_pow_val]; exact S.pow_mem_A htA _
    exact (commute_of_mem_spanE S.E₀ hfc hmem).symm
  let t' : GL ι K := ⟨t * f + (1 - f), ((t⁻¹ : GL ι K) : Matrix ι ι K) * f + (1 - f),
    by rw [block_mul hff htif, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul,
      add_sub_cancel],
    by rw [block_mul hff htf, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul,
      add_sub_cancel]⟩
  have hεf : ε * f = f := by rw [← commute_of_mem_spanE S.E₀ hfc hεA, hfε]
  refine ⟨t', fun e he => ?_, ?_, ?_, ?_, fun h => hfA ?_⟩
  · have hte : (t : Matrix ι ι K) * e = e * t := S.comm_A htA (S.mem_A_of_mem he)
    exact Units.ext (block_comm hte (hfc e he))
  · refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val]
    show ((t : Matrix ι ι K) * f + (1 - f)) ^ S.p = ((1 : GL ι K) : Matrix ι ι K)
    rw [block_pow hff htf, ← Units.val_pow_eq_pow_val, htp, Units.val_one, one_mul,
      add_sub_cancel]
  · refine Units.ext ?_
    show S.σ ((t : Matrix ι ι K) * f + (1 - f)) = (t : Matrix ι ι K) * f + (1 - f)
    rw [map_add, map_sub, map_mul, map_one,
      show S.σ (t : Matrix ι ι K) = t from congrArg Units.val htσ, hfσ]
  · show ((t : Matrix ι ι K) * f + (1 - f)) * (1 - ε) = 1 - ε
    calc ((t : Matrix ι ι K) * f + (1 - f)) * (1 - ε)
        = (t : Matrix ι ι K) * (f - f * ε) + (1 - ε - (f - f * ε)) := by noncomm_ring
      _ = 1 - ε := by rw [hfε, sub_self, mul_zero, zero_add, sub_zero]
  · have h1 : f = w * ((t : Matrix ι ι K) * f + (1 - f) - 1) := by
      calc f = ε * f := hεf.symm
        _ = w * (((t : Matrix ι ι K) - 1) * ε) * f := by rw [hw]
        _ = w * (((t : Matrix ι ι K) - 1) * (ε * f)) := by noncomm_ring
        _ = w * ((t : Matrix ι ι K) * f + (1 - f) - 1) := by rw [hεf]; noncomm_ring
    rw [h1]; exact S.mul_mem_A hwA (Submodule.sub_mem _ h S.one_mem_A)

def suppGroup {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) (ε : Matrix ι ι K) : Subgroup (GL ι K) where
  carrier := {g | (∀ e ∈ S.E₀, g * e = e * g) ∧ SuppOn ε g}
  one_mem' := ⟨fun e _ => by simp, by simp [SuppOn]⟩
  mul_mem' := by
    rintro g h ⟨hgc, hgs⟩ ⟨hhc, hhs⟩
    refine ⟨fun e he => ?_, ?_⟩
    · rw [mul_assoc, hhc e he, ← mul_assoc, hgc e he, mul_assoc]
    · unfold SuppOn at *; rw [Units.val_mul, mul_assoc, hhs, hgs]
  inv_mem' := by
    rintro g ⟨hgc, hgs⟩
    refine ⟨S.cent_inv hgc, ?_⟩
    unfold SuppOn at *
    calc ((g⁻¹ : GL ι K) : Matrix ι ι K) * (1 - ε)
        = ((g⁻¹ : GL ι K) : Matrix ι ι K) * ((g : Matrix ι ι K) * (1 - ε)) := by rw [hgs]
      _ = 1 - ε := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem sigma_mem_supp {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) [Fintype K] [CharP K 2] {ε : Matrix ι ι K} (hεA : ε ∈ S.A) (hεε : ε * ε = ε) {g : GL ι K}
    (hg : g ∈ S.suppGroup ε) : S.σGL g ∈ S.suppGroup ε := by
  obtain ⟨hgc, hgs⟩ := hg
  have hgs' : (g : Matrix ι ι K) * (1 - ε) = 1 - ε := hgs
  have hσε : S.σ (1 - ε) = 1 - ε := by rw [map_sub, map_one, S.sigma_idempotent hεA hεε]
  refine ⟨fun e he => ?_, ?_⟩
  · have hσe : S.σGL e = e := Units.ext (S.hEfix e he)
    calc S.σGL g * e = S.σGL g * S.σGL e := by rw [hσe]
      _ = S.σGL (g * e) := (map_mul _ _ _).symm
      _ = S.σGL (e * g) := by rw [hgc e he]
      _ = e * S.σGL g := by rw [map_mul, hσe]
  · show S.σ (g : Matrix ι ι K) * (1 - ε) = 1 - ε
    calc S.σ (g : Matrix ι ι K) * (1 - ε) = S.σ (g : Matrix ι ι K) * S.σ (1 - ε) := by rw [hσε]
      _ = S.σ ((g : Matrix ι ι K) * (1 - ε)) := (map_mul _ _ _).symm
      _ = 1 - ε := by rw [hgs', hσε]

def SatL {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) : Prop :=
  ∀ y : GL ι K, (∀ e ∈ S.E₀, y * e = e * y) → y ^ S.p = 1 → S.σGL y = y →
    (y : Matrix ι ι K) ∈ S.A

theorem pElt_mem_A_of_minIdem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) [Fintype K] [CharP K 2] (hSat : S.SatL) {ε : Matrix ι ι K} (hε : S.IsMinIdem ε)
    {z : GL ι K} (hz : ∀ e ∈ S.E₀, z * e = e * z) (hzs : SuppOn ε z)
    (hzp : ∃ k : ℕ, z ^ S.p ^ k = 1) : (z : Matrix ι ι K) ∈ S.A := by
  have hzs' : (z : Matrix ι ι K) * (1 - ε) = 1 - ε := hzs
  have hεA := hε.1
  have hεε := hε.2.1
  by_cases hC : ∃ c : Matrix ι ι K, (∀ e ∈ S.E₀, c * (e : Matrix ι ι K) = e * c) ∧ c * ε ∉ S.A
  swap
  · push Not at hC
    have hzc : ∀ e ∈ S.E₀, (z : Matrix ι ι K) * (e : Matrix ι ι K) = e * z := fun e he => by
      have := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) (hz e he); simpa using this
    have hzeq : (z : Matrix ι ι K) = z * ε + (1 - ε) := by rw [← hzs']; noncomm_ring
    rw [hzeq]; exact Submodule.add_mem _ (hC _ hzc) (Submodule.sub_mem _ S.one_mem_A hεA)
  by_contra hzA
  haveI : Finite (GL ι K) :=
    Finite.of_injective (fun u : GL ι K => (u : Matrix ι ι K)) fun _ _ h => Units.ext h
  set X := S.suppGroup ε
  let φ : X →* X :=
    { toFun := fun x => ⟨S.σGL (x : GL ι K), S.sigma_mem_supp hεA hεε x.2⟩
      map_one' := Subtype.ext (map_one S.σGL)
      map_mul' := fun x y => Subtype.ext (map_mul S.σGL (x : GL ι K) y) }
  have hφ : Function.Injective φ := fun x y h => Subtype.ext (Units.ext (S.σ.injective
    (congrArg (fun g : X => ((g : GL ι K) : Matrix ι ι K)) h)))
  let α : MulAut X := MulEquiv.ofBijective φ (Finite.injective_iff_bijective.1 hφ)
  have hαn : ∀ (n : ℕ) (x : X), (((α ^ n) x : GL ι K) : Matrix ι ι K) =
      ((x : GL ι K) : Matrix ι ι K).map ⇑(S.σ₀ ^ n) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply]
      change S.σ (((α ^ n) x : GL ι K) : Matrix ι ι K) = _
      rw [ih]
      ext i j
      change S.σ₀ ((S.σ₀ ^ n) _) = (S.σ₀ ^ (n + 1)) _
      rw [pow_succ']; rfl
  have hσp : S.σ₀ ^ S.p = 1 := S.hσ₀ ▸ pow_orderOf_eq_one S.σ₀
  have hαp : α ^ S.p = 1 := by
    ext x
    rw [hαn, hσp]; rfl
  have hzX : z ∈ X := ⟨hz, hzs⟩
  have hpX : S.p ∣ Nat.card X := by
    obtain ⟨k, hk⟩ := hzp
    have hdvd : orderOf (⟨z, hzX⟩ : X) ∣ S.p ^ k := by
      rw [← Subgroup.orderOf_coe]; exact orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow S.hp).1 hdvd
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      apply hzA
      rw [show z = 1 from congrArg Subtype.val hj, Units.val_one]; exact S.one_mem_A
    exact (dvd_pow_self S.p hj0).trans (hj ▸ orderOf_dvd_natCard _)
  obtain ⟨x, hxo, hxα⟩ := CFSG.HardMathSupport.C14Group.exists_fixed_of_order_p S.hp α hαp hpX
  set t : GL ι K := (x : GL ι K) with ht
  have htC : ∀ e ∈ S.E₀, t * e = e * t := x.2.1
  have hts : SuppOn ε t := x.2.2
  have htp : t ^ S.p = 1 := by
    rw [ht, ← Subgroup.coe_pow, ← hxo, pow_orderOf_eq_one, Subgroup.coe_one]
  have ht1 : t ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hxo
    exact S.hp.one_lt.ne hxo
  have htσ : S.σGL t = t := congrArg Subtype.val hxα
  have htA := hSat t htC htp htσ
  obtain ⟨f, hfc, hff, hfσ, hfε, hfA⟩ := S.exists_fixed_idem hε hC
  obtain ⟨t', ht'C, ht'p, ht'σ, -, ht'A⟩ :=
    S.exists_orderP_not_mem hε htA htp ht1 hts htσ hfc hff hfσ hfε hfA
  exact ht'A (hSat t' ht'C ht'p ht'σ)

def subIdemL {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) (η : Matrix ι ι K) : Set (Matrix ι ι K) :=
  {δ | δ ∈ S.A ∧ δ * δ = δ ∧ δ * η = δ}

theorem mul_idem_mem_A {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) [Fintype K] [CharP K 2] (hSat : S.SatL) {y : GL ι K} (hy : ∀ e ∈ S.E₀, y * e = e * y)
    (hyp : ∃ k : ℕ, y ^ S.p ^ k = 1) :
    ∀ (n : ℕ) (η : Matrix ι ι K), (S.subIdemL η).ncard = n → η ∈ S.A → η * η = η →
      (y : Matrix ι ι K) * η ∈ S.A := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro η hn hηA hηη
  haveI : Finite (Matrix ι ι K) := show Finite (ι → ι → K) from inferInstance
  by_cases hη0 : η = 0
  · rw [hη0, mul_zero]; exact Submodule.zero_mem _
  by_cases hmin : ∀ δ ∈ S.A, δ * δ = δ → δ * η = δ → δ = 0 ∨ δ = η
  · have hε : S.IsMinIdem η := ⟨hηA, hηη, hη0, hmin⟩
    have hyη : (y : Matrix ι ι K) * η = η * y := S.comm_of_cent hy hηA
    let z : GL ι K := ⟨y * η + (1 - η), ((y⁻¹ : GL ι K) : Matrix ι ι K) * η + (1 - η),
      by rw [block_mul hηη (S.comm_of_cent (S.cent_inv hy) hηA), ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_mul, add_sub_cancel],
      by rw [block_mul hηη hyη, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_mul, add_sub_cancel]⟩
    have hzc : ∀ e ∈ S.E₀, z * e = e * z := by
      intro e he
      have hye : (y : Matrix ι ι K) * e = e * y := S.comm_of_cent hy (S.mem_A_of_mem he)
      exact Units.ext (block_comm hye (S.comm_A hηA (S.mem_A_of_mem he)))
    have hzs : SuppOn η z := block_supp hηη
    have hzp : ∃ k : ℕ, z ^ S.p ^ k = 1 := by
      obtain ⟨k, hk⟩ := hyp
      refine ⟨k, Units.ext ?_⟩
      rw [Units.val_pow_eq_pow_val]
      show ((y : Matrix ι ι K) * η + (1 - η)) ^ S.p ^ k = ((1 : GL ι K) : Matrix ι ι K)
      rw [block_pow hηη hyη, ← Units.val_pow_eq_pow_val, hk, Units.val_one, one_mul,
        add_sub_cancel]
    have hzA := S.pElt_mem_A_of_minIdem hSat hε hzc hzs hzp
    have : (y : Matrix ι ι K) * η = (z : Matrix ι ι K) * η := by
      show (y : Matrix ι ι K) * η = ((y : Matrix ι ι K) * η + (1 - η)) * η
      rw [add_mul, mul_assoc, hηη, sub_mul, one_mul, hηη, sub_self, add_zero]
    rw [this]; exact S.mul_mem_A hzA hηA
  push Not at hmin
  obtain ⟨δ, hδA, hδδ, hδη, hδ0, hδne⟩ := hmin
  have hηδ : η * δ = δ := (S.comm_A hηA hδA).trans hδη
  set δ' := η - δ with hδ'
  have hδ'A : δ' ∈ S.A := Submodule.sub_mem _ hηA hδA
  have hδ'δ' : δ' * δ' = δ' := by
    rw [hδ', sub_mul, mul_sub, mul_sub, hηη, hηδ, hδη, hδδ]; abel
  have hδ'η : δ' * η = δ' := by rw [hδ', sub_mul, hηη, hδη]
  have hsub : ∀ γ, γ * η = γ → S.subIdemL γ ⊆ S.subIdemL η := by
    intro γ hγ x hx
    exact ⟨hx.1, hx.2.1, by rw [← hx.2.2, mul_assoc, hγ]⟩
  have hηmem : η ∈ S.subIdemL η := ⟨hηA, hηη, hηη⟩
  have hlt1 : (S.subIdemL δ).ncard < n := by
    rw [← hn]
    refine Set.ncard_lt_ncard ⟨hsub δ hδη, fun h => hδne ?_⟩ (Set.toFinite _)
    exact (((h hηmem).2.2).symm.trans hηδ).symm
  have hlt2 : (S.subIdemL δ').ncard < n := by
    rw [← hn]
    refine Set.ncard_lt_ncard ⟨hsub δ' hδ'η, fun h => hδ0 ?_⟩ (Set.toFinite _)
    have h1 := (h hηmem).2.2
    have : η * δ' = η - δ := by rw [hδ', mul_sub, hηη, hηδ]
    rw [this] at h1
    have h2 : δ = η - (η - δ) := by abel
    rw [h2, h1, sub_self]
  have hsplit : (y : Matrix ι ι K) * η = y * δ + y * δ' := by rw [hδ', mul_sub]; abel
  rw [hsplit]
  exact Submodule.add_mem _ (ih _ hlt1 δ rfl hδA hδδ) (ih _ hlt2 δ' rfl hδ'A hδ'δ')

theorem pElt_mem_A {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : LinSetting K ι) [Fintype K] [CharP K 2] (hSat : S.SatL) {y : GL ι K} (hy : ∀ e ∈ S.E₀, y * e = e * y)
    (hyp : ∃ k : ℕ, y ^ S.p ^ k = 1) : (y : Matrix ι ι K) ∈ S.A := by
  have h := S.mul_idem_mem_A hSat hy hyp _ 1 rfl S.one_mem_A (mul_one 1)
  rwa [mul_one] at h

end LinSetting

theorem pElt_mem_A_lin {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] [Fintype K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (σ₀ : K ≃+* K) (hσ₀ : orderOf σ₀ = p)
    (E₀ : Subgroup (GL ι K)) (hE : IsElemAbelian p E₀)
    (hEfix : ∀ e ∈ E₀, (e : Matrix ι ι K).map σ₀ = e)
    (hSat : ∀ y : GL ι K, (∀ e ∈ E₀, y * e = e * y) → y ^ p = 1 →
      (y : Matrix ι ι K).map σ₀ = y → (y : Matrix ι ι K) ∈ spanE K E₀)
    {y : GL ι K} (hy : ∀ e ∈ E₀, y * e = e * y) (hyp : ∃ k : ℕ, y ^ p ^ k = 1) :
    (y : Matrix ι ι K) ∈ spanE K E₀ :=
  (LinSetting.mk p hp hp2 σ₀ hσ₀ E₀ hE hEfix).pElt_mem_A
    (fun y hy hyp hyσ => hSat y hy hyp (congrArg Units.val hyσ)) hy hyp


end CFSG.HardMathSupport.C14Cl
