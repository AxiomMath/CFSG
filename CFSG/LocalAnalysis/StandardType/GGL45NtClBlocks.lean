module

public import CFSG.LocalAnalysis.StandardType.GGL45NtClAlgebra
public import CFSG.LocalAnalysis.StandardType.GGL45NtGroupLemmas

public section

namespace CFSG.HardMathSupport.C14Cl

open Matrix CFSG.Open

theorem dvd_of_forall_pow_two_pow_eq {K : Type} [Field K] [Fintype K] {n m : ℕ}
    (hn : Fintype.card K = 2 ^ n) (h : ∀ c : K, c ^ 2 ^ m = c) : n ∣ m := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units, hn]
  have hgm : g ^ (2 ^ m - 1) = 1 := by
    have h1 : g ^ (2 ^ m - 1) * g = g := by
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
      exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h g)
    simpa using h1
  have hdvd : 2 ^ n - 1 ∣ 2 ^ m - 1 := hord ▸ orderOf_dvd_of_pow_eq_one hgm
  have hgcd := Nat.pow_sub_one_gcd_pow_sub_one 2 n m
  rw [Nat.gcd_eq_left hdvd] at hgcd
  have h2 : 2 ^ Nat.gcd n m = 2 ^ n := by
    have := Nat.one_le_two_pow (n := Nat.gcd n m); have := Nat.one_le_two_pow (n := n); omega
  exact Nat.gcd_eq_left_iff_dvd.1 (Nat.pow_right_injective le_rfl h2)

theorem pow_eq_pow_of_modEq' {G : Type*} [Group G] {y : G} {N m m' : ℕ} (hy : y ^ N = 1)
    (h : m ≡ m' [MOD N]) : y ^ m = y ^ m' :=
  (pow_eq_pow_iff_modEq).2 (Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hy) h)

theorem exists_indep {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (E : Subgroup G)
    (hE : ∀ x ∈ E, x ^ p = 1) (hcard : p ^ 2 ≤ Nat.card E) :
    ∃ e₁ ∈ E, ∃ e₂ ∈ E, ∀ i j : ℕ, e₁ ^ i * e₂ ^ j = 1 → p ∣ i ∧ p ∣ j := by
  haveI := Fact.mk hp
  have hpos : 0 < Nat.card E := lt_of_lt_of_le (pow_pos hp.pos 2) hcard
  haveI : Finite E := Nat.finite_of_card_ne_zero hpos.ne'
  have hlt1 : 1 < Nat.card E := lt_of_lt_of_le (Nat.one_lt_pow two_ne_zero hp.one_lt) hcard
  haveI := Finite.one_lt_card_iff_nontrivial.1 hlt1
  obtain ⟨⟨e₁, he₁⟩, h1⟩ := exists_ne (1 : E)
  have he₁1 : e₁ ≠ 1 := fun h => h1 (Subtype.ext h)
  have ho₁ : orderOf e₁ = p := orderOf_eq_prime (hE e₁ he₁) he₁1
  have hZ : Nat.card (Subgroup.zpowers e₁) = p := by rw [Nat.card_zpowers, ho₁]
  haveI : Finite (Subgroup.zpowers e₁) := Nat.finite_of_card_ne_zero (by rw [hZ]; exact hp.ne_zero)
  have : ¬ E ≤ Subgroup.zpowers e₁ := by
    intro hle
    have := Subgroup.card_le_of_le hle
    rw [hZ] at this
    have : p ^ 2 ≤ p := hcard.trans this
    have : p < p ^ 2 := by nlinarith [hp.two_le]
    omega
  obtain ⟨e₂, he₂, he₂Z⟩ := Set.not_subset.1 this
  refine ⟨e₁, he₁, e₂, he₂, fun i j hij => ?_⟩
  have hj : p ∣ j := by
    by_contra hj
    have hcop : Nat.Coprime j p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hj).symm
    obtain ⟨j', -, hj'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have hmem : (e₂ ^ j) ^ j' ∈ Subgroup.zpowers e₁ := by
      have : e₂ ^ j = (e₁ ^ i)⁻¹ := eq_inv_of_mul_eq_one_right hij
      rw [this]
      exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)) _
    rw [← pow_mul, pow_eq_pow_of_modEq' (hE e₂ he₂) (show j * j' ≡ 1 [MOD p] from by
      rw [Nat.ModEq, hj', Nat.mod_eq_of_lt hp.one_lt]), pow_one] at hmem
    exact he₂Z hmem
  refine ⟨?_, hj⟩
  obtain ⟨c, rfl⟩ := hj
  rw [pow_mul, hE e₂ he₂, one_pow, mul_one] at hij
  exact ho₁ ▸ orderOf_dvd_of_pow_eq_one hij

structure ClSetting (K ι : Type) [Field K] [Fintype ι] [DecidableEq ι] where
  p : ℕ
  hp : p.Prime
  hp2 : p ≠ 2
  τ : K ≃+* K
  hτ : ∀ c, τ (τ c) = c
  G : Matrix ι ι K
  hG : IsUnit G.det
  hGs : (G.map τ)ᵀ = G
  σ₀ : K ≃+* K
  hσ₀ : orderOf σ₀ = p
  hGσ : G.map σ₀ = G
  E₀ : Subgroup (GL ι K)
  hE : IsElemAbelian p E₀
  hEU : ∀ e ∈ E₀, formAdj τ G (e : Matrix ι ι K) * e = 1
  hEfix : ∀ e ∈ E₀, (e : Matrix ι ι K).map σ₀ = e

@[expose] def SuppOn {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (η : Matrix ι ι K) (g : GL ι K) : Prop :=
  (g : Matrix ι ι K) * (1 - η) = 1 - η

namespace ClSetting

noncomputable abbrev adj {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (M : Matrix ι ι K) : Matrix ι ι K := formAdj S.τ S.G M

@[expose] def σ {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) : Matrix ι ι K ≃+* Matrix ι ι K := S.σ₀.mapMatrix

@[expose] def σGL {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) : GL ι K →* GL ι K := Units.map S.σ.toRingHom.toMonoidHom

@[expose] def Cent {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (g : GL ι K) : Prop :=
  S.adj (g : Matrix ι ι K) * g = 1 ∧ ∀ e ∈ S.E₀, g * e = e * g

abbrev A {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) : Submodule K (Matrix ι ι K) := spanE K S.E₀

@[expose] def IsAtom {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (η : Matrix ι ι K) : Prop :=
  η ∈ S.A ∧ η * η = η ∧ S.adj η = η ∧ η ≠ 0 ∧
    ∀ ε ∈ S.A, ε * ε = ε → S.adj ε = ε → ε * η = ε → ε = 0 ∨ ε = η

theorem mem_A_of_mem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) {e : GL ι K} (he : e ∈ S.E₀) : (e : Matrix ι ι K) ∈ S.A :=
  Submodule.subset_span ⟨⟨e, he⟩, rfl⟩

theorem one_mem_A {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) : (1 : Matrix ι ι K) ∈ S.A := by
  simpa using S.mem_A_of_mem S.E₀.one_mem

theorem mul_mem_A {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) {M N : Matrix ι ι K} (hM : M ∈ S.A) (hN : N ∈ S.A) : M * N ∈ S.A :=
  spanE_mul_mem S.E₀ hM hN

theorem pow_mem_A {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) {M : Matrix ι ι K} (hM : M ∈ S.A) (n : ℕ) : M ^ n ∈ S.A := by
  induction n with
  | zero => rw [pow_zero]; exact S.one_mem_A
  | succ n ih => rw [pow_succ]; exact S.mul_mem_A ih hM

theorem comm_A {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) {M N : Matrix ι ι K} (hM : M ∈ S.A) (hN : N ∈ S.A) : M * N = N * M :=
  spanE_commute S.E₀ S.hE.1 hM hN

theorem comm_of_cent {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) {y : GL ι K} (hy : ∀ e ∈ S.E₀, y * e = e * y) {M : Matrix ι ι K}
    (hM : M ∈ S.A) : (y : Matrix ι ι K) * M = M * y :=
  commute_of_mem_spanE S.E₀ (fun e he => by
    have := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) (hy e he); simpa using this) hM

theorem cent_inv {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) {y : GL ι K} (hy : ∀ e ∈ S.E₀, y * e = e * y) :
    ∀ e ∈ S.E₀, y⁻¹ * e = e * y⁻¹ := by
  intro e he
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hy e he, mul_assoc, mul_inv_cancel, mul_one]

theorem adj_mul {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (M N : Matrix ι ι K) : S.adj (M * N) = S.adj N * S.adj M := by
  have hGG : S.G * S.G⁻¹ = 1 := Matrix.mul_nonsing_inv _ S.hG
  have hm : (M * N).map S.τ = M.map S.τ * N.map S.τ := Matrix.map_mul (f := (S.τ : K →+* K))
  simp only [adj, formAdj]
  rw [hm, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc S.G S.G⁻¹, hGG, Matrix.one_mul]

theorem adj_one {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) : S.adj (1 : Matrix ι ι K) = 1 := by
  simp [adj, formAdj, Matrix.nonsing_inv_mul _ S.hG]

theorem adj_add {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (M N : Matrix ι ι K) : S.adj (M + N) = S.adj M + S.adj N := by
  simp [adj, formAdj, Matrix.map_add, Matrix.transpose_add, mul_add, add_mul]

theorem adj_sub {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (M N : Matrix ι ι K) : S.adj (M - N) = S.adj M - S.adj N := by
  simp [adj, formAdj, Matrix.map_sub, Matrix.transpose_sub, mul_sub, sub_mul]

theorem adj_pow {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (M : Matrix ι ι K) (n : ℕ) : S.adj (M ^ n) = S.adj M ^ n := by
  induction n with
  | zero => simp [S.adj_one]
  | succ n ih => rw [pow_succ, S.adj_mul, ih, pow_succ']

theorem adj_eq_inv {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (g : GL ι K) (h : S.adj (g : Matrix ι ι K) * g = 1) :
    S.adj (g : Matrix ι ι K) = ((g⁻¹ : GL ι K) : Matrix ι ι K) := by
  calc S.adj (g : Matrix ι ι K) = S.adj (g : Matrix ι ι K) * ((g * g⁻¹ : GL ι K) :
        Matrix ι ι K) := by rw [mul_inv_cancel, Units.val_one, mul_one]
    _ = ((g⁻¹ : GL ι K) : Matrix ι ι K) := by
        rw [Units.val_mul, ← mul_assoc, h, one_mul]

end ClSetting

theorem block_mul {R : Type*} [Ring R] {η Y W : R} (hη : η * η = η) (hW : W * η = η * W) :
    (Y * η + (1 - η)) * (W * η + (1 - η)) = Y * W * η + (1 - η) := by
  have h1 : η * (1 - η) = 0 := by rw [mul_sub, mul_one, hη, sub_self]
  have h2 : (1 - η) * η = 0 := by rw [sub_mul, one_mul, hη, sub_self]
  have h3 : (1 - η) * (1 - η) = 1 - η := by rw [sub_mul, one_mul, h1, sub_zero]
  have h4 : (1 - η) * W = W * (1 - η) := by rw [sub_mul, mul_sub, one_mul, mul_one, hW]
  calc (Y * η + (1 - η)) * (W * η + (1 - η))
      = Y * (η * W) * η + Y * (η * (1 - η)) + (1 - η) * W * η + (1 - η) * (1 - η) := by
        noncomm_ring
    _ = Y * W * η + (1 - η) := by
        rw [← hW, h1, h4, mul_assoc W, h2, h3]
        simp only [mul_zero, add_zero, mul_assoc, hη]

theorem block_pow {R : Type*} [Ring R] {η Y : R} (hη : η * η = η) (hY : Y * η = η * Y)
    (k : ℕ) : (Y * η + (1 - η)) ^ k = Y ^ k * η + (1 - η) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, block_mul hη hY, ← pow_succ]

theorem block_comm {R : Type*} [Ring R] {η Y X : R} (hY : Y * X = X * Y) (hη : η * X = X * η) :
    (Y * η + (1 - η)) * X = X * (Y * η + (1 - η)) := by
  calc (Y * η + (1 - η)) * X = Y * (η * X) + (X - η * X) := by noncomm_ring
    _ = Y * X * η + (X - X * η) := by rw [hη, mul_assoc]
    _ = X * (Y * η + (1 - η)) := by rw [hY]; noncomm_ring

theorem block_supp {R : Type*} [Ring R] {η Y : R} (hη : η * η = η) :
    (Y * η + (1 - η)) * (1 - η) = 1 - η := by
  have h1 : η * (1 - η) = 0 := by rw [mul_sub, mul_one, hη, sub_self]
  have h3 : (1 - η) * (1 - η) = 1 - η := by rw [sub_mul, one_mul, h1, sub_zero]
  calc (Y * η + (1 - η)) * (1 - η) = Y * (η * (1 - η)) + (1 - η) * (1 - η) := by noncomm_ring
    _ = 1 - η := by rw [h1, h3, mul_zero, zero_add]

theorem exists_trace_coeffs {L : Type} [Field L] [Fintype L] (σ₀ : L ≃+* L) :
    ∃ c : L → L, ∀ i < orderOf σ₀, ∑ l, c l * (σ₀ ^ i) l = if i = 0 then 1 else 0 := by
  classical
  haveI : Finite (L ≃+* L) := Finite.of_injective (fun e : L ≃+* L => (e : L → L))
    (fun a b h => RingEquiv.ext (congrFun h))
  set n := orderOf σ₀ with hn
  have hn0 : 0 < n := orderOf_pos σ₀
  let w : L → (Fin n → L) := fun l i => (σ₀ ^ (i : ℕ)) l
  let e0 : Fin n → L := fun i => if (i : ℕ) = 0 then 1 else 0
  have hmem : e0 ∈ Submodule.span L (Set.range w) := by
    by_contra hne
    obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_notMem hne
    let a : Fin n → L := fun i => f (Pi.single i 1)
    have hfx : ∀ x : Fin n → L, f x = ∑ i, a i * x i := by
      intro x
      conv_lhs => rw [show x = ∑ i, x i • (Pi.single i 1 : Fin n → L) by
        ext j; simp [Finset.sum_apply, Pi.single_apply]]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    let φ : Fin n → (L →* L) := fun i => ((σ₀ ^ (i : ℕ) : L ≃+* L) : L →+* L).toMonoidHom
    have hφ : Function.Injective φ := by
      intro i j h
      have h' : σ₀ ^ (i : ℕ) = σ₀ ^ (j : ℕ) := RingEquiv.ext fun c => DFunLike.congr_fun h c
      exact Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 h')
    have hli := (linearIndependent_monoidHom L L).comp φ hφ
    have ha : a = 0 := by
      funext i
      refine Fintype.linearIndependent_iff.1 hli a (funext fun l => ?_) i
      have := hfk (Submodule.subset_span ⟨l, rfl⟩)
      rw [LinearMap.mem_ker, hfx] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        Pi.zero_apply]
      exact this
    apply hf0
    rw [hfx]
    simp [ha]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hmem
  refine ⟨c, fun i hi => ?_⟩
  have := congrFun hc ⟨i, hi⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w, e0] at this
  exact this

theorem trace_descent_scalar {L : Type} [Field L] [Fintype L] (σ₀ : L ≃+* L) (c : L → L)
    (hc : ∀ i < orderOf σ₀, ∑ l, c l * (σ₀ ^ i) l = if i = 0 then 1 else 0) (z : L) :
    z = ∑ l, c l * ∑ i ∈ Finset.range (orderOf σ₀), (σ₀ ^ i) (l * z) := by
  have hn0 : 0 < orderOf σ₀ := by
    haveI : Finite (L ≃+* L) := Finite.of_injective (fun e : L ≃+* L => (e : L → L))
      (fun a b h => RingEquiv.ext (congrFun h))
    exact orderOf_pos σ₀
  simp_rw [Finset.mul_sum, map_mul]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  rw [Finset.sum_eq_single 0]
  · rw [hc 0 hn0]; simp
  · intro i hi hi0
    rw [hc i (Finset.mem_range.1 hi), if_neg hi0, zero_mul]
  · intro h; exact absurd (Finset.mem_range.2 hn0) h

theorem trace_fixed {L : Type} [Field L] [Finite L] (σ₀ : L ≃+* L) (z : L) :
    σ₀ (∑ i ∈ Finset.range (orderOf σ₀), (σ₀ ^ i) z) =
      ∑ i ∈ Finset.range (orderOf σ₀), (σ₀ ^ i) z := by
  haveI : Finite (L ≃+* L) := Finite.of_injective (fun e : L ≃+* L => (e : L → L))
    (fun a b h => RingEquiv.ext (congrFun h))
  rw [map_sum]
  have hs : ∀ i, σ₀ ((σ₀ ^ i) z) = (σ₀ ^ (i + 1)) z := fun i => by rw [pow_succ']; rfl
  simp_rw [hs]
  have e1 := Finset.sum_range_succ' (fun i => (σ₀ ^ i) z) (orderOf σ₀)
  have e2 := Finset.sum_range_succ (fun i => (σ₀ ^ i) z) (orderOf σ₀)
  rw [pow_orderOf_eq_one] at e2
  rw [pow_zero] at e1
  exact add_right_cancel (e1.symm.trans e2)

namespace ClSetting

theorem adj_block_mul {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) {η : Matrix ι ι K} (hηA : η ∈ S.A) (hηη : η * η = η) (hηa : S.adj η = η)
    {y : GL ι K} (hy : S.Cent y) :
    S.adj ((y : Matrix ι ι K) * η + (1 - η)) * ((y : Matrix ι ι K) * η + (1 - η)) = 1 := by
  have hyη : (y : Matrix ι ι K) * η = η * y := S.comm_of_cent hy.2 hηA
  have hyiη : ((y⁻¹ : GL ι K) : Matrix ι ι K) * η = η * ((y⁻¹ : GL ι K) : Matrix ι ι K) :=
    S.comm_of_cent (S.cent_inv hy.2) hηA
  rw [S.adj_add, S.adj_sub, S.adj_mul, S.adj_one, hηa, S.adj_eq_inv y hy.1, ← hyiη,
    block_mul hηη hyη, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, add_sub_cancel]

def blockGL {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) {η : Matrix ι ι K} (hηA : η ∈ S.A) (hηη : η * η = η) {y : GL ι K}
    (hy : ∀ e ∈ S.E₀, y * e = e * y) : GL ι K :=
  ⟨y * η + (1 - η), ((y⁻¹ : GL ι K) : Matrix ι ι K) * η + (1 - η),
    by rw [block_mul hηη (S.comm_of_cent (S.cent_inv hy) hηA), ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_mul, add_sub_cancel],
    by rw [block_mul hηη (S.comm_of_cent hy hηA), ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_mul, add_sub_cancel]⟩

theorem sigma_idempotent {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {ε : Matrix ι ι K} (hε : ε ∈ S.A) (hεε : ε * ε = ε) : S.σ ε = ε := by
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

theorem adj_mem_A {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {M : Matrix ι ι K} (hM : M ∈ S.A) : S.adj M ∈ S.A ∧ S.σ M ∈ S.A := by
  have hmemE : ∀ e : GL ι K, e ∈ S.E₀ → ((e : Matrix ι ι K)) ∈ S.A :=
    fun e he => Submodule.subset_span (Set.mem_range.2 ⟨(⟨e, he⟩ : S.E₀), rfl⟩)
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨e, he⟩, rfl⟩ := hx
    refine ⟨?_, ?_⟩
    · have h1 : S.adj (e : Matrix ι ι K) = ((e⁻¹ : GL ι K) : Matrix ι ι K) := by
        have h := S.hEU e he
        calc S.adj (e : Matrix ι ι K) = S.adj (e : Matrix ι ι K) * ((e * e⁻¹ : GL ι K) :
              Matrix ι ι K) := by rw [mul_inv_cancel, Units.val_one, mul_one]
          _ = ((e⁻¹ : GL ι K) : Matrix ι ι K) := by
              rw [Units.val_mul, ← mul_assoc]; erw [h]; rw [one_mul]
      simp only
      rw [h1]; exact hmemE _ (S.E₀.inv_mem he)
    · simp only
      have : S.σ (e : Matrix ι ι K) = e := S.hEfix e he
      rw [this]; exact hmemE _ he
  | zero => simp [adj, formAdj, σ]
  | add x y _ _ hx hy =>
    refine ⟨?_, ?_⟩
    · have : S.adj (x + y) = S.adj x + S.adj y := by
        simp [adj, formAdj, Matrix.map_add, Matrix.transpose_add, mul_add, add_mul]
      rw [this]; exact Submodule.add_mem _ hx.1 hy.1
    · rw [map_add]; exact Submodule.add_mem _ hx.2 hy.2
  | smul c x _ hx =>
    refine ⟨?_, ?_⟩
    · have : S.adj (c • x) = S.τ c • S.adj x := by
        simp only [adj, formAdj]
        rw [show (c • x).map S.τ = S.τ c • x.map S.τ by ext i j; simp [Matrix.map_apply]]
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
      rw [this]; exact Submodule.smul_mem _ _ hx.1
    · have : S.σ (c • x) = S.σ₀ c • S.σ x := by
        ext i j; simp [σ, RingEquiv.mapMatrix_apply, Matrix.map_apply]
      rw [this]; exact Submodule.smul_mem _ _ hx.2

theorem adj_sigma {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (M : Matrix ι ι K) : S.adj (S.σ M) = S.σ (S.adj M) := by
  obtain ⟨a, ha⟩ := exists_pow_two_of_ringEquiv S.σ₀
  obtain ⟨b, hb⟩ := exists_pow_two_of_ringEquiv S.τ
  have hστ : ∀ c, S.σ₀ (S.τ c) = S.τ (S.σ₀ c) := by
    intro c; rw [ha, hb, ha, hb, ← pow_mul, ← pow_mul, mul_comm]
  have hσG : S.σ S.G = S.G := S.hGσ
  have hσGi : S.σ S.G⁻¹ = S.G⁻¹ := by
    refine (Matrix.inv_eq_left_inv ?_).symm
    rw [show S.σ S.G⁻¹ * S.G = S.σ (S.G⁻¹ * S.G) by rw [map_mul, hσG],
      Matrix.nonsing_inv_mul _ S.hG, map_one]
  have hT : S.σ ((M.map S.τ)ᵀ) = ((S.σ M).map S.τ)ᵀ := by
    ext i j; simp [σ, RingEquiv.mapMatrix_apply, Matrix.map_apply, hστ]
  simp only [adj, formAdj]
  rw [map_mul, map_mul, hσG, hσGi, hT]

theorem adj_sigma_mul {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {g : GL ι K} (hg : S.adj (g : Matrix ι ι K) * g = 1) :
    S.adj (S.σGL g : Matrix ι ι K) * (S.σGL g : Matrix ι ι K) = 1 := by
  show S.adj (S.σ g) * S.σ g = 1
  rw [S.adj_sigma, ← map_mul, hg, map_one]

theorem exists_frob_exp {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] : ∃ Q : ℕ, 2 ≤ Q ∧ (∀ M ∈ S.A, M ^ Q = M) ∧ S.p ∣ Q - 1 := by
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

def subIdem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (ε : Matrix ι ι K) : Set (Matrix ι ι K) :=
  {δ | δ ∈ S.A ∧ δ * δ = δ ∧ S.adj δ = δ ∧ δ * ε = δ}

theorem exists_atom_decomp {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] : ∀ (n : ℕ) (ε : Matrix ι ι K), (S.subIdem ε).ncard = n →
    ε ∈ S.A → ε * ε = ε → S.adj ε = ε →
    ∃ T : Finset (Matrix ι ι K), (∀ η ∈ T, S.IsAtom η) ∧
      (∀ η ∈ T, ∀ η' ∈ T, η ≠ η' → η * η' = 0) ∧ (∀ η ∈ T, η * ε = η) ∧ ∑ η ∈ T, η = ε := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ε hn hεA hεε hεa
  classical
  by_cases hε0 : ε = 0
  · exact ⟨∅, by simp, by simp, by simp, by simp [hε0]⟩
  by_cases hat : S.IsAtom ε
  · exact ⟨{ε}, by simpa using hat, by simp, by simpa using hεε, by simp⟩
  have : ∃ δ ∈ S.A, δ * δ = δ ∧ S.adj δ = δ ∧ δ * ε = δ ∧ δ ≠ 0 ∧ δ ≠ ε := by
    by_contra hcon
    push Not at hcon
    exact hat ⟨hεA, hεε, hεa, hε0, fun δ hδA hδδ hδa hδε => by
      by_cases h0 : δ = 0
      · exact Or.inl h0
      · exact Or.inr (hcon δ hδA hδδ hδa hδε h0)⟩
  obtain ⟨δ, hδA, hδδ, hδa, hδε, hδ0, hδne⟩ := this
  have hεδ : ε * δ = δ := by rw [S.comm_A hεA hδA, hδε]
  set ε' := ε - δ with hε'
  have hε'A : ε' ∈ S.A := Submodule.sub_mem _ hεA hδA
  have hε'ε' : ε' * ε' = ε' := by
    rw [hε', sub_mul, mul_sub, mul_sub, hεε, hεδ, hδε, hδδ]; abel
  have hε'a : S.adj ε' = ε' := by rw [hε', S.adj_sub, hεa, hδa]
  have hε'ε : ε' * ε = ε' := by rw [hε', sub_mul, hεε, hδε]
  have hεε' : ε * ε' = ε' := by rw [S.comm_A hεA hε'A, hε'ε]
  have hδε' : δ * ε' = 0 := by rw [hε', mul_sub, hδε, hδδ, sub_self]
  have hε'δ : ε' * δ = 0 := by rw [hε', sub_mul, hεδ, hδδ, sub_self]
  have hfin : (S.subIdem ε).Finite := Set.toFinite _
  have hmemε : ε ∈ S.subIdem ε := ⟨hεA, hεε, hεa, hεε⟩
  have hsub1 : S.subIdem δ ⊂ S.subIdem ε := by
    refine Set.ssubset_iff_subset_ne.2 ⟨fun γ ⟨hγA, hγγ, hγa, hγδ⟩ => ⟨hγA, hγγ, hγa, ?_⟩,
      fun heq => hδne ?_⟩
    · rw [← hγδ, mul_assoc, hδε]
    · have h := (heq ▸ hmemε).2.2.2
      rw [hεδ] at h; exact h
  have hsub2 : S.subIdem ε' ⊂ S.subIdem ε := by
    refine Set.ssubset_iff_subset_ne.2 ⟨fun γ ⟨hγA, hγγ, hγa, hγδ⟩ => ⟨hγA, hγγ, hγa, ?_⟩,
      fun heq => hδ0 ?_⟩
    · rw [← hγδ, mul_assoc, hε'ε]
    · have h := (heq ▸ hmemε).2.2.2
      rw [hεε', hε'] at h
      exact sub_eq_self.1 h
  obtain ⟨T1, h1at, h1o, h1ε, h1s⟩ :=
    ih _ (hn ▸ Set.ncard_lt_ncard hsub1 hfin) δ rfl hδA hδδ hδa
  obtain ⟨T2, h2at, h2o, h2ε, h2s⟩ :=
    ih _ (hn ▸ Set.ncard_lt_ncard hsub2 hfin) ε' rfl hε'A hε'ε' hε'a
  have hcross : ∀ η ∈ T1, ∀ η' ∈ T2, η * η' = 0 ∧ η' * η = 0 := by
    intro η h η' h'
    have e1 : δ * η = η := by rw [S.comm_A hδA (h1at η h).1, h1ε η h]
    have e2 : ε' * η' = η' := by rw [S.comm_A hε'A (h2at η' h').1, h2ε η' h']
    constructor
    · calc η * η' = η * δ * (ε' * η') := by rw [h1ε η h, e2]
        _ = η * (δ * ε') * η' := by noncomm_ring
        _ = 0 := by rw [hδε', mul_zero, zero_mul]
    · calc η' * η = η' * ε' * (δ * η) := by rw [h2ε η' h', e1]
        _ = η' * (ε' * δ) * η := by noncomm_ring
        _ = 0 := by rw [hε'δ, mul_zero, zero_mul]
  have hdisj : Disjoint T1 T2 := Finset.disjoint_left.2 fun η h1 h2 => (h1at η h1).2.2.2.1 (by
    calc η = η * ε' * δ := by rw [h2ε η h2, h1ε η h1]
      _ = 0 := by rw [mul_assoc, hε'δ, mul_zero])
  refine ⟨T1 ∪ T2, fun η hη => ?_, fun η hη η' hη' hne => ?_, fun η hη => ?_, ?_⟩
  · rcases Finset.mem_union.1 hη with h | h
    exacts [h1at η h, h2at η h]
  · rcases Finset.mem_union.1 hη with h | h <;> rcases Finset.mem_union.1 hη' with h' | h'
    exacts [h1o η h η' h' hne, (hcross η h η' h').1, (hcross η' h' η h).2, h2o η h η' h' hne]
  · rcases Finset.mem_union.1 hη with h | h
    · calc η * ε = η * δ * ε := by rw [h1ε η h]
        _ = η := by rw [mul_assoc, hδε, h1ε η h]
    · calc η * ε = η * ε' * ε := by rw [h2ε η h]
        _ = η := by rw [mul_assoc, hε'ε, h2ε η h]
  · rw [Finset.sum_union hdisj, h1s, h2s, hε', add_sub_cancel]

theorem exists_atoms {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] : ∃ (r : ℕ) (η : Fin r → Matrix ι ι K), (∀ i, S.IsAtom (η i)) ∧
    (∀ i j, i ≠ j → η i * η j = 0) ∧ ∑ i, η i = 1 := by
  obtain ⟨T, hat, horth, -, hsum⟩ :=
    S.exists_atom_decomp _ 1 rfl S.one_mem_A (mul_one 1) S.adj_one
  refine ⟨T.card, fun i => (T.equivFin.symm i : Matrix ι ι K),
    fun i => hat _ (T.equivFin.symm i).2,
    fun i j hij => horth _ (T.equivFin.symm i).2 _ (T.equivFin.symm j).2
      (fun h => hij (T.equivFin.symm.injective (Subtype.ext h))), ?_⟩
  rw [Equiv.sum_comp T.equivFin.symm (fun x : T => (x : Matrix ι ι K)),
    Finset.sum_coe_sort T (fun x => x), hsum]

theorem blockPart {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {η : Matrix ι ι K} (hη : S.IsAtom η) {y : GL ι K} (hy : S.Cent y) :
    ∃ z : GL ι K, (z : Matrix ι ι K) = y * η + (1 - η) ∧ S.Cent z ∧ SuppOn η z ∧
      (∀ k : ℕ, y ^ k = 1 → z ^ k = 1) ∧ (S.σGL y = y → S.σGL z = z) := by
  obtain ⟨hηA, hηη, hηa, -, -⟩ := hη
  have hyη : (y : Matrix ι ι K) * η = η * y := S.comm_of_cent hy.2 hηA
  refine ⟨S.blockGL hηA hηη hy.2, rfl, ⟨S.adj_block_mul hηA hηη hηa hy, fun e he => ?_⟩,
    block_supp hηη, fun k hk => ?_, fun hσy => ?_⟩
  · have hye : (y : Matrix ι ι K) * e = e * y := by
      have := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) (hy.2 e he); simpa using this
    exact Units.ext (block_comm hye (S.comm_A hηA (S.mem_A_of_mem he)))
  · refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val]
    show ((y : Matrix ι ι K) * η + (1 - η)) ^ k = ((1 : GL ι K) : Matrix ι ι K)
    rw [block_pow hηη hyη, ← Units.val_pow_eq_pow_val, hk, Units.val_one, one_mul,
      add_sub_cancel]
  · have hσy' : S.σ (y : Matrix ι ι K) = y := congrArg Units.val hσy
    refine Units.ext ?_
    show S.σ ((y : Matrix ι ι K) * η + (1 - η)) = (y : Matrix ι ι K) * η + (1 - η)
    rw [map_add, map_sub, map_mul, map_one, hσy', S.sigma_idempotent hηA hηη]

theorem exists_inv_sub_one {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {η : Matrix ι ι K} (hη : S.IsAtom η) {t : GL ι K}
    (htA : (t : Matrix ι ι K) ∈ S.A) (htU : S.Cent t) (htp : t ^ S.p = 1) (ht1 : t ≠ 1)
    (hts : SuppOn η t) : ∃ w ∈ S.A, w * (((t : Matrix ι ι K) - 1) * η) = η := by
  obtain ⟨hηA, hηη, hηa, -, hmin⟩ := hη
  obtain ⟨Q, hQ2, hQA, ⟨c, hc⟩⟩ := S.exists_frob_exp
  have hneg : ∀ M : Matrix ι ι K, -M = M := fun M => by ext i j; simp [CharTwo.neg_eq]
  set ti := ((t⁻¹ : GL ι K) : Matrix ι ι K) with hti_def
  have hti : ti * t = 1 := by rw [hti_def, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set x := ((t : Matrix ι ι K) - 1) * η with hx
  have hxA : x ∈ S.A := S.mul_mem_A (Submodule.sub_mem _ htA S.one_mem_A) hηA
  have hxQ : x ^ Q = x := hQA x hxA
  have hxη : x * η = x := by rw [hx, mul_assoc, hηη]
  have htiη : ti * η = η * ti := S.comm_of_cent (S.cent_inv htU.2) hηA
  have htix : ti * x = x * ti := S.comm_of_cent (S.cent_inv htU.2) hxA
  have hadjx : S.adj x = ti * x := by
    calc S.adj x = η * (ti - 1) := by
          rw [hx, S.adj_mul, hηa, S.adj_sub, S.adj_one, S.adj_eq_inv t htU.1]
      _ = ti * x := by
          have h1 : ti * x = (1 - ti) * η := by rw [hx, ← mul_assoc, mul_sub, hti, mul_one]
          have h2 : η * (ti - 1) = (ti - 1) * η := by
            rw [mul_sub, sub_mul, mul_one, one_mul, htiη]
          rw [h2, h1, ← neg_sub ti 1, neg_mul, hneg]
  have htQ : t ^ (Q - 1) = 1 := by rw [hc, pow_mul, htp, one_pow]
  set e := x ^ (Q - 1) with he
  have hee : e * e = e := by
    rw [he, ← pow_add, show Q - 1 + (Q - 1) = Q + (Q - 2) by omega, pow_add, hxQ, ← pow_succ',
      show Q - 2 + 1 = Q - 1 by omega]
  have heη : e * η = e := by
    rw [he, show Q - 1 = Q - 2 + 1 by omega, pow_succ, mul_assoc, hxη]
  have hea : S.adj e = e := by
    rw [he, S.adj_pow, hadjx, (show Commute ti x from htix).mul_pow, hti_def,
      ← Units.val_pow_eq_pow_val, inv_pow, htQ, inv_one, Units.val_one, one_mul]
  rcases hmin e (S.pow_mem_A hxA _) hee hea heη with h0 | hη'
  · exfalso
    have hx0 : x = 0 := by
      rw [← hxQ, show Q = Q - 1 + 1 by omega, pow_succ, ← he, h0, zero_mul]
    have htη : (t : Matrix ι ι K) * η = η := by
      rw [hx, sub_mul, one_mul, sub_eq_zero] at hx0; exact hx0
    apply ht1
    refine Units.ext ?_
    calc (t : Matrix ι ι K) = t * η + t * (1 - η) := by noncomm_ring
      _ = ((1 : GL ι K) : Matrix ι ι K) := by
          rw [htη, show (t : Matrix ι ι K) * (1 - η) = 1 - η from hts, Units.val_one,
            add_sub_cancel]
  · refine ⟨x ^ (Q - 2), S.pow_mem_A hxA _, ?_⟩
    rw [← pow_succ, show Q - 2 + 1 = Q - 1 by omega, ← he, hη']

noncomputable def B {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (x y : ι → K) : K := (S.τ ∘ x) ⬝ᵥ (S.G *ᵥ y)

theorem B_add_left {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (x x' y : ι → K) : S.B (x + x') y = S.B x y + S.B x' y := by
  unfold B
  rw [show S.τ ∘ (x + x') = S.τ ∘ x + S.τ ∘ x' from funext fun i => map_add S.τ _ _,
    add_dotProduct]

theorem B_smul_left {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (c : K) (x y : ι → K) : S.B (c • x) y = S.τ c * S.B x y := by
  unfold B
  rw [show S.τ ∘ (c • x) = S.τ c • (S.τ ∘ x) from funext fun i => by simp, smul_dotProduct,
    smul_eq_mul]

theorem B_zero_left {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (y : ι → K) : S.B 0 y = 0 := by
  unfold B; simp

theorem B_add_right {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (x y y' : ι → K) : S.B x (y + y') = S.B x y + S.B x y' := by
  unfold B; rw [Matrix.mulVec_add, dotProduct_add]

theorem B_smul_right {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (c : K) (x y : ι → K) : S.B x (c • y) = c * S.B x y := by
  unfold B; rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem B_zero_right {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (x : ι → K) : S.B x 0 = 0 := by
  unfold B; simp

theorem B_sum_left {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {α : Type} (s : Finset α) (f : α → ι → K) (y : ι → K) :
    S.B (∑ a ∈ s, f a) y = ∑ a ∈ s, S.B (f a) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [B_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, B_add_left, ih]

theorem B_sum_right {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {α : Type} (s : Finset α) (f : α → ι → K) (x : ι → K) :
    S.B x (∑ a ∈ s, f a) = ∑ a ∈ s, S.B x (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [B_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, B_add_right, ih]

theorem comp_mulVec {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] [Fintype K] [CharP K 2] (f : K ≃+* K) (M : Matrix ι ι K) (x : ι → K) :
    f ∘ (M *ᵥ x) = M.map f *ᵥ (f ∘ x) :=
  funext fun i => RingHom.map_mulVec (f : K →+* K) M x i

theorem dot_mulVec_left {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] [Fintype K] [CharP K 2] (M : Matrix ι ι K) (v w : ι → K) : (M *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (Mᵀ *ᵥ w) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]

theorem G_inv_map_transpose {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] : ((S.G⁻¹).map S.τ)ᵀ = S.G⁻¹ := by
  have hmap : ∀ X Y : Matrix ι ι K, (X * Y).map S.τ = X.map S.τ * Y.map S.τ :=
    fun X Y => Matrix.map_mul (f := (S.τ : K →+* K))
  have h1 : (S.G⁻¹).map S.τ * S.G.map S.τ = 1 := by
    rw [← hmap, Matrix.nonsing_inv_mul _ S.hG]; ext i j; simp [Matrix.one_apply]
  have h2 : (S.G.map S.τ)⁻¹ = (S.G⁻¹).map S.τ := Matrix.inv_eq_left_inv h1
  rw [← h2, Matrix.transpose_nonsing_inv, S.hGs]

theorem B_mulVec {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (M : Matrix ι ι K) (x y : ι → K) : S.B x (M *ᵥ y) = S.B (S.adj M *ᵥ x) y := by
  have hmap : ∀ X Y : Matrix ι ι K, (X * Y).map S.τ = X.map S.τ * Y.map S.τ :=
    fun X Y => Matrix.map_mul (f := (S.τ : K →+* K))
  have hττ : (M.map S.τ).map S.τ = M := by ext i j; simp [S.hτ]
  have hkey : ((S.adj M).map S.τ)ᵀ * S.G = S.G * M := by
    simp only [adj, formAdj]
    rw [hmap, hmap, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_map, hττ,
      Matrix.transpose_transpose, S.hGs, S.G_inv_map_transpose, Matrix.mul_assoc,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ S.hG, Matrix.mul_one]
  unfold B
  rw [comp_mulVec, dot_mulVec_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hkey]

theorem B_symm {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (x y : ι → K) : S.B y x = S.τ (S.B x y) := by
  unfold B
  rw [show S.τ ((S.τ ∘ x) ⬝ᵥ (S.G *ᵥ y)) = (S.τ ∘ (S.τ ∘ x)) ⬝ᵥ (S.τ ∘ (S.G *ᵥ y)) from
    RingHom.map_dotProduct (S.τ : K →+* K) _ _, comp_mulVec,
    show S.τ ∘ (S.τ ∘ x) = x from funext fun i => S.hτ _, dotProduct_comm, dot_mulVec_left]
  have h : S.G.map S.τ = S.Gᵀ := by
    have := congrArg Matrix.transpose S.hGs
    rwa [Matrix.transpose_transpose] at this
  rw [h]

theorem tau_sigma_comm {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (c : K) : S.σ₀ (S.τ c) = S.τ (S.σ₀ c) := by
  obtain ⟨a, ha⟩ := exists_pow_two_of_ringEquiv S.σ₀
  obtain ⟨b, hb⟩ := exists_pow_two_of_ringEquiv S.τ
  rw [ha, hb, ha, hb, ← pow_mul, ← pow_mul, mul_comm]

theorem B_sigma {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (x y : ι → K) :
    S.σ₀ (S.B x y) = S.B (S.σ₀ ∘ x) (S.σ₀ ∘ y) := by
  unfold B
  rw [show S.σ₀ ((S.τ ∘ x) ⬝ᵥ (S.G *ᵥ y)) = (S.σ₀ ∘ (S.τ ∘ x)) ⬝ᵥ (S.σ₀ ∘ (S.G *ᵥ y)) from
    RingHom.map_dotProduct (S.σ₀ : K →+* K) _ _, comp_mulVec, S.hGσ]
  congr 1
  funext i; exact S.tau_sigma_comm _

theorem eq_zero_of_B_right {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {y : ι → K} (h : ∀ x, S.B x y = 0) : y = 0 := by
  have hGy : S.G *ᵥ y = 0 := by
    funext i
    have := h (Pi.single i 1)
    unfold B at this
    rw [show S.τ ∘ (Pi.single i 1 : ι → K) = Pi.single i 1 from funext fun j => by
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj], single_one_dotProduct] at this
    exact this
  rw [← Matrix.one_mulVec y, ← Matrix.nonsing_inv_mul _ S.hG, ← Matrix.mulVec_mulVec, hGy,
    Matrix.mulVec_zero]

theorem eq_zero_of_B_left {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {x : ι → K} (h : ∀ y, S.B x y = 0) : x = 0 :=
  S.eq_zero_of_B_right fun y => by rw [S.B_symm, h, map_zero]

theorem adj_adj {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (M : Matrix ι ι K) : S.adj (S.adj M) = M :=
  formAdj_formAdj S.τ S.hG S.hτ S.hGs M

theorem B_sub_right {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (x y y' : ι → K) : S.B x (y - y') = S.B x y - S.B x y' := by
  unfold B; rw [Matrix.mulVec_sub, dotProduct_sub]

theorem adj_zero {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] : S.adj (0 : Matrix ι ι K) = 0 := by simp [adj, formAdj]

theorem sigma_apply {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (M : Matrix ι ι K) : S.σ M = M.map S.σ₀ := rfl

theorem map_pow_of_sigma {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {M : Matrix ι ι K} (hM : S.σ M = M) (i : ℕ) :
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

theorem sigma_mulVec {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (M : Matrix ι ι K) (x : ι → K) :
    S.σ₀ ∘ (M *ᵥ x) = S.σ M *ᵥ (S.σ₀ ∘ x) := by rw [S.sigma_apply]; exact comp_mulVec S.σ₀ M x

theorem comp_add {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] [Fintype K] [CharP K 2] (f : K ≃+* K) (x y : ι → K) : f ∘ (x + y) = f ∘ x + f ∘ y :=
  funext fun _ => map_add f _ _

theorem vec_descent {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {ε' : Matrix ι ι K} (hσ : S.σ ε' = ε') {x : ι → K}
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
    have := comp_mulVec (S.σ₀ ^ i) ε' (l • x)
    rw [S.map_pow_of_sigma hσ, Matrix.mulVec_smul, hx] at this
    exact this.symm
  · funext a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hTa]
    exact trace_descent_scalar S.σ₀ c hc (x a)

theorem B_vanish {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {ε₁ ε₂ M : Matrix ι ι K} (h₁ : S.σ ε₁ = ε₁) (h₂ : S.σ ε₂ = ε₂)
    (h : ∀ v w, S.σ₀ ∘ v = v → ε₁ *ᵥ v = v → S.σ₀ ∘ w = w → ε₂ *ᵥ w = w → S.B v (M *ᵥ w) = 0)
    {x y : ι → K} (hx : ε₁ *ᵥ x = x) (hy : ε₂ *ᵥ y = y) : S.B x (M *ᵥ y) = 0 := by
  obtain ⟨c, T, hT, rfl⟩ := S.vec_descent h₁ hx
  obtain ⟨c', T', hT', rfl⟩ := S.vec_descent h₂ hy
  rw [S.B_sum_left]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [S.B_smul_left, Matrix.mulVec_sum, S.B_sum_right,
    Finset.sum_eq_zero fun l' _ => by
      rw [Matrix.mulVec_smul, S.B_smul_right, h _ _ (hT l).1 (hT l).2 (hT' l').1 (hT' l').2,
        mul_zero], mul_zero]

theorem B_compl_eta {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {η : Matrix ι ι K} (hηa : S.adj η = η) {z : ι → K} (hz : η *ᵥ z = z)
    (y : ι → K) : S.B z ((1 - η) *ᵥ y) = 0 := by
  rw [S.B_mulVec, S.adj_sub, S.adj_one, hηa, Matrix.sub_mulVec, Matrix.one_mulVec, hz, sub_self,
    S.B_zero_left]

theorem eq_zero_of_B_eta {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {η : Matrix ι ι K} (hηa : S.adj η = η) {x : ι → K}
    (hx : η *ᵥ x = x) (h : ∀ y, η *ᵥ y = y → S.B x y = 0) (hηη : η * η = η) : x = 0 := by
  refine S.eq_zero_of_B_left fun y => ?_
  have hy : y = η *ᵥ y + (1 - η) *ᵥ y := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  rw [hy, S.B_add_right, h _ (by rw [Matrix.mulVec_mulVec, hηη]), S.B_compl_eta hηa hx, add_zero]

theorem B_iso {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {δ δ' : Matrix ι ι K} (hadj : S.adj δ = δ') (h0 : δ' * δ = 0) {x y : ι → K}
    (hx : δ *ᵥ x = x) (hy : δ *ᵥ y = y) : S.B x y = 0 := by
  rw [← hy, S.B_mulVec, hadj, ← hx, Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec, S.B_zero_left]

def IsMinIdem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (ε : Matrix ι ι K) : Prop :=
  ε ∈ S.A ∧ ε * ε = ε ∧ ε ≠ 0 ∧ ∀ δ ∈ S.A, δ * δ = δ → δ * ε = δ → δ = 0 ∨ δ = ε

theorem minIdem_inv {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {ε : Matrix ι ι K} (hε : S.IsMinIdem ε)
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

theorem exists_minIdem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {η : Matrix ι ι K} (hηA : η ∈ S.A) (hηη : η * η = η)
    (hη0 : η ≠ 0) : ∃ ε, S.IsMinIdem ε ∧ ε * η = ε := by
  classical
  haveI : Finite (Matrix ι ι K) := show Finite (ι → ι → K) from inferInstance
  let T : Matrix ι ι K → Set (Matrix ι ι K) :=
    fun δ => {δ' | δ' ∈ S.A ∧ δ' * δ' = δ' ∧ δ' * δ = δ'}
  have hex : ∃ n, ∃ δ, δ ∈ S.A ∧ δ * δ = δ ∧ δ ≠ 0 ∧ δ * η = δ ∧ (T δ).ncard = n :=
    ⟨_, η, hηA, hηη, hη0, hηη, rfl⟩
  obtain ⟨δ, hδA, hδδ, hδ0, hδη, hδn⟩ := Nat.find_spec hex
  refine ⟨δ, ⟨hδA, hδδ, hδ0, fun δ' hδ'A hδ'δ' hδ'δ => ?_⟩, hδη⟩
  by_contra hne
  push Not at hne
  obtain ⟨h0, hne'⟩ := hne
  have hsub : T δ' ⊂ T δ := by
    refine ⟨fun x hx => ⟨hx.1, hx.2.1, by rw [← hx.2.2, mul_assoc, hδ'δ]⟩, fun hsub => ?_⟩
    have h1 := (hsub ⟨hδA, hδδ, hδδ⟩).2.2
    exact hne' (hδ'δ.symm.trans ((S.comm_A hδ'A hδA).trans h1))
  have hlt := Set.ncard_lt_ncard hsub (Set.toFinite _)
  exact Nat.find_min hex (hδn ▸ hlt) ⟨δ', hδ'A, hδ'δ', h0, by rw [← hδ'δ, mul_assoc, hδη], rfl⟩

theorem adj_minIdem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {ε : Matrix ι ι K} (hε : S.IsMinIdem ε) :
    S.IsMinIdem (S.adj ε) := by
  obtain ⟨hεA, hεε, hε0, hmin⟩ := hε
  refine ⟨(S.adj_mem_A hεA).1, ?_, ?_, ?_⟩
  · rw [← S.adj_mul, hεε]
  · intro h; apply hε0; rw [← S.adj_adj ε, h, S.adj_zero]
  intro δ hδA hδδ hδε
  have hδsA := (S.adj_mem_A hδA).1
  have h1 : S.adj δ * ε = S.adj δ := by
    have := congrArg S.adj hδε
    rw [S.adj_mul, S.adj_adj] at this
    rw [S.comm_A hδsA hεA, this]
  rcases hmin (S.adj δ) hδsA (by rw [← S.adj_mul, hδδ]) h1 with h | h
  · left; rw [← S.adj_adj δ, h, S.adj_zero]
  · right; rw [← S.adj_adj δ, h]

theorem minIdem_cases {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {η ε : Matrix ι ι K} (hη : S.IsAtom η) (hε : S.IsMinIdem ε)
    (hεη : ε * η = ε) : ε = η ∨ (ε * S.adj ε = 0 ∧ ε + S.adj ε = η) := by
  obtain ⟨hηA, hηη, hηa, hη0, hat⟩ := hη
  have hεA := hε.1
  have hεε := hε.2.1
  have hε0 := hε.2.2.1
  have hε' := S.adj_minIdem hε
  have hεsA := hε'.1
  have hεsεs := hε'.2.1
  have hcomm : S.adj ε * ε = ε * S.adj ε := S.comm_A hεsA hεA
  have hδ : (ε * S.adj ε) * (ε * S.adj ε) = ε * S.adj ε := by
    rw [mul_assoc, ← mul_assoc (S.adj ε), hcomm, mul_assoc ε, hεsεs, ← mul_assoc, hεε]
  have hδε : (ε * S.adj ε) * ε = ε * S.adj ε := by rw [mul_assoc, hcomm, ← mul_assoc, hεε]
  rcases hε.2.2.2 _ (S.mul_mem_A hεA hεsA) hδ hδε with h | h
  · right
    refine ⟨h, ?_⟩
    have hγγ : (ε + S.adj ε) * (ε + S.adj ε) = ε + S.adj ε := by
      rw [add_mul, mul_add, mul_add, hεε, hεsεs, h, hcomm, h, add_zero, zero_add]
    have hγa : S.adj (ε + S.adj ε) = ε + S.adj ε := by rw [S.adj_add, S.adj_adj, add_comm]
    have hsη : S.adj ε * η = S.adj ε := by
      have := congrArg S.adj (show η * ε = ε from (S.comm_A hηA hεA).trans hεη)
      rwa [S.adj_mul, hηa] at this
    have hγη : (ε + S.adj ε) * η = ε + S.adj ε := by rw [add_mul, hεη, hsη]
    rcases hat _ (Submodule.add_mem _ hεA hεsA) hγγ hγa hγη with h0 | h1
    · exfalso; apply hε0
      have : ε * (ε + S.adj ε) = ε := by rw [mul_add, hεε, h, add_zero]
      rw [← this, h0, mul_zero]
    · exact h1
  · left
    rcases hε'.2.2.2 ε hεA hεε h with h0 | hs
    · exact absurd h0 hε0
    · rcases hat ε hεA hεε hs.symm hεη with h0 | h1
      · exact absurd h0 hε0
      · exact h1

theorem mul_mem_A_of_cyclic {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {ε' c : Matrix ι ι K} (hε'A : ε' ∈ S.A) (hε' : ε' * ε' = ε')
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

theorem sigma_pow_mem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {W : Submodule K (ι → K)} (hWσ : ∀ w ∈ W, S.σ₀ ∘ w ∈ W) :
    ∀ (k : ℕ), ∀ w ∈ W, ⇑(S.σ₀ ^ k) ∘ w ∈ W := by
  intro k
  induction k with
  | zero => intro w hw; exact hw
  | succ k ih =>
    intro w hw
    have : ⇑(S.σ₀ ^ (k + 1)) ∘ w = S.σ₀ ∘ (⇑(S.σ₀ ^ k) ∘ w) := by
      funext a; rw [pow_succ']; rfl
    rw [this]; exact hWσ _ (ih w hw)

theorem sigma_surj {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (w : ι → K) :
    S.σ₀ ∘ (⇑(S.σ₀ ^ (S.p - 1)) ∘ w) = w := by
  have hσp : S.σ₀ ^ S.p = 1 := S.hσ₀ ▸ pow_orderOf_eq_one S.σ₀
  have h1 : 1 ≤ S.p := S.hp.one_lt.le
  funext a
  change (S.σ₀ * S.σ₀ ^ (S.p - 1)) (w a) = w a
  rw [← pow_succ', Nat.sub_add_cancel h1, hσp]; rfl

theorem exists_proj {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {η : Matrix ι ι K} (hηA : η ∈ S.A)
    (hηa : S.adj η = η) (W : Submodule K (ι → K)) (hWA : ∀ a ∈ S.A, ∀ w ∈ W, a *ᵥ w ∈ W)
    (hWσ : ∀ w ∈ W, S.σ₀ ∘ w ∈ W) (hWη : ∀ w ∈ W, η *ᵥ w = w)
    (hnd : ∀ w ∈ W, (∀ w' ∈ W, S.B w' w = 0) → w = 0) :
    ∃ f : Matrix ι ι K, (∀ e ∈ S.E₀, f * (e : Matrix ι ι K) = e * f) ∧ f * f = f ∧
      S.adj f = f ∧ S.σ f = f ∧ f * η = f ∧ (∀ w ∈ W, f *ᵥ w = w) ∧ (∀ x, f *ᵥ x ∈ W) := by
  classical
  let Wp : Submodule K (ι → K) :=
    { carrier := {y | ∀ w ∈ W, S.B w y = 0}
      add_mem' := fun {x y} hx hy w hw => by rw [S.B_add_right, hx w hw, hy w hw, add_zero]
      zero_mem' := fun w _ => S.B_zero_right w
      smul_mem' := fun c y hy w hw => by rw [S.B_smul_right, hy w hw, mul_zero] }
  have hWp : ∀ y, y ∈ Wp ↔ ∀ w ∈ W, S.B w y = 0 := fun y => Iff.rfl
  have hdisj : W ⊓ Wp = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxp⟩ := Submodule.mem_inf.1 hx
    exact (Submodule.mem_bot K).2 (hnd x hxW hxp)
  set r := Module.finrank K W
  let b := Module.finBasis K W
  let Φ : (ι → K) →ₗ[K] (Fin r → K) :=
    { toFun := fun y i => S.B (b i : ι → K) y
      map_add' := fun y y' => funext fun i => S.B_add_right _ _ _
      map_smul' := fun c y => funext fun i => by simp [S.B_smul_right] }
  have hker : LinearMap.ker Φ ≤ Wp := by
    intro y hy w hw
    have hy' : ∀ i, S.B (b i : ι → K) y = 0 := fun i => congrFun (LinearMap.mem_ker.1 hy) i
    have hw' : w = ∑ i, (b.repr ⟨w, hw⟩ i) • (b i : ι → K) := by
      have := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hw', S.B_sum_left]
    exact Finset.sum_eq_zero fun i _ => by rw [S.B_smul_left, hy' i, mul_zero]
  have hrank := LinearMap.finrank_range_add_finrank_ker Φ
  have hrange : Module.finrank K (LinearMap.range Φ) ≤ r :=
    (Submodule.finrank_le _).trans (by simp)
  have hkp : Module.finrank K (LinearMap.ker Φ) ≤ Module.finrank K Wp := Submodule.finrank_mono hker
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq W Wp
  rw [hdisj, finrank_bot] at hsup
  have htop : W ⊔ Wp = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (by omega))
  have hc : IsCompl W Wp := ⟨disjoint_iff.2 hdisj, codisjoint_iff.2 htop⟩
  have hdec : ∀ x : ι → K, ∃ w ∈ W, ∃ y ∈ Wp, w + y = x := fun x =>
    Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : x ∈ W ⊔ Wp)
  let P : (ι → K) →ₗ[K] (ι → K) := W.subtype ∘ₗ Submodule.projectionOnto W Wp hc
  set f := LinearMap.toMatrix' P with hf
  have hfx : ∀ x, f *ᵥ x = P x := fun x => LinearMap.toMatrix'_mulVec P x
  have hfW : ∀ w ∈ W, f *ᵥ w = w := fun w hw => by
    rw [hfx]
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨w, hw⟩)
  have hfWp : ∀ y ∈ Wp, f *ᵥ y = 0 := fun y hy => by
    rw [hfx]
    show ((Submodule.projectionOnto W Wp hc y : W) : ι → K) = 0
    rw [(Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).2 hy]
    rfl
  have hfmem : ∀ x, f *ᵥ x ∈ W := fun x => by
    rw [hfx]; exact (Submodule.projectionOnto W Wp hc x).2
  have huniq : ∀ M : Matrix ι ι K, (∀ w ∈ W, M *ᵥ w = w) → (∀ y ∈ Wp, M *ᵥ y = 0) → M = f := by
    intro M h1 h2
    refine Matrix.ext_iff_mulVec.2 fun x => ?_
    obtain ⟨w, hw, y, hy, rfl⟩ := hdec x
    rw [Matrix.mulVec_add, Matrix.mulVec_add, h1 w hw, h2 y hy, hfW w hw, hfWp y hy]
  have hWpA : ∀ a ∈ S.A, ∀ y ∈ Wp, a *ᵥ y ∈ Wp := fun a ha y hy w hw => by
    rw [S.B_mulVec]; exact hy _ (hWA _ (S.adj_mem_A ha).1 w hw)
  have hsub : ∀ x, x - f *ᵥ x ∈ Wp := fun x => by
    obtain ⟨w, hw, y, hy, rfl⟩ := hdec x
    rw [Matrix.mulVec_add, hfW w hw, hfWp y hy, add_zero, add_sub_cancel_left]; exact hy
  have hWpσ : ∀ y ∈ Wp, S.σ₀ ∘ y ∈ Wp := fun y hy w hw => by
    rw [← S.sigma_surj w, ← S.B_sigma, hy _ (S.sigma_pow_mem hWσ _ w hw), map_zero]
  refine ⟨f, fun e he => ?_, ?_, ?_, ?_, ?_, hfW, hfmem⟩
  · have heA : ((e⁻¹ : GL ι K) : Matrix ι ι K) ∈ S.A := S.mem_A_of_mem (S.E₀.inv_mem he)
    have hei : ((e⁻¹ : GL ι K) : Matrix ι ι K) * e = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hei' : (e : Matrix ι ι K) * ((e⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h := huniq ((e : Matrix ι ι K) * f * ((e⁻¹ : GL ι K) : Matrix ι ι K))
      (fun w hw => by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfW _ (hWA _ heA w hw),
          Matrix.mulVec_mulVec, hei', Matrix.one_mulVec])
      (fun y hy => by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfWp _ (hWpA _ heA y hy),
          Matrix.mulVec_zero])
    calc f * (e : Matrix ι ι K) = (e : Matrix ι ι K) * f * ((e⁻¹ : GL ι K) : Matrix ι ι K) * e := by
          rw [h]
      _ = (e : Matrix ι ι K) * f := by rw [mul_assoc, hei, mul_one]
  · exact huniq _ (fun w hw => by rw [← Matrix.mulVec_mulVec, hfW w hw, hfW w hw])
      (fun y hy => by rw [← Matrix.mulVec_mulVec, hfWp y hy, Matrix.mulVec_zero])
  · refine huniq _ (fun w hw => ?_) (fun y hy => ?_)
    · rw [← sub_eq_zero]
      refine S.eq_zero_of_B_right fun x => ?_
      rw [S.B_sub_right, S.B_mulVec, S.adj_adj]
      have hBx : S.B x w = S.B (f *ᵥ x) w := by
        conv_lhs => rw [show x = f *ᵥ x + (x - f *ᵥ x) by abel]
        rw [S.B_add_left, S.B_symm w (x - f *ᵥ x), hsub x w hw, map_zero, add_zero]
      rw [hBx, sub_self]
    · refine S.eq_zero_of_B_right fun x => ?_
      rw [S.B_mulVec, S.adj_adj]; exact hy _ (hfmem x)
  · refine huniq _ (fun w hw => ?_) (fun y hy => ?_)
    · have hw' := S.sigma_surj w
      rw [← hw', ← S.sigma_mulVec, hfW _ (S.sigma_pow_mem hWσ _ w hw)]
    · have hy' := S.sigma_surj y
      have hmem : ⇑(S.σ₀ ^ (S.p - 1)) ∘ y ∈ Wp := by
        clear hy'
        induction (S.p - 1) generalizing y with
        | zero => exact hy
        | succ k ih =>
          have : ⇑(S.σ₀ ^ (k + 1)) ∘ y = S.σ₀ ∘ (⇑(S.σ₀ ^ k) ∘ y) := by
            funext a; rw [pow_succ']; rfl
          rw [this]; exact hWpσ _ (ih y hy)
      rw [← hy', ← S.sigma_mulVec, hfWp _ hmem]
      funext a; simp
  · exact huniq _ (fun w hw => by rw [← Matrix.mulVec_mulVec, hWη w hw, hfW w hw])
      (fun y hy => by rw [← Matrix.mulVec_mulVec, hfWp _ (hWpA _ hηA y hy)])

theorem exists_fixed_tau_ne {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (hτ1 : ¬ ∀ c, S.τ c = c) :
    ∃ l : K, S.σ₀ l = l ∧ S.τ l ≠ l := by
  classical
  by_contra H
  push Not at H
  haveI : Finite (K ≃+* K) := Finite.of_injective (fun e : K ≃+* K => (e : K → K))
    (fun a b h => RingEquiv.ext (congrFun h))
  obtain ⟨c, hc⟩ := exists_trace_coeffs S.σ₀
  set n := orderOf S.σ₀ with hn
  let d : ℕ → K := fun i => ∑ l, S.τ (c l) * (S.σ₀ ^ i) l
  have hτz : ∀ z, S.τ z = ∑ i ∈ Finset.range n, d i * (S.σ₀ ^ i) z := by
    intro z
    conv_lhs => rw [trace_descent_scalar S.σ₀ c hc z]
    rw [← hn]
    have h1 : ∀ l, S.τ (c l * ∑ i ∈ Finset.range n, (S.σ₀ ^ i) (l * z)) =
        S.τ (c l) * ∑ i ∈ Finset.range n, (S.σ₀ ^ i) (l * z) := fun l => by
      rw [map_mul, H _ (trace_fixed S.σ₀ _)]
    rw [map_sum]
    simp_rw [h1, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [d, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => by ring
  have hτne : ∀ i : ℕ, S.τ ≠ S.σ₀ ^ i := by
    intro i hi
    apply hτ1
    have hτ2 : S.τ ^ 2 = 1 := RingEquiv.ext fun x => by rw [pow_two]; exact S.hτ x
    have hτp : S.τ ^ S.p = 1 := by
      rw [hi, ← pow_mul, mul_comm, pow_mul, ← S.hσ₀, pow_orderOf_eq_one, one_pow]
    have h1 : orderOf S.τ ∣ Nat.gcd 2 S.p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hτ2) (orderOf_dvd_of_pow_eq_one hτp)
    have hg : Nat.gcd 2 S.p = 1 :=
      (Nat.coprime_primes Nat.prime_two S.hp).2 (Ne.symm S.hp2)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h1
    intro x; rw [h1]; rfl
  let φ : Option (Fin n) → (K →* K) := fun o => match o with
    | none => ((S.τ : K ≃+* K) : K →+* K).toMonoidHom
    | some i => ((S.σ₀ ^ (i : ℕ) : K ≃+* K) : K →+* K).toMonoidHom
  have hφ : Function.Injective φ := by
    intro o o' h
    have h' : ∀ x, φ o x = φ o' x := fun x => DFunLike.congr_fun h x
    rcases o with _ | i <;> rcases o' with _ | j
    · rfl
    · exact absurd (RingEquiv.ext h') (hτne j)
    · exact absurd (RingEquiv.ext fun x => (h' x).symm) (hτne i)
    · exact congrArg some (Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 (RingEquiv.ext h')))
  have hli := (linearIndependent_monoidHom K K).comp φ hφ
  let g : Option (Fin n) → K := fun o => match o with
    | none => 1
    | some i => -d i
  have hsum : ∀ x, ∑ o, g o * φ o x = 0 := by
    intro x
    rw [Fintype.sum_option]
    change 1 * S.τ x + ∑ i : Fin n, -d i * (S.σ₀ ^ (i : ℕ)) x = 0
    rw [one_mul, hτz x, Fin.sum_univ_eq_sum_range (fun i => -d i * (S.σ₀ ^ i) x) n,
      ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring
  have := Fintype.linearIndependent_iff.1 hli g (funext fun x => by
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
      Pi.zero_apply]
    exact hsum x) none
  exact one_ne_zero this

def subAV {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (v u : ι → K) : Submodule K (ι → K) where
  carrier := {x | ∃ a ∈ S.A, ∃ b ∈ S.A, x = a *ᵥ v + b *ᵥ u}
  add_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    exact ⟨a + a', Submodule.add_mem _ ha ha', b + b', Submodule.add_mem _ hb hb', by
      simp only [Matrix.add_mulVec]; abel⟩
  zero_mem' := ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simp⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨c • a, Submodule.smul_mem _ c ha, c • b, Submodule.smul_mem _ c hb, by
      rw [Matrix.smul_mulVec, Matrix.smul_mulVec, smul_add]⟩

theorem sa_idem_of_sub {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {η : Matrix ι ι K} (hη : S.IsAtom η)
    (W : Submodule K (ι → K)) (hWA : ∀ a ∈ S.A, ∀ w ∈ W, a *ᵥ w ∈ W)
    (hWσ : ∀ w ∈ W, S.σ₀ ∘ w ∈ W) (hWη : ∀ w ∈ W, η *ᵥ w = w)
    (hnd : ∀ w ∈ W, (∀ w' ∈ W, S.B w' w = 0) → w = 0) (hW0 : ∃ w ∈ W, w ≠ 0)
    (hWη' : ∃ x, η *ᵥ x = x ∧ x ∉ W) :
    ∃ f : Matrix ι ι K, (∀ e ∈ S.E₀, f * (e : Matrix ι ι K) = e * f) ∧ f * f = f ∧
      S.adj f = f ∧ S.σ f = f ∧ f * η = f ∧ f ∉ S.A := by
  obtain ⟨f, hfc, hff, hfa, hfσ, hfη, hfW, hfmem⟩ :=
    S.exists_proj hη.1 hη.2.2.1 W hWA hWσ hWη hnd
  refine ⟨f, hfc, hff, hfa, hfσ, hfη, fun hfA => ?_⟩
  rcases hη.2.2.2.2 f hfA hff hfa hfη with h0 | h1
  · obtain ⟨w, hw, hw0⟩ := hW0
    have := hfW w hw
    rw [h0, Matrix.zero_mulVec] at this
    exact hw0 this.symm
  · obtain ⟨x, hx, hxW⟩ := hWη'
    have := hfmem x
    rw [h1, hx] at this
    exact hxW this

theorem subAV_props {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {η : Matrix ι ι K} (hηA : η ∈ S.A) {v u : ι → K}
    (hvσ : S.σ₀ ∘ v = v) (huσ : S.σ₀ ∘ u = u) (hvη : η *ᵥ v = v) (huη : η *ᵥ u = u) :
    (∀ a ∈ S.A, ∀ w ∈ S.subAV v u, a *ᵥ w ∈ S.subAV v u) ∧
    (∀ w ∈ S.subAV v u, S.σ₀ ∘ w ∈ S.subAV v u) ∧ (∀ w ∈ S.subAV v u, η *ᵥ w = w) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro a' ha' _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨a' * a, S.mul_mem_A ha' ha, a' * b, S.mul_mem_A ha' hb, by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨S.σ a, (S.adj_mem_A ha).2, S.σ b, (S.adj_mem_A hb).2, by
      rw [comp_add, S.sigma_mulVec, S.sigma_mulVec, hvσ, huσ]⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, S.comm_A hηA ha,
      S.comm_A hηA hb, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvη, huη]

theorem mulVec_comm_fix {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {M δ : Matrix ι ι K} (hM : M ∈ S.A) (hδ : δ ∈ S.A) {x : ι → K}
    (hx : δ *ᵥ x = x) : δ *ᵥ (M *ᵥ x) = M *ᵥ x := by
  rw [Matrix.mulVec_mulVec, S.comm_A hδ hM, ← Matrix.mulVec_mulVec, hx]

theorem exists_aniso {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {η : Matrix ι ι K} (hη : S.IsAtom η) {t : GL ι K}
    (htA : (t : Matrix ι ι K) ∈ S.A) (htU : S.Cent t) (htp : t ^ S.p = 1) (ht1 : t ≠ 1)
    (hts : SuppOn η t) :
    ∃ v : ι → K, S.σ₀ ∘ v = v ∧ η *ᵥ v = v ∧ ∃ a ∈ S.A, S.B (a *ᵥ v) v ≠ 0 := by
  obtain ⟨hηA, hηη, hηa, hη0, -⟩ := hη
  have hση : S.σ η = η := S.sigma_idempotent hηA hηη
  by_contra H
  push Not at H
  have hpol : ∀ v w, S.σ₀ ∘ v = v → η *ᵥ v = v → S.σ₀ ∘ w = w → η *ᵥ w = w → ∀ a ∈ S.A,
      S.B (a *ᵥ v) w + S.τ (S.B (S.adj a *ᵥ v) w) = 0 := by
    intro v w hv hvη hw hwη a ha
    have h := H (v + w) (by rw [comp_add, hv, hw]) (by rw [Matrix.mulVec_add, hvη, hwη]) a ha
    rw [Matrix.mulVec_add, S.B_add_left, S.B_add_right, S.B_add_right, H v hv hvη a ha,
      H w hw hwη a ha, zero_add, add_zero, S.B_symm v (a *ᵥ w), S.B_mulVec] at h
    exact h
  by_cases hτ1 : ∀ c, S.τ c = c
  · set N := (t : Matrix ι ι K) + S.adj (t : Matrix ι ι K) with hN
    have hNA : N ∈ S.A := Submodule.add_mem _ htA (S.adj_mem_A htA).1
    have h1 : ∀ v w, S.σ₀ ∘ v = v → η *ᵥ v = v → S.σ₀ ∘ w = w → η *ᵥ w = w →
        S.B v (S.adj N *ᵥ w) = 0 := by
      intro v w hv hvη hw hwη
      rw [S.B_mulVec, S.adj_adj, hN, Matrix.add_mulVec, S.B_add_left]
      have := hpol v w hv hvη hw hwη _ htA
      rwa [hτ1] at this
    have h2 : ∀ x, η *ᵥ x = x → N *ᵥ x = 0 := by
      intro x hx
      have hNx : η *ᵥ (N *ᵥ x) = N *ᵥ x := S.mulVec_comm_fix hNA hηA hx
      refine S.eq_zero_of_B_eta hηa hNx (fun y hy => ?_) hηη
      have := S.B_vanish hση hση h1 hx hy
      rwa [S.B_mulVec, S.adj_adj] at this
    have h3 : N * η = 0 := Matrix.ext_iff_mulVec.2 fun x => by
      rw [← Matrix.mulVec_mulVec, h2 _ (by rw [Matrix.mulVec_mulVec, hηη]), Matrix.zero_mulVec]
    have hneg : ∀ M : Matrix ι ι K, -M = M := fun M => by ext i j; simp [CharTwo.neg_eq]
    set ti := ((t⁻¹ : GL ι K) : Matrix ι ι K) with hti
    have h4 : (t : Matrix ι ι K) * η = ti * η := by
      rw [hN, S.adj_eq_inv t htU.1, add_mul, add_eq_zero_iff_eq_neg, hneg] at h3
      exact h3
    have hti1 : (t : Matrix ι ι K) * ti = 1 := by
      rw [hti, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h5 : (t : Matrix ι ι K) ^ 2 * η = η := by
      rw [pow_two, mul_assoc, h4, ← mul_assoc, hti1, one_mul]
    have h6 : ∀ k : ℕ, (t : Matrix ι ι K) ^ (2 * k) * η = η := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [mul_add, mul_one, pow_add, mul_assoc, h5, ih]
    obtain ⟨k, hk⟩ := S.hp.odd_of_ne_two S.hp2
    have htp' : (t : Matrix ι ι K) ^ S.p = 1 := by
      rw [← Units.val_pow_eq_pow_val, htp, Units.val_one]
    have h7 : (t : Matrix ι ι K) * η = η := by
      calc (t : Matrix ι ι K) * η = (t : Matrix ι ι K) * ((t : Matrix ι ι K) ^ (2 * k) * η) := by
            rw [h6 k]
        _ = (t : Matrix ι ι K) ^ S.p * η := by rw [hk, pow_succ', mul_assoc]
        _ = η := by rw [htp', one_mul]
    apply ht1
    refine Units.ext ?_
    calc (t : Matrix ι ι K) = t * η + t * (1 - η) := by noncomm_ring
      _ = ((1 : GL ι K) : Matrix ι ι K) := by
          rw [h7, show (t : Matrix ι ι K) * (1 - η) = 1 - η from hts, Units.val_one,
            add_sub_cancel]
  · obtain ⟨l, hlσ, hlτ⟩ := S.exists_fixed_tau_ne hτ1
    have h1 : ∀ v w, S.σ₀ ∘ v = v → η *ᵥ v = v → S.σ₀ ∘ w = w → η *ᵥ w = w →
        S.B v (1 *ᵥ w) = 0 := by
      intro v w hv hvη hw hwη
      rw [Matrix.one_mulVec]
      have e1 := hpol v w hv hvη hw hwη η hηA
      have hlv : S.σ₀ ∘ (l • v) = l • v := by
        funext a
        have := congrFun hv a
        simp only [Function.comp_apply] at this
        simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, hlσ, this]
      have hlvη : η *ᵥ (l • v) = l • v := by rw [Matrix.mulVec_smul, hvη]
      have e2 := hpol (l • v) w hlv hlvη hw hwη η hηA
      rw [hηa, hvη] at e1
      rw [hηa, hlvη, S.B_smul_left, map_mul, S.hτ] at e2
      have hβ : S.τ (S.B v w) = S.B v w := by
        rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at e1
        exact e1.symm
      rw [hβ, ← add_mul] at e2
      rcases mul_eq_zero.1 e2 with h | h
      · exfalso; apply hlτ
        rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
        exact h
      · exact h
    apply hη0
    refine Matrix.ext_iff_mulVec.2 fun x => ?_
    rw [Matrix.zero_mulVec]
    have hx : η *ᵥ (η *ᵥ x) = η *ᵥ x := by rw [Matrix.mulVec_mulVec, hηη]
    refine S.eq_zero_of_B_eta hηa hx (fun y hy => ?_) hηη
    have := S.B_vanish hση hση h1 hx hy
    rwa [Matrix.one_mulVec] at this

theorem exists_sa_idem_self {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {η : Matrix ι ι K} (hη : S.IsAtom η)
    (hηm : S.IsMinIdem η) {t : GL ι K}
    (htA : (t : Matrix ι ι K) ∈ S.A) (htU : S.Cent t) (htp : t ^ S.p = 1) (ht1 : t ≠ 1)
    (hts : SuppOn η t)
    (hC : ∃ c : Matrix ι ι K, (∀ e ∈ S.E₀, c * (e : Matrix ι ι K) = e * c) ∧ c * η ∉ S.A) :
    ∃ f : Matrix ι ι K, (∀ e ∈ S.E₀, f * (e : Matrix ι ι K) = e * f) ∧ f * f = f ∧
      S.adj f = f ∧ S.σ f = f ∧ f * η = f ∧ f ∉ S.A := by
  obtain ⟨v, hvσ, hvη, a₀, ha₀A, ha₀⟩ := S.exists_aniso hη htA htU htp ht1 hts
  obtain ⟨c, hc, hcη⟩ := hC
  have hv0 : v ≠ 0 := by rintro rfl; apply ha₀; rw [Matrix.mulVec_zero, S.B_zero_left]
  obtain ⟨x, hxη, hxv⟩ : ∃ x, η *ᵥ x = x ∧ ∀ a ∈ S.A, x ≠ a *ᵥ v := by
    by_contra H
    push Not at H
    exact hcη (S.mul_mem_A_of_cyclic hη.1 hη.2.1 hc hvη H)
  obtain ⟨hWA, hWσ, hWη⟩ := S.subAV_props hη.1 hvσ (u := 0) (by funext a; simp) hvη
    (Matrix.mulVec_zero η)
  refine S.sa_idem_of_sub hη (S.subAV v 0) hWA hWσ hWη ?_
    ⟨v, ⟨1, S.one_mem_A, 0, Submodule.zero_mem _, by simp⟩, hv0⟩ ⟨x, hxη, ?_⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩ hw
    rw [Matrix.mulVec_zero, add_zero] at hw ⊢
    by_contra hne
    have h0 : a * η ≠ 0 := fun h => hne (by
      rw [← hvη, Matrix.mulVec_mulVec, h, Matrix.zero_mulVec])
    obtain ⟨a', ha'A, ha'⟩ := S.minIdem_inv hηm ha h0
    have hv' : (a' * a) *ᵥ v = v := by rw [← hvη, Matrix.mulVec_mulVec, mul_assoc, ha']
    have hmem : S.adj a' *ᵥ (a₀ *ᵥ v) ∈ S.subAV v 0 :=
      ⟨S.adj a' * a₀, S.mul_mem_A (S.adj_mem_A ha'A).1 ha₀A, 0, Submodule.zero_mem _, by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_zero, add_zero]⟩
    have := hw _ hmem
    rw [← S.B_mulVec, Matrix.mulVec_mulVec, hv'] at this
    exact ha₀ this
  · rintro ⟨a, ha, b, hb, hxab⟩
    rw [Matrix.mulVec_zero, add_zero] at hxab
    exact hxv a ha hxab

theorem exists_sa_idem_pair {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {η ε₁ : Matrix ι ι K} (hη : S.IsAtom η)
    (h₁ : S.IsMinIdem ε₁) (h₂ : S.IsMinIdem (S.adj ε₁)) (h12 : ε₁ * S.adj ε₁ = 0)
    (hsum : ε₁ + S.adj ε₁ = η) {c : Matrix ι ι K}
    (hc : ∀ e ∈ S.E₀, c * (e : Matrix ι ι K) = e * c) (hcA : c * ε₁ ∉ S.A) :
    ∃ f : Matrix ι ι K, (∀ e ∈ S.E₀, f * (e : Matrix ι ι K) = e * f) ∧ f * f = f ∧
      S.adj f = f ∧ S.σ f = f ∧ f * η = f ∧ f ∉ S.A := by
  have hηa := hη.2.2.1
  have hηη := hη.2.1
  set ε₂ := S.adj ε₁ with hε₂
  have hε₁A := h₁.1
  have hε₁ε₁ := h₁.2.1
  have hε₁0 := h₁.2.2.1
  have hε₂A := h₂.1
  have hε₂ε₂ := h₂.2.1
  have h21 : ε₂ * ε₁ = 0 := (S.comm_A hε₂A hε₁A).trans h12
  have hadj₂ : S.adj ε₂ = ε₁ := S.adj_adj ε₁
  have hσ₁ := S.sigma_idempotent hε₁A hε₁ε₁
  have hσ₂ := S.sigma_idempotent hε₂A hε₂ε₂
  have hη₁ : ∀ x, ε₁ *ᵥ x = x → η *ᵥ x = x := fun x hx => by
    have : ε₂ *ᵥ x = 0 := by rw [← hx, Matrix.mulVec_mulVec, h21, Matrix.zero_mulVec]
    rw [← hsum, Matrix.add_mulVec, hx, this, add_zero]
  have hη₂ : ∀ x, ε₂ *ᵥ x = x → η *ᵥ x = x := fun x hx => by
    have : ε₁ *ᵥ x = 0 := by rw [← hx, Matrix.mulVec_mulVec, h12, Matrix.zero_mulVec]
    rw [← hsum, Matrix.add_mulVec, hx, this, zero_add]
  have hncyc : ∀ v, ε₁ *ᵥ v = v → ∃ x, ε₁ *ᵥ x = x ∧ ∀ a ∈ S.A, x ≠ a *ᵥ v := by
    intro v hv
    by_contra H
    push Not at H
    exact hcA (S.mul_mem_A_of_cyclic hε₁A hε₁ε₁ hc hv H)
  obtain ⟨v, hvσ, hv₁, hv0⟩ : ∃ v, S.σ₀ ∘ v = v ∧ ε₁ *ᵥ v = v ∧ v ≠ 0 := by
    by_contra H
    push Not at H
    apply hε₁0
    refine Matrix.ext_iff_mulVec.2 fun x => ?_
    have hx : ε₁ *ᵥ (ε₁ *ᵥ x) = ε₁ *ᵥ x := by rw [Matrix.mulVec_mulVec, hε₁ε₁]
    obtain ⟨c', T, hT, hTx⟩ := S.vec_descent hσ₁ hx
    rw [hTx, Matrix.zero_mulVec]
    exact Finset.sum_eq_zero fun l _ => by rw [H _ (hT l).1 (hT l).2, smul_zero]
  obtain ⟨u, huσ, hu₂, hvu⟩ : ∃ u, S.σ₀ ∘ u = u ∧ ε₂ *ᵥ u = u ∧ S.B v u ≠ 0 := by
    by_contra H
    push Not at H
    apply hv0
    refine S.eq_zero_of_B_eta hηa (hη₁ v hv₁) (fun y hy => ?_) hηη
    have hy' : y = ε₁ *ᵥ y + ε₂ *ᵥ y := by rw [← Matrix.add_mulVec, hsum, hy]
    have hy₂ : ε₂ *ᵥ (ε₂ *ᵥ y) = ε₂ *ᵥ y := by rw [Matrix.mulVec_mulVec, hε₂ε₂]
    rw [hy', S.B_add_right, S.B_iso hε₂.symm h21 hv₁ (by rw [Matrix.mulVec_mulVec, hε₁ε₁]),
      zero_add]
    obtain ⟨c', T, hT, hTy⟩ := S.vec_descent hσ₂ hy₂
    rw [hTy, S.B_sum_right]
    exact Finset.sum_eq_zero fun l _ => by rw [S.B_smul_right, H _ (hT l).1 (hT l).2, mul_zero]
  obtain ⟨hWA, hWσ, hWη⟩ := S.subAV_props hη.1 hvσ huσ (hη₁ v hv₁) (hη₂ u hu₂)
  have hnd : ∀ w ∈ S.subAV v u, (∀ w' ∈ S.subAV v u, S.B w' w = 0) → w = 0 := by
    rintro _ ⟨a, ha, b, hb, rfl⟩ hw
    have hav : a *ᵥ v = 0 := by
      by_contra hne
      have h0 : a * ε₁ ≠ 0 := fun h => hne (by
        rw [← hv₁, Matrix.mulVec_mulVec, h, Matrix.zero_mulVec])
      obtain ⟨a', ha'A, ha'⟩ := S.minIdem_inv h₁ ha h0
      have hmem : S.adj a' *ᵥ u ∈ S.subAV v u :=
        ⟨0, Submodule.zero_mem _, S.adj a', (S.adj_mem_A ha'A).1, by
          rw [Matrix.zero_mulVec, zero_add]⟩
      have hv' : (a' * a) *ᵥ v = v := by rw [← hv₁, Matrix.mulVec_mulVec, mul_assoc, ha']
      have e1 : S.B (S.adj a' *ᵥ u) (a *ᵥ v) = S.B u v := by
        rw [← S.B_mulVec, Matrix.mulVec_mulVec, hv']
      have e2 : S.B (S.adj a' *ᵥ u) (b *ᵥ u) = 0 :=
        S.B_iso hadj₂ h12 (S.mulVec_comm_fix (S.adj_mem_A ha'A).1 hε₂A hu₂)
          (S.mulVec_comm_fix hb hε₂A hu₂)
      have := hw _ hmem
      rw [S.B_add_right, e1, e2, add_zero] at this
      exact hvu (by rw [S.B_symm u v, this, map_zero])
    have hbu : b *ᵥ u = 0 := by
      by_contra hne
      have h0 : b * ε₂ ≠ 0 := fun h => hne (by
        rw [← hu₂, Matrix.mulVec_mulVec, h, Matrix.zero_mulVec])
      obtain ⟨b', hb'A, hb'⟩ := S.minIdem_inv h₂ hb h0
      have hmem : S.adj b' *ᵥ v ∈ S.subAV v u :=
        ⟨S.adj b', (S.adj_mem_A hb'A).1, 0, Submodule.zero_mem _, by
          rw [Matrix.zero_mulVec, add_zero]⟩
      have hu' : (b' * b) *ᵥ u = u := by rw [← hu₂, Matrix.mulVec_mulVec, mul_assoc, hb']
      have e1 : S.B (S.adj b' *ᵥ v) (b *ᵥ u) = S.B v u := by
        rw [← S.B_mulVec, Matrix.mulVec_mulVec, hu']
      have e2 : S.B (S.adj b' *ᵥ v) (a *ᵥ v) = 0 :=
        S.B_iso hε₂.symm h21 (S.mulVec_comm_fix (S.adj_mem_A hb'A).1 hε₁A hv₁)
          (S.mulVec_comm_fix ha hε₁A hv₁)
      have := hw _ hmem
      rw [S.B_add_right, e1, e2, zero_add] at this
      exact hvu this
    rw [hav, hbu, add_zero]
  obtain ⟨x, hx₁, hxv⟩ := hncyc v hv₁
  refine S.sa_idem_of_sub hη (S.subAV v u) hWA hWσ hWη hnd
    ⟨v, ⟨1, S.one_mem_A, 0, Submodule.zero_mem _, by simp⟩, hv0⟩ ⟨x, hη₁ x hx₁, ?_⟩
  rintro ⟨a, ha, b, hb, hxab⟩
  have hu₁ : ε₁ *ᵥ u = 0 := by rw [← hu₂, Matrix.mulVec_mulVec, h12, Matrix.zero_mulVec]
  apply hxv a ha
  calc x = ε₁ *ᵥ x := hx₁.symm
    _ = ε₁ *ᵥ (a *ᵥ v) + ε₁ *ᵥ (b *ᵥ u) := by rw [hxab, Matrix.mulVec_add]
    _ = a *ᵥ v := by
        rw [S.mulVec_comm_fix ha hε₁A hv₁, Matrix.mulVec_mulVec, S.comm_A hε₁A hb,
          ← Matrix.mulVec_mulVec, hu₁, Matrix.mulVec_zero, add_zero]

theorem exists_sa_idempotent_aux {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {η : Matrix ι ι K} (hη : S.IsAtom η)
    {t : GL ι K} (htA : (t : Matrix ι ι K) ∈ S.A) (htU : S.Cent t) (htp : t ^ S.p = 1)
    (ht1 : t ≠ 1) (hts : SuppOn η t)
    (hC : ∃ c : Matrix ι ι K, (∀ e ∈ S.E₀, c * (e : Matrix ι ι K) = e * c) ∧ c * η ∉ S.A) :
    ∃ f : Matrix ι ι K, (∀ e ∈ S.E₀, f * (e : Matrix ι ι K) = e * f) ∧ f * f = f ∧
      S.adj f = f ∧ S.σ f = f ∧ f * η = f ∧ f ∉ S.A := by
  obtain ⟨ε, hε, hεη⟩ := S.exists_minIdem hη.1 hη.2.1 hη.2.2.2.1
  rcases S.minIdem_cases hη hε hεη with rfl | ⟨h12, hsum⟩
  · exact S.exists_sa_idem_self hη hε htA htU htp ht1 hts hC
  · obtain ⟨c, hc, hcη⟩ := hC
    by_cases h1 : c * ε ∈ S.A
    · have h2 : c * S.adj ε ∉ S.A := fun h2 => hcη (by
        rw [← hsum, mul_add]; exact Submodule.add_mem _ h1 h2)
      refine S.exists_sa_idem_pair hη (S.adj_minIdem hε) (by rw [S.adj_adj]; exact hε) ?_ ?_
        hc h2
      · rw [S.adj_adj, S.comm_A (S.adj_minIdem hε).1 hε.1, h12]
      · rw [S.adj_adj, add_comm, hsum]
    · exact S.exists_sa_idem_pair hη hε (S.adj_minIdem hε) h12 hsum hc h1

theorem exists_sa_idempotent {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {η : Matrix ι ι K} (hη : S.IsAtom η) {t : GL ι K}
    (htA : (t : Matrix ι ι K) ∈ S.A) (htU : S.Cent t) (htp : t ^ S.p = 1) (ht1 : t ≠ 1)
    (hts : SuppOn η t)
    (hC : ∃ c : Matrix ι ι K, (∀ e ∈ S.E₀, c * (e : Matrix ι ι K) = e * c) ∧ c * η ∉ S.A) :
    ∃ f : Matrix ι ι K, (∀ e ∈ S.E₀, f * (e : Matrix ι ι K) = e * f) ∧ f * f = f ∧
      S.adj f = f ∧ S.σ f = f ∧ f * η = f ∧ f ∉ S.A :=
  S.exists_sa_idempotent_aux hη htA htU htp ht1 hts hC

theorem exists_orderP_not_mem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {η : Matrix ι ι K} (hη : S.IsAtom η) {t : GL ι K}
    (htA : (t : Matrix ι ι K) ∈ S.A) (htU : S.Cent t) (htp : t ^ S.p = 1) (ht1 : t ≠ 1)
    (hts : SuppOn η t) (htσ : S.σGL t = t) {f : Matrix ι ι K}
    (hfc : ∀ e ∈ S.E₀, f * (e : Matrix ι ι K) = e * f) (hff : f * f = f) (hfa : S.adj f = f)
    (hfσ : S.σ f = f) (hfη : f * η = f) (hfA : f ∉ S.A) :
    ∃ t' : GL ι K, (t' : Matrix ι ι K) = t * f + (1 - f) ∧ S.Cent t' ∧ t' ^ S.p = 1 ∧
      S.σGL t' = t' ∧ SuppOn η t' ∧ (t' : Matrix ι ι K) ∉ S.A := by
  have hηA := hη.1
  have hηη := hη.2.1
  obtain ⟨w, hwA, hw⟩ := S.exists_inv_sub_one hη htA htU htp ht1 hts
  have htf : (t : Matrix ι ι K) * f = f * t := (commute_of_mem_spanE S.E₀ hfc htA).symm
  have htif : ((t⁻¹ : GL ι K) : Matrix ι ι K) * f = f * ((t⁻¹ : GL ι K) : Matrix ι ι K) := by
    have hmem : ((t⁻¹ : GL ι K) : Matrix ι ι K) ∈ S.A := by
      rw [← S.adj_eq_inv t htU.1]; exact (S.adj_mem_A htA).1
    exact (commute_of_mem_spanE S.E₀ hfc hmem).symm
  let t' : GL ι K := ⟨t * f + (1 - f), ((t⁻¹ : GL ι K) : Matrix ι ι K) * f + (1 - f),
    by rw [block_mul hff htif, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul,
      add_sub_cancel],
    by rw [block_mul hff htf, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul,
      add_sub_cancel]⟩
  have hηf : η * f = f := by rw [← commute_of_mem_spanE S.E₀ hfc hηA, hfη]
  refine ⟨t', rfl, ⟨?_, fun e he => ?_⟩, ?_, ?_, ?_, fun h => hfA ?_⟩
  · show S.adj ((t : Matrix ι ι K) * f + (1 - f)) * ((t : Matrix ι ι K) * f + (1 - f)) = 1
    rw [S.adj_add, S.adj_sub, S.adj_mul, S.adj_one, hfa, S.adj_eq_inv t htU.1, ← htif,
      block_mul hff htf, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, add_sub_cancel]
  · have hte : (t : Matrix ι ι K) * e = e * t := by
      have := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) (htU.2 e he); simpa using this
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
  · show ((t : Matrix ι ι K) * f + (1 - f)) * (1 - η) = 1 - η
    calc ((t : Matrix ι ι K) * f + (1 - f)) * (1 - η)
        = (t : Matrix ι ι K) * (f - f * η) + (1 - η - (f - f * η)) := by noncomm_ring
      _ = 1 - η := by rw [hfη, sub_self, mul_zero, zero_add, sub_zero]
  · have h1 : f = w * ((t : Matrix ι ι K) * f + (1 - f) - 1) := by
      calc f = η * f := hηf.symm
        _ = w * (((t : Matrix ι ι K) - 1) * η) * f := by rw [hw]
        _ = w * (((t : Matrix ι ι K) - 1) * (η * f)) := by noncomm_ring
        _ = w * ((t : Matrix ι ι K) * f + (1 - f) - 1) := by rw [hηf]; noncomm_ring
    rw [h1]; exact S.mul_mem_A hwA (Submodule.sub_mem _ h S.one_mem_A)

structure GoodGroup {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (H : Subgroup (GL ι K)) : Prop where
  cent : ∀ g ∈ H, S.adj (g : Matrix ι ι K) * g = 1
  sigma : ∀ g ∈ H, S.σGL g ∈ H
  block : ∀ η, S.IsAtom η → ∀ y ∈ H, S.Cent y → ∀ z : GL ι K,
    (z : Matrix ι ι K) = y * η + (1 - η) → z ∈ H
  tprime : ∀ η, S.IsAtom η → ∀ t ∈ H, (t : Matrix ι ι K) ∈ S.A → S.Cent t → t ^ S.p = 1 →
    t ≠ 1 → SuppOn η t → ∀ t' : GL ι K, S.Cent t' → SuppOn η t' → t' ∈ H
  spanIso : ∀ g : GL ι K, (g : Matrix ι ι K) ∈ S.A → S.adj (g : Matrix ι ι K) * g = 1 → g ∈ H

@[expose] def Sat {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (H : Subgroup (GL ι K)) : Prop :=
  ∀ y ∈ H, S.Cent y → y ^ S.p = 1 → S.σGL y = y → (y : Matrix ι ι K) ∈ S.A

def suppGroup {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (H : Subgroup (GL ι K)) {η : Matrix ι ι K} (_hη : S.IsAtom η) :
    Subgroup (GL ι K) where
  carrier := {g | g ∈ H ∧ S.Cent g ∧ SuppOn η g}
  one_mem' := ⟨H.one_mem, ⟨by simp [S.adj_one], fun e _ => by simp⟩, by simp [SuppOn]⟩
  mul_mem' := by
    rintro g h ⟨hg, ⟨hga, hgc⟩, hgs⟩ ⟨hh, ⟨hha, hhc⟩, hhs⟩
    refine ⟨H.mul_mem hg hh, ⟨?_, fun e he => ?_⟩, ?_⟩
    · rw [Units.val_mul, S.adj_mul, show S.adj (h : Matrix ι ι K) * S.adj (g : Matrix ι ι K) *
        ((g : Matrix ι ι K) * h) = S.adj (h : Matrix ι ι K) * (S.adj (g : Matrix ι ι K) * g) * h
        by noncomm_ring, hga, mul_one, hha]
    · rw [mul_assoc, hhc e he, ← mul_assoc, hgc e he, mul_assoc]
    · unfold SuppOn at *; rw [Units.val_mul, mul_assoc, hhs, hgs]
  inv_mem' := by
    rintro g ⟨hg, ⟨hga, hgc⟩, hgs⟩
    refine ⟨H.inv_mem hg, ⟨?_, S.cent_inv hgc⟩, ?_⟩
    · have h1 : S.adj ((g⁻¹ : GL ι K) : Matrix ι ι K) * S.adj (g : Matrix ι ι K) = 1 := by
        rw [← S.adj_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, S.adj_one]
      calc S.adj ((g⁻¹ : GL ι K) : Matrix ι ι K) * ((g⁻¹ : GL ι K) : Matrix ι ι K)
          = S.adj ((g⁻¹ : GL ι K) : Matrix ι ι K) * S.adj (g : Matrix ι ι K) := by
            rw [S.adj_eq_inv g hga]
        _ = 1 := h1
    · unfold SuppOn at *
      calc ((g⁻¹ : GL ι K) : Matrix ι ι K) * (1 - η)
          = ((g⁻¹ : GL ι K) : Matrix ι ι K) * ((g : Matrix ι ι K) * (1 - η)) := by rw [hgs]
        _ = 1 - η := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem sigma_mem_supp {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {H : Subgroup (GL ι K)} (hH : S.GoodGroup H) {η : Matrix ι ι K}
    (hη : S.IsAtom η) {g : GL ι K} (hg : g ∈ S.suppGroup H hη) :
    S.σGL g ∈ S.suppGroup H hη := by
  obtain ⟨hgH, ⟨hga, hgc⟩, hgs⟩ := hg
  have hgs' : (g : Matrix ι ι K) * (1 - η) = 1 - η := hgs
  have hση : S.σ (1 - η) = 1 - η := by rw [map_sub, map_one, S.sigma_idempotent hη.1 hη.2.1]
  refine ⟨hH.sigma g hgH, ⟨S.adj_sigma_mul hga, fun e he => ?_⟩, ?_⟩
  · have hσe : S.σGL e = e := Units.ext (S.hEfix e he)
    calc S.σGL g * e = S.σGL g * S.σGL e := by rw [hσe]
      _ = S.σGL (g * e) := (map_mul _ _ _).symm
      _ = S.σGL (e * g) := by rw [hgc e he]
      _ = e * S.σGL g := by rw [map_mul, hσe]
  · show S.σ (g : Matrix ι ι K) * (1 - η) = 1 - η
    calc S.σ (g : Matrix ι ι K) * (1 - η) = S.σ (g : Matrix ι ι K) * S.σ (1 - η) := by rw [hση]
      _ = S.σ ((g : Matrix ι ι K) * (1 - η)) := (map_mul _ _ _).symm
      _ = 1 - η := by rw [hgs', hση]

theorem pElt_mem_A_of_atom {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {H : Subgroup (GL ι K)} (hH : S.GoodGroup H) (hSat : S.Sat H)
    {η : Matrix ι ι K} (hη : S.IsAtom η) {z : GL ι K} (hzH : z ∈ H) (hz : S.Cent z)
    (hzs : SuppOn η z) (hzp : ∃ k : ℕ, z ^ S.p ^ k = 1) : (z : Matrix ι ι K) ∈ S.A := by
  have hzs' : (z : Matrix ι ι K) * (1 - η) = 1 - η := hzs
  by_cases hC : ∃ c : Matrix ι ι K, (∀ e ∈ S.E₀, c * (e : Matrix ι ι K) = e * c) ∧ c * η ∉ S.A
  swap
  · push Not at hC
    have hzc : ∀ e ∈ S.E₀, (z : Matrix ι ι K) * (e : Matrix ι ι K) = e * z := fun e he => by
      have := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) (hz.2 e he); simpa using this
    have hzeq : (z : Matrix ι ι K) = z * η + (1 - η) := by rw [← hzs']; noncomm_ring
    rw [hzeq]; exact Submodule.add_mem _ (hC _ hzc) (Submodule.sub_mem _ S.one_mem_A hη.1)
  by_contra hzA
  haveI : Finite (GL ι K) := Finite.of_injective (fun u : GL ι K => (u : Matrix ι ι K)) fun _ _ h => Units.ext h
  set X := S.suppGroup H hη
  let φ : X →* X :=
    { toFun := fun x => ⟨S.σGL (x : GL ι K), S.sigma_mem_supp hH hη x.2⟩
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
  have hzX : z ∈ X := ⟨hzH, hz, hzs⟩
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
  have htH : t ∈ H := x.2.1
  have htC : S.Cent t := x.2.2.1
  have hts : SuppOn η t := x.2.2.2
  have htp : t ^ S.p = 1 := by
    rw [ht, ← Subgroup.coe_pow, ← hxo, pow_orderOf_eq_one, Subgroup.coe_one]
  have ht1 : t ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hxo
    exact S.hp.one_lt.ne hxo
  have htσ : S.σGL t = t := congrArg Subtype.val hxα
  have htA := hSat t htH htC htp htσ
  obtain ⟨f, hfc, hff, hfa, hfσ, hfη, hfA⟩ := S.exists_sa_idempotent hη htA htC htp ht1 hts hC
  obtain ⟨t', -, ht'C, ht'p, ht'σ, ht's, ht'A⟩ :=
    S.exists_orderP_not_mem hη htA htC htp ht1 hts htσ hfc hff hfa hfσ hfη hfA
  exact ht'A (hSat t' (hH.tprime η hη t htH htA htC htp ht1 hts t' ht'C ht's) ht'C ht'p ht'σ)

theorem pElt_mem_A {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {H : Subgroup (GL ι K)} (hH : S.GoodGroup H) (hSat : S.Sat H) {y : GL ι K}
    (hyH : y ∈ H) (hy : S.Cent y) (hyp : ∃ k : ℕ, y ^ S.p ^ k = 1) :
    (y : Matrix ι ι K) ∈ S.A := by
  obtain ⟨r, η, hat, -, hsum⟩ := S.exists_atoms
  obtain ⟨k, hk⟩ := hyp
  have hmem : ∀ i, (y : Matrix ι ι K) * η i ∈ S.A := fun i => by
    obtain ⟨z, hz, hzC, hzs, hzpow, -⟩ := S.blockPart (hat i) hy
    have hzA := S.pElt_mem_A_of_atom hH hSat (hat i) (hH.block (η i) (hat i) y hyH hy z hz) hzC
      hzs ⟨k, hzpow _ hk⟩
    have hηη := (hat i).2.1
    have : (y : Matrix ι ι K) * η i = z * η i := by
      rw [hz, add_mul, mul_assoc, hηη, sub_mul, one_mul, hηη, sub_self, add_zero]
    rw [this]; exact S.mul_mem_A hzA (hat i).1
  rw [← mul_one (y : Matrix ι ι K), ← hsum, Finset.mul_sum]
  exact Submodule.sum_mem _ fun i _ => hmem i

theorem goodGroup_U {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] (U : Subgroup (GL ι K))
    (hU : ∀ g : GL ι K, g ∈ U ↔ S.adj (g : Matrix ι ι K) * g = 1) : S.GoodGroup U := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg; exact (hU g).1 hg
  · intro g hg; exact (hU _).2 (S.adj_sigma_mul ((hU g).1 hg))
  · intro η hη y _ hy z hz
    exact (hU z).2 (by rw [hz]; exact S.adj_block_mul hη.1 hη.2.1 hη.2.2.1 hy)
  · intro η hη t _ _ _ _ _ _ t' ht' _
    exact (hU t').2 ht'.1
  · intro g _ hg; exact (hU g).2 hg

@[expose] def CentP {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) (H : Subgroup (GL ι K)) (g : GL ι K) : Prop :=
  g ∈ H ∧ S.Cent g ∧ ∃ k : ℕ, g ^ S.p ^ k = 1

theorem matrix_core {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (S : ClSetting K ι) [Fintype K] [CharP K 2] {H : Subgroup (GL ι K)} (hH : S.GoodGroup H) (hSat : S.Sat H)
    (hEH : ∀ e ∈ S.E₀, e ∈ H) (hcard : S.p ^ 2 ≤ Nat.card S.E₀) :
    ∃ s : ℕ, 2 ≤ s ∧ ∃ k : ℕ, ¬ S.p ∣ k ∧
      (∀ x y, S.CentP H x → S.CentP H y → x * y = y * x) ∧
      (∀ x, S.CentP H x → x ^ S.p ^ s = 1 ∧
        S.σGL x = x ^ (1 + (S.p : ℤ) ^ (s - 1) * k)) ∧
      (∀ x, S.CentP H x → ∀ w ∈ H, S.Cent w → w * x = x * w) ∧
      ∃ a₁ a₂ : GL ι K, S.CentP H a₁ ∧ S.CentP H a₂ ∧
        a₁ ^ S.p ^ (s - 1) ∈ S.E₀ ∧ a₂ ^ S.p ^ (s - 1) ∈ S.E₀ ∧
        ∀ i j : ℕ, (a₁ ^ S.p ^ (s - 1)) ^ i * (a₂ ^ S.p ^ (s - 1)) ^ j = 1 → S.p ∣ i ∧ S.p ∣ j := by
  haveI := Fact.mk S.hp
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  obtain ⟨a, ha⟩ := exists_pow_two_of_ringEquiv S.σ₀
  have hσp : S.σ₀ ^ S.p = 1 := S.hσ₀ ▸ pow_orderOf_eq_one S.σ₀
  have hiter : ∀ k (c : K), (S.σ₀ ^ k) c = c ^ 2 ^ (a * k) := by
    intro k
    induction k with
    | zero => intro c; simp
    | succ k ih =>
      intro c
      rw [pow_succ']
      change S.σ₀ ((S.σ₀ ^ k) c) = _
      rw [ih, map_pow, ha, ← pow_mul, ← pow_add, Nat.mul_succ, add_comm]
  have hfix : ∀ c : K, c ^ 2 ^ (a * S.p) = c := fun c => by rw [← hiter, hσp]; rfl
  have hap : (n : ℕ) ∣ a * S.p := dvd_of_forall_pow_two_pow_eq hn hfix
  have hna : ¬ (n : ℕ) ∣ a := by
    rintro ⟨j, hj⟩
    have h1 : S.σ₀ = 1 := RingEquiv.ext fun c => by
      show S.σ₀ c = c
      rw [ha, hj, pow_mul, ← hn]; exact FiniteField.pow_card_pow j c
    have h2 := S.hσ₀
    rw [h1, orderOf_one] at h2
    exact S.hp.one_lt.ne h2
  set d := orderOf (((2 ^ (n : ℕ) : ℕ)) : ZMod S.p) with hd
  set s := padicValNat S.p ((2 ^ (n : ℕ)) ^ d - 1) with hs
  obtain ⟨hs2, k, hk, hN⟩ := power_class S.hp S.hp2 hap hna hd hs
  have hA : ∀ x, S.CentP H x → (x : Matrix ι ι K) ∈ S.A := fun x hx =>
    S.pElt_mem_A hH hSat hx.1 hx.2.1 hx.2.2
  have hd0 : d ≠ 0 := by
    have h2 : ¬ S.p ∣ 2 ^ (n : ℕ) := fun h => S.hp2
      ((Nat.prime_dvd_prime_iff_eq S.hp Nat.prime_two).1 (S.hp.dvd_of_dvd_pow h))
    have : ((2 ^ (n : ℕ) : ℕ) : ZMod S.p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact h2
    exact (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨S.p - 1, by have := S.hp.two_le; omega,
      ZMod.pow_card_sub_one_eq_one this⟩)).ne'
  have hQ : ∀ M ∈ S.A, M ^ 2 ^ ((n : ℕ) * d) = M := by
    refine pow_eq_self_of_mem_spanE S.E₀ S.hE.1 S.hE.2 (fun c => ?_) ?_
    · rw [pow_mul, ← hn]; exact FiniteField.pow_card_pow d c
    · rw [← ZMod.natCast_eq_natCast_iff, pow_mul, Nat.cast_pow (2 ^ (n : ℕ)), hd]
      push_cast
      rw [← Nat.cast_ofNat, ← Nat.cast_pow, pow_orderOf_eq_one]
  have hexp : ∀ x, S.CentP H x → x ^ S.p ^ s = 1 := by
    intro x hx
    obtain ⟨j, hj⟩ := hx.2.2
    have hxQ : x ^ (2 ^ ((n : ℕ) * d) - 1) = 1 := by
      have h1 : x ^ (2 ^ ((n : ℕ) * d) - 1) * x = x := by
        rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
        exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hQ _ (hA x hx))
      simpa using h1
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow S.hp).1 (orderOf_dvd_of_pow_eq_one hj)
    have hne : 2 ^ ((n : ℕ) * d) - 1 ≠ 0 := by
      have : 1 < 2 ^ ((n : ℕ) * d) := Nat.one_lt_two_pow (mul_ne_zero n.ne_zero hd0)
      omega
    have hpi : S.p ^ i ∣ 2 ^ ((n : ℕ) * d) - 1 := hi ▸ orderOf_dvd_of_pow_eq_one hxQ
    rw [padicValNat_dvd_iff_le hne, pow_mul] at hpi
    exact orderOf_dvd_iff_pow_eq_one.1 (hi ▸ pow_dvd_pow S.p hpi)
  refine ⟨s, hs2, k, hk, fun x y hx hy => Units.ext ?_, fun x hx => ⟨hexp x hx, ?_⟩,
    fun x hx w _ hw => Units.ext ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]; exact S.comm_A (hA x hx) (hA y hy)
  ·
    have hmod : 2 ^ (a * S.p) ≡ 2 ^ a [MOD S.p] := by
      rw [← ZMod.natCast_eq_natCast_iff, pow_mul, Nat.cast_pow, ZMod.pow_card]
    have hA2 := semilinear_pow_eq S.E₀ S.hE.1 S.hE.2 S.σ S.σ₀
      (fun c M => by ext i j; simp [σ, RingEquiv.mapMatrix_apply, Matrix.map_apply])
      (fun e he => S.hEfix e he) ha hfix hmod (x : Matrix ι ι K) (hA x hx)
    have hA2' : (S.σGL x) ^ 2 ^ (a * S.p) = x ^ 2 ^ a := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]; exact hA2)
    have hcop : Nat.Coprime (2 ^ (a * S.p)) (S.p ^ s) := Nat.Coprime.pow _ _
      ((Nat.coprime_primes Nat.prime_two S.hp).2 (Ne.symm S.hp2))
    have hps : 1 < S.p ^ s := Nat.one_lt_pow (by omega) S.hp.one_lt
    obtain ⟨M, -, hM⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hps
    have hM' : 2 ^ (a * S.p) * M ≡ 1 [MOD S.p ^ s] := by
      rw [Nat.ModEq, hM, Nat.mod_eq_of_lt hps]
    have hNmod : 2 ^ a * M * 2 ^ (a * S.p) ≡ 2 ^ a [MOD S.p ^ s] := by
      have := Nat.ModEq.mul_left (2 ^ a) hM'
      rw [mul_one] at this
      rwa [mul_assoc, mul_comm M]
    have hσx : (S.σGL x) ^ S.p ^ s = 1 := by rw [← map_pow, hexp x hx, map_one]
    have hpow : S.σGL x = x ^ (1 + S.p ^ (s - 1) * k) := by
      calc S.σGL x = (S.σGL x) ^ 1 := (pow_one _).symm
        _ = (S.σGL x) ^ (2 ^ (a * S.p) * M) := pow_eq_pow_of_modEq' hσx hM'.symm
        _ = x ^ (2 ^ a * M) := by rw [pow_mul, hA2', ← pow_mul]
        _ = x ^ (1 + S.p ^ (s - 1) * k) := pow_eq_pow_of_modEq' (hexp x hx) (hN _ hNmod)
    rw [hpow]; exact_mod_cast (zpow_natCast x (1 + S.p ^ (s - 1) * k)).symm
  · rw [Units.val_mul, Units.val_mul]; exact S.comm_of_cent hw.2 (hA x hx)
  · obtain ⟨e₁, he₁, e₂, he₂, hind⟩ := exists_indep S.hp S.E₀ S.hE.2 hcard
    have hroot : ∀ e ∈ S.E₀, ∃ c : GL ι K, S.CentP H c ∧ c ^ S.p ^ (s - 1) = e := by
      intro e he
      obtain ⟨c, hcA, hcU, hce, hcs⟩ := exists_pow_eq_of_pow_eq_one_adj (q := 2 ^ (n : ℕ)) S.hp
        S.hp2 hn hd hs S.τ S.hτ S.G S.hG S.hGs S.E₀ S.hE.1 S.hE.2 S.hEU
        e (S.mem_A_of_mem he) (S.hE.2 e he) (S.hEU e he)
      refine ⟨c, ⟨hH.spanIso c hcA hcU, ⟨hcU, fun e' he' => Units.ext ?_⟩, ⟨s, hcs⟩⟩, hce⟩
      rw [Units.val_mul, Units.val_mul]; exact S.comm_A hcA (S.mem_A_of_mem he')
    obtain ⟨a₁, ha₁, h₁⟩ := hroot e₁ he₁
    obtain ⟨a₂, ha₂, h₂⟩ := hroot e₂ he₂
    exact ⟨a₁, a₂, ha₁, ha₂, by rw [h₁]; exact he₁, by rw [h₂]; exact he₂,
      fun i j h => hind i j (by rw [← h₁, ← h₂]; exact h)⟩

end ClSetting

end CFSG.HardMathSupport.C14Cl
