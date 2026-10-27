module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.C14Cl

open Matrix

@[expose] def spanE (K : Type) [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (E₀ : Subgroup (GL ι K)) : Submodule K (Matrix ι ι K) :=
  Submodule.span K (Set.range fun e : E₀ => ((e : GL ι K) : Matrix ι ι K))

theorem spanE_mul_mem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (E₀ : Subgroup (GL ι K)) {M N : Matrix ι ι K}
    (hM : M ∈ spanE K E₀) (hN : N ∈ spanE K E₀) : M * N ∈ spanE K E₀ := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    induction hN using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, rfl⟩ := hy
      exact Submodule.subset_span ⟨e * f, by simp⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem commute_of_mem_spanE {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (E₀ : Subgroup (GL ι K)) {C : Matrix ι ι K}
    (hC : ∀ e ∈ E₀, C * (e : Matrix ι ι K) = (e : Matrix ι ι K) * C) {M : Matrix ι ι K}
    (hM : M ∈ spanE K E₀) : C * M = M * C := by
  induction hM using Submodule.span_induction with
  | mem x hx => obtain ⟨e, rfl⟩ := hx; exact hC e e.2
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, add_mul, hx, hy]
  | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc, hx]

theorem spanE_commute {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (E₀ : Subgroup (GL ι K)) (hE : IsMulCommutative E₀) {M N : Matrix ι ι K}
    (hM : M ∈ spanE K E₀) (hN : N ∈ spanE K E₀) : M * N = N * M := by
  refine (commute_of_mem_spanE E₀ (C := N) (fun e he => ?_) hM).symm
  induction hN using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, rfl⟩ := hx
    have h := congrArg (fun g : E₀ => ((g : GL ι K) : Matrix ι ι K))
      (hE.is_comm.comm ⟨e, he⟩ f)
    simpa using h.symm
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, add_mul, hx, hy]
  | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc, hx]

theorem semilinear_pow_eq {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    [CharP K 2] {p a b : ℕ} (E₀ : Subgroup (GL ι K))
    (hE : IsMulCommutative E₀) (hexp : ∀ e ∈ E₀, e ^ p = 1)
    (σ : Matrix ι ι K ≃+* Matrix ι ι K) (σ₀ : K ≃+* K)
    (hσ : ∀ (c : K) (M : Matrix ι ι K), σ (c • M) = σ₀ c • σ M)
    (hfix : ∀ e ∈ E₀, σ (e : Matrix ι ι K) = e)
    (hr : ∀ c, σ₀ c = c ^ 2 ^ a) (hm : ∀ c : K, c ^ 2 ^ b = c) (hmod : 2 ^ b ≡ 2 ^ a [MOD p]) :
    ∀ M ∈ spanE K E₀, σ M ^ 2 ^ b = M ^ 2 ^ a := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · intro M _; exact Subsingleton.elim _ _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσmem : ∀ M ∈ spanE K E₀, σ M ∈ spanE K E₀ := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx => obtain ⟨e, rfl⟩ := hx; rw [hfix e e.2]; exact Submodule.subset_span ⟨e, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [hσ]; exact Submodule.smul_mem _ _ hx
  intro M hM
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    simp only
    rw [hfix e e.2, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
    congr 1
    rw [pow_eq_pow_iff_modEq]
    exact Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one (by
      have := hexp e e.2; exact this)) hmod
  | zero => simp
  | add x y hx hy ihx ihy =>
    have h1 : Commute (σ x) (σ y) := spanE_commute E₀ hE (hσmem x hx) (hσmem y hy)
    have h2 : Commute x y := spanE_commute E₀ hE hx hy
    rw [map_add, add_pow_char_pow_of_commute (p := 2) (h := h1),
      add_pow_char_pow_of_commute (p := 2) (h := h2), ihx, ihy]
  | smul c x _ ih =>
    rw [hσ, smul_pow, smul_pow, ih, hm, hr]

theorem pow_eq_self_of_mem_spanE {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    [CharP K 2] {p b : ℕ} (E₀ : Subgroup (GL ι K))
    (hE : IsMulCommutative E₀) (hexp : ∀ e ∈ E₀, e ^ p = 1)
    (hm : ∀ c : K, c ^ 2 ^ b = c) (hmod : 2 ^ b ≡ 1 [MOD p]) :
    ∀ M ∈ spanE K E₀, M ^ 2 ^ b = M := by
  intro M hM
  have h := semilinear_pow_eq (a := 0) (b := b) E₀ hE hexp (RingEquiv.refl _) (RingEquiv.refl K)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun c => by simp) hm (by simpa using hmod) M hM
  simpa using h

theorem field_root {F : Type*} [Field F] [Finite F] {p s : ℕ} (hp : p.Prime) (hs : 1 ≤ s) (u : F)
    (hu : u ^ p = 1) (hpF : u ≠ 1 → p ^ s ∣ Nat.card F - 1) :
    ∃ c : F, c ^ p ^ (s - 1) = u ∧ c ^ p ^ s = 1 := by
  by_cases hu1 : u = 1
  · exact ⟨1, by simp [hu1], by simp⟩
  have hu0 : u ≠ 0 := by rintro rfl; rw [zero_pow hp.ne_zero] at hu; exact zero_ne_one hu
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Fˣ)
  have hord : orderOf g = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_powers hg, Nat.card_units]
  obtain ⟨j, hj⟩ := hg (Units.mk0 u hu0)
  obtain ⟨M, hM⟩ := hpF hu1
  have hjp : orderOf g ∣ j * p := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul]
    simp only at hj
    rw [hj]; exact Units.ext (by simp [hu])
  rw [hord, hM, show p ^ s * M = p ^ (s - 1) * M * p by
    rw [mul_right_comm, ← pow_succ, Nat.sub_add_cancel hs]] at hjp
  obtain ⟨i, hi⟩ := Nat.dvd_of_mul_dvd_mul_right hp.pos hjp
  refine ⟨((g ^ (M * i) : Fˣ) : F), ?_, ?_⟩
  · simp only at hj
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, show M * i * p ^ (s - 1) = j by rw [hi]; ring, hj,
      Units.val_mk0]
  · rw [← Units.val_pow_eq_pow_val, ← pow_mul, show M * i * p ^ s = (p ^ s * M) * i by ring, ← hM,
      ← hord, pow_mul, pow_orderOf_eq_one, one_pow, Units.val_one]

theorem exists_pow_eq_of_pow_eq_one {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    [Fintype K] [CharP K 2] {p q d s : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : Fintype.card K = q) (hd : d = orderOf (q : ZMod p))
    (hs : s = padicValNat p (q ^ d - 1)) (E₀ : Subgroup (GL ι K)) (hE : IsMulCommutative E₀)
    (hexp : ∀ e ∈ E₀, e ^ p = 1) (u : GL ι K) (hu : (u : Matrix ι ι K) ∈ spanE K E₀)
    (hup : u ^ p = 1) :
    ∃ c : GL ι K, (c : Matrix ι ι K) ∈ spanE K E₀ ∧ c ^ p ^ (s - 1) = u ∧ c ^ p ^ s = 1 := by
  classical
  haveI := Fact.mk hp
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have h2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have hqn : q = 2 ^ (n : ℕ) := hq ▸ hn
  have hq0 : (q : ZMod p) ≠ 0 := by
    rw [hqn, Ne, ZMod.natCast_eq_zero_iff]; exact fun h => h2 (hp.dvd_of_dvd_pow h)
  have hqd : (q : ZMod p) ^ d = 1 := hd ▸ pow_orderOf_eq_one _
  have hd0 : d ≠ 0 := by
    rw [hd]
    exact (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p - 1, by have := hp.two_le; omega,
      ZMod.pow_card_sub_one_eq_one hq0⟩)).ne'
  have hq2 : 2 ≤ q := hqn ▸ (Nat.le_self_pow n.ne_zero 2 |>.trans' le_rfl)
  have hQ1 : 1 < q ^ d := Nat.one_lt_pow hd0 (by omega)
  have hpQ : p ∣ q ^ d - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hQ1.le, Nat.cast_pow, hqd, Nat.cast_one, sub_self]
  have hs1 : 1 ≤ s := hs ▸ one_le_padicValNat_of_dvd (by omega) hpQ
  have h1 : (1 : Matrix ι ι K) ∈ spanE K E₀ :=
    Submodule.subset_span ⟨⟨1, E₀.one_mem⟩, Units.val_one⟩
  let B : Subalgebra K (Matrix ι ι K) :=
    { carrier := spanE K E₀
      mul_mem' := fun ha hb => spanE_mul_mem E₀ ha hb
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      algebraMap_mem' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one]; exact Submodule.smul_mem _ c h1 }
  letI : CommRing B :=
    { (inferInstance : Ring B) with
      mul_comm := fun x y => Subtype.ext (spanE_commute E₀ hE x.2 y.2) }
  have hQ : ∀ x : B, x ^ q ^ d = x := by
    have := pow_eq_self_of_mem_spanE (b := (n : ℕ) * d) E₀ hE hexp
      (fun c => by rw [pow_mul, ← hn]; exact FiniteField.pow_card_pow d c)
      (by rw [← ZMod.natCast_eq_natCast_iff, pow_mul, Nat.cast_pow, ← hqn, hqd, Nat.cast_one])
    intro x
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hqn, ← pow_mul]
    exact this x x.2
  haveI : Finite B := Subtype.finite
  haveI : IsReduced B := ⟨fun x ⟨m, hm⟩ => by
    have hk : ∀ k, x ^ (q ^ d) ^ k = x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, pow_mul, ih, hQ]
    have hm' : m ≤ (q ^ d) ^ m := (Nat.lt_pow_self hQ1).le
    rw [← hk m, ← Nat.sub_add_cancel hm', pow_add, hm, mul_zero]⟩
  let e := IsArtinianRing.equivPi B
  let uB : B := ⟨u, hu⟩
  have huB : uB ^ p = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow]
    show (u : Matrix ι ι K) ^ p = 1
    rw [← Units.val_pow_eq_pow_val, hup, Units.val_one])
  have hroot : ∀ I : MaximalSpectrum B, ∃ c : B ⧸ I.asIdeal,
      c ^ p ^ (s - 1) = Ideal.Quotient.mk I.asIdeal uB ∧ c ^ p ^ s = 1 := by
    intro I
    haveI := I.isMaximal
    letI : Field (B ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Finite (B ⧸ I.asIdeal) :=
      Finite.of_surjective (Ideal.Quotient.mk I.asIdeal) Ideal.Quotient.mk_surjective
    haveI : Module.Finite K (B ⧸ I.asIdeal) := Module.Finite.of_finite
    refine field_root hp hs1 _ (by rw [← map_pow, huB, map_one]) fun hne => ?_
    set ū := Ideal.Quotient.mk I.asIdeal uB
    have hū : ū ^ p = 1 := by rw [← map_pow, huB, map_one]
    have hcard : Nat.card (B ⧸ I.asIdeal) = q ^ Module.finrank K (B ⧸ I.asIdeal) := by
      rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card, hq]
    set f := Module.finrank K (B ⧸ I.asIdeal)
    have hū0 : ū ≠ 0 := by
      rintro h; rw [h, zero_pow hp.ne_zero] at hū; exact zero_ne_one hū
    haveI : Fintype (B ⧸ I.asIdeal) := Fintype.ofFinite _
    have hpF : p ∣ q ^ f - 1 := by
      rw [← hcard, Nat.card_eq_fintype_card, ← orderOf_eq_prime hū hne]
      exact orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one ū hū0)
    have hf1 : 1 ≤ q ^ f := Nat.one_le_pow _ _ (by omega)
    have hdf : d ∣ f := by
      rw [hd]
      apply orderOf_dvd_of_pow_eq_one
      have := (ZMod.natCast_eq_zero_iff _ _).2 hpF
      rwa [Nat.cast_sub hf1, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at this
    rw [hcard, hs]
    exact (pow_padicValNat_dvd).trans (Nat.pow_sub_one_dvd_pow_sub_one q hdf)
  choose cb hcb using hroot
  set c : B := e.symm cb
  have hc1 : c ^ p ^ (s - 1) = uB := e.injective (by
    rw [map_pow, AlgEquiv.apply_symm_apply]
    funext I
    rw [Pi.pow_apply, (hcb I).1, IsArtinianRing.equivPi_apply])
  have hc2 : c ^ p ^ s = 1 := e.injective (by
    rw [map_pow, AlgEquiv.apply_symm_apply, map_one]
    funext I
    rw [Pi.pow_apply, (hcb I).2]; rfl)
  have hps : 1 ≤ p ^ s := Nat.one_le_pow _ _ hp.pos
  have hcoe : ∀ m : ℕ, ((c ^ m : B) : Matrix ι ι K) = (c : Matrix ι ι K) ^ m :=
    fun m => SubmonoidClass.coe_pow c m
  have hinv : (c : Matrix ι ι K) ^ p ^ s = 1 := by rw [← hcoe, hc2]; rfl
  let cG : GL ι K := ⟨c, (c : Matrix ι ι K) ^ (p ^ s - 1),
    by rw [← pow_succ', Nat.sub_add_cancel hps, hinv],
    by rw [← pow_succ, Nat.sub_add_cancel hps, hinv]⟩
  refine ⟨cG, c.2, Units.ext ?_, Units.ext ?_⟩
  · rw [Units.val_pow_eq_pow_val]
    show (c : Matrix ι ι K) ^ p ^ (s - 1) = u
    rw [← hcoe, hc1]
  · rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hinv

@[expose] noncomputable def formAdj {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : K ≃+* K) (G : Matrix ι ι K) (M : Matrix ι ι K) : Matrix ι ι K :=
  G⁻¹ * (M.map τ)ᵀ * G

theorem formAdj_mul {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : K ≃+* K) {G : Matrix ι ι K} (hG : IsUnit G.det) (M N : Matrix ι ι K) :
    formAdj τ G (M * N) = formAdj τ G N * formAdj τ G M := by
  have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ hG
  have hm : (M * N).map τ = M.map τ * N.map τ := Matrix.map_mul (f := (τ : K →+* K))
  simp only [formAdj]
  rw [hm, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc G G⁻¹, hGG, Matrix.one_mul]

theorem formAdj_one {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : K ≃+* K) {G : Matrix ι ι K} (hG : IsUnit G.det) :
    formAdj τ G (1 : Matrix ι ι K) = 1 := by
  simp [formAdj, Matrix.nonsing_inv_mul _ hG]

theorem formAdj_pow {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : K ≃+* K) {G : Matrix ι ι K} (hG : IsUnit G.det) (M : Matrix ι ι K) (n : ℕ) :
    formAdj τ G (M ^ n) = formAdj τ G M ^ n := by
  induction n with
  | zero => simp [formAdj_one τ hG]
  | succ n ih => rw [pow_succ, formAdj_mul τ hG, ih, pow_succ']

theorem formAdj_formAdj {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : K ≃+* K) {G : Matrix ι ι K} (hG : IsUnit G.det)
    (hτ : ∀ c, τ (τ c) = c) (hGs : (G.map τ)ᵀ = G) (M : Matrix ι ι K) :
    formAdj τ G (formAdj τ G M) = M := by
  have hmap : ∀ X Y : Matrix ι ι K, (X * Y).map τ = X.map τ * Y.map τ :=
    fun X Y => Matrix.map_mul (f := (τ : K →+* K))
  have hττ : (M.map τ).map τ = M := by ext i j; simp [hτ]
  have hGi : ((G⁻¹).map τ)ᵀ = G⁻¹ := by
    have h1 : (G⁻¹).map τ * G.map τ = 1 := by
      rw [← hmap, Matrix.nonsing_inv_mul _ hG]; ext i j; simp [Matrix.one_apply]
    have h2 : (G.map τ)⁻¹ = (G⁻¹).map τ := Matrix.inv_eq_left_inv h1
    rw [← h2, Matrix.transpose_nonsing_inv, hGs]
  have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ hG
  have hGG' : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hG
  simp only [formAdj]
  rw [hmap, hmap, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_map, hττ,
    Matrix.transpose_transpose, hGs, hGi]
  simp only [← Matrix.mul_assoc]
  rw [hGG', Matrix.one_mul, Matrix.mul_assoc, hGG', Matrix.mul_one]

theorem formAdj_eq_inv {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : K ≃+* K) {G : Matrix ι ι K} (hG : IsUnit G.det) {g : GL ι K}
    (h : formAdj τ G (g : Matrix ι ι K) * g = 1) :
    formAdj τ G (g : Matrix ι ι K) = ((g⁻¹ : GL ι K) : Matrix ι ι K) := by
  calc formAdj τ G (g : Matrix ι ι K) = formAdj τ G (g : Matrix ι ι K) * ((g * g⁻¹ : GL ι K) :
        Matrix ι ι K) := by rw [mul_inv_cancel, Units.val_one, mul_one]
    _ = ((g⁻¹ : GL ι K) : Matrix ι ι K) := by
        rw [Units.val_mul, ← mul_assoc, h, one_mul]

theorem formAdj_mem_spanE {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : K ≃+* K) {G : Matrix ι ι K} (hG : IsUnit G.det) (E₀ : Subgroup (GL ι K))
    (hEU : ∀ e ∈ E₀, formAdj τ G (e : Matrix ι ι K) * e = 1) {M : Matrix ι ι K}
    (hM : M ∈ spanE K E₀) : formAdj τ G M ∈ spanE K E₀ := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨e, he⟩, rfl⟩ := hx
    simp only
    rw [formAdj_eq_inv τ hG (hEU e he)]
    exact Submodule.subset_span ⟨⟨e⁻¹, E₀.inv_mem he⟩, rfl⟩
  | zero => simp [formAdj]
  | add x y _ _ hx hy =>
    have : formAdj τ G (x + y) = formAdj τ G x + formAdj τ G y := by
      simp [formAdj, Matrix.map_add, Matrix.transpose_add, mul_add, add_mul]
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have : formAdj τ G (c • x) = τ c • formAdj τ G x := by
      simp only [formAdj]
      rw [show (c • x).map τ = τ c • x.map τ by ext i j; simp [Matrix.map_apply]]
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
    rw [this]; exact Submodule.smul_mem _ _ hx

theorem spanE_pow_mem {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (E₀ : Subgroup (GL ι K)) {M : Matrix ι ι K} (hM : M ∈ spanE K E₀)
    (n : ℕ) : M ^ n ∈ spanE K E₀ := by
  induction n with
  | zero => exact Submodule.subset_span ⟨⟨1, E₀.one_mem⟩, Units.val_one⟩
  | succ n ih => rw [pow_succ]; exact spanE_mul_mem E₀ ih hM

theorem exists_pow_eq_of_pow_eq_one_adj {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] [Fintype K] [CharP K 2] {p q d s : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : Fintype.card K = q) (hd : d = orderOf (q : ZMod p))
    (hs : s = padicValNat p (q ^ d - 1)) (τ : K ≃+* K) (hτ : ∀ c, τ (τ c) = c)
    (G : Matrix ι ι K) (hG : IsUnit G.det) (hGs : (G.map τ)ᵀ = G)
    (E₀ : Subgroup (GL ι K)) (hE : IsMulCommutative E₀) (hexp : ∀ e ∈ E₀, e ^ p = 1)
    (hEU : ∀ e ∈ E₀, formAdj τ G (e : Matrix ι ι K) * e = 1) (u : GL ι K)
    (hu : (u : Matrix ι ι K) ∈ spanE K E₀) (hup : u ^ p = 1)
    (huU : formAdj τ G (u : Matrix ι ι K) * u = 1) :
    ∃ c : GL ι K, (c : Matrix ι ι K) ∈ spanE K E₀ ∧ formAdj τ G (c : Matrix ι ι K) * c = 1 ∧
      c ^ p ^ (s - 1) = u ∧ c ^ p ^ s = 1 := by
  obtain ⟨c, hcA, hc1, hc2⟩ :=
    exists_pow_eq_of_pow_eq_one hp hp2 hq hd hs E₀ hE hexp u hu hup
  have hcinvA : ((c⁻¹ : GL ι K) : Matrix ι ι K) ∈ spanE K E₀ := by
    have : c⁻¹ = c ^ (p ^ s - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos), hc2]
    rw [this, Units.val_pow_eq_pow_val]; exact spanE_pow_mem E₀ hcA _
  let cs : GL ι K := ⟨formAdj τ G c, formAdj τ G ((c⁻¹ : GL ι K) : Matrix ι ι K),
    by rw [← formAdj_mul τ hG, ← Units.val_mul, inv_mul_cancel, Units.val_one, formAdj_one τ hG],
    by rw [← formAdj_mul τ hG, ← Units.val_mul, mul_inv_cancel, Units.val_one, formAdj_one τ hG]⟩
  have hcsA : (cs : Matrix ι ι K) ∈ spanE K E₀ := formAdj_mem_spanE τ hG E₀ hEU hcA
  have hcsiA : ((cs⁻¹ : GL ι K) : Matrix ι ι K) ∈ spanE K E₀ := formAdj_mem_spanE τ hG E₀ hEU hcinvA
  have hcomm : Commute c cs⁻¹ := Units.ext (by
    rw [Units.val_mul, Units.val_mul]; exact spanE_commute E₀ hE hcA hcsiA)
  have hcspow : ∀ k : ℕ, ((cs ^ k : GL ι K) : Matrix ι ι K) = formAdj τ G (((c ^ k : GL ι K)) : Matrix ι ι K) := by
    intro k
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, formAdj_pow τ hG]
  set w := c * cs⁻¹ with hw
  have hwpow : ∀ k : ℕ, w ^ k = c ^ k * (cs ^ k)⁻¹ := fun k => by rw [hw, hcomm.mul_pow, inv_pow]
  have hcs1 : cs ^ p ^ (s - 1) = u⁻¹ := Units.ext (by rw [hcspow, hc1]; exact formAdj_eq_inv τ hG huU)
  have hcs2 : cs ^ p ^ s = 1 := Units.ext (by rw [hcspow, hc2, Units.val_one]; exact formAdj_one τ hG)
  have hodd : 2 * ((p + 1) / 2) = p + 1 := by
    have := (hp.eq_one_or_self_of_dvd 2 |> fun _ => hp.odd_of_ne_two hp2); obtain ⟨r, hr⟩ := this; omega
  refine ⟨w ^ ((p + 1) / 2), ?_, ?_, ?_, ?_⟩
  · rw [Units.val_pow_eq_pow_val]
    exact spanE_pow_mem E₀ (by rw [Units.val_mul]; exact spanE_mul_mem E₀ hcA hcsiA) _
  ·
    have hadjw : formAdj τ G (w : Matrix ι ι K) = ((w⁻¹ : GL ι K) : Matrix ι ι K) := by
      have hcsi : ((cs⁻¹ : GL ι K) : Matrix ι ι K) = formAdj τ G ((c⁻¹ : GL ι K) : Matrix ι ι K) := rfl
      rw [hw, Units.val_mul, formAdj_mul τ hG, hcsi, formAdj_formAdj τ hG hτ hGs, _root_.mul_inv_rev,
        inv_inv, Units.val_mul]
      exact spanE_commute E₀ hE hcinvA hcsA
    rw [Units.val_pow_eq_pow_val, formAdj_pow τ hG, hadjw, ← Units.val_pow_eq_pow_val,
      ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
  · rw [← pow_mul, mul_comm, pow_mul, hwpow, hc1, hcs1, inv_inv, ← pow_two, ← pow_mul, hodd,
      pow_succ, hup, one_mul]
  · rw [← pow_mul, mul_comm, pow_mul, hwpow, hc2, hcs2, inv_one, mul_one, one_pow]

theorem split_of_dvd {p n a : ℕ} (hp : p.Prime) (hn : n ∣ a * p) (hna : ¬ n ∣ a) :
    ∃ m j : ℕ, n = p * m ∧ a = m * j ∧ ¬ p ∣ j := by
  obtain ⟨n', a', hcop, hn', ha'⟩ := Nat.exists_coprime n a
  generalize Nat.gcd n a = g at hn' ha'
  subst hn' ha'
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · exfalso; apply hna; simp [h]
    · exact h
  have hdvd : n' ∣ a' * p := by
    have h1 : g * n' ∣ g * (a' * p) := by
      rw [mul_comm g n', ← mul_assoc, mul_comm g a']; exact hn
    exact Nat.dvd_of_mul_dvd_mul_left hg0 h1
  have hn'p : n' ∣ p := hcop.dvd_of_dvd_mul_left hdvd
  rcases (Nat.dvd_prime hp).1 hn'p with h1 | h1
  · exfalso; apply hna; rw [h1, one_mul]; exact dvd_mul_left _ _
  · refine ⟨g, a', by rw [h1, mul_comm], mul_comm _ _, fun hpa => ?_⟩
    rw [h1] at hcop
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hpa)

theorem val_eq {p n a d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : n ∣ a * p) (hna : ¬ n ∣ a)
    (hd : d = orderOf ((2 ^ n : ℕ) : ZMod p)) :
    padicValNat p ((2 ^ n) ^ d - 1) = padicValNat p ((2 ^ a) ^ (p - 1) - 1) + 1 ∧
      1 ≤ padicValNat p ((2 ^ a) ^ (p - 1) - 1) := by
  haveI := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨m, j, rfl, rfl, hj⟩ := split_of_dvd hp hn hna
  have hm : m ≠ 0 := by rintro rfl; simp at hna
  have hj0 : j ≠ 0 := by rintro rfl; simp at hj
  have h2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have h2pow : ∀ t, ¬ p ∣ 2 ^ t := fun t h => h2 (hp.dvd_of_dvd_pow h)
  have hne : ((2 ^ (p * m) : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact h2pow _
  have hdvd : d ∣ p - 1 := hd ▸ ZMod.orderOf_dvd_card_sub_one hne
  have hd0 : d ≠ 0 := by rintro rfl; rw [zero_dvd_iff] at hdvd; omega
  have hpd : ¬ p ∣ d := fun h => by
    have := Nat.le_of_dvd (by omega) hdvd; have := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) h; omega
  have hyd : p ∣ (2 ^ (p * m)) ^ d - 1 := by
    have h1 : (((2 ^ (p * m)) ^ d : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [Nat.cast_pow, hd, pow_orderOf_eq_one, Nat.cast_one]
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by positivity))).1
      ((ZMod.natCast_eq_natCast_iff _ _ _).1 h1).symm
  have hF : p ∣ 2 ^ (p - 1) - 1 := by
    have h1 : ((2 ^ (p - 1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [Nat.cast_pow, Nat.cast_one]
      exact ZMod.pow_card_sub_one_eq_one (by
        rw [Ne, show ((2 : ℕ) : ZMod p) = (2 : ZMod p) by norm_num, ← Nat.cast_ofNat,
          ZMod.natCast_eq_zero_iff]; exact h2)
    exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).1
      ((ZMod.natCast_eq_natCast_iff _ _ _).1 h1).symm
  have hlt : 1 < 2 ^ (p - 1) := Nat.one_lt_two_pow (by omega)
  set v₁ := padicValNat p (2 ^ (p - 1) - 1)
  have hv₁ : 1 ≤ v₁ := one_le_padicValNat_of_dvd (by omega) hF
  have lte : ∀ r, r ≠ 0 → padicValNat p ((2 ^ (p - 1)) ^ r - 1) = v₁ + padicValNat p r := by
    intro r hr
    have := padicValNat.pow_sub_pow (p := p) (hp1 := hodd) (x := 2 ^ (p - 1)) (y := 1) hlt
      hF (h2pow _) hr
    rwa [one_pow] at this
  have hA : padicValNat p ((2 ^ (m * j)) ^ (p - 1) - 1) = v₁ + padicValNat p m := by
    rw [← pow_mul, mul_comm (m * j), pow_mul, lte _ (mul_ne_zero hm hj0),
      padicValNat.mul hm hj0, padicValNat.eq_zero_of_not_dvd hj, add_zero]
  have hy1 : 1 < (2 ^ (p * m)) ^ d :=
    Nat.one_lt_pow hd0 (Nat.one_lt_two_pow (mul_ne_zero hp.ne_zero hm))
  have hS : padicValNat p ((2 ^ (p * m)) ^ d - 1) = v₁ + 1 + padicValNat p m := by
    have e1 := padicValNat.pow_sub_pow (p := p) (hp1 := hodd) (x := (2 ^ (p * m)) ^ d) (y := 1)
      hy1 hyd (h2pow _ ∘ fun h => by rw [← pow_mul] at h; exact h) (n := p - 1) (by omega)
    have hp1 : padicValNat p (p - 1) = 0 := padicValNat.eq_zero_of_not_dvd (fun h => by
      have := Nat.le_of_dvd (by omega) h; omega)
    rw [one_pow, hp1, add_zero] at e1
    rw [← e1, ← pow_mul, ← pow_mul, show p * m * (d * (p - 1)) = (p - 1) * (p * m * d) by ring,
      pow_mul, lte _ (by positivity), padicValNat.mul (by positivity) hd0,
      padicValNat.eq_zero_of_not_dvd hpd, padicValNat.mul hp.ne_zero hm, padicValNat_self]
    ring
  refine ⟨?_, ?_⟩
  · rw [hS, hA]; ring
  · rw [hA]; omega

theorem power_class {p n a d s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : n ∣ a * p) (hna : ¬ n ∣ a)
    (hd : d = orderOf ((2 ^ n : ℕ) : ZMod p)) (hs : s = padicValNat p ((2 ^ n) ^ d - 1)) :
    2 ≤ s ∧ ∃ k : ℕ, ¬ p ∣ k ∧ ∀ N : ℕ, N * 2 ^ (a * p) ≡ 2 ^ a [MOD p ^ s] →
      N ≡ 1 + p ^ (s - 1) * k [MOD p ^ s] := by
  haveI := Fact.mk hp
  obtain ⟨hv, hv1⟩ := val_eq hp hp2 hn hna hd
  rw [← hs] at hv
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have ha : a ≠ 0 := by rintro rfl; exact hna (dvd_zero _)
  set X := (2 ^ a) ^ (p - 1) with hX
  have hX1 : 1 < X := Nat.one_lt_pow (by omega) (Nat.one_lt_two_pow ha)
  set v := padicValNat p (X - 1)
  obtain ⟨k', hk'⟩ := pow_padicValNat_dvd (p := p) (n := X - 1)
  have hk'p : ¬ p ∣ k' := by
    rintro ⟨c, hc⟩
    exact pow_succ_padicValNat_not_dvd (p := p) (n := X - 1) (by omega)
      ⟨c, by rw [pow_succ, mul_assoc, ← hc]; exact hk'⟩
  refine ⟨by omega, (p - 1) * k', fun h => hk'p ((Nat.Prime.dvd_mul hp).1 h |>.resolve_left
    (fun h' => by have := Nat.le_of_dvd (by omega) h'; omega)), fun N hN => ?_⟩
  have hsv : s - 1 = v := by omega
  rw [← ZMod.natCast_eq_natCast_iff] at hN ⊢
  set u : ZMod (p ^ s) := ((p ^ (s - 1) * k' : ℕ) : ZMod (p ^ s))
  have hXu : ((X : ℕ) : ZMod (p ^ s)) = 1 + u := by
    rw [show X = 1 + p ^ (s - 1) * k' by rw [hsv, ← hk']; omega, Nat.cast_add, Nat.cast_one]
  have hu2 : u * u = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact (pow_dvd_pow p (by omega : s ≤ (s - 1) + (s - 1))).trans ⟨k' * k', by ring⟩
  have hpu : (p : ZMod (p ^ s)) * u = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff,
      show p * (p ^ (s - 1) * k') = p ^ s * k' by
        rw [← mul_assoc, ← pow_succ']; congr 2; omega]
    exact dvd_mul_right _ _
  have hunit : IsUnit ((2 ^ a : ℕ) : ZMod (p ^ s)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).2 (fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)))
  have hsplit : (2 : ℕ) ^ (a * p) = 2 ^ a * X := by
    rw [hX, ← pow_mul, ← pow_add]; congr 1
    rw [Nat.mul_sub, mul_one]; have : a ≤ a * p := Nat.le_mul_of_pos_right _ (by omega); omega
  rw [hsplit] at hN
  push_cast at hN
  rw [hXu] at hN
  have hunit' : IsUnit ((2 : ZMod (p ^ s)) ^ a) := by simpa using hunit
  have h1 : (N : ZMod (p ^ s)) * (1 + u) = 1 := by
    refine hunit'.mul_left_cancel ?_
    rw [mul_one]; linear_combination hN
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  show (N : ZMod (p ^ s)) = 1 + ((p : ZMod (p ^ s)) ^ (s - 1) * ((p - 1) * k'))
  have hu : u = (p : ZMod (p ^ s)) ^ (s - 1) * k' := by simp [u]
  rw [show (p : ZMod (p ^ s)) ^ (s - 1) * ((p - 1) * k') = (p - 1) * u by rw [hu]; ring]
  linear_combination (1 - u) * h1 + (N : ZMod (p ^ s)) * hu2 - hpu

theorem exists_pow_two_of_ringEquiv {K : Type} [Field K] [Fintype K] [CharP K 2]
    (σ₀ : K ≃+* K) :
    ∃ a : ℕ, ∀ c, σ₀ c = c ^ 2 ^ a := by
  letI := ZMod.algebra K 2
  let g : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv (f := σ₀) (fun c => by
    rw [← ZMod.natCast_zmod_val c, map_natCast, map_natCast])
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (k := ZMod 2) (l := K) (p := 2) g
  refine ⟨i, fun c => ?_⟩
  have := hi c
  rw [Nat.card_zmod] at this
  exact this

end CFSG.HardMathSupport.C14Cl
