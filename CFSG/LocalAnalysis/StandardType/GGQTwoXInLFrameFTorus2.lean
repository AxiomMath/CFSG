module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFDefs

public section

namespace CFSG.StandardType.QTwoFrameTorus

open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.Held

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {R : Type} [Group R]

lemma frame_card_units {M : Type} [Field M] [Finite M] (hM : Nat.card M = 4) :
    Nat.card Mˣ = 3 := by
  rw [Nat.card_units, hM]

lemma frame_pow_three_eq_one {M : Type} [Field M] [Finite M] (hM : Nat.card M = 4)
    {a : M} (ha : a ≠ 0) : a ^ 3 = 1 := by
  let _ : Fintype M := Fintype.ofFinite M
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  have hcard : Fintype.card M = 4 := by rw [← Nat.card_eq_fintype_card, hM]
  rw [hcard] at h
  exact h

theorem frame_sq_add_add_one_eq_zero {M : Type} [Field M] {a : M}
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) : a ^ 2 + a + 1 = 0 := by
  have h : (a - 1) * (a ^ 2 + a + 1) = a ^ 3 - 1 := by ring
  have h0 : (a - 1) * (a ^ 2 + a + 1) = 0 := by rw [h, sub_eq_zero.mpr ha3]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr ha1)

lemma frame_tau_tau {M : Type} [Field M] [Finite M] (hM : Nat.card M = 4)
    {τ : M ≃+* M} (hτ2 : ∀ y, τ y = y ^ 2) (y : M) : τ (τ y) = y := by
  rw [hτ2, hτ2]
  by_cases hy : y = 0
  · simp [hy]
  · calc (y ^ 2) ^ 2 = y ^ 3 * y := by ring
      _ = 1 * y := by rw [frame_pow_three_eq_one hM hy]
      _ = y := one_mul y

lemma frame_sq_eq_add_one {M : Type} [Field M] [CharP M 2] {a : M}
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) : a ^ 2 = a + 1 := by
  have h := frame_sq_add_add_one_eq_zero ha3 ha1
  have hsum : a ^ 2 + a = 1 := by
    have h' := congrArg (fun t : M => t + 1) h
    simpa [add_assoc, CharTwo.add_self_eq_zero] using h'
  calc a ^ 2 = a ^ 2 + a + a := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = 1 + a := by rw [hsum]
    _ = a + 1 := add_comm _ _

lemma frame_exists_pow_three_eq_one_ne_one {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) : ∃ ζ : M, ζ ^ 3 = 1 ∧ ζ ≠ 1 := by
  have hcard : Nat.card Mˣ = 3 := frame_card_units hM
  have hnt : Nontrivial Mˣ :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨ζ, hζ⟩ := @exists_ne Mˣ hnt (1 : Mˣ)
  refine ⟨(ζ : M), frame_pow_three_eq_one hM (Units.ne_zero ζ), ?_⟩
  simpa using hζ

lemma frame_four_le_of_injective {α : Type*} {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {f : α → Fin n → Mˣ} (hf : Function.Injective f)
    (hα : 3 ^ 4 ≤ Nat.card α) : 4 ≤ n := by
  have hcard_le : Nat.card α ≤ Nat.card (Fin n → Mˣ) :=
    Nat.card_le_card_of_injective f hf
  rw [Nat.card_fun, Nat.card_fin, frame_card_units hM] at hcard_le
  have h4 : 3 ^ 4 ≤ 3 ^ n := le_trans hα hcard_le
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h4

theorem frame_eq_one_or_eq_or_sq {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {ζ a : M} (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    (ha3 : a ^ 3 = 1) : a = 1 ∨ a = ζ ∨ a = ζ ^ 2 := by
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h] at hζ3
    norm_num at hζ3
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at ha3
    norm_num at ha3
  let z : Mˣ := Units.mk0 ζ hζ0
  let u : Mˣ := Units.mk0 a ha0
  have hz3 : z ^ 3 = 1 := by
    apply Units.ext
    simpa [z] using hζ3
  have hz1 : z ≠ 1 := by
    intro h
    exact hζ1 (congrArg Units.val h)
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hcard : Nat.card Mˣ = 3 := by
    rw [Nat.card_units, hM]
  have htop : Subgroup.zpowers z = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hcard]
  have hu_mem : u ∈ Subgroup.zpowers z := by
    rw [htop]
    exact Subgroup.mem_top u
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hu_mem
  have hred : z ^ n = z ^ (n % (3 : ℤ)) := zpow_eq_zpow_emod' n hz3
  have hua' : a = ζ ^ (n % (3 : ℤ)) := by
    have h1 : ((z ^ n : Mˣ) : M) = a := by rw [hn]; rfl
    have h2 : ((z ^ (n % (3 : ℤ)) : Mˣ) : M) = a := by rw [← hred]; exact h1
    simpa [z] using h2.symm
  have hr0 : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have hr3 : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
  interval_cases h : n % 3 <;> simp [hua']

theorem frame_exists_zmod3_pow_eq {M : Type} [Monoid M] {ζ a : M}
    (ha : a = 1 ∨ a = ζ ∨ a = ζ ^ 2) : ∃ n : ZMod 3, ζ ^ n.val = a := by
  rcases ha with rfl | rfl | rfl
  · refine ⟨0, ?_⟩
    simp
  · refine ⟨1, ?_⟩
    rw [ZMod.val_one, pow_one]
  · refine ⟨2, ?_⟩
    rw [show (2 : ZMod 3).val = 2 by decide]

private lemma frame_tau_mul_self {M : Type} [Field M] [Finite M] (hM : Nat.card M = 4)
    {τ : M ≃+* M} (hτ2 : ∀ y, τ y = y ^ 2) {a : M} (ha : a ≠ 0) : τ a * a = 1 := by
  rw [hτ2, ← pow_succ]
  simpa using frame_pow_three_eq_one hM ha




noncomputable def frameDiagGL {n : ℕ} {M : Type} [Field M] (d : Fin n → Mˣ) :
    GL (Fin n) M :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun i => (d i : M)) (by
    rw [Matrix.det_diagonal, ← Units.coe_prod]
    exact Units.ne_zero _)

lemma frameDiagGL_val {n : ℕ} {M : Type} [Field M] (d : Fin n → Mˣ) :
    ((frameDiagGL d : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
      Matrix.diagonal (fun i => (d i : M)) :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

lemma frameDiagGL_mem_heldGU {n : ℕ} {M : Type} [Field M] {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} {d : Fin n → Mˣ} (hd : ∀ i, τ (d i) * (d i) = 1) :
    frameDiagGL d ∈ heldGU n M τ hτ := by
  rw [mem_heldGU, frameDiagGL_val, Matrix.diagonal_map (map_zero τ), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one, Matrix.diagonal_eq_diagonal_iff]
  exact hd

lemma frame_diag_entry_ne_zero {n : ℕ} {M : Type} [Field M]
    {A : GL (Fin n) M} (hd : ∀ i j, i ≠ j →
      ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) (i : Fin n) :
    ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i ≠ 0 := by
  intro hzero
  have hcol : ∀ k, ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) k i = 0 := by
    intro k
    by_cases hk : k = i
    · subst hk
      exact hzero
    · exact hd k i hk
  have hdet : ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M).det = 0 :=
    Matrix.det_eq_zero_of_column_eq_zero i hcol
  exact Matrix.GeneralLinearGroup.det_ne_zero A hdet

private noncomputable def frameDiagHom {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2) :
    (Fin n → Mˣ) →* ↥(heldGU n M τ hτ) where
  toFun d := ⟨frameDiagGL d, frameDiagGL_mem_heldGU fun i =>
    frame_tau_mul_self hM hτ2 (Units.ne_zero (d i))⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change ((frameDiagGL (1 : Fin n → Mˣ) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) = 1
    rw [frameDiagGL_val]
    simp only [Pi.one_apply, Units.val_one]
    rw [Matrix.diagonal_one]
  map_mul' d e := by
    apply Subtype.ext
    apply Units.ext
    change ((frameDiagGL (d * e) : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
      ((frameDiagGL d : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
        ((frameDiagGL e : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)
    rw [frameDiagGL_val, frameDiagGL_val, frameDiagGL_val, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_eq_diagonal_iff]
    intro i
    simp

noncomputable def frameDiagSub {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2) :
    Subgroup ↥(heldGU n M τ hτ) :=
  (frameDiagHom (n := n) (τ := τ) (hτ := hτ) hM hτ2).range

private lemma frameDiagHom_injective {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2) :
    Function.Injective (frameDiagHom (n := n) (τ := τ) (hτ := hτ) hM hτ2) := by
  intro d e h
  funext i
  apply Units.ext
  have h' := congrArg (fun A : ↥(heldGU n M τ hτ) =>
    (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i)) h
  simpa [frameDiagHom, frameDiagGL_val, Matrix.diagonal_apply_eq] using h'

noncomputable def frameDiagEquiv {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2) :
    (Fin n → Mˣ) ≃* ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) :=
  MonoidHom.ofInjective (f := frameDiagHom (n := n) (τ := τ) (hτ := hτ) hM hτ2)
    (frameDiagHom_injective hM hτ2)

lemma frame_mem_diagSub_iff {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    (A : ↥(heldGU n M τ hτ)) :
    A ∈ frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2 ↔ ∀ i j, i ≠ j →
      (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j) = 0 := by
  constructor
  · intro hA i j hij
    obtain ⟨d, rfl⟩ := hA
    change ((frameDiagGL d : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0
    rw [frameDiagGL_val]
    exact Matrix.diagonal_apply_ne _ hij
  · intro hA
    have hne : ∀ i, (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i) ≠ 0 :=
      fun i => frame_diag_entry_ne_zero hA i
    let d : Fin n → Mˣ := fun i => Units.mk0 _ (hne i)
    refine ⟨d, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change ((frameDiagGL d : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
      ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)
    rw [frameDiagGL_val]
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Units.val_mk0]
    · rw [Matrix.diagonal_apply_ne _ hij, hA i j hij]


lemma frame_E_eq_diagSub {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {ρ : ↥(heldGU n M τ hτ) →* R} {E : Subgroup R} {x : R} {L : Subgroup R}
    (hU : GGQTwoUFrame ρ E x L) :
    E = (frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2).map ρ := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · intro hg
    obtain ⟨A, hdiag, hA⟩ := (hU.2.1 g).mp hg
    exact ⟨A, (frame_mem_diagSub_iff hM hτ2 A).mpr hdiag, hA⟩
  · rintro ⟨A, hA, rfl⟩
    exact (hU.2.1 (ρ A)).mpr ⟨A, (frame_mem_diagSub_iff hM hτ2 A).mp hA, rfl⟩

lemma frame_card_diagSub {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2) :
    Nat.card ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) = 3 ^ n := by
  rw [← Nat.card_congr (frameDiagEquiv hM hτ2).toEquiv, Nat.card_fun, Nat.card_fin,
    frame_card_units hM]


noncomputable def frameDlog {M : Type} [Field M] [Finite M] (c : Mˣ)
    (hgen : ∀ u : Mˣ, u ∈ Subgroup.zpowers c) (hn : Nat.card Mˣ = 3) :
    Mˣ ≃* Multiplicative (ZMod 3) :=
  (zmodMulEquivOfGenerator hgen hn).symm

lemma frameDlog_apply_gen {M : Type} [Field M] [Finite M] (c : Mˣ)
    (hgen : ∀ u : Mˣ, u ∈ Subgroup.zpowers c) (hn : Nat.card Mˣ = 3) :
    frameDlog c hgen hn c = Multiplicative.ofAdd 1 := by
  rw [frameDlog, zmodMulEquivOfGenerator_symm_apply_generator]

lemma frameDlog_pow {M : Type} [Field M] [Finite M] (c : Mˣ)
    (hgen : ∀ u : Mˣ, u ∈ Subgroup.zpowers c) (hn : Nat.card Mˣ = 3) (u : Mˣ) :
    (c : M) ^ (frameDlog c hgen hn u).toAdd.val = (u : M) := by
  let e := zmodMulEquivOfGenerator hgen hn
  have h := zmodMulEquivOfGenerator_apply_ofAdd_intCast hgen hn
    (((frameDlog c hgen hn u).toAdd).val : ℤ)
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at h
  have hd : Multiplicative.ofAdd ((frameDlog c hgen hn u).toAdd) =
      frameDlog c hgen hn u := rfl
  rw [hd] at h
  have heu : e (frameDlog c hgen hn u) = u := e.apply_symm_apply u
  have h' := congrArg (fun x : Mˣ => (x : M)) h
  rw [zpow_natCast, heu] at h'
  exact h'.symm

private noncomputable def frameED {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {E : Subgroup R} {x : R} {L : Subgroup R}
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L) :
    ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) ≃* ↥E :=
  (Subgroup.equivMapOfInjective
    (frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) ρ hU.1).trans
    (MulEquiv.subgroupCongr
      (frame_E_eq_diagSub (n := n) (M := M) (τ := τ) (hτ := hτ) (ρ := ρ)
        (E := E) (x := x) (L := L) hM hτ2 hU).symm)

private noncomputable def frameCoordMul {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {E : Subgroup R} {x : R} {L : Subgroup R}
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L) (c : Mˣ)
    (hgen : ∀ u : Mˣ, u ∈ Subgroup.zpowers c) (hn : Nat.card Mˣ = 3) :
    ↥E ≃* (Fin n → Multiplicative (ZMod 3)) :=
  ((frameED hM hτ2 hU).symm.trans
    (frameDiagEquiv (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2).symm).trans
    (MulEquiv.piCongrRight fun _ => frameDlog c hgen hn)

noncomputable def frameCoordAdd {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {E : Subgroup R} {x : R} {L : Subgroup R}
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L) (c : Mˣ)
    (hgen : ∀ u : Mˣ, u ∈ Subgroup.zpowers c) (hn : Nat.card Mˣ = 3) :
    Additive ↥E ≃+ (Fin n → ZMod 3) :=
  (frameCoordMul hM hτ2 hU c hgen hn).toAdditive.trans
    (AddEquiv.additiveMultiplicative (Fin n → ZMod 3))

private lemma frameCoordAdd_apply {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {E : Subgroup R} {x : R} {L : Subgroup R}
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L) (c : Mˣ)
    (hgen : ∀ u : Mˣ, u ∈ Subgroup.zpowers c) (hn : Nat.card Mˣ = 3)
    (a : Additive ↥E) (i : Fin n) :
    frameCoordAdd hM hτ2 hU c hgen hn a i =
      (frameCoordMul hM hτ2 hU c hgen hn (Additive.toMul a) i).toAdd :=
  rfl

private lemma frameDiagEquiv_apply_coe {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    (d : Fin n → Mˣ) :
    ((frameDiagEquiv (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2 d :
      ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2)) :
      ↥(heldGU n M τ hτ)) =
      frameDiagHom (n := n) (τ := τ) (hτ := hτ) hM hτ2 d :=
  MonoidHom.ofInjective_apply
    (f := frameDiagHom (n := n) (τ := τ) (hτ := hτ) hM hτ2)
    (frameDiagHom_injective (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2)

lemma frameDiagEquiv_apply_val {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    (d : Fin n → Mˣ) :
    ((((frameDiagEquiv (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2 d :
      ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2)) :
      ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) =
      ((frameDiagGL d : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) := by
  rw [frameDiagEquiv_apply_coe]
  rfl

private lemma frame_diagEquiv_symm_apply {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    (A : ↥(heldGU n M τ hτ))
    (hd : ∀ i j, i ≠ j → (((A : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) i j) = 0)
    (hne : ∀ i, (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i) ≠ 0) :
    (frameDiagEquiv (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2).symm
        ⟨A, (frame_mem_diagSub_iff (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2 A).mpr hd⟩ =
      fun i => Units.mk0 (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i) (hne i) := by
  apply (frameDiagEquiv (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
    ((frameDiagGL (fun i => Units.mk0
      (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i) (hne i)) :
      GL (Fin n) M) : Matrix (Fin n) (Fin n) M)
  rw [frameDiagGL_val]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Units.val_mk0]
  · rw [Matrix.diagonal_apply_ne _ hij, hd i j hij]

private lemma frameED_symm_apply {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {E : Subgroup R} {x : R} {L : Subgroup R}
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L)
    (A : ↥(heldGU n M τ hτ))
    (hd : ∀ i j, i ≠ j → (((A : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) i j) = 0) (he : ρ A ∈ E) :
    (frameED hM hτ2 hU).symm ⟨ρ A, he⟩ =
      ⟨A, (frame_mem_diagSub_iff (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2 A).mpr hd⟩ := by
  let hEeq := frame_E_eq_diagSub (n := n) (M := M) (τ := τ) (hτ := hτ) (ρ := ρ)
    (E := E) (x := x) (L := L) hM hτ2 hU
  let eED : ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) ≃* ↥E :=
    (Subgroup.equivMapOfInjective
      (frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) ρ hU.1).trans
      (MulEquiv.subgroupCongr hEeq.symm)
  change eED.symm ⟨ρ A, he⟩ = _
  have h1 : eED ⟨A, (frame_mem_diagSub_iff (n := n) (M := M) (τ := τ) (hτ := hτ)
      hM hτ2 A).mpr hd⟩ = ⟨ρ A, he⟩ := by
    apply Subtype.ext
    dsimp [eED, hEeq]
  rw [MulEquiv.symm_apply_eq, h1]

private lemma frameCoordMul_diag {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {E : Subgroup R} {x : R} {L : Subgroup R}
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L) (c : Mˣ)
    (hgen : ∀ u : Mˣ, u ∈ Subgroup.zpowers c) (hn : Nat.card Mˣ = 3)
    (A : ↥(heldGU n M τ hτ))
    (hd : ∀ i j, i ≠ j → (((A : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) i j) = 0)
    (hne : ∀ i, (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i) ≠ 0)
    (he : ρ A ∈ E) (i : Fin n) :
    frameCoordMul hM hτ2 hU c hgen hn ⟨ρ A, he⟩ i =
      frameDlog c hgen hn (Units.mk0
        (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i) (hne i)) := by
  rw [frameCoordMul]
  simp only [MulEquiv.trans_apply, MulEquiv.piCongrRight_apply]
  rw [frameED_symm_apply (n := n) (M := M) (τ := τ) (hτ := hτ) (E := E) (x := x) (L := L)
    (ρ := ρ) (hU := hU) (A := A) (hd := hd) (he := he)]
  rw [frame_diagEquiv_symm_apply (n := n) (M := M) (τ := τ) (hτ := hτ) (A := A)
    (hd := hd) (hne := hne)]

lemma frameCoordAdd_diag {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {E : Subgroup R} {x : R} {L : Subgroup R}
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L) (c : Mˣ)
    (hgen : ∀ u : Mˣ, u ∈ Subgroup.zpowers c) (hn : Nat.card Mˣ = 3)
    (A : ↥(heldGU n M τ hτ))
    (hd : ∀ i j, i ≠ j → (((A : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) i j) = 0)
    (hne : ∀ i, (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i) ≠ 0)
    (he : ρ A ∈ E) (i : Fin n) :
    frameCoordAdd hM hτ2 hU c hgen hn (Additive.ofMul ⟨ρ A, he⟩) i =
      (frameDlog c hgen hn (Units.mk0
        (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i) (hne i))).toAdd := by
  rw [frameCoordAdd_apply]
  change (frameCoordMul hM hτ2 hU c hgen hn ⟨ρ A, he⟩ i).toAdd =
    (frameDlog c hgen hn (Units.mk0
      (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i) (hne i))).toAdd
  rw [frameCoordMul_diag (n := n) (M := M) (τ := τ) (hτ := hτ) (E := E) (x := x)
    (L := L) (ρ := ρ) (hU := hU) (A := A) (hd := hd) (hne := hne) (he := he)]

end CFSG.StandardType.QTwoFrameTorus

end
