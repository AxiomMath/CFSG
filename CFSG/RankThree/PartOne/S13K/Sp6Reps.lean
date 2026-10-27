module

public import CFSG.RankThree.PartOne.S13K.Sp6At
public import CFSG.RankThree.PartOne.S13K.Sp6DBlock
public import CFSG.RankThree.PartOne.S13K.Sp6SBlock

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree.PartOne.KFQ CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem torusEquiv_injective : Function.Injective (torusEquiv : (Fin 3 → (Qext K)ˣ) → AutV K) := by
  intro x y h
  funext i
  have := congrArg (fun g : AutV K => g (fun _ => 1) i) h
  simp only [torusEquiv_apply, mul_one] at this
  exact Units.ext this

omit [Finite K] in
theorem eq_of_sq_eq {a b : (Qext K)ˣ} (hp : Odd p) (ha : a ^ p = 1) (hb : b ^ p = 1)
    (h : a * a = b * b) : a = b := by
  obtain ⟨k, hk⟩ := hp
  have h1 : ∀ a : (Qext K)ˣ, a ^ p = 1 → a = (a * a) ^ (k + 1) := fun a ha => by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = p + 1 by omega, pow_succ, ha, one_mul]
  rw [h1 a ha, h1 b hb, h]

omit [Finite K] in
theorem exists_sqrt {a : (Qext K)ˣ} (hp : Odd p) (ha : a ^ p = 1) :
    ∃ s : (Qext K)ˣ, s ^ p = 1 ∧ s * s = a := by
  obtain ⟨k, hk⟩ := hp
  refine ⟨a ^ (k + 1), ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]
  · rw [← pow_add, show k + 1 + (k + 1) = p + 1 by omega, pow_succ, ha, one_mul]

@[expose] noncomputable def tor10 (hpq : p ∣ Nat.card K + 1) (x : Fin 3 → (Qext K)ˣ)
    (hx : ∀ i, x i ^ p = 1) : ↥(M10 K) :=
  ⟨torusEquiv x, torusEquiv_mem_M10 hpq hx⟩

theorem tor10_coe (hpq : p ∣ Nat.card K + 1) (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1) :
    (tor10 hpq x hx).1 = torusEquiv x := rfl

theorem tor10_isTor (hpq : p ∣ Nat.card K + 1) (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1) :
    IsTor p (tor10 hpq x hx) := ⟨x, hx, rfl⟩

omit [Finite K] in
theorem pow_unit_of_pow {x y : Fin 3 → (Qext K)ˣ} (hx : ∀ i, x i ^ p = 1)
    (hy : ∀ i, y i ^ p = 1) : ∀ i, (x * y) i ^ p = 1 := fun i => by
  simp [mul_pow, hx i, hy i]

theorem tor10_mul (hpq : p ∣ Nat.card K + 1) (x y : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1)
    (hy : ∀ i, y i ^ p = 1) :
    tor10 hpq x hx * tor10 hpq y hy = tor10 hpq (x * y) (pow_unit_of_pow hx hy) :=
  Subtype.ext (torusEquiv_mul x y).symm

theorem tor10_inv (hpq : p ∣ Nat.card K + 1) (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1) :
    (tor10 hpq x hx)⁻¹ = tor10 hpq x⁻¹ (fun i => by simp [inv_pow, hx i]) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [tor10_mul]
  apply Subtype.ext
  change torusEquiv (x * x⁻¹) = 1
  rw [mul_inv_cancel, torusEquiv_one]

theorem tor10_npow (hpq : p ∣ Nat.card K + 1) (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1)
    (n : ℕ) : (tor10 hpq x hx) ^ n = tor10 hpq (x ^ n) (fun i => by
      simp only [Pi.pow_apply]
      rw [← pow_mul, mul_comm, pow_mul, hx i, one_pow]) := by
  induction n with
  | zero =>
    rw [pow_zero]
    apply Subtype.ext
    change (1 : AutV K) = torusEquiv (x ^ 0)
    rw [pow_zero, torusEquiv_one]
  | succ n ih =>
    rw [pow_succ, ih, tor10_mul]
    congr 1
    rw [pow_succ]

theorem exists_unit_primitiveRoot (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hmp, hm1, -⟩ := exists_root_not_mem hp hp2 hpq
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hmp
    exact zero_ne_one hmp
  refine ⟨Units.mk0 m hm0, ?_⟩
  have hu : (Units.mk0 m hm0) ^ p = 1 := Units.ext (by simpa using hmp)
  have hu1 : Units.mk0 m hm0 ≠ 1 := fun h1 => hm1 (by simpa using congrArg Units.val h1)
  rw [IsPrimitiveRoot.iff_orderOf]
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hu) with h1 | h1
  · exact absurd (orderOf_eq_one_iff.mp h1) hu1
  · exact h1

omit [Finite K] in
theorem exists_pow_eq (hp : p.Prime) {ζ : (Qext K)ˣ} (hζ : IsPrimitiveRoot ζ p) {y : (Qext K)ˣ}
    (hy : y ^ p = 1) : ∃ i : ℕ, ζ ^ i = y := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h1 : IsPrimitiveRoot (ζ : Qext K) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have h2 : (y : Qext K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hy, Units.val_one]
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one h2
  exact ⟨i, Units.ext (by simpa using hi)⟩

@[simp] theorem perm_one_symm_apply (i : Fin 3) : (1 : Equiv.Perm (Fin 3)).symm i = i := rfl

@[simp] theorem swap01_two : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide

theorem bool_false_vec (j : Fin 3) : (![false, false, false] : Fin 3 → Bool) j = false := by
  fin_cases j <;> rfl

@[expose] noncomputable def gS (K : Type) [Field K] [Finite K] [CharP K 2] : ↥(M10 K) :=
  ⟨sgnPerm 1 ![true, false, false], sgnPerm_mem_M10 _ _⟩

@[expose] noncomputable def gD (K : Type) [Field K] [Finite K] [CharP K 2] : ↥(M10 K) :=
  ⟨sgnPerm (Equiv.swap 0 1) ![false, false, false], sgnPerm_mem_M10 _ _⟩

theorem gS_apply (v : QV K (Fin 3)) (i : Fin 3) :
    (gS K).1 v i = if i = 0 then frobQ K (v 0) else v i := by
  change sgnPerm 1 ![true, false, false] v i = _
  rw [sgnPerm_apply]
  fin_cases i <;> simp

theorem gD_apply (v : QV K (Fin 3)) (i : Fin 3) : (gD K).1 v i = v (Equiv.swap 0 1 i) := by
  change sgnPerm (Equiv.swap 0 1) ![false, false, false] v i = _
  rw [sgnPerm_apply]
  simp [bool_false_vec]

theorem gS_mul_self : gS K * gS K = 1 := by
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  funext i
  change (gS K).1 ((gS K).1 v) i = v i
  by_cases hi : i = 0
  · subst hi
    simp [gS_apply, frobQ_frobQ]
  · simp [gS_apply, hi]

theorem gD_mul_self : gD K * gD K = 1 := by
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  funext i
  change (gD K).1 ((gD K).1 v) i = v i
  simp [gD_apply]

theorem gS_inv : (gS K)⁻¹ = gS K := inv_eq_of_mul_eq_one_right gS_mul_self

theorem gD_inv : (gD K)⁻¹ = gD K := inv_eq_of_mul_eq_one_right gD_mul_self

theorem gS_conj (hpq : p ∣ Nat.card K + 1) {x : Fin 3 → (Qext K)ˣ} (hx : ∀ i, x i ^ p = 1) :
    (gS K).1 * torusEquiv x * (gS K).1⁻¹ = torusEquiv ![(x 0)⁻¹, x 1, x 2] := by
  have := sgnPerm_conj hpq 1 ![true, false, false] x ![(x 0)⁻¹, x 1, x 2] hx (fun i => by
    fin_cases i <;> simp)
  exact this

theorem gD_conj (hpq : p ∣ Nat.card K + 1) {x : Fin 3 → (Qext K)ˣ} (hx : ∀ i, x i ^ p = 1) :
    (gD K).1 * torusEquiv x * (gD K).1⁻¹ = torusEquiv ![x 1, x 0, x 2] := by
  have := sgnPerm_conj hpq (Equiv.swap 0 1) ![false, false, false] x ![x 1, x 0, x 2] hx
    (fun i => by fin_cases i <;> simp [bool_false_vec])
  exact this

omit [Finite K] in
theorem inv_vec_pow {x : Fin 3 → (Qext K)ˣ} (hx : ∀ i, x i ^ p = 1) :
    ∀ i, (![(x 0)⁻¹, x 1, x 2] : Fin 3 → (Qext K)ˣ) i ^ p = 1 := by
  intro i
  fin_cases i <;> simp [inv_pow, hx]

omit [Finite K] in
theorem swap_vec_pow {x : Fin 3 → (Qext K)ˣ} (hx : ∀ i, x i ^ p = 1) :
    ∀ i, (![x 1, x 0, x 2] : Fin 3 → (Qext K)ˣ) i ^ p = 1 := by
  intro i
  fin_cases i <;> simp [hx]

theorem gS_hg1 (hpq : p ∣ Nat.card K + 1) :
    ∀ x : ↥(M10 K), IsTor p x → IsTor p (gS K * x * (gS K)⁻¹) := by
  rintro x ⟨a, ha, hxa⟩
  refine ⟨![(a 0)⁻¹, a 1, a 2], inv_vec_pow ha, ?_⟩
  change (gS K).1 * x.1 * (gS K).1⁻¹ = _
  rw [hxa, gS_conj hpq ha]

theorem gS_hg2 (hpq : p ∣ Nat.card K + 1) :
    ∀ x : ↥(M10 K), IsTor p x → IsTor p ((gS K)⁻¹ * x * gS K) := by
  intro x hx
  have := gS_hg1 hpq x hx
  rw [gS_inv] at this ⊢
  exact this

theorem gD_hg1 (hpq : p ∣ Nat.card K + 1) :
    ∀ x : ↥(M10 K), IsTor p x → IsTor p (gD K * x * (gD K)⁻¹) := by
  rintro x ⟨a, ha, hxa⟩
  refine ⟨![a 1, a 0, a 2], swap_vec_pow ha, ?_⟩
  change (gD K).1 * x.1 * (gD K).1⁻¹ = _
  rw [hxa, gD_conj hpq ha]

theorem gD_hg2 (hpq : p ∣ Nat.card K + 1) :
    ∀ x : ↥(M10 K), IsTor p x → IsTor p ((gD K)⁻¹ * x * gD K) := by
  intro x hx
  have := gD_hg1 hpq x hx
  rw [gD_inv] at this ⊢
  exact this

theorem gS_comm_zero (hpq : p ∣ Nat.card K + 1) (hodd : Odd p) {x : ↥(M10 K)}
    {a : Fin 3 → (Qext K)ˣ} (ha : ∀ i, a i ^ p = 1) (hxa : x.1 = torusEquiv a)
    (hcomm : gS K * x = x * gS K) : a 0 = 1 := by
  have h1 : gS K * x * (gS K)⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr hcomm
  have h2 : (gS K).1 * torusEquiv a * (gS K).1⁻¹ = torusEquiv a := by
    rw [← hxa]
    exact congrArg (fun y : ↥(M10 K) => y.1) h1
  rw [gS_conj hpq ha] at h2
  have h3 := torusEquiv_injective h2
  have h4 : (a 0)⁻¹ = a 0 := congrFun h3 0
  refine eq_of_sq_eq hodd (ha 0) (one_pow _) ?_
  rw [mul_one]
  calc a 0 * a 0 = a 0 * (a 0)⁻¹ := by rw [h4]
    _ = 1 := mul_inv_cancel _

theorem gS_comm_tor10 (hpq : p ∣ Nat.card K + 1) {a : Fin 3 → (Qext K)ˣ} (ha : ∀ i, a i ^ p = 1)
    (h0 : a 0 = 1) : gS K * tor10 hpq a ha = tor10 hpq a ha * gS K := by
  have h1 := gS_conj hpq ha
  have h2 : (![(a 0)⁻¹, a 1, a 2] : Fin 3 → (Qext K)ˣ) = a := by
    funext i
    fin_cases i <;> simp [h0]
  rw [h2] at h1
  apply Subtype.ext
  change (gS K).1 * torusEquiv a = torusEquiv a * (gS K).1
  exact mul_inv_eq_iff_eq_mul.mp h1

theorem gS_mem_sBlk : gS K ∈ sBlk K := by
  intro a
  refine ⟨?_, ?_⟩
  · funext i
    rw [show (gS K).1 (sg 1 a) i = _ from gS_apply _ i]
    by_cases hi : i = 0
    · subst hi
      simp
    · simp [hi]
  · funext i
    rw [show (gS K).1 (sg 2 a) i = _ from gS_apply _ i]
    by_cases hi : i = 0
    · subst hi
      simp
    · simp [hi]

namespace Sp6Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} (C : Sp6Ctx p A c L E f K)

theorem kfAtBlock_gS : KFAt p E f (E.normalizerMonoidHom
    ⟨C.phi (gS K), C.mem_normalizer (gS_hg1 C.hpq') (gS_hg2 C.hpq')⟩) ∧
    kZero p E (E.normalizerMonoidHom
      ⟨C.phi (gS K), C.mem_normalizer (gS_hg1 C.hpq') (gS_hg2 C.hpq')⟩) = (sBlk K).map C.phi := by
  have hp := C.h.prime
  have hp2 := C.hp2
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpq := C.hpq'
  obtain ⟨ζ, hζ⟩ := exists_unit_primitiveRoot hp hp2 hpq
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  obtain ⟨hBqs, hBc, hBmodel⟩ := sBlk_model C.hK C.hf2
  set zv : Fin 3 → (Qext K)ˣ := ![ζ, 1, 1] with hzvdef
  have hzv : ∀ i, zv i ^ p = 1 := by
    intro i
    fin_cases i <;> simp [zv, hζp]
  have hx1 : ∀ i, (![1, ζ, 1] : Fin 3 → (Qext K)ˣ) i ^ p = 1 := by
    intro i
    fin_cases i <;> simp [hζp]
  have hx2 : ∀ i, (![1, 1, ζ] : Fin 3 → (Qext K)ˣ) i ^ p = 1 := by
    intro i
    fin_cases i <;> simp [hζp]
  refine C.kfAtBlock (gS_hg1 hpq) (gS_hg2 hpq) (sBlk K) hBqs hBc hBmodel ?_ ?_
    (z := tor10 hpq zv hzv) ?_ (tor10_isTor hpq zv hzv) ?_ ?_ ?_ gS_mem_sBlk
  · intro b hb x hx hgx
    obtain ⟨a, ha, hxa⟩ := hx
    have h0 : a 0 = 1 := gS_comm_zero hpq hodd ha hxa hgx
    have := sBlk_comm_tor hb h0
    apply Subtype.ext
    change b.1 * x.1 = x.1 * b.1
    rw [hxa]
    exact this
  · intro m hm b hb
    have hm1 := congrArg (fun y : ↥(M10 K) => y.1)
      (hm (tor10 hpq _ hx1) (tor10_isTor hpq _ hx1) (gS_comm_tor10 hpq hx1 rfl))
    have hm2 := congrArg (fun y : ↥(M10 K) => y.1)
      (hm (tor10 hpq _ hx2) (tor10_isTor hpq _ hx2) (gS_comm_tor10 hpq hx2 rfl))
    exact sBlk_normalized hζ1 hm1 hm2 hb
  · intro a
    refine ⟨?_, ?_⟩
    · change torusEquiv zv (sg 1 a) = sg 1 a
      rw [torusEquiv_sg]
      simp [zv]
    · change torusEquiv zv (sg 2 a) = sg 2 a
      rw [torusEquiv_sg]
      simp [zv]
  · intro h1
    have := congrArg (fun y : ↥(M10 K) => y.1 (sg 0 1) 0) h1
    simp only [tor10_coe, torusEquiv_sg, sg_apply_self] at this
    have h2 : (zv 0 : Qext K) = 1 := by simpa [zv] using this
    exact hζ1 (Units.ext (by simpa [zv] using h2))
  · apply Subtype.ext
    change (gS K).1 * torusEquiv zv * (gS K).1⁻¹ = (tor10 hpq zv hzv)⁻¹.1
    rw [gS_conj hpq hzv, tor10_inv]
    change torusEquiv ![(zv 0)⁻¹, zv 1, zv 2] = torusEquiv zv⁻¹
    congr 1
    funext i
    fin_cases i <;> simp [zv]
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨k, hk⟩ := exists_pow_eq hp hζ (ha 0)
    set uv : Fin 3 → (Qext K)ˣ := ![1, a 1, a 2] with huv
    have hu : ∀ i, uv i ^ p = 1 := by
      intro i
      fin_cases i <;> simp [uv, ha]
    refine ⟨tor10 hpq uv hu, tor10_isTor hpq uv hu, gS_comm_tor10 hpq hu rfl, (k : ℤ), ?_⟩
    rw [zpow_natCast, tor10_npow, tor10_mul]
    apply Subtype.ext
    change x.1 = torusEquiv (uv * zv ^ k)
    rw [hxa]
    congr 1
    funext i
    fin_cases i <;> simp [uv, zv, hk]

end Sp6Ctx

theorem gD_comm_zero (hpq : p ∣ Nat.card K + 1) {x : ↥(M10 K)}
    {a : Fin 3 → (Qext K)ˣ} (ha : ∀ i, a i ^ p = 1) (hxa : x.1 = torusEquiv a)
    (hcomm : gD K * x = x * gD K) : a 0 = a 1 := by
  have h1 : gD K * x * (gD K)⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr hcomm
  have h2 : (gD K).1 * torusEquiv a * (gD K).1⁻¹ = torusEquiv a := by
    rw [← hxa]
    exact congrArg (fun y : ↥(M10 K) => y.1) h1
  rw [gD_conj hpq ha] at h2
  have h3 := torusEquiv_injective h2
  exact (congrFun h3 0).symm

theorem gD_comm_tor10 (hpq : p ∣ Nat.card K + 1) {a : Fin 3 → (Qext K)ˣ} (ha : ∀ i, a i ^ p = 1)
    (h0 : a 0 = a 1) : gD K * tor10 hpq a ha = tor10 hpq a ha * gD K := by
  have h1 := gD_conj hpq ha
  have h2 : (![a 1, a 0, a 2] : Fin 3 → (Qext K)ˣ) = a := by
    funext i
    fin_cases i <;> simp [h0]
  rw [h2] at h1
  apply Subtype.ext
  change (gD K).1 * torusEquiv a = torusEquiv a * (gD K).1
  exact mul_inv_eq_iff_eq_mul.mp h1

theorem gD_mem_dBlk : gD K ∈ dBlk K := by
  refine ⟨fun a => ?_, ⟨fun u hu => ?_, fun c u hu => ?_⟩, ?_⟩
  · funext i
    rw [show (gD K).1 (sg 2 a) i = _ from gD_apply _ i]
    fin_cases i <;> simp
  · rw [show (gD K).1 u 2 = _ from gD_apply _ 2]
    simpa using hu
  · funext i
    simp [gD_apply]
  · change (dMat (gD K).1).det = 1
    have hm : dMat (gD K).1 = !![0, 1; 1, 0] := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [dMat, gD_apply]
    rw [hm, Matrix.det_fin_two_of]
    simp [CharTwo.neg_eq]

namespace Sp6Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} (C : Sp6Ctx p A c L E f K)

theorem kfAtBlock_gD : KFAt p E f (E.normalizerMonoidHom
    ⟨C.phi (gD K), C.mem_normalizer (gD_hg1 C.hpq') (gD_hg2 C.hpq')⟩) ∧
    kZero p E (E.normalizerMonoidHom
      ⟨C.phi (gD K), C.mem_normalizer (gD_hg1 C.hpq') (gD_hg2 C.hpq')⟩) = (dBlk K).map C.phi := by
  have hp := C.h.prime
  have hp2 := C.hp2
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpq := C.hpq'
  obtain ⟨ζ, hζ⟩ := exists_unit_primitiveRoot hp hp2 hpq
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  obtain ⟨hBqs, hBc, hBmodel⟩ := dBlk_model C.hK C.hf2
  set zv : Fin 3 → (Qext K)ˣ := ![ζ, ζ⁻¹, 1] with hzvdef
  have hzv : ∀ i, zv i ^ p = 1 := by
    intro i
    fin_cases i <;> simp [zv, hζp, inv_pow]
  refine C.kfAtBlock (gD_hg1 hpq) (gD_hg2 hpq) (dBlk K) hBqs hBc hBmodel ?_ ?_
    (z := tor10 hpq zv hzv) ?_ (tor10_isTor hpq zv hzv) ?_ ?_ ?_ gD_mem_dBlk
  · intro b hb x hx hgx
    obtain ⟨a, ha, hxa⟩ := hx
    have h0 : a 0 = a 1 := gD_comm_zero hpq ha hxa hgx
    have := dBlk_comm_tor hb h0
    apply Subtype.ext
    change b.1 * x.1 = x.1 * b.1
    rw [hxa]
    exact this
  · intro m hm b hb
    have hcm : CommTorD p m.1 := by
      intro x hx hx01
      exact congrArg (fun y : ↥(M10 K) => y.1)
        (hm (tor10 hpq x hx) (tor10_isTor hpq x hx) (gD_comm_tor10 hpq hx hx01))
    exact dBlk_normalized hp hp2 hpq hcm hζp hζ1 hb
  · refine ⟨fun a => ?_, ⟨fun u hu => ?_, fun c' u hu => ?_⟩, ?_⟩
    · change torusEquiv zv (sg 2 a) = sg 2 a
      rw [torusEquiv_sg]
      simp [zv]
    · change torusEquiv zv u 2 = 0
      simp [torusEquiv_apply, zv, hu]
    · change torusEquiv zv (c' • u) = c' • torusEquiv zv u
      funext i
      simp only [torusEquiv_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · change (dMat (torusEquiv zv)).det = 1
      have hm : dMat (torusEquiv zv) = !![(ζ : Qext K), 0; 0, ((ζ⁻¹ : (Qext K)ˣ) : Qext K)] := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [dMat, torusEquiv_apply, zv]
      rw [hm, Matrix.det_fin_two_of]
      simp
  · intro h1
    have := congrArg (fun y : ↥(M10 K) => y.1 (sg 0 1) 0) h1
    simp only [tor10_coe, torusEquiv_sg, sg_apply_self] at this
    have h2 : (zv 0 : Qext K) = 1 := by simpa [zv] using this
    exact hζ1 (Units.ext (by simpa [zv] using h2))
  · apply Subtype.ext
    change (gD K).1 * torusEquiv zv * (gD K).1⁻¹ = (tor10 hpq zv hzv)⁻¹.1
    rw [gD_conj hpq hzv, tor10_inv]
    change torusEquiv ![zv 1, zv 0, zv 2] = torusEquiv zv⁻¹
    congr 1
    funext i
    fin_cases i <;> simp [zv]
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨s, hsp, hss⟩ := exists_sqrt hodd (show (a 0 * a 1) ^ p = 1 by
      rw [mul_pow, ha 0, ha 1, one_mul])
    obtain ⟨r, hrp, hrr⟩ := exists_sqrt hodd (show (a 0 * (a 1)⁻¹) ^ p = 1 by
      rw [mul_pow, inv_pow, ha 0, ha 1, one_mul, inv_one])
    have hsr : s * r = a 0 := by
      refine eq_of_sq_eq hodd (by rw [mul_pow, hsp, hrp, one_mul]) (ha 0) ?_
      calc s * r * (s * r) = (s * s) * (r * r) := by rw [mul_mul_mul_comm]
        _ = (a 0 * a 1) * (a 0 * (a 1)⁻¹) := by rw [hss, hrr]
        _ = (a 0 * a 0) * (a 1 * (a 1)⁻¹) := mul_mul_mul_comm _ _ _ _
        _ = a 0 * a 0 := by rw [mul_inv_cancel, mul_one]
    have hsr' : s * r⁻¹ = a 1 := by
      refine eq_of_sq_eq hodd (by rw [mul_pow, inv_pow, hsp, hrp, inv_one, one_mul]) (ha 1) ?_
      calc s * r⁻¹ * (s * r⁻¹) = (s * s) * (r * r)⁻¹ := by
            rw [mul_mul_mul_comm, ← mul_inv]
        _ = (a 0 * a 1) * (a 0 * (a 1)⁻¹)⁻¹ := by rw [hss, hrr]
        _ = a 1 * a 1 := by
          rw [mul_inv, inv_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
    obtain ⟨k, hk⟩ := exists_pow_eq hp hζ hrp
    set uv : Fin 3 → (Qext K)ˣ := ![s, s, a 2] with huv
    have hu : ∀ i, uv i ^ p = 1 := by
      intro i
      fin_cases i <;> simp [uv, hsp, ha]
    refine ⟨tor10 hpq uv hu, tor10_isTor hpq uv hu, gD_comm_tor10 hpq hu rfl, (k : ℤ), ?_⟩
    rw [zpow_natCast, tor10_npow, tor10_mul]
    apply Subtype.ext
    change x.1 = torusEquiv (uv * zv ^ k)
    rw [hxa]
    congr 1
    funext i
    fin_cases i
    · simp [uv, zv, hk, hsr]
    · simp [uv, zv, inv_pow, hk, hsr']
    · simp [uv, zv]

theorem kfAt_gS : KFAt p E f (E.normalizerMonoidHom
    ⟨C.phi (gS K), C.mem_normalizer (gS_hg1 C.hpq') (gS_hg2 C.hpq')⟩) := C.kfAtBlock_gS.1

theorem kfAt_gD : KFAt p E f (E.normalizerMonoidHom
    ⟨C.phi (gD K), C.mem_normalizer (gD_hg1 C.hpq') (gD_hg2 C.hpq')⟩) := C.kfAtBlock_gD.1

end Sp6Ctx

end CFSG.RankThree.PartOne.S13K
