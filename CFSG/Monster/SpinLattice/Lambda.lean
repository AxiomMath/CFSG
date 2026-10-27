module

public import CFSG.Monster.Code.LatticeBasic
public import CFSG.Monster.CodeLatticeUnimodular
public import CFSG.Monster.Code.Cocycle

public section

namespace CFSG.Monster.SpinLattice

open CFSG.Monster CFSG.Monster.Code

theorem weight_mod_four' : ∀ d ∈ C, weight d % 4 = 0 := fun _ hd => weight_mod_four hd

abbrev L2 : Type := codeLatticeModTwo C allOnes_mem_C

noncomputable abbrev qL : QuadraticForm (ZMod 2) L2 := codeQuadForm C allOnes_mem_C weight_mod_four'

@[expose] def cls (u : Fin 24 → ℤ) (hu : u ∈ codeLattice C) : L2 :=
  Submodule.Quotient.mk (⟨u, hu⟩ : codeLatticeSubgroup allOnes_mem_C)

theorem cls_add {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    cls u hu + cls v hv = cls (u + v) (add_mem_codeLattice allOnes_mem_C hu hv) := rfl

theorem cls_two_smul {w : Fin 24 → ℤ} (hw : w ∈ codeLattice C)
    (h : (2 : ℤ) • w ∈ codeLattice C) : cls ((2 : ℤ) • w) h = 0 := by
  rw [cls, Submodule.Quotient.mk_eq_zero, mem_two_range_iff]
  exact ⟨⟨w, hw⟩, rfl⟩

theorem cls_congr {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (huv : u = v) :
    cls u hu = cls v (huv ▸ hu) := by
  subst huv; rfl

theorem qL_cls {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    qL (cls u hu) = ((hInt u u / 2 : ℤ) : ZMod 2) :=
  codeQuadForm_mk allOnes_mem_C weight_mod_four' ⟨u, hu⟩

theorem bL_cls {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    QuadraticMap.polarBilin qL (cls u hu) (cls v hv) = ((hInt u v : ℤ) : ZMod 2) :=
  polarBilin_codeQuadForm_mk allOnes_mem_C weight_mod_four' ⟨u, hu⟩ ⟨v, hv⟩

theorem bitLift_intCast (y : ℤ) : bitLift (y : ZMod 2) = y % 2 := by
  rw [bitLift, ZMod.val_intCast]
  omega

theorem mem_of_even {u y : Fin 24 → ℤ} (hu : ∀ i, u i = 2 * y i)
    (hy : (fun i => (y i : ZMod 2)) ∈ C) (hs : (∑ i, u i) % 8 = 0) : u ∈ codeLattice C := by
  refine ⟨0, .inl rfl, _, hy, fun i => ?_, ?_⟩
  · rw [hu i, bitLift_intCast]
    unfold Int.ModEq
    omega
  · unfold Int.ModEq
    omega

theorem bitLift_mul (x y : ZMod 2) : bitLift (x * y) = bitLift x * bitLift y := by
  fin_cases x <;> fin_cases y <;> rfl

theorem bitLift_add' (x y : ZMod 2) :
    bitLift x + bitLift y = bitLift (x + y) + 2 * bitLift (x * y) := by
  fin_cases x <;> fin_cases y <;> rfl

theorem bitLift_sq (x : ZMod 2) : bitLift x * bitLift x = bitLift x := by
  fin_cases x <;> rfl

theorem sum_bitLift_mul (a b : Fin 24 → ZMod 2) :
    ∑ i, bitLift (a i) * bitLift (b i) = hammingNorm (a * b) := by
  rw [← sum_bitLift]
  exact Finset.sum_congr rfl fun i _ => (bitLift_mul _ _).symm

theorem sum_affine (b c : Fin 24 → ℤ) (α β γ δ : ℤ) :
    ∑ k, (α + β * b k + γ * c k + δ * (b k * c k)) =
      24 * α + β * ∑ k, b k + γ * ∑ k, c k + δ * ∑ k, b k * c k := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

@[expose] def lamSum (v : Fin 24 → ZMod 2) : Fin 24 → ℤ :=
  fun k => (hammingNorm v : ℤ) - 4 * bitLift (v k)

theorem lamSum_mem (v : Fin 24 → ZMod 2) : lamSum v ∈ codeLattice C := by
  set n : ℤ := ((hammingNorm v : ℕ) : ℤ)
  have hsum : ∑ k, lamSum v k = 20 * n := by
    simp only [lamSum, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_bitLift, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  set m : ℤ := n % 2
  set t : ZMod 2 := ((n / 2 : ℤ) : ZMod 2)
  have hd : t • Ω ∈ C := C.smul_mem t Ω_mem_C
  refine ⟨m, by omega, t • Ω, hd, fun k => ?_, ?_⟩
  · simp only [lamSum, Pi.smul_apply, Ω, smul_eq_mul, mul_one, t, bitLift_intCast]
    unfold Int.ModEq
    have := bitLift_zero_or_one (v k)
    omega
  · rw [hsum]
    unfold Int.ModEq
    omega

@[expose] def lamVec (v : Fin 24 → ZMod 2) : L2 := cls (lamSum v) (lamSum_mem v)

theorem lamSum_add (v w : Fin 24 → ZMod 2) :
    lamSum v + lamSum w = lamSum (v + w) + (2 : ℤ) • lamSum (v * w) := by
  funext k
  have h1 := hammingNorm_add_add v w
  have h2 := bitLift_add' (v k) (w k)
  simp only [lamSum, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  have h1' : ((hammingNorm (v + w) : ℕ) : ℤ) + 2 * (hammingNorm (v * w) : ℕ) =
      (hammingNorm v : ℕ) + (hammingNorm w : ℕ) := by exact_mod_cast h1
  linear_combination h1'.symm - 4 * h2

theorem lamVec_add (v w : Fin 24 → ZMod 2) : lamVec (v + w) = lamVec v + lamVec w := by
  have h2 : (2 : ℤ) • lamSum (v * w) ∈ codeLattice C :=
    (codeLatticeSubgroup allOnes_mem_C).zsmul_mem (lamSum_mem _) 2
  calc lamVec (v + w) = cls (lamSum (v + w)) (lamSum_mem _) + cls ((2 : ℤ) • lamSum (v * w)) h2 := by
        rw [cls_two_smul (lamSum_mem _) h2, add_zero]
        rfl
    _ = cls (lamSum (v + w) + (2 : ℤ) • lamSum (v * w)) _ := cls_add _ _
    _ = cls (lamSum v + lamSum w) _ := cls_congr _ (lamSum_add v w).symm
    _ = lamVec v + lamVec w := (cls_add _ _).symm

theorem lamVec_zero : lamVec 0 = 0 := by
  have h := lamVec_add 0 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem lamVec_eq_zero_of_mem {c : Fin 24 → ZMod 2} (hc : c ∈ C) : lamVec c = 0 := by
  obtain ⟨s, hs⟩ := four_dvd_wt hc
  set w : Fin 24 → ℤ := fun k => 2 * (s : ℤ) - 2 * bitLift (c k) with hwdef
  have hw : w ∈ codeLattice C := by
    refine mem_of_even (y := fun k => (s : ℤ) - bitLift (c k)) (fun k => by simp only [hwdef]; ring)
      ?_ ?_
    · have : (fun k => (((s : ℤ) - bitLift (c k) : ℤ) : ZMod 2)) = (s : ZMod 2) • Ω + c := by
        funext k
        simp only [Int.cast_sub, Int.cast_natCast, Pi.add_apply, Pi.smul_apply, Ω, smul_eq_mul,
          mul_one, bitLift_cast]
        rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
      rw [this]
      exact C.add_mem (C.smul_mem _ Ω_mem_C) hc
    · simp only [hwdef, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_bitLift, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs]
      push_cast
      omega
  have heq : lamSum c = (2 : ℤ) • w := by
    funext k
    simp only [lamSum, hwdef, Pi.smul_apply, smul_eq_mul, hs]
    push_cast
    ring
  rw [lamVec, cls_congr _ heq, cls_two_smul hw]

@[expose] noncomputable def lamVecLin : (Fin 24 → ZMod 2) →ₗ[ZMod 2] L2 :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := lamVec
      map_zero' := lamVec_zero
      map_add' := lamVec_add }

theorem lamVecLin_apply (v : Fin 24 → ZMod 2) : lamVecLin v = lamVec v := rfl

theorem le_ker_lamVecLin : C ≤ LinearMap.ker lamVecLin := fun _ hc => lamVec_eq_zero_of_mem hc

theorem lamSum_single (i : Fin 24) :
    lamSum (Pi.single i 1) = fun k => 1 - 4 * (Pi.single i (1 : ℤ) : Fin 24 → ℤ) k := by
  funext k
  have h1 : hammingNorm (Pi.single i (1 : ZMod 2) : Fin 24 → ZMod 2) = 1 := by
    rw [hammingNorm, Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext j
    by_cases hj : j = i <;> simp [hj]
  simp only [lamSum, h1]
  by_cases hk : k = i
  · subst hk; simp; rfl
  · simp [hk, bitLift]

@[expose] def Pint (a : Fin 24 → ZMod 2) : ℤ := bitLift (P a)

@[expose] def lamCode (a : Fin 24 → ZMod 2) : Fin 24 → ℤ :=
  fun k => 2 * bitLift (a k) + 2 * Pint a - 4 * Pint a * bitLift (a k)

theorem lamCode_of_P_zero {a : Fin 24 → ZMod 2} (h : P a = 0) :
    lamCode a = fun k => 2 * bitLift (a k) := by
  funext k; simp [lamCode, Pint, h, bitLift]

theorem lamCode_of_P_one {a : Fin 24 → ZMod 2} (h : P a = 1) :
    lamCode a = fun k => 2 * (1 - bitLift (a k)) := by
  funext k; simp only [lamCode, Pint, h]; rw [show bitLift 1 = 1 from rfl]; ring

theorem Pint_zero_or_one (a : Fin 24 → ZMod 2) : Pint a = 0 ∨ Pint a = 1 := bitLift_zero_or_one _

theorem Pint_eq (a : Fin 24 → ZMod 2) : Pint a = ((hammingNorm a / 4 : ℕ) : ℤ) % 2 := by
  rw [Pint, P, ← bitLift_intCast]
  push_cast
  rfl

theorem lamCode_mem {a : Fin 24 → ZMod 2} (ha : a ∈ C) : lamCode a ∈ codeLattice C := by
  obtain ⟨s, hs⟩ := four_dvd_wt ha
  refine mem_of_even (y := fun k => bitLift (a k) + Pint a - 2 * Pint a * bitLift (a k))
    (fun k => by simp only [lamCode]; ring) ?_ ?_
  · have : (fun k => ((bitLift (a k) + Pint a - 2 * Pint a * bitLift (a k) : ℤ) : ZMod 2)) =
        a + (P a) • Ω := by
      funext k
      simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Pint, bitLift_cast, Pi.add_apply,
        Pi.smul_apply, Ω, smul_eq_mul, mul_one]
      rw [show ((2 : ℤ) : ZMod 2) = 0 from rfl, zero_mul, zero_mul, sub_zero]
    rw [this]
    exact C.add_mem ha (C.smul_mem _ Ω_mem_C)
  · have e : ∑ k, lamCode a k = 2 * hammingNorm a + 48 * Pint a - 4 * Pint a * hammingNorm a := by
      have := sum_affine (fun k => bitLift (a k)) (fun k => bitLift (a k)) (2 * Pint a) 2
        (-4 * Pint a) 0
      simp only [sum_bitLift] at this
      rw [← sum_bitLift]
      simp only [lamCode]
      rw [show (∑ k, (2 * bitLift (a k) + 2 * Pint a - 4 * Pint a * bitLift (a k))) =
          ∑ k, (2 * Pint a + 2 * bitLift (a k) + -4 * Pint a * bitLift (a k) +
            0 * (bitLift (a k) * bitLift (a k))) from
        Finset.sum_congr rfl fun k _ => by ring, this, sum_bitLift]
      ring
    rw [e, hs]
    push_cast
    have h16 : 4 * Pint a * (4 * (s : ℤ)) = 8 * (2 * Pint a * s) := by ring
    omega

@[expose] def lamCodeCls {a : Fin 24 → ZMod 2} (ha : a ∈ C) : L2 := cls (lamCode a) (lamCode_mem ha)

private theorem bit01 (x : ZMod 2) : bitLift x = 0 ∨ bitLift x = 1 := bitLift_zero_or_one x

theorem hInt_lamSum (v w : Fin 24 → ZMod 2) :
    hInt (lamSum v) (lamSum w) = 2 * (hammingNorm v : ℤ) * (hammingNorm w : ℤ) +
      2 * (hammingNorm (v * w) : ℤ) := by
  have e : ∑ k, lamSum v k * lamSum w k = 16 * (hammingNorm v : ℤ) * (hammingNorm w : ℤ) +
      16 * (hammingNorm (v * w) : ℤ) := by
    have h := sum_affine (fun k => bitLift (v k)) (fun k => bitLift (w k))
      ((hammingNorm v : ℤ) * (hammingNorm w : ℤ)) (-4 * (hammingNorm w : ℤ))
      (-4 * (hammingNorm v : ℤ)) 16
    rw [sum_bitLift, sum_bitLift, sum_bitLift_mul] at h
    rw [show (∑ k, lamSum v k * lamSum w k) = ∑ k, ((hammingNorm v : ℤ) * (hammingNorm w : ℤ) +
        -4 * (hammingNorm w : ℤ) * bitLift (v k) + -4 * (hammingNorm v : ℤ) * bitLift (w k) +
        16 * (bitLift (v k) * bitLift (w k))) from
      Finset.sum_congr rfl fun k _ => by simp only [lamSum]; ring, h]
    ring
  rw [hInt, e, show 16 * (hammingNorm v : ℤ) * (hammingNorm w : ℤ) + 16 * (hammingNorm (v * w) : ℤ)
    = 8 * (2 * (hammingNorm v : ℤ) * (hammingNorm w : ℤ) + 2 * (hammingNorm (v * w) : ℤ)) by ring,
    Int.mul_ediv_cancel_left _ (by norm_num)]

theorem qL_lamVec (v : Fin 24 → ZMod 2) : qL (lamVec v) = 0 := by
  rw [lamVec, qL_cls, hInt_lamSum]
  have h : 2 * (hammingNorm v : ℤ) * (hammingNorm v : ℤ) + 2 * (hammingNorm (v * v) : ℤ) =
      2 * ((hammingNorm v : ℤ) * (hammingNorm v : ℤ) + (hammingNorm v : ℤ)) := by
    have : v * v = v := by
      funext k
      simp only [Pi.mul_apply]
      generalize v k = x
      fin_cases x <;> rfl
    rw [this]; ring
  rw [h, Int.mul_ediv_cancel_left _ (by norm_num)]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (by
    have := Int.even_mul_succ_self (hammingNorm v : ℤ)
    rw [mul_add, mul_one] at this
    exact even_iff_two_dvd.1 this)

theorem bL_lamVec_lamVec (v w : Fin 24 → ZMod 2) :
    QuadraticMap.polarBilin qL (lamVec v) (lamVec w) = 0 := by
  rw [lamVec, lamVec, bL_cls, hInt_lamSum]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2
    ⟨(hammingNorm v : ℤ) * (hammingNorm w : ℤ) + (hammingNorm (v * w) : ℤ), by ring⟩

theorem cast_Pint (a : Fin 24 → ZMod 2) : ((Pint a : ℤ) : ZMod 2) = P a := bitLift_cast _

theorem P_eq_of_hammingNorm {a : Fin 24 → ZMod 2} {s : ℕ} (hs : hammingNorm a = 4 * s) :
    P a = (s : ZMod 2) := by
  rw [P, hs, Nat.mul_div_cancel_left _ (by norm_num)]

theorem qL_lamCodeCls {a : Fin 24 → ZMod 2} (ha : a ∈ C) : qL (lamCodeCls ha) = P a := by
  obtain ⟨s, hs⟩ := four_dvd_wt ha
  have hP := Pint_zero_or_one a
  have e : ∑ k, lamCode a k * lamCode a k = 8 * (12 * Pint a + 2 * s - 4 * (Pint a * s)) := by
    have h := sum_affine (fun k => bitLift (a k)) (fun k => bitLift (a k)) (4 * Pint a)
      (4 - 8 * Pint a) 0 0
    rw [sum_bitLift, sum_bitLift_mul] at h
    rw [show (∑ k, lamCode a k * lamCode a k) = ∑ k, (4 * Pint a + (4 - 8 * Pint a) *
        bitLift (a k) + 0 * bitLift (a k) + 0 * (bitLift (a k) * bitLift (a k))) from
      Finset.sum_congr rfl fun k _ => by
        simp only [lamCode]
        rcases bit01 (a k) with hb | hb <;> rcases hP with hp | hp <;> rw [hb, hp] <;> ring, h, hs]
    push_cast
    ring
  rw [lamCodeCls, qL_cls, hInt, e, Int.mul_ediv_cancel_left _ (by norm_num)]
  have h2 : (12 * Pint a + 2 * (s : ℤ) - 4 * (Pint a * s)) / 2 =
      6 * Pint a + s - 2 * (Pint a * s) := by omega
  rw [h2]
  push_cast
  rw [cast_Pint, P_eq_of_hammingNorm hs]
  generalize ((s : ℕ) : ZMod 2) = x
  revert x
  decide

theorem bL_lamCodeCls_lamVec {a : Fin 24 → ZMod 2} (ha : a ∈ C) (v : Fin 24 → ZMod 2) :
    QuadraticMap.polarBilin qL (lamCodeCls ha) (lamVec v) = a ⬝ᵥ v := by
  obtain ⟨s, hs⟩ := four_dvd_wt ha
  have e : ∑ k, lamCode a k * lamSum v k =
      8 * (5 * Pint a * (hammingNorm v : ℤ) + ((hammingNorm v : ℤ) - 2 * Pint a *
        (hammingNorm v : ℤ)) * s + (2 * Pint a - 1) * (hammingNorm (a * v) : ℤ)) := by
    have h := sum_affine (fun k => bitLift (a k)) (fun k => bitLift (v k))
      (2 * Pint a * (hammingNorm v : ℤ)) (2 * (hammingNorm v : ℤ) - 4 * Pint a *
        (hammingNorm v : ℤ)) (-8 * Pint a) (16 * Pint a - 8)
    rw [sum_bitLift, sum_bitLift, sum_bitLift_mul] at h
    rw [show (∑ k, lamCode a k * lamSum v k) = ∑ k, (2 * Pint a * (hammingNorm v : ℤ) +
        (2 * (hammingNorm v : ℤ) - 4 * Pint a * (hammingNorm v : ℤ)) * bitLift (a k) +
        -8 * Pint a * bitLift (v k) + (16 * Pint a - 8) * (bitLift (a k) * bitLift (v k))) from
      Finset.sum_congr rfl fun k _ => by simp only [lamCode, lamSum]; ring, h, hs]
    push_cast
    ring
  rw [lamCodeCls, lamVec, bL_cls, hInt, e, Int.mul_ediv_cancel_left _ (by norm_num),
    dotProduct_eq_hammingNorm]
  push_cast
  rw [cast_Pint, P_eq_of_hammingNorm hs]
  generalize ((s : ℕ) : ZMod 2) = x
  generalize ((hammingNorm v : ℕ) : ZMod 2) = y
  generalize ((hammingNorm (a * v) : ℕ) : ZMod 2) = z
  revert x y z
  decide

theorem bL_lamCodeCls_lamCodeCls {a b : Fin 24 → ZMod 2} (ha : a ∈ C) (hb : b ∈ C) :
    QuadraticMap.polarBilin qL (lamCodeCls ha) (lamCodeCls hb) = K a b := by
  obtain ⟨s, hs⟩ := four_dvd_wt ha
  obtain ⟨t, ht⟩ := four_dvd_wt hb
  obtain ⟨m, hm⟩ := two_dvd_hammingNorm_mul ha hb
  have hP := Pint_zero_or_one a
  have hR := Pint_zero_or_one b
  have e : ∑ k, lamCode a k * lamCode b k = 8 * (12 * Pint a * Pint b + 2 * Pint b * s -
      4 * Pint a * Pint b * s + 2 * Pint a * t - 4 * Pint a * Pint b * t + m - 2 * Pint b * m -
      2 * Pint a * m + 4 * Pint a * Pint b * m) := by
    have h := sum_affine (fun k => bitLift (a k)) (fun k => bitLift (b k)) (4 * Pint a * Pint b)
      (4 * Pint b - 8 * Pint a * Pint b) (4 * Pint a - 8 * Pint a * Pint b)
      (4 - 8 * Pint b - 8 * Pint a + 16 * Pint a * Pint b)
    rw [sum_bitLift, sum_bitLift, sum_bitLift_mul] at h
    rw [show (∑ k, lamCode a k * lamCode b k) = ∑ k, (4 * Pint a * Pint b +
        (4 * Pint b - 8 * Pint a * Pint b) * bitLift (a k) +
        (4 * Pint a - 8 * Pint a * Pint b) * bitLift (b k) +
        (4 - 8 * Pint b - 8 * Pint a + 16 * Pint a * Pint b) * (bitLift (a k) * bitLift (b k))) from
      Finset.sum_congr rfl fun k _ => by simp only [lamCode]; ring, h, hs, ht, hm]
    push_cast
    ring
  rw [lamCodeCls, lamCodeCls, bL_cls, hInt, e, Int.mul_ediv_cancel_left _ (by norm_num), K_eq,
    hm, Nat.mul_div_cancel_left _ (by norm_num)]
  push_cast
  rw [cast_Pint, cast_Pint]
  generalize P a = x
  generalize P b = y
  generalize ((s : ℕ) : ZMod 2) = u
  generalize ((t : ℕ) : ZMod 2) = u'
  generalize ((m : ℕ) : ZMod 2) = z
  revert x y u u' z
  decide

theorem lamCodeCls_add {a b : Fin 24 → ZMod 2} (ha : a ∈ C) (hb : b ∈ C) :
    lamCodeCls ha + lamCodeCls hb = lamCodeCls (C.add_mem ha hb) + lamVec (a * b) := by
  obtain ⟨s, hs⟩ := four_dvd_wt ha
  obtain ⟨t, ht⟩ := four_dvd_wt hb
  obtain ⟨m, hm⟩ := two_dvd_hammingNorm_mul ha hb
  set P₁ := Pint a
  set R₁ := Pint b
  set S₁ := Pint (a + b)
  have hpar : (2 : ℤ) ∣ P₁ + R₁ - S₁ - m := by
    have h := P_add ha hb
    rw [K_eq, hm, Nat.mul_div_cancel_left _ (by norm_num)] at h
    have h0 : ((P₁ + R₁ - S₁ - m : ℤ) : ZMod 2) = 0 := by
      push_cast
      rw [cast_Pint, cast_Pint, cast_Pint, h]
      generalize P a = x
      generalize P b = y
      generalize ((m : ℕ) : ZMod 2) = z
      revert x y z
      decide
    have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (P₁ + R₁ - S₁ - m) 2).1 h0
    exact_mod_cast h1
  obtain ⟨c', hc'⟩ := hpar
  set w : Fin 24 → ℤ := fun k => 2 * c' + (2 * S₁ - 2 * P₁) * bitLift (a k) +
    (2 * S₁ - 2 * R₁) * bitLift (b k) + (4 - 4 * S₁) * (bitLift (a k) * bitLift (b k)) with hwdef
  have hw : w ∈ codeLattice C := by
    refine mem_of_even (y := fun k => c' + (S₁ - P₁) * bitLift (a k) + (S₁ - R₁) * bitLift (b k) +
      (2 - 2 * S₁) * (bitLift (a k) * bitLift (b k))) (fun k => by simp only [hwdef]; ring) ?_ ?_
    · have : (fun k => ((c' + (S₁ - P₁) * bitLift (a k) + (S₁ - R₁) * bitLift (b k) +
          (2 - 2 * S₁) * (bitLift (a k) * bitLift (b k)) : ℤ) : ZMod 2)) =
          (c' : ZMod 2) • Ω + ((S₁ - P₁ : ℤ) : ZMod 2) • a + ((S₁ - R₁ : ℤ) : ZMod 2) • b := by
        funext k
        simp only [Int.cast_add, Int.cast_mul, Int.cast_sub, bitLift_cast, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, Ω, mul_one]
        rw [show ((2 : ℤ) : ZMod 2) = 0 from rfl]
        ring
      rw [this]
      exact C.add_mem (C.add_mem (C.smul_mem _ Ω_mem_C) (C.smul_mem _ ha)) (C.smul_mem _ hb)
    · have h := sum_affine (fun k => bitLift (a k)) (fun k => bitLift (b k)) (2 * c')
        (2 * S₁ - 2 * P₁) (2 * S₁ - 2 * R₁) (4 - 4 * S₁)
      rw [sum_bitLift, sum_bitLift, sum_bitLift_mul, hs, ht, hm] at h
      rw [show (∑ k, w k) = _ from h]
      push_cast
      have e : 24 * (2 * c') + (2 * S₁ - 2 * P₁) * (4 * (s : ℤ)) + (2 * S₁ - 2 * R₁) * (4 * t) +
          (4 - 4 * S₁) * (2 * m) = 8 * (6 * c' + (S₁ - P₁) * s + (S₁ - R₁) * t + (1 - S₁) * m) := by
        ring
      rw [e]
      omega
  have hvec : lamCode a + lamCode b = lamCode (a + b) + lamSum (a * b) + (2 : ℤ) • w := by
    funext k
    have h3 := bitLift_add' (a k) (b k)
    have h12 := bitLift_mul (a k) (b k)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lamCode, lamSum, Pi.mul_apply, hwdef]
    rw [h12, hm]
    have hb3 : bitLift (a k + b k) = bitLift (a k) + bitLift (b k) - 2 * (bitLift (a k) *
        bitLift (b k)) := by
      rw [h12] at h3; linarith
    rw [hb3]
    push_cast
    linear_combination (2 : ℤ) * hc'
  have h2w : (2 : ℤ) • w ∈ codeLattice C := (codeLatticeSubgroup allOnes_mem_C).zsmul_mem hw 2
  have hXY : lamCode (a + b) + lamSum (a * b) ∈ codeLattice C :=
    add_mem_codeLattice allOnes_mem_C (lamCode_mem (C.add_mem ha hb)) (lamSum_mem _)
  calc lamCodeCls ha + lamCodeCls hb = cls (lamCode a + lamCode b)
        (add_mem_codeLattice allOnes_mem_C (lamCode_mem ha) (lamCode_mem hb)) := cls_add _ _
    _ = cls (lamCode (a + b) + lamSum (a * b) + (2 : ℤ) • w)
        (add_mem_codeLattice allOnes_mem_C hXY h2w) := cls_congr _ hvec
    _ = cls (lamCode (a + b) + lamSum (a * b)) hXY + cls ((2 : ℤ) • w) h2w := (cls_add hXY h2w).symm
    _ = lamCodeCls (C.add_mem ha hb) + lamVec (a * b) := by
        rw [cls_two_smul hw h2w, add_zero, lamCodeCls, lamVec, cls_add]

end CFSG.Monster.SpinLattice
