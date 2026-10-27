module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.Assembly.Defs
import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag
import CFSG.RankThree.PartTwo.Sec4.LThreePiEigen
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusLinear
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace ProofKS1623Parab

open CFSG
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

theorem psi_eq_of_traces {K : Type} [Field K] [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (ψ : K →+* K) (hψω : ψ ω = ω ^ 2) {a b c : K} (h0 : ψ (a + b + c) = a + b + c)
    (h1 : ψ (ω * a + ω ^ 2 * b + c) = ω * a + ω ^ 2 * b + c)
    (h2 : ψ (ω ^ 2 * a + ω * b + c) = ω ^ 2 * a + ω * b + c) : ψ a = b := by
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have ha : a = (a + b + c) + ω ^ 2 * (ω * a + ω ^ 2 * b + c) + ω * (ω ^ 2 * a + ω * b + c) := by
    linear_combination (-ω ^ 3 * a) * h2K + (-b - c) * hω + (-b * ω) * hω3
  calc ψ a = ψ ((a + b + c) + ω ^ 2 * (ω * a + ω ^ 2 * b + c) +
        ω * (ω ^ 2 * a + ω * b + c)) := congrArg ψ ha
    _ = (a + b + c) + ω ^ 4 * (ω * a + ω ^ 2 * b + c) + ω ^ 2 * (ω ^ 2 * a + ω * b + c) := by
        rw [map_add, map_add, map_mul, map_mul, map_pow, hψω, h0, h1, h2]
        ring
    _ = b := by
        linear_combination (a + c) * hω +
          (a * ω + a * ω ^ 2 + c * ω + b * (ω ^ 3 + 2)) * hω3 + b * h2K

theorem univ_eq_of_distinct {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (Finset.univ : Finset (Fin 3)) = {i, j, k} := by
  symm
  apply Finset.eq_univ_of_card
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · rfl
  · simpa using hjk
  · simp [hij, hik]

theorem prod_fin_three_of_distinct {R : Type*} [CommMonoid R] (f : Fin 3 → R) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : ∏ l, f l = f i * f j * f k := by
  rw [univ_eq_of_distinct hij hik hjk, Finset.prod_insert (by simp [hij, hik]),
    Finset.prod_insert (by simpa using hjk), Finset.prod_singleton, mul_assoc]

theorem sum_fin_three_of_distinct {R : Type*} [AddCommMonoid R] (f : Fin 3 → R) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : ∑ l, f l = f i + f j + f k := by
  rw [univ_eq_of_distinct hij hik hjk, Finset.sum_insert (by simp [hij, hik]),
    Finset.sum_insert (by simpa using hjk), Finset.sum_singleton, add_assoc]

theorem eq_or_eq_or_eq_of_distinct {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (l : Fin 3) : l = i ∨ l = j ∨ l = k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all

theorem conj_mul_conj {K : Type} [Field K] {g gi X Y : Matrix (Fin 3) (Fin 3) K}
    (hggi : g * gi = 1) : (gi * X * g) * (gi * Y * g) = gi * (X * Y) * g := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc g gi, hggi, Matrix.one_mul]

theorem false_of_two {F : Type} [Field F] [Finite F] [CharP F 2] (hq : Nat.card F % 3 = 2)
    {b : projectiveSL 3 F} (hb : orderOf b = 3) {p : ℕ} (hp : p.Prime)
    {P : Subgroup (projectiveSL 3 F)}
    (hPC : P ≤ Subgroup.centralizer ({b} : Set (projectiveSL 3 F)))
    (hPel : CFSG.Assembly.IsElemAbelian p P) (hPc : Nat.card P = p ^ 2) : False := by
  classical
  have := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have hcube : ∀ c : Fˣ, c ^ 3 = 1 → c = 1 := by
    intro c hc
    have hdvd : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      have h3' : 3 ∣ Nat.card Fˣ := h3 ▸ orderOf_dvd_natCard c
      rw [Nat.card_units] at h3'
      have h1 : 1 ≤ Nat.card F := Nat.card_pos
      omega
  have hscal : ∀ z ∈ scalars 3 F, z = 1 := by
    intro z hz
    obtain ⟨c, hc3, hzc⟩ := mem_scalars.mp hz
    apply Subtype.ext
    rw [hzc, hcube c hc3, Units.val_one, map_one]
    rfl
  have hproj : ∀ x y : SpecialLinearGroup (Fin 3) F, proj 3 F x = proj 3 F y → x = y := by
    intro x y hxy
    have := hscal _ (proj_eq_proj_iff.mp hxy)
    rw [inv_mul_eq_one] at this
    exact this
  obtain ⟨B, rfl⟩ := proj_surjective 3 F b
  have hB3 : B ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one (proj 3 F B)
    rw [hb] at h1
    exact hproj _ _ (by rw [map_pow, h1, map_one])
  have hlift : ∀ x : P, ∃ h : SpecialLinearGroup (Fin 3) F, proj 3 F h = x :=
    fun x => proj_surjective 3 F x
  choose hx hhx using hlift
  have hcomm : ∀ x : P, hx x * B = B * hx x := by
    intro x
    apply hproj
    rw [map_mul, map_mul, hhx]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPC x.2)
  have hmul : ∀ x y : P, hx (x * y) = hx x * hx y := fun x y =>
    hproj _ _ (by rw [hhx, map_mul, hhx, hhx]; rfl)
  have hone : hx 1 = 1 := hproj _ _ (by rw [hhx, map_one]; rfl)
  obtain ⟨K, _, _, φ, ω, hω⟩ := Sec6.BThreeCensus.exists_splittingField_cubeRoot F
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have h2K : (2 : K) = 0 := by
    rw [show (2 : K) = φ 2 by rw [map_ofNat], h2F, map_zero]
  have : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by exact_mod_cast h2K)
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    have : (1 : K) = 0 := by linear_combination hω - h2K
    exact one_ne_zero this
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have h3K : (3 : K) ≠ 0 := by
    intro h3
    have : (1 : K) = 0 := by linear_combination h3 - h2K
    exact one_ne_zero this
  set B' : Matrix (Fin 3) (Fin 3) K := B.val.map φ with hB'
  have hB'3 : B' ^ 3 = 1 := by
    rw [hB', ← Matrix.map_pow, show B.val ^ 3 = (B ^ 3).val from rfl, hB3]
    exact Matrix.map_one φ (map_zero φ) (map_one φ)
  have hB's : ∀ a : K, B' ≠ a • 1 := by
    intro a ha
    have hBs := Sec6.BThreeCensus.eq_smul_one_of_map_eq_smul_one φ ha
    have hdet : (B.val 0 0) ^ 3 = 1 := by
      have := B.prop
      rw [hBs, det_smul, det_one, mul_one, Fintype.card_fin] at this
      exact this
    have h00 : B.val 0 0 ≠ 0 := by
      intro h0
      rw [h0] at hdet
      norm_num at hdet
    have hBZ : B ∈ scalars 3 F := by
      refine ⟨Units.mk0 _ h00, ?_, ?_⟩
      · apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, hdet, Units.val_one]
      · rw [Units.val_mk0, scalar_apply, ← smul_one_eq_diagonal]
        exact hBs
    have h1 := hscal B hBZ
    rw [h1, one_pow] at hB3
    have : proj 3 F B = 1 := by rw [h1, map_one]
    rw [this, orderOf_one] at hb
    norm_num at hb
  obtain ⟨g, j, hg, hform⟩ := Sec4.exists_normal_form hω3 hω1 h3K hB'3 hB's
  have hgdet : g.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g).mp hg).ne_zero
  have hdetB' : B'.det = 1 := by
    rw [hB', show B.val.map φ = φ.mapMatrix B.val from rfl, ← RingHom.map_det, B.prop, map_one]
  have hdetD : ∀ {D : Matrix (Fin 3) (Fin 3) K}, (ω ^ (j : ℕ) • B') * g = g * D → D.det = 1 := by
    intro D hD
    have h1 := congrArg Matrix.det hD
    rw [det_mul, det_mul, det_smul, hdetB', Fintype.card_fin, mul_one, ← pow_mul,
      mul_comm (j : ℕ) 3, pow_mul, hω3, one_pow, one_mul] at h1
    exact (mul_right_eq_self₀.1 h1.symm).resolve_right hgdet
  rcases hform with hD | hD | hD
  swap
  · have h1 := hdetD hD
    rw [det_diagonal, Fin.prod_univ_three] at h1
    simp at h1
    exact hω1 h1
  swap
  · have h1 := hdetD hD
    rw [det_diagonal, Fin.prod_univ_three] at h1
    change ω ^ 2 * 1 * 1 = 1 at h1
    rw [mul_one, mul_one] at h1
    exact hω1 (by linear_combination hω3 - ω * h1)
  have hgu : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg
  set gi := g⁻¹ with hgidef
  have hgig : gi * g = 1 := Matrix.nonsing_inv_mul g hgu
  have hggi : g * gi = 1 := Matrix.mul_nonsing_inv g hgu
  have hωj : ω ^ (j : ℕ) ≠ 0 := pow_ne_zero _ hω0
  set d : Fin 3 → K := (ω ^ (j : ℕ))⁻¹ • ![ω, ω ^ 2, 1] with hd
  have hBg : B' * g = g * diagonal d := by
    have h1 : B' * g = (ω ^ (j : ℕ))⁻¹ • ((ω ^ (j : ℕ) • B') * g) := by
      rw [Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hωj, one_smul]
    rw [h1, hD, hd, diagonal_smul, Matrix.mul_smul]
  have hDconj : diagonal d = gi * B' * g := by
    rw [Matrix.mul_assoc, hBg, ← Matrix.mul_assoc, hgig, Matrix.one_mul]
  have hBconj : B' = g * diagonal d * gi := by
    rw [hDconj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hggi, Matrix.one_mul, Matrix.mul_assoc,
      hggi, Matrix.mul_one]
  have hinv : ω⁻¹ = ω ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', hω3]
  have hω4 : (ω ^ 2) ^ 2 = ω := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hω3, one_mul]
  have hinv2 : (ω ^ 2)⁻¹ = ω := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ, hω3]
  obtain ⟨i1, i2, i0, h12, h10, h20, hd1, hd2, hd0⟩ : ∃ i1 i2 i0 : Fin 3, i1 ≠ i2 ∧ i1 ≠ i0 ∧
      i2 ≠ i0 ∧ d i1 = ω ∧ d i2 = ω ^ 2 ∧ d i0 = 1 := by
    fin_cases j
    · refine ⟨0, 1, 2, by decide, by decide, by decide, ?_, ?_, ?_⟩ <;>
        simp [hd]
    · refine ⟨1, 2, 0, by decide, by decide, by decide, ?_, ?_, ?_⟩ <;>
        simp only [hd, Pi.smul_apply, smul_eq_mul, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pow_one,
          hinv]
      · linear_combination ω * hω3
      · rw [mul_one]
      · linear_combination hω3
    · refine ⟨2, 0, 1, by decide, by decide, by decide, ?_, ?_, ?_⟩ <;>
        simp only [hd, Pi.smul_apply, smul_eq_mul, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hinv2]
      · rw [mul_one]
      · rw [← sq]
      · rw [← pow_succ', hω3]
  have hv12 : ω ≠ ω ^ 2 := by
    intro h
    apply hω1
    have : ω * ω = ω * 1 := by rw [← sq, ← h, mul_one]
    exact mul_left_cancel₀ hω0 this
  have hv2 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [hω3, h, inv_one, one_mul]
  have hdne : ∀ i k, i ≠ k → d i ≠ d k := by
    intro i k hik
    rcases eq_or_eq_or_eq_of_distinct h12 h10 h20 i with rfl | rfl | rfl <;>
    rcases eq_or_eq_or_eq_of_distinct h12 h10 h20 k with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hik
      | (rw [hd1, hd2]; exact hv12)
      | (rw [hd1, hd0]; exact hω1)
      | (rw [hd2, hd1]; exact hv12.symm)
      | (rw [hd2, hd0]; exact hv2)
      | (rw [hd0, hd1]; exact Ne.symm hω1)
      | (rw [hd0, hd2]; exact Ne.symm hv2)
  set Λ : P → Matrix (Fin 3) (Fin 3) K := fun x => gi * (hx x).val.map φ * g with hΛ
  have hcomm' : ∀ x : P, (hx x).val.map φ * B' = B' * (hx x).val.map φ := by
    intro x
    have h1 := congrArg (fun A : SpecialLinearGroup (Fin 3) F => A.val.map φ) (hcomm x)
    simp only [show ∀ A C : SpecialLinearGroup (Fin 3) F, (A * C).val = A.val * C.val from
      fun _ _ => rfl, Matrix.map_mul] at h1
    exact h1
  have hΛD : ∀ x, Λ x * diagonal d = diagonal d * Λ x := by
    intro x
    rw [hDconj]
    simp only [hΛ]
    rw [conj_mul_conj hggi, conj_mul_conj hggi, hcomm' x]
  have hΛdiag : ∀ x, Λ x = diagonal fun i => Λ x i i := by
    intro x
    ext i k
    by_cases hik : i = k
    · subst hik
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hik]
      exact Sec4.entry_eq_zero_of_commute_diagonal (hΛD x) (hdne i k hik)
  have hΛmul : ∀ x y, Λ (x * y) = Λ x * Λ y := by
    intro x y
    simp only [hΛ, hmul, show ∀ A C : SpecialLinearGroup (Fin 3) F, (A * C).val = A.val * C.val
      from fun _ _ => rfl, Matrix.map_mul]
    rw [conj_mul_conj hggi]
  have hΛ1 : Λ 1 = 1 := by
    simp only [hΛ, hone]
    rw [show (1 : SpecialLinearGroup (Fin 3) F).val = 1 from rfl,
      Matrix.map_one φ (map_zero φ) (map_one φ), Matrix.mul_one, hgig]
  have hentry : ∀ x y i, Λ (x * y) i i = Λ x i i * Λ y i i := by
    intro x y i
    rw [hΛmul]
    conv_lhs => rw [hΛdiag x, hΛdiag y]
    rw [diagonal_mul_diagonal, diagonal_apply_eq]
  let χ : P →* K :=
    { toFun := fun x => Λ x i1 i1
      map_one' := by simp only [hΛ1, Matrix.one_apply_eq]
      map_mul' := fun x y => hentry x y i1 }
  obtain ⟨nF, -, hnF⟩ := FiniteField.card F 2
  set ψ : K →+* K := iterateFrobenius K 2 (nF : ℕ) with hψ
  have hψφ : ∀ a : F, ψ (φ a) = φ a := by
    intro a
    rw [hψ, iterateFrobenius_def, ← map_pow, ← hnF, FiniteField.pow_card]
  have hψω : ψ ω = ω ^ 2 := by
    have hq' : 2 ^ (nF : ℕ) % 3 = 2 := by
      rw [← hnF, ← Nat.card_eq_fintype_card]
      exact hq
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
    rw [hψ, iterateFrobenius_def, ← pow_mod_orderOf, hord, hq']
  have hpowB : ∀ k : ℕ, B' ^ k = g * diagonal d ^ k * gi := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hggi]
    | succ k ih =>
      rw [pow_succ, ih, hBconj, pow_succ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc gi g, hgig, Matrix.one_mul]
  have htr : ∀ x : P, ∀ k : ℕ, ψ (∑ l, d l ^ k * Λ x l l) = ∑ l, d l ^ k * Λ x l l := by
    intro x k
    have h1 : ∑ l, d l ^ k * Λ x l l = trace (diagonal d ^ k * Λ x) := by
      rw [diagonal_pow, trace]
      congr 1
      funext l
      rw [diag_apply, diagonal_mul]
      rfl
    have h2 : trace (diagonal d ^ k * Λ x) = φ (trace ((B ^ k * hx x).val)) := by
      rw [AddMonoidHom.map_trace φ, show (B ^ k * hx x).val = B.val ^ k * (hx x).val from rfl,
        Matrix.map_mul, Matrix.map_pow, ← hB', hpowB]
      simp only [hΛ]
      rw [Matrix.mul_assoc g, Matrix.mul_assoc g, Matrix.trace_mul_comm g]
      simp only [Matrix.mul_assoc]
    rw [h1, h2, hψφ]
  have hψab : ∀ x : P, ψ (Λ x i1 i1) = Λ x i2 i2 := by
    intro x
    have t0 := htr x 0
    have t1 := htr x 1
    have t2 := htr x 2
    rw [sum_fin_three_of_distinct _ h12 h10 h20, hd1, hd2, hd0] at t0 t1 t2
    simp only [pow_zero, one_mul, pow_one, one_pow] at t0 t1 t2
    rw [hω4] at t2
    exact psi_eq_of_traces hω ψ hψω t0 t1 t2
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro x hx1
    have ha : Λ x i1 i1 = 1 := hx1
    have hb : Λ x i2 i2 = 1 := by rw [← hψab x, ha, map_one]
    have hdetΛ : Λ x i1 i1 * Λ x i2 i2 * Λ x i0 i0 = 1 := by
      have h1 : (Λ x).det = 1 := by
        simp only [hΛ]
        have hgg : gi.det * g.det = 1 := by rw [← det_mul, hgig, det_one]
        rw [det_mul, det_mul, mul_right_comm, hgg, one_mul,
          show (hx x).val.map φ = φ.mapMatrix (hx x).val from rfl, ← RingHom.map_det,
          (hx x).prop, map_one]
      rw [hΛdiag x, det_diagonal, prod_fin_three_of_distinct _ h12 h10 h20] at h1
      exact h1
    have hc : Λ x i0 i0 = 1 := by
      rw [ha, hb, one_mul, one_mul] at hdetΛ
      exact hdetΛ
    have hΛx : Λ x = 1 := by
      rw [hΛdiag x, ← diagonal_one]
      congr 1
      funext i
      rcases eq_or_eq_or_eq_of_distinct h12 h10 h20 i with rfl | rfl | rfl
      exacts [ha, hb, hc]
    have hh' : (hx x).val.map φ = 1 := by
      calc (hx x).val.map φ = g * (gi * (hx x).val.map φ * g) * gi := by
            simp only [Matrix.mul_assoc]
            rw [hggi, Matrix.mul_one, ← Matrix.mul_assoc, hggi, Matrix.one_mul]
        _ = g * Λ x * gi := rfl
        _ = 1 := by rw [hΛx, Matrix.mul_one, hggi]
    have hhx1 : hx x = 1 := by
      apply Subtype.ext
      ext i k
      have h1 := congrFun (congrFun hh' i) k
      rw [Matrix.map_apply, Matrix.one_apply] at h1
      rw [show (1 : SpecialLinearGroup (Fin 3) F).val = 1 from rfl, Matrix.one_apply]
      split_ifs at h1 ⊢
      · exact φ.injective (h1.trans (map_one φ).symm)
      · exact φ.injective (h1.trans (map_zero φ).symm)
    apply Subtype.ext
    rw [← hhx x, hhx1, map_one]
    rfl
  have hcyc := isCyclic_of_injective_ringHom χ hinj
  obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := P)
  have hord : orderOf y = p ^ 2 := by rw [orderOf_eq_card_of_forall_mem_zpowers hy, hPc]
  have hyp : y ^ p = 1 := Subtype.ext (hPel.2 y y.2)
  have hdvd := orderOf_dvd_of_pow_eq_one hyp
  rw [hord] at hdvd
  have hle := Nat.le_of_dvd hp.pos hdvd
  have hp2 := hp.two_le
  nlinarith

end ProofKS1623Parab

end CFSG.RankThree.PartTwo.Sec16
