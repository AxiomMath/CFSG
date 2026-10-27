module

public import CFSG.RankThree.PartOne.KF.OrthChar2Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.RankThree.PartOne.KFU.OrthChar2

open Matrix

variable {K : Type} [Field K] (b c : K)

@[expose] def Nf (w : Fin 2 → K) : K := w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2

@[expose] def Bf (x y : Fin 2 → K) : K := b * (x 0 * y 1 + x 1 * y 0)

theorem Nf_smul (r : K) (w : Fin 2 → K) : Nf b c (r • w) = r ^ 2 * Nf b c w := by
  simp only [Nf, Pi.smul_apply, smul_eq_mul]
  ring

theorem Bf_add_left (x x' y : Fin 2 → K) : Bf b (x + x') y = Bf b x y + Bf b x' y := by
  simp only [Bf, Pi.add_apply]
  ring

theorem Bf_add_right (x y y' : Fin 2 → K) : Bf b x (y + y') = Bf b x y + Bf b x y' := by
  simp only [Bf, Pi.add_apply]
  ring

theorem Bf_smul_left (r : K) (x y : Fin 2 → K) : Bf b (r • x) y = r * Bf b x y := by
  simp only [Bf, Pi.smul_apply, smul_eq_mul]
  ring

theorem Bf_smul_right (r : K) (x y : Fin 2 → K) : Bf b x (r • y) = r * Bf b x y := by
  simp only [Bf, Pi.smul_apply, smul_eq_mul]
  ring

theorem Nf_add (h2 : (2 : K) = 0) (x y : Fin 2 → K) :
    Nf b c (x + y) = Nf b c x + Nf b c y + Bf b x y := by
  simp only [Nf, Bf, Pi.add_apply]
  linear_combination (x 0 * y 0 + c * x 1 * y 1) * h2

@[expose] def planeSpace (h2 : (2 : K) = 0) : QSpace K (Fin 2 → K) where
  Q := Nf b c
  B := LinearMap.mk₂ K (Bf b) (Bf_add_left b)
    (fun r x y => by simpa only [smul_eq_mul] using Bf_smul_left b r x y) (Bf_add_right b)
    (fun r x y => by simpa only [smul_eq_mul] using Bf_smul_right b r x y)
  Q_smul := Nf_smul b c
  Q_add := Nf_add b c h2

theorem Nf_ne_zero (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {w : Fin 2 → K} (hw : w ≠ 0) :
    Nf b c w ≠ 0 := by
  intro h
  by_cases h1 : w 1 = 0
  · have h0 : w 0 ≠ 0 := by
      intro h0
      apply hw
      funext i
      fin_cases i <;> simp [h0, h1]
    apply h0
    have : w 0 ^ 2 = 0 := by simpa [Nf, h1] using h
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  · apply hirr (w 0 / w 1)
    have : Nf b c w = (w 1) ^ 2 * ((w 0 / w 1) ^ 2 + b * (w 0 / w 1) + c) := by
      simp only [Nf]
      field_simp
    rw [this] at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero 2 h1)

section Companion

variable (h2 : (2 : K) = 0)

@[expose] def Cm : Matrix (Fin 2) (Fin 2) K := !![0, c; 1, b]

include h2 in
theorem Nf_eq_det (w : Fin 2 → K) :
    Nf b c w = (!![w 0, (Cm b c *ᵥ w) 0; w 1, (Cm b c *ᵥ w) 1]).det := by
  simp only [Nf, Cm, Matrix.det_fin_two_of, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination (c * w 1 * w 1) * h2

include h2 in
theorem Nf_mulVec (g : Matrix (Fin 2) (Fin 2) K) (hg : g * Cm b c = Cm b c * g)
    (w : Fin 2 → K) : Nf b c (g *ᵥ w) = g.det * Nf b c w := by
  rw [Nf_eq_det b c h2, Nf_eq_det b c h2]
  have e : Cm b c *ᵥ (g *ᵥ w) = g *ᵥ (Cm b c *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]
  rw [e, ← Matrix.det_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]

@[expose] def tauM : Matrix (Fin 2) (Fin 2) K := !![1, b; 0, 1]

include h2 in
theorem Nf_tau (w : Fin 2 → K) : Nf b c (tauM b *ᵥ w) = Nf b c w := by
  simp only [Nf, tauM, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  linear_combination (b * w 0 * w 1 + b ^ 2 * w 1 ^ 2) * h2

include h2 in
theorem tauM_mul_self : tauM b * tauM b = 1 := by
  have h : b + b = 0 := by linear_combination b * h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tauM, Matrix.mul_apply, Fin.sum_univ_two, h]

theorem tauM_det : (tauM b).det = 1 := by
  simp [tauM, Matrix.det_fin_two_of]

include h2 in
theorem tau_conj_mul (g : Matrix (Fin 2) (Fin 2) K) (hg : g * Cm b c = Cm b c * g)
    (hdet : g.det = 1) : tauM b * g * tauM b * g = 1 := by
  obtain ⟨a, β, γ, δ, rfl⟩ : ∃ a β γ δ : K, g = !![a, β; γ, δ] :=
    ⟨g 0 0, g 0 1, g 1 0, g 1 1, Matrix.eta_fin_two g⟩
  have e01 : β = c * γ := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hg
    simpa [Cm, Matrix.mul_fin_two] using this
  have e11 : δ = a + b * γ := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hg
    simpa [Cm, Matrix.mul_fin_two] using this
  have hd : a * δ - β * γ = 1 := by simpa [Matrix.det_fin_two_of] using hdet
  subst e01 e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM]
  · linear_combination hd + (c * γ ^ 2 + a * b * γ + b ^ 2 * γ ^ 2) * h2
  · linear_combination (c * γ * (a + b * γ) + 2 * a * b ^ 2 * γ + a ^ 2 * b + b ^ 3 * γ ^ 2) * h2
  · linear_combination (a * γ + γ ^ 2 * b) * h2
  · linear_combination hd + (c * γ ^ 2 + γ * b * a + γ ^ 2 * b ^ 2) * h2

end Companion

section Centralizer

@[expose] def Rm (a t : K) : Matrix (Fin 2) (Fin 2) K := !![a, c * t; t, a + b * t]

theorem Rm_comm (a t : K) : Rm b c a t * Cm b c = Cm b c * Rm b c a t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rm, Cm] <;> ring

theorem det_Rm (h2 : (2 : K) = 0) (a t : K) : (Rm b c a t).det = Nf b c ![a, t] := by
  simp only [Rm, Nf, Matrix.det_fin_two_of, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (-(c * t * t)) * h2

theorem c_ne_zero (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : c ≠ 0 := by
  intro h
  exact hirr 0 (by simp [h])

theorem entries_of_comm {g : Matrix (Fin 2) (Fin 2) K} (hg : g * Cm b c = Cm b c * g) :
    g 0 1 = c * g 1 0 ∧ g 1 1 = g 0 0 + b * g 1 0 := by
  constructor
  · have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hg
    simpa [Cm, Matrix.mul_apply, Fin.sum_univ_two] using this
  · have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hg
    simpa [Cm, Matrix.mul_apply, Fin.sum_univ_two] using this

theorem eq_Rm_of_comm {g : Matrix (Fin 2) (Fin 2) K} (hg : g * Cm b c = Cm b c * g) :
    g = Rm b c (g 0 0) (g 1 0) := by
  obtain ⟨e01, e11⟩ := entries_of_comm b c hg
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rm, e01, e11]

@[expose] noncomputable def Cu (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : GL (Fin 2) K :=
  Matrix.nonsingInvUnit (Cm b c) (by
    simp only [Cm, Matrix.det_fin_two_of]
    exact isUnit_iff_ne_zero.2 (by simpa using c_ne_zero b c hirr))

theorem coe_Cu (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ((Cu b c hirr : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Cm b c := rfl

theorem mem_centralizer_Cu (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (g : GL (Fin 2) K) :
    g ∈ Subgroup.centralizer ({Cu b c hirr} : Set (GL (Fin 2) K)) ↔
      (g : Matrix (Fin 2) (Fin 2) K) * Cm b c = Cm b c * (g : Matrix (Fin 2) (Fin 2) K) := by
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) h
    simpa [Units.val_mul, coe_Cu] using this.symm
  · intro h
    apply Units.ext
    simpa [Units.val_mul, coe_Cu] using h.symm

end Centralizer

section Count

variable [Finite K]

omit [Finite K] in
theorem Rm_det_ne (h2 : (2 : K) = 0) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (w : K × K)
    (hw : w ≠ 0) : (Rm b c w.1 w.2).det ≠ 0 := by
  rw [det_Rm b c h2]
  refine Nf_ne_zero b c hirr fun h => hw ?_
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
  exact Prod.ext h0 h1

theorem card_nonzero_pairs : Nat.card {w : K × K // w ≠ 0} = Nat.card K ^ 2 - 1 := by
  classical
  have := Fintype.ofFinite K
  have h1 : Fintype.card {w : K × K // w ≠ 0} = Fintype.card (K × K) - 1 := by
    simp
  rw [Nat.card_eq_fintype_card, h1, Fintype.card_prod, Nat.card_eq_fintype_card, sq]

theorem card_centralizer_Cu (h2 : (2 : K) = 0) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (Subgroup.centralizer ({Cu b c hirr} : Set (GL (Fin 2) K))) =
      Nat.card K ^ 2 - 1 := by
  classical
  let ψ : {w : K × K // w ≠ 0} →
      Subgroup.centralizer ({Cu b c hirr} : Set (GL (Fin 2) K)) := fun w =>
    ⟨Matrix.nonsingInvUnit (Rm b c w.1.1 w.1.2)
        (isUnit_iff_ne_zero.2 (Rm_det_ne b c h2 hirr w.1 w.2)),
      (mem_centralizer_Cu b c hirr _).2 (Rm_comm b c _ _)⟩
  have hψ : ∀ w, (((ψ w : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) = Rm b c w.1.1 w.1.2 :=
    fun w => rfl
  have hinj : Function.Injective ψ := by
    intro w w' h
    have hm : Rm b c w.1.1 w.1.2 = Rm b c w'.1.1 w'.1.2 := by
      rw [← hψ, ← hψ, h]
    have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hm
    have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hm
    simp only [Rm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h0 h1
    exact Subtype.ext (Prod.ext h0 h1)
  have hsurj : Function.Surjective ψ := by
    intro g
    have hg := (mem_centralizer_Cu b c hirr _).1 g.2
    set M : Matrix (Fin 2) (Fin 2) K := ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hM
    have hMR : M = Rm b c (M 0 0) (M 1 0) := eq_Rm_of_comm b c hg
    have hne : ((M 0 0, M 1 0) : K × K) ≠ 0 := by
      intro h0
      have ha : M 0 0 = 0 := congrArg Prod.fst h0
      have ht : M 1 0 = 0 := congrArg Prod.snd h0
      have hdet : M.det = 0 := by
        rw [hMR, ha, ht]
        simp [Rm, Matrix.det_fin_two_of]
      have hunit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 (g : GL (Fin 2) K).isUnit
      rw [hdet] at hunit
      exact not_isUnit_zero hunit
    refine ⟨⟨(M 0 0, M 1 0), hne⟩, Subtype.ext (Units.ext ?_)⟩
    rw [hψ]
    exact hMR.symm
  rw [← Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩), card_nonzero_pairs]

theorem exists_order_centralizer (h2 : (2 : K) = 0) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    ∃ ζ : GL (Fin 2) K, orderOf ζ = p ∧
      (ζ : Matrix (Fin 2) (Fin 2) K) * Cm b c = Cm b c * (ζ : Matrix (Fin 2) (Fin 2) K) ∧
      (ζ : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hdvd : p ∣ Nat.card (Subgroup.centralizer ({Cu b c hirr} : Set (GL (Fin 2) K))) := by
    rw [card_centralizer_Cu b c h2 hirr]
    have e : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
      obtain ⟨k, hk⟩ : ∃ k, Nat.card K = k + 1 := ⟨Nat.card K - 1, by omega⟩
      rw [hk]
      have : (k + 1) ^ 2 = k * (k + 1 + 1) + 1 := by ring
      simp only [Nat.add_sub_cancel]
      omega
    rw [e]
    exact Dvd.dvd.mul_left hpq _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hxo : orderOf (x : GL (Fin 2) K) = p := by rw [Subgroup.orderOf_coe]; exact hx
  refine ⟨x, hxo, (mem_centralizer_Cu b c hirr _).1 x.2, ?_⟩
  set d : Kˣ := Matrix.GeneralLinearGroup.det (x : GL (Fin 2) K) with hd
  have hdp : d ^ p = 1 := by
    rw [hd, ← map_pow, ← hxo, pow_orderOf_eq_one, map_one]
  have h1 : orderOf d ∣ p := orderOf_dvd_of_pow_eq_one hdp
  have h2' : orderOf d ∣ Nat.card K - 1 := by
    rw [← Nat.card_units]
    exact orderOf_dvd_natCard d
  have hd1 : d = 1 := by
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exfalso
      rw [h] at h2'
      have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq h2'
      have : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
      rw [this] at h3
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)
  have := Matrix.GeneralLinearGroup.val_det_apply (x : GL (Fin 2) K)
  rw [← this]
  change ((d : Kˣ) : K) = 1
  rw [hd1, Units.val_one]

end Count

end CFSG.RankThree.PartOne.KFU.OrthChar2
