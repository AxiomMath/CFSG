module

public import CFSG.LieType.Universal.SpinCenterMinus
import CFSG.LieType.Universal.Spin.Twisted.Short
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.Timmesfeld.Orders.ClassicalAnisotropic
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesPlane

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open Matrix
open CFSG.LieType.Universal.Spin (binaryForm binaryForm_apply)
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv toLinEquiv_apply)
open CFSG.SeitzReduction.F4Pilot

variable {K : Type} [Field K]

@[expose] def planeO (b c : K) : Subgroup (GL (Fin 2) K) where
  carrier := {X | ∀ w, binaryForm K b c ((X : Matrix (Fin 2) (Fin 2) K) *ᵥ w) =
    binaryForm K b c w}
  mul_mem' {X Y} hX hY w := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hX, hY]
  one_mem' w := by simp
  inv_mem' {X} hX w := by
    rw [← hX (((X⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w), Matrix.mulVec_mulVec,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mem_planeO {b c : K} {X : GL (Fin 2) K} :
    X ∈ planeO b c ↔
      ∀ w, binaryForm K b c ((X : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = binaryForm K b c w :=
  Iff.rfl

theorem card_planeO [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(planeO b c) = 2 * (Nat.card K + 1) := by
  classical
  have hmap : (planeO b c).map (toLinEquiv (Fin 2) K).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup (binaryForm K b c) := by
    ext f
    constructor
    · intro hf
      rw [Subgroup.mem_map] at hf
      obtain ⟨X, hX, rfl⟩ := hf
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro w
      rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply]
      simpa only [binaryForm_apply] using hX w
    · intro hf
      refine ⟨(toLinEquiv (Fin 2) K).symm f, ?_, (toLinEquiv (Fin 2) K).apply_symm_apply f⟩
      change ∀ w, binaryForm K b c (((toLinEquiv (Fin 2) K).symm f : GL (Fin 2) K) *ᵥ w) =
        binaryForm K b c w
      intro w
      have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hf w
      have h1 : (((toLinEquiv (Fin 2) K).symm f : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w =
          f w := by
        rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
      rw [h1]
      simpa only [binaryForm_apply] using h
  have hcard0 : Nat.card ↥((planeO b c).map (toLinEquiv (Fin 2) K).toMonoidHom) =
      Nat.card ↥(planeO b c) :=
    Subgroup.card_map_of_injective (toLinEquiv (Fin 2) K).injective
  rw [hmap] at hcard0
  have hcard : Nat.card ↥(planeO b c) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (binaryForm K b c)) := hcard0.symm
  rw [hcard]
  refine CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_of_anisotropic
    (A := Fin 2 → K) (Q := binaryForm K b c) ?_ ?_
  · rw [Module.finrank_fin_fun]
  · intro x hx
    rw [binaryForm_apply]
    exact CFSG.LieType.Universal.Spin.Twisted.binary_ne_zero hirr hx

private theorem odd_card_add_one [Finite K] [CharP K 2] : Odd (Nat.card K + 1) := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hcard⟩ := FiniteField.card K 2
  have heven : Even (Nat.card K) := by
    rw [Nat.card_eq_fintype_card, hcard, even_iff_two_dvd]
    exact dvd_pow_self 2 m.ne_zero
  exact heven.add_one

theorem pow_card_add_one_eq_one [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {X : GL (Fin 2) K} (hX : X ∈ planeO b c)
    (hodd : Odd (orderOf X)) : X ^ (Nat.card K + 1) = 1 := by
  have hdvd : orderOf X ∣ Nat.card ↥(planeO b c) :=
    Subgroup.orderOf_dvd_natCard (planeO b c) hX
  rw [card_planeO hirr] at hdvd
  have hcop : Nat.Coprime (orderOf X) 2 := Nat.coprime_two_right.mpr hodd
  have hdvd' : orderOf X ∣ (Nat.card K + 1) * 2 := by rwa [mul_comm] at hdvd
  exact orderOf_dvd_iff_pow_eq_one.mp (Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd')

theorem sq_eq_one_of_pow_two_pow_eq_one [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {X : GL (Fin 2) K} (hX : X ∈ planeO b c) {k : ℕ}
    (hk : X ^ 2 ^ k = 1) : X ^ 2 = 1 := by
  have hdiv : orderOf X ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hdvd : orderOf X ∣ Nat.card ↥(planeO b c) :=
    Subgroup.orderOf_dvd_natCard (planeO b c) hX
  rw [card_planeO hirr] at hdvd
  have h2j : 2 ^ j ∣ 2 * (Nat.card K + 1) := hj ▸ hdvd
  have hoddq : Odd (Nat.card K + 1) := odd_card_add_one
  have hle : j ≤ 1 := by
    by_contra h
    have hj2 : 2 ≤ j := by omega
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hj2
    have h4 : 4 ∣ 2 ^ j := by
      refine ⟨2 ^ l, ?_⟩
      rw [hl, pow_add]
      ring
    have h4' : 4 ∣ 2 * (Nat.card K + 1) := h4.trans h2j
    obtain ⟨t, ht⟩ := h4'
    have h2 : 2 ∣ Nat.card K + 1 := ⟨t, by omega⟩
    exact hoddq.not_two_dvd_nat h2
  exact orderOf_dvd_iff_pow_eq_one.mp (hj.symm ▸ pow_dvd_pow 2 hle)

private theorem anisoNorm_eq_binaryForm (b c : K) (w : Fin 2 → K) :
    anisoNorm b c w = binaryForm K b c w := by
  rw [anisoNorm, binaryForm_apply]

private theorem mem_planeO_iff_anisoNorm {b c : K} {X : GL (Fin 2) K} :
    X ∈ planeO b c ↔
      ∀ w, anisoNorm b c ((X : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = anisoNorm b c w := by
  rw [mem_planeO]
  constructor
  · intro h w
    rw [anisoNorm_eq_binaryForm, anisoNorm_eq_binaryForm]
    exact h w
  · intro h w
    rw [← anisoNorm_eq_binaryForm, ← anisoNorm_eq_binaryForm]
    exact h w

private theorem eq_one_of_isAnisoRot_mul_self [CharP K 2] {b c : K} (hb : b ≠ 0)
    {T : Matrix (Fin 2) (Fin 2) K} (hrot : IsAnisoRot b c T) (hT2 : T * T = 1) : T = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨h01, h11⟩ := hrot
  have h10 : T 1 0 = 0 := by
    have h := congrArg (fun M => M 1 0) hT2
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at h
    norm_num at h
    rw [h11] at h
    have hs : b * (T 1 0) ^ 2 = 0 := by
      linear_combination h - (T 1 0 * T 0 0) * h2
    exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hs).resolve_left hb)
  have h01' : T 0 1 = 0 := by simp [h01, h10]
  have h11' : T 1 1 = T 0 0 := by simp [h11, h10]
  have h00 : T 0 0 * T 0 0 = 1 := by
    have h := congrArg (fun M => M 0 0) hT2
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at h
    norm_num at h
    simpa [h01, h10] using h
  have hp : T 0 0 = 1 := CharTwo.sq_injective (by simpa [pow_two] using h00)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01', h11', hp]

private theorem mul_self_eq_one_of_isAnisoRef [CharP K 2] {b c : K}
    {R : Matrix (Fin 2) (Fin 2) K} (hR : IsAnisoRef b c R)
    (hiso : ∀ w, binaryForm K b c (R *ᵥ w) = binaryForm K b c w) : R * R = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨h01, h11⟩ := hR
  have hN : R 0 0 ^ 2 + b * R 0 0 * R 1 0 + c * R 1 0 ^ 2 = 1 := by
    have h := hiso ![1, 0]
    have h1 : binaryForm K b c ![1, 0] = 1 := by
      rw [binaryForm_apply]
      norm_num
    rw [h1, binaryForm_apply] at h
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have h00 : (R * R) 0 0 = 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, h01]
    linear_combination hN
  have h01e : (R * R) 0 1 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, h01, h11]
    linear_combination (R 0 0 * (c * R 1 0 + b * R 0 0)) * h2
  have h10e : (R * R) 1 0 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, h11]
    linear_combination (R 1 0 * R 0 0) * h2
  have h11e : (R * R) 1 1 = 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, h01, h11]
    linear_combination hN
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using h00
  · simpa using h01e
  · simpa using h10e
  · simpa using h11e

private theorem isAnisoRot_sq_of_class [CharP K 2] {b c : K} {Y : GL (Fin 2) K}
    (hY : IsAnisoRot b c (Y : Matrix (Fin 2) (Fin 2) K) ∨
      IsAnisoRef b c (Y : Matrix (Fin 2) (Fin 2) K)) :
    IsAnisoRot b c (((Y * Y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
  rcases hY with h | h
  · simpa [Units.val_mul] using IsAnisoRot.mul h h
  · have ht : AnisoType b c (1 : ZMod 2) (Y : Matrix (Fin 2) (Fin 2) K) := Or.inr ⟨rfl, h⟩
    have hmul := AnisoType.mul ht ht
    have h0 : (1 + 1 : ZMod 2) = 0 := by decide
    rw [h0] at hmul
    rcases hmul with ⟨-, hrot⟩ | ⟨hbad, -⟩
    · simpa [Units.val_mul] using hrot
    · exact absurd hbad (by decide)

theorem conj_eq_inv [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {T X : GL (Fin 2) K} (hT : T ∈ planeO b c) (hT2 : T ^ 2 = 1) (hT1 : T ≠ 1)
    (hX : X ∈ planeO b c) (hodd : Odd (orderOf X)) : T * X * T⁻¹ = X⁻¹ := by
  classical
  have hb : b ≠ 0 := ne_zero_of_irr hirr
  have hTclass := isAnisoRot_or_isAnisoRef hirr ((mem_planeO_iff_anisoNorm).mp hT)
  have hTmat2 : (T : Matrix (Fin 2) (Fin 2) K) * (T : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have h := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) hT2
    simpa [pow_two, Units.val_mul] using h
  have hTref : IsAnisoRef b c (T : Matrix (Fin 2) (Fin 2) K) := by
    rcases hTclass with hrot | href
    · exfalso
      exact hT1 (Units.ext (eq_one_of_isAnisoRot_mul_self hb hrot hTmat2))
    · exact href
  obtain ⟨m, hm⟩ := hodd
  have hYeq : (X ^ (m + 1)) * (X ^ (m + 1)) = X := by
    rw [(pow_add X (m + 1) (m + 1)).symm]
    have hexp : m + 1 + (m + 1) = orderOf X + 1 := by omega
    rw [hexp, pow_succ, pow_orderOf_eq_one, one_mul]
  have hYmem : X ^ (m + 1) ∈ planeO b c := (planeO b c).pow_mem hX (m + 1)
  have hYclass := isAnisoRot_or_isAnisoRef hirr ((mem_planeO_iff_anisoNorm).mp hYmem)
  have hXrot : IsAnisoRot b c (X : Matrix (Fin 2) (Fin 2) K) := by
    have hsq := isAnisoRot_sq_of_class hYclass
    rw [hYeq] at hsq
    exact hsq
  have hTXref : IsAnisoRef b c (((T * X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    have hTtype : AnisoType b c 1 (T : Matrix (Fin 2) (Fin 2) K) := Or.inr ⟨rfl, hTref⟩
    have hXtype : AnisoType b c 0 (X : Matrix (Fin 2) (Fin 2) K) := Or.inl ⟨rfl, hXrot⟩
    have hmul := AnisoType.mul hTtype hXtype
    have hsum : (1 + 0 : ZMod 2) = 1 := by decide
    rw [hsum] at hmul
    rcases hmul with ⟨hbad, -⟩ | ⟨-, href⟩
    · exact absurd hbad (by decide)
    · simpa [Units.val_mul] using href
  have hTXsq : ((T * X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((T * X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 :=
    mul_self_eq_one_of_isAnisoRef hTXref ((planeO b c).mul_mem hT hX)
  have hTXsq' : (T * X) * (T * X) = 1 := by
    apply Units.ext
    simpa [Units.val_mul] using hTXsq
  have hTXinv : T * X * T = X⁻¹ := by
    have h := congrArg (fun y : GL (Fin 2) K => y * X⁻¹) hTXsq'
    simpa [mul_assoc] using h
  have hTsq : T * T = 1 := by simpa [pow_two] using hT2
  have hTinv : T⁻¹ = T := inv_eq_of_mul_eq_one_right hTsq
  rw [hTinv]
  exact hTXinv

theorem exists_mulVec_eq_self {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] [CharP K 2]
    {X : GL n K} {k : ℕ} (hk : X ^ 2 ^ k = 1) :
    ∃ a : n → K, a ≠ 0 ∧ (X : Matrix n n K) *ᵥ a = a := by
  classical
  obtain ⟨i⟩ := ‹Nonempty n›
  have hsingle : (Pi.single i (1 : K) : n → K) ≠ 0 := by
    intro h
    have := congrFun h i
    simp at this
  have hXk : (X : Matrix n n K) ^ 2 ^ k = 1 := by
    have h := congrArg (fun u : GL n K => (u : Matrix n n K)) hk
    simpa using h
  by_cases hk0 : k = 0
  · subst hk0
    have hX1 : X = 1 := by simpa using hk
    refine ⟨Pi.single i 1, hsingle, ?_⟩
    rw [hX1]
    exact Matrix.one_mulVec _
  · have hVpow : ((X : Matrix n n K) - 1) ^ 2 ^ k = 0 := by
      have hcomm : Commute (X : Matrix n n K) (1 : Matrix n n K) := Commute.one_right _
      rw [sub_pow_expChar_pow_of_commute (p := 2) (n := k) hcomm, hXk, one_pow, sub_self]
    have hdet : ((X : Matrix n n K) - 1).det = 0 := by
      have h := congrArg Matrix.det hVpow
      rw [Matrix.det_pow, Matrix.det_zero] at h
      exact eq_zero_of_pow_eq_zero h
    obtain ⟨a, ha0, haV⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    refine ⟨a, ha0, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at haV
    exact haV

theorem eq_smul_of_mulVec_eq_self {X : Matrix (Fin 2) (Fin 2) K} (hX : X ≠ 1) {a z : Fin 2 → K}
    (ha0 : a ≠ 0) (ha : X *ᵥ a = a) (hz : X *ᵥ z = z) : ∃ s : K, z = s • a := by
  classical
  set Y : Matrix (Fin 2) (Fin 2) K := X - 1 with hY
  have hYa : Y *ᵥ a = 0 := by
    rw [hY, Matrix.sub_mulVec, ha, Matrix.one_mulVec, sub_self]
  have hYz : Y *ᵥ z = 0 := by
    rw [hY, Matrix.sub_mulVec, hz, Matrix.one_mulVec, sub_self]
  by_cases hdet : a 0 * z 1 - a 1 * z 0 = 0
  · have ha01 : a 0 ≠ 0 ∨ a 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact ha0 (funext fun i => by fin_cases i <;> [exact h.1; exact h.2])
    rcases ha01 with ha0' | ha1'
    · refine ⟨z 0 / a 0, ?_⟩
      ext i
      fin_cases i
      · show z 0 = (z 0 / a 0) * a 0
        rw [div_mul_eq_mul_div, eq_div_iff ha0']
      · have h : a 0 * z 1 = a 1 * z 0 := sub_eq_zero.mp hdet
        show z 1 = (z 0 / a 0) * a 1
        rw [div_mul_eq_mul_div, eq_div_iff ha0']
        linear_combination h
    · refine ⟨z 1 / a 1, ?_⟩
      ext i
      fin_cases i
      · have h : a 0 * z 1 = a 1 * z 0 := sub_eq_zero.mp hdet
        show z 0 = (z 1 / a 1) * a 0
        rw [div_mul_eq_mul_div, eq_div_iff ha1']
        linear_combination -h
      · show z 1 = (z 1 / a 1) * a 1
        rw [div_mul_eq_mul_div, eq_div_iff ha1']
  · exfalso
    have hYzero : Y = 0 := by
      ext i j
      have h1 : Y i 0 * a 0 + Y i 1 * a 1 = 0 := by
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hYa i
      have h2 : Y i 0 * z 0 + Y i 1 * z 1 = 0 := by
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hYz i
      have hY0 : Y i 0 = 0 := by
        have h : Y i 0 * (a 0 * z 1 - a 1 * z 0) = 0 := by
          linear_combination z 1 * h1 - a 1 * h2
        exact (mul_eq_zero.mp h).resolve_right hdet
      have hY1 : Y i 1 = 0 := by
        have h : Y i 1 * (a 1 * z 0 - a 0 * z 1) = 0 := by
          linear_combination z 0 * h1 - a 0 * h2
        have hdet' : a 1 * z 0 - a 0 * z 1 ≠ 0 := by
          intro hh
          exact hdet (by linear_combination -hh)
        exact (mul_eq_zero.mp h).resolve_right hdet'
      fin_cases j <;> simp [hY0, hY1]
    rw [hY] at hYzero
    exact hX (sub_eq_zero.mp hYzero)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
