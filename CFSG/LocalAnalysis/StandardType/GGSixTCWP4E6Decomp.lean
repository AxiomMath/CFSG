module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Root
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Frame

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem pair_decomp_aux_four {R : Type*} [CommRing R] (u4 u5 s t : R)
    (hs : 3 * s = 2 * u4 + u5) (ht : 3 * t = u4 + 2 * u5) :
    3 * (u4 - (s * 2 + t * -1)) = 0 := by
  linear_combination (-2 : R) * hs + ht

theorem pair_decomp_aux_five {R : Type*} [CommRing R] (u4 u5 s t : R)
    (hs : 3 * s = 2 * u4 + u5) (ht : 3 * t = u4 + 2 * u5) :
    3 * (u5 - (s * -1 + t * 2)) = 0 := by
  linear_combination hs - 2 * ht

theorem pair_decomp_of_frame {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (m : Fin 6 → (Fin Tag.E6.rank → ℤ))
    (hnorm : ∀ i, iform (m i) (m i) = 2)
    (h01 : iform (m 0) (m 1) = -1) (h23 : iform (m 2) (m 3) = -1) (h45 : iform (m 4) (m 5) = -1)
    (horth : ∀ i j : Fin 6, i.val / 2 ≠ j.val / 2 → iform (m i) (m j) = 0)
    (v : Fin Tag.E6.rank → ℤ)
    (h0 : (p : ℤ) ∣ ∑ j, m 0 j * v j) (h1 : (p : ℤ) ∣ ∑ j, m 1 j * v j)
    (h2 : (p : ℤ) ∣ ∑ j, m 2 j * v j) (h3 : (p : ℤ) ∣ ∑ j, m 3 j * v j) :
    ∃ s t : ℤ, ∀ γ : Fin Tag.E6.rank → ℤ,
      (p : ℤ) ∣ (∑ j, γ j * v j) - (s * iform γ (m 4) + t * iform γ (m 5)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h3ne : (3 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((3 : ℤ) : ZMod p) = 0 := by exact_mod_cast h
    have hd : (p : ℤ) ∣ 3 := (ZMod.intCast_zmod_eq_zero_iff_dvd 3 p).mp h'
    have hle : (p : ℤ) ≤ 3 := Int.le_of_dvd (by norm_num) hd
    omega
  have h27 : (27 : ZMod p) ≠ 0 := by
    have e : (27 : ZMod p) = 3 ^ 3 := by norm_num
    rw [e]
    exact pow_ne_zero _ h3ne
  have hsymC : ∀ a b : Fin 6, Tag.cartanE 6 a b = Tag.cartanE 6 b a := by
    intro a b
    fin_cases a <;> fin_cases b <;> first | rfl | decide
  have hsymE : ∀ x y : Fin Tag.E6.rank → ℤ, iform x y = iform y x := by
    intro x y
    simp only [iform, symmetrizedCartan_E6_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsymC b a]
    ring
  have h10 : iform (m 1) (m 0) = -1 := by rw [hsymE]; exact h01
  have h32 : iform (m 3) (m 2) = -1 := by rw [hsymE]; exact h23
  have h54 : iform (m 5) (m 4) = -1 := by rw [hsymE]; exact h45
  obtain ⟨G6, hG6⟩ : ∃ G : Matrix (Fin 6) (Fin 6) ℤ,
      G = !![2, -1, 0, 0, 0, 0; -1, 2, 0, 0, 0, 0; 0, 0, 2, -1, 0, 0;
        0, 0, -1, 2, 0, 0; 0, 0, 0, 0, 2, -1; 0, 0, 0, 0, -1, 2] := ⟨_, rfl⟩
  have hG6det : G6.det = 27 := by
    rw [hG6, ← laplaceDet_eq_det]
    decide +kernel
  have hGint : ∀ i k : Fin 6, iform (m i) (m k) = G6 i k := by
    intro i k
    fin_cases i <;> fin_cases k <;>
      first
        | (simp [hG6, hnorm, h01, h10, h23, h32, h45, h54]; done)
        | exact (horth _ _ (by decide)).trans (by simp [hG6])
  obtain ⟨Mp, hMp⟩ : ∃ M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) (ZMod p),
      ∀ i j, M i j = ((m i j : ℤ) : ZMod p) :=
    ⟨Matrix.of fun i j => ((m i j : ℤ) : ZMod p), fun _ _ => rfl⟩
  obtain ⟨Cp, hCp⟩ : ∃ C : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) (ZMod p),
      ∀ i j, C i j = ((Tag.cartanE 6 i j : ℤ) : ZMod p) :=
    ⟨Matrix.of fun i j => ((Tag.cartanE 6 i j : ℤ) : ZMod p), fun _ _ => rfl⟩
  obtain ⟨vp, hvp⟩ : ∃ x : Fin Tag.E6.rank → ZMod p, ∀ j, x j = ((v j : ℤ) : ZMod p) :=
    ⟨fun j => ((v j : ℤ) : ZMod p), fun _ => rfl⟩
  obtain ⟨mp, hmp⟩ : ∃ f : Fin 6 → Fin Tag.E6.rank → ZMod p,
      ∀ k l, f k l = ((m k l : ℤ) : ZMod p) :=
    ⟨fun k l => ((m k l : ℤ) : ZMod p), fun _ _ => rfl⟩
  have hMp6 : ∀ (i : Fin 6) (j : Fin Tag.E6.rank), Mp i j = ((m i j : ℤ) : ZMod p) :=
    fun i j => hMp i j
  have hform : ∀ x y : Fin Tag.E6.rank → ℤ,
      (∑ j, ((x j : ℤ) : ZMod p) * ∑ l, ((Tag.cartanE 6 j l : ℤ) : ZMod p) * ((y l : ℤ) : ZMod p)) =
        ((iform x y : ℤ) : ZMod p) := by
    intro x y
    simp only [iform, symmetrizedCartan_E6_apply, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hMC : Mp * (Cp * Mp.transpose) = (Int.castRingHom (ZMod p)).mapMatrix G6 := by
    ext i k
    have key0 := hform (m i) (m k)
    rw [hGint i k] at key0
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply,
      Matrix.transpose_apply, hMp, hCp]
    exact key0
  have hMgram : ∀ (x : Fin Tag.E6.rank → ℤ) (k : Fin 6),
      (∑ j, ((x j : ℤ) : ZMod p) * Matrix.mulVec Cp (mp k) j) = ((iform x (m k) : ℤ) : ZMod p) := by
    intro x k
    rw [← hform x (m k)]
    simp only [Matrix.mulVec, dotProduct, hCp, hmp]
    try rfl
  have hMv : ∀ i k : Fin 6, Matrix.mulVec Mp (Matrix.mulVec Cp (mp k)) i =
      ((iform (m i) (m k) : ℤ) : ZMod p) := by
    intro i k
    rw [← hMgram (m i) k]
    simp only [Matrix.mulVec, dotProduct, hMp6]
    try rfl
  have hu : ∀ i : Fin 6, Matrix.mulVec Mp vp i = ((∑ j, m i j * v j : ℤ) : ZMod p) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, hMp6, hvp, Int.cast_sum, Int.cast_mul]
    try rfl
  have hCdet : Cp.det = 3 := by
    have hC : Cp = (Int.castRingHom (ZMod p)).mapMatrix Tag.E6.cartan := by
      ext i j
      rw [hCp]
      rfl
    have h := RingHom.map_det (Int.castRingHom (ZMod p)) Tag.E6.cartan
    rw [det_cartan_E6] at h
    rw [hC, ← h]
    simp
  have hdetMC : (Mp * (Cp * Mp.transpose)).det = 27 := by
    have hd := RingHom.map_det (Int.castRingHom (ZMod p)) G6
    rw [hG6det] at hd
    rw [hMC]
    exact hd.symm.trans (by simp)
  have hdetMC' : Mp.det * (3 * Mp.det) = 27 := by
    rw [← hdetMC, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hCdet]
  have hMp_ne : Mp.det ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hdetMC'
    exact h27 hdetMC'.symm
  obtain ⟨s, hs⟩ : ∃ s : ZMod p,
      3 * s = 2 * Matrix.mulVec Mp vp (4 : Fin 6) + Matrix.mulVec Mp vp (5 : Fin 6) :=
    ⟨(2 * Matrix.mulVec Mp vp (4 : Fin 6) + Matrix.mulVec Mp vp (5 : Fin 6)) * 3⁻¹, by
      linear_combination (2 * Matrix.mulVec Mp vp (4 : Fin 6) + Matrix.mulVec Mp vp (5 : Fin 6)) *
        mul_inv_cancel₀ h3ne⟩
  obtain ⟨t, ht⟩ : ∃ t : ZMod p,
      3 * t = Matrix.mulVec Mp vp (4 : Fin 6) + 2 * Matrix.mulVec Mp vp (5 : Fin 6) :=
    ⟨(Matrix.mulVec Mp vp (4 : Fin 6) + 2 * Matrix.mulVec Mp vp (5 : Fin 6)) * 3⁻¹, by
      linear_combination (Matrix.mulVec Mp vp (4 : Fin 6) + 2 * Matrix.mulVec Mp vp (5 : Fin 6)) *
        mul_inv_cancel₀ h3ne⟩
  have z04_0 : iform (m 0) (m 4) = 0 := horth 0 4 (by decide)
  have z05_0 : iform (m 0) (m 5) = 0 := horth 0 5 (by decide)
  have z04_1 : iform (m 1) (m 4) = 0 := horth 1 4 (by decide)
  have z05_1 : iform (m 1) (m 5) = 0 := horth 1 5 (by decide)
  have z04_2 : iform (m 2) (m 4) = 0 := horth 2 4 (by decide)
  have z05_2 : iform (m 2) (m 5) = 0 := horth 2 5 (by decide)
  have z04_3 : iform (m 3) (m 4) = 0 := horth 3 4 (by decide)
  have z05_3 : iform (m 3) (m 5) = 0 := horth 3 5 (by decide)
  have hu0 : Matrix.mulVec Mp vp (0 : Fin 6) = 0 := by
    rw [hu 0]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h0
  have hu1 : Matrix.mulVec Mp vp (1 : Fin 6) = 0 := by
    rw [hu 1]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h1
  have hu2 : Matrix.mulVec Mp vp (2 : Fin 6) = 0 := by
    rw [hu 2]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h2
  have hu3 : Matrix.mulVec Mp vp (3 : Fin 6) = 0 := by
    rw [hu 3]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h3
  have key : ∀ i : Fin 6, Matrix.mulVec Mp vp i -
      (s * ((iform (m i) (m 4) : ℤ) : ZMod p) + t * ((iform (m i) (m 5) : ℤ) : ZMod p)) = 0 := by
    intro i
    fin_cases i
    · show Matrix.mulVec Mp vp (0 : Fin 6) -
        (s * ((iform (m 0) (m 4) : ℤ) : ZMod p) + t * ((iform (m 0) (m 5) : ℤ) : ZMod p)) = 0
      rw [hu0, z04_0, z05_0]
      simp
    · show Matrix.mulVec Mp vp (1 : Fin 6) -
        (s * ((iform (m 1) (m 4) : ℤ) : ZMod p) + t * ((iform (m 1) (m 5) : ℤ) : ZMod p)) = 0
      rw [hu1, z04_1, z05_1]
      simp
    · show Matrix.mulVec Mp vp (2 : Fin 6) -
        (s * ((iform (m 2) (m 4) : ℤ) : ZMod p) + t * ((iform (m 2) (m 5) : ℤ) : ZMod p)) = 0
      rw [hu2, z04_2, z05_2]
      simp
    · show Matrix.mulVec Mp vp (3 : Fin 6) -
        (s * ((iform (m 3) (m 4) : ℤ) : ZMod p) + t * ((iform (m 3) (m 5) : ℤ) : ZMod p)) = 0
      rw [hu3, z04_3, z05_3]
      simp
    · show Matrix.mulVec Mp vp (4 : Fin 6) -
        (s * ((iform (m 4) (m 4) : ℤ) : ZMod p) + t * ((iform (m 4) (m 5) : ℤ) : ZMod p)) = 0
      have g44 : ((iform (m 4) (m 4) : ℤ) : ZMod p) = 2 := by simp [hnorm 4]
      have g45 : ((iform (m 4) (m 5) : ℤ) : ZMod p) = -1 := by rw [h45]; norm_num <;> rfl
      rw [g44, g45]
      exact (mul_eq_zero.mp (pair_decomp_aux_four _ _ s t hs ht)).resolve_left h3ne
    · show Matrix.mulVec Mp vp (5 : Fin 6) -
        (s * ((iform (m 5) (m 4) : ℤ) : ZMod p) + t * ((iform (m 5) (m 5) : ℤ) : ZMod p)) = 0
      have g54 : ((iform (m 5) (m 4) : ℤ) : ZMod p) = -1 := by rw [h54]; norm_num <;> rfl
      have g55 : ((iform (m 5) (m 5) : ℤ) : ZMod p) = 2 := by simp [hnorm 5]
      rw [g54, g55]
      exact (mul_eq_zero.mp (pair_decomp_aux_five _ _ s t hs ht)).resolve_left h3ne
  have hMw : ∀ i : Fin 6, Matrix.mulVec Mp (vp - Matrix.mulVec Cp (s • mp 4 + t • mp 5)) i =
      Matrix.mulVec Mp vp i -
        (s * Matrix.mulVec Mp (Matrix.mulVec Cp (mp 4)) i +
          t * Matrix.mulVec Mp (Matrix.mulVec Cp (mp 5)) i) := by
    intro i
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    try rfl
  have hMw0 : Matrix.mulVec Mp (vp - Matrix.mulVec Cp (s • mp 4 + t • mp 5)) = 0 := by
    funext i
    have hi := key i
    rw [hMw i, hMv i 4, hMv i 5]
    exact hi
  have hw0 : vp - Matrix.mulVec Cp (s • mp 4 + t • mp 5) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hMp_ne hMw0
  have hvp_eq : vp = Matrix.mulVec Cp (s • mp 4 + t • mp 5) := sub_eq_zero.mp hw0
  obtain ⟨s', hs'⟩ := ZMod.intCast_surjective s
  obtain ⟨t', ht'⟩ := ZMod.intCast_surjective t
  refine ⟨s', t', fun γ => ?_⟩
  have hsum : (∑ j, ((γ j : ℤ) : ZMod p) * ((v j : ℤ) : ZMod p)) =
      s * ((iform γ (m 4) : ℤ) : ZMod p) + t * ((iform γ (m 5) : ℤ) : ZMod p) := by
    simp only [← hvp]
    rw [hvp_eq]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hMgram γ 4, ← hMgram γ 5, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  push_cast
  rw [hs', ht', hsum]
  ring

theorem tab12_det : ∀ u ∈ tab12, ∀ u' ∈ tab12,
    (u.1 * u'.2 - u.2 * u'.1 = 0 → u' = u ∨ u' = (-u.1, -u.2)) ∧
      |u.1 * u'.2 - u.2 * u'.1| ≤ 3 := by
  decide +kernel

theorem line_class_arith {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {s t : ℤ}
    (hst : ¬ ((p : ℤ) ∣ s ∧ (p : ℤ) ∣ t)) {u u' : ℤ × ℤ} (hu : u ∈ tab12) (hu' : u' ∈ tab12)
    (h : (p : ℤ) ∣ s * u.1 + t * u.2) (h' : (p : ℤ) ∣ s * u'.1 + t * u'.2) :
    u' = u ∨ u' = (-u.1, -u.2) := by
  obtain ⟨hdet, hbd⟩ := tab12_det u hu u' hu'
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have h1 : (p : ℤ) ∣ s * (u.1 * u'.2 - u.2 * u'.1) := by
    have : s * (u.1 * u'.2 - u.2 * u'.1) =
        (s * u.1 + t * u.2) * u'.2 - (s * u'.1 + t * u'.2) * u.2 := by ring
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_left h' _)
  have h2 : (p : ℤ) ∣ t * (u.1 * u'.2 - u.2 * u'.1) := by
    have : t * (u.1 * u'.2 - u.2 * u'.1) =
        (s * u'.1 + t * u'.2) * u.1 - (s * u.1 + t * u.2) * u'.1 := by ring
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_left h' _) (dvd_mul_of_dvd_left h _)
  have h3 : (p : ℤ) ∣ u.1 * u'.2 - u.2 * u'.1 := by
    by_contra hnd
    exact hst ⟨(hpz.dvd_or_dvd h1).resolve_right hnd, (hpz.dvd_or_dvd h2).resolve_right hnd⟩
  have h4 : u.1 * u'.2 - u.2 * u'.1 = 0 := by
    have hp5' : (5 : ℤ) ≤ p := by exact_mod_cast hp5
    by_contra hne
    have := Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 h3)
    omega
  exact hdet h4

end CFSG.StandardType.TableCRes

end
