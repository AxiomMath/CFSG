module

public import Certificates.Kernel.BabyMonster.Facts3102
public import Certificates.Kernel.BabyMonster.PktBind

public section

namespace CertificateChecks.KernelBM.Dy

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat CFSG.KC.BM.Pkt CFSG.Monster.B.Dyadic
  CFSG.Monster.B.Dyadic.Native CertificateChecks.KernelBM.Lat CertificateChecks.KernelBM.Pkt

@[expose] noncomputable def Nk (g : ℕ) : ℕ → ℕ → ℤ :=
  if g < 24 then kNumMono (nthN monoTs g)
  else if g = 24 then kNumSparse CFSG.KC.BM.Dyadic.SG24 else kNumSparse CFSG.KC.BM.Dyadic.SG25

theorem numer_eq (g : Fin 26) (t u : ℕ) (ht : t < 4371) (hu : u < 4371) :
    numer g t u = Nk g t u := by
  have e : numer g t u = numerOf CFSG.Monster.B.Native.packetRows (selK g) t u := rfl
  rw [e, Nk]
  by_cases h : (g : ℕ) < 24
  · rw [ite_eq_left h]
    exact numer_mono g h t u ht
  · rw [ite_eq_right h]
    have := g.2
    by_cases h' : (g : ℕ) = 24
    · rw [ite_eq_left h', h']
      exact numer_sparse24 t u ht hu
    · rw [ite_eq_right h', show (g : ℕ) = 25 by omega]
      exact numer_sparse25 t u ht hu

theorem bz_ent : ∀ t k : Fin 4371, Bz t k = (ent CFSG.KC.BM.Dyadic.Bs t k : ℤ) := by
  intro t k
  rw [Bz, basisRowsK, basisRows_of_text t k t.2 k.2]
  rfl

theorem cnum_int (g : Fin 26)
    {N : ℕ → ℕ → ℤ} {r : ℕ → ℕ} (hst : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs N (r i) i)
    (hnum : ∀ t u : ℕ, t < 4371 → u < 4371 → numer g t u = N t u) :
    ∃ C : Matrix (Fin 4371) (Fin 4371) ℤ, Cnum g = C.map (Int.cast : ℤ → ℚ) ∧
      ∀ i t : Fin 4371, C i t % 2 = if (r i).testBit t then 1 else 0 := by
  obtain ⟨-, hdiag, hlow, -, hcont⟩ := fact3102_of
  have hbz := bz_ent
  choose c hc using hcont
  choose q hq using fun i : Fin 4371 => hst i i.2
  choose w hw using fun i u : Fin 4371 => (hq i).2 u u.2
  set Cz : Matrix (Fin 4371) (Fin 4371) ℤ := fun i t => q i t + 2 * ∑ u, w i u * c u t with hCz
  have hrow : ∀ i k : Fin 4371, ∑ t : Fin 4371, Bz i t * N t k = 8 * ∑ t, Cz i t * Bz t k := by
    intro i k
    have h1 := hw i k
    rw [Finset.sum_range, Finset.sum_range] at h1
    simp only [← hbz] at h1
    rw [h1]
    refine congrArg (8 * ·) ?_
    simp only [hCz, add_mul, Finset.sum_add_distrib]
    rw [add_right_inj]
    have e1 : ∑ u : Fin 4371, w i u * (if k = u then (128 : ℤ) else 0) = w i k * 128 := by
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq]
      simp
    calc 256 * w i k = 2 * ∑ u : Fin 4371, w i u * (if k = u then (128 : ℤ) else 0) := by
          rw [e1]
          ring
      _ = 2 * ∑ u : Fin 4371, w i u * ∑ t : Fin 4371, c u t * Bz t k := by simp only [hc]
      _ = ∑ t : Fin 4371, 2 * (∑ u : Fin 4371, w i u * c u t) * Bz t k := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => by ring
  have key : Bzq * Mq g = Cz.map (Int.cast : ℤ → ℚ) * Bzq := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.map_apply, Bzq, Mq]
    have h2 := congrArg (fun z : ℤ => (z : ℚ)) (hrow i k)
    push_cast at h2
    calc ∑ t : Fin 4371, (Bz i t : ℚ) * ((numer g t k : ℚ) / 8) =
        (∑ t : Fin 4371, (Bz i t : ℚ) * (N t k : ℚ)) / 8 := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun t _ => by
            rw [hnum t k t.2 k.2]
            ring
      _ = ∑ t : Fin 4371, (Cz i t : ℚ) * (Bz t k : ℚ) := by
          rw [h2]
          ring
  have hU : Bzq.IsUpperTriangular := fun i j hij => by
    simp only [Bzq]
    rw [hlow i j hij]
    simp
  have hdet : IsUnit Bzq.det := by
    rw [Matrix.det_of_isUpperTriangular hU]
    refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    simp only [Bzq]
    rw [hdiag i]
    positivity
  refine ⟨Cz, ?_, fun i t => ?_⟩
  · rw [Cnum, key, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  · rw [hCz, Int.add_mul_emod_self_left]
    exact (hq i).1 t t.2

theorem cnum_den (g : Fin 26)
    {N : ℕ → ℕ → ℤ} {r : ℕ → ℕ} (hst : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs N (r i) i)
    (hnum : ∀ t u : ℕ, t < 4371 → u < 4371 → numer g t u = N t u) :
    ∀ i t : Fin 4371, (Cnum g i t).den = 1 := by
  obtain ⟨C, hC, -⟩ := cnum_int g hst hnum
  intro i t
  rw [hC, Matrix.map_apply]
  exact Rat.den_intCast _

theorem cmat_eq (g : Fin 26)
    {N : ℕ → ℕ → ℤ} {r : ℕ → ℕ} (hst : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs N (r i) i)
    (hnum : ∀ t u : ℕ, t < 4371 → u < 4371 → numer g t u = N t u) :
    ∀ i t : Fin 4371, Cmat g i t = if (r i).testBit t then 1 else 0 := by
  obtain ⟨C, hC, hp⟩ := cnum_int g hst hnum
  intro i t
  rw [Cmat, hC, Matrix.map_apply, Rat.num_intCast, ← ZMod.intCast_mod, Nat.cast_ofNat, hp i t]
  split <;> simp

end CertificateChecks.KernelBM.Dy

end
