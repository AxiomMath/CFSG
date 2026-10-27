module

public import Certificates.Kernel.BabyMonster.A0
public import Certificates.Kernel.BabyMonster.Stab.Stab26
public import Certificates.Kernel.BabyMonster.Facts3101
public import CFSG.Monster.B.Dyadic.FactsA0

public section

namespace CertificateChecks.KernelBM.A0

open CFSG.KC.BM CFSG.KC.BM.Pkt CFSG.KC.BM.Dy CFSG.KC.BM.Lat CFSG.KC.BM.Dyadic CFSG.Monster.B.Dyadic
  CertificateChecks.KernelBM.Pkt

theorem mqN_mul {T U : Nat} (hT : tabOK T = true) (hU : tabOK U = true) :
    MqN (kNumMono T) * MqN (kNumMono U) = MqN (kNumMono (compT T U)) := by
  ext t u
  simp only [Matrix.mul_apply, MqN]
  have h := compT_sound hT hU t u t.2 u.2
  rw [Finset.sum_range] at h
  have h2 := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at h2
  calc ∑ j : Fin 4371, (kNumMono T t j : ℚ) / 8 * ((kNumMono U j u : ℚ) / 8) =
      (∑ j : Fin 4371, (kNumMono T t j : ℚ) * (kNumMono U j u : ℚ)) / 64 := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = (kNumMono (compT T U) t u : ℚ) / 8 := by
        rw [← h2]
        ring

theorem numerAt_mono {k T : Nat} (hk : k < 48)
    (h : monoOK (lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S k) T = true) (hT : tabOK T = true) :
    MqN (numerAt k) = MqN (kNumMono T) := by
  ext t u
  have e : numerAt k t u = kNumMono T t u := by
    change numerOf CFSG.Monster.B.Native.packetRows k t u = _
    rw [CFSG.Monster.B.Native.packetRows, CFSG.KD.PktBind.eq]
    exact numerOf_mono CFSG.KD.PktBind.lines CFSG.KD.PktBind.nlines lines_ok hk h pieces_ok hT
      t u t.2
  simp only [MqN]
  rw [e]

theorem numerAt_sel {g : Nat} (hg : g < 24) :
    MqN (numerAt (selK g)) = MqN (kNumMono (nthN monoTs g)) := by
  ext t u
  have e : numerAt (selK g) t u = kNumMono (nthN monoTs g) t u := numer_mono g hg t u t.2
  simp only [MqN]
  rw [e]

theorem prod_mat : MqN (numerAt 28) * MqN (numerAt 1) * MqN (numerAt 2) * MqN (numerAt 4) *
    MqN (numerAt 5) * MqN (numerAt 10) * MqN (numerAt 17) = Mq26 := by
  have h28 : MqN (numerAt 28) = MqN (kNumMono (nthN G6.b0 0)) := numerAt_sel (g := 6) (by norm_num)
  have h1 : MqN (numerAt 1) = MqN (kNumMono (nthN G0.b0 0)) := numerAt_sel (g := 0) (by norm_num)
  rw [h28, h1, numerAt_mono (by norm_num) mono2 tab2, numerAt_mono (by norm_num) mono4 tab4,
    numerAt_mono (by norm_num) mono5 tab5, numerAt_mono (by norm_num) mono10 tab10,
    numerAt_mono (by norm_num) mono17 tab17, mqN_mul tabG6 tabG0]
  change MqN (kNumMono c1) * _ * _ * _ * _ * _ = _
  rw [mqN_mul tab_c1 tab2]
  change MqN (kNumMono c2) * _ * _ * _ * _ = _
  rw [mqN_mul tab_c2 tab4]
  change MqN (kNumMono c3) * _ * _ * _ = _
  rw [mqN_mul tab_c3 tab5]
  change MqN (kNumMono c4) * _ * _ = _
  rw [mqN_mul tab_c4 tab10]
  change MqN (kNumMono c5) * _ = _
  rw [mqN_mul tab_c5 tab17, Nat.eq_of_beq_eq_true prod_a0]
  rfl

theorem skipP_eq (k : Fin 4370) : skipP k = (pIdx.succAbove k : ℕ) := by
  rw [skipP, CertificateChecks.KernelBM.Fix.val_succAbove]

theorem intCast_mod2 (x : ℤ) : ((x % 2 : ℤ) : ZMod 2) = (x : ZMod 2) := by
  have h := ZMod.intCast_mod x 2
  rwa [Nat.cast_ofNat] at h

theorem rows_a0 : ∀ j : Fin 4370,
    ∃ c : Fin 4371 → ℤ, (∀ u : Fin 4371,
      ∑ t : Fin 4371, Bz (pIdx.succAbove j) t * numer26 t u = 8 * ∑ t : Fin 4371, c t * Bz t u) ∧
    ∀ t : Fin 4370,
      (c (pIdx.succAbove t) : ZMod 2) + (c pIdx : ZMod 2) * fvec (pIdx.succAbove t) =
        F0row j t := by
  obtain ⟨-, -, -, -, hcont⟩ := CertificateChecks.KernelBM.Dy.fact3102_of
  have hbz := CertificateChecks.KernelBM.Dy.bz_ent
  choose c' hc' using hcont
  intro j
  obtain ⟨q, hq, hw⟩ := CertificateChecks.KernelBM.Dy.stab26 j j.2
  have hw2 : ∀ u : Fin 4371, ∃ w : ℤ, ∑ t ∈ Finset.range 4371,
      (ent CFSG.KC.BM.Dyadic.Bs (skipP j) t : ℤ) * kNumMono (nthN G26.b0 0) t u =
        8 * (∑ i ∈ Finset.range 4371, q i * (ent CFSG.KC.BM.Dyadic.Bs i u : ℤ) + 256 * w) :=
    fun u => hw u u.2
  choose w hw' using hw2
  refine ⟨fun t => q t + 2 * ∑ v : Fin 4371, w v * c' v t, fun u => ?_, fun t => ?_⟩
  · have h1 := hw' u
    rw [Finset.sum_range, Finset.sum_range, skipP_eq] at h1
    simp only [← hbz] at h1
    change ∑ t : Fin 4371, Bz (pIdx.succAbove j) t * kNumMono (nthN G26.b0 0) t u = _
    rw [h1]
    refine congrArg (8 * ·) ?_
    simp only [add_mul, Finset.sum_add_distrib]
    rw [add_right_inj]
    have e1 : ∑ v : Fin 4371, w v * (if u = v then (128 : ℤ) else 0) = w u * 128 := by
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq]
      simp
    calc 256 * w u = 2 * ∑ v : Fin 4371, w v * (if u = v then (128 : ℤ) else 0) := by
          rw [e1]
          ring
      _ = 2 * ∑ v : Fin 4371, w v * ∑ t : Fin 4371, c' v t * Bz t u := by simp only [hc']
      _ = ∑ t : Fin 4371, 2 * (∑ v : Fin 4371, w v * c' v t) * Bz t u := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun v _ => by ring
  · have h2 := congrArg (fun z : ℤ => (z : ZMod 2)) (hq t t.2)
    simp only [intCast_mod2, skipP_eq] at h2
    push_cast at h2
    have h20 : (2 : ZMod 2) = 0 := rfl
    have hp : ((pIdx : Fin 4371) : ℕ) = 1197 := rfl
    push_cast
    simp only [h20, zero_mul, add_zero, hp, CertificateChecks.KernelBM.Fix.fvec_eq,
      CFSG.KC.BM.Fix.vecOf, F0row]
    exact h2

theorem factA0_of : FactA0 :=
  ⟨prod_mat, rows_a0⟩

end CertificateChecks.KernelBM.A0

end
