module

public import CFSG.Timmesfeld.Orders.Distinct
import all CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.Timmesfeld

open CFSG.Open
open CFSG.Timmesfeld.Orders

private theorem top_ne_six {n f g : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hN : f * (n * (n + 1) / 2) = 12 * g) (hw : f * (n + 1) = 6) : False := by
  have h2 : f * (n * (n + 1)) = 24 * g := by
    have hd : n * (n + 1) = 2 * (n * (n + 1) / 2) :=
      (Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd).symm
    calc f * (n * (n + 1)) = f * (2 * (n * (n + 1) / 2)) :=
          congrArg (fun x => f * x) hd
      _ = 2 * (f * (n * (n + 1) / 2)) := by ring
      _ = 2 * (12 * g) := by rw [hN]
      _ = 24 * g := by ring
  have hn4 : n = 4 * g := by
    have h6 : 6 * n = 24 * g := by
      calc 6 * n = f * (n + 1) * n := by rw [← hw]
        _ = f * (n * (n + 1)) := by ring
        _ = 24 * g := h2
    omega
  subst hn4
  have hfg : f * (4 * g + 1) = 6 := by simpa [Nat.mul_add, mul_assoc] using hw
  have hf5 : f * 5 ≤ 6 := by
    calc f * 5 ≤ f * (4 * g + 1) := Nat.mul_le_mul_left f (by omega)
      _ = 6 := hfg
  have hf1 : f ≤ 1 := by nlinarith [hf, hf5]
  have hf_eq : f = 1 := by omega
  rw [hf_eq] at hfg
  omega

theorem ordA_ne_ordD_four {n f g : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordA n (2 ^ f) ≠ ordD 4 (2 ^ g) := by
  intro hm
  have hA := profile_ordA hn hf
  have hD : Profile (ordA n (2 ^ f)) (g * (4 * (4 - 1))) (zD 4 g) := by
    rw [hm]
    exact profile_ordD (by norm_num : 1 ≤ 4) hg
  obtain ⟨hN, hZ⟩ := hA.transfer hD
  have hN' : f * (n * (n + 1) / 2) = 12 * g := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hN
  have hwA : zA n f (f * (n + 1)) := by
    unfold zA
    exact ⟨n + 1, Finset.mem_Icc.2 ⟨by omega, le_rfl⟩, dvd_rfl⟩
  have hw2 : 2 ≤ f * (n + 1) := by
    have : 2 ≤ n + 1 := by omega
    exact le_trans (by omega : 2 ≤ 1 * (n + 1)) (Nat.mul_le_mul_right _ hf)
  have hw6 : f * (n + 1) ≠ 6 := fun h6 => top_ne_six hn hf hg hN' h6
  have hwD : zD 4 g (f * (n + 1)) := (hZ _ hw2 hw6).1 hwA
  have hwle : f * (n + 1) ≤ 6 * g := by
    have := zD_le (n := 4) (f := g) (k := f * (n + 1)) (by omega) (by norm_num) hwD
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hwge : 6 * g ≤ f * (n + 1) := by
    by_cases hg1 : g = 1
    · subst hg1
      have hw2' : 2 ≤ f * (n + 1) := hw2
      have hwle' : f * (n + 1) ≤ 6 := by simpa using hwle
      have h2 : n * (f * (n + 1)) = 24 := by
        have hd : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
          Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd
        calc n * (f * (n + 1)) = f * (n * (n + 1)) := by ring
          _ = f * (2 * (n * (n + 1) / 2)) := congrArg (fun x => f * x) hd.symm
          _ = 2 * (f * (n * (n + 1) / 2)) := by ring
          _ = 2 * 12 := by rw [hN']
          _ = 24 := by norm_num
      set w := f * (n + 1) with hwdef
      have hw2w : 2 ≤ w := hw2'
      have hwlew : w ≤ 6 := hwle'
      have hwn6 : w ≠ 6 := hw6
      have h2w : n * w = 24 := h2
      exfalso
      have hwle5 : w ≤ 5 := by omega
      interval_cases w
      · have hn : n = 12 := by omega
        subst hn
        omega
      · have hn : n = 8 := by omega
        subst hn
        omega
      · have hn : n = 6 := by omega
        subst hn
        omega
      · omega
    · have h6g : zD 4 g (6 * g) := by
        unfold zD
        exact Or.inr ⟨3, Finset.mem_Icc.2 ⟨by norm_num, by norm_num⟩, ⟨1, by ring⟩⟩
      have h6g6 : 6 * g ≠ 6 := by omega
      have hzA : zA n f (6 * g) := (hZ _ (by omega) h6g6).2 h6g
      exact zA_le (by omega) hzA
  have hw : f * (n + 1) = 6 * g := le_antisymm hwle hwge
  have h2 : n * (f * (n + 1)) = 24 * g := by
    have hd : n * (n + 1) = 2 * (n * (n + 1) / 2) :=
      (Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd).symm
    calc n * (f * (n + 1)) = f * (n * (n + 1)) := by ring
      _ = f * (2 * (n * (n + 1) / 2)) := congrArg (fun x => f * x) hd
      _ = 2 * (f * (n * (n + 1) / 2)) := by ring
      _ = 2 * (12 * g) := by rw [hN']
      _ = 24 * g := by ring
  rw [hw] at h2
  have hn4 : n = 4 := by
    have h2' : 6 * n = 24 := by
      have e : n * (6 * g) = (6 * n) * g := by ring
      rw [e] at h2
      exact Nat.eq_of_mul_eq_mul_right (by omega) h2
    omega
  subst hn4
  have h5f : f * 5 = 6 * g := by
    have := hN'
    norm_num at this
    omega
  have hzA4 : zA 4 f (4 * f) := by
    unfold zA
    exact ⟨4, Finset.mem_Icc.2 ⟨by norm_num, by norm_num⟩, ⟨1, by ring⟩⟩
  have hzD4 : zD 4 g (4 * f) := (hZ (4 * f) (by omega) (by omega)).1 hzA4
  obtain ⟨t, rfl⟩ : ∃ t, f = 6 * t := by
    have h6 : 6 ∣ f := by
      have h65 : 6 ∣ 5 * f := ⟨g, by rw [mul_comm 5 f]; exact h5f⟩
      exact Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 6 5) h65
    exact h6
  have hg5 : g = 5 * t := by
    have h : 6 * (5 * t) = 6 * g := by
      rw [← h5f]
      ring
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 6) h).symm
  subst hg5
  have ht : 0 < t := by omega
  simp only [zD] at hzD4
  rcases hzD4 with h | ⟨i, hi, h⟩
  · have hle := Nat.le_of_dvd (by positivity) h
    omega
  · have h' : 24 ∣ 5 * (2 * i) := by
      have h2 : 24 * t ∣ (5 * (2 * i)) * t := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using h
      exact Nat.dvd_of_mul_dvd_mul_right ht h2
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    have hi3 : i ≤ 3 := by simpa using (Finset.mem_Icc.1 hi).2
    interval_cases i <;> norm_num at h'

theorem ordA_ne_ordTrialityD4 {n f g : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordA n (2 ^ f) ≠ ordTrialityD4 (2 ^ g) := by
  intro hm
  have hA := profile_ordA hn hf
  have hD : Profile (ordA n (2 ^ f)) (g * 12) (zD4 g) := by
    rw [hm]
    exact profile_ordTrialityD4 hg
  obtain ⟨hN, hZ⟩ := hA.transfer hD
  have hN' : f * (n * (n + 1) / 2) = 12 * g := by
    rw [hN]
    ring
  have hwA : zA n f (f * (n + 1)) := by
    unfold zA
    exact ⟨n + 1, Finset.mem_Icc.2 ⟨by omega, le_rfl⟩, dvd_rfl⟩
  have hw2 : 2 ≤ f * (n + 1) := by
    have : 2 ≤ n + 1 := by omega
    exact le_trans (by omega : 2 ≤ 1 * (n + 1)) (Nat.mul_le_mul_right _ hf)
  have hw6 : f * (n + 1) ≠ 6 := fun h6 => top_ne_six hn hf hg hN' h6
  have hwD : zD4 g (f * (n + 1)) := (hZ _ hw2 hw6).1 hwA
  have hwle : f * (n + 1) ≤ 12 * g := by
    have := zD4_le (f := g) (k := f * (n + 1)) (by omega) hwD
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have h12g : zD4 g (12 * g) := by
    unfold zD4
    refine Or.inl ⟨⟨1, by ring⟩, ?_⟩
    intro h
    have hle := Nat.le_of_dvd (by positivity) h
    omega
  have h12g6 : 12 * g ≠ 6 := by omega
  have hzA : zA n f (12 * g) := (hZ _ (by omega) h12g6).2 h12g
  have hwge : 12 * g ≤ f * (n + 1) := zA_le (by omega) hzA
  have hw : f * (n + 1) = 12 * g := le_antisymm hwle hwge
  have h2 : n * (f * (n + 1)) = 24 * g := by
    have hd : n * (n + 1) = 2 * (n * (n + 1) / 2) :=
      (Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd).symm
    calc n * (f * (n + 1)) = f * (n * (n + 1)) := by ring
      _ = f * (2 * (n * (n + 1) / 2)) := congrArg (fun x => f * x) hd
      _ = 2 * (f * (n * (n + 1) / 2)) := by ring
      _ = 2 * (12 * g) := by rw [hN']
      _ = 24 * g := by ring
  rw [hw] at h2
  have hn2 : n = 2 := by
    have h2' : 12 * n = 24 := by
      have e : n * (12 * g) = (12 * n) * g := by ring
      rw [e] at h2
      exact Nat.eq_of_mul_eq_mul_right (by omega) h2
    omega
  have hf4 : f = 4 * g := by
    have := hN'
    rw [hn2] at this
    norm_num at this
    omega
  subst hn2
  have hzA2 : zA 2 f (2 * f) := by
    unfold zA
    exact ⟨2, Finset.mem_Icc.2 ⟨by norm_num, by norm_num⟩, ⟨1, by ring⟩⟩
  have h2f6 : 2 * f ≠ 6 := by omega
  have hzD4 : zD4 g (2 * f) := (hZ (2 * f) (by omega) h2f6).1 hzA2
  subst hf4
  have hzD4' : zD4 g (8 * g) := by
    have e : 2 * (4 * g) = 8 * g := by ring
    rwa [e] at hzD4
  simp only [zD4] at hzD4'
  rcases hzD4' with ⟨h, -⟩ | h | h
  · have h' : 8 ∣ 12 := by
      rw [mul_comm g 12] at h
      exact Nat.dvd_of_mul_dvd_mul_right (by omega) h
    norm_num at h'
  · have h' : 8 ∣ 6 := by
      rw [mul_comm g 6] at h
      exact Nat.dvd_of_mul_dvd_mul_right (by omega) h
    norm_num at h'
  · have h' : 8 ∣ 2 := by
      rw [mul_comm g 2] at h
      exact Nat.dvd_of_mul_dvd_mul_right (by omega) h
    norm_num at h'

end CFSG.Timmesfeld

end
