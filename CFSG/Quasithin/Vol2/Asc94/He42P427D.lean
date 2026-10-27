module

public import CFSG.Quasithin.Vol2.Asc94.He42P427C

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

theorem p427_odd_dvd_two_pow {n k : ℕ} (hn : Odd n) (hd : n ∣ 2 ^ k) : n = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rcases j with _ | j
  · simpa using hj
  · exfalso
    rw [hj, pow_succ] at hn
    exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 (dvd_mul_left 2 _))

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p427_fin_e12_ne : ∀ g : HeJ.GL2, g ^ 3 = 1 → g ≠ 1 →
    (Matrix.of ![![0, 1], ![0, 0]] : HeJ.M2) + g.val ≠ 0 := by
  decide +kernel

theorem p427_card_pow2 (T : HeSetup G) (hB : T.BaseFacts) {z : G} (P : P427 T z)
    {w : G} (hwZ : w ∈ T.Z) (hw1 : w ≠ 1) (hwdet : (T.m w).det = 0) :
    ∃ k : ℕ, Nat.card ↥(centralizer ({w} : Set G) ⊓ centralizer ({T.a} : Set G)) = 2 ^ k := by
  obtain ⟨s, hs⟩ := (T.fusion_facts P.hfus P.hzZ P.hzm).1 w hwZ hw1 hwdet
  obtain ⟨n, hnN, hn⟩ := P.hfus z P.hzZ w hwZ s⁻¹ (by rw [inv_inv]; exact hs)
  have hzeq : z = n * w * n⁻¹ := by rw [← hn]; group
  have haZ : T.a ∈ T.Z := T.hD.ha
  have hta : n * T.a * n⁻¹ ∈ T.Z := T.hD.mem_Z_conj hnN haZ
  have hta_det : (T.m (n * T.a * n⁻¹)).det ≠ 0 := by
    have hconj : (n⁻¹)⁻¹ * T.a * n⁻¹ = n * T.a * n⁻¹ := by rw [inv_inv]
    refine p427_det_conj T P.hfus (g := n⁻¹) haZ hta hconj ?_
    rw [T.hD.ham, Matrix.det_one]
    exact one_ne_zero
  have hfour := P.hfour _ hta hta_det
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hfour
  refine ⟨k, ?_⟩
  rw [← hk]
  apply p427_card_conj_eq _ _ n
  · intro x hx
    have hxw : x * w = w * x := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).1
    have hxa : x * T.a = T.a * x := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2
    refine Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_singleton_iff.2 ?_⟩
    · calc n * x * n⁻¹ * z = n * x * n⁻¹ * (n * w * n⁻¹) := by rw [← hzeq]
        _ = n * (x * w) * n⁻¹ := by group
        _ = n * (w * x) * n⁻¹ := by rw [hxw]
        _ = z * (n * x * n⁻¹) := by rw [hzeq]; group
    · calc n * x * n⁻¹ * (n * T.a * n⁻¹) = n * (x * T.a) * n⁻¹ := by group
        _ = n * (T.a * x) * n⁻¹ := by rw [hxa]
        _ = (n * T.a * n⁻¹) * (n * x * n⁻¹) := by group
  · intro y hy
    have hyz : y * z = z * y := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).1
    have hya : y * (n * T.a * n⁻¹) = (n * T.a * n⁻¹) * y :=
      mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).2
    refine Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_singleton_iff.2 ?_⟩
    · calc n⁻¹ * y * n * w = n⁻¹ * y * n * (n⁻¹ * z * n) := by rw [hn]
        _ = n⁻¹ * (y * z) * n := by group
        _ = n⁻¹ * (z * y) * n := by rw [hyz]
        _ = n⁻¹ * z * n * (n⁻¹ * y * n) := by group
        _ = w * (n⁻¹ * y * n) := by rw [hn]
    · calc n⁻¹ * y * n * T.a = n⁻¹ * (y * (n * T.a * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * T.a * n⁻¹) * y) * n := by rw [hya]
        _ = T.a * (n⁻¹ * y * n) := by group

theorem p427_O_trivial (T : HeSetup G) (hB : T.BaseFacts) {z : G} (P : P427 T z)
    (O : Subgroup G) (hOM : O ≤ centralizer ({T.a} : Set G))
    (hOn : ∀ m ∈ centralizer ({T.a} : Set G), ∀ o ∈ O, m * o * m⁻¹ ∈ O)
    (hodd : Odd (Nat.card ↥O)) : O = ⊥ := by
  have haZ : T.a ∈ T.Z := T.hD.ha
  have haB : T.a ∈ T.B := T.hD.a_mem_B T.hxN T.hxa T.hx3
  obtain ⟨b, hbB, hb1, hba, hbm⟩ := p427_exists_b T
  have hbZ : b ∈ T.Z := hB.B_le_Z hbB
  have hb2 : b * b = 1 := hB.A_sq b (hB.Z_le_A hbZ)
  have hzZ := P.hzZ
  have hz2 := P.hz2
  have hLM : T.L ≤ centralizer ({T.a} : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (p427_L_le_centB T hB hl) T.a haB).symm
  have hzM : z ∈ centralizer ({T.a} : Set G) :=
    mem_centralizer_singleton_iff.2 (hB.A_comm z (hB.Z_le_A hzZ) T.a (hB.Z_le_A haZ))
  have hbM : b ∈ centralizer ({T.a} : Set G) :=
    mem_centralizer_singleton_iff.2 (hB.A_comm b (hB.Z_le_A hbZ) T.a (hB.Z_le_A haZ))
  have hOL : O ⊓ T.L = ⊥ := by
    have hnorm : ((O ⊓ T.L).subgroupOf T.L).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      refine Subgroup.mem_inf.2 ⟨hOn g (hLM g.2) _ (Subgroup.mem_inf.1 hn).1, ?_⟩
      exact T.L.mul_mem (T.L.mul_mem g.2 (Subgroup.mem_inf.1 hn).2) (T.L.inv_mem g.2)
    have hKodd : Odd (Nat.card ↥(O ⊓ T.L)) :=
      Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)
    have hKB := P.hLodd (O ⊓ T.L) inf_le_right hnorm hKodd
    have hd := Subgroup.card_dvd_of_le hKB
    rw [hB.card_B] at hd
    have h1 := p427_odd_dvd_two_pow (k := 2) hKodd hd
    exact Subgroup.eq_bot_of_card_eq _ h1
  have hfpb : ∀ o ∈ O, b * o * b⁻¹ = o → o = 1 := by
    intro o ho hbo
    have hbo' : b * o = o * b := (mul_inv_eq_iff_eq_mul).1 hbo
    have hcomm := p427_comm_all_B T hbB hb1 hba
      (mem_centralizer_singleton_iff.1 (hOM ho)) hbo'.symm
    have hoL : o ∈ O ⊓ T.L := Subgroup.mem_inf.2 ⟨ho, P.hL o hcomm⟩
    have : o ∈ (⊥ : Subgroup G) := by rw [← hOL]; exact hoL
    exact (Subgroup.mem_bot.1 this)
  have hOS : O ⊓ (centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)) = ⊥ := by
    have hKodd : Odd (Nat.card ↥(O ⊓ (centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)))) :=
      Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)
    have hd := Subgroup.card_dvd_of_le (inf_le_right :
      O ⊓ (centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)) ≤
        centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G))
    rw [P.hS] at hd
    have h1 := p427_odd_dvd_two_pow (k := 9) hKodd hd
    exact Subgroup.eq_bot_of_card_eq _ h1
  have hfpz : ∀ o ∈ O, z * o * z⁻¹ = o → o = 1 := by
    intro o ho hzo
    have hzo' : z * o = o * z := (mul_inv_eq_iff_eq_mul).1 hzo
    have hoS : o ∈ O ⊓ (centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)) :=
      Subgroup.mem_inf.2 ⟨ho, Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 hzo'.symm,
        mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 (hOM ho))⟩⟩
    have : o ∈ (⊥ : Subgroup G) := by rw [← hOS]; exact hoS
    exact (Subgroup.mem_bot.1 this)
  have hinvb := p427_inv_of_fpf O hb2 (fun o ho => hOn b hbM o ho) hfpb
  have hinvz := p427_inv_of_fpf O hz2 (fun o ho => hOn z hzM o ho) hfpz
  have hwcent : ∀ o ∈ O, (z * b) * o * (z * b)⁻¹ = o := by
    intro o ho
    calc (z * b) * o * (z * b)⁻¹ = z * (b * o * b⁻¹) * z⁻¹ := by group
      _ = z * o⁻¹ * z⁻¹ := by rw [hinvb o ho]
      _ = (z * o * z⁻¹)⁻¹ := by group
      _ = o := by rw [hinvz o ho, inv_inv]
  have hwZ : z * b ∈ T.Z := T.Z.mul_mem hzZ hbZ
  have hmw : T.m (z * b) = Matrix.of ![![0, 1], ![0, 0]] + T.g.val := by
    rw [T.hD.hT.mmul z hzZ b hbZ, P.hzm, hbm]
  have hw1 : z * b ≠ 1 := by
    intro h
    have h0 : T.m (z * b) = 0 := by rw [h, T.hD.hT.m_one]
    rw [hmw] at h0
    exact p427_fin_e12_ne T.g (T.hD.g_pow_three T.hxN T.hxa T.hx3)
      (T.hD.g_ne_one T.hxN T.hxa T.hx3) h0
  have hwdet : (T.m (z * b)).det = 0 := by
    rw [hmw]
    exact p427_fin_e12 T.g (T.hD.g_pow_three T.hxN T.hxa T.hx3) (T.hD.g_ne_one T.hxN T.hxa T.hx3)
  obtain ⟨k, hk⟩ := p427_card_pow2 T hB P hwZ hw1 hwdet
  have hOR : O ≤ centralizer ({z * b} : Set G) ⊓ centralizer ({T.a} : Set G) := by
    intro o ho
    refine Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_,
      mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 (hOM ho))⟩
    have := hwcent o ho
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hd := Subgroup.card_dvd_of_le hOR
  rw [hk] at hd
  have h1 := p427_odd_dvd_two_pow hodd hd
  exact Subgroup.eq_bot_of_card_eq _ h1

end CFSG.Quasithin.A94.He42
