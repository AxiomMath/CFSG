module

public import CFSG.Quasithin.Vol2.TwoF4F48Spec

public section

namespace CFSG.Quasithin.H13.TwoF4F48

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.TwoF4F48 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Quasithin.H13.F45Ru CFSG.Quasithin.RuType

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

open scoped Pointwise

section Mem


theorem n1_mem : titsGen 3 ∈ twoF4H :=
  (J47.mem_twoF4H_iff (titsGen_mem_titsA (by norm_num))).2 (n1_zero)

theorem t_mem_H : titsGen 1 ∈ twoF4H :=
  (J47.mem_twoF4H_iff (titsGen_mem_titsA (by norm_num))).2 (t_zero)

theorem t_mem_N : titsGen 1 ∈ twoF4N :=
  (J47.mem_twoF4N_iff (titsGen_mem_titsA (by norm_num))).2 (t_line)

theorem q_mem_N : titsGen 2 ∈ twoF4N :=
  (J47.mem_twoF4N_iff (titsGen_mem_titsA (by norm_num))).2 (q_line)

end Mem

section Rigid

variable
  (π : ↥twoF4H →* Equiv.Perm (Fin 1755))
  (hB : ∀ (x : Equiv.Perm (Fin 1755)) (hx : x ∈ twoF4H), x ∈ twoF4N → π ⟨x, hx⟩ = x)
  (hN : ∀ (x : Equiv.Perm (Fin 1755)) (hx : x ∈ twoF4H) (p : Fin 1755),
    octGraph.dist (Sum.inl 0) (Sum.inl p) ≤ 6 → π ⟨x, hx⟩ p = x p)

theorem n1_sqH :
    (⟨titsGen 3, n1_mem⟩ : ↥twoF4H) * ⟨titsGen 3, n1_mem⟩ = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mk, n1_sq, Subgroup.coe_one]

theorem pi_n1_sq : π ⟨titsGen 3, n1_mem⟩ * π ⟨titsGen 3, n1_mem⟩ = 1 := by
  rw [← map_mul, n1_sqH, map_one]

include hN in
theorem sig_near (p : Fin 1755) (hp : octGraph.dist (Sum.inl 0) (Sum.inl p) ≤ 6) :
    (titsGen 3 * π ⟨titsGen 3, n1_mem⟩) p = p := by
  rw [Equiv.Perm.mul_apply, hN (titsGen 3) (n1_mem) p hp, ← Equiv.Perm.mul_apply, n1_sq,
    Equiv.Perm.one_apply]

include hB in
theorem sig_comm {b : Equiv.Perm (Fin 1755)} (hbA : b ∈ TA) (hb0 : b 0 = 0)
    (hbl : b • titsLine 0 = titsLine 0) (hnA : titsGen 3 * b * titsGen 3 ∈ TA)
    (hn0 : (titsGen 3 * b * titsGen 3) 0 = 0)
    (hnl : (titsGen 3 * b * titsGen 3) • titsLine 0 = titsLine 0) :
    titsGen 3 * π ⟨titsGen 3, n1_mem⟩ * b = b * (titsGen 3 * π ⟨titsGen 3, n1_mem⟩) := by
  have hbH : b ∈ twoF4H := (J47.mem_twoF4H_iff hbA).2 hb0
  have hnH : titsGen 3 * b * titsGen 3 ∈ twoF4H := (J47.mem_twoF4H_iff hnA).2 hn0
  have hpn2 := pi_n1_sq π
  have e1 := hB _ hbH ((J47.mem_twoF4N_iff hbA).2 hbl)
  have e2 := hB _ hnH ((J47.mem_twoF4N_iff hnA).2 hnl)
  have e3 : (⟨titsGen 3 * b * titsGen 3, hnH⟩ : ↥twoF4H) =
      ⟨titsGen 3, n1_mem⟩ * ⟨b, hbH⟩ * ⟨titsGen 3, n1_mem⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
  have hA : π ⟨titsGen 3, n1_mem⟩ * b * π ⟨titsGen 3, n1_mem⟩ =
      titsGen 3 * b * titsGen 3 := by
    rw [← e2, e3, map_mul, map_mul, e1]
  calc titsGen 3 * π ⟨titsGen 3, n1_mem⟩ * b
      = titsGen 3 * (π ⟨titsGen 3, n1_mem⟩ * b * π ⟨titsGen 3, n1_mem⟩) *
          π ⟨titsGen 3, n1_mem⟩ := by
        simp only [mul_assoc, hpn2, mul_one]
    _ = titsGen 3 * (titsGen 3 * b * titsGen 3) * π ⟨titsGen 3, n1_mem⟩ := by rw [hA]
    _ = b * (titsGen 3 * π ⟨titsGen 3, n1_mem⟩) := by
        simp only [← mul_assoc, n1_sq, one_mul]

include hB hN in
theorem pi_n1 (hX : (π ⟨titsGen 3, n1_mem⟩ * titsGen 2) ^ gOrder = 1) :
    π ⟨titsGen 3, n1_mem⟩ = titsGen 3 := by
  have hπn : π ⟨titsGen 3, n1_mem⟩ =
      titsGen 3 * (titsGen 3 * π ⟨titsGen 3, n1_mem⟩) := by
    rw [← mul_assoc, n1_sq, one_mul]
  have hσ1 : titsGen 3 * π ⟨titsGen 3, n1_mem⟩ = 1 := by
    refine rigid_spec _ (sig_near π hN)
      (fun b hbA hb0 hbl hnA hn0 hnl => sig_comm π hB hbA hb0 hbl hnA hn0 hnl) ?_ ?_
    · rw [← hπn, sq]
      exact pi_n1_sq π
    · rw [← hπn]
      exact hX
  rw [hπn, hσ1, mul_one]

include hB hN in
theorem twoF4_rigid (hX : (π ⟨titsGen 3, n1_mem⟩ * titsGen 2) ^ gOrder = 1)
    (y : ↥twoF4H) : π y = y := by
  have hπn := pi_n1 π hB hN hX
  obtain ⟨x, hx⟩ := y
  have hπt : π ⟨titsGen 1, t_mem_H⟩ = titsGen 1 := hB _ (t_mem_H) (t_mem_N)
  have hxA : x ∈ TA := J47.mem_A_of_mem_twoF4H hx
  have hx0 : x 0 = 0 := (J47.mem_twoF4H_iff hxA).1 hx
  obtain ⟨v, hv⟩ : ∃ v, titsLineHom ⟨x, hxA⟩ 0 = v := ⟨_, rfl⟩
  have hLv : titsLine v = x • titsLine 0 := by
    rw [← hv]
    exact titsLine_lineHom _ _
  have h0v : (0 : Fin 1755) ∈ titsLine v := by
    rw [← hv, ← hx0]
    exact J47.smul_mem_lineHom hxA ((J47.titsLine_mem_iff 0 0).2 J47.onLine_0_0)
  rcases lines_spec v h0v with hv0 | ⟨i, hi, hg⟩
  · have hxN : x ∈ twoF4N := by
      rw [J47.mem_twoF4N_iff hxA, ← hLv, hv0]
    exact hB x hx hxN
  · obtain ⟨gH, hgH⟩ : ∃ g : ↥twoF4H,
        g = (⟨titsGen 1, t_mem_H⟩ : ↥twoF4H) ^ i * ⟨titsGen 3, n1_mem⟩ := ⟨_, rfl⟩
    have hgHc : (gH : Equiv.Perm (Fin 1755)) = titsGen 1 ^ i * titsGen 3 := by
      rw [hgH, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_mk, Subgroup.coe_mk]
    have hπg : π gH = (gH : Equiv.Perm (Fin 1755)) := by
      rw [hgHc, hgH, map_mul, map_pow, hπt, hπn]
    obtain ⟨b, hb⟩ : ∃ b : ↥twoF4H, b = gH⁻¹ * ⟨x, hx⟩ := ⟨_, rfl⟩
    have hbc : (b : Equiv.Perm (Fin 1755)) = (titsGen 1 ^ i * titsGen 3)⁻¹ * x := by
      rw [hb, Subgroup.coe_mul, Subgroup.coe_inv, hgHc, Subgroup.coe_mk]
    have hbA : (b : Equiv.Perm (Fin 1755)) ∈ TA := J47.mem_A_of_mem_twoF4H b.2
    have hbN : (b : Equiv.Perm (Fin 1755)) ∈ twoF4N := by
      rw [J47.mem_twoF4N_iff hbA, hbc, mul_smul, ← hLv, ← hg, inv_smul_smul]
    have e1 : π b = b :=
      (congrArg π (Subtype.coe_eta b b.2)).symm.trans (hB _ b.2 hbN)
    have hgb : gH * b = ⟨x, hx⟩ := by rw [hb, mul_inv_cancel_left]
    calc π ⟨x, hx⟩ = π (gH * b) := by rw [hgb]
      _ = π gH * π b := map_mul _ _ _
      _ = (gH : Equiv.Perm (Fin 1755)) * (b : Equiv.Perm (Fin 1755)) := by rw [e1, hπg]
      _ = ((gH * b : ↥twoF4H) : Equiv.Perm (Fin 1755)) := (Subgroup.coe_mul _ _ _).symm
      _ = x := by rw [hgb, Subgroup.coe_mk]

end Rigid

end CFSG.Quasithin.H13.TwoF4F48
