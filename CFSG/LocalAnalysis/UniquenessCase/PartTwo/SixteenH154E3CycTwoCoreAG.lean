module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoFrameG

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {X : Type} [CommGroup X] {Mb : Subgroup (MulAut X)} {ψ z : MulAut X} {U : Subgroup X}
  {q m : ℕ}

theorem s16h_e3_CycTwoCoreAG_isElemAbelian (F : s16h_CycFrameG q m Mb ψ z U)
    {D : Subgroup (MulAut ↥U)} (hD : IsElemAbelian q D) : IsElemAbelian q (F.core D) := by
  have hexp : ∀ n : MulAut X, n ∈ F.core D → n ^ q = 1 := by
    intro n hn
    have hnN : n ∈ s16h_CycN Mb z := hn.1
    have hnqN : n ^ q ∈ s16h_CycN Mb z := (s16h_CycN Mb z).pow_mem hnN q
    refine F.eq_one_of_rho_eq_one hnqN ?_ ?_
    · have h1 : (⟨n ^ q, hnqN⟩ : ↥(s16h_CycN Mb z)) = ⟨n, hnN⟩ ^ q :=
        Subtype.ext (by simp)
      rw [h1, map_pow]
      exact hD.2 _ (F.rho_mem_of_mem_core D hn)
    · have hnψN : ψ⁻¹ * n * ψ ∈ s16h_CycN Mb z := F.conj_inv_mem F.psi_mem hnN
      have hψpow : (ψ⁻¹ * n * ψ) ^ q = ψ⁻¹ * n ^ q * ψ := by
        simpa using (conj_pow (a := ψ⁻¹) (b := n) (i := q))
      have h2 : (⟨ψ⁻¹ * n ^ q * ψ, F.conj_inv_mem F.psi_mem hnqN⟩ :
            ↥(s16h_CycN Mb z)) = (⟨ψ⁻¹ * n * ψ, hnψN⟩ : ↥(s16h_CycN Mb z)) ^ q :=
        Subtype.ext (by
          simp only [Subgroup.coe_pow, Subtype.coe_mk]
          rw [hψpow])
      rw [h2, map_pow]
      exact hD.2 _ (hn.2 ψ F.psi_mem hnψN)
  have hcomm : ∀ a b : MulAut X, a ∈ F.core D → b ∈ F.core D → a * b = b * a := by
    intro a b ha hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ F.core D :=
      (F.core D).mul_mem ((F.core D).mul_mem ((F.core D).mul_mem ha hb)
        ((F.core D).inv_mem ha)) ((F.core D).inv_mem hb)
    have hcN : a * b * a⁻¹ * b⁻¹ ∈ s16h_CycN Mb z := hc.1
    have hρ : F.rho ⟨a * b * a⁻¹ * b⁻¹, hcN⟩ = 1 := by
      have e : (⟨a * b * a⁻¹ * b⁻¹, hcN⟩ : ↥(s16h_CycN Mb z)) =
          ⟨a, ha.1⟩ * ⟨b, hb.1⟩ * (⟨a, ha.1⟩)⁻¹ * (⟨b, hb.1⟩)⁻¹ :=
        Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk])
      rw [e]
      simp only [map_mul, map_inv]
      have hxy : F.rho ⟨a, ha.1⟩ * F.rho ⟨b, hb.1⟩ =
          F.rho ⟨b, hb.1⟩ * F.rho ⟨a, ha.1⟩ :=
        congrArg Subtype.val (hD.1.is_comm.comm
          ⟨F.rho ⟨a, ha.1⟩, F.rho_mem_of_mem_core D ha⟩
          ⟨F.rho ⟨b, hb.1⟩, F.rho_mem_of_mem_core D hb⟩)
      rw [hxy]
      group
    have hρψ : F.rho ⟨ψ⁻¹ * (a * b * a⁻¹ * b⁻¹) * ψ,
        F.conj_inv_mem F.psi_mem hcN⟩ = 1 := by
      have haψN : ψ⁻¹ * a * ψ ∈ s16h_CycN Mb z := F.conj_inv_mem F.psi_mem ha.1
      have hbψN : ψ⁻¹ * b * ψ ∈ s16h_CycN Mb z := F.conj_inv_mem F.psi_mem hb.1
      have e : (⟨ψ⁻¹ * (a * b * a⁻¹ * b⁻¹) * ψ,
            F.conj_inv_mem F.psi_mem hcN⟩ : ↥(s16h_CycN Mb z)) =
          ⟨ψ⁻¹ * a * ψ, haψN⟩ * ⟨ψ⁻¹ * b * ψ, hbψN⟩ *
            (⟨ψ⁻¹ * a * ψ, haψN⟩)⁻¹ * (⟨ψ⁻¹ * b * ψ, hbψN⟩)⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
        group
      rw [e]
      simp only [map_mul, map_inv]
      have hxy : F.rho ⟨ψ⁻¹ * a * ψ, haψN⟩ * F.rho ⟨ψ⁻¹ * b * ψ, hbψN⟩ =
          F.rho ⟨ψ⁻¹ * b * ψ, hbψN⟩ * F.rho ⟨ψ⁻¹ * a * ψ, haψN⟩ :=
        congrArg Subtype.val (hD.1.is_comm.comm
          ⟨F.rho ⟨ψ⁻¹ * a * ψ, haψN⟩, ha.2 ψ F.psi_mem haψN⟩
          ⟨F.rho ⟨ψ⁻¹ * b * ψ, hbψN⟩, hb.2 ψ F.psi_mem hbψN⟩)
      rw [hxy]
      group
    have hone : a * b * a⁻¹ * b⁻¹ = 1 := F.eq_one_of_rho_eq_one hcN hρ hρψ
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = 1 * (b * a) := by rw [hone]
      _ = b * a := by rw [one_mul]
  exact ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext (by
    simpa using hcomm a b a.2 b.2)), hexp⟩

theorem s16h_e3_CycTwoCoreAG_mem_of_prime (hq : q.Prime) (F : s16h_CycFrameG q m Mb ψ z U)
    {D : Subgroup (MulAut ↥U)}
    (hD : ∀ a ∈ autSub (s16h_CycN Mb z) U, (∃ k : ℕ, orderOf a = q ^ k) → a ∈ D)
    {n : MulAut X} (hn : n ∈ s16h_CycN Mb z) (hqn : ∃ k : ℕ, orderOf n = q ^ k) :
    n ∈ F.core D := by
  refine ⟨hn, fun g hg h => ?_⟩
  have hmem : F.rho ⟨g⁻¹ * n * g, h⟩ ∈ autSub (s16h_CycN Mb z) U := by
    rw [← F.rho_range]
    exact MonoidHom.mem_range.mpr ⟨⟨g⁻¹ * n * g, h⟩, rfl⟩
  refine hD _ hmem ?_
  obtain ⟨k, hk⟩ := hqn
  have hgk : (g⁻¹ * n * g) ^ (q ^ k) = 1 := by
    have hgroup : (g⁻¹ * n * g) ^ (q ^ k) = g⁻¹ * n ^ (q ^ k) * g := by
      simpa using (conj_pow (a := g⁻¹) (b := n) (i := q ^ k))
    rw [hgroup, ← hk, pow_orderOf_eq_one]
    simp
  have hdiv : orderOf (⟨g⁻¹ * n * g, h⟩ : ↥(s16h_CycN Mb z)) ∣ q ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one]
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, Subtype.coe_mk] using hgk
  have hdiv2 : orderOf (F.rho ⟨g⁻¹ * n * g, h⟩) ∣ q ^ k :=
    (orderOf_map_dvd F.rho (⟨g⁻¹ * n * g, h⟩ : ↥(s16h_CycN Mb z))).trans hdiv
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hq).1 hdiv2
  exact ⟨j, hj⟩

theorem s16h_e3_CycTwoCoreAG_le_autSub [Finite X] [Finite (MulAut X)] (hq : q.Prime)
    (F : s16h_CycFrameG q m Mb ψ z U) {D : Subgroup (MulAut ↥U)}
    (hDA : D ≤ autSub (s16h_CycN Mb z) U) (hD : IsElemAbelian q D)
    (hSyl : ∀ a ∈ autSub (s16h_CycN Mb z) U, (∃ k : ℕ, orderOf a = q ^ k) → a ∈ D) :
    D ≤ autSub (F.core D) U := by
  intro d hd
  have hd_range : d ∈ F.rho.range := by
    rw [F.rho_range]
    exact hDA hd
  obtain ⟨n₀, hn₀⟩ := MonoidHom.mem_range.mp hd_range
  have hpos : orderOf (n₀ : MulAut X) ≠ 0 := (orderOf_pos (n₀ : MulAut X)).ne'
  obtain ⟨a, b, hb_notdvd, h_o⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos q hq.ne_one
  have hb_ne : b ≠ 0 := by
    rintro rfl
    exact hb_notdvd (dvd_zero q)
  have hb_one : 1 ≤ b := by omega
  set e : ℕ := b ^ (q - 1) with he
  set n : MulAut X := (n₀ : MulAut X) ^ e with hn_def
  have hq1 : q - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hq.one_lt
  have hb_dvd_e : b ∣ e := by
    rw [he]
    exact dvd_pow_self b hq1
  have hdiv : orderOf (n₀ : MulAut X) ∣ e * q ^ a := by
    have h1 : q ^ a * b ∣ q ^ a * e := mul_dvd_mul_left (q ^ a) hb_dvd_e
    rw [mul_comm (q ^ a) e] at h1
    rwa [← h_o] at h1
  have hn_pow : n ^ (q ^ a) = 1 := by
    rw [hn_def, ← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp hdiv
  have hord_dvd : orderOf n ∣ q ^ a := orderOf_dvd_iff_pow_eq_one.mpr hn_pow
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hq).1 hord_dvd
  have hnq : ∃ k : ℕ, orderOf n = q ^ k := ⟨k, hk⟩
  have hnN : n ∈ s16h_CycN Mb z := by
    rw [hn_def]
    exact (s16h_CycN Mb z).pow_mem n₀.2 e
  have hcore : n ∈ F.core D := s16h_e3_CycTwoCoreAG_mem_of_prime hq F hSyl hnN hnq
  have hd_pow : d ^ e = d := by
    have hd_q : d ^ q = 1 := hD.2 d hd
    have horder_dvd_q : orderOf d ∣ q := orderOf_dvd_iff_pow_eq_one.mpr hd_q
    have hcop : Nat.Coprime b q := (hq.coprime_iff_not_dvd.mpr hb_notdvd).symm
    have hfermat : e ≡ 1 [MOD q] := by
      rw [he]
      exact Nat.ModEq.pow_card_sub_one_eq_one hq hcop
    have hle : 1 ≤ e := by
      rw [he]
      exact one_le_pow₀ hb_one
    have hq_dvd : q ∣ e - 1 := (Nat.modEq_iff_dvd' hle).mp hfermat.symm
    have horder_dvd : orderOf d ∣ e - 1 := horder_dvd_q.trans hq_dvd
    have hd_e1 : d ^ (e - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp horder_dvd
    have he_eq : e = (e - 1) + 1 := by omega
    rw [he_eq, pow_succ, hd_e1, one_mul]
  have hρn : F.rho ⟨n, hnN⟩ = d := by
    have hsub : (⟨n, hnN⟩ : ↥(s16h_CycN Mb z)) = n₀ ^ e := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subtype.coe_mk]
      exact hn_def
    rw [hsub, map_pow, hn₀, hd_pow]
  rw [mem_autSub]
  refine ⟨⟨n, F.stab hnN⟩, ?_, ?_⟩
  · simpa using hcore
  · have : resHom U ⟨n, F.stab hnN⟩ = F.rho ⟨n, hnN⟩ := rfl
    rw [this]
    exact hρn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
