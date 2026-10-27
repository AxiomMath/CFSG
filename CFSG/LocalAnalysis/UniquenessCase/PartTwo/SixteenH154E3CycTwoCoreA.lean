module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoFrame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {X : Type} [CommGroup X] {Mb : Subgroup (MulAut X)} {ψ z : MulAut X} {U : Subgroup X}

namespace s16h_CycFrame

variable {Mb : Subgroup (MulAut X)} {ψ z : MulAut X} {U : Subgroup X}

private theorem s16h_e3_CycTwoCoreA_pow_three (F : s16h_CycFrame Mb ψ z U)
    {D : Subgroup (MulAut ↥U)} (hD : IsElemAbelian 3 D) {n : MulAut X}
    (hn : n ∈ F.core D) : n ^ 3 = 1 := by
  have hnc : n ^ 3 ∈ F.core D := (F.core D).pow_mem hn 3
  have hψ : ψ⁻¹ * n * ψ ∈ F.core D :=
    F.conj_mem_core D (Mb.inv_mem F.psi_mem) hn
  have h1 : F.rho ⟨n ^ 3, hnc.1⟩ = 1 := by
    have e : (⟨n ^ 3, hnc.1⟩ : ↥(s16h_CycN Mb z)) =
        (⟨n, hn.1⟩ : ↥(s16h_CycN Mb z)) ^ 3 := Subtype.ext (by simp)
    rw [e, map_pow]
    exact hD.2 _ (F.rho_mem_of_mem_core D hn)
  have h2 : F.rho ⟨ψ⁻¹ * n ^ 3 * ψ, F.conj_inv_mem F.psi_mem hnc.1⟩ = 1 := by
    have e : (⟨ψ⁻¹ * n ^ 3 * ψ, F.conj_inv_mem F.psi_mem hnc.1⟩ :
        ↥(s16h_CycN Mb z)) = (⟨ψ⁻¹ * n * ψ, hψ.1⟩ : ↥(s16h_CycN Mb z)) ^ 3 :=
      Subtype.ext (by
        show ψ⁻¹ * n ^ 3 * ψ = (ψ⁻¹ * n * ψ) ^ 3
        simpa using (conj_pow (a := ψ⁻¹) (b := n) (i := 3)).symm)
    rw [e, map_pow]
    exact hD.2 _ (F.rho_mem_of_mem_core D hψ)
  exact F.eq_one_of_rho_eq_one hnc.1 h1 h2

private theorem s16h_e3_CycTwoCoreA_comm (F : s16h_CycFrame Mb ψ z U)
    {D : Subgroup (MulAut ↥U)} (hD : IsElemAbelian 3 D) {a b : MulAut X}
    (ha : a ∈ F.core D) (hb : b ∈ F.core D) : a * b = b * a := by
  let c : MulAut X := a * b * a⁻¹ * b⁻¹
  have hc : c ∈ F.core D :=
    (F.core D).mul_mem ((F.core D).mul_mem ((F.core D).mul_mem ha hb) ((F.core D).inv_mem ha))
      ((F.core D).inv_mem hb)
  have hpa : ψ⁻¹ * a * ψ ∈ F.core D :=
    F.conj_mem_core D (Mb.inv_mem F.psi_mem) ha
  have hpb : ψ⁻¹ * b * ψ ∈ F.core D :=
    F.conj_mem_core D (Mb.inv_mem F.psi_mem) hb
  have hcomm : F.rho ⟨a, ha.1⟩ * F.rho ⟨b, hb.1⟩ =
      F.rho ⟨b, hb.1⟩ * F.rho ⟨a, ha.1⟩ :=
    congrArg Subtype.val (hD.1.is_comm.comm
      ⟨F.rho ⟨a, ha.1⟩, F.rho_mem_of_mem_core D ha⟩
      ⟨F.rho ⟨b, hb.1⟩, F.rho_mem_of_mem_core D hb⟩)
  have hcommψ : F.rho ⟨ψ⁻¹ * a * ψ, hpa.1⟩ * F.rho ⟨ψ⁻¹ * b * ψ, hpb.1⟩ =
      F.rho ⟨ψ⁻¹ * b * ψ, hpb.1⟩ * F.rho ⟨ψ⁻¹ * a * ψ, hpa.1⟩ :=
    congrArg Subtype.val (hD.1.is_comm.comm
      ⟨F.rho ⟨ψ⁻¹ * a * ψ, hpa.1⟩, F.rho_mem_of_mem_core D hpa⟩
      ⟨F.rho ⟨ψ⁻¹ * b * ψ, hpb.1⟩, F.rho_mem_of_mem_core D hpb⟩)
  have h1 : F.rho ⟨c, hc.1⟩ = 1 := by
    have e : (⟨c, hc.1⟩ : ↥(s16h_CycN Mb z)) =
        (⟨a, ha.1⟩ : ↥(s16h_CycN Mb z)) * ⟨b, hb.1⟩ *
          (⟨a, ha.1⟩ : ↥(s16h_CycN Mb z))⁻¹ *
          (⟨b, hb.1⟩ : ↥(s16h_CycN Mb z))⁻¹ :=
      Subtype.ext (by
        show c = a * b * a⁻¹ * b⁻¹
        rfl)
    rw [e]
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  have h2 : F.rho ⟨ψ⁻¹ * c * ψ, F.conj_inv_mem F.psi_mem hc.1⟩ = 1 := by
    have e : (⟨ψ⁻¹ * c * ψ, F.conj_inv_mem F.psi_mem hc.1⟩ :
        ↥(s16h_CycN Mb z)) =
        (⟨ψ⁻¹ * a * ψ, hpa.1⟩ : ↥(s16h_CycN Mb z)) *
          ⟨ψ⁻¹ * b * ψ, hpb.1⟩ *
          (⟨ψ⁻¹ * a * ψ, hpa.1⟩ : ↥(s16h_CycN Mb z))⁻¹ *
          (⟨ψ⁻¹ * b * ψ, hpb.1⟩ : ↥(s16h_CycN Mb z))⁻¹ :=
      Subtype.ext (by
        show ψ⁻¹ * c * ψ =
          (ψ⁻¹ * a * ψ) * (ψ⁻¹ * b * ψ) * (ψ⁻¹ * a * ψ)⁻¹ * (ψ⁻¹ * b * ψ)⁻¹
        rw [show c = a * b * a⁻¹ * b⁻¹ from rfl]
        group)
    rw [e]
    simp only [map_mul, map_inv]
    rw [hcommψ]
    group
  have hc1 : c = 1 := F.eq_one_of_rho_eq_one hc.1 h1 h2
  calc a * b = (a⁻¹ * b⁻¹)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        simpa [c, mul_assoc] using hc1
    _ = b * a := by group

end s16h_CycFrame

theorem s16h_e3_CycTwoCoreA_isElemAbelian (F : s16h_CycFrame Mb ψ z U)
    {D : Subgroup (MulAut ↥U)} (hD : IsElemAbelian 3 D) : IsElemAbelian 3 (F.core D) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · exact s16h_CycFrame.s16h_e3_CycTwoCoreA_comm F hD a.2 b.2
  · intro x hx
    exact s16h_CycFrame.s16h_e3_CycTwoCoreA_pow_three F hD hx

theorem s16h_e3_CycTwoCoreA_mem_of_three (F : s16h_CycFrame Mb ψ z U)
    {D : Subgroup (MulAut ↥U)}
    (hD : ∀ a ∈ autSub (s16h_CycN Mb z) U, (∃ k : ℕ, orderOf a = 3 ^ k) → a ∈ D)
    {n : MulAut X} (hn : n ∈ s16h_CycN Mb z) (h3 : ∃ k : ℕ, orderOf n = 3 ^ k) :
    n ∈ F.core D := by
  refine ⟨hn, fun m hm _ => ?_⟩
  have hconjN : m⁻¹ * n * m ∈ s16h_CycN Mb z := F.conj_inv_mem hm hn
  obtain ⟨k, hk⟩ := h3
  have hord : orderOf (m⁻¹ * n * m) = 3 ^ k := by
    have hsem : SemiconjBy m⁻¹ n (m⁻¹ * n * m) := by
      show m⁻¹ * n = (m⁻¹ * n * m) * m⁻¹
      group
    rw [← SemiconjBy.orderOf_eq m⁻¹ hsem, hk]
  have hb : F.rho ⟨m⁻¹ * n * m, hconjN⟩ ∈ autSub (s16h_CycN Mb z) U := by
    rw [← F.rho_range]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hb3 : ∃ j : ℕ, orderOf (F.rho ⟨m⁻¹ * n * m, hconjN⟩) = 3 ^ j := by
    have hdvd : orderOf (F.rho ⟨m⁻¹ * n * m, hconjN⟩) ∣ 3 ^ k := by
      simpa [hord] using orderOf_map_dvd F.rho ⟨m⁻¹ * n * m, hconjN⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact ⟨j, hj⟩
  exact hD _ hb hb3

theorem s16h_e3_CycTwoCoreA_le_autSub [Finite X] [Finite (MulAut X)]
    (F : s16h_CycFrame Mb ψ z U) {D : Subgroup (MulAut ↥U)}
    (hDA : D ≤ autSub (s16h_CycN Mb z) U) (hD : IsElemAbelian 3 D)
    (hSyl : ∀ a ∈ autSub (s16h_CycN Mb z) U, (∃ k : ℕ, orderOf a = 3 ^ k) → a ∈ D) :
    D ≤ autSub (F.core D) U := by
  intro d hd
  have hdA : d ∈ autSub (s16h_CycN Mb z) U := hDA hd
  rw [← F.rho_range] at hdA
  obtain ⟨n₀, hn₀⟩ := MonoidHom.mem_range.1 hdA
  by_cases hd1 : d = 1
  · refine mem_autSub.mpr ⟨1, (F.core D).one_mem, ?_⟩
    rw [map_one, hd1]
  · have hd3 : d ^ 3 = 1 := hD.2 d hd
    have hdord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
    obtain ⟨e, m, hm3, hord⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (ne_of_gt (orderOf_pos (n₀ : MulAut X))) 3
        (by norm_num)
    have hm3mod : m % 3 = 1 ∨ m % 3 = 2 := by
      have hlt : m % 3 < 3 := Nat.mod_lt m (by norm_num)
      have hne : m % 3 ≠ 0 := fun h => hm3 (Nat.dvd_iff_mod_eq_zero.mpr h)
      omega
    have hmul3 : m * m % 3 = 1 := by
      rcases hm3mod with h | h <;> rw [Nat.mul_mod, h] <;> norm_num
    let n : MulAut X := (n₀ : MulAut X) ^ (m * m)
    have hN : n ∈ s16h_CycN Mb z := (s16h_CycN Mb z).pow_mem n₀.2 (m * m)
    have h3n : ∃ k : ℕ, orderOf n = 3 ^ k := by
      have h3pow : n ^ (3 ^ e) = 1 := by
        show ((n₀ : MulAut X) ^ (m * m)) ^ (3 ^ e) = 1
        rw [← pow_mul]
        have hmul : m * m * 3 ^ e = 3 ^ e * m * m := by ring
        rw [hmul, pow_mul]
        have ho : (n₀ : MulAut X) ^ (3 ^ e * m) = 1 := by
          rw [← hord]
          exact pow_orderOf_eq_one _
        rw [ho, one_pow]
      have hdvd : orderOf n ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one h3pow
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
      exact ⟨j, hj⟩
    have hcore : n ∈ F.core D := s16h_e3_CycTwoCoreA_mem_of_three F hSyl hN h3n
    refine mem_autSub.mpr ⟨⟨n, F.stab hcore.1⟩, hcore, ?_⟩
    have hr : resHom U ⟨n, F.stab hcore.1⟩ = F.rho ⟨n, hcore.1⟩ := rfl
    rw [hr]
    have hpow : F.rho ⟨n, hcore.1⟩ = d := by
      have e' : (⟨n, hcore.1⟩ : ↥(s16h_CycN Mb z)) = n₀ ^ (m * m) := by
        apply Subtype.ext
        show (n : MulAut X) = ((n₀ : MulAut X)) ^ (m * m)
        rfl
      rw [e', map_pow, hn₀]
      rw [← pow_mod_orderOf d (m * m), hdord, hmul3, pow_one]
    exact hpow

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
