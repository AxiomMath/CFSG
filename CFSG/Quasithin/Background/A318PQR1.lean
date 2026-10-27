module

public import CFSG.Sporadic.Schreier.J4SOuter
public import CFSG.Quasithin.Background.A318PQuotes

public section

namespace CFSG.Quasithin

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4 CFSG.LocalAnalysis.ComponentInitial MulAction
open CFSG.ComponentClassification.OuterAutomorphisms

section Kernel3

variable {G : Type*} [Group G] [Finite G] {X : Type*} [MulAction G X] [Finite X]
  [IsPretransitive G X] {H N K : Subgroup G} {r : X}

theorem pointwise_kernel_element_trivial_three (hstab : stabilizer G r = H) (hcoatom : IsCoatom H)
    (hNH : N ≤ H) (hKH : K ≤ H) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hNK : N ⊓ K = ⊥)
    (hprod : ∀ h ∈ H, ∃ n ∈ N, ∃ k ∈ K, h = n * k) (hN2 : IsPGroup 2 N)
    (hcardN : Nat.card N = 2048) (hcardH : Nat.card H = 501397585920)
    (horb : ∃ x₀ : X, (orbit H x₀).ncard = 28336 ∧
      ∀ x : X, (orbit H x).ncard = 28336 → orbit H x = orbit H x₀)
    (h3 : ∀ k ∈ K, orderOf k = 3 → Nat.card (Subgroup.centralizer {k} ⊓ N : Subgroup G) ≤ 32)
    {α : MulAut G} (hα : α ∈ pointwiseFixingAut H) (hα3 : α ^ 3 = 1) : α = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hα1
  obtain ⟨x₀, hx₀, hu⟩ := horb
  have hd1 : (orbit H x₀).ncard ≠ 1 := by rw [hx₀]; norm_num
  obtain ⟨g, h, hh, ho, hc, hcard⟩ := exists_centralizing_element hstab hcoatom hα hα1 hα3
    (fun x hx => hu x (hx.trans hx₀)) (by rw [hx₀]; norm_num) hd1
  rw [hx₀, hcardH] at hcard
  obtain ⟨n, hn, k, hk, rfl⟩ := hprod h hh
  have hok : orderOf k = 3 := orderOf_part hKH hnorm hNK hN2 (by norm_num) hn hk ho
  have hle : (N ⊓ Dg H g : Subgroup G) ≤ Subgroup.centralizer {k} ⊓ N := by
    intro m hm
    rw [Subgroup.mem_inf] at hm
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hm.1⟩
    exact (commute_part_of_mem hKH hnorm hcomm hn hk hm.1 (hc m hm.2)).eq.symm
  have hcardle := (Subgroup.card_le_of_le hle).trans (h3 k hk hok)
  have h1 := card_mul_card_dvd hNH (Dg_le g) hnorm
  rw [hcardN, hcardH] at h1
  have hpos : 0 < Nat.card (Dg H g) := Nat.card_pos
  have h2 : 2048 ∣ Nat.card (N ⊓ Dg H g : Subgroup G) * 28336 := by
    refine Nat.dvd_of_mul_dvd_mul_left hpos ?_
    rw [show Nat.card (Dg H g) * (Nat.card (N ⊓ Dg H g : Subgroup G) * 28336) =
        Nat.card (N ⊓ Dg H g : Subgroup G) * (Nat.card (Dg H g) * 28336) by ring, hcard]
    rw [mul_comm (Nat.card (Dg H g)) 2048]
    exact h1
  have h4 : Nat.card (N ⊓ Dg H g : Subgroup G) ∣ 2048 := by
    rw [← hcardN]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hpos' : 0 < Nat.card (N ⊓ Dg H g : Subgroup G) := Nat.card_pos
  have hm : Nat.card (N ⊓ Dg H g : Subgroup G) ≤ 32 := hcardle
  generalize Nat.card (N ⊓ Dg H g : Subgroup G) = m at hpos' hm h2 h4
  omega

end Kernel3

@[expose] def J4OrderThreeCentralizerBound : Prop :=
  ∀ k : J, k ∈ K → orderOf k = 3 → Nat.card (Subgroup.centralizer {k} ⊓ N : Subgroup J) ≤ 32

theorem not_dvd_card_outer_J_three
    (h3 : J4OrderThreeCentralizerBound) : ¬ 3 ∣ Nat.card (Outer J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCp : ¬ 3 ∣ Nat.card (pointwiseFixingAut H) := by
    intro h
    obtain ⟨β, hβ⟩ := exists_prime_orderOf_dvd_card' (G := pointwiseFixingAut H) 3 h
    have hβ3 : (β : MulAut J) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← hβ, pow_orderOf_eq_one, Subgroup.coe_one]
    have h1 : (β : MulAut J) = 1 :=
      pointwise_kernel_element_trivial_three stabilizer_root H_isCoatom N_le_H K_le_H
        conj_mem_N_of_mem_H N_comm (by rw [inf_comm, K_inf_N]) (fun _ hh => exists_mul_of_mem_H hh)
        isPGroup_N (by rw [card_N]; norm_num) card_H (horb_J 28336 (by simp)) h3 β.2 hβ3
    have h2 : β = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hβ
    omega
  exact not_dvd_card_outer_of_sylow_bound (by omega : 3 ≠ 2) S0Sylow N H
    (by rw [S0Sylow_coe]; exact N_le_S0) (by rw [S0Sylow_coe]; exact S0_le_H) isPGroup_N
    normalizer_N QT_unique_J4_local_normal_module_irreducible.2.2.2.2.2.2.2.2.2.le hCp
    (R3E_J4_Sylow_two_automorphism_group_is_two_group S0Sylow).2

theorem qSporOutTwo_of_orderThreeCentralizerBound
    (h3 : J4OrderThreeCentralizerBound) : QSporOutTwo := by
  have hcard := @card_outer_congr (CFSG.Blueprint.NativeSporadic.Carrier .J4) J _ (Subgroup.toGroup J)
    (seedEquiv j4Facts.mat)
  unfold QSporOutTwo
  rw [hcard]
  exact not_dvd_card_outer_J_three h3

end CFSG.Quasithin
