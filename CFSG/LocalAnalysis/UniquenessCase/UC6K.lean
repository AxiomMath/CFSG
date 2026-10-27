module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open

theorem no_pgroup_quotient_of_generated_by_r_elements {Kg : Type} [Group Kg] [Finite Kg] {r : ℕ}
    (hr : r.Prime) {S : Set Kg} (hS : closure S = ⊤) (hSr : ∀ s ∈ S, s ^ r = 1)
    (hsimple : IsSimpleGroup (Kg ⧸ CFSG.pPrimeCore r Kg))
    (hnab : ∃ a b : Kg ⧸ CFSG.pPrimeCore r Kg, a * b ≠ b * a)
    {q : ℕ} (hq : q.Prime) (N : Subgroup Kg) [N.Normal] (hN : IsPGroup q (Kg ⧸ N)) : N = ⊤ := by
  classical
  by_cases hqr : q = r
  · subst hqr
    haveI : Fact q.Prime := ⟨hq⟩
    have hU : CFSG.pPrimeCore q Kg ≤ N := by
      intro u hu
      obtain ⟨n, hn⟩ := hN (u : Kg ⧸ N)
      have hcop : Nat.Coprime q (Nat.card (CFSG.pPrimeCore q Kg)) := CFSG.pPrimeCore_coprime_card
      have hord : orderOf (⟨u, hu⟩ : CFSG.pPrimeCore q Kg) ∣ Nat.card (CFSG.pPrimeCore q Kg) :=
        orderOf_dvd_natCard _
      have hord' : Nat.Coprime q (orderOf u) := by
        have := Nat.Coprime.coprime_dvd_right (by simpa using hord) hcop
        simpa using this
      have h1 : orderOf (u : Kg ⧸ N) ∣ orderOf u := orderOf_map_dvd (QuotientGroup.mk' N) u
      have h2 : orderOf (u : Kg ⧸ N) ∣ q ^ n := orderOf_dvd_of_pow_eq_one (by simpa using hn)
      have h3 : Nat.Coprime (q ^ n) (orderOf u) := Nat.Coprime.pow_left n hord'
      have h4 : orderOf (u : Kg ⧸ N) = 1 :=
        Nat.eq_one_of_dvd_coprimes h3 h2 h1
      have h5 : (u : Kg ⧸ N) = 1 := orderOf_eq_one_iff.1 h4
      exact (QuotientGroup.eq_one_iff u).1 h5
    haveI hUn : (CFSG.pPrimeCore q Kg).Normal := CFSG.pPrimeCore_normal
    set N' : Subgroup (Kg ⧸ CFSG.pPrimeCore q Kg) := N.map (QuotientGroup.mk' (CFSG.pPrimeCore q Kg))
      with hN'
    haveI : N'.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases hsimple.eq_bot_or_eq_top_of_normal N' with h | h
    ·
      exfalso
      have hNU : N ≤ CFSG.pPrimeCore q Kg := by
        intro x hx
        have : (x : Kg ⧸ CFSG.pPrimeCore q Kg) ∈ N' := ⟨x, hx, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff x).1 this
      have hNeq : N = CFSG.pPrimeCore q Kg := le_antisymm hNU hU
      subst hNeq
      haveI : Nontrivial (Kg ⧸ CFSG.pPrimeCore q Kg) := hsimple.toNontrivial
      have hc := hN.center_nontrivial
      rcases hsimple.eq_bot_or_eq_top_of_normal
          (Subgroup.center (Kg ⧸ CFSG.pPrimeCore q Kg)) with hb | ht
      · exact (Subgroup.nontrivial_iff_ne_bot _).1 hc hb
      · obtain ⟨a, b, hab⟩ := hnab
        have : a ∈ Subgroup.center (Kg ⧸ CFSG.pPrimeCore q Kg) := by
          rw [ht]; exact Subgroup.mem_top a
        exact hab (Subgroup.mem_center_iff.1 this b).symm
    ·
      rw [eq_top_iff]
      intro x _
      have : (x : Kg ⧸ CFSG.pPrimeCore q Kg) ∈ N' := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := this
      have : n⁻¹ * x ∈ CFSG.pPrimeCore q Kg := by
        rw [← QuotientGroup.eq]
        exact hnx
      have hx := hU this
      simpa using N.mul_mem hn hx
  ·
    rw [eq_top_iff, ← hS, Subgroup.closure_le]
    intro s hs
    obtain ⟨n, hn⟩ := hN (s : Kg ⧸ N)
    have h1 : orderOf (s : Kg ⧸ N) ∣ r := orderOf_dvd_of_pow_eq_one (by
      rw [← QuotientGroup.mk_pow, hSr s hs]; simp)
    have h2 : orderOf (s : Kg ⧸ N) ∣ q ^ n := orderOf_dvd_of_pow_eq_one hn
    have hcop : Nat.Coprime (q ^ n) r :=
      Nat.Coprime.pow_left n ((Nat.coprime_primes hq hr).2 hqr)
    have h3 : orderOf (s : Kg ⧸ N) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
    exact (QuotientGroup.eq_one_iff s).1 (orderOf_eq_one_iff.1 h3)

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem hr : m.r.Prime := m.d.prime

theorem Z_le_K : m.Z ≤ m.K := fun z hz =>
  subset_closure ⟨1, m.M.one_mem, z, hz, by simp⟩

theorem Z_le_M : m.Z ≤ m.M := fun z hz => m.R_le_M (m.hZ.le hz)

theorem K_le_M : m.K ≤ m.M := by
  refine (closure_le _).2 ?_
  rintro _ ⟨g, hg, z, hz, rfl⟩
  exact m.M.mul_mem (m.M.mul_mem hg (m.Z_le_M hz)) (m.M.inv_mem hg)

theorem card_Z : Nat.card m.Z = m.r := m.hZ.card

theorem pow_r_eq_one_of_mem {x : G} (hx : x ∈ {x | ∃ g ∈ m.M, ∃ z ∈ m.Z, x = g * z * g⁻¹}) :
    x ^ m.r = 1 := by
  obtain ⟨g, -, z, hz, rfl⟩ := hx
  have h1 : (⟨z, hz⟩ : m.Z) ^ Nat.card m.Z = 1 := pow_card_eq_one'
  have h2 : z ^ m.r = 1 := by
    have := congrArg Subtype.val h1
    rw [m.card_Z] at this
    simpa using this
  rw [conj_pow, h2]
  simp

theorem K_no_pgroup_quotient (h629 : m.C629) {q : ℕ} (hq : q.Prime) (N : Subgroup ↥m.K)
    [N.Normal] (hN : IsPGroup q (↥m.K ⧸ N)) : N = ⊤ := by
  refine no_pgroup_quotient_of_generated_by_r_elements m.hr (S := (((↑) : m.K → G)) ⁻¹'
    {x | ∃ g ∈ m.M, ∃ z ∈ m.Z, x = g * z * g⁻¹}) ?_ ?_ h629.1 h629.2 hq N hN
  · exact Subgroup.closure_closure_coe_preimage
  · intro s hs
    apply Subtype.ext
    simpa using m.pow_r_eq_one_of_mem hs

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
