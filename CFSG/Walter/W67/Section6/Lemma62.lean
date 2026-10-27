module

public import CFSG.Walter.W67.Section6.Std62
public import CFSG.Walter.W67.Section6.Core62M
public import CFSG.Walter.W67.Section6.Prop66
public import CFSG.Walter.W67.Section4.Prop41C

public section

namespace CFSG.Walter.W67

open Sec6

namespace Sec6

variable {G : Type} [Group G] [Finite G] (s : Std G)

theorem isCyclic_of_le_E
    {P : Subgroup G} (hPE : P ≤ s.fr.E) : IsCyclic P := by
  have e := Subgroup.subgroupOfEquivOfLe hPE
  have : IsCyclic (P.subgroupOf s.fr.E) := by
    have := isCyclic_E s
    infer_instance
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

end Sec6

theorem lemma_6_2_of
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) : S_lemma_6_2 := by
  intro G _ _ s hJ hR r _ hrσ P₀ hP₀E hP₀r hP₀f hns P hPN hPr hPf hPE hPJ hcyc
  have hrp : r.Prime := Fact.out
  have hrE : r ∣ Nat.card s.fr.E := ((mem_sigma_iff s).mp hrσ).2
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr s.fr.odd_card_E) (even_iff_two_dvd.mpr hrE)
  have hr3' : r ≠ 3 := by
    rintro rfl
    exact not_three_dvd_card_E s h41 h56 hJ hR hrE
  have hr3 : 3 ≤ r := by
    have := hrp.two_le
    omega
  have hP₀c : Nat.card P₀ = r ^ (Nat.card s.fr.E).factorization r := by
    obtain ⟨k, hk⟩ := hP₀r.exists_card_eq
    have h1 : (Nat.card P₀).factorization r = k := by
      rw [hk, hrp.factorization_pow, Finsupp.single_eq_same]
    rw [← hP₀f, h1, hk]
  obtain ⟨x₀, hx₀, hxo, hX⟩ := exists_omega1 s hrσ hP₀E hP₀c
  rw [hX] at hns hPN hPf hcyc
  have hXE : Subgroup.zpowers x₀ ≤ s.fr.E := by
    rw [Subgroup.zpowers_le]
    exact hP₀E hx₀
  have hX1 : Subgroup.zpowers x₀ ≠ ⊥ := by
    intro h
    have := Nat.card_zpowers x₀
    rw [h, Subgroup.card_bot, hxo] at this
    exact hrp.one_lt.ne this
  obtain ⟨P₀', P₁, hP₀'E, hP₀'c, hP₁L, hP₁c, hEP₁, hdata, -, hPL', -, hPcard'⟩ :=
    exists_P s h41 h56 hJ hR hrσ hXE hX1 hns
  have hP₀' : P₀' = P₀ := eq_of_le_cyclic (isCyclic_E s) hP₀'E hP₀E (by rw [hP₀'c, hP₀c])
  rw [hP₀'] at hPL' hPcard'
  set M := Subgroup.normalizer ((Subgroup.zpowers x₀ : Subgroup G) : Set G) with hM
  have hP'M : P₀ ⊔ P₁ ≤ M := by
    rw [hM, normalizer_eq s hXE hX1]
    exact sup_le (hP₀E.trans le_sup_right) (hP₁L.trans le_sup_left)
  have hPc : Nat.card P = r ^ (Nat.card M).factorization r := by
    obtain ⟨k, hk⟩ := hPr.exists_card_eq
    have h1 : (Nat.card P).factorization r = k := by
      rw [hk, hrp.factorization_pow, Finsupp.single_eq_same]
    rw [← hPf, h1, hk]
  obtain ⟨g, hgM, hgP⟩ := exists_conj_of_sylowIn hP'M hPN hPcard' hPc
  have hgL := normalizer_le_normalizer_L s hXE hX1 hgM
  have hPL : P ⊓ s.L (Subgroup.zpowers x₀) = cj g P₁ := by
    rw [hgP, ← cj_eq_self_of_mem_normalizer hgL, ← cj_inf, hPL']
  have hP₁cyc : IsCyclic P₁ := by
    have h1 : IsCyclic (cj g P₁) := hPL ▸ hcyc
    have := isCyclic_cj (g := g⁻¹) h1
    rwa [cj_inv_cj] at this
  obtain ⟨g₀, -, hg₀⟩ := exists_generator s
  have hMpow : ∀ m ∈ M, m ^ Nat.card P₀ ∈
      s.L (Subgroup.zpowers x₀) ⊔ Subgroup.zpowers (g₀ ^ Nat.card P₀) := by
    intro m hm
    rw [hM, normalizer_eq s hXE hX1, sup_comm, ← hg₀] at hm
    exact pow_mem_sup_zpowers (hg₀ ▸ E_le_normalizer_L s hXE hX1) hm _
  have hP₀M₁ := inf_M₁ s h41 h56 hJ hR hP₀E hP₀c hXE hX1 hg₀
  by_cases hP₁ : P₁ = ⊥
  · rw [hP₁, sup_bot_eq] at hPcard'
    exact false_of_sylow_P₀ s.perfect hr3 (isCyclic_of_le_E s hP₀E) hP₀r hx₀ hxo rfl
      hPcard' hMpow hP₀M₁
  obtain ⟨C, W, hD, hEW⟩ := hdata hP₁
  have hP₁r : IsPGroup r P₁ := IsPGroup.of_card hP₁c
  obtain ⟨y₀, hy₀, hyo⟩ := exists_orderOf_eq_of_ne_bot hP₁r hP₁
  have hy₀1 : y₀ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hyo
    exact hrp.one_lt.ne hyo
  obtain ⟨q₀, hq₀p, hq₀W, hq₀odd, hq₀r⟩ : ∃ q₀ : ℕ, q₀.Prime ∧ q₀ ∣ Nat.card W ∧ Odd q₀ ∧
      q₀ ≠ r := by
    rcases hD.W_card with h6 | ⟨-, h11, h10⟩
    · exact ⟨3, Nat.prime_three, by rw [h6]; norm_num, by decide, fun h3 => hr3' h3.symm⟩
    · refine ⟨5, by norm_num, by rw [h10]; norm_num, by decide, by omega⟩
  have : Fact q₀.Prime := ⟨hq₀p⟩
  obtain ⟨⟨d, hdW⟩, hdo⟩ := exists_prime_orderOf_dvd_card' (G := W) q₀ hq₀W
  rw [Subgroup.orderOf_mk] at hdo
  have hWN := hD.W_le_N
  have hdL : d ∈ s.L (Subgroup.zpowers x₀) := (Subgroup.mem_inf.mp (hWN hdW)).1
  have hJW := hD.J_mem
  have hJL : s.J ∈ s.L (Subgroup.zpowers x₀) := (Subgroup.mem_inf.mp (hWN hJW)).1
  have hCinv : ∀ c ∈ C, s.J * c * s.J⁻¹ = c⁻¹ := by
    apply inv_of_fixedPointFree s.J_mul_J (hD.C_norm (hWN hJW))
    intro c hc hcJ
    by_contra hc1
    have hJC : s.J ∈ C := by
      rw [← hD.C_cent c hc hc1]
      refine Subgroup.mem_inf.mpr ⟨hJL, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc s.J * c = s.J * c * s.J⁻¹ * s.J := by group
        _ = c * s.J := by rw [hcJ]
    have : s.J ∈ C ⊓ W := Subgroup.mem_inf.mpr ⟨hJC, hJW⟩
    rw [hD.CW_inf, Subgroup.mem_bot] at this
    have h2 := s.orderOf_J
    rw [this, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hx₀X : x₀ ∈ Subgroup.zpowers x₀ := Subgroup.mem_zpowers x₀
  refine Hyp62.elim (r := r) (J := s.J) (d := d) (x₀ := x₀) (y₀ := y₀) (P₀ := P₀) (P₁ := P₁)
    (M := M) (M₁ := s.L (Subgroup.zpowers x₀) ⊔ Subgroup.zpowers (g₀ ^ Nat.card P₀))
    (H₃ := Subgroup.zpowers s.J ⊔ s.K ⊔ Subgroup.zpowers (g₀ ^ Nat.card P₀))
    { r_ne_two := hr2
      perfect := s.perfect
      orderOf_J := s.orderOf_J
      P₀_cyc := isCyclic_of_le_E s hP₀E
      P₀_r := hP₀r
      x₀_mem := hx₀
      orderOf_x₀ := hxo
      P₀_le := hP₀E.trans s.fr.E_le_H
      normalizer_X := rfl
      M_le := by
        rw [hM, normalizer_eq s hXE hX1]
        refine sup_le ((L_le_centralizer s hXE hX1).trans
          (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx₀X))) ?_
        intro e he
        exact Subgroup.mem_centralizer_singleton_iff.mpr (E_comm s e he x₀ (hP₀E hx₀))
      P₁_cyc := hP₁cyc
      P₁_r := hP₁r
      y₀_mem := hy₀
      orderOf_y₀ := hyo
      P₁_inv := fun y hy => hCinv y (hD.P_le_C hy)
      P₀_le_N := hP₀E.trans hEP₁
      P₁_le_M := hP₁L.trans (L_le_normalizer s hXE hX1)
      P_card := hPcard'
      d_P₀ := Subgroup.mem_centralizer_iff.mpr fun a ha =>
        (Subgroup.mem_centralizer_iff.mp (hEW (hP₀E ha)) d hdW).symm
      d_P₁ := (Subgroup.mem_inf.mp (hWN hdW)).2
      d_y₀ := by
        intro hdy
        have hdC : d ∈ C := by
          rw [← hD.C_cent y₀ (hD.P_le_C hy₀) hy₀1]
          refine Subgroup.mem_inf.mpr ⟨hdL, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
          calc d * y₀ = d * y₀ * d⁻¹ * d := by group
            _ = y₀ * d := by rw [hdy]
        have : d ∈ C ⊓ W := Subgroup.mem_inf.mpr ⟨hdC, hdW⟩
        rw [hD.CW_inf, Subgroup.mem_bot] at this
        rw [this, orderOf_one] at hdo
        exact hq₀p.one_lt.ne hdo
      d_odd := by rw [hdo]; exact hq₀odd
      M_pow := hMpow
      P₀_M₁ := hP₀M₁
      H_pow := fun x hx => pow_mem_H₃ s hg₀ _ hx
      P₀_H₃ := inf_H₃ s hP₀E hP₀c hg₀
      H_card := by
        have h1 := s.factorization_card_H hrp hr2
        rw [Nat.factorization_eq_zero_of_not_dvd (not_dvd_card_K s h41 h56 hJ hR hrσ), zero_add,
          ← hP₀f] at h1
        exact h1
      two_comm := fun T hT a ha b hb => (two_facts s hT ha hb).1
      two_sq := fun T hT a ha => (two_facts s hT ha ha).2
      no_real := no_real s h41 h56 hJ hR hrσ
      CP := by
        intro t ht ht2
        have htx : t * x₀ = x₀ * t :=
          (Subgroup.mem_centralizer_iff.mp ht x₀ (Subgroup.mem_sup_left hx₀)).symm
        have htN : t ∈ Subgroup.normalizer ((Subgroup.zpowers x₀ : Subgroup G) : Set G) := by
          apply Subgroup.centralizer_le_normalizer
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
          exact (Commute.zpow_left (show Commute x₀ t from htx.symm) k).eq
        have htL := mem_L_of_mul_self s h41 h56 hJ hR hXE hX1 htN ht2
        have hty : t * y₀ = y₀ * t :=
          (Subgroup.mem_centralizer_iff.mp ht y₀ (Subgroup.mem_sup_right hy₀)).symm
        have htC : t ∈ C := by
          rw [← hD.C_cent y₀ (hD.P_le_C hy₀) hy₀1]
          exact Subgroup.mem_inf.mpr ⟨htL, Subgroup.mem_centralizer_singleton_iff.mpr hty⟩
        have hodd : Odd (orderOf t) := hD.odd_card_C.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ htC)
        have hd : orderOf t ∣ Nat.gcd 2 (orderOf t) :=
          Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht2)) dvd_rfl
        rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd), Nat.dvd_one,
          orderOf_eq_one_iff] at hd
        exact hd }

end CFSG.Walter.W67
