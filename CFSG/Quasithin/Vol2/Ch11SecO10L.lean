module

public import CFSG.Quasithin.Vol2.Ch11SecA15R1b
public import CFSG.Quasithin.Vol2.Ch11SecD551B
public import CFSG.Quasithin.Vol2.Ch11SecE42SL2

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 SecE

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem mem_normalizer_V₁ (hF15 : SecA.Facts15) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) {x : G} (hxV : x ∈ Subgroup.normalizer (fsuV T I : Set G))
    (hxR : x ∈ Subgroup.normalizer (ROf T L V₁ : Set G)) :
    x ∈ Subgroup.normalizer (V₁ : Set G) := by
  have hle := SecA.IsVi.le_fsuV hV₁
  have hfix : ∀ r ∈ ROf T L V₁, ∀ u ∈ V₁, r * u * r⁻¹ = u := by
    intro r hr u hu
    have h1 := SecA.ROf_act_V1 hF15 h1102 h hV₁ hr hu
    have hrV : r ∈ Subgroup.normalizer (fsuV T I : Set G) :=
      SecA.T_le_normalizer_fsuV T I (SecD.ROf_le_T h V₁ hr)
    have h2 : r * u * r⁻¹ * u⁻¹ ∈ fsuV T I :=
      (fsuV T I).mul_mem ((Subgroup.mem_normalizer_iff.mp hrV u).mp (hle hu))
        ((fsuV T I).inv_mem (hle hu))
    have h3 : r * u * r⁻¹ * u⁻¹ ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) := ⟨h2, h1⟩
    rwa [hcV, Subgroup.mem_bot, mul_inv_eq_one] at h3
  have key : ∀ y ∈ Subgroup.normalizer (fsuV T I : Set G),
      y ∈ Subgroup.normalizer (ROf T L V₁ : Set G) → ∀ u ∈ V₁, y * u * y⁻¹ ∈ V₁ := by
    intro y hyV hyR u hu
    refine SecA.mem_V1_of_fixed hF15 h1102 h hV₁
      ((Subgroup.mem_normalizer_iff.mp hyV u).mp (hle hu)) fun r hr => ?_
    have hr' : y⁻¹ * r * y ∈ ROf T L V₁ := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyR) r).mp hr
    have e := hfix _ hr' u hu
    calc r * (y * u * y⁻¹) * r⁻¹ = y * ((y⁻¹ * r * y) * u * (y⁻¹ * r * y)⁻¹) * y⁻¹ := by group
      _ = y * u * y⁻¹ := by rw [e]
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key x hxV hxR u, fun hu => ?_⟩
  simpa [mul_assoc] using key x⁻¹ (Subgroup.inv_mem _ hxV) (Subgroup.inv_mem _ hxR) _ hu

theorem mem_normalizer_fsuV_of_TI (h1103 : Stmt11_0_3) (h : Hyp11 G T L I n) {z : G}
    (hzV : z ∈ fsuV T I) (hz1 : z ≠ 1) {x : G} (hxM : x ∈ Subgroup.normalizer (L : Set G))
    (hxz : x ∈ Subgroup.centralizer ({z} : Set G)) :
    x ∈ Subgroup.normalizer (fsuV T I : Set G) := by
  obtain ⟨-, -, -, hTI, -⟩ := h1103 G T L I n h
  by_contra hx
  have hz : z ∈ fsuV T I ⊓ conjSubgroup (fsuV T I) x := by
    refine ⟨hzV, CFSG.Quasithin.mem_conjSubgroup_iff.mpr ?_⟩
    rwa [Subgroup.mem_centralizer_singleton_iff.mp hxz, mul_inv_cancel_right]
  rw [hTI.2 x hxM hx] at hz
  exact hz1 (Subgroup.mem_bot.mp hz)

theorem even_of_three_dvd {n : ℕ} (h3 : 3 ∣ 2 ^ n - 1) : Even n := by
  rcases Nat.even_or_odd n with he | ⟨k, rfl⟩
  · exact he
  · exfalso
    have e1 : (2 : ℕ) ^ (2 * k + 1) = 2 * 4 ^ k := by rw [pow_succ, pow_mul]; ring
    have e2 : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    have e3 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
    rw [e1] at h3
    omega

theorem mem_L_of_prime (h1102 : Stmt11_0_2) (h1104 : Stmt11_0_4) (h : Hyp11 G T L I n) {x : G}
    (hxM : x ∈ Subgroup.normalizer (L : Set G)) (hxV : x ∈ Subgroup.normalizer (fsuV T I : Set G))
    (hp : (orderOf x).Prime) (hpd : orderOf x ∣ 2 ^ n - 1) : x ∈ L := by
  obtain ⟨h1, h2⟩ := h1104 G T L I n h
  have hmem : x ∈ CFSG.Quasithin.oPrimeResidualOf (orderOf x)
      (Subgroup.normalizer (L : Set G)) := by
    unfold CFSG.Quasithin.oPrimeResidualOf
    exact Subgroup.subset_closure ⟨hxM, 1, (pow_one _).symm⟩
  have hpd2 : orderOf x ∣ 2 ^ (2 * n) - 1 := by
    refine hpd.trans ?_
    have := Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2
    rwa [one_pow, ← pow_mul, mul_comm] at this
  rcases SecA.kind_cases h1102 h with hk | hk | hk
  · by_cases h3 : 3 < orderOf x
    · rwa [h1 _ hp (Or.inr ⟨hk, hpd, h3⟩)] at hmem
    · have hn : 1 ≤ n := by have := h.one_lt; omega
      have hp2 : orderOf x ≠ 2 := by
        intro e
        rw [e] at hpd
        obtain ⟨c, hc⟩ := hpd
        obtain ⟨d, hd⟩ : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
        have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
      have hp3 : orderOf x = 3 := by have := hp.two_le; omega
      rw [hp3] at hpd
      exact h2 hk (even_of_three_dvd hpd) x hxM hp3 (Or.inl hxV)
  · rwa [h1 _ hp (Or.inl ⟨Or.inl hk, hpd2⟩)] at hmem
  · rwa [h1 _ hp (Or.inl ⟨Or.inr hk, hpd2⟩)] at hmem

end CFSG.Quasithin.Vol2.Ch11.O10
