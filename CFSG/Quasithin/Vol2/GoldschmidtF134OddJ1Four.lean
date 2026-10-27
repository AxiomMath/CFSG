module

public import CFSG.Walter.J1Props.Janko

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Walter.J1 CFSG.Walter.J1Props Subgroup

section Action

theorem conj_eq_or_inv_of_normalizes_zpowers {G : Type*} [Group G] {y u : G} {p : ℕ}
    (hp : p.Prime) (hy : orderOf y = p) (hu : u * u = 1) (hN : u * y * u⁻¹ ∈ zpowers y) :
    u * y * u⁻¹ = y ∨ u * y * u⁻¹ = y⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hN
  have h1 : y ^ (k * k) = y := by
    have h0 : u * (u * y * u⁻¹) * u⁻¹ = y := by
      calc u * (u * y * u⁻¹) * u⁻¹ = (u * u) * y * (u * u)⁻¹ := by group
        _ = y := by rw [hu]; group
    have h2 : u * y ^ k * u⁻¹ = (u * y * u⁻¹) ^ k := conj_zpow.symm
    rw [← hk, h2, ← hk, ← zpow_mul] at h0
    exact h0
  have h3 : y ^ (k * k - 1) = 1 := by rw [zpow_sub_one, h1, mul_inv_cancel]
  have h4 : (p : ℤ) ∣ k * k - 1 := by
    rw [← hy]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h3
  have h5 : (p : ℤ) ∣ (k - 1) * (k + 1) := by
    convert h4 using 1
    ring
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h5 with h | h
  · left
    have h6 : y ^ (k - 1) = 1 := by
      rw [← hy] at h
      exact orderOf_dvd_iff_zpow_eq_one.mp h
    rw [← hk, ← sub_add_cancel k 1, zpow_add_one, h6, one_mul]
  · right
    have h6 : y ^ (k + 1) = 1 := by
      rw [← hy] at h
      exact orderOf_dvd_iff_zpow_eq_one.mp h
    rw [← hk]
    exact eq_inv_of_mul_eq_one_left (by rw [← zpow_add_one]; exact h6)

theorem exists_two_centralizing_of_card_eight {G : Type*} [Group G] [Finite G] {U : Subgroup G}
    (hUc : Nat.card U = 8) (hsq : ∀ u ∈ U, u * u = 1) {y : G} {p : ℕ} (hp : p.Prime)
    (hy : orderOf y = p) (hN : ∀ u ∈ U, u * y * u⁻¹ ∈ zpowers y) :
    ∃ s₁ ∈ U, ∃ s₂ ∈ U, s₁ ≠ 1 ∧ s₂ ≠ 1 ∧ s₁ ≠ s₂ ∧ y * s₁ = s₁ * y ∧ y * s₂ = s₂ * y := by
  set D : Subgroup U := (centralizer ({y} : Set G)).subgroupOf U with hD
  have hconj : ∀ u : G, u * y = y * u ↔ u * y * u⁻¹ = y := fun u => by
    rw [mul_inv_eq_iff_eq_mul]
  have hmemD : ∀ u : U, u ∈ D ↔ (u : G) * y * (u : G)⁻¹ = y := fun u => by
    rw [hD, mem_subgroupOf, mem_centralizer_singleton_iff, hconj]
  have hinvD : ∀ u : U, u ∉ D → (u : G) * y * (u : G)⁻¹ = y⁻¹ := fun u hu =>
    (conj_eq_or_inv_of_normalizes_zpowers hp hy (hsq u u.2) (hN u u.2)).resolve_left
      ((hmemD u).not.mp hu)
  have hD2 : D = ⊤ ∨ D.index = 2 := by
    by_cases htop : D = ⊤
    · exact Or.inl htop
    · right
      obtain ⟨a, ha⟩ : ∃ a : U, a ∉ D := by
        by_contra hcon
        push Not at hcon
        exact htop (eq_top_iff.mpr fun x _ => hcon x)
      refine index_eq_two_iff.mpr ⟨a, fun b => ?_⟩
      by_cases hb : b ∈ D
      · right
        exact ⟨hb, fun hba => ha (by simpa using D.mul_mem (D.inv_mem hb) hba)⟩
      · left
        refine ⟨?_, hb⟩
        rw [hmemD]
        have hb' := hinvD b hb
        have ha' := hinvD a ha
        calc ((b * a : U) : G) * y * ((b * a : U) : G)⁻¹
            = (b : G) * ((a : G) * y * (a : G)⁻¹) * (b : G)⁻¹ := by simp [mul_assoc]
          _ = ((b : G) * y * (b : G)⁻¹)⁻¹ := by rw [ha']; group
          _ = y := by rw [hb', inv_inv]
  have hcard : 4 ≤ Nat.card D := by
    have h := D.card_mul_index
    rw [hUc] at h
    rcases hD2 with htop | h2
    · rw [htop, card_top, hUc]
      norm_num
    · rw [h2] at h
      omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ : ∃ a b c : D, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    have := Fintype.ofFinite D
    exact Fintype.two_lt_card_iff.mp (by rw [← Nat.card_eq_fintype_card]; omega)
  have key : ∃ s t : D, s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t := by
    by_cases ha1 : a = 1
    · exact ⟨b, c, fun h => hab (ha1.trans h.symm), fun h => hac (ha1.trans h.symm), hbc⟩
    · by_cases hb1 : b = 1
      · exact ⟨a, c, ha1, fun h => hbc (hb1.trans h.symm), hac⟩
      · exact ⟨a, b, ha1, hb1, hab⟩
  obtain ⟨s, t, hs1, ht1, hst⟩ := key
  refine ⟨((s : U) : G), (s : U).2, ((t : U) : G), (t : U).2, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hs1 (Subtype.ext (Subtype.ext h))
  · exact fun h => ht1 (Subtype.ext (Subtype.ext h))
  · exact fun h => hst (Subtype.ext (Subtype.ext h))
  · exact ((hconj _).mpr ((hmemD _).mp s.2)).symm
  · exact ((hconj _).mpr ((hmemD _).mp t.2)).symm

end Action

section Janko

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_commute_of_commute (g a b : G) (hab : a * b = b * a) :
    g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹) := by
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [hab]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem not_commute_t_of_prime_ge_five (h : JankoHyp₀ G) {y s : G} {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hy : orderOf y = p) (hs : s * s = 1) (hs1 : s ≠ 1) (hst : s ≠ h.t)
    (hsc : s * h.t = h.t * s) (hyt : y * h.t = h.t * y) (hys : y * s = s * y) : False := by
  have hodd : Odd (orderOf y) := by rw [hy]; exact hp.odd_of_ne_two (by omega)
  have hyF : y ∈ h.F := h.mem_F_of_odd (mem_centralizer_singleton_iff.mpr hyt) hodd
  have key : ∃ f ∈ h.F, f * f = 1 ∧ f ≠ 1 ∧ y * f = f * y := by
    rcases h.mem_centralizer_t.mp (mem_centralizer_singleton_iff.mpr hsc) with hF | hF
    · exact ⟨s, hF, hs, hs1, hys⟩
    · refine ⟨h.t * s, hF, ?_, ?_, ?_⟩
      · calc h.t * s * (h.t * s) = h.t * (s * h.t) * s := by group
          _ = (h.t * h.t) * (s * s) := by rw [hsc]; group
          _ = 1 := by rw [h.t_mul_t, hs, one_mul]
      · intro he
        apply hst
        calc s = h.t⁻¹ * (h.t * s) := by group
          _ = h.t⁻¹ := by rw [he, mul_one]
          _ = h.t := inv_eq_of_mul_eq_one_left h.t_mul_t
      · calc y * (h.t * s) = (y * h.t) * s := by group
          _ = h.t * (y * s) := by rw [hyt]; group
          _ = h.t * s * y := by rw [hys]; group
  obtain ⟨f, hfF, hf2, hf1, hyf⟩ := key
  have hy1 : y ≠ 1 := fun he => by rw [he, orderOf_one] at hy; omega
  have hy5 : y ^ 5 = 1 := by
    rcases A5Sub.pow_three_or_five h.iso hyF hodd with h3 | h5
    · have := Nat.le_of_dvd (by norm_num) (hy ▸ orderOf_dvd_of_pow_eq_one h3)
      omega
    · exact h5
  have hmem := A5Sub.mem_zpowers_of_commute_five h.iso hyF hfF hy5 hy1 hyf
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hmem
  have hf5 : (y ^ k) ^ 5 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy5, one_zpow]
  have hf2' : (y ^ k) ^ 2 = 1 := by rw [sq]; exact hf2
  have hord : orderOf (y ^ k) ∣ Nat.gcd 5 2 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hf5) (orderOf_dvd_of_pow_eq_one hf2')
  rw [show Nat.gcd 5 2 = 1 from rfl, Nat.dvd_one, orderOf_eq_one_iff] at hord
  exact hf1 hord

theorem not_commute_four_of_prime_ge_five (h : JankoHyp₀ G) {y s₁ s₂ : G} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hy : orderOf y = p) (h1 : s₁ * s₁ = 1) (h1' : s₁ ≠ 1)
    (h2 : s₂ * s₂ = 1) (h2' : s₂ ≠ 1) (h12 : s₁ ≠ s₂) (hc : s₁ * s₂ = s₂ * s₁)
    (hy1 : y * s₁ = s₁ * y) (hy2 : y * s₂ = s₂ * y) : False := by
  have hs₁ : orderOf s₁ = 2 := orderOf_eq_prime (by rw [sq]; exact h1) h1'
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hs₁
  have hyg : orderOf (g * y * g⁻¹) = p := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  refine not_commute_t_of_prime_ge_five h hp hp5 hyg (s := g * s₂ * g⁻¹) ?_ ?_ ?_ ?_ ?_ ?_
  · calc g * s₂ * g⁻¹ * (g * s₂ * g⁻¹) = g * (s₂ * s₂) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group
  · intro he
    apply h2'
    calc s₂ = g⁻¹ * (g * s₂ * g⁻¹) * g := by group
      _ = 1 := by rw [he]; group
  · intro he
    apply h12
    calc s₁ = g⁻¹ * (g * s₁ * g⁻¹) * g := by group
      _ = g⁻¹ * (g * s₂ * g⁻¹) * g := by rw [hg, he]
      _ = s₂ := by group
  · rw [← hg]
    exact conj_commute_of_commute g s₂ s₁ hc.symm
  · rw [← hg]
    exact conj_commute_of_commute g y s₁ hy1
  · exact conj_commute_of_commute g y s₂ hy2

theorem mul_self_of_sylow_two (h : JankoHyp₀ G) (S : Sylow 2 G) {x : G}
    (hx : x ∈ (S : Subgroup G)) : x * x = 1 := by
  obtain ⟨T, hT⟩ := h.exists_sylow_mem_t
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  have hx' : x ∈ ((g • T : Sylow 2 G) : Subgroup G) := by rw [hg]; exact hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
  have h1 := h.mul_self_of_mem_sylow T hT hx'
  rw [MulAut.smul_def, MulAut.conj_inv_apply] at h1
  calc x * x = g * (g⁻¹ * x * g * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem not_normalizes_zpowers_of_sylow (h : JankoHyp₀ G) {U : Subgroup G} {y : G} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hy : orderOf y = p) (hU : IsPGroup 2 U)
    (hUi : ¬ 2 ∣ U.index) (hN : ∀ u ∈ U, u * y * u⁻¹ ∈ zpowers y) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUc : Nat.card U = 8 := h.card_sylow (hU.toSylow hUi)
  have hsq : ∀ u ∈ U, u * u = 1 := fun u hu => mul_self_of_sylow_two h (hU.toSylow hUi) hu
  have hab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    have := h.abelian_sylow (hU.toSylow hUi)
    exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨s₁, hs₁, s₂, hs₂, h1, h2, h12, hy1, hy2⟩ :=
    exists_two_centralizing_of_card_eight hUc hsq hp hy hN
  exact not_commute_four_of_prime_ge_five h hp hp5 hy (hsq s₁ hs₁) h1 (hsq s₂ hs₂) h2 h12
    (hab _ hs₁ _ hs₂) hy1 hy2

end Janko

end CFSG.Quasithin.H13.NQCore
