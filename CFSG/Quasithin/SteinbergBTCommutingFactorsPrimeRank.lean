module

public import CFSG.Quasithin.SteinbergBSSmallRankEscape

public noncomputable section

namespace CFSG.Quasithin.SteinbergBT

open Subgroup

theorem commuting_central_quotient_factors_force_prime_rank {H : Type*} [Group H] [Finite H]
    {r : ℕ} (hr : r.Prime) (d : ℕ) (L : Fin d → Subgroup H)
    (hcomm : ∀ i j, i ≠ j → ⁅L i, L j⁆ = ⊥)
    (hdvd : ∀ i, r ∣ Nat.card (L i ⧸ center (L i))) :
    d ≤ CFSG.pRank r H := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hy : ∀ i, ∃ y : L i, orderOf (y : L i ⧸ center (L i)) = r := fun i => by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := L i ⧸ center (L i)) r (hdvd i)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨y, hz⟩
  choose y hy using hy
  set x : Fin d → H := fun i => (y i : H) with hxdef
  have hxC : ∀ i j, i ≠ j → x j ∈ centralizer (L i : Set H) := fun i j hij =>
    (commutator_eq_bot_iff_le_centralizer.1 (hcomm j i hij.symm)) (y j).2
  have hxx : ∀ i j, i ≠ j → Commute (x i) (x j) := fun i j hij =>
    (mem_centralizer_iff.1 (hxC i j hij) (x i) (y i).2)
  set ϕ : ∀ i : Fin d, Multiplicative ℤ →* H := fun i => zpowersHom H (x i) with hϕ
  have hϕcomm : Pairwise fun i j => ∀ a b, Commute (ϕ i a) (ϕ j b) := fun i j hij a b =>
    (hxx i j hij).zpow_zpow _ _
  set Φ : (Fin d → Multiplicative ℤ) →* H := MonoidHom.noncommPiCoprod ϕ hϕcomm with hΦdef
  have hind : ∀ n : Fin d → Multiplicative ℤ, Φ n = 1 → ∀ i, (r : ℤ) ∣ (n i).toAdd := by
    intro n hn i
    set n' := Function.update n i 1 with hn'
    have hsplit : n = Pi.mulSingle i (n i) * n' := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [hn']
      · simp [hn', hj]
    have hΦn : Φ n = x i ^ (n i).toAdd * Φ n' := by
      conv_lhs => rw [hsplit]
      rw [map_mul, hΦdef, MonoidHom.noncommPiCoprod_mulSingle]
      rfl
    have hmem : Φ n' ∈ centralizer (L i : Set H) := by
      change Finset.univ.noncommProd (fun j => ϕ j (n' j))
        (fun _ _ _ _ h => hϕcomm h _ _) ∈ _
      refine Subgroup.noncommProd_mem _ _ fun j _ => ?_
      by_cases hj : j = i
      · subst hj
        rw [hn', Function.update_self, map_one]
        exact one_mem _
      · rw [hn', Function.update_of_ne hj, hϕ, zpowersHom_apply]
        exact zpow_mem (hxC i j (Ne.symm hj)) _
    have hxi : x i ^ (n i).toAdd ∈ centralizer (L i : Set H) := by
      have h1 : x i ^ (n i).toAdd = (Φ n')⁻¹ := eq_inv_of_mul_eq_one_left (hΦn ▸ hn)
      rw [h1]
      exact inv_mem hmem
    have hcen : y i ^ (n i).toAdd ∈ center (L i) := by
      rw [mem_center_iff]
      intro z
      apply Subtype.ext
      rw [coe_mul, coe_mul, coe_zpow]
      exact (mem_centralizer_iff.1 hxi) z z.2
    have h1 : (y i : L i ⧸ center (L i)) ^ (n i).toAdd = 1 := by
      rw [← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]
      exact hcen
    rw [← hy i]
    exact orderOf_dvd_iff_zpow_eq_one.2 h1
  set X := Φ.range with hXdef
  have hXcomm : ∀ a b : X, a * b = b * a := by
    rintro ⟨_, u, rfl⟩ ⟨_, v, rfl⟩
    apply Subtype.ext
    change Φ u * Φ v = Φ v * Φ u
    rw [← map_mul, ← map_mul, mul_comm u v]
  let ρ : X →* X :=
    { toFun := fun a => a ^ r
      map_one' := one_pow r
      map_mul' := fun a b => (Commute.mul_pow (hXcomm a b) r) }
  have hρ : ∀ a, ρ a = a ^ r := fun a => rfl
  set Φ' : (Fin d → Multiplicative ℤ) →* X := Φ.rangeRestrict with hΦ'
  let ψ : (Fin d → Fin r) → X ⧸ ρ.range := fun g =>
    (Φ' fun i => Multiplicative.ofAdd ((g i : ℕ) : ℤ) : X ⧸ ρ.range)
  have hψ : Function.Injective ψ := by
    intro g g' h
    rw [QuotientGroup.eq] at h
    obtain ⟨c, hc⟩ := h
    obtain ⟨m, rfl⟩ := Φ.rangeRestrict_surjective c
    set ng : Fin d → Multiplicative ℤ := fun i => Multiplicative.ofAdd ((g i : ℕ) : ℤ)
    set ng' : Fin d → Multiplicative ℤ := fun i => Multiplicative.ofAdd ((g' i : ℕ) : ℤ)
    have h1 : Φ (ng⁻¹ * ng' * (m ^ r)⁻¹) = 1 := by
      have h2 := congrArg Subtype.val hc
      rw [hρ, coe_pow, coe_mul, coe_inv, MonoidHom.coe_rangeRestrict,
        MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict] at h2
      rw [map_mul, map_mul, map_inv, map_inv, map_pow, h2]
      group
    funext i
    have h3 := hind _ h1 i
    have h4 : ((ng⁻¹ * ng' * (m ^ r)⁻¹) i).toAdd =
        ((g' i : ℕ) : ℤ) - ((g i : ℕ) : ℤ) - (r : ℤ) * (m i).toAdd := by
      simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, toAdd_mul, toAdd_inv, toAdd_pow, ng, ng',
        toAdd_ofAdd, nsmul_eq_mul]
      ring
    rw [h4] at h3
    have h5 : (r : ℤ) ∣ ((g' i : ℕ) : ℤ) - ((g i : ℕ) : ℤ) := by
      have := dvd_add h3 (dvd_mul_right (r : ℤ) (m i).toAdd)
      rwa [sub_add_cancel] at this
    obtain ⟨c, hc⟩ := h5
    have hgi := (g i).isLt
    have hgi' := (g' i).isLt
    apply Fin.ext
    have hr0 : (0 : ℤ) < r := by exact_mod_cast hr.pos
    rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
    · have : (r : ℤ) * c ≤ (r : ℤ) * (-1) := mul_le_mul_of_nonneg_left (by omega) hr0.le
      omega
    · subst hc0
      omega
    · have : (r : ℤ) * 1 ≤ (r : ℤ) * c := mul_le_mul_of_nonneg_left (by omega) hr0.le
      omega
  have hquot : r ^ d ≤ Nat.card (X ⧸ ρ.range) := by
    have := Nat.card_le_card_of_injective ψ hψ
    rwa [Nat.card_eq_fintype_card (α := Fin d → Fin r), Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin] at this
  have hΩ : Nat.card ρ.ker = Nat.card (X ⧸ ρ.range) := by
    have h1 := card_mul_index ρ.ker
    rw [index_ker] at h1
    have h2 := card_eq_card_quotient_mul_card_subgroup ρ.range
    have hpos : 0 < Nat.card ρ.range := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2)
  set E : Subgroup H := ρ.ker.map X.subtype with hEdef
  have hEX : ∀ e ∈ E, e ∈ X ∧ e ^ r = 1 := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨k.2, ?_⟩
    have := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
    rwa [hρ, coe_pow, coe_one] at this
  have hEe : CFSG.IsElementaryAbelian r E :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (by
        have h := congrArg Subtype.val (hXcomm ⟨a, (hEX a a.2).1⟩ ⟨b, (hEX b b.2).1⟩)
        exact h)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext (by
        rw [coe_pow, (hEX a a.2).2, coe_one]) }
  have hEp : IsPGroup r E := fun a => ⟨1, Subtype.ext (by
    rw [pow_one, coe_pow, (hEX a a.2).2, coe_one])⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hEp
  have hEcard : Nat.card E = Nat.card ρ.ker := card_map_of_injective X.subtype_injective
  have hdm : d ≤ m := by
    have h1 : r ^ d ≤ r ^ m := by rw [← hm, hEcard, hΩ]; exact hquot
    exact (Nat.pow_le_pow_iff_right hr.one_lt).1 h1
  exact hdm.trans (SteinbergBS.le_pRank_of_card hr.one_lt hEe hm)

end CFSG.Quasithin.SteinbergBT
