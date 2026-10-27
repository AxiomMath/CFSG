module

public import CFSG.RankThree.PartOne.SLB4B.CoverKer

public section

namespace CFSG.RankThree.PartOne.SLB4B

open Subgroup CFSG CFSG.RankThree.PartOne.SRC

section PTorsion

variable {Y X : Type*} [Group Y] [Group X] {p : ℕ}

@[expose] def pPowHom (φ : Y →* X) (U : Subgroup X) (p : ℕ)
    (hcomm : ∀ x ∈ U.comap φ, ∀ y ∈ U.comap φ, x * y = y * x) : U.comap φ →* U.comap φ where
  toFun y := y ^ p
  map_one' := one_pow p
  map_mul' a b := Commute.mul_pow (Subtype.ext (hcomm a a.2 b b.2) : Commute a b) p

@[expose] def preimagePTorsion (φ : Y →* X) (U : Subgroup X) (p : ℕ)
    (hcomm : ∀ x ∈ U.comap φ, ∀ y ∈ U.comap φ, x * y = y * x) : Subgroup Y :=
  (pPowHom φ U p hcomm).ker.map (U.comap φ).subtype

theorem mem_preimagePTorsion {φ : Y →* X} {U : Subgroup X}
    {hcomm : ∀ x ∈ U.comap φ, ∀ y ∈ U.comap φ, x * y = y * x} {x : Y} :
    x ∈ preimagePTorsion φ U p hcomm ↔ φ x ∈ U ∧ x ^ p = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, congrArg Subtype.val (MonoidHom.mem_ker.mp hy)⟩
  · rintro ⟨hx, hxp⟩
    exact ⟨⟨x, hx⟩, MonoidHom.mem_ker.mpr (Subtype.ext hxp), rfl⟩

theorem isElementaryAbelian_preimagePTorsion (φ : Y →* X) (U : Subgroup X)
    (hcomm : ∀ x ∈ U.comap φ, ∀ y ∈ U.comap φ, x * y = y * x) :
    IsElementaryAbelian p (preimagePTorsion φ U p hcomm) := by
  refine { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext ?_⟩⟩, exponent_dvd_p := ?_ }
  · exact hcomm a (mem_preimagePTorsion.mp a.2).1 b (mem_preimagePTorsion.mp b.2).1
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => Subtype.ext ?_
    exact (mem_preimagePTorsion.mp x.2).2

theorem card_le_card_preimagePTorsion [Finite Y] [Fact p.Prime] (φ : Y →* X)
    (hφ : Function.Surjective φ) {U : Subgroup X} (hU : IsElementaryAbelian p U)
    (hcomm : ∀ x ∈ U.comap φ, ∀ y ∈ U.comap φ, x * y = y * x) :
    Nat.card U ≤ Nat.card (preimagePTorsion φ U p hcomm) := by
  classical
  have := hU
  set pw := pPowHom φ U p hcomm with hpw
  let ψ : U.comap φ →* U := (φ.comp (U.comap φ).subtype).codRestrict U fun y => y.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨u, hu⟩
    obtain ⟨y, rfl⟩ := hφ u
    exact ⟨⟨y, hu⟩, rfl⟩
  have hrange : pw.range ≤ ψ.ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change φ ((y : Y) ^ p) = 1
    rw [map_pow]
    exact elemPow_eq_one_of_isElementaryAbelian (p := p) (φ y) y.2
  have h1 : Nat.card pw.ker * Nat.card pw.range = Nat.card (U.comap φ) :=
    Subgroup.card_ker_mul_card_range pw
  have h2 : Nat.card ψ.ker * Nat.card U = Nat.card (U.comap φ) :=
    Subgroup.card_ker_mul_card_of_surjective hψ
  have h3 : Nat.card pw.range ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hrange
  have hpos : 0 < Nat.card pw.range := Nat.card_pos
  have hU' : Nat.card U ≤ Nat.card pw.ker := by
    by_contra hlt
    push Not at hlt
    have h4 := Nat.mul_lt_mul_of_lt_of_le' hlt h3 hpos
    rw [h1, mul_comm (Nat.card U), h2] at h4
    exact lt_irrefl _ h4
  have h5 : Nat.card (preimagePTorsion φ U p hcomm) = Nat.card pw.ker :=
    Subgroup.card_map_of_injective (U.comap φ).subtype_injective
  rw [h5]
  exact hU'

theorem card_mul_le_card_preimagePTorsion [Finite Y] [Fact p.Prime] (φ : Y →* X) {U : Subgroup X}
    (hcomm : ∀ x ∈ U.comap φ, ∀ y ∈ U.comap φ, x * y = y * x)
    (hlift : ∀ u ∈ U, ∃ x : Y, φ x = u ∧ x ^ p = 1) {n : Y} (hn : φ n = 1) (hn1 : n ≠ 1)
    (hnp : n ^ p = 1) :
    p * Nat.card U ≤ Nat.card (preimagePTorsion φ U p hcomm) := by
  classical
  set Ω := preimagePTorsion φ U p hcomm with hΩ
  let ψ : Ω →* U := (φ.comp Ω.subtype).codRestrict U fun y => (mem_preimagePTorsion.mp y.2).1
  have hψ : Function.Surjective ψ := by
    rintro ⟨u, hu⟩
    obtain ⟨x, hx, hxp⟩ := hlift u hu
    exact ⟨⟨x, mem_preimagePTorsion.mpr ⟨hx ▸ hu, hxp⟩⟩, Subtype.ext hx⟩
  have h2 : Nat.card ψ.ker * Nat.card U = Nat.card Ω :=
    Subgroup.card_ker_mul_card_of_surjective hψ
  have hnΩ : n ∈ Ω := mem_preimagePTorsion.mpr ⟨by rw [hn]; exact one_mem U, hnp⟩
  set n' : Ω := ⟨n, hnΩ⟩ with hn'
  have hn'1 : n' ≠ 1 := fun h => hn1 (congrArg Subtype.val h)
  have hn'p : n' ^ p = 1 := Subtype.ext hnp
  have hord : orderOf n' = p := orderOf_eq_prime hn'p hn'1
  have hmem : n' ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext hn
  have hle : Subgroup.zpowers n' ≤ ψ.ker := (Subgroup.zpowers_le).mpr hmem
  have h3 : p ≤ Nat.card ψ.ker := by
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, hord] at this
  rw [← h2]
  exact Nat.mul_le_mul_right _ h3

end PTorsion

section Cover

theorem rank_four_of_cover_quasisimple_comm {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q : Type}
    [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    (hZ : Nat.Coprime p (Nat.card (center Q))) (h : Q) (hhc : h ∉ center Q)
    (hho : Nat.Coprime (orderOf h) p)
    {E₀ : Subgroup Q} (hE₀ : IsElementaryAbelian p E₀) {k : ℕ} (hk : 4 ≤ k)
    (hcard : Nat.card E₀ = p ^ k)
    (hcomm : ∀ (Y : Type) [Group Y] (φ : Y →* Q), Function.Surjective φ →
      φ.ker ≤ center Y → ∀ x ∈ E₀.comap φ, ∀ y ∈ E₀.comap φ, x * y = y * x)
    {W : Type} [Group W] [Finite W] (ρ : W →* Q) (hρ : Function.Surjective ρ)
    (hker : IsPGroup p ρ.ker) :
    ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  have hp : p.Prime := Fact.out
  have hQp : p ^ 4 ∣ Nat.card Q :=
    (pow_dvd_pow p hk).trans (hcard ▸ Subgroup.card_subgroup_dvd_card E₀)
  by_contra hno
  have hrank := card_le_pow_three_of_not_rank_four hno
  obtain ⟨W₀, hs, hcen, -⟩ :=
    exists_central_cover_of_rank_le_three hp2 hQ hZ h hhc hho hQp ρ hρ hker hrank
  have hc := hcomm W₀ (ρ.comp W₀.subtype) hs hcen
  have hV := card_le_card_preimagePTorsion (ρ.comp W₀.subtype) hs hE₀ hc
  have hVea := isElementaryAbelian_preimagePTorsion (p := p) (ρ.comp W₀.subtype) E₀ hc
  have h1 := hrank _ (isElementaryAbelian_map' W₀.subtype hVea)
  rw [Subgroup.card_map_of_injective W₀.subtype_injective] at h1
  have hp4 : p ^ 3 < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

theorem rank_four_of_cover_quasisimple_ker_comm {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q : Type}
    [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    (hZ : Nat.Coprime p (Nat.card (center Q))) (h : Q) (hhc : h ∉ center Q)
    (hho : Nat.Coprime (orderOf h) p) (hQp : p ^ 4 ∣ Nat.card Q)
    {E₀ : Subgroup Q} (hE₀ : IsElementaryAbelian p E₀) (hcard : Nat.card E₀ = p ^ 3)
    (hcomm : ∀ (Y : Type) [Group Y] (φ : Y →* Q), Function.Surjective φ →
      φ.ker ≤ center Y → ∀ x ∈ E₀.comap φ, ∀ y ∈ E₀.comap φ, x * y = y * x)
    (hlift : ∀ (Y : Type) [Group Y] (φ : Y →* Q), Function.Surjective φ →
      φ.ker ≤ center Y → ∀ e ∈ E₀, ∃ x : Y, φ x = e ∧ x ^ p = 1)
    {W : Type} [Group W] [Finite W] (π : W →* Q) (hπ : Function.Surjective π)
    (hker : IsPGroup p π.ker) (hker1 : π.ker ≠ ⊥) :
    ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  classical
  have hp : p.Prime := Fact.out
  by_contra hno
  have hrank := card_le_pow_three_of_not_rank_four hno
  obtain ⟨W₀, hs, hcen, hker₀⟩ :=
    exists_central_cover_of_rank_le_three hp2 hQ hZ h hhc hho hQp π hπ hker hrank
  set ρ₀ : W₀ →* Q := π.comp W₀.subtype with hρ₀
  by_cases hN : ρ₀.ker = ⊥
  ·
    have hinj : Function.Injective ρ₀ := (MonoidHom.ker_eq_bot_iff ρ₀).mp hN
    let e : W₀ ≃* Q := MulEquiv.ofBijective ρ₀ ⟨hinj, hs⟩
    have hσ : ∀ g, π ((W₀.subtype.comp e.symm.toMonoidHom) g) = g := fun g => by
      have := e.apply_symm_apply g
      exact this
    exact hno (exists_rank_four_of_section_ker hQ hZ hQp hE₀ hcard π hker hker1 hrank
      (W₀.subtype.comp e.symm.toMonoidHom) hσ)
  ·
    have hnt : Nontrivial ρ₀.ker := (Subgroup.nontrivial_iff_ne_bot _).mpr hN
    obtain ⟨m, hm⟩ := hker₀.exists_card_eq
    have hpdvd : p ∣ Nat.card ρ₀.ker := by
      have h1 : 1 < Nat.card ρ₀.ker := Finite.one_lt_card_iff_nontrivial.mpr hnt
      rw [hm] at h1 ⊢
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [pow_zero] at h1
        exact lt_irrefl 1 h1
      exact dvd_pow_self p hm0
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ρ₀.ker) p hpdvd
    have hzp : (z : W₀) ^ p = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz] at this
      simpa using congrArg Subtype.val this
    have hz1 : (z : W₀) ≠ 1 := by
      intro h0
      have : z = 1 := Subtype.ext h0
      rw [this, orderOf_one] at hz
      exact hp.one_lt.ne hz
    have hc := hcomm W₀ ρ₀ hs hcen
    have hl := hlift W₀ ρ₀ hs hcen
    have hV := card_mul_le_card_preimagePTorsion (p := p) ρ₀ hc hl (n := (z : W₀))
      (MonoidHom.mem_ker.mp z.2) hz1 hzp
    have hVea := isElementaryAbelian_preimagePTorsion (p := p) ρ₀ E₀ hc
    have h1 := hrank _ (isElementaryAbelian_map' W₀.subtype hVea)
    rw [Subgroup.card_map_of_injective W₀.subtype_injective] at h1
    have hp4 : p ^ 3 < p * p ^ 3 := by
      calc p ^ 3 = 1 * p ^ 3 := (one_mul _).symm
        _ < p * p ^ 3 := Nat.mul_lt_mul_of_pos_right hp.one_lt (pow_pos hp.pos 3)
    rw [hcard] at hV
    omega

end Cover

end CFSG.RankThree.PartOne.SLB4B
