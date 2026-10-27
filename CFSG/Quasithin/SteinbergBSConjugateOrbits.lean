module

public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup

variable {G : Type*} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {g x : G} : x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ ∈ H
    rwa [show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y by group]
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    change g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
    group

theorem conjugate_mul (H : Subgroup G) (a b : G) :
    conjugate H (a * b) = conjugate (conjugate H a) b := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff]
  rw [show a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ by group]

theorem conjugate_one (H : Subgroup G) : conjugate H 1 = H := by
  ext x
  rw [mem_conjugate_iff, one_mul, inv_one, mul_one]

theorem conjugate_of_mem_normalizer {H : Subgroup G} {a : G}
    (ha : a ∈ normalizer (H : Set G)) : conjugate H a = H := by
  ext x
  rw [mem_conjugate_iff]
  exact ((mem_normalizer_iff.1 ha x).symm)

theorem conj_mem_conjugate {H : Subgroup G} {x : G} (hx : x ∈ H) (g : G) :
    g⁻¹ * x * g ∈ conjugate H g := by
  rw [mem_conjugate_iff]
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]

theorem exists_centralizer_conjugate_eq {V N : Subgroup G} (hN : N ≤ normalizer (V : Set G))
    (htrans : ∀ x ∈ V, x ≠ 1 → ∀ y ∈ V, y ≠ 1 → ∃ n ∈ N, n⁻¹ * x * n = y) {z : G}
    (hzV : z ∈ V) (hz1 : z ≠ 1) {g : G} (hzg : z ∈ conjugate V g) :
    ∃ h ∈ centralizer ({z} : Set G), conjugate V h = conjugate V g := by
  have hgz : g * z * g⁻¹ ∈ V := mem_conjugate_iff.1 hzg
  have hgz1 : g * z * g⁻¹ ≠ 1 := fun h => hz1 (by
    rw [show z = g⁻¹ * (g * z * g⁻¹) * g by group, h]
    group)
  obtain ⟨m, hm, hmz⟩ := htrans z hzV hz1 _ hgz hgz1
  refine ⟨m * g, mem_centralizer_singleton_iff.2 ?_, ?_⟩
  · calc m * g * z = m * (g * z * g⁻¹) * g := by group
      _ = m * (m⁻¹ * z * m) * g := by rw [hmz]
      _ = z * (m * g) := by group
  · rw [conjugate_mul, conjugate_of_mem_normalizer (hN hm)]

theorem element_centralizer_orbit_commuting_propagation {V N : Subgroup G}
    (hN : N ≤ normalizer (V : Set G))
    (htrans : ∀ x ∈ V, x ≠ 1 → ∀ y ∈ V, y ≠ 1 → ∃ n ∈ N, n⁻¹ * x * n = y) {z : G}
    (hzV : z ∈ V) (hz1 : z ≠ 1) :
    {W : Subgroup G | ∃ g : G, z ∈ conjugate V g ∧ W = conjugate V g} =
      {W : Subgroup G | ∃ h ∈ centralizer ({z} : Set G), W = conjugate V h} ∧
    ((∀ x ∈ ⨆ h ∈ centralizer ({z} : Set G), conjugate V h,
        ∀ y ∈ ⨆ h ∈ centralizer ({z} : Set G), conjugate V h, x * y = y * x) →
      ∀ g : G, V ⊓ conjugate V g ≠ ⊥ → ⁅V, conjugate V g⁆ = ⊥) := by
  refine ⟨?_, fun hJ g hg => ?_⟩
  · ext W
    constructor
    · rintro ⟨g, hzg, rfl⟩
      obtain ⟨h, hh, hhg⟩ := exists_centralizer_conjugate_eq hN htrans hzV hz1 hzg
      exact ⟨h, hh, hhg.symm⟩
    · rintro ⟨h, hh, rfl⟩
      refine ⟨h, mem_conjugate_iff.2 ?_, rfl⟩
      rw [(mem_centralizer_singleton_iff.1 hh), mul_inv_cancel_right]
      exact hzV
  obtain ⟨⟨a, haV, hag⟩, ha1⟩ := (ne_bot_iff_exists_ne_one).1 hg
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  obtain ⟨n, hn, hnz⟩ := htrans a haV ha1' z hzV hz1
  have hzgn : z ∈ conjugate V (g * n) := by
    rw [mem_conjugate_iff, ← hnz]
    have h1 := mem_conjugate_iff.1 hag
    rwa [show g * n * (n⁻¹ * a * n) * (g * n)⁻¹ = g * a * g⁻¹ by group]
  obtain ⟨h, hh, hhg⟩ := exists_centralizer_conjugate_eq hN htrans hzV hz1 hzgn
  have hVJ : V ≤ ⨆ h ∈ centralizer ({z} : Set G), conjugate V h := by
    refine le_trans ?_ (le_iSup₂ (f := fun h (_ : h ∈ centralizer ({z} : Set G)) =>
      conjugate V h) 1 (one_mem _))
    rw [conjugate_one]
  have hVhJ : conjugate V h ≤ ⨆ h ∈ centralizer ({z} : Set G), conjugate V h :=
    le_iSup₂ (f := fun h (_ : h ∈ centralizer ({z} : Set G)) => conjugate V h) h hh
  rw [commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [mem_centralizer_iff]
  intro w hw
  have hv' : n⁻¹ * v * n ∈ V := by
    have h1 := (mem_normalizer_iff.1 (inv_mem (hN hn)) v).1 hv
    rwa [inv_inv] at h1
  have hw' : n⁻¹ * w * n ∈ conjugate V h := by
    rw [hhg, conjugate_mul]
    exact conj_mem_conjugate hw n
  have hc := hJ _ (hVhJ hw') _ (hVJ hv')
  calc w * v = n * ((n⁻¹ * w * n) * (n⁻¹ * v * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * v * n) * (n⁻¹ * w * n)) * n⁻¹ := by rw [hc]
    _ = v * w := by group

theorem mem_normalizer_of_conjugate_eq {Z : Subgroup G} {h : G} (hh : conjugate Z h = Z) :
    h ∈ normalizer (Z : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [← mem_conjugate_iff, hh]

theorem exists_normalizer_conjugate_eq {p : ℕ} {V Z : Subgroup G} (hZV : Z ≤ V)
    (hZp : Nat.card Z = p)
    (htrans : ∀ Z₁ : Subgroup G, Z₁ ≤ V → Nat.card Z₁ = p → ∀ Z₂ : Subgroup G, Z₂ ≤ V →
      Nat.card Z₂ = p → ∃ a ∈ normalizer (V : Set G), conjugate Z₁ a = Z₂)
    {g : G} (hZg : Z ≤ conjugate V g) :
    ∃ h ∈ normalizer (Z : Set G), conjugate V h = conjugate V g := by
  have hZg' : conjugate Z g⁻¹ ≤ V := by
    intro x hx
    rw [mem_conjugate_iff, inv_inv] at hx
    have h1 := hZg hx
    rw [mem_conjugate_iff] at h1
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
  have hZg'p : Nat.card (conjugate Z g⁻¹) = p := by
    rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹⁻¹).injective, hZp]
  obtain ⟨a, ha, haZ⟩ := htrans Z hZV hZp _ hZg' hZg'p
  refine ⟨a * g, mem_normalizer_of_conjugate_eq ?_, ?_⟩
  · rw [conjugate_mul, haZ, ← conjugate_mul, inv_mul_cancel, conjugate_one]
  · rw [conjugate_mul, conjugate_of_mem_normalizer ha]

theorem linear_line_normalizer_conjugate_fusion {p : ℕ} [hp : Fact p.Prime] {V : Subgroup G}
    [IsElementaryAbelian p V]
    (htrans : ∀ Z₁ : Subgroup G, Z₁ ≤ V → Nat.card Z₁ = p → ∀ Z₂ : Subgroup G, Z₂ ≤ V →
      Nat.card Z₂ = p → ∃ a ∈ normalizer (V : Set G), conjugate Z₁ a = Z₂) :
    (∀ Z : Subgroup G, Z ≤ V → Nat.card Z = p →
      {W : Subgroup G | ∃ g : G, Z ≤ conjugate V g ∧ W = conjugate V g} =
        {W : Subgroup G | ∃ h ∈ normalizer (Z : Set G), W = conjugate V h} ∧
      ∀ g : G, Z ≤ conjugate V g → conjugate V g ≤ ⨆ h ∈ normalizer (Z : Set G), conjugate V h) ∧
    ((∀ Z : Subgroup G, Z ≤ V → Nat.card Z = p →
        ∀ x ∈ ⨆ h ∈ normalizer (Z : Set G), conjugate V h,
          ∀ y ∈ ⨆ h ∈ normalizer (Z : Set G), conjugate V h, x * y = y * x) →
      ∀ g : G, V ⊓ conjugate V g ≠ ⊥ → ⁅V, conjugate V g⁆ = ⊥) ∧
    ∀ Z : Subgroup G, Z ≤ V → Nat.card Z = p →
      (∀ x ∈ ⨆ h ∈ normalizer (Z : Set G), conjugate V h,
        ∀ y ∈ ⨆ h ∈ normalizer (Z : Set G), conjugate V h, x * y = y * x) →
      IsElementaryAbelian p ↥(⨆ h ∈ normalizer (Z : Set G), conjugate V h) ∧
        (⨆ h ∈ normalizer (Z : Set G), conjugate V h) ≤ normalizer (Z : Set G) ∧
        normalizer (Z : Set G) ≤
          normalizer (((⨆ h ∈ normalizer (Z : Set G), conjugate V h) : Subgroup G) : Set G) := by
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : V) ⟨y, hy⟩)
  have hVp : ∀ x ∈ V, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hcab : ∀ g : G, ∀ x ∈ conjugate V g, ∀ y ∈ conjugate V g, x * y = y * x := by
    intro g x hx y hy
    have h1 := hVab _ (mem_conjugate_iff.1 hx) _ (mem_conjugate_iff.1 hy)
    calc x * y = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h1]
      _ = y * x := by group
  have hcp : ∀ g : G, ∀ x ∈ conjugate V g, x ^ p = 1 := by
    intro g x hx
    have h1 := hVp _ (mem_conjugate_iff.1 hx)
    rw [show g * x * g⁻¹ = (MulAut.conj g) x from rfl, ← map_pow] at h1
    exact (MulAut.conj g).injective (h1.trans (map_one _).symm)
  have horbit : ∀ Z : Subgroup G, Z ≤ V → Nat.card Z = p →
      {W : Subgroup G | ∃ g : G, Z ≤ conjugate V g ∧ W = conjugate V g} =
        {W : Subgroup G | ∃ h ∈ normalizer (Z : Set G), W = conjugate V h} := by
    intro Z hZV hZp
    ext W
    constructor
    · rintro ⟨g, hZg, rfl⟩
      obtain ⟨h, hh, hhg⟩ := exists_normalizer_conjugate_eq hZV hZp htrans hZg
      exact ⟨h, hh, hhg.symm⟩
    · rintro ⟨h, hh, rfl⟩
      refine ⟨h, fun x hx => mem_conjugate_iff.2 (hZV ((mem_normalizer_iff.1 hh x).1 hx)), rfl⟩
  have hle : ∀ Z : Subgroup G, Z ≤ V → Nat.card Z = p → ∀ g : G, Z ≤ conjugate V g →
      conjugate V g ≤ ⨆ h ∈ normalizer (Z : Set G), conjugate V h := by
    intro Z hZV hZp g hZg
    obtain ⟨h, hh, hhg⟩ := exists_normalizer_conjugate_eq hZV hZp htrans hZg
    rw [← hhg]
    exact le_iSup₂ (f := fun h (_ : h ∈ normalizer (Z : Set G)) => conjugate V h) h hh
  have hVJ : ∀ Z : Subgroup G, V ≤ ⨆ h ∈ normalizer (Z : Set G), conjugate V h := fun Z => by
    refine le_trans ?_ (le_iSup₂ (f := fun h (_ : h ∈ normalizer (Z : Set G)) =>
      conjugate V h) 1 (one_mem _))
    rw [conjugate_one]
  refine ⟨fun Z hZV hZp => ⟨horbit Z hZV hZp, hle Z hZV hZp⟩, fun hJ g hg => ?_,
    fun Z hZV hZp hJ => ?_⟩
  ·
    obtain ⟨⟨a, haV, hag⟩, ha1⟩ := (ne_bot_iff_exists_ne_one).1 hg
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hao : orderOf a = p := orderOf_eq_prime (hVp a haV) ha1'
    have hZp : Nat.card (zpowers a) = p := by rw [Nat.card_zpowers, hao]
    have hZV : zpowers a ≤ V := (zpowers_le).2 haV
    have hZg : zpowers a ≤ conjugate V g := (zpowers_le).2 hag
    have h1 := hle _ hZV hZp g hZg
    rw [commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [mem_centralizer_iff]
    intro w hw
    exact hJ _ hZV hZp _ (h1 hw) _ (hVJ _ hv)
  · set J := ⨆ h ∈ normalizer (Z : Set G), conjugate V h with hJdef
    let T : Subgroup G :=
      { carrier := {x | x ∈ J ∧ x ^ p = 1}
        mul_mem' := fun {x y} hx hy => ⟨J.mul_mem hx.1 hy.1, by
          rw [(Commute.mul_pow (hJ x hx.1 y hy.1)), hx.2, hy.2, one_mul]⟩
        one_mem' := ⟨J.one_mem, one_pow p⟩
        inv_mem' := fun {x} hx => ⟨J.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
    have hJT : J ≤ T := iSup₂_le fun h hh x hx =>
      ⟨le_iSup₂ (f := fun h (_ : h ∈ normalizer (Z : Set G)) => conjugate V h) h hh hx,
        hcp h x hx⟩
    refine ⟨{ toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (hJ _ x.2 _ y.2)⟩⟩
              exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
                Subtype.ext (by
                  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
                  exact (hJT x.2).2) }, ?_, ?_⟩
    ·
      refine iSup₂_le fun h hh x hx => centralizer_le_normalizer _ ?_
      rw [mem_centralizer_iff]
      intro z hz
      have hzh : z ∈ conjugate V h :=
        mem_conjugate_iff.2 (hZV ((mem_normalizer_iff.1 hh z).1 hz))
      exact hcab h z hzh x hx
    ·
      have hmapJ : ∀ x ∈ normalizer (Z : Set G), ∀ y ∈ J, x * y * x⁻¹ ∈ J := by
        intro x hx y hy
        have hle' : J ≤ J.comap (MulAut.conj x).toMonoidHom := by
          refine iSup₂_le fun h hh w hw => ?_
          show x * w * x⁻¹ ∈ J
          have hmem : x * w * x⁻¹ ∈ conjugate V (h * x⁻¹) := by
            rw [mem_conjugate_iff]
            rwa [show h * x⁻¹ * (x * w * x⁻¹) * (h * x⁻¹)⁻¹ = h * w * h⁻¹ by group,
              ← mem_conjugate_iff]
          exact le_iSup₂ (f := fun h (_ : h ∈ normalizer (Z : Set G)) => conjugate V h)
            (h * x⁻¹) (mul_mem hh (inv_mem hx)) hmem
        exact hle' hy
      intro x hx
      rw [mem_normalizer_iff]
      intro y
      refine ⟨fun hy => hmapJ x hx y hy, fun hy => ?_⟩
      have h1 := hmapJ x⁻¹ (inv_mem hx) _ hy
      rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1

end CFSG.Quasithin.SteinbergBS
