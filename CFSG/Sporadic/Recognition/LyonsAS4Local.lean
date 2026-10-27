module

public import CFSG.Sporadic.Recognition.LyonsAS4Cover
public import CFSG.Sporadic.Recognition.LyonsAS4Perm

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

theorem self_mem_centralizer_singleton {G : Type*} [Group G] (t : G) :
    t ∈ centralizer ({t} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

structure LyData (G : Type) [Group G] (t : G)
    (ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)) : Prop where
  order_t : orderOf t = 2
  cover : IsCover11 ρ ⟨t, self_mem_centralizer_singleton t⟩
  one_class : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v

section Plumbing

variable {G : Type*} [Group G]

theorem map_subtype_centralizer (H : Subgroup G) (x : H) :
    (centralizer ({x} : Set H)).map H.subtype = centralizer ({(x : G)} : Set G) ⊓ H := by
  ext g
  simp only [Subgroup.mem_map, mem_centralizer_singleton_iff, Subgroup.mem_inf,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨congrArg Subtype.val hh, h.2⟩
  · rintro ⟨hg, hgH⟩
    exact ⟨⟨g, hgH⟩, Subtype.ext hg, rfl⟩

theorem card_centralizer_inf (H : Subgroup G) (x : H) :
    Nat.card ↥(centralizer ({(x : G)} : Set G) ⊓ H) = Nat.card ↥(centralizer ({x} : Set H)) := by
  rw [← map_subtype_centralizer, Subgroup.card_map_of_injective H.subtype_injective]

theorem card_centralizer_eq_of_isConj {x y : G} (h : IsConj x y) :
    Nat.card ↥(centralizer ({x} : Set G)) = Nat.card ↥(centralizer ({y} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  have : (centralizer ({x} : Set G)).map (MulAut.conj c).toMonoidHom =
      centralizer ({c * x * c⁻¹} : Set G) := by
    ext g
    simp only [Subgroup.mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨h, hh, rfl⟩
      calc c * h * c⁻¹ * (c * x * c⁻¹) = c * (h * x) * c⁻¹ := by group
        _ = c * (x * h) * c⁻¹ := by rw [hh]
        _ = c * x * c⁻¹ * (c * h * c⁻¹) := by group
    · intro hg
      refine ⟨c⁻¹ * g * c, ?_, by group⟩
      calc c⁻¹ * g * c * x = c⁻¹ * (g * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * x * c⁻¹ * g) * c := by rw [hg]
        _ = x * (c⁻¹ * g * c) := by group
  rw [← this, Subgroup.card_map_of_injective (MulAut.conj c).injective]

end Plumbing

namespace LyData

variable {G : Type} [Group G] {t : G} {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}

theorem card_centralizer_inf (D : LyData G t ρ) {x : ↥(centralizer ({t} : Set G))}
    (hx : x ^ 3 = 1) :
    Nat.card ↥(centralizer ({(x : G)} : Set G) ⊓ centralizer ({t} : Set G)) =
      2 * Nat.card ↥(CA (ρ x)) := by
  rw [LyonsSims.card_centralizer_inf, D.cover.card_centralizer hx]
  rfl

end LyData

namespace IsCover11

variable {E : Type*} [Group E] {ρ : E →* Perm (Fin 11)} {z : E}

theorem isConj_of_cycleType_eq (h : IsCover11 ρ z) {a b : E} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hc : (ρ a).cycleType = (ρ b).cycleType) : IsConj a b := by
  have ha3 : ρ a ^ 3 = 1 := by rw [← map_pow, ha, map_one]
  obtain ⟨g, hgs, hg⟩ := exists_even_conj_of_cycleType_eq ha3 hc
  obtain ⟨g', hg'⟩ := h.exists_lift hgs
  have h1 : ρ (g' * a * g'⁻¹) = ρ b := by rw [map_mul, map_mul, map_inv, hg', hg]
  have h2 : (g' * a * g'⁻¹) ^ 3 = 1 := by rw [conj_pow, ha]; group
  exact isConj_iff.2 ⟨g', h.eq_of_rho_eq_of_pow_three h2 hb h1⟩

end IsCover11

end CFSG.Sporadic.Recognition.LyonsSims
