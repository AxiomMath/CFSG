module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.SzF53MSecA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher.S43

namespace Odd

namespace Twelve

variable {G : Type} [Group G]

@[expose] def commHom {V T A₀ : Subgroup G} {y : G} (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hy : y ∈ Subgroup.normalizer (V : Set G)) (hA₀ : A₀ ≤ V)
    (h : ∀ a ∈ A₀, y * a * y⁻¹ * a⁻¹ ∈ T) : ↥A₀ →* ↥T where
  toFun a := ⟨y * a * y⁻¹ * (a : G)⁻¹, h a a.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    have hb : y * (b : G) * y⁻¹ * (b : G)⁻¹ ∈ V := by
      have h1 : y * (b : G) * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hy b).mp (hA₀ b.2)
      exact V.mul_mem h1 (V.inv_mem (hA₀ b.2))
    have hc := hV _ (V.inv_mem (hA₀ a.2)) _ hb
    show y * ((a : G) * b) * y⁻¹ * ((a : G) * b)⁻¹ =
      y * (a : G) * y⁻¹ * (a : G)⁻¹ * (y * (b : G) * y⁻¹ * (b : G)⁻¹)
    calc y * ((a : G) * b) * y⁻¹ * ((a : G) * b)⁻¹ =
          y * (a : G) * y⁻¹ * ((y * (b : G) * y⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
      _ = y * (a : G) * y⁻¹ * ((a : G)⁻¹ * (y * (b : G) * y⁻¹ * (b : G)⁻¹)) := by rw [hc]
      _ = _ := by group

theorem le_normalizer_of_comm {V L : Subgroup G}
    (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hLV : L ≤ V) :
    V ≤ Subgroup.normalizer (L : Set G) := fun v hv => by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have e : v * x * v⁻¹ = x := by rw [hV v hv x (hLV hx)]; group
    rw [e]
    exact hx
  · intro hx
    have hxV : x ∈ V := by
      have e : x = v⁻¹ * (v * x * v⁻¹) * v := by group
      rw [e]
      exact V.mul_mem (V.mul_mem (V.inv_mem hv) (hLV hx)) hv
    have e : v * x * v⁻¹ = x := by rw [hV v hv x hxV]; group
    rw [e] at hx
    exact hx

theorem secIdx_le_of_comm_mem [Finite G] {V L T A₀ : Subgroup G} {y : G}
    (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hy : y ∈ Subgroup.normalizer (V : Set G))
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) (hLT : L ≤ T) (hTV : T ≤ V) (hA₀ : A₀ ≤ V)
    (h : ∀ a ∈ A₀, y * a * y⁻¹ * a⁻¹ ∈ T) :
    secIdx (Subgroup.zpowers y) L V ≤ A₀.relIndex V * L.relIndex T := by
  have hVL : V ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_comm hV (hLT.trans hTV)
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hTV.trans hVL
  have := Subgroup.normal_subgroupOf_of_le_normalizer hTL
  set F := fixSecIn (Subgroup.zpowers y) L V with hF
  have hmemF : ∀ x, x ∈ F ↔ x ∈ V ∧ y * x * y⁻¹ * x⁻¹ ∈ L := fun x =>
    mem_fixSecIn_zpowers_iff hVL hyL
  set g : ↥A₀ →* ↥T ⧸ L.subgroupOf T :=
    (QuotientGroup.mk' (L.subgroupOf T)).comp (commHom hV hy hA₀ h) with hg
  have hker : g.ker = (F ⊓ A₀).subgroupOf A₀ := by
    ext a
    rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf, hmemF]
    exact ⟨fun h1 => ⟨⟨hA₀ a.2, h1⟩, a.2⟩, fun h1 => h1.1.2⟩
  have h1 : (F ⊓ A₀).relIndex A₀ ≤ L.relIndex T := by
    unfold Subgroup.relIndex
    rw [← hker, Subgroup.index_ker]
    exact (Subgroup.card_le_card_group _).trans le_rfl
  have h2 : F.relIndex V ≤ (F ⊓ A₀).relIndex V :=
    Subgroup.relIndex_le_of_le_left inf_le_left Subgroup.index_ne_zero_of_finite
  have h3 := Subgroup.relIndex_mul_relIndex (F ⊓ A₀) A₀ V inf_le_right hA₀
  unfold secIdx
  rw [← hF]
  calc F.relIndex V ≤ (F ⊓ A₀).relIndex V := h2
    _ = (F ⊓ A₀).relIndex A₀ * A₀.relIndex V := h3.symm
    _ ≤ L.relIndex T * A₀.relIndex V := Nat.mul_le_mul_right _ h1
    _ = A₀.relIndex V * L.relIndex T := Nat.mul_comm _ _

theorem conjSub_eq_of_commute {g : G} {U : Subgroup G} (h : ∀ u ∈ U, g * u = u * g) :
    conjSub g U = U := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro hx
    have h1 := h _ hx
    have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e, h1]
    simpa using hx
  · intro hx
    have h1 := h x hx
    have e : g⁻¹ * x * g = x := by
      calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
        _ = g⁻¹ * (g * x) := by rw [h1]
        _ = x := by group
    rw [e]
    exact hx

theorem eq_of_card_le_two [Finite G] {K : Subgroup G} (hK : Nat.card K ≤ 2) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  by_contra hab
  have := Fintype.ofFinite K
  let s : Finset K := {⟨1, K.one_mem⟩, ⟨a, ha⟩, ⟨b, hb⟩}
  have hs : s.card = 3 := by
    have h1 : (⟨1, K.one_mem⟩ : K) ∉ ({⟨a, ha⟩, ⟨b, hb⟩} : Finset K) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hb1⟩
    have h2 : (⟨a, ha⟩ : K) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
    rw [Finset.card_insert_of_notMem h1, Finset.card_pair h2]
  have h3 := Finset.card_le_univ s
  rw [hs, ← Nat.card_eq_fintype_card] at h3
  omega

theorem card_zpowers_le_two [Finite G] {d : G} (hd : d ^ 2 = 1) :
    Nat.card (Subgroup.zpowers d) ≤ 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by norm_num) hd

end Twelve

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
