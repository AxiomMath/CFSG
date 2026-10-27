module

public import CFSG.GH74.ThompsonOrderFormula

public section

namespace CFSG.Monster.Existence

open Subgroup CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {G : Type*} [Group G]

theorem IsConj.subgroup_coe {H : Subgroup G} {a b : H} (h : IsConj a b) :
    IsConj (a : G) (b : G) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨c, by rw [← hc]; rfl⟩

theorem isConj_subgroup_of_isConj {H : Subgroup G} {t u : H} (htu : ¬ IsConj (t : G) (u : G))
    (hcl : ∀ x : H, orderOf x = 2 → IsConj t x ∨ IsConj u x) {a : H} (ha : orderOf a = 2)
    (hta : IsConj (t : G) (a : G)) : IsConj t a := by
  rcases hcl a ha with h | h
  · exact h
  · exact absurd (hta.trans (IsConj.subgroup_coe h).symm) htu

theorem thompsonPairCount_subgroup [Finite G] {H : Subgroup G} {t u v : H}
    (ht : orderOf t = 2) (hu : orderOf u = 2) (htu : ¬ IsConj (t : G) (u : G))
    (hcl : ∀ x : H, orderOf x = 2 → IsConj t x ∨ IsConj u x)
    (hpairs : ∀ p ∈ thompsonPairs (t : G) (u : G) (v : G), p.1 ∈ H ∧ p.2 ∈ H) :
    thompsonPairCount t u v = thompsonPairCount (t : G) (u : G) (v : G) := by
  have hord : ∀ {a : H} {s : H}, orderOf s = 2 → IsConj (s : G) (a : G) → orderOf a = 2 :=
    fun {a s} hs h => by
      rw [← Subgroup.orderOf_coe a, ← orderOf_eq_of_isConj h, Subgroup.orderOf_coe]
      exact hs
  let f : thompsonPairs t u v → thompsonPairs (t : G) (u : G) (v : G) := fun p =>
    ⟨((p.1.1 : G), (p.1.2 : G)), by
      obtain ⟨h1, h2, h3⟩ := mem_thompsonPairs.1 p.2
      refine mem_thompsonPairs.2 ⟨IsConj.subgroup_coe h1, IsConj.subgroup_coe h2, ?_⟩
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h3
      exact mem_zpowers_iff.2 ⟨k, by
        have := congrArg Subtype.val hk
        simpa using this⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun q => ?_⟩
    · have h := congrArg Subtype.val hpq
      simp only [f, Prod.mk.injEq] at h
      exact Subtype.ext (Prod.ext (Subtype.ext h.1) (Subtype.ext h.2))
    · obtain ⟨h1H, h2H⟩ := hpairs q.1 q.2
      obtain ⟨h1, h2, h3⟩ := mem_thompsonPairs.1 q.2
      have ha : orderOf (⟨q.1.1, h1H⟩ : H) = 2 := hord ht h1
      have hb : orderOf (⟨q.1.2, h2H⟩ : H) = 2 := hord hu h2
      have h1' : IsConj t ⟨q.1.1, h1H⟩ := isConj_subgroup_of_isConj htu hcl ha h1
      have h2' : IsConj u ⟨q.1.2, h2H⟩ := by
        rcases hcl _ hb with h | h
        · exact absurd ((IsConj.subgroup_coe h).trans h2.symm) htu
        · exact h
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h3
      refine ⟨⟨(⟨q.1.1, h1H⟩, ⟨q.1.2, h2H⟩), mem_thompsonPairs.2 ⟨h1', h2', ?_⟩⟩, ?_⟩
      · refine mem_zpowers_iff.2 ⟨k, Subtype.ext ?_⟩
        simpa using hk
      · rfl
  exact Nat.card_congr (Equiv.ofBijective f hf)

theorem eq_top_of_two_classes [Finite G] (H : Subgroup G) {t u : G} (htH : t ∈ H) (huH : u ∈ H)
    (ht : orderOf t = 2) (hu : orderOf u = 2) (htu : ¬ IsConj t u)
    (hH : ∀ y ∈ H, orderOf y = 2 → (∃ h ∈ H, h * t * h⁻¹ = y) ∨ ∃ h ∈ H, h * u * h⁻¹ = y)
    (hG : ∀ y : G, orderOf y = 2 → ∃ g : G, g * y * g⁻¹ ∈ H)
    (hCt : centralizer {t} ≤ H) (hCu : centralizer {u} ≤ H) : H = ⊤ := by
  set t' : H := ⟨t, htH⟩
  set u' : H := ⟨u, huH⟩
  have ht' : orderOf t' = 2 := by rw [orderOf_mk, ht]
  have hu' : orderOf u' = 2 := by rw [orderOf_mk, hu]
  have hclH : ∀ x : H, orderOf x = 2 → IsConj t' x ∨ IsConj u' x := by
    intro x hx
    have hx' : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    rcases hH x x.2 hx' with ⟨h, hh, hht⟩ | ⟨h, hh, hhu⟩
    · exact Or.inl (isConj_iff.2 ⟨⟨h, hh⟩, Subtype.ext hht⟩)
    · exact Or.inr (isConj_iff.2 ⟨⟨h, hh⟩, Subtype.ext hhu⟩)
  have htu' : ¬ IsConj t' u' := fun h => htu (IsConj.subgroup_coe h)
  have hclG : ∀ y : G, orderOf y = 2 → IsConj t y ∨ IsConj u y := by
    intro y hy
    obtain ⟨g, hg⟩ := hG y hy
    have hgy : orderOf (g * y * g⁻¹) = 2 := by
      rw [← orderOf_eq_of_isConj (isConj_iff.2 ⟨g, rfl⟩), hy]
    have hconj : IsConj (g * y * g⁻¹) y := (isConj_iff.2 ⟨g, rfl⟩).symm
    rcases hH _ hg hgy with ⟨h, -, hht⟩ | ⟨h, -, hhu⟩
    · exact Or.inl ((isConj_iff.2 ⟨h, hht⟩).trans hconj)
    · exact Or.inr ((isConj_iff.2 ⟨h, hhu⟩).trans hconj)
  obtain ⟨hGcard, hGpairs⟩ :=
    CFSG.GH74.thompson_two_involution_class_order_formula ht hu htu hclG
  obtain ⟨hHcard, -⟩ :=
    CFSG.GH74.thompson_two_involution_class_order_formula ht' hu' htu' hclH
  have hcent : ∀ {s : G} (hs : s ∈ H), centralizer {s} ≤ H →
      Nat.card (centralizer ({(⟨s, hs⟩ : H)} : Set H)) = Nat.card (centralizer ({s} : Set G)) := by
    intro s hs hC
    have : centralizer ({(⟨s, hs⟩ : H)} : Set H) = (centralizer ({s} : Set G)).subgroupOf H := by
      ext x
      simp only [mem_centralizer_singleton_iff, mem_subgroupOf]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [this, Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv]
  have hp : ∀ v : G, (v = t ∨ v = u) → ∀ p ∈ thompsonPairs t u v, p.1 ∈ H ∧ p.2 ∈ H := by
    intro v hv p hpv
    obtain ⟨h1, h2⟩ := hGpairs v hv p hpv
    rcases hv with rfl | rfl
    · exact ⟨hCt h1, hCt h2⟩
    · exact ⟨hCu h1, hCu h2⟩
  have hrt := thompsonPairCount_subgroup (v := t') ht' hu' htu hclH (hp t (Or.inl rfl))
  have hru := thompsonPairCount_subgroup (v := u') ht' hu' htu hclH (hp u (Or.inr rfl))
  have hcard : Nat.card H = Nat.card G := by
    rw [hHcard, hGcard, hcent huH hCu, hcent htH hCt, hrt, hru]
  exact card_eq_iff_eq_top H |>.1 hcard

end CFSG.Monster.Existence
