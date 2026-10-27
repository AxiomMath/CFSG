module

public import CFSG.Quasithin.EmptyFaithful.SBd8Trio
public import CFSG.Quasithin.Background.GoldschmidtS146RLatSmall

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

section A6

open CFSG.QuasithinUnique.Borel252.A6

theorem mem_normalizer_sup {G : Type*} [Group G] {H K : Subgroup G} {x : G}
    (hH : x ∈ Subgroup.normalizer (H : Set G)) (hK : x ∈ Subgroup.normalizer (K : Set G)) :
    x ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  have key : ∀ z : G, z ∈ Subgroup.normalizer (H : Set G) → z ∈ Subgroup.normalizer (K : Set G) →
      ∀ y ∈ H ⊔ K, z * y * z⁻¹ ∈ H ⊔ K := by
    intro z hzH hzK
    have hle : H ⊔ K ≤ (H ⊔ K).comap (MulAut.conj z).toMonoidHom :=
      sup_le (fun y hy => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hzH y).mp hy))
        (fun y hy => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hzK y).mp hy))
    exact fun y hy => hle hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hH hK y, fun hy => ?_⟩
  have := key x⁻¹ ((Subgroup.normalizer (H : Set G)).inv_mem hH)
    ((Subgroup.normalizer (K : Set G)).inv_mem hK) _ hy
  simpa [mul_assoc] using this

theorem normalizer_D0_subgroupOf :
    Subgroup.normalizer ((D0.subgroupOf A6s : Subgroup ↥A6s) : Set ↥A6s) = D0.subgroupOf A6s := by
  rw [← Subgroup.subgroupOf_normalizer_eq D0_le_A6]
  ext x
  exact norm_D0 x x.2

theorem Sa_ne_Sb : Sa ≠ Sb := by
  intro h
  have hle : Sa ≤ D0 := by
    intro x hx
    have hxA : x ∈ A6s := Sa_le_A6 hx
    have hNa : x ∈ Subgroup.normalizer (VA : Set P6) := (norm_VA x hxA).2 hx
    have hNb : x ∈ Subgroup.normalizer (VB : Set P6) := (norm_VB x hxA).2 (h ▸ hx)
    have hND : x ∈ Subgroup.normalizer (D0 : Set P6) := by
      rw [← sup_VA_VB]
      exact mem_normalizer_sup hNa hNb
    exact (norm_D0 x hxA).1 hND
  have h1 : Nat.card Sa ≤ Nat.card D0 := Subgroup.card_le_of_le hle
  rw [CFSG.Quasithin.GoldS146R.card_Sa, card_D0] at h1
  omega

theorem a6_overgroups_D0 (Y : Subgroup ↥A6s) (hY : D0.subgroupOf A6s ≤ Y) :
    Y = D0.subgroupOf A6s ∨ Y = Sa.subgroupOf A6s ∨ Y = Sb.subgroupOf A6s ∨ Y = ⊤ := by
  have hinj : Function.Injective A6s.subtype := A6s.subtype_injective
  have hD : D0 ≤ Y.map A6s.subtype := fun d hd =>
    ⟨⟨d, D0_le_A6 hd⟩, hY (by rwa [Subgroup.mem_subgroupOf]), rfl⟩
  have hA : Y.map A6s.subtype ≤ A6s := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hback : ∀ H : Subgroup P6, Y.map A6s.subtype = H → Y = H.subgroupOf A6s := by
    intro H hH
    change Y = H.comap A6s.subtype
    rw [← hH, Subgroup.comap_map_eq_self_of_injective hinj]
  rcases six_overgroups _ hD hA with h | h | h | h
  · exact Or.inl (hback _ h)
  · exact Or.inr (Or.inl (hback _ h))
  · exact Or.inr (Or.inr (Or.inl (hback _ h)))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [hback _ h]
    exact Subgroup.subgroupOf_self A6s

theorem trioShape_a6_D0 : TrioShape ↥A6s (D0.subgroupOf A6s) := by
  have hc : ∀ {H : Subgroup P6}, H ≤ A6s → Nat.card (H.subgroupOf A6s) = Nat.card H :=
    fun h => Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have hU : Nat.card (D0.subgroupOf A6s) = 8 := by rw [hc D0_le_A6, card_D0]
  have hSa : Nat.card (Sa.subgroupOf A6s) = 24 := by
    rw [hc Sa_le_A6, CFSG.Quasithin.GoldS146R.card_Sa]
  have hSb : Nat.card (Sb.subgroupOf A6s) = 24 := by
    rw [hc Sb_le_A6, CFSG.Quasithin.GoldS146R.card_Sb]
  have hne : ∀ {H : Subgroup P6}, Nat.card H = 24 → H ≤ A6s → H.subgroupOf A6s ≠ ⊤ := by
    intro H hH _ h
    have h1 : Nat.card (H.subgroupOf A6s) = Nat.card ↥A6s := by rw [h, Subgroup.card_top]
    rw [hc ‹H ≤ A6s›, hH, card_A6] at h1
    omega
  refine ⟨normalizer_D0_subgroupOf, Sa.subgroupOf A6s, Sb.subgroupOf A6s, ?_,
    hne (CFSG.Quasithin.GoldS146R.card_Sa) Sa_le_A6, hne (CFSG.Quasithin.GoldS146R.card_Sb) Sb_le_A6,
    lt_of_le_of_ne (fun x hx => D0_le_Sa hx) (fun h => by rw [h, hSa] at hU; omega),
    lt_of_le_of_ne (fun x hx => D0_le_Sb hx) (fun h => by rw [h, hSb] at hU; omega),
    by rw [hSa, hU], by rw [hSb, hU], a6_overgroups_D0⟩
  intro h
  apply Sa_ne_Sb
  have := congrArg (Subgroup.map A6s.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le Sa_le_A6, Subgroup.map_subgroupOf_eq_of_le Sb_le_A6] at this

end A6

section A6Abstract

variable {X : Type} [Group X] [Finite X]

theorem trioShape_A6 (h : IsAlt 6 X) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) : TrioShape X U := by
  obtain ⟨e⟩ := h
  exact TrioShape.of_equiv_sylow e.symm CFSG.Quasithin.GoldS146R.isSylowTwoOf_D0 trioShape_a6_D0 hU

end A6Abstract

end SBd8

end CFSG.Quasithin
