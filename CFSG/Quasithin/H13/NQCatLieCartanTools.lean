module

public import CFSG.Quasithin.H13.NQCatLieCartan
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic

public section

namespace CFSG.Quasithin.H13.NQCat.LieCartan

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem lt_relIndex_of_hom [Finite G] {H C : Subgroup G} {A : Type*} [Group A] (χ : ↥H →* A)
    (hC : ∀ h : ↥H, (h : G) ∈ C → χ h = 1) (hχ : 3 < Nat.card χ.range) :
    3 < (H ⊓ C).relIndex H := by
  have hle : (H ⊓ C).subgroupOf H ≤ χ.ker := fun h hh => hC h hh.2
  have hpos : 0 < ((H ⊓ C).subgroupOf H).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h1 := Nat.le_of_dvd hpos (Subgroup.index_dvd_of_le hle)
  rw [Subgroup.index_ker] at h1
  exact lt_of_lt_of_le hχ h1

theorem card_le_relIndex_of_hom [Finite G] {H C : Subgroup G} {A : Type*} [Group A] (φ : A →* G)
    (hφH : ∀ a, φ a ∈ H) (hφC : ∀ a, φ a ∈ C → a = 1) :
    Nat.card A ≤ (H ⊓ C).relIndex H := by
  let ψ : A → ↥H ⧸ (H ⊓ C).subgroupOf H := fun a => (⟨φ a, hφH a⟩ : ↥H)
  have hψ : Function.Injective ψ := by
    intro a b hab
    have h1 := QuotientGroup.eq.1 hab
    have h2 : φ (a⁻¹ * b) ∈ C := by
      rw [map_mul, map_inv]
      exact h1.2
    have h3 := hφC _ h2
    rw [← one_mul b, ← mul_inv_cancel a, mul_assoc, h3, mul_one]
  exact Nat.card_le_card_of_injective ψ hψ

theorem torusConcl_of_le [Finite G] {C U H : Subgroup G} {alt : Prop} (hUC : U ≤ C)
    (hHC : H ≤ C) (hU : IsSylowTwoOf U C) (hHN : H ≤ Subgroup.normalizer (U : Set G))
    (hNH : C ⊓ Subgroup.normalizer (U : Set G) ≤ U ⊔ H) (hodd : Odd (Nat.card H))
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (h : ∀ E : Subgroup G, E ≤ U → IsElemAbelian 2 E → Nat.card E = 16 →
      E ≤ Subgroup.centralizer (U : Set G) →
      3 < (H ⊓ Subgroup.centralizer (E : Set G)).relIndex H ∧
        (H ⊓ Subgroup.centralizer (E : Set G) = ⊥ → alt)) :
    TorusConcl ↥C alt := by
  refine torusConcl_of_torus (U := U.subgroupOf C) (H := H.subgroupOf C)
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top hU) ?_ ?_ ?_ ?_ ?_
  · rw [← Subgroup.subgroupOf_normalizer_eq hUC]
    exact fun x hx => hHN hx
  · rw [← Subgroup.subgroupOf_normalizer_eq hUC, ← Subgroup.subgroupOf_sup hUC hHC]
    exact fun x hx => hNH ⟨x.2, hx⟩
  · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHC).toEquiv]
  · exact fun a ha b hb => Subtype.ext (hcomm _ ha _ hb)
  intro E hEU hE hE16 hEC
  have hEU' : E.map C.subtype ≤ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hEU hx
  have hEC' : E.map C.subtype ≤ Subgroup.centralizer (U : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := Subgroup.mem_centralizer_iff.1 (hEC hx) ⟨u, hUC hu⟩ hu
    exact congrArg Subtype.val h1
  have hcard : Nat.card (E.map C.subtype) = 16 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hE16
  obtain ⟨h1, h2⟩ := h _ hEU' (isElemAbelian_map hE _) hcard hEC'
  have heq : H.subgroupOf C ⊓ Subgroup.centralizer (E : Set ↥C) =
      (H ⊓ Subgroup.centralizer ((E.map C.subtype : Subgroup G) : Set G)).subgroupOf C := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    refine and_congr_right fun _ => ⟨fun hx => ?_, fun hx e he => Subtype.ext (hx _ ⟨e, he, rfl⟩)⟩
    rintro _ ⟨e, he, rfl⟩
    exact congrArg Subtype.val (hx e he)
  rw [heq, Subgroup.relIndex_subgroupOf hHC]
  refine ⟨h1, fun h0 => h2 ?_⟩
  have hd := Subgroup.subgroupOf_eq_bot.1 h0
  exact hd.eq_bot_of_le (inf_le_left.trans hHC)

end CFSG.Quasithin.H13.NQCat.LieCartan
