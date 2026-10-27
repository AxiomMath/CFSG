module

public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

section Solvable

variable {G : Type} [Group G]

theorem isSolvable_sup_of_le_normalizer_of_isSolvable {N R : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (N : Set G)) (hN : Group.IsSolvable ↥N)
    (hR' : Group.IsSolvable ↥R) : Group.IsSolvable ↥(N ⊔ R) := by
  set V := N ⊔ R with hV
  have hNV : N ≤ V := le_sup_left
  have hRV : R ≤ V := le_sup_right
  have hVN : V ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hR
  have hnorm : (N.subgroupOf V).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNV).mpr hVN
  set π := QuotientGroup.mk' (N.subgroupOf V) with hπ
  set f : R →* V ⧸ N.subgroupOf V := π.comp (Subgroup.inclusion hRV) with hf
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hv : (v : G) ∈ ((R ⊔ N : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact v.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right R N hR] at hv
    obtain ⟨t, ht, n, hn, htn⟩ := hv
    refine ⟨⟨t, ht⟩, ?_⟩
    change π (Subgroup.inclusion hRV ⟨t, ht⟩) = π v
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h : ((Subgroup.inclusion hRV ⟨t, ht⟩)⁻¹ * v : V) = (t⁻¹ * v : G) := rfl
    rw [h, ← htn, inv_mul_cancel_left]
    exact hn
  have hNVs : Group.IsSolvable ↥(N.subgroupOf V) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNV).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNV).injective
  have hquot : Group.IsSolvable (V ⧸ N.subgroupOf V) := Group.isSolvable_of_surjective hfs
  exact Group.isSolvable_of_ker_le_range (N.subgroupOf V).subtype π
    (by rw [hπ, QuotientGroup.ker_mk', Subgroup.range_subtype])

end Solvable

section Borel

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_inf_normalizer_of_isSylowTwoOf {S X : Subgroup G} (hS : IsSylowTwoOf S X) :
    Group.IsSolvable ↥(X ⊓ Subgroup.normalizer (S : Set G)) := by
  set B := X ⊓ Subgroup.normalizer (S : Set G) with hB
  have hSX : S ≤ X := hS.1
  have hSB : S ≤ B := le_inf hSX Subgroup.le_normalizer
  have hBX : B ≤ X := inf_le_left
  have hnorm : (S.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr inf_le_right
  have hSsolv : Group.IsSolvable ↥(S.subgroupOf B) := by
    have h2 : IsPGroup 2 ↥(S.subgroupOf B) :=
      (hS.2.1).of_injective (Subgroup.subgroupOfEquivOfLe hSB).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hSB).injective
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := h2.isNilpotent
    infer_instance
  have hodd : Odd (Nat.card (↥B ⧸ S.subgroupOf B)) := by
    have h1 : S.relIndex B * B.relIndex X = S.relIndex X :=
      Subgroup.relIndex_mul_relIndex S B X hSB hBX
    have h2 : ¬ 2 ∣ S.relIndex X := hS.2.2
    have h3 : ¬ 2 ∣ S.relIndex B := fun h => h2 (h1 ▸ h.mul_right _)
    have h4 : Nat.card (↥B ⧸ S.subgroupOf B) = S.relIndex B := rfl
    rw [h4]
    exact Nat.odd_iff.mpr (by omega)
  have hq : Group.IsSolvable (↥B ⧸ S.subgroupOf B) := CFSG.Milestones.odd_order_solvable hodd
  exact Group.isSolvable_of_ker_le_range (S.subgroupOf B).subtype (QuotientGroup.mk' (S.subgroupOf B))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_sup_of_isSylowTwoOf_of_normalizer {S X T : Subgroup G} (hS : IsSylowTwoOf S X)
    (hT : IsPGroup 2 ↥T) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) :
    Group.IsSolvable ↥((X ⊓ Subgroup.normalizer (S : Set G)) ⊔ T) := by
  have hB := isSolvable_inf_normalizer_of_isSylowTwoOf hS
  have hTB : T ≤ Subgroup.normalizer ((X ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) := by
    intro g hg
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hTX hg, ?_⟩
    exact Subgroup.le_normalizer (hTS hg)
  have hTs : Group.IsSolvable ↥T := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := hT.isNilpotent
    infer_instance
  exact isSolvable_sup_of_le_normalizer_of_isSolvable hTB hB hTs

theorem input14620Borel : Input14620Borel := by
  intro G _ _ K T hsyl _ _ _ _
  have hTK₀ : T ≤ Subgroup.normalizer (conjClosure K T : Set G) := le_normalizer_conjClosure K T
  have hS : IsSylowTwoOf (T ⊓ conjClosure K T) (conjClosure K T) :=
    isSylowTwoOf_inf_normal hsyl le_sup_left hTK₀
  refine isSolvable_sup_of_isSylowTwoOf_of_normalizer hS hsyl.2.1 hTK₀ ?_
  intro g hg
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hTK₀ hg⟩

end Borel

end CFSG.Quasithin
