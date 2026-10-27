module

public import CFSG.Quasithin.EmptyFaithful.ModHBr
public import CFSG.Quasithin.EmptyFaithful.ModGRed2

public section

namespace CFSG.Quasithin.ModH

open CFSG.Quasithin CFSG.QuasithinUnique

theorem isSolvable_sup_of_le_normalizer {G : Type} [Group G] [Finite G] {Y S : Subgroup G}
    (hY : Group.IsSolvable ↥Y) (hS : IsPGroup 2 ↥S) (hN : S ≤ Subgroup.normalizer (Y : Set G)) :
    Group.IsSolvable ↥(Y ⊔ S) := by
  have hYZ : Y ≤ Y ⊔ S := le_sup_left
  have hSZ : S ≤ Y ⊔ S := le_sup_right
  have hZN : Y ⊔ S ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hN
  have hnorm : (Y.subgroupOf (Y ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYZ).2 hZN
  have hsolvN : Group.IsSolvable ↥(Y.subgroupOf (Y ⊔ S)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hYZ).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYZ).injective
  have hSp : IsPGroup 2 ↥(S.subgroupOf (Y ⊔ S)) :=
    hS.of_injective (Subgroup.subgroupOfEquivOfLe hSZ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hSZ).injective
  let ρ : ↥(S.subgroupOf (Y ⊔ S)) →* ↥(Y ⊔ S) ⧸ Y.subgroupOf (Y ⊔ S) :=
    (QuotientGroup.mk' (Y.subgroupOf (Y ⊔ S))).comp (S.subgroupOf (Y ⊔ S)).subtype
  have hρ : Function.Surjective ρ := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨p, hp, t, ht, hz⟩ := ModG.Red.exists_mul_of_mem_sup' hN z.2
    refine ⟨⟨⟨t, hSZ ht⟩, Subgroup.mem_subgroupOf.mpr ht⟩, ?_⟩
    show QuotientGroup.mk (⟨t, hSZ ht⟩ : ↥(Y ⊔ S)) = QuotientGroup.mk z
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (((⟨t, hSZ ht⟩ : ↥(Y ⊔ S))⁻¹ * z : ↥(Y ⊔ S)) : G) = t⁻¹ * p * t := by
      show t⁻¹ * (z : G) = _
      rw [hz]
      group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.1 (hN (S.inv_mem ht)) p).1 hp
    simpa using this
  have hq : IsPGroup 2 (↥(Y ⊔ S) ⧸ Y.subgroupOf (Y ⊔ S)) := hSp.of_surjective ρ hρ
  have : Group.IsNilpotent (↥(Y ⊔ S) ⧸ Y.subgroupOf (Y ⊔ S)) := hq.isNilpotent
  have : Group.IsSolvable (↥(Y ⊔ S) ⧸ Y.subgroupOf (Y ⊔ S)) := inferInstance
  exact Group.isSolvable_of_ker_le_range (Y.subgroupOf (Y ⊔ S)).subtype
    (QuotientGroup.mk' (Y.subgroupOf (Y ⊔ S))) (by simp)

theorem solvNine_of_sylow {X : Type} [Group X] [Finite X] {S₀ : Subgroup X}
    (hS₀ : IsSylowTwoOf S₀ ⊤)
    (h : ∀ Y : Subgroup X, S₀ ≤ Subgroup.normalizer (Y : Set X) → Group.IsSolvable ↥Y →
      9 ∣ Nat.card ↥Y → False) : SolvNine X := by
  intro P Y hP hN hs h9
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hS₀ hP
  let φ : X ≃* X := MulAut.conj g⁻¹
  refine h (Y.map φ.toMonoidHom) ?_ ?_ ?_
  · intro s hs'
    have hPs : g * s * g⁻¹ ∈ P := by rw [← hg]; exact ⟨s, hs', rfl⟩
    have h1 := (R3c11.mem_normalizer_map_equiv_iff φ Y (g * s * g⁻¹)).mpr (hN hPs)
    have h2 : φ (g * s * g⁻¹) = s := by simp [φ, mul_assoc]
    rwa [h2] at h1
  · have := hs
    exact Group.isSolvable_of_surjective (f := φ.toMonoidHom.subgroupMap Y)
      (φ.toMonoidHom.subgroupMap_surjective Y)
  · rw [Nat.card_congr (Y.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv.symm]
    exact h9

end CFSG.Quasithin.ModH
