module

public import CFSG.Quasithin.EmptyFaithful.A38c17Gu2Struct
public import CFSG.Quasithin.EmptyFaithful.A38c17Gu2Gl2
public import CFSG.Quasithin.EmptyFaithful.A38c17CentralSup

public section

namespace CFSG.Quasithin.A38c17

open Matrix CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.Quasithin.A38c15 CFSG.QuasithinUnique.Vol2Native.A312L
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]

theorem isSolvable_subgroupOf_range_of_comap {G H : Type*} [Group G] [Group H] (f : H →* G)
    (N : Subgroup G) (h : Group.IsSolvable ↥(N.comap f)) :
    Group.IsSolvable ↥(N.subgroupOf f.range) := by
  have hsurj : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  have e : (N.comap f).map f.rangeRestrict = N.subgroupOf f.range := by
    have h0 : N.comap f = (N.subgroupOf f.range).comap f.rangeRestrict := rfl
    rw [h0, Subgroup.map_comap_eq_self_of_surjective hsurj]
  have h2 : Group.IsSolvable ↥((N.comap f).map f.rangeRestrict) :=
    Group.isSolvable_of_surjective (f := f.rangeRestrict.subgroupMap (N.comap f))
      (f.rangeRestrict.subgroupMap_surjective _)
  rw [e] at h2
  exact h2

theorem gu2_oddIndex (hR1 : GL2OddIndex) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ 2)
    (M : Subgroup ↥(GU (unitaryInvolution K p 1) 2)) (hodd : Odd M.index) :
    Group.IsSolvable ↥M ∨ IsSL2 p ↥(perfectCore M) := by
  have hK' : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK'
  have hF : Nat.card (fixedSubfield K p 1) = p := by simpa using card_fixedSubfield hK'
  let M' : Subgroup (GL (Fin 2) K) := M.map (GU (unitaryInvolution K p 1) 2).subtype
  have hM'le : M' ≤ GU (unitaryInvolution K p 1) 2 := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hodd' : Odd (M'.relIndex (GU (unitaryInvolution K p 1) 2)) := by
    have : M'.relIndex (GU (unitaryInvolution K p 1) 2) = M.index := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective Subtype.val_injective]
    rw [this]
    exact hodd
  have hZ : Subgroup.center (GL (Fin 2) K) ≤ Subgroup.center (GL (Fin 2) K) := le_rfl
  have h1 := GU_two_le_range_sup_center hζ0 hζ hK
  have h2 := hypEmbedGL_range_le_GU_sup_center hζ0 hζ hK
  have hoddA := sup_central_relIndex_odd hZ h1 h2 hM'le hodd'
  let M₂ : Subgroup (GL (Fin 2) (fixedSubfield K p 1)) :=
    (M' ⊔ Subgroup.center (GL (Fin 2) K)).comap (hypEmbedGL hζ0)
  have hM₂odd : Odd M₂.index := by
    rw [Subgroup.index_comap]
    exact hoddA
  by_cases hsolv : Group.IsSolvable ↥M₂
  · left
    have hM'solv : Group.IsSolvable ↥M' :=
      sup_central_isSolvable hZ h1 hM'le (isSolvable_subgroupOf_range_of_comap _ _ hsolv)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (M.equivMapOfInjective (GU (unitaryInvolution K p 1) 2).subtype
        Subtype.val_injective).toMonoidHom) (MulEquiv.injective _)
  · right
    have hp3 : p ≠ 3 := ne_three_of_not_isSolvable_gl2 hF M₂ hsolv
    have hSL : ∀ B : GL (Fin 2) (fixedSubfield K p 1),
        (B : Matrix (Fin 2) (Fin 2) (fixedSubfield K p 1)).det = 1 → B ∈ M₂ := fun B hB =>
      gl2OddIndex_of_card hR1 hp2 hF M₂ hM₂odd hsolv B hB
    have hXle : SU (unitaryInvolution K p 1) 2 ≤ M' ⊔ Subgroup.center (GL (Fin 2) K) := by
      intro x hx
      obtain ⟨A, hA⟩ := (hypEquiv hζ0 hζ).surjective ⟨x, hx⟩
      have hxA : x = hypEmbedGL hζ0 (Matrix.SpecialLinearGroup.toGL A) :=
        (congrArg Subtype.val hA).symm
      have hmem : Matrix.SpecialLinearGroup.toGL A ∈ M₂ := hSL _ A.2
      rw [hxA]
      exact hmem
    have hXperf := SU_two_commutator_eq hζ0 hζ hp2 hp3 hK
    have hX1 : SU (unitaryInvolution K p 1) 2 ≤ perfectCore M' :=
      le_perfectCore_of_le_sup_central hZ hXperf hXle
    have hX2 : perfectCore M' ≤ SU (unitaryInvolution K p 1) 2 :=
      (perfectCore_le_derivedSeriesOf M' 1).trans (commutator_le_SU hM'le)
    have hcore : perfectCore M' = SU (unitaryInvolution K p 1) 2 := le_antisymm hX2 hX1
    have hinj : ∀ x ∈ perfectCore M, ∀ y ∈ perfectCore M,
        (GU (unitaryInvolution K p 1) 2).subtype x = (GU (unitaryInvolution K p 1) 2).subtype y →
          x = y := fun x _ y _ h => Subtype.ext h
    exact ⟨((perfectCoreMapEquiv (GU (unitaryInvolution K p 1) 2).subtype M hinj).trans
      (MulEquiv.subgroupCongr hcore)).trans
      ((hypEquiv hζ0 hζ).symm.trans
        (CFSG.ClassicalModels.specialLinearFieldEquiv (fieldEquivZMod hF) (Fin 2)))⟩

end CFSG.Quasithin.A38c17
