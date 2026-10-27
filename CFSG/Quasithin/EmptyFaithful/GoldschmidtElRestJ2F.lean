module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtElRestJ2
public import CFSG.Quasithin.EmptyFaithful.ModHGen
public import CFSG.Sporadic.J2

public section

namespace CFSG.Quasithin.ModH

open CFSG.Blueprint CFSG.Open CFSG.QuasithinUnique CFSG.ComponentClassification
  CFSG.ComponentClassification.J2Cover CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Sporadic.J2 CFSG.Sporadic.Th.Native

theorem centerSmall_of_center_data {G : Type} [Group G] [Finite G] {T : Subgroup G} {z : G}
    (hT : IsSylowTwoOf T ⊤)
    (hz : ∀ c ∈ T, (∀ t ∈ T, c * t = t * c) → c = 1 ∨ c = z) : CenterSmall G :=
  centerSmall_of_one hT fun x y hx hy hxc hyc => by
    rcases hz x hx hxc with h | h
    · exact Or.inl h
    · rcases hz y hy hyc with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (h.trans h'.symm))

theorem centerSmall_j2_P :
    CenterSmall ↥J2Cover.P := by
  obtain ⟨Q, zJ, hQ, hQz⟩ := j2_center_data
  have key : ∃ (T : Subgroup ↥J2Cover.P) (z : ↥J2Cover.P), IsSylowTwoOf T ⊤ ∧ IsPGroup 2 T ∧
      ∀ c ∈ T, (∀ t ∈ T, c * t = t * c) → c = 1 ∨ c = z :=
    @exists_sylow_center_of_equiv ↥J ↥J2Cover.P _ _
      (CFSG.Sporadic.Bridge.J2.nativeEquiv.symm.trans nativeEquivP) Q zJ hQ hQz
  obtain ⟨T, z, hT, -, hz⟩ := key
  exact centerSmall_of_center_data hT hz

theorem centerSmall_j2 :
    CenterSmall (NativeSporadic.Carrier .J2) := by
  have : Finite (NativeSporadic.Carrier .J2) := (CFSG.Sporadic.J2.fam_j2_simplicity).1
  obtain ⟨Q, zJ, hQ, hQz⟩ := j2_center_data
  have key : ∃ (T : Subgroup (NativeSporadic.Carrier .J2)) (z : NativeSporadic.Carrier .J2),
      IsSylowTwoOf T ⊤ ∧ IsPGroup 2 T ∧
        ∀ c ∈ T, (∀ t ∈ T, c * t = t * c) → c = 1 ∨ c = z :=
    @exists_sylow_center_of_equiv ↥J (NativeSporadic.Carrier .J2) _ _
      CFSG.Sporadic.Bridge.J2.nativeEquiv.symm Q zJ hQ hQz
  obtain ⟨T, z, hT, -, hz⟩ := key
  exact centerSmall_of_center_data hT hz

theorem sylowFactsJ2_unfolded :
    CenterSmall (NativeSporadic.Carrier .J2) ∧
      ∀ (T : Sylow 2 (NativeSporadic.Carrier .J2)) (α : MulAut (NativeSporadic.Carrier .J2)),
        (∀ t ∈ (T : Subgroup (NativeSporadic.Carrier .J2)), α t = t) →
          ∃ z : (T : Subgroup (NativeSporadic.Carrier .J2)),
            z ∈ Subgroup.center (T : Subgroup (NativeSporadic.Carrier .J2)) ∧
              ∀ g : NativeSporadic.Carrier .J2, α g = (z : NativeSporadic.Carrier .J2) * g *
                (z : NativeSporadic.Carrier .J2)⁻¹ := by
  have key : ∀ T : Subgroup (NativeSporadic.Carrier .J2), IsSylowTwoOf T ⊤ →
      ∀ α : MulAut (NativeSporadic.Carrier .J2), (∀ t ∈ T, α t = t) →
        ∃ z ∈ T, (∀ t ∈ T, z * t = t * z) ∧ ∀ g, α g = z * g * z⁻¹ :=
    pointwise_of_equiv nativeEquivP (pointwise_j2_P centerSmall_j2_P)
  refine ⟨centerSmall_j2, fun T α hα => ?_⟩
  have : Finite (NativeSporadic.Carrier .J2) := (CFSG.Sporadic.J2.fam_j2_simplicity).1
  have hT : IsSylowTwoOf (T : Subgroup (NativeSporadic.Carrier .J2)) ⊤ :=
    K1.isSylowTwoOf_top_iff.2 ⟨T.isPGroup', T.not_dvd_index⟩
  obtain ⟨z, hzT, hzc, hz⟩ := key _ hT α hα
  exact ⟨⟨z, hzT⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hzc g g.2).symm, hz⟩

end CFSG.Quasithin.ModH
