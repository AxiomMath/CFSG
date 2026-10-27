module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA6
import CFSG.LocalAnalysis.StandardType.GGSixJNotA6A6Syl

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggB2der_noncyclic_three {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hJ : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) :
    ∃ S : Subgroup G, S ≤ J ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
  classical
  obtain ⟨e⟩ := ggB2der_label_iso_A6 hJ
  let π : ↥J →* ↥J ⧸ Subgroup.center ↥J := QuotientGroup.mk' (Subgroup.center ↥J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  obtain ⟨S₀, -, hS₀p, hS₀nc⟩ := exists_noncyclic_three_group_of_alt_six
    (G := ↥J ⧸ Subgroup.center ↥J) (J := ⊤) (L := ⊤) le_rfl (Subgroup.topEquiv.trans e)
  let S' : Subgroup ↥J := S₀.comap π
  let g : ↥S' →* ↥S₀ := (π.comp S'.subtype).codRestrict S₀ (fun x => x.2)
  have hg : Function.Surjective g := fun t => by
    obtain ⟨j, hj⟩ := hπ (t : ↥J ⧸ Subgroup.center ↥J)
    exact ⟨⟨j, by show π j ∈ S₀; rw [hj]; exact t.2⟩, Subtype.ext hj⟩
  let P : Sylow 3 ↥S' := default
  let T : Sylow 3 ↥S₀ := Sylow.mapSurjective hg P
  have hTtop : (T : Subgroup ↥S₀) = ⊤ := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := hS₀p.exists_card_eq
    have hT : Nat.card T = 3 ^ n := by
      rw [Sylow.card_eq_multiplicity, hn, Nat.factorization_pow]
      simp [Nat.Prime.factorization_self Nat.prime_three]
    exact Subgroup.eq_top_of_card_eq _ (by rw [hT, hn])
  have hcoe : (T : Subgroup ↥S₀) = (P : Subgroup ↥S').map g := by
    simpa only [T] using Sylow.coe_mapSurjective hg P
  let h : P →* ↥S₀ := g.comp (P : Subgroup ↥S').subtype
  have hh : Function.Surjective h := by
    intro t
    have ht : t ∈ (P : Subgroup ↥S').map g := by
      rw [← hcoe, hTtop]; exact Subgroup.mem_top t
    obtain ⟨p, hpP, hpg⟩ := ht
    exact ⟨⟨p, hpP⟩, hpg⟩
  have hPnc : ¬ IsCyclic P := by
    intro hP
    haveI : IsCyclic P := hP
    haveI : IsCyclic ↥S₀ := isCyclic_of_surjective h hh
    exact hS₀nc inferInstance
  let ι : ↥S' →* G := J.subtype.comp S'.subtype
  have hι : Function.Injective ι := J.subtype_injective.comp S'.subtype_injective
  refine ⟨(P : Subgroup ↥S').map ι, ?_, ?_, ?_⟩
  · rintro _ ⟨s, -, rfl⟩
    exact s.1.2
  · exact IsPGroup.of_equiv (Sylow.isPGroup' P) (Subgroup.equivMapOfInjective P ι hι)
  · intro hScyc
    haveI : IsCyclic ↥((P : Subgroup ↥S').map ι) := hScyc
    exact hPnc (isCyclic_of_surjective (Subgroup.equivMapOfInjective P ι hι).symm
      (Subgroup.equivMapOfInjective P ι hι).symm.surjective)

end CFSG.StandardType

end
