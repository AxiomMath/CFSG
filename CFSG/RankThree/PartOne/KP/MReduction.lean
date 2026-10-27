module

public import CFSG.RankThree.PartOne.KS.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint.NativeSporadic (Carrier)

theorem exists_section_of_section {G : Type} [Group G] (H : Subgroup G) (K : Subgroup H)
    [K.Normal] {T : Type} [Group T] (φ : H ⧸ K ≃* T) (A : Subgroup T) (N : Subgroup A)
    [N.Normal] {B : Type} [Group B] (ψ : A ⧸ N ≃* B) :
    ∃ (H' : Subgroup G) (K' : Subgroup H') (_ : K'.Normal), Nonempty ((H' ⧸ K') ≃* B) := by
  let q : H →* T := φ.toMonoidHom.comp (QuotientGroup.mk' K)
  have hq : Function.Surjective q := φ.surjective.comp (QuotientGroup.mk'_surjective K)
  let HA : Subgroup H := A.comap q
  let π0 : HA →* A := q.subgroupComap A
  have hπ0 : Function.Surjective π0 := by
    intro a
    obtain ⟨h, hh⟩ := hq (a : T)
    refine ⟨⟨h, ?_⟩, Subtype.ext hh⟩
    rw [Subgroup.mem_comap]
    change q h ∈ A
    rw [hh]
    exact a.2
  let H' : Subgroup G := HA.map H.subtype
  let e : H' ≃* HA := (HA.equivMapOfInjective H.subtype H.subtype_injective).symm
  let π : H' →* B := (ψ.toMonoidHom.comp (QuotientGroup.mk' N)).comp (π0.comp e.toMonoidHom)
  have hπ : Function.Surjective π := by
    refine ψ.surjective.comp ((QuotientGroup.mk'_surjective N).comp (hπ0.comp e.surjective))
  exact ⟨H', π.ker, inferInstance, ⟨QuotientGroup.quotientKerEquivOfSurjective π hπ⟩⟩

@[expose] def SimplePresentationMHasBSection : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.M) →
      ∃ (A : Subgroup T) (N : Subgroup A) (_ : N.Normal), Nonempty ((A ⧸ N) ≃* Carrier .B)

theorem simplePresentationM_sections_of_B_section (hB : SectionsForceEvenRankFour (Carrier .B))
    (hM : SimplePresentationMHasBSection) : SimplePresentationMSectionsForceEvenRankFour := by
  intro G _ _ H K _ T _ _ _ hnab ⟨φ⟩ hTM
  obtain ⟨A, N, hN, ⟨ψ⟩⟩ := hM T hnab hTM
  obtain ⟨H', K', hK', ⟨χ⟩⟩ := exists_section_of_section H K φ A N ψ
  exact hB G H' K' ⟨χ⟩

end CFSG.RankThree.PartOne
