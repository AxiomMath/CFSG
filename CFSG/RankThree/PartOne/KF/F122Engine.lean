module

public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.S11c.Sec66TDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.PartOne.Sec66T

theorem false_of_localRank_fixed {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    {α : MulAut T} (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) (N : Subgroup T)
    (hNfix : ∀ y ∈ N, α y = y) (hN : 2 ≤ localRank p ↥N) (hLRA : LocalRankAut p T α) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, hU2, hU1, E, hEN, hE, hEc⟩ :=
    exists_elemAbelian_of_le_localRank hp (by omega : 1 ≤ 2) hN
  refine hLRA hαp hαinn (E.map N.subtype) ?_ ?_ ?_ (U.map N.subtype) ?_ (hU2.map N.subtype) ?_ ?_
  · exact IsElementaryAbelian.map_subtype
  · rw [Subgroup.card_map_of_injective N.subtype_injective, hEc]
  · rintro _ ⟨y, -, rfl⟩
    exact hNfix y y.2
  · intro h
    apply hU1
    have := (Subgroup.map_eq_bot_iff _).mp h
    rw [Subgroup.ker_subtype] at this
    exact eq_bot_iff.mpr this
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, hu, (hNfix u u.2).symm⟩
  · rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have hmemU : ∀ s : N, (s : T) ∈ U.map N.subtype ↔ s ∈ U := fun s => by
      constructor
      · rintro ⟨u, hu, hus⟩
        have : u = s := Subtype.ext hus
        rwa [← this]
      · intro hs
        exact ⟨s, hs, rfl⟩
    have heN : (e : T) ∈ N := e.2
    by_cases htN : t ∈ N
    · have h1 := (Subgroup.mem_normalizer_iff.mp (hEN he)) ⟨t, htN⟩
      exact (hmemU ⟨t, htN⟩).trans (h1.trans (hmemU (e * ⟨t, htN⟩ * e⁻¹)).symm)
    · have h2 : (e : T) * t * (e : T)⁻¹ ∉ N := by
        intro h
        apply htN
        have := N.mul_mem (N.mul_mem (N.inv_mem heN) h) heN
        simpa [mul_assoc] using this
      constructor
      · rintro ⟨u, -, hut⟩
        exact absurd (hut ▸ u.2) htN
      · rintro ⟨u, -, hut⟩
        exact absurd (hut ▸ u.2) h2

end CFSG.RankThree.PartOne
