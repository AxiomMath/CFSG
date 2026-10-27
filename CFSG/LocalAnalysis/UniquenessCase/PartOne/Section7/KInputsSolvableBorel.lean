module

public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.RankThree.PartOne.CTP.StrongPGlue
import CFSG.RankThree.PartOne.CTP.OutEmbed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem normalizer_subgroupOf_le_of_isStronglyPEmbedded {X : Type} [Group X] {p : ℕ}
    [Fact p.Prime] {N K Q : Subgroup X} (hN : IsStronglyPEmbedded p N) (hQ : Q ≠ ⊥)
    (hQp : IsPGroup p Q) (hQN : Q ≤ N) (hQK : Q ≤ K) :
    Subgroup.normalizer ((Q.subgroupOf K : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K := by
  rw [← Subgroup.subgroupOf_normalizer_eq hQK]
  exact Subgroup.subgroupOf_mono K (hN.normalizer_le hQ hQp hQN)

theorem isSolvable_of_isCoatom_normalizer {X : Type} [Group X] {K N : Subgroup X}
    [K.Normal] (hKC : Subgroup.centralizer (K : Set X) = ⊥) (hout : Group.IsSolvable (Outer ↥K))
    {T : Subgroup ↥K} (hmax : IsCoatom (Subgroup.normalizer (T : Set ↥K)))
    (hsol : Group.IsSolvable (Subgroup.normalizer (T : Set ↥K)))
    (hle : Subgroup.normalizer (T : Set ↥K) ≤ N.subgroupOf K) (hne : N.subgroupOf K ≠ ⊤) :
    Group.IsSolvable ↥N := by
  have hNK : N.subgroupOf K = Subgroup.normalizer (T : Set ↥K) := by
    rcases hle.eq_or_lt with h | h
    · exact h.symm
    · exact absurd (hmax.2 _ h) hne
  haveI : Group.IsSolvable ↥(N.subgroupOf K) := hNK ▸ hsol
  let f : ↥(N.subgroupOf K) →* ↥N :=
    { toFun := fun x => ⟨(x : ↥K), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hfrange : f.range = K.subgroupOf N := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.1.2
    · intro hy
      exact ⟨⟨⟨(y : X), hy⟩, y.2⟩, rfl⟩
  let g : ↥N →* X ⧸ K := (QuotientGroup.mk' K).comp N.subtype
  have hker : g.ker = K.subgroupOf N := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  haveI : Group.IsSolvable (X ⧸ K) := by
    haveI := hout
    exact CFSG.RankThree.PartOne.CTP.solvable_quotient_of_outer K hKC
  exact Group.isSolvable_of_ker_le_range f g (by rw [hker, hfrange])

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
