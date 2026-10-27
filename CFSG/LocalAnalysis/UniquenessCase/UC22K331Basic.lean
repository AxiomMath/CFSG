module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InS3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.Blueprint (LieModel)

@[expose] def K331At (L : Type) [Group L] [Finite L] : Prop :=
  ∀ T : Subgroup L, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
    ∀ K : Subgroup L, IsAlt (Bar2 K) 8 → T ≤ Subgroup.normalizer (K : Set L) →
      K = ⊤ ∨ LieModel L .PSL 5 2 1 ∨ IsSpor L .M24 ∨ IsSpor L .J4

@[expose] def K331Idx (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
    CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 → Nonempty (L ≃* i.Group) → K331At L

@[expose] def K331Fam (F : TauCeti.CFSGIndex → Prop) : Prop := ∀ i, F i → K331Idx i

theorem K331Fam.union {F G : TauCeti.CFSGIndex → Prop} (hF : K331Fam F) (hG : K331Fam G) :
    K331Fam fun i => F i ∨ G i :=
  fun i hi => hi.elim (hF i) (hG i)

theorem k331_of_fam (h : K331Fam fun _ => True) : K331 := by
  intro L _ _ hs hc h3 T hT K hK hTK
  obtain ⟨i, e⟩ := hc
  exact h i trivial L hs h3 e T hT K hK hTK

section Order

variable {L : Type} [Group L] [Finite L]

theorem nat_card_alt_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem dvd_card_of_isAlt_eight {K : Subgroup L} (hK : IsAlt (Bar2 K) 8) :
    20160 ∣ Nat.card K := by
  obtain ⟨e⟩ := hK
  have h1 : Nat.card (Bar2 K) = 20160 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alt_eight]
  exact h1 ▸ Subgroup.card_quotient_dvd_card _

theorem k331At_of_card (h : ¬ 20160 ∣ Nat.card L ∨ Nat.card L = 20160) : K331At L := by
  intro T _ K hK _
  have hKd := dvd_card_of_isAlt_eight hK
  have hKL : Nat.card K ∣ Nat.card L := Subgroup.card_subgroup_dvd_card K
  rcases h with h | h
  · exact absurd (hKd.trans hKL) h
  · left
    have hle : Nat.card K ≤ Nat.card L := Nat.le_of_dvd Nat.card_pos hKL
    have hge : 20160 ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos hKd
    exact Subgroup.eq_top_of_card_eq K (by omega)

end Order

theorem K331Idx.of_card {i : TauCeti.CFSGIndex}
    (h : ¬ 20160 ∣ Nat.card i.Group ∨ Nat.card i.Group = 20160) : K331Idx i := by
  intro L _ _ _ _ ⟨e⟩
  refine k331At_of_card ?_
  rwa [Nat.card_congr e.toEquiv]

theorem K331Idx.of_three_le {i : TauCeti.CFSGIndex}
    (h : ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* i.Group) →
      3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S)) : K331Idx i := by
  intro L _ _ _ h2 he
  have := h L he
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
