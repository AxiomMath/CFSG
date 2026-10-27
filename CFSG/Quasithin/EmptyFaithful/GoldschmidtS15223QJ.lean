module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223QBase
public import CFSG.Quasithin.EmptyFaithful.S151S9P2A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_sup_le_Q {K S I X₀ Mc : Subgroup G} (hS : IsSylowTwoOf S I) (hKI : K ≤ I)
    (hKX : K ≤ Subgroup.normalizer (X₀ : Set G)) (hSX : S ≤ Subgroup.normalizer (X₀ : Set G))
    (hKMc : K ≤ Mc) (hSMc : S ≤ Mc) (hA : IsSylowTwoOf (S ⊓ X₀) X₀) :
    pCoreOf 2 (X₀ ⊔ pCoreOf 2 (K ⊔ S)) ≤ pCoreOf 2 (K ⊔ S) := by
  set Q := pCoreOf 2 (K ⊔ S) with hQ
  set A := S ⊓ X₀ with hAdef
  have hQS : Q ≤ S := pCoreOf_sup_le hS hKI
  have hKSN : K ⊔ S ≤ Subgroup.normalizer (X₀ : Set G) := sup_le hKX hSX
  have hKSMc : K ⊔ S ≤ Mc := sup_le hKMc hSMc
  set M₀ := X₀ ⊓ Mc with hM₀
  have hAM₀ : A ≤ M₀ := le_inf inf_le_right (inf_le_left.trans hSMc)
  have hM₀X : M₀ ≤ X₀ := inf_le_left
  have hM₀N : K ⊔ S ≤ Subgroup.normalizer (M₀ : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKSN hg, Subgroup.le_normalizer (hKSMc hg)⟩
  have hQN : K ⊔ S ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 (K ⊔ S)
  set N' := M₀ ⊔ Q with hN'
  have hN'N : K ⊔ S ≤ Subgroup.normalizer (N' : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hM₀N hg, hQN hg⟩
  set P₀ := A ⊔ Q with hP₀
  have hP₀S : P₀ ≤ S := sup_le inf_le_left hQS
  have hP₀2 : IsPGroup 2 P₀ := hS.2.1.to_le hP₀S
  have hP₀A : P₀ ⊓ X₀ = A :=
    le_antisymm (le_inf (inf_le_left.trans hP₀S) inf_le_right) (le_inf le_sup_left inf_le_right)
  have hP₀AM : P₀ ⊓ M₀ = A := le_antisymm (le_inf (inf_le_left.trans hP₀S)
    (inf_le_right.trans hM₀X)) (le_inf le_sup_left hAM₀)
  have hXP : X₀ ⊔ P₀ = X₀ ⊔ Q := le_antisymm
    (sup_le le_sup_left (sup_le (inf_le_right.trans le_sup_left) le_sup_right))
    (sup_le le_sup_left (le_sup_right.trans le_sup_right))
  have hMP : M₀ ⊔ P₀ = N' := le_antisymm
    (sup_le le_sup_left (sup_le (hAM₀.trans le_sup_left) le_sup_right))
    (sup_le le_sup_left (le_sup_right.trans le_sup_right))
  have hSylX : IsSylowTwoOf P₀ (X₀ ⊔ Q) := by
    rw [← hXP]
    exact HSRuLoc.Lift.isSylowTwoOf_sup (K := X₀) (L := X₀) le_rfl (hP₀S.trans hSX) hP₀2
      (by rw [hP₀A]; exact hA)
  have hAM : IsSylowTwoOf A M₀ := SBd7.isSylowTwoOf_of_le_of_le' hA hAM₀ hM₀X
  have hSylM : IsSylowTwoOf P₀ N' := by
    rw [← hMP]
    exact HSRuLoc.Lift.isSylowTwoOf_sup (K := M₀) (L := M₀) le_rfl (hP₀S.trans
      (le_sup_right.trans hM₀N)) hP₀2
      (by rw [hP₀AM]; exact hAM)
  set O := pCoreOf 2 (X₀ ⊔ Q) with hO
  have hOP : O ≤ P₀ := pCoreOf_two_le_of_isSylowTwoOf hSylX
  have hP₀N' : P₀ ≤ N' := sup_le (hAM₀.trans le_sup_left) le_sup_right
  have hN'X : N' ≤ X₀ ⊔ Q := sup_le (hM₀X.trans le_sup_left) le_sup_right
  have hON : O ≤ pCoreOf 2 N' :=
    le_pCoreOf_of_le_normalizer 2 (hOP.trans hP₀N') (hN'X.trans (le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  have hN'P : pCoreOf 2 N' ≤ P₀ := pCoreOf_two_le_of_isSylowTwoOf hSylM
  have hnorm : K ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 N' : Set G) :=
    hN'N.trans (normalizer_le_normalizer_pCoreOf 2 N')
  have hle : pCoreOf 2 N' ≤ Q :=
    le_pCoreOf_of_le_normalizer 2 ((hN'P.trans hP₀S).trans le_sup_right) hnorm
      (pCoreOf_isPGroup 2 _)
  exact hON.trans hle

omit [Finite G] in
theorem exists_isMaxElemAbelian_not_le {Q O : Subgroup G} (h : ¬ thompsonJ Q ≤ O) :
    ∃ A : Subgroup G, IsMaxElemAbelian Q A ∧ ¬ A ≤ O := by
  by_contra hcon
  push Not at hcon
  exact h (iSup₂_le fun A hA => hcon A hA)

end S15223

end CFSG.Quasithin
