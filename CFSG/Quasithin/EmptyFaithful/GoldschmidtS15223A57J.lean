module

public import CFSG.Quasithin.Background.GoldschmidtTDC111Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223QJ

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

namespace S15223

variable {G : Type} [Group G] [Finite G]

theorem not_thompsonJ_le_pCoreOf_of_le {H Mc X Q Q₁ : Subgroup G} (hU : IsUniqueM H Mc)
    (hQ2 : IsPGroup 2 Q) (hQ0 : Q ≠ ⊥) (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hO : pCoreOf 2 (X ⊔ Q₁) ≤ Q) (hX : ¬ X ≤ Mc) :
    ¬ thompsonJ Q ≤ pCoreOf 2 (X ⊔ Q₁) := by
  intro hJ
  have hJe := B6.thompsonJ_eq_of_le hJ hO
  have hXN : X ≤ Subgroup.normalizer (thompsonJ Q : Set G) := by
    rw [← hJe]
    exact (le_sup_left.trans (le_normalizer_pCoreOf 2 (X ⊔ Q₁))).trans
      (normalizer_le_normalizer_thompsonJ (pCoreOf 2 (X ⊔ Q₁)))
  have hHJ : H ≤ Subgroup.normalizer (thompsonJ Q : Set G) :=
    hHQ.trans (normalizer_le_normalizer_thompsonJ Q)
  have hJ2 : IsPGroup 2 (thompsonJ Q) := hQ2.to_le (B6.thompsonJ_le Q)
  have hle := normalizer_le_of_normal hU hJ2 (S1414.thompsonJ_ne_bot hQ2 hQ0) hHJ
  exact hX (hXN.trans hle)

theorem exists_isMaxElemAbelian_not_le_pCoreOf {H Mc X Q Q₁ : Subgroup G} (hU : IsUniqueM H Mc)
    (hQ2 : IsPGroup 2 Q) (hQ0 : Q ≠ ⊥) (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hO : pCoreOf 2 (X ⊔ Q₁) ≤ Q) (hX : ¬ X ≤ Mc) :
    ∃ A : Subgroup G, IsMaxElemAbelian Q A ∧ ¬ A ≤ pCoreOf 2 (X ⊔ Q₁) :=
  exists_isMaxElemAbelian_not_le (not_thompsonJ_le_pCoreOf_of_le hU hQ2 hQ0 hHQ hO hX)

omit [Finite G] in
theorem isSylowTwoOf_sup_inf {S X Q₁ : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSX : S ≤ Subgroup.normalizer (X : Set G)) (hQS : Q₁ ≤ S)
    (hA : IsSylowTwoOf (S ⊓ X) X) : IsSylowTwoOf ((S ⊓ X) ⊔ Q₁) (X ⊔ Q₁) := by
  have hP₀S : (S ⊓ X) ⊔ Q₁ ≤ S := sup_le inf_le_left hQS
  have hP₀2 : IsPGroup 2 ((S ⊓ X) ⊔ Q₁ : Subgroup G) := hS2.to_le hP₀S
  have hP₀A : ((S ⊓ X) ⊔ Q₁) ⊓ X = S ⊓ X :=
    le_antisymm (le_inf (inf_le_left.trans hP₀S) inf_le_right) (le_inf le_sup_left inf_le_right)
  have hXP : X ⊔ ((S ⊓ X) ⊔ Q₁) = X ⊔ Q₁ := le_antisymm
    (sup_le le_sup_left (sup_le (inf_le_right.trans le_sup_left) le_sup_right))
    (sup_le le_sup_left (le_sup_right.trans le_sup_right))
  rw [← hXP]
  exact HSRuLoc.Lift.isSylowTwoOf_sup (K := X) (L := X) le_rfl (hP₀S.trans hSX) hP₀2
    (by rw [hP₀A]; exact hA)

theorem sup_inf_centralizer_blockU {X Q₁ P₀ : Subgroup G} (hX : IsShort2 X)
    (hQ₁ : Q₁ ≤ Subgroup.normalizer (X : Set G)) (hP₀ : IsSylowTwoOf P₀ (X ⊔ Q₁))
    (hQP : Q₁ ≤ P₀) :
    (X ⊔ Q₁) ⊓ Subgroup.centralizer (blockU X : Set G) = pCoreOf 2 (X ⊔ Q₁) := by
  have hXN : X ⊔ Q₁ ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer hQ₁
  have hblk : IsBlock2 (X ⊔ Q₁) X :=
    ⟨hX, le_sup_left, Subgroup.Normal.isSubnormal
      (Subgroup.normal_subgroupOf_of_le_normalizer hXN)⟩
  have hdec : ∀ h ∈ X ⊔ Q₁, ∃ k ∈ X, ∃ s ∈ P₀, h = k * s := by
    intro h hh
    have hh' : h ∈ (X : Set G) * (Q₁ : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left X Q₁ hQ₁]
      exact hh
    obtain ⟨k, hk, q, hq, rfl⟩ := hh'
    exact ⟨k, hk, q, hQP hq, rfl⟩
  exact asc111Statement_holds G (X ⊔ Q₁) X P₀ Unit (fun _ => X) inferInstance (fun _ => hblk)
    (fun i j hij => absurd (Subsingleton.elim i j) hij) (by simp) le_sup_left hP₀ hdec

theorem not_le_centralizer_blockU_of_not_le_pCoreOf {X Q₁ P₀ A : Subgroup G} (hX : IsShort2 X)
    (hQ₁ : Q₁ ≤ Subgroup.normalizer (X : Set G)) (hP₀ : IsSylowTwoOf P₀ (X ⊔ Q₁))
    (hQP : Q₁ ≤ P₀) (hAle : A ≤ X ⊔ Q₁) (hA : ¬ A ≤ pCoreOf 2 (X ⊔ Q₁)) :
    ¬ A ≤ Subgroup.centralizer (blockU X : Set G) := fun h =>
  hA ((le_inf hAle h).trans (sup_inf_centralizer_blockU hX hQ₁ hP₀ hQP).le)

end S15223

end CFSG.Quasithin
