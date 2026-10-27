module

public import CFSG.Quasithin.EmptyFaithful.SzN28PMain
public import CFSG.Quasithin.Background.G9StmtsModels
public import CFSG.Quasithin.EmptyFaithful.SzN28PCase
public import CFSG.Quasithin.EmptyFaithful.SzN28PDefs
public import CFSG.Quasithin.EmptyFaithful.SzN28PSvMain
public import CFSG.Quasithin.EmptyFaithful.SzN28PTwMain
public import CFSG.Quasithin.EmptyFaithful.SzN28Solv
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabInputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11

namespace SzPS8

section Strong

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def G112Concl13S (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  G112Concl13 Γ ∧
    (∃ Z : Subgroup ↥Γ, Z.Normal ∧ Nat.card ↥Z = 3 ∧
      ∀ N : Subgroup ↥Γ, N.Normal → N ≠ ⊥ → Z ≤ N) ∧
    ∃ N : Subgroup ↥Γ, N.Normal ∧ N.index = 2 ∧
      IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22

@[expose] def G112Concl7S (Γ X : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  G112Concl7 Γ X ∧
    IsNaturalMatrixModule ((genFittingFStar ↥Γ).map Γ.subtype)
      (CFSG.Assembly.LowTwoRank.StatedOmega
        (CFSG.Assembly.LowTwoRank.StatedQuadPlus 2 (GaloisField 2 2)))

@[expose] def G112Concl6U33S (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  G112Concl6U33 Γ ∧
    IsG2NaturalModule Γ ⁅CFSG.Open.quasithinG2 (GaloisField 2 1),
      CFSG.Open.quasithinG2 (GaloisField 2 1)⁆

@[expose] def G112ConclusionFixS (B : LinearMap.BilinForm (ZMod 2) V)
    (Γ X : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  (G112Concl1 Γ ∨ G112Concl2 Γ ∨ G112Concl3 Γ ∨ G112Concl4 Γ ∨ G112Concl5 B Γ ∨ G112Concl6 Γ ∨
    G112Concl7S Γ X ∨ G112Concl8 B Γ X ∨ G112Concl9 Γ ∨ G112Concl10 Γ X ∨ G112Concl11 Γ ∨
    G112Concl12 Γ X ∨ G112Concl13S Γ) ∨ G112Concl8S8 B Γ X ∨ G112Concl6U33S Γ

end Strong

@[expose] def TheoremG112FixS : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G111Hyp B Γ v₁ W X X₀ → IsQuotientOfSQTKTauCeti ↥Γ → G112ConclusionFixS B Γ X

theorem G112ConclusionFixS.toFix {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {Γ X : Subgroup (GLV V)}
    (h : G112ConclusionFixS B Γ X) : G112ConclusionFix B Γ X := by
  rcases h with (c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11 | c12 | c13) | c8s | c6u
  · exact Or.inl (Or.inl c1)
  · exact Or.inl (Or.inr (Or.inl c2))
  · exact Or.inl (Or.inr (Or.inr (Or.inl c3)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl c4))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c5)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c6))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c7.1)))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c8))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl c9)))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl c10))))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl c11)))))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl c12))))))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr c13.1))))))))))))
  · exact Or.inr (Or.inl c8s)
  · exact Or.inr (Or.inr c6u.1)

theorem theoremG112Fix_of_S (h : TheoremG112FixS) : TheoremG112Fix :=
  fun V _ _ _ B Γ v₁ W X X₀ hyp hq => (h V B Γ v₁ W X X₀ hyp hq).toFix

@[expose] def Lemma14315Excl7S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    ¬ IsMulCommutative ↥(uOfL22 T M) → ∀ D : HatModel T M, ∀ g : G,
      GoodElt128 T (yOfL22 T M) g →
      G112Concl7S (D.img (mcOf T)) (D.img (rconj (Hyp1281Two.wOfU T M) g)) →
        Group.IsSolvable ↥(D.img (mcOf T))

@[expose] def Lemma14315Excl6U33S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    ¬ IsMulCommutative ↥(uOfL22 T M) → ∀ D : HatModel T M,
      G112Concl6U33S (D.img (mcOf T)) → Group.IsSolvable ↥(D.img (mcOf T))

@[expose] def Lemma14315Excl13S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    ¬ IsMulCommutative ↥(uOfL22 T M) → ∀ D : HatModel T M,
      G112Concl13S (D.img (mcOf T)) → Group.IsSolvable ↥(D.img (mcOf T))

structure Lemma14315ResidueS : Prop where
  c2 : Lemma14315Excl2
  c4 : Lemma14315Excl4
  c5 : Lemma14315Excl5
  c6 : Lemma14315Excl6
  c6U33 : Lemma14315Excl6U33S
  c7 : Lemma14315Excl7S
  c11 : Lemma14315Excl11
  c13 : Lemma14315Excl13S

theorem lemma14315SolvableS8_of_residueS (hG : TheoremG112FixS) (h11 : StageLemma14111)
    (h113 : StageLemma14113) (h35 : Lemma1435) (r : Lemma14315ResidueS) :
    Lemma14315SolvableS8 := by
  intro G _ _ T M hyp hnot hnab D
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  obtain ⟨a, haV, haZ⟩ := h1281.exists_mem_VZ_not_mem
  obtain ⟨g, hg⟩ := h1281.exists_goodElt_L
  have key : G112ConclusionFixS D.B (D.img (mcOf T)) (D.img (rconj (Hyp1281Two.wOfU T M) g)) :=
    hG D.V D.B _ (D.π a) _ _ _ (h1281.lemma_12_8_12_three hnab hg D haV haZ)
      (h1281.isQuotientOfSQTK_img D)
  rcases key with
    (c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11 | c12 | c13) | c8s8 | c6u
  · exact Or.inl (SzN28P.isSolvable_of_concl1 c1)
  · exact Or.inl (r.c2 G T M hyp hnot hnab D c2)
  · exact Or.inl (SzN28P.isSolvable_of_concl3 c3)
  · exact Or.inl (r.c4 G T M hyp hnot hnab D c4)
  · exact Or.inl (r.c5 G T M hyp hnot hnab D c5)
  · exact Or.inl (r.c6 G T M hyp hnot hnab D c6)
  · exact Or.inl (r.c7 G T M hyp hnot hnab D g hg c7)
  · exact (SzN28P.not_concl8 h11 h113 h35 hyp hnot hnab D hg c8).elim
  · exact (SzN28P.not_concl9 h11 h113 h35 hyp hnot hnab D c9).elim
  · exact (SzN28P.not_concl10 h11 h113 h35 hyp hnot hnab D _ c10).elim
  · exact Or.inl (r.c11 G T M hyp hnot hnab D c11)
  · exact (SzN28P.not_concl12 h11 h113 hyp hnab D hg c12).elim
  · exact Or.inl (r.c13 G T M hyp hnot hnab D c13)
  · exact Or.inr ⟨g, hg, c8s8⟩
  · exact Or.inl (r.c6U33 G T M hyp hnot hnab D c6u)

end SzPS8

end CFSG.Quasithin
