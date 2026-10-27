module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts15b
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp StatedProj
  projectiveSpecialLinearGroupEquivStatedProj)

section Lie

variable {X Y : Type} [Group X] [Group Y]

theorem IsRankTwoLie2Derived.of_mulEquiv (e : X ≃* Y) (h : IsRankTwoLie2Derived X) :
    IsRankTwoLie2Derived Y := by
  rcases h with ⟨k, h⟩ | ⟨k, h⟩ | ⟨k, h⟩ | ⟨k, h⟩ | h | ⟨k, h⟩ | h | ⟨k, h⟩ | ⟨k, h⟩ | h
  · exact Or.inl ⟨k, IsPSL.of_mulEquiv e h⟩
  · exact Or.inr (Or.inl ⟨k, IsPSU.of_mulEquiv e h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨k, IsPSU.of_mulEquiv e h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, IsPSp4.of_mulEquiv e h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (IsAlt.of_mulEquiv e h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, IsG2.of_mulEquiv e h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (IsPSU.of_mulEquiv e h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, Is3D4.of_mulEquiv e h⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, Is2F4.of_mulEquiv e h⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (IsTits.of_mulEquiv e h)))))))))

@[expose] noncomputable def quotCenterEquiv (e : X ≃* Y) :
    X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem isRankTwoLie2Derived_SL3 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    IsRankTwoLie2Derived (Matrix.SpecialLinearGroup (Fin 3) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) := by
  refine Or.inl ⟨n, ⟨Nat.prime_two, hn, by norm_num, ?_, ?_⟩, K, inferInstance, inferInstance,
    hK, ⟨projectiveSpecialLinearGroupEquivStatedProj 3 K⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega

end Lie

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem rankTwo_L (hF : Facts15) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  obtain ⟨_, -, -, ⟨e⟩, hk⟩ := h1102 G T L I n h
  have hn : 2 ≤ n := h.one_lt
  rcases hk with ⟨K, _, _, hK, ⟨e'⟩, -⟩ | ⟨K, _, _, hK, ⟨e'⟩, -⟩ | ⟨K, _, _, hK, ⟨e'⟩, -⟩
  · exact IsRankTwoLie2Derived.of_mulEquiv (quotCenterEquiv (e.trans e')).symm
      (isRankTwoLie2Derived_SL3 (by omega) hK)
  · exact IsRankTwoLie2Derived.of_mulEquiv (quotCenterEquiv (e.trans e')).symm
      (hF.rankTwo K n hn hK).1
  · exact IsRankTwoLie2Derived.of_mulEquiv (quotCenterEquiv (e.trans e')).symm
      (hF.rankTwo K n hn hK).2

end CFSG.Quasithin.Vol2.Ch11.SecA
