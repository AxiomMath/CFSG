module

public import CFSG.RankThree.PartTwo.Sec8.Item87Proof88
import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofLink
import CFSG.RankThree.PartTwo.KFacts.K71Residual
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


@[expose] def KF88StepD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      ∃ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x ∧
        IsQuasisimple (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
          aschbacherSolvableCore 3
            (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) ∧
        (∃ m : ℕ, 1 ≤ m ∧
          IsType418 (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
            aschbacherSolvableCore 3
              (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) m) ∧
        KFacts.InducesStdKind
          (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) x .field

@[expose] def KF88StepOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G), Sec8Pair G A c L a b X 1 →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      ∃ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x ∧
        IsQuasisimple (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
          aschbacherSolvableCore 3
            (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) ∧
        (∃ m : ℕ, 1 ≤ m ∧
          IsType418 (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
            aschbacherSolvableCore 3
              (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) m) ∧
        KFacts.InducesStdKind
          (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) x .field ∧
        ¬ ⁅inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)),
            inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G))⁆ ≤
          inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G))

theorem kF88Step_of (hD : KF88StepD) (h1 : KF88StepOne) (hF : KF84Field) : KF88Step := by
  intro G _ _ A c L a b X n h Y hY hIJ x hx hxY
  obtain ⟨hbA, -, hn, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    exact h1 G A c L a b X h Y hY hIJ x hx hxY
  · obtain ⟨d, hdS, hdx, hUq, htypeU, hUx⟩ := hD G A c L a b X n h Y hY hIJ x hx hxY
    refine ⟨d, hdS, hdx, hUq, htypeU, hUx, ?_⟩
    have hAel := h.mem_partTwoF.1
    have ha3 : a ^ 3 = 1 := hAel.2 a h.a_mem
    set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hK
    set U := inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) with hU
    set T := inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({a} : Set G)) with hT
    have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
      (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
    have hKcb : K ≤ Subgroup.centralizer {c} ⊓ Subgroup.centralizer {b} :=
      le_inf ((Item87Proof.residual_le _).trans (inf_le_left.trans hLc))
        ((Item87Proof.residual_le _).trans inf_le_right)
    have hKd : K ≤ Subgroup.centralizer ({d} : Set G) := by
      intro k hk
      have hk' : k ∈ Subgroup.centralizer ((Subgroup.closure ({c, b} : Set G) : Subgroup G) :
          Set G) := by
        rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
        intro w hw
        obtain ⟨hkc, hkb⟩ := Subgroup.mem_inf.mp (hKcb hk)
        rcases hw with rfl | rfl
        · exact (Subgroup.mem_centralizer_singleton_iff.mp hkc).symm
        · exact (Subgroup.mem_centralizer_singleton_iff.mp hkb).symm
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hk' d hdS).symm
    have hKX : K ≤ X := h.pairRel.2.2.2.1
    have hTK : T ≤ K ⊓ Subgroup.centralizer ({a} : Set G) := Item87Proof.residual_le _
    have hTp : Group.IsPerfect T := Item87Proof.isPerfect_residual _
    have hTJ : T ≤ sec8J X a :=
      KFacts.le_inSubgroup_perfectResidual hTp
        (le_inf (hTK.trans (inf_le_left.trans hKX)) (hTK.trans inf_le_right))
    have hTU : T ≤ U :=
      KFacts.le_inSubgroup_perfectResidual hTp
        (le_inf (hTJ.trans (le_sup_right.trans hIJ)) (hTK.trans (inf_le_left.trans hKd)))
    have hTK' : T ≤ K := hTK.trans inf_le_left
    have hT1 : T ≠ ⊥ := by
      refine Item87Res2Proof.residual_centralizer_ne_bot_of_field hn2 ?_ ha3
        (hF G A c L a b X n h)
      rcases Item87Res2Proof.quot_cases_of_isGammaIndex h.isGammaIndex with ⟨hRee, hSU⟩ | hL2
      · exact Or.inl ⟨Item87Res2Proof.odd_of_isGammaTypeRee hRee, hSU⟩
      · exact Or.inr hL2
    intro hle
    apply Item87Res2Proof.not_le_theta_of_isPerfect hTp hT1
      (M := Subgroup.centralizer ({d} : Set G))
    calc T = ⁅T, T⁆ := (Item87Res2Proof.commutator_self_eq_of_isPerfect hTp).symm
      _ ≤ ⁅U, K⁆ := Subgroup.commutator_mono hTU hTK'
      _ ≤ _ := hle

end CFSG.RankThree.PartTwo.Sec8
