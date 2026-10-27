module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KModels
public import CFSG.RankThree.PartTwo.Sec12.Hering129KOrders
public import CFSG.RankThree.PartTwo.Sec21.Item21Res6ProofNoField
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace Hering129KOut



section Pure

theorem isG2D4_congr {X X' : Type} [Group X] [Group X'] (e : X ≃* X') {r : TauCeti.PrimePower}
    {δ : ℕ} (h : IsG2D4 X r δ) : IsG2D4 X' r δ := by
  rcases h with ⟨h1, hq, ⟨f⟩⟩ | ⟨h3, hr, ⟨f⟩⟩
  · exact Or.inl ⟨h1, hq, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨h3, hr, ⟨e.symm.trans f⟩⟩

theorem aschbacherSolvableCore_eq_pCore_two {Y : Type} [Group Y] [Finite Y]
    {r : TauCeti.PrimePower} {δ : ℕ} (h : IsG2D4 (Y ⧸ CFSG.pCore 2 Y) r δ) :
    aschbacherSolvableCore 3 Y = CFSG.pCore 2 Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hθsol, hθchar, -, -, -, -, hpc⟩ :=
    solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  haveI hS : IsSimpleGroup (Y ⧸ CFSG.pCore 2 Y) := Hering129KModels.isSimpleGroup_of_isG2D4 h
  apply le_antisymm
  · set P := CFSG.pCore 2 Y with hP
    haveI : P.Normal := CFSG.pCore_normal
    haveI := hθsol
    set M := (aschbacherSolvableCore 3 Y).map (QuotientGroup.mk' P) with hM
    haveI hMn : M.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    have hMsolv : Group.IsSolvable M :=
      solvable_of_surjective ((QuotientGroup.mk' P).subgroupMap_surjective _)
    rcases hS.eq_bot_or_eq_top_of_normal M with h0 | h1
    · intro y hy
      have : QuotientGroup.mk' P y ∈ M := Subgroup.mem_map_of_mem _ hy
      rw [h0, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff y).mp this
    · exfalso
      haveI : Group.IsSolvable (Y ⧸ P) :=
        solvable_of_surjective (f := M.subtype) (fun y => ⟨⟨y, h1 ▸ trivial⟩, rfl⟩)
      haveI : Group.IsPerfect (Y ⧸ P) := Hering129KModels.isPerfect_of_isG2D4 h
      haveI : Nontrivial (Y ⧸ P) := hS.toNontrivial
      exact Group.IsPerfect.not_isSolvable _ ‹_›
  · exact hpc 2 Nat.prime_two (by norm_num)


end Pure


theorem inducesStdKind_of_outer {G : Type} [Group G] [Finite G] {Y : Subgroup G} {e : G}
    {r : TauCeti.PrimePower} {δ : ℕ}
    (h : IsG2D4 (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) r δ) (hr4 : 4 ≤ r.card) (hrp3 : r.p ≠ 3)
    (hrδ : δ = 3 → r.p = 2) (he3 : e ^ 3 = 1) (hout : Sec4.InducesOuterTheta e Y) :
    KFacts.InducesStdKind Y e .field ∨ KFacts.InducesStdKind Y e .graphField := by
  rcases h with ⟨hδ, hX⟩ | ⟨hδ, hr, ⟨f⟩⟩
  · obtain ⟨K, hK1, hK2, hK, hKp, ⟨eK⟩⟩ := Hering129KModels.exists_adjoint_model hX
    left
    have hK3 : ringChar K ≠ 3 := hKp ▸ hrp3
    have hK4 : 4 ≤ Nat.card K := hK ▸ hr4
    exact KFacts.InducesStdKind.g2 K hK3 hK4
      (KFacts.inducesKindG2_field Y hK3 hK4 he3 hout eK)
  · obtain ⟨K, hK1, hK2, σ, hK, hσ, ⟨eK⟩⟩ := Hering129KModels.exists_d4_model f
    right
    have hp2 : r.p = 2 := hrδ hδ
    have hrc : r.card = 2 ^ r.exponent := by rw [TauCeti.PrimePower.card_def, hp2]
    have hK' : Nat.card K = (2 ^ r.exponent) ^ 3 := by rw [hK, hrc]
    have hσ' : ∀ c, σ c = c ^ 2 ^ r.exponent := fun c => by rw [hσ c, hrc]
    have hf1 : 1 ≤ r.exponent := r.exponent_pos
    exact KFacts.InducesStdKind.triality r.exponent hf1 K hK' σ hσ'
      (KFacts.inducesKindTriality_graphField hf1 hK' hσ' Y he3 hout eK)

theorem not_nonempty_projSL_two_eight {X : Type} [Group X] {r : TauCeti.PrimePower} {δ : ℕ}
    (h : IsG2D4 X r δ) (hr : 4 ≤ r.card) :
    ¬ Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3)) := by
  rintro ⟨e⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Sec11.KSListsProof.card_projSL_two_mul (GaloisField 2 3)
  have hK : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  rw [hK] at h1
  have h2 : Nat.card (CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3)) = 504 := by
    have : Nat.gcd 2 (8 - 1) = 1 := by norm_num
    rw [this, mul_one] at h1
    omega
  have h3 := Hering129KOrders.lt_card_of_isG2D4 h (by omega) (fun _ => by omega)
  rw [Nat.card_congr e.toEquiv, h2] at h3
  exact lt_irrefl _ h3

theorem not_isSLThreePiAt_of_isG2D4 {X : Type} [Group X] {r : TauCeti.PrimePower} {δ : ℕ}
    (h : IsG2D4 X r δ) (q : ℕ) : ¬ Sec4.IsSLThreePiAt X q := by
  intro hq
  have h3 := card_center_eq_three_of_isSLThreePi (X := X) ⟨q, hq⟩
  rw [Hering129KModels.center_eq_bot_of_isG2D4 h] at h3
  simp at h3

theorem not_inducesOuterTheta_of_core (h1134N : Sec11.Item1134E27N)
    (h1134ST : Sec21.Item1134E27ST) {G : Type} [Group G] [Finite G] (hst : PartTwoStanding G)
    {A : Subgroup G} (hAF : A ∈ partTwoF G) (hAS : A ∈ partTwoS G)
    (hFE : partTwoF G = partTwoE G) (h27 : Nat.card A = 27) {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 x) (hAN : A ≤ Subgroup.normalizer (Y : Set G))
    (hAC : A ⊓ Sec4.thetaQuotCentralizer Y = Subgroup.zpowers x)
    {r : TauCeti.PrimePower} {δ : ℕ} (h : IsG2D4 (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) r δ)
    (hr4 : 4 ≤ r.card) (hrp3 : r.p ≠ 3) (hrδ : δ = 3 → r.p = 2) {e : G} (heA : e ∈ A) :
    ¬ Sec4.InducesOuterTheta e Y := by
  intro hout
  have he3 : e ^ 3 = 1 := hAF.1.2 e heA
  have hle : A ⊓ Sec4.thetaQuotCentralizer Y ≤ Subgroup.zpowers x := hAC.le
  have hstar : Y ∈ lStarAt A x :=
    ⟨Sec6.mem_lStar_of_inf_le_zpowers hAF.1 hxA hx1 hY hAN hle, hY⟩
  have hsc : Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) =
      (Subgroup.zpowers x : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf hAN, hAC]
  have hL8 := not_nonempty_projSL_two_eight h hr4
  have hS8 := not_isSLThreePiAt_of_isG2D4 h 8
  have hnf : ¬ KFacts.InducesStdKind Y e .field ∧ ¬ KFacts.InducesStdKind Y e .graphField := by
    by_cases hT : A ∈ partTwoT G
    · exact h1134ST G A x Y hst hAS hT h27 hxA hx1 hstar hsc
        (Or.inr (Or.inr ⟨hL8, hS8⟩)) hFE.symm e heA
    · exact h1134N G A x Y hst hAF hT h27 hxA hx1 hstar hsc hL8 hS8 (fun _ => hFE.symm) e heA
  rcases inducesStdKind_of_outer h hr4 hrp3 hrδ he3 hout with hk | hk
  · exact hnf.1 hk
  · exact hnf.2 hk

end Hering129KOut

end CFSG.RankThree.PartTwo.Sec12
