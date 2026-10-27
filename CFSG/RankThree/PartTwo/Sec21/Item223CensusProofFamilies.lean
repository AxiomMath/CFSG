module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofClassical
public import CFSG.RankThree.PartTwo.Sec4.Item413Orders
public import CFSG.RankThree.PartTwo.Census.OddClassical.LinearTwo
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
public import CFSG.RankThree.CentralLiftU.UnitaryThreeEven
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def Census223Fact (S : Type) [Group S] : Prop :=
  CFSG.pRank 3 (S ⧸ Subgroup.center S) ≤ 2 ∨ NoL2Inner223 S

@[expose] def Census223RankTwoOdd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p →
    (∀ (X : Type) [Group X], Blueprint.ChevalleyExceptionalModel X .G2 p 1 →
      Census223Fact X) ∧
    Census223Fact (projSp 2 (GaloisField p 1)) ∧
    (p % 3 = 1 → Census223Fact (projSU 4 p 1)) ∧
    (p % 3 = 2 → Census223Fact (projSL 4 (GaloisField p 1)))

@[expose] def Census223RankTwoEven : Prop :=
  (∀ n : ℕ, 1 ≤ n → Census223Fact (projSp 2 (GaloisField 2 n))) ∧
  (∀ n : ℕ, 1 ≤ n → Even n → Census223Fact (projSU 4 2 n)) ∧
  (∀ (X : Type) [Group X] (f : ℕ),
    (Blueprint.ChevalleyExceptionalModel X .G2 2 f ∨
      Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f ∨
      Blueprint.ReeTitsModel X .twistedF4 2 f ∨ Blueprint.ReeTitsModel X .Tits 2 f) →
    Census223Fact X)

@[expose] def Census223A9 : Prop :=
  Census223Fact (alternatingGroup (Fin 9))

@[expose] def Census223Sporadic : Prop :=
  (∀ s ∈ Sec4.sporadics46, Census223Fact (Blueprint.NativeSporadic.Carrier s)) ∧
  ∀ s ∈ Sec4.sporadicCovers46, ∀ (Y : Type) [Group Y] [Finite Y],
    Sec4.IsExtOf Y (Blueprint.NativeSporadic.Carrier s) (Multiplicative (ZMod 3)) →
      Census223Fact Y

@[expose] def Census223Sp62 : Prop :=
  Census223Fact (projSp 3 (GaloisField 2 1))

@[expose] def Census223CharThree : Prop :=
  Census223Fact (projSL 3 (GaloisField 3 2)) ∧ Census223Fact (projSU 3 3 1) ∧
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card (Subgroup.center Y) ≤ 3 →
    (Blueprint.ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .G2 3 1 ∨
      Nonempty (Y ⧸ Subgroup.center Y ≃* projSU 4 3 1)) → Census223Fact Y

namespace Item223CensusProof

open CFSG.GorensteinWalter in
theorem noL2Inner223_PSL2_charThree {K : Type} [Field K] [Finite K] [CharP K 3] :
    NoL2Inner223 (PSL2 K) := by
  intro Kb m a ⟨eK⟩ hm1 _ haZ ha3 hcomm
  have hZ := CFSG.GorensteinWalter.psl2_center_eq_bot K
  rw [hZ, Subgroup.mem_bot] at haZ ha3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha : orderOf a = 3 := orderOf_eq_prime ha3 haZ
  have h2 : 2 ∣ Nat.card Kb := by
    rw [Nat.card_congr eK.toEquiv, card_projSL_two m (by omega)]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have : Finite Kb := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_congr eK.toEquiv, card_projSL_two m (by omega)]
    have : 0 < (2 ^ m) ^ 2 - 1 := by
      have : 1 < (2 ^ m) ^ 2 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
      omega
    positivity)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact Census.not_commute_PSL_two_char_three a t ha (by rwa [Subgroup.orderOf_coe])
    (hcomm t t.2)

theorem le_center_of_card_eq_three {Y : Type} [Group Y] {N : Subgroup Y} [hN : N.Normal]
    (h3 : Nat.card N = 3) [Group.IsPerfect (Y ⧸ N)] : N ≤ Subgroup.center Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic N := isCyclic_of_prime_card h3
  have hNc : ∀ a b : N, a * b = b * a := fun a b => hcyc.isMulCommutative.is_comm.comm a b
  have hAut : ∀ σ τ : MulAut N, σ * τ = τ * σ := fun σ τ => by
    apply (IsCyclic.mulAutMulEquiv (G := N)).injective
    rw [map_mul, map_mul, mul_comm]
  set φ : Y →* MulAut N := MulAut.conjNormal
  have hcomm : commutator Y ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, commutatorElement_def]
    simp only [map_mul, map_inv]
    rw [hAut (φ a) (φ b)]
    group
  have hNk : N ≤ φ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    ext x
    change n * (x : Y) * n⁻¹ = x
    have h1 : n * (x : Y) = x * n := congrArg Subtype.val (hNc ⟨n, hn⟩ x)
    rw [h1, mul_inv_cancel_right]
  have htop : commutator Y ⊔ N = ⊤ := by
    have hmap : (commutator Y).map (QuotientGroup.mk' N) = ⊤ := by
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), ← commutator_def,
        Group.IsPerfect.commutator_eq_top]
    have h := congrArg (Subgroup.comap (QuotientGroup.mk' N)) hmap
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : y ∈ φ.ker := sup_le hcomm hNk (htop ▸ Subgroup.mem_top y)
  have h1 := congrArg (fun σ : MulAut N => ((σ ⟨n, hn⟩ : N) : Y)) (MonoidHom.mem_ker.mp hy)
  change y * n * y⁻¹ = n at h1
  calc y * n = y * n * y⁻¹ * y := by group
    _ = n * y := by rw [h1]

theorem card_quotient_center_dvd_of_isExtOf {Y : Type} {S : Type*} [Group Y] [Group S]
    [Group.IsPerfect S] (h : Sec4.IsExtOf Y S (Multiplicative (ZMod 3))) :
    Nat.card (Y ⧸ Subgroup.center Y) ∣ Nat.card S := by
  obtain ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ := h
  have h3 : Nat.card N = 3 := by
    rw [Nat.card_congr eN.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  have : Group.IsPerfect (Y ⧸ N) := Group.IsPerfect.ofSurjective (f := eQ.symm.toMonoidHom)
    eQ.symm.surjective
  rw [← Nat.card_congr eQ.toEquiv]
  exact Sec4.card_quotient_center_dvd (le_center_of_card_eq_three h3)

theorem isPerfect_alternatingGroup_seven : Group.IsPerfect (alternatingGroup (Fin 7)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  exact isPerfect_of_isSimpleGroup
    ⟨⟨Equiv.swap 0 1 * Equiv.swap 0 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
      ⟨Equiv.swap 0 1 * Equiv.swap 0 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
      by decide⟩

end Item223CensusProof

open Item223CensusProof

namespace Config223

variable {Y : Type} [Group Y] {E D : Subgroup (MulAut Y)} {Kb : Subgroup Y} {m : ℕ}

theorem false_of_fact [Finite Y] (h : Config223 Y E D Kb m) {S : Type} [Group S] (e : Y ≃* S)
    (hS : Census223Fact S) : False := by
  have : Finite S := Finite.of_equiv _ e.toEquiv
  rcases hS with hS | hS
  · exact h.false_of_pRank (Sec4.quotientCenterCongr e) hS
  · exact h.false_of_noL2Inner e hS

end Config223

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial in
theorem innerCensus223_of (hOdd : Census223RankTwoOdd)
    (hEven : Census223RankTwoEven) (hA9 : Census223A9) (hSpor : Census223Sporadic)
    (hSp62 : Census223Sp62) (hThree : Census223CharThree) : InnerCensus223 := by
  refine innerCensus223_of_config fun Y _ _ E D Kb m hL h => ?_
  rcases hL with ⟨p, e, _, hp2, he, ⟨eY⟩⟩ | ⟨p, e, _, hp3, he1, he2, hSL | ⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩⟩ |
      ⟨p, _, hp3, hG2 | ⟨⟨eY⟩⟩ | ⟨hp1, ⟨eY⟩⟩ | ⟨hp2, ⟨eY⟩⟩⟩ |
      (⟨n, hn, ⟨eY⟩⟩ | hA6 | hA7) | (⟨s, hs, ⟨eY⟩⟩ | ⟨s, hs, hext⟩) |
      (hchev | ⟨n, hn, hSL⟩) | (⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩) |
      ((⟨e, he1, he2, ⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩⟩) | ⟨⟨eY⟩⟩ | ⟨hZ3, hG23 | ⟨⟨eY⟩⟩⟩)
  ·
    exfalso
    by_cases hp3 : p = 3
    · subst hp3
      exact h.false_of_noL2Inner (eY.trans (Sec4.projSLEquivPSLn 2 _))
        noL2Inner223_PSL2_charThree
    · exact h.false_of_projSL_two hp3 he eY
  ·
    exfalso
    obtain ⟨K, _, _, ⟨hK, ⟨eY⟩⟩ | ⟨hK, ⟨eY⟩⟩⟩ := hSL
    · exact h.false_of_statedSL_three (Sec4.three_ne_zero_of_card Fact.out (by omega) hK) eY
    · have hU : UnitaryFieldData p e K := ⟨Fact.out, he1, by rw [hK, ← pow_mul, mul_comm]⟩
      exact h.false_of_statedSU_three hU (Sec4.three_ne_zero_of_card Fact.out (by omega) hU.card)
        (lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)) eY
  ·
    exact (h.false_of_projSL_three (by omega) he1 eY).elim
  ·
    exact (h.false_of_projSU_three (by omega) he1 eY).elim
  ·
    exact (h.false_of_fact (MulEquiv.refl _) ((hOdd p hp3).1 Y hG2)).elim
  ·
    exact (h.false_of_fact eY (hOdd p hp3).2.1).elim
  ·
    exact (h.false_of_fact eY ((hOdd p hp3).2.2.1 hp1)).elim
  ·
    exact (h.false_of_fact eY ((hOdd p hp3).2.2.2 hp2)).elim
  ·
    exfalso
    rcases Nat.lt_or_ge n 9 with hn8 | hn9
    · refine h.false_of_not_dvd_card eY fun h27 => ?_
      have h1 := h27.trans ((Sec4.card_alternatingGroup_dvd n).trans
        (Nat.factorial_dvd_factorial (show n ≤ 8 by omega)))
      revert h1
      decide
    · obtain rfl : n = 9 := by omega
      exact h.false_of_fact eY hA9
  ·
    exfalso
    obtain ⟨N, _, ⟨eN⟩, ⟨eQ⟩⟩ := hA6
    have hY : Nat.card Y = 1080 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr eQ.toEquiv,
        Nat.card_congr eN.toEquiv, nat_card_alternatingGroup, Nat.card_fin,
        Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      decide
    exact h.false_of_card_dvd (N := 1080) (b := 11) (hY ▸ dvd_rfl) (by norm_num) (by norm_num)
      (by decide)
  ·
    exfalso
    have := isPerfect_alternatingGroup_seven
    refine h.false_of_not_dvd fun h27 => ?_
    have h1 := h27.trans (card_quotient_center_dvd_of_isExtOf hA7)
    rw [nat_card_alternatingGroup, Nat.card_fin] at h1
    revert h1
    decide
  ·
    exact (h.false_of_fact eY (hSpor.1 s hs)).elim
  ·
    exact (h.false_of_fact (MulEquiv.refl _) (hSpor.2 s hs Y hext)).elim
  ·
    rcases hchev with ⟨n, hn, ⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩⟩ |
        ⟨f, hG2 | hD4 | hSz | hF4 | hTits⟩
    · exact (h.false_of_projSL_two (by norm_num) hn eY).elim
    · exact (h.false_of_projSL_three (by norm_num) hn eY).elim
    · exact (h.false_of_projSU_three (by norm_num) hn eY).elim
    · exact (h.false_of_fact eY (hEven.1 n hn)).elim
    · rcases Nat.even_or_odd n with hev | hodd
      · exact (h.false_of_fact eY (hEven.2.1 n hn hev)).elim
      · exact ⟨n, hodd, ⟨eY⟩⟩
    · exact (h.false_of_fact (MulEquiv.refl _) (hEven.2.2 Y f (Or.inl hG2))).elim
    · exact (h.false_of_fact (MulEquiv.refl _) (hEven.2.2 Y f (Or.inr (Or.inl hD4)))).elim
    · exfalso
      have h1 := KFacts.KP7.pRank_three_mulAut_le_one hSz
      have h2 := Sec4.le_pRank_mulAut (MulEquiv.refl Y) h.elemAbelian h.card_E
      omega
    · exact (h.false_of_fact (MulEquiv.refl _)
        (hEven.2.2 Y f (Or.inr (Or.inr (Or.inl hF4))))).elim
    · exact (h.false_of_fact (MulEquiv.refl _)
        (hEven.2.2 Y f (Or.inr (Or.inr (Or.inr hTits))))).elim
  ·
    exfalso
    obtain ⟨K, _, _, ⟨hK, ⟨eY⟩⟩ | ⟨hK, ⟨eY⟩⟩⟩ := hSL
    · exact h.false_of_statedSL_three (Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num) hK)
        eY
    · have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
      rcases Nat.lt_or_ge n 2 with hn1 | hn2
      · obtain rfl : n = 1 := by omega
        refine h.false_of_card_dvd (N := 216) (b := 8) ?_ (by norm_num) (by norm_num) (by decide)
        rw [Nat.card_congr eY.toEquiv, CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl]
      · exact h.false_of_statedSU_three hU
          (Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num) hU.card)
          (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)) eY
  ·
    exfalso
    have : Finite (projSL 5 (GaloisField 2 1)) :=
      Finite.of_equiv _ (Sec4.projSLEquivPSLn 5 (GaloisField 2 1)).symm.toEquiv
    refine h.false_of_not_dvd_card eY fun h27 => ?_
    have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
    have h1 := h27.trans (Sec4.card_projSL_dvd 5 (GaloisField 2 1))
    rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num)] at h1
    norm_num [Fin.prod_univ_succ] at h1
  ·
    exact (h.false_of_fact eY hSp62).elim
  ·
    exfalso
    have hU := Sec4.unitaryFieldData_galoisField 2 2 (by norm_num)
    have hSU := CFSG.RankThree.PartTwo.Census.card_statedSU_five_four hU
    have : Finite (CFSG.Assembly.LowTwoRank.StatedSU 5 (2 ^ 2) (GaloisField 2 (2 * 2))) :=
      Nat.finite_of_card_ne_zero (by rw [hSU]; norm_num)
    have : Finite (projSU 5 2 2) :=
      Finite.of_equiv _ (Sec4.projSUEquivStatedProj 5 2 2).symm.toEquiv
    refine h.false_of_not_dvd_card eY fun h27 => ?_
    have h1 := h27.trans (Sec4.card_projSU_dvd 5 2 2)
    rw [hSU] at h1
    norm_num at h1
  ·
    rcases (show e = 1 ∨ e = 2 by omega) with rfl | rfl
    · exfalso
      have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
      have h1 := Sec4.card_projSL_dvd 3 (GaloisField 3 1)
      rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by norm_num)]
        at h1
      norm_num [Fin.prod_univ_succ] at h1
      exact h.false_of_card_dvd (N := 5616) (b := 13) (by rw [Nat.card_congr eY.toEquiv]; exact h1)
        (by norm_num) (by norm_num) (by decide)
    · exact (h.false_of_fact eY hThree.1).elim
  ·
    rcases (show e = 1 ∨ e = 2 by omega) with rfl | rfl
    · exact (h.false_of_fact eY hThree.2.1).elim
    · exfalso
      have h1 := KFacts.KS14.card_projSU_three_mul_gcd 3 2 (by norm_num)
      norm_num at h1
      exact h.false_of_card_dvd (N := 42573600) (b := 26)
        (by rw [Nat.card_congr eY.toEquiv, h1]) (by norm_num) (by norm_num) (by decide)
  ·
    exfalso
    have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
    have h1 := Sec4.card_projSL_dvd 4 (GaloisField 3 1)
    rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by norm_num)] at h1
    norm_num [Fin.prod_univ_succ] at h1
    exact h.false_of_card_dvd (N := 12130560) (b := 24)
      (by rw [Nat.card_congr eY.toEquiv]; exact h1)
      (by norm_num) (by norm_num) (by decide)
  ·
    exact (h.false_of_fact (MulEquiv.refl _) (hThree.2.2 Y hZ3 (Or.inl hG23))).elim
  ·
    exact (h.false_of_fact (MulEquiv.refl _) (hThree.2.2 Y hZ3 (Or.inr ⟨eY⟩))).elim

end CFSG.RankThree.PartTwo.Sec21
