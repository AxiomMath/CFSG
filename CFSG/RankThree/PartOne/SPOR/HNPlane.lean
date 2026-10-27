module

public import CFSG.RankThree.PartOne.SPOR.HNCover
public import CFSG.RankThree.PartOne.SPOR.HNChecks
public import CFSG.Sporadic.HNOddCore.ThreeInvol
public import CFSG.Sporadic.HNOddCore.Fusion
public import CFSG.Sporadic.HNOddCore.OuterFix
public import CFSG.Sporadic.HNSchreier.Order
public import CFSG.Sporadic.HNSchreier.FullAut
public import CFSG.RankThree.PartOne.KS.Assembly
public import CFSG.RankThree.PartOne.KS.Arith
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.RankThree.PartOne.SPOR

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore

theorem fixSub_conjR (y : RH) :
    (fixSub (conjR y) : Subgroup JH) = CFSG.Sporadic.HNOddCore.CJ y :=
  Subgroup.ext fun j => by rw [mem_fixSub, conjR_fix_iff, CFSG.Sporadic.HNOddCore.mem_CJ]

theorem hn_cover_of_ok
    {y : RH} {nQ n N m k : ℕ} (hf : HNClassFacts y nQ n)
    (hN : Nat.card (CFSG.Sporadic.HNOddCore.CJ y) = N) (hNm : N = 5 ^ k * m) (hm : ¬ 5 ∣ m)
    (hk : nQ = 5 ^ k) :
    ∀ z : JH, conjR y z = z → orderOf z = 5 →
      ∃ l : List JH, (∀ g ∈ l, g * z = z * g) ∧
        5 ∣ orderOf ((l.map fun g => MulAut.conj g * conjR y * (MulAut.conj g)⁻¹).prod) := by
  obtain ⟨Q, xs, hcomm, hcard, hcov, hwit⟩ := hf
  have hN' : Nat.card (fixSub (conjR y) : Subgroup JH) = N := by rw [fixSub_conjR]; exact hN
  have hQfix : Q ≤ (fixSub (conjR y) : Subgroup JH) := fun q hq =>
    (conjR_fix_iff _ _).2 (hcomm q hq)
  have hQk : Nat.card Q = 5 ^ k := by rw [hcard, hk]
  have hQp : IsPGroup 5 Q := IsPGroup.of_card hQk
  have hSyl := exists_sylow_subgroupOf_eq Nat.prime_five hQfix hQp hN' hNm hm hQk
  have hcov' : ∀ z ∈ Q, orderOf z = 5 → ∃ i : Fin n, ∃ g : JH,
      conjR y g = g ∧ Subgroup.zpowers z = Subgroup.zpowers (g * xs i * g⁻¹) := by
    intro z hz hzo
    obtain ⟨i, hi, g, hg, hz'⟩ := hcov z hz hzo
    exact ⟨⟨i, hi⟩, g, (conjR_fix_iff _ _).2 hg, hz'⟩
  have hwit' : ∀ i : Fin n, ∃ l : List JH, (∀ g ∈ l, g * xs i = xs i * g) ∧
      5 ∣ orderOf ((l.map fun g => MulAut.conj g * conjR y * (MulAut.conj g)⁻¹).prod) :=
    fun i => hwit i.1 i.2
  exact @cover_of_lines_conj JH inferInstance inferInstance 5 Nat.prime_five
    (conjR y) Q hSyl (Fin n) (fun i => xs i) hcov' hwit'

theorem hn_card_CJ :
    Nat.card (CFSG.Sporadic.HNOddCore.CJ (jR aJ)) = 177408000 ∧
      Nat.card (CFSG.Sporadic.HNOddCore.CJ (jR t4J)) = 3686400 ∧
      Nat.card (CFSG.Sporadic.HNOddCore.CJ t1R) = 3628800 := by
  obtain ⟨-, -, -, h4, -, -, -, -, -, -, -, -, h13, -, -, -, -, -, h19, -⟩ :=
    ctuc_hn_three_involution_centralizers_exact
  refine ⟨?_, ?_, h4⟩
  · rw [CFSG.Sporadic.HNOddCore.CJ_jR]
    exact h19
  · rw [CFSG.Sporadic.HNOddCore.CJ_jR]
    exact h13

theorem hn_cover_A :
    ∀ z : JH, conjR (jR aJ) z = z → orderOf z = 5 →
      ∃ l : List JH, (∀ g ∈ l, g * z = z * g) ∧
        5 ∣ orderOf ((l.map fun g => MulAut.conj g * conjR (jR aJ) * (MulAut.conj g)⁻¹).prod) :=
  hn_cover_of_ok hn_class_a_check hn_card_CJ.1 (k := 3) (m := 1419264) (by norm_num)
    (by norm_num) rfl

theorem hn_cover_B :
    ∀ z : JH, conjR (jR t4J) z = z → orderOf z = 5 →
      ∃ l : List JH, (∀ g ∈ l, g * z = z * g) ∧
        5 ∣ orderOf ((l.map fun g => MulAut.conj g * conjR (jR t4J) * (MulAut.conj g)⁻¹).prod) :=
  hn_cover_of_ok hn_class_b_check hn_card_CJ.2.1 (k := 2) (m := 147456) (by norm_num)
    (by norm_num) rfl

theorem hn_cover_C :
    ∀ z : JH, conjR t1R z = z → orderOf z = 5 →
      ∃ l : List JH, (∀ g ∈ l, g * z = z * g) ∧
        5 ∣ orderOf ((l.map fun g => MulAut.conj g * conjR t1R * (MulAut.conj g)⁻¹).prod) :=
  hn_cover_of_ok hn_class_c_check hn_card_CJ.2.2 (k := 2) (m := 145152) (by norm_num)
    (by norm_num) rfl

theorem hn_involution_classes
    (v : MulAut JH) (hv : orderOf v = 2) :
    IsConj v (conjR (jR aJ)) ∨ IsConj v (conjR (jR t4J)) ∨ IsConj v (conjR t1R) := by
  obtain ⟨y, rfl⟩ := conjR_bijective.2 v
  have h2 : y ^ 2 = 1 := by
    apply conjR_bijective.1
    rw [map_pow, map_one]
    have := pow_orderOf_eq_one (conjR y)
    rwa [hv] at this
  have h1 : y ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hv
    omega
  obtain ⟨hcls, -⟩ := ctuc_hn_involution_fusion_and_local_stabilizers
  rcases hcls y h2 h1 with hc | hc | hc
  · exact Or.inr (Or.inr (conjR.map_isConj hc).symm)
  · exact Or.inl (conjR.map_isConj ((CFSG.Sporadic.HNOddCore.isConj_jR
      CFSG.Sporadic.HNOddCore.isConj_t2_aJ).symm.trans hc)).symm
  · exact Or.inr (Or.inl (conjR.map_isConj hc).symm)

@[expose] noncomputable def hnReps :
    Fin 3 → MulAut JH
  | 0 => conjR (jR aJ)
  | 1 => conjR (jR t4J)
  | 2 => conjR t1R

theorem hnReps_zero :
    hnReps 0 = conjR (jR aJ) := rfl

theorem hnReps_one :
    hnReps 1 = conjR (jR t4J) := rfl

theorem hnReps_two :
    hnReps 2 = conjR t1R := rfl

theorem conjWitness_JH :
    ConjWitness JH 5 := by
  have hc : ∀ a : JH, (∀ b : JH, a * b = b * a) → a = 1 := fun a ha =>
    Subgroup.mem_bot.1 (center_JH ▸ Subgroup.mem_center_iff.2 fun b => (ha b).symm)
  refine @conjWitness_of_cover JH inferInstance 5 hc (Fin 3) hnReps ?_ ?_
  · intro v hv
    rcases hn_involution_classes v hv with h | h | h
    exacts [⟨0, by rw [hnReps_zero]; exact h⟩, ⟨1, by rw [hnReps_one]; exact h⟩,
      ⟨2, by rw [hnReps_two]; exact h⟩]
  · intro j
    match j with
    | 0 =>
      intro y hy ho
      rw [hnReps_zero] at hy ⊢
      exact hn_cover_A y hy ho
    | 1 =>
      intro y hy ho
      rw [hnReps_one] at hy ⊢
      exact hn_cover_B y hy ho
    | 2 =>
      intro y hy ho
      rw [hnReps_two] at hy ⊢
      exact hn_cover_C y hy ho

theorem conjWitness_HN :
    ConjWitness (CFSG.Blueprint.NativeSporadic.Carrier .HN) 5 := by
  have h : ConjWitness CFSG.Blueprint.NativeSporadic.HN 5 :=
    @ConjWitness.of_mulEquiv CFSG.Blueprint.NativeSporadic.HN JH inferInstance inferInstance 5
      hnEquivJ conjWitness_JH
  exact h

theorem hn_card_outer :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.Blueprint.NativeSporadic.Carrier .HN)) = 2 :=
  CFSG.Sporadic.HNSchreier.card_outer_HN

theorem hn_card :
    Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .HN) = 273030912000000 :=
  CFSG.Sporadic.HNSchreier.card_HN

theorem sporadicPlaneOdd_HN :
    SporadicPlaneOdd (CFSG.Blueprint.NativeSporadic.Carrier .HN) := by
  have hW := conjWitness_HN
  refine sporadicPlaneOdd_of_conjWitness {5} ?_ ?_ ?_
  · intro q hq _
    simp only [Finset.mem_singleton] at hq
    rw [hq]
    exact hW
  · intro T _ _ _ _ he q hq _
    obtain ⟨e⟩ := he
    simp only [Finset.mem_singleton] at hq
    rw [hq, Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv,
      hn_card_outer]
    norm_num
  · intro T _ _ _ hnab he p hp hp3 hpS
    obtain ⟨e⟩ := he
    simp only [Finset.mem_singleton] at hpS
    refine not_sq_dvd_card_mulAut_of_outer_le hnab e (N := 273030912000000) (k := 2)
      hn_card hn_card_outer.le hp (by omega) ?_
    have hs : Nat.Coprime p (2 ^ 14 * 3 ^ 6 * 5 ^ 6) := coprime_two_three_five_pow hp hp3 hpS 14 6 6
    have hN : (273030912000000 : ℕ) = (2 ^ 14 * 3 ^ 6 * 5 ^ 6) * 1463 := by norm_num
    rw [hN]
    exact not_sq_dvd_mul_of_coprime hp hs (B := 38) (by norm_num) (by decide) (by norm_num)

end CFSG.RankThree.PartOne.SPOR
