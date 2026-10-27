module

import CFSG.RankThree.PartTwo.Sec15.Sylow155R1V
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T114
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T114B
import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofMaxT
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofPL
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec14.Concrete
public import CFSG.RankThree.PartTwo.Sec14.Item1446
public import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofCases
public import CFSG.RankThree.PartTwo.Sec15.Item155wProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_delta_and_oPrimeResidualOf_sup_commutator {A X Q : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hXΔ : X = delta A LB X) (hX3 : X = oPrimeResidualOf 3 X)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hQ : Q ∈ scriptQ A LB)
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) :
    X ⊔ ⁅X, Q⁆ = delta A LB (X ⊔ ⁅X, Q⁆) ∧ oPrimeResidualOf 3 (X ⊔ ⁅X, Q⁆) = X ⊔ ⁅X, Q⁆ := by
  have hCQ : ⁅X, Q⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro x hx q hq
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXQ hx) q).mp hq) (Q.inv_mem hq)
  have hAC : A ≤ Subgroup.normalizer ((⁅X, Q⁆ : Subgroup G) : Set G) :=
    Proof1418Res3.le_normalizer_commutator hAX hQ.1.2.2
  refine ⟨le_antisymm (sup_le (hXΔ.le.trans (delta_mono le_sup_left))
    (le_delta (mem_scriptQ_of_le hQ hCQ hAC) le_sup_right)) (delta_le _), ?_⟩
  set O := oPrimeResidualOf 3 (X ⊔ ⁅X, Q⁆) with hO
  have hXO : X ≤ O := hX3.le.trans (Sec15.oPrimeResidualOf_mono 3 le_sup_left)
  have hQO : Q ≤ Subgroup.normalizer (O : Set G) :=
    Sec14.le_normalizer_oPrimeResidualOf (le_normalizer_sup_commutator X Q)
  refine le_antisymm (Sec14.oPrimeResidualOf_le_self 3 _) (sup_le hXO ?_)
  rw [Subgroup.commutator_le]
  intro x hx q hq
  have h1 : q * x⁻¹ * q⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp (hQO hq) x⁻¹).mp (O.inv_mem (hXO hx))
  have h2 : ⁅x, q⁆ = x * (q * x⁻¹ * q⁻¹) := by
    simp only [commutatorElement_def, mul_assoc]
  rw [h2]
  exact O.mul_mem (hXO hx) h1

theorem pPrimeCoreOf_two_host_le_n155_of_lt {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) {X K Y M T P : Subgroup G}
    (hC : Ctx155 A X K Y M T) (hab : Above155w A X) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) (hKX : K = X ⊔ CFSG.Open.pCoreOf 2 K)
    {𝔐 X'' : Subgroup G} (h𝔐 : IsPLocal 2 𝔐) (hA𝔐 : A ≤ 𝔐)
    (hO𝔐 : pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      𝔐)
    (hX'' : X'' ∈ scriptY4 A (lB A)) (hlt : X < X'') (hX''K : X'' ≤ K) (hX''𝔐 : X'' ≤ 𝔐) :
    pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      n155 A K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX''3 : oPrimeResidualOf 3 X'' = X'' := hX''.2.1.symm
  have hKX'' : K = X'' ⊔ CFSG.Open.pCoreOf 2 K :=
    le_antisymm (hKX.le.trans (sup_le_sup_right hlt.le _))
      (sup_le hX''K (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
  have hX''U : X'' = X ⊔ CFSG.Open.pCoreOf 2 X'' := eq_sup_pCoreOf_of_le hlt.le hX''K hKX
  have hO2 : CFSG.Open.pCoreOf 2 X'' ≠ ⊥ := fun h0 => hlt.ne (by
    rw [h0, sup_bot_eq] at hX''U
    exact hX''U.symm)
  have hY : IsY155 A X'' := by
    refine ⟨⟨⟨hX''.1, hO2⟩, hX''.2.2.1⟩, ?_, ?_⟩
    · rw [hX''3]
      exact hX''
    · rw [hX''3]
      exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 X'')).symm
  have hlt' : X < oPrimeResidualOf 3 X'' := by
    rw [hX''3]
    exact hlt
  obtain ⟨M', hle, hM'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge h𝔐
  have hM'mem : M' ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ X'' : Subgroup G) : Set G) :=
    ⟨hM', fun x hx => hle ((sup_le hA𝔐 hX''𝔐) hx)⟩
  have hΓ : K ∈ gam155 A (lB A) X'' (oPrimeResidualOf 3 X'') := by
    rw [hX''3]
    exact ⟨hC.mem_k, hX''K, hX''K.trans Subgroup.le_normalizer⟩
  have hhyp : omg155 A (oPrimeResidualOf 3 X'') ∨
      K = oPrimeResidualOf 3 X'' ⊔ CFSG.Open.pCoreOf 2 K := by
    rw [hX''3]
    exact Or.inr hKX''
  exact (le_delta (pPrimeCoreOf_two_host_mem_scriptQ h h146 hC hE hRP) (hO𝔐.trans hle)).trans
    ((hab X'' hY hlt').2 K hΓ hhyp M' hM'mem)

theorem delta_inf_le_normalizer {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) {X K Y M T P : Subgroup G}
    (hC : Ctx155 A X K Y M T) (hab : Above155w A X) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) (hKX : K = X ⊔ CFSG.Open.pCoreOf 2 K)
    (hE0N : ¬ pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
      pPrimeCoreOf 3 (u155 A M X))) ≤ n155 A K)
    {𝔐 : Subgroup G} (h𝔐 : IsPLocal 2 𝔐) (hA𝔐 : A ≤ 𝔐)
    (hO𝔐 : pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      𝔐)
    (hX𝔐 : X ≤ 𝔐) :
    delta A (lB A) (CFSG.Open.pCoreOf 2 K ⊓ 𝔐) ≤ Subgroup.normalizer (X : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := CFSG.Open.pCoreOf 2 K with hV
  set Q := delta A (lB A) (V ⊓ 𝔐) with hQdef
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hK4 : K ∈ scriptY4 A (lB A) := hC.mem_k.prop.1
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX4.1.2
  have hV2 : IsPGroup 2 ↥V := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hVK : V ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hnorm : ∀ {H : Subgroup G}, H ≤ Subgroup.normalizer (V : Set G) → H ≤ 𝔐 →
      H ≤ Subgroup.normalizer ((V ⊓ 𝔐 : Subgroup G) : Set G) := by
    intro H hHV hH𝔐 x hx
    have h1 := Subgroup.mem_normalizer_iff.mp (hHV hx)
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hH𝔐 hx))
    exact Subgroup.mem_normalizer_iff.mpr fun g => by
      simp only [SetLike.mem_coe, Subgroup.mem_inf] at h1 h2 ⊢
      exact and_congr (h1 g) (h2 g)
  have hVI : V ⊓ 𝔐 ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, Sec15.isPiSubgroup_piCompl_three_of_isPGroup Nat.prime_two (by norm_num)
      (hV2.to_le inf_le_left),
      hnorm (hK4.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)) hA𝔐⟩
  have hΔ : ∀ Z ∈ invariantPiSubgroups ⊤ A (piCompl 3), delta A (lB A) Z ∈ scriptQ A (lB A) :=
    fun Z hZ => delta_mem_scriptQ h.isE27 h146 hZ
  have hQ : Q ∈ scriptQ A (lB A) := hΔ _ hVI
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) :=
    hX4.2.2.1.le.trans (delta_le_normalizer_delta hΔ hVI (hnorm (hC.le_k.trans hKV) hX𝔐))
  have hQV : Q ≤ V ⊓ 𝔐 := delta_le _
  by_contra hQX
  obtain ⟨hX''Δ, hX''3⟩ :=
    eq_delta_and_oPrimeResidualOf_sup_commutator hX4.2.2.1 hX4.2.1 hAX hQ hXQ
  have hCQ : ⁅X, Q⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro x hx q hq
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXQ hx) q).mp hq) (Q.inv_mem hq)
  have hX''K : X ⊔ ⁅X, Q⁆ ≤ K := sup_le hC.le_k (hCQ.trans (hQV.trans (inf_le_left.trans hVK)))
  have hX''𝔐 : X ⊔ ⁅X, Q⁆ ≤ 𝔐 := sup_le hX𝔐 (hCQ.trans (hQV.trans inf_le_right))
  have hKX'' : K ≤ (X ⊔ ⁅X, Q⁆) ⊔ V := hKX.le.trans (sup_le_sup_right le_sup_left _)
  obtain ⟨e⟩ := Proof155R2.isoQuot_of_le_sup hX''K hKX'' (hX''K.trans hKV) hKV hV2
  have hX''4 : X ⊔ ⁅X, Q⁆ ∈ scriptY4 A (lB A) :=
    ⟨⟨fun htop => hK4.1.1 (top_le_iff.mp (htop ▸ hX''K)),
        Sec14.le_normalizer_sup hAX (Proof1418Res3.le_normalizer_commutator hAX hQ.1.2.2)⟩,
      hX''3.symm, hX''Δ, CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hK4.2.2.2⟩
  have hlt : X < X ⊔ ⁅X, Q⁆ := by
    refine lt_of_le_of_ne le_sup_left fun heq => hQX fun q hq => ?_
    have hCX : ⁅X, Q⁆ ≤ X := le_sup_right.trans heq.ge
    have hconj : ∀ {g : G}, g ∈ Q → ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
      intro g hg x hx
      have h3 : ⁅x, g⁆ ∈ X := hCX (Subgroup.commutator_mem_commutator hx hg)
      have h4 : g * x * g⁻¹ = (⁅x, g⁆)⁻¹ * x := by
        rw [commutatorElement_def]
        group
      rw [h4]
      exact X.mul_mem (X.inv_mem h3) hx
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hconj hq x hx, fun hx => ?_⟩
    have h5 := hconj (Q.inv_mem hq) _ hx
    have h6 : q⁻¹ * (q * x * q⁻¹) * q⁻¹⁻¹ = x := by group
    rwa [h6] at h5
  exact hE0N (pPrimeCoreOf_two_host_le_n155_of_lt h h146 hC hab hE hRP hKX h𝔐 hA𝔐 hO𝔐 hX''4
    hlt hX''K hX''𝔐)

theorem inf_le_normalizer_of_mem_scriptQ {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) {X K Y M T P : Subgroup G}
    (hC : Ctx155 A X K Y M T) (hab : Above155w A X) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) (hKX : K = X ⊔ CFSG.Open.pCoreOf 2 K)
    (hE0N : ¬ pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
      pPrimeCoreOf 3 (u155 A M X))) ≤ n155 A K)
    (hV : CFSG.Open.pCoreOf 2 K ∈ scriptQ A (lB A))
    {𝔐 : Subgroup G} (h𝔐 : IsPLocal 2 𝔐) (hA𝔐 : A ≤ 𝔐)
    (hO𝔐 : pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      𝔐)
    (hX𝔐 : X ≤ 𝔐) :
    CFSG.Open.pCoreOf 2 K ⊓ 𝔐 ≤ Subgroup.normalizer (X : Set G) := by
  have hK4 : K ∈ scriptY4 A (lB A) := hC.mem_k.prop.1
  have hAV : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    hK4.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hAI : A ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 K ⊓ 𝔐 : Subgroup G) : Set G) := by
    intro x hx
    have h1 := Subgroup.mem_normalizer_iff.mp (hAV hx)
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hA𝔐 hx))
    exact Subgroup.mem_normalizer_iff.mpr fun g => by
      simp only [SetLike.mem_coe, Subgroup.mem_inf] at h1 h2 ⊢
      exact and_congr (h1 g) (h2 g)
  exact (le_delta (mem_scriptQ_of_le hV inf_le_left hAI) le_rfl).trans
    (delta_inf_le_normalizer h h146 hC hab hE hRP hKX hE0N h𝔐 hA𝔐 hO𝔐 hX𝔐)

theorem inf_normalizer_pCoreOf_le_normalizer {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) (h149 : Item149 A (lB A))
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hab : Above155w A X)
    (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hKX : K = X ⊔ CFSG.Open.pCoreOf 2 K)
    (hE0N : ¬ pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
      pPrimeCoreOf 3 (u155 A M X))) ≤ n155 A K)
    (hV : CFSG.Open.pCoreOf 2 K ∈ scriptQ A (lB A)) :
    CFSG.Open.pCoreOf 2 K ⊓ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) ≤
      Subgroup.normalizer (X : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hU1 : CFSG.Open.pCoreOf 2 X ≠ ⊥ := (isCharacteristicP_x_and_pCoreOf_ne_bot h h149 hC hIX).2
  have hXU : Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
  have hOX : pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)))
      ≤ Subgroup.normalizer (X : Set G) :=
    ((pPrimeCoreOf_two_host_le_centralizer h h146 h149 hC hE hRP hIX).trans
      (Subgroup.centralizer_le fun x hx => x_le_oPrimeResidualOf_delta hC hx)).trans
      (Subgroup.centralizer_le_normalizer _)
  exact inf_le_normalizer_of_mem_scriptQ h h146 hC hab hE hRP hKX hE0N hV
    (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X) hU1)
    (hX4.1.2.trans hXU) (hOX.trans hXU) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
