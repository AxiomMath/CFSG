module

public import CFSG.RankThree.PartTwo.Sec15.Item155wProofCorrDefs
import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofSubn
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Item153Claims
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Step155YQ0W (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A)

@[expose] noncomputable def Step155PJQ0W (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → ∀ J ∈ thetaComponentsIn M, J ∈ scriptY0 A (lB A) → X ≤ J →
    ∀ P ∈ scriptQPiStar A (lB A) (M ⊓ Subgroup.normalizer (J : Set G)) (piOf 2), T ≤ P →
      CFSG.Open.pCoreOf 2 (P ⊔ J) ∈ scriptQ A (lB A)

@[expose] noncomputable def Step155CasesTwoW (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → ∀ J ∈ thetaComponentsIn M, J ∈ scriptY0 A (lB A) → X ≤ J →
    (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L') →
    ¬ (Case154Two L J X ∧ IsLThreePi (↥X ⧸ CFSG.pCore 2 ↥X))

@[expose] noncomputable def Step155CasesBW (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → ∀ J ∈ thetaComponentsIn M, J ∈ scriptY0 A (lB A) → X ≤ J →
    ∀ P ∈ scriptQPiStar A (lB A) (M ⊓ Subgroup.normalizer (J : Set G)) (piOf 2), T ≤ P →
      CFSG.Open.pCoreOf 2 Y ≤ P → CFSG.Open.pCoreOf 2 (P ⊔ J) ≤ P →
      Case154Three A L J X (CFSG.Open.pCoreOf 2 Y) → Hyp322 (P ⊔ J) (CFSG.Open.pCoreOf 2 Y)

@[expose] noncomputable def Step155YQ0WR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155YQ0W A c L

@[expose] noncomputable def Step155PJQ0WR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155PJQ0W A c L

@[expose] noncomputable def Step155CasesTwoWR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155CasesTwoW A c L

@[expose] noncomputable def Step155CasesBWR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155CasesBW A c L

namespace Proof155w2

theorem le_pCoreOf_sup_of_commutator_le {P J R : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPJ : P ≤ Subgroup.normalizer (J : Set G)) (hRP : R ≤ P)
    (hRJ : ⁅R, J⁆ ≤ CFSG.Open.pCoreOf 2 J) : R ≤ CFSG.Open.pCoreOf 2 (P ⊔ J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 J with hO
  set C := centralizerSection J O with hCdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J
  have hOJ : O ≤ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J
  have hJO : J ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J
  have hNO : Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J
  set V := P ⊓ C with hV
  have hRV : R ≤ V := by
    intro r hr
    have hrC : r ∈ C := by
      refine ⟨hPJ (hRP hr), hNO (hPJ (hRP hr)), fun k hk => ?_⟩
      have h1 : ⁅r, k⁆ ∈ O := hRJ (Subgroup.commutator_mem_commutator hr hk)
      rw [← commutatorElement_inv]
      exact inv_mem h1
    exact Subgroup.mem_inf.mpr ⟨hRP hr, hrC⟩
  have hV2 : IsPGroup 2 V := hP2.to_le inf_le_left
  have hVO : V ≤ Subgroup.normalizer (O : Set G) := (inf_le_left.trans hPJ).trans hNO
  set W := V ⊔ O with hW
  have hW2 : IsPGroup 2 W := IsPGroup.to_sup_of_normal_right' hV2 hO2 hVO
  have hWH : W ≤ P ⊔ J := sup_le (inf_le_left.trans le_sup_left) (hOJ.trans le_sup_right)
  have hPC : P ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizerSection hPJ (hPJ.trans hNO)
  have hPW : P ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_sup (Late.le_normalizer_inf Subgroup.le_normalizer hPC) (hPJ.trans hNO)
  have hJW : J ≤ Subgroup.normalizer (W : Set G) := by
    intro j hj
    refine Sec13.Item138Proof.mem_normalizer_of_map_le ?_
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      have hvC : v ∈ C := (Subgroup.mem_inf.mp hv).2
      have h1 : ⁅j, v⁆ ∈ O := hvC.2.2 j hj
      have he : (MulAut.conj j).toMonoidHom v = ⁅j, v⁆ * v := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [he]
      exact mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hv)
    · rw [Late.map_conj_eq_of_mem_normalizer (hJO hj)]
      exact le_sup_right
  exact hRV.trans (le_sup_left.trans
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWH (sup_le hPW hJW) hW2))

end Proof155w2

theorem step155CasesNW_of {A : Subgroup G} {c : G} {L : Subgroup G} (h146 : Item146 A (lB A))
    (hYQ : Step155YQ0W A c L) (hPJQ : Step155PJQ0W A c L) (htwo : Step155CasesTwoW A c L)
    (hb : Step155CasesBW A c L) : Step155CasesNW A c L := by
  intro h X K Y M T hC hmax hab J hJM hJ0 hXJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : Late.IsE27 A := h.isE27
  set R := CFSG.Open.pCoreOf 2 Y with hR
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := by
    rw [← hC.res]
    exact le_normalizer_oPrimeResidualOf Subgroup.le_normalizer
  have hM' : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hC.mem_m
  obtain ⟨hYM, -, -, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM'
  have hYJ : Y ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_mem_thetaComponentsIn (hYM.trans Subgroup.le_normalizer) hJM hXJ
      (isPerfect_of_mem_scriptY4 hX4) (ne_bot_of_mem_scriptY4 hX4) hYX
  have hJM' : J ≤ M := le_of_mem_thetaComponentsIn hJM
  have hTmem : T ∈ scriptQPi A (lB A) (M ⊓ Subgroup.normalizer (J : Set G)) (piOf 2) :=
    ⟨⟨hC.mem_t.prop.1.1, hC.mem_t.prop.1.2.trans (le_inf hYM hYJ)⟩, hC.mem_t.prop.2⟩
  obtain ⟨P, hTP, hP⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (M ⊓ Subgroup.normalizer (J : Set G)) (piOf 2))) hTmem
  have hP2 : IsPGroup 2 P := isPGroup_of_mem_scriptQPi Nat.prime_two hP.prop
  have hPJn : P ≤ Subgroup.normalizer (J : Set G) := hP.prop.1.2.trans inf_le_right
  set Q := CFSG.Open.pCoreOf 2 (P ⊔ J) with hQ
  have hR𝓠 : R ∈ scriptQ A (lB A) := hYQ h X K Y M T hC hmax hab
  have hRT : R ≤ T := by
    have hRmem : R ∈ scriptQPi A (lB A) Y (piOf 2) :=
      ⟨⟨hR𝓠, CFSG.LieType.BorelTits.pCoreOf_le 2 Y⟩, (isPiSubgroup_piOf_iff Nat.prime_two R).mpr
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)⟩
    have hTR := sup_mem_scriptQPi_of_item146 hA h146 hC.mem_t.prop hRmem
      (hC.mem_t.prop.1.2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
    exact le_sup_right.trans (hC.mem_t.2 hTR le_sup_left)
  have hRP : R ≤ P := hRT.trans hTP
  have hQ𝓠 : Q ∈ scriptQ A (lB A) := hPJQ h X K Y M T hC hmax hab J hJM hJ0 hXJ P hP hTP
  have hQP : Q ≤ P := by
    have hPJM : P ⊔ J ≤ M ⊓ Subgroup.normalizer (J : Set G) :=
      sup_le hP.prop.1.2 (le_inf hJM' Subgroup.le_normalizer)
    have hQmem : Q ∈ scriptQPi A (lB A) (M ⊓ Subgroup.normalizer (J : Set G)) (piOf 2) :=
      ⟨⟨hQ𝓠, (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hPJM⟩,
        (isPiSubgroup_piOf_iff Nat.prime_two Q).mpr
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _)⟩
    have hPQ := sup_mem_scriptQPi_of_item146 hA h146 hP.prop hQmem
      (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    exact le_sup_right.trans (hP.2 hPQ le_sup_left)
  refine ⟨P, hP, hTP, hQP, ?_, fun hRJ => Proof155w2.le_pCoreOf_sup_of_commutator_le hP2 hPJn
    hRP hRJ, htwo h X K Y M T hC hmax hab J hJM hJ0 hXJ,
    hb h X K Y M T hC hmax hab J hJM hJ0 hXJ P hP hTP hRP hQP⟩
  exact (hRP.trans le_sup_left).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

theorem step155CasesNWR_of (h146 : Item146S14) (hYQ : Step155YQ0WR) (hPJQ : Step155PJQ0WR)
    (htwo : Step155CasesTwoWR) (hb : Step155CasesBWR) : Step155CasesNWR :=
  fun G _ _ A c L hR => step155CasesNW_of (h146 G A c L hR.toSec14Std) (hYQ G A c L hR)
    (hPJQ G A c L hR) (htwo G A c L hR) (hb G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
