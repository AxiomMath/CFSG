module

public import CFSG.RankThree.PartTwo.Sec16.Item166ThreeFac
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec14.Item146General
public import CFSG.GH74.GLS.Balance.SolvCompBasic
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.Open.GilmanSolomonDefs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Triple

public section

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem pPrimeCoreOf_two_delta_le_centralizer (h : Sec17Std G A c L Y₀) (h146 : Item146S14)
    {X : Subgroup G} (hX : X ∈ scriptY3Star A (lB A))
    (hXT : X ≤ Subgroup.normalizer (delta A (lB A) (pPrimeCoreOf 3 X) : Set G))
    (hF : generalizedFitting ↥(deltaZero A (lB A) X) = CFSG.pCore 2 ↥(deltaZero A (lB A) X)) :
    pPrimeCoreOf 2 (delta A (lB A) (pPrimeCoreOf 3 X)) ≤ Subgroup.centralizer (A : Set G) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R : Subgroup G := pPrimeCoreOf 3 X with hR
  set T : Subgroup G := delta A (lB A) R with hT
  set X₀ : Subgroup G := deltaZero A (lB A) X with hX₀
  set O : Subgroup G := pPrimeCoreOf 2 T with hO
  have h146' : Item146 A (lB A) := h146 G A c L h.toSec14Std
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.prop.1.1.2
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hAX.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)
  have hRpi : IsPiSubgroup (piCompl 3) R :=
    (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 X))
  have hRinv : R ∈ invariantPiSubgroups ⊤ A (piCompl 3) := ⟨le_top, hRpi, hAR⟩
  have hTQ : T ∈ scriptQ A (lB A) := delta_mem_scriptQ h.isE27 h146' hRinv
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := le_normalizer_delta R
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAT.trans (normalizer_le_normalizer_pPrimeCoreOf 2 T)
  have hOQ : O ∈ scriptQ A (lB A) := mem_scriptQ_of_le hTQ (pPrimeCoreOf_le 2 T) hAO
  have hOAle : ⁅O, A⁆ ≤ O := (Subgroup.le_normalizer_iff_commutator_le_left).mp hAO
  have hAOA : A ≤ Subgroup.normalizer ((⁅O, A⁆ : Subgroup G) : Set G) :=
    fun a ha => CFSG.GH74.GLS.Balance.SolvComp.mem_normalizer_commutator
      (hAO ha) (Subgroup.le_normalizer ha)
  have hOAQ : ⁅O, A⁆ ∈ scriptQ A (lB A) := mem_scriptQ_of_le hOQ hOAle hAOA
  have hTR : T ≤ R := delta_le R
  have hcop3R : Nat.Coprime 3 (Nat.card R) := coprime_card_pPrimeCoreOf 3 X
  have hcop3T : Nat.Coprime 3 (Nat.card T) :=
    hcop3R.of_dvd_right (Subgroup.card_dvd_of_le hTR)
  have hcop3O : Nat.Coprime 3 (Nat.card O) :=
    hcop3T.of_dvd_right (Subgroup.card_dvd_of_le (pPrimeCoreOf_le 2 T))
  have hidem : ⁅⁅O, A⁆, A⁆ = ⁅O, A⁆ :=
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent
      3 Nat.prime_three A O h.isE27.isPGroup hAO hcop3O
  have hOAQZero : ⁅O, A⁆ ∈ scriptQZero A (lB A) := ⟨hOAQ, hidem.symm⟩
  have hOAX : ⁅O, A⁆ ≤ X := hOAle.trans ((pPrimeCoreOf_le 2 T).trans (hTR.trans
    (pPrimeCoreOf_le 3 X)))
  have hOAX₀ : ⁅O, A⁆ ≤ X₀ := le_deltaZero hOAQZero hOAX
  have hX₀O : X₀ ≤ Subgroup.normalizer (O : Set G) :=
    (deltaZero_le X).trans (hXT.trans (normalizer_le_normalizer_pPrimeCoreOf 2 T))
  have hX₀N : X₀ ≤ Subgroup.normalizer ((O ⊓ X₀ : Subgroup G) : Set G) :=
    (le_inf hX₀O Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hnormal : ((O ⊓ X₀).subgroupOf X₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hX₀N
  have hcopO2 : Nat.Coprime 2 (Nat.card O) := coprime_card_pPrimeCoreOf 2 T
  have hcopN : Nat.Coprime 2 (Nat.card ((O ⊓ X₀).subgroupOf X₀)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact hcopO2.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  have hchar : IsCharacteristicP 2 ↥X₀ :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥X₀ 2).mpr hF
  have hcore : CFSG.pPrimeCore 2 ↥X₀ = ⊥ :=
    pPrimeCore_eq_bot_of_isCharacteristicP ↥X₀ 2 hchar
  have hNbot : (O ⊓ X₀).subgroupOf X₀ = ⊥ :=
    (pPrimeCore_eq_bot_iff (p := 2) (G := ↥X₀)).mp hcore _ hnormal hcopN
  have hOX₀bot : O ⊓ X₀ = ⊥ := by
    rw [← Subgroup.map_subgroupOf_eq_of_le inf_le_right, hNbot, Subgroup.map_bot]
  have hle_bot : ⁅O, A⁆ ≤ ⊥ := by
    rw [← hOX₀bot]
    exact le_inf hOAle hOAX₀
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp (le_bot_iff.mp hle_bot)

theorem exists_sylow_two_delta (h : Sec17Std G A c L Y₀)
    {X : Subgroup G} (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    ∃ S : Subgroup G, S ≤ delta A (lB A) (pPrimeCoreOf 3 X) ∧ IsPGroup 2 S ∧
      ¬ 2 ∣ S.relIndex (delta A (lB A) (pPrimeCoreOf 3 X)) ∧
      A ≤ Subgroup.normalizer (S : Set G) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup G := pPrimeCoreOf 3 X with hR
  set T : Subgroup G := delta A (lB A) R with hT
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hAX.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := le_normalizer_delta R
  have hTR : T ≤ R := delta_le R
  have hcop3R : Nat.Coprime 3 (Nat.card R) := coprime_card_pPrimeCoreOf 3 X
  have hT3 : ¬ 3 ∣ Nat.card T :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (hcop3R.of_dvd_right (Subgroup.card_dvd_of_le hTR))
  obtain ⟨S, hSyl, -, hAS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two h.isE27.isPGroup hT3 hAT bot_le
    (IsPGroup.of_bot (p := 2) (G := G))
    (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
  have hSidx : ¬ 2 ∣ S.relIndex T := by
    obtain ⟨-, P, hP⟩ := CFSG.Open.fusionIsSylowIn_iff.mp hSyl
    have hidx : S.relIndex T = (S.subgroupOf T).index := rfl
    rw [hidx, ← hP]
    exact P.not_dvd_index
  exact ⟨S, hSyl.1, hSyl.2.1, hSidx, hAS⟩

theorem delta_le_normalizer_of_delta_normalizer_le (h : Sec17Std G A c L Y₀)
    (h146 : Item146S14) {X S : Subgroup G} (hX : X ∈ scriptY3Star A (lB A))
    (hsol : Group.IsSolvable ↥(pPrimeCoreOf 3 X))
    (hXT : X ≤ Subgroup.normalizer (delta A (lB A) (pPrimeCoreOf 3 X) : Set G))
    (hF : generalizedFitting ↥(deltaZero A (lB A) X) = CFSG.pCore 2 ↥(deltaZero A (lB A) X))
    (hST : S ≤ delta A (lB A) (pPrimeCoreOf 3 X)) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex (delta A (lB A) (pPrimeCoreOf 3 X)))
    (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hJ : delta A (lB A) (Subgroup.normalizer (jOf S : Set G)) ≤
      Subgroup.normalizer (Y₀ : Set G))
    (hΩ : delta A (lB A) (Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G)) ≤
      Subgroup.normalizer (Y₀ : Set G)) :
    delta A (lB A) (pPrimeCoreOf 3 X) ≤ Subgroup.normalizer (Y₀ : Set G) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup G := pPrimeCoreOf 3 X with hR
  set T : Subgroup G := delta A (lB A) R with hT
  set M : Subgroup G := Subgroup.normalizer (Y₀ : Set G) with hM
  have h146' : Item146 A (lB A) := h146 G A c L h.toSec14Std
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.prop.1.1.2
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hAX.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)
  have hRpi : IsPiSubgroup (piCompl 3) R :=
    (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 X))
  have hRinv : R ∈ invariantPiSubgroups ⊤ A (piCompl 3) := ⟨le_top, hRpi, hAR⟩
  have hTQ : T ∈ scriptQ A (lB A) := delta_mem_scriptQ h.isE27 h146' hRinv
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := le_normalizer_delta R
  have hTR : T ≤ R := delta_le R
  have hsolT : Group.IsSolvable ↥T :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hTR)
  have hcop3R : Nat.Coprime 3 (Nat.card R) := coprime_card_pPrimeCoreOf 3 X
  have hT3 : ¬ 3 ∣ Nat.card T :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (hcop3R.of_dvd_right (Subgroup.card_dvd_of_le hTR))
  have hO : pPrimeCoreOf 2 T ≤ M :=
    (pPrimeCoreOf_two_delta_le_centralizer h h146 hX hXT hF).trans
      ((Subgroup.centralizer_le_normalizer (A : Set G)).trans h.normalizer_le)
  have hAJS : A ≤ Subgroup.normalizer (jOf S : Set G) :=
    hAS.trans (by simpa only [Sec7.tripleOf_zero] using
      Sec7.normalizer_le_normalizer_tripleOf S 0)
  have hAΩ : A ≤ Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) :=
    hAS.trans (by simpa only [Sec7.tripleOf_one] using
      Sec7.normalizer_le_normalizer_tripleOf S 1)
  have hJle : Subgroup.normalizer (jOf S : Set G) ⊓ T ≤ M := by
    have hQ : Subgroup.normalizer (jOf S : Set G) ⊓ T ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le hTQ inf_le_right
        ((le_inf (hAJS.trans Subgroup.le_normalizer) hAT).trans
          Subgroup.inf_normalizer_le_normalizer_inf)
    exact (le_delta hQ inf_le_left).trans hJ
  have hΩle : Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) ⊓ T ≤ M := by
    have hQ : Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) ⊓ T ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le hTQ inf_le_right
        ((le_inf (hAΩ.trans Subgroup.le_normalizer) hAT).trans
          Subgroup.inf_normalizer_le_normalizer_inf)
    exact (le_delta hQ inf_le_left).trans hΩ
  exact Proof166Three.le_of_normalizer_le hsolT hT3 hST hS2 hSidx hO hJle hΩle

end CFSG.RankThree.PartTwo.Sec16.Ctr166
