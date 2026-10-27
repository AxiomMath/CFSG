module

public import CFSG.RankThree.PartTwo.Sec16.Item166ThreeL42
public import CFSG.RankThree.PartTwo.Sec16.Item166ThreePerp
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Triple
import CFSG.RankThree.PartTwo.Sec16.Item166ThreeFac
import CFSG.RankThree.PartTwo.Sec16.Item166ThreeCent
import CFSG.RankThree.PartTwo.Sec17.Item17Res14ProofKb
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Three

open CFSG CFSG.Open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS
  CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

@[expose] def OmegaNe166 (A Y₀ : Subgroup G) : Prop :=
  ∀ K₀ Z : Subgroup G, K₀ = delta A (lB A) K₀ →
    (∃ m : ℕ, CFSG.Blueprint.SuzukiModel (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) 2 m) → K₀ ≤ Z →
      Z ∈ scriptY3Star A (lB A) → oPrimeResidualOf 3 Z ≠ ⊥ →
        Z ≤ Subgroup.normalizer (Y₀ : Set G)

theorem sSup_thetaComponentsIn_le (Z : Subgroup G) :
    (sSup (thetaComponentsIn Z) : Subgroup G) ≤ Z :=
  sSup_le fun _ hK => le_of_mem_thetaComponentsIn hK

theorem isPerfect_sSup_thetaComponentsIn (Z : Subgroup G) :
    Group.IsPerfect ↥((sSup (thetaComponentsIn Z) : Subgroup G)) :=
  Proof171Steps.isPerfect_sSup fun _ hK => isPerfect_of_mem_thetaComponentsIn hK

theorem normalizer_le_normalizer_sSup_thetaComponentsIn (Z : Subgroup G) :
    Subgroup.normalizer (Z : Set G) ≤
      Subgroup.normalizer ((sSup (thetaComponentsIn Z) : Subgroup G) : Set G) :=
  fun _ hg => Proof17Res14.mem_normalizer_sSup_thetaComponentsIn hg

theorem le_normalizer_sSup_thetaComponentsIn (Z : Subgroup G) :
    Z ≤ Subgroup.normalizer ((sSup (thetaComponentsIn Z) : Subgroup G) : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_sSup_thetaComponentsIn Z)

theorem not_three_dvd_sSup_thetaComponentsIn {Z : Subgroup G} (hZ3 : ¬ 3 ∣ Nat.card Z) :
    ¬ 3 ∣ Nat.card ↥((sSup (thetaComponentsIn Z) : Subgroup G)) :=
  fun h3 => hZ3 (h3.trans (Subgroup.card_dvd_of_le (sSup_thetaComponentsIn_le Z)))

theorem mem_scriptQ_of_mem_scriptY3Star_three (h : Sec17Std G A c L Y₀)
    (h146 : Item146 A (lB A)) {Z : Subgroup G} (hZ : Z ∈ scriptY3Star A (lB A))
    (hZ3 : ¬ 3 ∣ Nat.card Z) : Z ∈ scriptQ A (lB A) :=
  Proof165.mem_scriptQ_of_three (HeadProof.isE27_of_std h) h146 hZ.prop.2 hZ.prop.1.1.2 hZ3

theorem containers_le_delta_normalizer {A Z S E Q C : Subgroup G}
    (hZQ : Z ∈ scriptQ A (lB A)) (hQQ : Q ∈ scriptQ A (lB A))
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G))
    (hAC : A ≤ Subgroup.normalizer (C : Set G))
    (hSZ : S ≤ Z) (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hEZ : E ≤ Z) (hAE : A ≤ Subgroup.normalizer (E : Set G))
    (hEC : E ≤ Subgroup.normalizer (C : Set G))
    (hSC : S ≤ Subgroup.normalizer (C : Set G))
    (hQC : Q ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (C : Set G)) :
    Z ⊓ Subgroup.normalizer (C : Set G) ≤ delta A (lB A) (Subgroup.normalizer (C : Set G)) ∧
      E ≤ delta A (lB A) (Subgroup.normalizer (C : Set G)) ∧
        S ≤ delta A (lB A) (Subgroup.normalizer (C : Set G)) ∧
          Q ⊓ Subgroup.normalizer (S : Set G) ≤
            delta A (lB A) (Subgroup.normalizer (C : Set G)) := by
  have hAZC : A ≤ Subgroup.normalizer (Z ⊓ Subgroup.normalizer (C : Set G) : Subgroup G) :=
    (le_inf hAZ (hAC.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hAQS : A ≤ Subgroup.normalizer (Q ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) :=
    (le_inf (mem_scriptQ_iff.mp hQQ).2.1 (hAS.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  exact ⟨le_delta (mem_scriptQ_of_le hZQ inf_le_left hAZC) inf_le_right,
    le_delta (mem_scriptQ_of_le hZQ hEZ hAE) hEC,
    le_delta (mem_scriptQ_of_le hZQ hSZ hAS) hSC,
    le_delta (mem_scriptQ_of_le hQQ inf_le_left hAQS) hQC⟩

theorem pPrimeCoreOf_perpOf_le_centralizer (h : Sec17Std G A c L Y₀)
    (h146 : Item146 A (lB A)) (h149 : Item149 A (lB A)) {Z : Subgroup G}
    (hZ : Z ∈ scriptY3Star A (lB A)) (hZ3 : ¬ 3 ∣ Nat.card Z) :
    pPrimeCoreOf 2 (perpOf Z ((sSup (thetaComponentsIn Z) : Subgroup G))) ≤
      Subgroup.centralizer (A : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEZ : (sSup (thetaComponentsIn Z) : Subgroup G) ≤ Z := sSup_thetaComponentsIn_le Z
  have hZE : Z ≤ Subgroup.normalizer ((sSup (thetaComponentsIn Z) : Subgroup G) : Set G) :=
    le_normalizer_sSup_thetaComponentsIn Z
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := hZ.prop.1.1.2
  have hAE : A ≤ Subgroup.normalizer ((sSup (thetaComponentsIn Z) : Subgroup G) : Set G) :=
    hAZ.trans (normalizer_le_normalizer_sSup_thetaComponentsIn Z)
  have hAN : A ≤
      Subgroup.normalizer (perpOf Z ((sSup (thetaComponentsIn Z) : Subgroup G)) : Set G) :=
    fun _ ha => mem_normalizer_perpOf (hAZ ha) (hAE ha)
  refine le_centralizer_of_odd h.toSec14Std h146 h149 hZ hZ3 ?_ ?_ ?_ ?_
  · exact (Sec14.pPrimeCoreOf_le 2 _).trans (perpOf_le Z _)
  · exact (le_normalizer_perpOf hZE).trans (Sec14.normalizer_le_normalizer_pPrimeCoreOf 2 _)
  · exact (Nat.prime_two.coprime_iff_not_dvd).mp (Sec14.coprime_card_pPrimeCoreOf 2 _)
  · exact hAN.trans (Sec14.normalizer_le_normalizer_pPrimeCoreOf 2 _)

theorem pPrimeCoreOf_perpOf_le_M (h : Sec17Std G A c L Y₀) (h146 : Item146 A (lB A))
    (h149 : Item149 A (lB A)) {Z : Subgroup G} (hZ : Z ∈ scriptY3Star A (lB A))
    (hZ3 : ¬ 3 ∣ Nat.card Z) :
    pPrimeCoreOf 2 (perpOf Z ((sSup (thetaComponentsIn Z) : Subgroup G))) ≤
      Subgroup.normalizer (Y₀ : Set G) :=
  (pPrimeCoreOf_perpOf_le_centralizer h h146 h149 hZ hZ3).trans (HeadProof.centralizer_le_M h)

theorem le_M_of_isPGroup_two (h : Sec17Std G A c L Y₀) (h146 : Item146 A (lB A))
    {Z T : Subgroup G} (hZ : Z ∈ scriptY3 A (lB A)) (hZ3 : ¬ 3 ∣ Nat.card Z) (hTZ : T ≤ Z)
    (hT2 : IsPGroup 2 T) (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have hTQ : T ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le
      (Proof165.mem_scriptQ_of_three (HeadProof.isE27_of_std h) h146 hZ.2 hZ.1.1.2 hZ3)
      hTZ hAT
  exact HeadProof.le_M_of_mem_scriptQPi_two h
    ⟨⟨hTQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two T).mpr hT2⟩

theorem le_M_of_delta_normalizer_le (h : Sec17Std G A c L Y₀) (h146 : Item146 A (lB A))
    (h149 : Item149 A (lB A)) (hQ0 : pCoreOf 2 Y₀ ∈ scriptQ A (lB A))
    {Z S : Subgroup G} (hZ : Z ∈ scriptY3Star A (lB A)) (hZ3 : ¬ 3 ∣ Nat.card Z)
    (hSle : S ≤ perpOf Z ((sSup (thetaComponentsIn Z) : Subgroup G))) (hS2 : IsPGroup 2 S)
    (hSyl : ¬ 2 ∣ S.relIndex (perpOf Z ((sSup (thetaComponentsIn Z) : Subgroup G))))
    (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hΔ0 : delta A (lB A) (Subgroup.normalizer (S : Set G)) ≤
      Subgroup.normalizer (Y₀ : Set G))
    (hΔ1 : delta A (lB A) (Subgroup.normalizer (jOf S : Set G)) ≤
      Subgroup.normalizer (Y₀ : Set G))
    (hΔ2 : delta A (lB A) (Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G)) ≤
      Subgroup.normalizer (Y₀ : Set G)) :
    Z ≤ Subgroup.normalizer (Y₀ : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := (sSup (thetaComponentsIn Z) : Subgroup G) with hE
  have hEZ : E ≤ Z := by rw [hE]; exact sSup_thetaComponentsIn_le Z
  have hZE : Z ≤ Subgroup.normalizer (E : Set G) := le_normalizer_sSup_thetaComponentsIn Z
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := hZ.prop.1.1.2
  have hAE : A ≤ Subgroup.normalizer (E : Set G) :=
    hAZ.trans (normalizer_le_normalizer_sSup_thetaComponentsIn Z)
  have hSZ : S ≤ Z := hSle.trans (perpOf_le Z E)
  have hES : E ≤ Subgroup.normalizer (S : Set G) := le_normalizer_of_sylow hEZ hZE hSle hS2 hSyl
  have hZQ : Z ∈ scriptQ A (lB A) := mem_scriptQ_of_mem_scriptY3Star_three h h146 hZ hZ3
  have hN1 : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (jOf S : Set G) := by
    simpa only [Sec7.tripleOf_zero] using Sec7.normalizer_le_normalizer_tripleOf S 0
  have hN2 : Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) := by
    simpa only [Sec7.tripleOf_one] using Sec7.normalizer_le_normalizer_tripleOf S 1
  have hM0 : Z ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) :=
    ((containers_le_delta_normalizer (A := A) (Z := Z) (S := S) (E := E)
      (Q := pCoreOf 2 Y₀) (C := S) hZQ hQ0 hAZ hAS hSZ hAS hEZ hAE hES
      Subgroup.le_normalizer inf_le_right).1).trans hΔ0
  have hJ : Subgroup.normalizer (jOf S : Set G) ⊓ perpOf Z E ≤
      Subgroup.normalizer (Y₀ : Set G) :=
    ((le_inf (inf_le_right.trans (perpOf_le Z E)) inf_le_left).trans
      ((containers_le_delta_normalizer (A := A) (Z := Z) (S := S) (E := E)
        (Q := pCoreOf 2 Y₀) (C := jOf S) hZQ hQ0 hAZ (hAS.trans hN1) hSZ hAS hEZ hAE
        (hES.trans hN1) (Subgroup.le_normalizer.trans hN1) (inf_le_right.trans hN1)).1)).trans
      hΔ1
  have hΩ : Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) ⊓ perpOf Z E ≤
      Subgroup.normalizer (Y₀ : Set G) :=
    ((le_inf (inf_le_right.trans (perpOf_le Z E)) inf_le_left).trans
      ((containers_le_delta_normalizer (A := A) (Z := Z) (S := S) (E := E)
        (Q := pCoreOf 2 Y₀) (C := omegaOneZ (jOneOf S)) hZQ hQ0 hAZ (hAS.trans hN2) hSZ hAS hEZ
        hAE (hES.trans hN2) (Subgroup.le_normalizer.trans hN2) (inf_le_right.trans hN2)).1)).trans
      hΔ2
  have hPerp : perpOf Z E ≤ Subgroup.normalizer (Y₀ : Set G) :=
    le_of_normalizer_le (isSolvable_perpOf (E := E) hZ3 hZE (fun _ hJ => le_sSup hJ))
      (fun h3 => hZ3 (h3.trans (Subgroup.card_dvd_of_le (perpOf_le Z E))))
      hSle hS2 hSyl (pPrimeCoreOf_perpOf_le_M h h146 h149 hZ hZ3) hJ hΩ
  have hfr : Z ≤ perpOf Z E ⊔ (Z ⊓ Subgroup.normalizer (S : Set G)) :=
    Proof17Res12.le_sup_inf_normalizer (perpOf_le Z E) (le_normalizer_perpOf hZE)
      (CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hSle, hS2, hSyl⟩)
  exact hfr.trans (sup_le hPerp hM0)

theorem exists_three_containers (h : Sec17Std G A c L Y₀) (h146 : Item146 A (lB A))
    (hQ0 : pCoreOf 2 Y₀ ∈ scriptQ A (lB A))
    {Z S : Subgroup G} (hZ : Z ∈ scriptY3Star A (lB A)) (hZ3 : ¬ 3 ∣ Nat.card Z)
    (hSle : S ≤ perpOf Z ((sSup (thetaComponentsIn Z) : Subgroup G))) (hS2 : IsPGroup 2 S)
    (hSyl : ¬ 2 ∣ S.relIndex (perpOf Z ((sSup (thetaComponentsIn Z) : Subgroup G))))
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    ∃ Z0 Z1 Z2 : Subgroup G,
      (Z0 ∈ scriptY3Star A (lB A) ∧
        delta A (lB A) (Subgroup.normalizer (S : Set G)) ≤ Z0 ∧
          (sSup (thetaComponentsIn Z) : Subgroup G) ≤ Z0 ∧ S ≤ Z0 ∧
            pCoreOf 2 Y₀ ⊓ Subgroup.normalizer (S : Set G) ≤ Z0) ∧
      (Z1 ∈ scriptY3Star A (lB A) ∧
        delta A (lB A) (Subgroup.normalizer (jOf S : Set G)) ≤ Z1 ∧
          (sSup (thetaComponentsIn Z) : Subgroup G) ≤ Z1 ∧ S ≤ Z1 ∧
            pCoreOf 2 Y₀ ⊓ Subgroup.normalizer (S : Set G) ≤ Z1) ∧
      (Z2 ∈ scriptY3Star A (lB A) ∧
        delta A (lB A) (Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G)) ≤ Z2 ∧
          (sSup (thetaComponentsIn Z) : Subgroup G) ≤ Z2 ∧ S ≤ Z2 ∧
            pCoreOf 2 Y₀ ⊓ Subgroup.normalizer (S : Set G) ≤ Z2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := (sSup (thetaComponentsIn Z) : Subgroup G) with hE
  have hEZ : E ≤ Z := by rw [hE]; exact sSup_thetaComponentsIn_le Z
  have hZE : Z ≤ Subgroup.normalizer (E : Set G) := le_normalizer_sSup_thetaComponentsIn Z
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := hZ.prop.1.1.2
  have hAE : A ≤ Subgroup.normalizer (E : Set G) :=
    hAZ.trans (normalizer_le_normalizer_sSup_thetaComponentsIn Z)
  have hSZ : S ≤ Z := hSle.trans (perpOf_le Z E)
  have hES : E ≤ Subgroup.normalizer (S : Set G) := le_normalizer_of_sylow hEZ hZE hSle hS2 hSyl
  have hZQ : Z ∈ scriptQ A (lB A) := mem_scriptQ_of_mem_scriptY3Star_three h h146 hZ hZ3
  have hS1 : S ≠ ⊥ := by
    intro hSbot
    apply hZ.prop.1.2
    have hle : pCoreOf 2 Z ≤ S := pCoreOf_two_le_of_sylow hEZ hZE hSle hS2 hSyl
    rw [hSbot] at hle
    exact le_bot_iff.mp hle
  have hSQ : S ∈ scriptQ A (lB A) := mem_scriptQ_of_le hZQ hSZ hAS
  have hN1 : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (jOf S : Set G) := by
    simpa only [Sec7.tripleOf_zero] using Sec7.normalizer_le_normalizer_tripleOf S 0
  have hN2 : Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) := by
    simpa only [Sec7.tripleOf_one] using Sec7.normalizer_le_normalizer_tripleOf S 1
  have hJ1 : jOf S ≠ ⊥ := Sec7.jOf_ne_bot hS2 hS1
  have hJ2 : IsPGroup 2 (jOf S) := Sec7.tripleOf_isPGroup hS2 0
  have hJQ : jOf S ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hSQ (Sec7.jOf_le S) (hAS.trans hN1)
  have hO1 : omegaOneZ (jOneOf S) ≠ ⊥ := by
    simpa only [Sec7.tripleOf_one] using Sec7.tripleOf_ne_bot hS2 hS1 1
  have hO2 : IsPGroup 2 (omegaOneZ (jOneOf S)) := Sec7.tripleOf_isPGroup hS2 1
  have hOQ : omegaOneZ (jOneOf S) ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hSQ (Sec7.omegaOneZ_jOneOf_le S) (hAS.trans hN2)
  have hD0 : delta A (lB A) (Subgroup.normalizer (S : Set G)) ∈ scriptY3 A (lB A) :=
    Proof165.delta_normalizer_mem_scriptY3 h.isSimpleGroup h.nonabelian hS1 hS2 hSQ
  have hD1 : delta A (lB A) (Subgroup.normalizer (jOf S : Set G)) ∈ scriptY3 A (lB A) :=
    Proof165.delta_normalizer_mem_scriptY3 h.isSimpleGroup h.nonabelian hJ1 hJ2 hJQ
  have hD2 : delta A (lB A) (Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G)) ∈
      scriptY3 A (lB A) :=
    Proof165.delta_normalizer_mem_scriptY3 h.isSimpleGroup h.nonabelian hO1 hO2 hOQ
  obtain ⟨Z0, hD0Z0, hZ0⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hD0
  obtain ⟨Z1, hD1Z1, hZ1⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hD1
  obtain ⟨Z2, hD2Z2, hZ2⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hD2
  have hcont0 := containers_le_delta_normalizer (A := A) (Z := Z) (S := S) (E := E)
    (Q := pCoreOf 2 Y₀) (C := S) hZQ hQ0 hAZ hAS hSZ hAS hEZ hAE hES
    Subgroup.le_normalizer inf_le_right
  have hcont1 := containers_le_delta_normalizer (A := A) (Z := Z) (S := S) (E := E)
    (Q := pCoreOf 2 Y₀) (C := jOf S) hZQ hQ0 hAZ (hAS.trans hN1) hSZ hAS hEZ hAE
    (hES.trans hN1) (Subgroup.le_normalizer.trans hN1) (inf_le_right.trans hN1)
  have hcont2 := containers_le_delta_normalizer (A := A) (Z := Z) (S := S) (E := E)
    (Q := pCoreOf 2 Y₀) (C := omegaOneZ (jOneOf S)) hZQ hQ0 hAZ (hAS.trans hN2) hSZ hAS hEZ
    hAE (hES.trans hN2) (Subgroup.le_normalizer.trans hN2) (inf_le_right.trans hN2)
  exact ⟨Z0, Z1, Z2,
    ⟨hZ0, hD0Z0, hcont0.2.1.trans hD0Z0, hcont0.2.2.1.trans hD0Z0,
      hcont0.2.2.2.trans hD0Z0⟩,
    ⟨hZ1, hD1Z1, hcont1.2.1.trans hD1Z1, hcont1.2.2.1.trans hD1Z1,
      hcont1.2.2.2.trans hD1Z1⟩,
    ⟨hZ2, hD2Z2, hcont2.2.1.trans hD2Z2, hcont2.2.2.1.trans hD2Z2,
      hcont2.2.2.2.trans hD2Z2⟩⟩

section Certified

theorem not_isSolvable_sSup_of_three (h : Sec17Std G A c L Y₀) {X : Subgroup G}
    (hX : X ∈ scriptY3 A (lB A)) (hX3 : ¬ 3 ∣ Nat.card X) (hXns : ¬ Group.IsSolvable ↥X) :
    ¬ Group.IsSolvable ↥((sSup (thetaComponentsIn X) : Subgroup G)) ∧
      2 ∣ Nat.card ↥((sSup (thetaComponentsIn X) : Subgroup G)) := by
  obtain ⟨K, hK⟩ := Sec15.Proof1423.exists_mem_thetaComponents_of_not_isSolvable
    (H := ↥X) hX3 hXns
  let K' : Subgroup G := K.map X.subtype
  have hK' : K' ∈ thetaComponentsIn X := ⟨K, hK, rfl⟩
  have hK'E : K' ≤ (sSup (thetaComponentsIn X) : Subgroup G) := le_sSup hK'
  obtain ⟨n, hn⟩ := Proof17Res14.exists_suzukiModel_of_mem_thetaComponentsIn
    h.toTheoremFourHyp hX.1.1.1 hX3 hK'
  have hK'ns : ¬ Group.IsSolvable ↥K' :=
    Proof17Res14.not_isSolvable_of_suzukiModel_quot _ hn
  refine ⟨fun hs => hK'ns ?_, ?_⟩
  · haveI := hs
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hK'E) (Subgroup.inclusion_injective hK'E)
  have h2q : 2 ∣ Nat.card (↥K' ⧸ aschbacherSolvableCore 3 ↥K') :=
    (Proof1619.isPerfect_and_two_dvd_of_suzukiModel hn).2
  exact h2q.trans ((Subgroup.card_quotient_dvd_card
    (aschbacherSolvableCore 3 ↥K')).trans (Subgroup.card_dvd_of_le hK'E))

theorem not_three_dvd_of_mem_scriptY3Star_of_containers (h : Sec17Std G A c L Y₀)
    (hgen : Gen166 A c) (hnosz : NoSz166 Y₀) (h146 : Item146 A (lB A))
    (hne : OmegaNe166 A Y₀) {Z Z' : Subgroup G} (hZ : Z ∈ scriptY3Star A (lB A))
    (hZ3 : ¬ 3 ∣ Nat.card Z) (hZns : ¬ Group.IsSolvable ↥Z)
    (hZ' : Z' ∈ scriptY3Star A (lB A)) (hZ'M : ¬ Z' ≤ Subgroup.normalizer (Y₀ : Set G))
    (hEZ' : (sSup (thetaComponentsIn Z) : Subgroup G) ≤ Z') : ¬ 3 ∣ Nat.card Z' := by
  by_contra h3'
  have hO : oPrimeResidualOf 3 Z' ≠ ⊥ := fun hbot =>
    Sec14.not_three_dvd_of_oPrimeResidualOf_eq_bot hbot h3'
  obtain ⟨K, hK⟩ := Sec15.Proof1423.exists_mem_thetaComponents_of_not_isSolvable
    (H := ↥Z) hZ3 hZns
  let K' : Subgroup G := K.map Z.subtype
  have hK' : K' ∈ thetaComponentsIn Z := ⟨K, hK, rfl⟩
  have hK'Z : K' ≤ Z := le_of_mem_thetaComponentsIn hK'
  have hK'Z' : K' ≤ Z' := (le_sSup hK').trans hEZ'
  have hAK' : A ≤ Subgroup.normalizer (K' : Set G) :=
    le_normalizer_of_mem_thetaComponentsIn_of_three h hZ.prop hZ3 hK'
  have hK'Q : K' ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le (mem_scriptQ_of_mem_scriptY3Star_three h h146 hZ hZ3) hK'Z hAK'
  have hK'Δ : K' = delta A (lB A) K' :=
    le_antisymm (le_delta hK'Q le_rfl) (delta_le K')
  obtain ⟨m, hm⟩ :=
    (pCore_eq_and_subset_of_mem_thetaComponentsIn h hgen hnosz hZ.prop hZ3 hK').2.2
  exact hZ'M (hne K' Z' hK'Δ ⟨m, hm⟩ hK'Z' hZ' hO)

theorem exists_container (h : Sec17Std G A c L Y₀) (hgen : Gen166 A c) (hnosz : NoSz166 Y₀)
    (h146 : Item146 A (lB A)) (h149 : Item149 A (lB A))
    (hQ0 : pCoreOf 2 Y₀ ∈ scriptQ A (lB A)) (hne : OmegaNe166 A Y₀)
    {Z S : Subgroup G} (hZ : Z ∈ scriptY3Star A (lB A)) (hZ3 : ¬ 3 ∣ Nat.card Z)
    (hZns : ¬ Group.IsSolvable ↥Z) (hZM : ¬ Z ≤ Subgroup.normalizer (Y₀ : Set G))
    (hSle : S ≤ perpOf Z ((sSup (thetaComponentsIn Z) : Subgroup G))) (hS2 : IsPGroup 2 S)
    (hSyl : ¬ 2 ∣ S.relIndex (perpOf Z ((sSup (thetaComponentsIn Z) : Subgroup G))))
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    ∃ Z' ∈ scriptY3Star A (lB A), ¬ 3 ∣ Nat.card Z' ∧
      ¬ Z' ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        (sSup (thetaComponentsIn Z) : Subgroup G) ≤ Z' ∧ S ≤ Z' ∧
          pCoreOf 2 Y₀ ⊓ Subgroup.normalizer (S : Set G) ≤ Z' := by
  obtain ⟨Z0, Z1, Z2, ⟨hZ0, hD0, hE0, hST0, hQT0⟩, ⟨hZ1, hD1, hE1, hST1, hQT1⟩,
    ⟨hZ2, hD2, hE2, hST2, hQT2⟩⟩ := exists_three_containers h h146 hQ0 hZ hZ3 hSle hS2 hSyl hAS
  by_cases hM0 : Z0 ≤ Subgroup.normalizer (Y₀ : Set G)
  · by_cases hM1 : Z1 ≤ Subgroup.normalizer (Y₀ : Set G)
    · by_cases hM2 : Z2 ≤ Subgroup.normalizer (Y₀ : Set G)
      · exact absurd (le_M_of_delta_normalizer_le h h146 h149 hQ0 hZ hZ3 hSle hS2 hSyl hAS
          (hD0.trans hM0) (hD1.trans hM1) (hD2.trans hM2)) hZM
      · exact ⟨Z2, hZ2,
          not_three_dvd_of_mem_scriptY3Star_of_containers h hgen hnosz h146 hne hZ hZ3 hZns hZ2
            hM2 hE2, hM2, hE2, hST2, hQT2⟩
    · exact ⟨Z1, hZ1,
        not_three_dvd_of_mem_scriptY3Star_of_containers h hgen hnosz h146 hne hZ hZ3 hZns hZ1
          hM1 hE1, hM1, hE1, hST1, hQT1⟩
  · exact ⟨Z0, hZ0,
      not_three_dvd_of_mem_scriptY3Star_of_containers h hgen hnosz h146 hne hZ hZ3 hZns hZ0
        hM0 hE0, hM0, hE0, hST0, hQT0⟩

end Certified

end CFSG.RankThree.PartTwo.Sec16.Proof166Three
