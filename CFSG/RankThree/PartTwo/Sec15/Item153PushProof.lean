module

public import CFSG.RankThree.PartTwo.Sec15.Item153TwinProofMain
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Concl153Push (A Y S : Subgroup G) : Prop :=
  (∃ H : Subgroup G, Y ⊔ S ≤ H ∧ H ≤ n155 A Y ∧
      (((oResidual 2 ↥H).map H.subtype).subgroupOf (n155 A Y)).IsSubnormal ∧ Hyp315 H S) ∨
    ∃ M L' : Subgroup G, CFSG.IsMaximalTwoLocal M ∧ IsScriptLBlock M L'

@[expose] def FF153 (Y S : Subgroup G) : Prop :=
  CFSG.Open.pCoreOf 2 (Y ⊔ S) ≤ S ∧ ¬ CFSG.Quasithin.thompsonJ S ≤ CFSG.Open.pCoreOf 2 (Y ⊔ S)

@[expose] def Listed315 (Q : Type) [Group Q] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ Even n ∧ Nonempty (Q ≃* projSL 2 (GaloisField 2 n))) ∨
    Sec4.IsTripleCover Q (alternatingGroup (Fin 6)) ∨ Nonempty (Q ≃* alternatingGroup (Fin 7))

@[expose] def InvA315 (H S : Subgroup G) : Prop :=
  ∃ A' : Subgroup ↥H, CFSG.Assembly.IsElemAbelian 3 A' ∧
    (∀ B : Subgroup ↥H, CFSG.Assembly.IsElemAbelian 3 B → A' ≤ B → B = A') ∧
    S.subgroupOf H ∈ maxInvariantPiSubgroups ⊤ A' (piOf 2)

@[expose] def IsL3Type153 (Q : Type) [Group Q] : Prop :=
  (∃ (p f : ℕ) (_ : Fact p.Prime), IsLThreeEpsAt Q p f) ∨ ∃ q : ℕ, Sec4.IsSLThreeEpsAt Q q

@[expose] def IsM22Type153 (Q : Type) [Group Q] : Prop :=
  Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
    Sec4.IsTripleCover Q CFSG.Blueprint.NativeSporadic.M22

@[expose] noncomputable def Step153PushCoreR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
      ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2), ¬ CharNormal153 Y S →
        CFSG.Open.pCoreOf 2 (Y ⊔ S) ≤ S

@[expose] noncomputable def Step153PushTwinR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
      ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2), ¬ CharNormal153 Y S → FF153 Y S →
        ¬ S ≤ Subgroup.normalizer (Y : Set G) → Concl153Push A Y S

@[expose] noncomputable def Step153PushListedR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
      ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2), ¬ CharNormal153 Y S → FF153 Y S →
        S ≤ Subgroup.normalizer (Y : Set G) → Listed315 (↥Y ⧸ CFSG.pCore 2 ↥Y) →
          InvA315 (Y ⊔ S) S

@[expose] noncomputable def Step153PushHJR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
      ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2), ¬ CharNormal153 Y S → FF153 Y S →
        S ≤ Subgroup.normalizer (Y : Set G) →
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2) →
          Concl153Push A Y S

@[expose] noncomputable def Step153PushL3R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
      ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2), ¬ CharNormal153 Y S → FF153 Y S →
        S ≤ Subgroup.normalizer (Y : Set G) → IsL3Type153 (↥Y ⧸ CFSG.pCore 2 ↥Y) →
          Concl153Push A Y S

@[expose] noncomputable def Step153PushM22R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
      ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2), ¬ CharNormal153 Y S → FF153 Y S →
        S ≤ Subgroup.normalizer (Y : Set G) → IsM22Type153 (↥Y ⧸ CFSG.pCore 2 ↥Y) →
          Concl153Push A Y S

@[expose] noncomputable def Step153PushM12R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
      ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2), ¬ CharNormal153 Y S → FF153 Y S →
        S ≤ Subgroup.normalizer (Y : Set G) →
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M12) →
          Concl153Push A Y S

@[expose] noncomputable def Step153PushA10R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
      ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2), ¬ CharNormal153 Y S → FF153 Y S →
        S ≤ Subgroup.normalizer (Y : Set G) →
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) →
          Concl153Push A Y S

@[expose] noncomputable def Step153PushRestR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
      ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2), ¬ CharNormal153 Y S → FF153 Y S →
        S ≤ Subgroup.normalizer (Y : Set G) → ¬ Listed315 (↥Y ⧸ CFSG.pCore 2 ↥Y) →
        IsEmpty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2) →
        ¬ IsL3Type153 (↥Y ⧸ CFSG.pCore 2 ↥Y) → ¬ IsM22Type153 (↥Y ⧸ CFSG.pCore 2 ↥Y) →
        IsEmpty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M12) →
        IsEmpty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) →
          Concl153Push A Y S

namespace Push153

theorem charNormal153_of_thompsonJ_le {Y S : Subgroup G} (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hRS : CFSG.Open.pCoreOf 2 (Y ⊔ S) ≤ S)
    (hJ : CFSG.Quasithin.thompsonJ S ≤ CFSG.Open.pCoreOf 2 (Y ⊔ S)) : CharNormal153 Y S :=
  ⟨CFSG.Quasithin.thompsonJ S, CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hS2 hS1,
    thompsonJ_le_self S, CFSG.QuasithinUnique.Setup.characteristic_thompsonJ S,
    le_normalizer_thompsonJ_of_le hJ hRS (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)⟩

theorem listed315_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : Listed315 Q') : Listed315 Q := by
  rcases h with ⟨n, hn, hev, ⟨f⟩⟩ | ⟨hcard, ⟨φ⟩⟩ | hf
  · exact Or.inl ⟨n, hn, hev, ⟨e.trans f⟩⟩
  · right; left
    have hc : (Subgroup.center Q').map e.symm.toMonoidHom = Subgroup.center Q :=
      Subgroup.map_center_eq e.symm
    refine ⟨?_, ⟨(QuotientGroup.congr _ _ e.symm hc).symm.trans φ⟩⟩
    rw [← hc, Subgroup.card_map_of_injective e.symm.injective, hcard]
  · obtain ⟨f⟩ := hf
    exact Or.inr (Or.inr ⟨e.trans f⟩)

theorem generalizedFitting_eq_of_mem_scriptY0Star {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h149 : Item149 A (lB A)) (htwin : Claim153Twin A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) :
    generalizedFitting ↥Y = CFSG.pCore 2 ↥Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar2 : CFSG.Assembly.IsCharTwoType G := h.toTheoremFourHyp.charTwoType
  obtain ⟨-, hYX, hXN, -⟩ := facts153 h h149 hY
  set X := oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hX
  obtain ⟨M₀, hM₀⟩ := exists_mem_maximalTwoLocalsContaining hY.prop.2
  have hNXmax : IsMaximalTwoLocal (Subgroup.normalizer (X : Set G)) :=
    eq_normalizer_of_mem_maximalTwoLocalsContaining h h149 htwin hY hM₀ ▸ hM₀.1
  have hXc : IsCharacteristicP 2 ↥(Subgroup.normalizer (X : Set G)) :=
    CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal hchar2 hNXmax.1
  have hXchar : IsCharacteristicP 2 ↥X :=
    isCharacteristicP_of_le_normalizer Subgroup.le_normalizer le_rfl hXc
  have hYchar : IsCharacteristicP 2 ↥Y := isCharacteristicP_of_le_normalizer hYX hXN hXchar
  exact (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥Y 2).mp hYchar

theorem exists_hyp315_of_listed {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h149 : Item149 A (lB A)) (htwin : Claim153Twin A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2))
    (hSY : S ≤ Subgroup.normalizer (Y : Set G)) (hT : Listed315 (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hA' : InvA315 (Y ⊔ S) S) :
    ∃ H : Subgroup G, Y ⊔ S ≤ H ∧ H ≤ n155 A Y ∧
      (((oResidual 2 ↥H).map H.subtype).subgroupOf (n155 A Y)).IsSubnormal ∧ Hyp315 H S := by
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hY3 : Y = oPrimeResidualOf 3 Y := hY.prop.1.2.1
  obtain ⟨-, hYX, hXN, -⟩ := facts153 h h149 hY
  refine ⟨Y ⊔ S, le_rfl, sup_le (hYX.trans Subgroup.le_normalizer) hS.prop.1.2, ?_, ?_⟩
  · rw [oResidual_sup_eq hS2 hSY hY3, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr le_sup_left]
    exact isSubnormal_subgroupOf_normalizer hYX hXN
  · obtain ⟨e⟩ := nonempty_oResidual_quotient_equiv hS2 hSY hY3
    exact ⟨le_sup_right,
      generalizedFitting_sup_eq (generalizedFitting_eq_of_mem_scriptY0Star h h149 htwin hY)
        hS2 hSY,
      listed315_of_mulEquiv e hT, hA'⟩

end Push153

open Push153

theorem step153CharPush_of_types (h149 : Sec16.Item149S14) (htwin : Claim153TwinR)
    (hcore : Step153PushCoreR) (htw : Step153PushTwinR) (hlist : Step153PushListedR)
    (hHJ : Step153PushHJR) (hL3 : Step153PushL3R) (hM22 : Step153PushM22R)
    (hM12 : Step153PushM12R) (hA10 : Step153PushA10R) (hrest : Step153PushRestR) :
    Step153CharPush := by
  intro G _ _ A c L hR Y hY S hS hno
  have hO := hcore G A c L hR Y hY S hS hno
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hS1 : S ≠ ⊥ := by
    rintro rfl
    rw [sup_bot_eq] at hO
    exact hY.prop.2.2 (le_bot_iff.mp hO)
  have hFF : FF153 Y S := ⟨hO, fun hJ => hno (charNormal153_of_thompsonJ_le hS2 hS1 hO hJ)⟩
  change Concl153Push A Y S
  by_cases hSY : S ≤ Subgroup.normalizer (Y : Set G)
  swap
  · exact htw G A c L hR Y hY S hS hno hFF hSY
  by_cases hT : Listed315 (↥Y ⧸ CFSG.pCore 2 ↥Y)
  · exact Or.inl (exists_hyp315_of_listed hR.toSec14Std (h149 G A c L hR.toSec14Std)
      (htwin G A c L hR) hY hS hSY hT (hlist G A c L hR Y hY S hS hno hFF hSY hT))
  by_cases hJ2 : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2)
  · exact hHJ G A c L hR Y hY S hS hno hFF hSY hJ2
  by_cases hL : IsL3Type153 (↥Y ⧸ CFSG.pCore 2 ↥Y)
  · exact hL3 G A c L hR Y hY S hS hno hFF hSY hL
  by_cases hM : IsM22Type153 (↥Y ⧸ CFSG.pCore 2 ↥Y)
  · exact hM22 G A c L hR Y hY S hS hno hFF hSY hM
  by_cases hM' : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M12)
  · exact hM12 G A c L hR Y hY S hS hno hFF hSY hM'
  by_cases hA : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))
  · exact hA10 G A c L hR Y hY S hS hno hFF hSY hA
  exact hrest G A c L hR Y hY S hS hno hFF hSY hT (not_nonempty_iff.mp hJ2) hL hM
    (not_nonempty_iff.mp hM') (not_nonempty_iff.mp hA)

end CFSG.RankThree.PartTwo.Sec15
