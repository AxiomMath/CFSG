module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res4ProofHJ
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item162Res4ProofChoice
import CFSG.RankThree.PartTwo.Sec16.Item163ProofY4
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
import CFSG.RankThree.PartTwo.Sec17.Item17Q0Proof
import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofCover
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def KS162J2TwoInner : Prop :=
  ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ E : Subgroup X, Nat.card E = 9 →
      ∀ P : Subgroup (MulAut X), IsPGroup 2 P →
        E.map (MulAut.conj : X →* MulAut X) ≤ Subgroup.normalizer (P : Set (MulAut X)) →
          P ≤ (MulAut.conj : X →* MulAut X).range

@[expose] def KS162J2NormSolv : Prop :=
  ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ E : Subgroup X, Nat.card E = 9 →
      ∀ S ∈ maxInvariantPiSubgroups ⊤ E (piOf 2),
        Group.IsSolvable ↥(Subgroup.normalizer (S : Set X))

@[expose] def Step162UJHJStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      CFSG.Open.pCoreOf 2 L = ⊥ →
      ∀ Y₁ Y₂ S₁ S₂ : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂ →
      ¬ S₁ ≤ S₂ → ¬ S₂ ≤ S₁ →
      ¬ TransOn A (lB A) (xA A)
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) →
      ∀ J ∈ scriptY0 A (lB A),
        J ≤ delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G)) →
        Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)) →
        (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
          L' = (L' ⊓ J) ⊔ CFSG.Open.pCoreOf 2 L') →
        L ≤ Y₁ → L ≤ Y₂ → Y₁ = L ⊔ CFSG.Open.pCoreOf 2 Y₁ → Y₂ = L ⊔ CFSG.Open.pCoreOf 2 Y₂ →
        Y₁ ⊓ Y₂ = L →
        S₁ ⊓ S₂ ∈ scriptQPiStar A (lB A) L (piOf 2) →
        oPrimeResidualOf 3
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) = ⊥

namespace Res162Six

variable {G : Type} [Group G] [Finite G]

theorem eq_of_sup_isPGroup {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h155 : Item155 A (lB A)) (h153 : Item153Main A (lB A)) (hL4 : L ∈ scriptY4 A (lB A))
    {D : Subgroup G} (hDQ : D ∈ scriptQ A (lB A)) (hD2 : IsPGroup 2 D) (hD1 : D ≠ ⊥)
    (hLD : L ≤ Subgroup.normalizer (D : Set G)) (htop : L ⊔ D ≠ ⊤)
    (hX4 : oPrimeResidualOf 3 (L ⊔ D) ∈ scriptY4 A (lB A))
    {K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ scriptY0Star A (lB A)) (hK₂ : K₂ ∈ scriptY0Star A (lB A))
    (hXK₁ : oPrimeResidualOf 3 (L ⊔ D) ≤ K₁) (hXK₂ : oPrimeResidualOf 3 (L ⊔ D) ≤ K₂)
    (hN₁ : L ⊔ D ≤ Subgroup.normalizer (K₁ : Set G))
    (hN₂ : L ⊔ D ≤ Subgroup.normalizer (K₂ : Set G)) : K₁ = K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY'D : L ⊔ D ≤ Subgroup.normalizer (D : Set G) := sup_le hLD Subgroup.le_normalizer
  have hDO : D ≤ CFSG.Open.pCoreOf 2 (L ⊔ D) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hY'D hD2
  have hO2 : CFSG.Open.pCoreOf 2 (L ⊔ D) ≠ ⊥ := fun h0 => hD1 (le_bot_iff.mp (h0 ▸ hDO))
  have hY'Δ : L ⊔ D = delta A (lB A) (L ⊔ D) :=
    le_antisymm (sup_le (hL4.2.2.1.le.trans (delta_mono le_sup_left)) (le_delta hDQ le_sup_right))
      (delta_le _)
  have hAY' : A ≤ Subgroup.normalizer ((L ⊔ D : Subgroup G) : Set G) :=
    le_normalizer_sup hL4.1.2 hDQ.1.2.2
  have hY'3 : L ⊔ D ∈ scriptY3 A (lB A) := ⟨⟨⟨htop, hAY'⟩, hO2⟩, hY'Δ⟩
  have hLX : L ≤ oPrimeResidualOf 3 (L ⊔ D) :=
    hL4.2.1.le.trans (oPrimeResidualOf_mono 3 le_sup_left)
  have hY'eq : L ⊔ D = oPrimeResidualOf 3 (L ⊔ D) ⊔ CFSG.Open.pCoreOf 2 (L ⊔ D) :=
    le_antisymm (sup_le (hLX.trans le_sup_left) (hDO.trans le_sup_right))
      (sup_le (Subgroup.map_subtype_le _) (CFSG.LieType.BorelTits.pCoreOf_le 2 _))
  have hΩ : omg155 A (oPrimeResidualOf 3 (L ⊔ D)) := Or.inr ⟨c, L, h.zpowers_mem_omegaA, h.mem_lA,
    by rw [inf_eq_left.mpr hLX, sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)]⟩
  exact Proof162.eq_of_mem_gam155 h155 h153 hY'3 hX4 hY'eq ⟨hK₁, hXK₁, hN₁⟩ ⟨hK₂, hXK₂, hN₂⟩
    (Or.inl hΩ)

theorem le_pCoreOf_of_cover {L Y P : Subgroup G} (hLY : L ≤ Y)
    (hcov : Y ≤ L ⊔ CFSG.Open.pCoreOf 2 Y) (hPY : P ≤ Y) (hP2 : IsPGroup 2 P)
    (hLP : L ≤ Subgroup.normalizer (P : Set G)) : P ≤ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYO : Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hPO2 : IsPGroup 2 (P ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hP2 (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)
      (hPY.trans hYO)
  have hPOY : P ⊔ CFSG.Open.pCoreOf 2 Y ≤ Y := sup_le hPY (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
  have hN : Y ≤ Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) :=
    hcov.trans (sup_le (le_normalizer_sup hLP (hLY.trans hYO))
      (le_sup_right.trans Subgroup.le_normalizer))
  exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPOY hN hPO2)

theorem inf_eq_of_pCoreOf_inf {L Y₁ Y₂ : Subgroup G} (hL₁ : L ≤ Y₁) (hL₂ : L ≤ Y₂)
    (hc₁ : Y₁ ≤ L ⊔ CFSG.Open.pCoreOf 2 Y₁) (hc₂ : Y₂ ≤ L ⊔ CFSG.Open.pCoreOf 2 Y₂)
    (hD : CFSG.Open.pCoreOf 2 Y₁ ⊓ CFSG.Open.pCoreOf 2 Y₂ = ⊥) : Y₁ ⊓ Y₂ = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL₁O : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₁ : Set G) :=
    hL₁.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₁)
  have hP : CFSG.Open.pCoreOf 2 Y₁ ⊓ Y₂ ≤ CFSG.Open.pCoreOf 2 Y₂ :=
    le_pCoreOf_of_cover hL₂ hc₂ inf_le_right
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₁).to_le inf_le_left)
      (Late.le_normalizer_inf hL₁O (hL₂.trans Subgroup.le_normalizer))
  have hP1 : CFSG.Open.pCoreOf 2 Y₁ ⊓ Y₂ = ⊥ := by
    rw [eq_bot_iff, ← hD]
    exact le_inf inf_le_left hP
  refine le_antisymm (fun y hy => ?_) (le_inf hL₁ hL₂)
  have hy1 : y ∈ ((L ⊔ CFSG.Open.pCoreOf 2 Y₁ : Subgroup G) : Set G) := hc₁ hy.1
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L _ hL₁O] at hy1
  obtain ⟨l, hl, o, ho, rfl⟩ := hy1
  have hoY : o ∈ Y₂ := by
    have := mul_mem (inv_mem (hL₂ hl)) hy.2
    rwa [inv_mul_cancel_left] at this
  have ho1 : o ∈ CFSG.Open.pCoreOf 2 Y₁ ⊓ Y₂ := ⟨ho, hoY⟩
  rw [hP1, Subgroup.mem_bot] at ho1
  show l * o ∈ L
  rw [ho1, mul_one]
  exact hl

theorem mem_scriptY4_of_j2_cover
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {Y : Subgroup G} (hY : Y ∈ scriptY4 A (lB A)) (hLY : L ≤ Y)
    (hcov : Y ≤ L ⊔ CFSG.Open.pCoreOf 2 Y) : L ∈ scriptY4 A (lB A) :=
  ⟨⟨fun hL => hY.1.1 (top_le_iff.mp (hL ▸ hLY)), h.toSec13Data.le_normalizer⟩,
    eq_oPrimeResidualOf_of_j2
      (Sec6.isPerfect_of_mem_thetaComponentsAt h.toSec13Data.mem_thetaComponentsAt) hJ,
    eq_delta_of_j2 h hJ hY hLY hcov, isQuasisimple_of_cover hY hLY hcov (three_dvd_card_of_j2 hJ)⟩

theorem pCoreOf_inf_eq_bot {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h155 : Item155 A (lB A)) (h153 : Item153Main A (lB A)) (h1444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h142 : Concl142 A (lB A))
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hL4 : L ∈ scriptY4 A (lB A)) {Y₁ Y₂ : Subgroup G} (hY₁ : Y₁ ∈ scriptY0Star A (lB A))
    (hY₂ : Y₂ ∈ scriptY0Star A (lB A)) (hL₁ : L ≤ Y₁) (hL₂ : L ≤ Y₂)
    (hc₁ : Y₁ = (Y₁ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₁) (hne : Y₁ ≠ Y₂) :
    CFSG.Open.pCoreOf 2 Y₁ ⊓ CFSG.Open.pCoreOf 2 Y₂ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hD1
  set D := CFSG.Open.pCoreOf 2 Y₁ ⊓ CFSG.Open.pCoreOf 2 Y₂ with hDdef
  have hO₁Q : CFSG.Open.pCoreOf 2 Y₁ ∈ scriptQ A (lB A) :=
    Sec17.Proof17Q0.pCoreOf_mem_scriptQ_of_cover h.toSec14Std h1444 h146 hbot h142 hY₁.prop.1
      (Or.inl hc₁)
  have hAO₁ : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₁ : Set G) :=
    hY₁.prop.1.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₁)
  have hAO₂ : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₂ : Set G) :=
    hY₂.prop.1.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₂)
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := Late.le_normalizer_inf hAO₁ hAO₂
  have hDQ : D ∈ scriptQ A (lB A) := mem_scriptQ_of_le hO₁Q inf_le_left hAD
  have hD2 : IsPGroup 2 D :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₁).to_le inf_le_left
  have hLD : L ≤ Subgroup.normalizer (D : Set G) :=
    Late.le_normalizer_inf (hL₁.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₁))
      (hL₂.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₂))
  have hLD₁ : L ⊔ D ≤ Y₁ :=
    sup_le hL₁ (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₁))
  have hLD₂ : L ⊔ D ≤ Y₂ :=
    sup_le hL₂ (inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₂))
  have htop : L ⊔ D ≠ ⊤ := fun ht => hY₁.prop.1.1.1 (top_le_iff.mp (ht ▸ hLD₁))
  set X := oPrimeResidualOf 3 (L ⊔ D) with hXdef
  have hXY : X ≤ L ⊔ D := Subgroup.map_subtype_le _
  have hLX : L ≤ X := hL4.2.1.le.trans (oPrimeResidualOf_mono 3 le_sup_left)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Proof1515Res.le_normalizer_oRes3 (le_normalizer_sup hL4.1.2 hAD)
  have hXcov : X ≤ L ⊔ (X ⊓ D) := by
    intro x hx
    have hx' : x ∈ ((L ⊔ D : Subgroup G) : Set G) := hXY hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L D hLD] at hx'
    obtain ⟨l, hl, d, hd, rfl⟩ := hx'
    have hdX : d ∈ X := by
      have := mul_mem (inv_mem (hLX hl)) hx
      rwa [inv_mul_cancel_left] at this
    exact mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right ⟨hdX, hd⟩)
  have hXΔ : X = delta A (lB A) X := by
    refine le_antisymm (hXcov.trans (sup_le (hL4.2.2.1.le.trans (delta_mono hLX)) ?_))
      (delta_le _)
    exact le_delta (mem_scriptQ_of_le hDQ inf_le_right (Late.le_normalizer_inf hAX hAD))
      inf_le_left
  have hcov₁ : Y₁ ≤ L ⊔ CFSG.Open.pCoreOf 2 Y₁ := by
    have := hc₁.le
    rwa [inf_eq_right.mpr hL₁] at this
  have hX4 : X ∈ scriptY4 A (lB A) :=
    ⟨⟨fun ht => htop (top_le_iff.mp (ht ▸ hXY)), hAX⟩, (Proof1515Res.oRes3_idem _).symm, hXΔ,
      isQuasisimple_of_cover hY₁.prop.1 (hXY.trans hLD₁) (hcov₁.trans (sup_le_sup_right hLX _))
        ((three_dvd_card_of_j2 hJ).trans (Subgroup.card_dvd_of_le hLX))⟩
  exact hne (eq_of_sup_isPGroup h h155 h153 hL4 hDQ hD2 hD1 hLD htop hX4 hY₁ hY₂
    (hXY.trans hLD₁) (hXY.trans hLD₂) (hLD₁.trans Subgroup.le_normalizer)
    (hLD₂.trans Subgroup.le_normalizer))

theorem inf_centralizer_eq_bot {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h155 : Item155 A (lB A)) (h153 : Item153Main A (lB A)) (hL4 : L ∈ scriptY4 A (lB A))
    (hL1 : L ≠ ⊥) {Y₁ Y₂ S₁ S₂ : Subgroup G} (hmax : MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂)
    (hL₁ : L ≤ Y₁) (hL₂ : L ≤ Y₂) :
    S₁ ⊓ S₂ ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hQ1
  set Q := S₁ ⊓ S₂ ⊓ Subgroup.centralizer (L : Set G) with hQdef
  have hS₁ := hmax.1.s₁.prop
  have hS₂ := hmax.1.s₂.prop
  have hAU : A ≤ Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hS₁.1.1.1.2.2 hS₂.1.1.1.2.2
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    Late.le_normalizer_inf hAU (hL4.1.2.trans (Res162d.normalizer_le_normalizer_centralizer' L))
  have hQS₁ : Q ≤ S₁ := inf_le_left.trans inf_le_left
  have hQS₂ : Q ≤ S₂ := inf_le_left.trans inf_le_right
  have hQQ : Q ∈ scriptQ A (lB A) := mem_scriptQ_of_le hS₁.1.1 hQS₁ hAQ
  have hQ2 : IsPGroup 2 Q := (isPGroup_of_mem_scriptQPi Nat.prime_two hS₁).to_le hQS₁
  have hQL : Q ≤ Subgroup.centralizer (L : Set G) := inf_le_right
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.le_centralizer_iff.mp hQL).trans (Subgroup.centralizer_le_normalizer _)
  have hQN : Q ≤ Subgroup.normalizer (L : Set G) :=
    hQL.trans (Subgroup.centralizer_le_normalizer _)
  have hNL : Subgroup.normalizer (L : Set G) ≠ ⊤ :=
    (normalizer_mem_scriptY h.isSimpleGroup hL4.1 hL1).1
  have htop : L ⊔ Q ≠ ⊤ := fun ht =>
    hNL (top_le_iff.mp (ht ▸ sup_le Subgroup.le_normalizer hQN))
  have hres : oPrimeResidualOf 3 (L ⊔ Q) = L :=
    ((oPrimeResidualOf_eq_of_le le_sup_left fun x hx k hk =>
      mem_of_pow_three_of_mem_sup hQN hQ2 hx hk).symm.trans hL4.2.1.symm)
  have hX4 : oPrimeResidualOf 3 (L ⊔ Q) ∈ scriptY4 A (lB A) := by
    rw [hres]
    exact hL4
  have hX₁ : oPrimeResidualOf 3 (L ⊔ Q) ≤ Y₁ := by
    rw [hres]
    exact hL₁
  have hX₂ : oPrimeResidualOf 3 (L ⊔ Q) ≤ Y₂ := by
    rw [hres]
    exact hL₂
  have hYY := eq_of_sup_isPGroup h h155 h153 hL4 hQQ hQ2 hQ1 hLQ htop hX4 hmax.1.mem₁ hmax.1.mem₂
    hX₁ hX₂ (sup_le (hL₁.trans Subgroup.le_normalizer) (hQS₁.trans hS₁.1.2))
    (sup_le (hL₂.trans Subgroup.le_normalizer) (hQS₂.trans hS₂.1.2))
  exact hmax.1.not_conj ⟨1, one_mem _, by rw [Late.map_conj_one, hYY]⟩

omit [Finite G] in
theorem le_centralizer_of_inf_centralizer {L U : Subgroup G} {c : G}
    (hcU : c ∈ Subgroup.normalizer (U : Set G)) (hcL : c ∈ Subgroup.centralizer (L : Set G))
    (hUL : U ≤ Subgroup.normalizer (L : Set G))
    (hUC : U ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    U ≤ Subgroup.centralizer ({c} : Set G) := by
  intro u hu
  have hw1 : c * u * c⁻¹ * u⁻¹ ∈ U :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hcU u).mp hu) (inv_mem hu)
  have hw2 : c * u * c⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    have hu' : u * c⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
      (Subgroup.mem_normalizer_iff.mp
        (Res162d.normalizer_le_normalizer_centralizer' L (hUL hu)) c⁻¹).mp (inv_mem hcL)
    have e : c * u * c⁻¹ * u⁻¹ = c * (u * c⁻¹ * u⁻¹) := by group
    rw [e]
    exact mul_mem hcL hu'
  have hw : c * u * c⁻¹ * u⁻¹ ∈ U ⊓ Subgroup.centralizer (L : Set G) := ⟨hw1, hw2⟩
  rw [hUC, Subgroup.mem_bot] at hw
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc u * c = c * u * c⁻¹ * u⁻¹ * (u * c) := by rw [hw, one_mul]
    _ = c * u := by group

theorem le_of_maxCE {A : Subgroup G} {Y₁ Y₂ S₁ S₂ : Subgroup G}
    (hmax : MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂) {T : Subgroup G} (hTQ : T ∈ scriptQ A (lB A))
    (hT2 : IsPGroup 2 T) (hT₁ : T ≤ Subgroup.normalizer (Y₁ : Set G))
    (hT₂ : T ≤ Subgroup.normalizer (Y₂ : Set G)) (hUT : S₁ ⊓ S₂ ≤ T) : T ≤ S₁ ⊓ S₂ := by
  have hpi : IsPiSubgroup (piOf 2) T := (isPiSubgroup_piOf_iff Nat.prime_two T).mpr hT2
  obtain ⟨S₁', hTS₁', hS₁'⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y₁ : Set G)) (piOf 2)))
    (⟨⟨hTQ, hT₁⟩, hpi⟩ : T ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y₁ : Set G)) (piOf 2))
  obtain ⟨S₂', hTS₂', hS₂'⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y₂ : Set G)) (piOf 2)))
    (⟨⟨hTQ, hT₂⟩, hpi⟩ : T ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y₂ : Set G)) (piOf 2))
  have hTS : T ≤ S₁' ⊓ S₂' := le_inf hTS₁' hTS₂'
  have hne : S₁' ⊓ S₂' ≠ ⊥ := fun h0 =>
    hmax.1.ne_bot (le_bot_iff.mp (h0 ▸ (hUT.trans hTS)))
  have hcard := hmax.2 Y₁ Y₂ S₁' S₂' ⟨hmax.1.mem₁, hmax.1.mem₂, hS₁', hS₂', hne, hmax.1.not_conj⟩
  have hle : Nat.card T ≤ Nat.card (S₁ ⊓ S₂ : Subgroup G) :=
    (Subgroup.card_le_of_le hTS).trans hcard
  exact (Subgroup.eq_of_le_of_card_ge hUT hle).symm.le

theorem nonempty_mulEquiv_j2
    {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hO : CFSG.Open.pCoreOf 2 L = ⊥) : Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  have hD := h.toSec13Data
  have hLtop : L ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hD.ne_one
      (top_le_iff.mp (htop ▸ hD.le_centralizer))
  obtain ⟨ψ⟩ : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    Sec12.gap128OTwoHJ ↥L (h.toTheoremFourHyp.sectionFourHyp hLtop)
      (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) hJ
  have hP2 : CFSG.pCore 2 ↥L = ⊥ := by
    have h0 : (CFSG.Open.pCore 2 ↥L).map L.subtype = ⊥ := hO
    exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h0
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hP2).trans QuotientGroup.quotientBot).symm.trans ψ⟩

theorem mem_scriptQPiStar_of_faithful
    (hK : KS162J2TwoInner) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hO : CFSG.Open.pCoreOf 2 L = ⊥) {Y₁ Y₂ S₁ S₂ : Subgroup G}
    (hmax : MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂) (hL₁ : L ≤ Y₁) (hL₂ : L ≤ Y₂)
    (hUL : S₁ ⊓ S₂ ≤ Subgroup.normalizer (L : Set G))
    (hUC : S₁ ⊓ S₂ ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hUc : S₁ ⊓ S₂ ≤ Subgroup.centralizer ({c} : Set G)) :
    S₁ ⊓ S₂ ∈ scriptQPiStar A (lB A) L (piOf 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hD := h.toSec13Data
  set U := S₁ ⊓ S₂ with hUdef
  have hS₁ := hmax.1.s₁.prop
  have hS₂ := hmax.1.s₂.prop
  have hU2 : IsPGroup 2 U := (isPGroup_of_mem_scriptQPi Nat.prime_two hS₁).to_le inf_le_left
  have hAU : A ≤ Subgroup.normalizer (U : Set G) :=
    Late.le_normalizer_inf hS₁.1.1.1.2.2 hS₂.1.1.1.2.2
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := hD.le_centralizer
  have hmemQ : ∀ T : Subgroup G, T ≤ Subgroup.centralizer ({c} : Set G) → IsPGroup 2 T →
      A ≤ Subgroup.normalizer (T : Set G) → T ∈ scriptQ A (lB A) := fun T hTc hT2 hAT =>
    (mem_scriptQ_of_hj_point h.toSec14Std hJ ⟨hTc.trans
      (centralizer_singleton_le_normalizer_zpowers c),
      isPiSubgroup_piCompl_three_of_piOf_two ((isPiSubgroup_piOf_iff Nat.prime_two T).mpr hT2),
      hAT⟩).1
  obtain ⟨φ⟩ := nonempty_mulEquiv_j2 h hJ hO
  have hZ : Subgroup.center ↥L = ⊥ :=
    Sec13.center_eq_bot_of_mulEquiv φ (KFacts.KS14.center_nativeJ2_eq_bot h415)
  have hconj_inj : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro l hl
    rw [← hZ, Subgroup.mem_center_iff]
    intro y
    have h1 := DFunLike.congr_fun (MonoidHom.mem_ker.mp hl) y
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc y * l = l * y * l⁻¹ * l := by rw [h1]
      _ = l * y := by group
  obtain ⟨-, h9, hAc⟩ := j2_point_facts hD hJ
  have hE9 : Nat.card (A.subgroupOf L) = 9 := by
    rw [← Subgroup.inf_subgroupOf_right, ← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv
  set ρ := L.normalizerMonoidHom with hρdef
  set P := (U.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ with hPdef
  have hP2 : IsPGroup 2 P :=
    (hU2.comap_of_injective (Subgroup.normalizer (L : Set G)).subtype
      (Subgroup.normalizer (L : Set G)).subtype_injective).map ρ
  have hρe : ∀ e : ↥L, MulAut.conj e = ρ ⟨(e : G), Subgroup.le_normalizer e.2⟩ := by
    intro e
    ext y
    rw [hρdef, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp [MulAut.conj_apply]
  have hEP : (A.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L) ≤
      Subgroup.normalizer (P : Set (MulAut ↥L)) := by
    rintro _ ⟨e, he, rfl⟩
    rw [hρe e]
    refine Subgroup.le_normalizer_map ρ ⟨_, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro n
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have heA : (e : G) ∈ A := Subgroup.mem_subgroupOf.mp he
    simpa using Subgroup.mem_normalizer_iff.mp (hAU heA) (n : G)
  have hPinn := hK ↥L ⟨φ⟩ (A.subgroupOf L) hE9 P hP2 hEP
  have hinner : ∀ u (hu : u ∈ U), ∃ l : ↥L, MulAut.conj l = ρ ⟨u, hUL hu⟩ := by
    intro u hu
    have hmem : ρ ⟨u, hUL hu⟩ ∈ P := ⟨⟨u, hUL hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    obtain ⟨l, hl⟩ := hPinn hmem
    exact ⟨l, hl⟩
  have hact : ∀ u (hu : u ∈ U) (l : ↥L), MulAut.conj l = ρ ⟨u, hUL hu⟩ →
      ∀ y ∈ L, u * y * u⁻¹ = (l : G) * y * (l : G)⁻¹ := by
    intro u hu l hl y hy
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hl ⟨y, hy⟩)
    rw [hρdef, Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    simpa [MulAut.conj_apply] using h1.symm
  have hcent : ∀ u (hu : u ∈ U) (l : ↥L), MulAut.conj l = ρ ⟨u, hUL hu⟩ →
      (l : G)⁻¹ * u ∈ Subgroup.centralizer (L : Set G) := by
    intro u hu l hl
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    calc y * ((l : G)⁻¹ * u) = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * u := by group
      _ = (l : G)⁻¹ * (u * y * u⁻¹) * u := by rw [hact u hu l hl y hy]
      _ = (l : G)⁻¹ * u * y := by group
  set Uh := (P.comap (MulAut.conj : ↥L →* MulAut ↥L)).map L.subtype with hUhdef
  have hUh2 : IsPGroup 2 Uh := (hP2.comap_of_injective _ hconj_inj).map L.subtype
  have hUhL : Uh ≤ L := Subgroup.map_subtype_le _
  have hAUh : A ≤ Subgroup.normalizer (Uh : Set G) := by
    rw [hAc]
    refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (Uh : Set G) ?_))
      (inf_le_normalizer_map_comap _ hEP)
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hLc (hUhL hv)))
  have hUhinv : Uh ∈ invariantPiSubgroups L A (piOf 2) :=
    ⟨hUhL, (isPiSubgroup_piOf_iff Nat.prime_two Uh).mpr hUh2, hAUh⟩
  obtain ⟨V, hV, hUhV⟩ := exists_le_mem_maxInvariantPiSubgroups hUhinv
  have hstar : scriptQPiStar A (lB A) L (piOf 2) = maxInvariantPiSubgroups L A (piOf 2) :=
    scriptQPiStar_two_eq fun W hW => hmemQ W (hW.1.trans hLc)
      ((isPiSubgroup_piOf_iff Nat.prime_two W).mp hW.2.1) hW.2.2
  have hVL : V ≤ L := hV.prop.1
  have hV2 : IsPGroup 2 V := (isPiSubgroup_piOf_iff Nat.prime_two V).mp hV.prop.2.1
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := hV.prop.2.2
  have hlV : ∀ u (hu : u ∈ U) (l : ↥L), MulAut.conj l = ρ ⟨u, hUL hu⟩ → (l : G) ∈ V := by
    intro u hu l hl
    apply hUhV
    refine ⟨l, ?_, rfl⟩
    show MulAut.conj l ∈ P
    rw [hl]
    exact ⟨⟨u, hUL hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  have hconjV : ∀ u ∈ U, ∀ v ∈ V, u * v * u⁻¹ ∈ V := by
    intro u hu v hv
    obtain ⟨l, hl⟩ := hinner u hu
    rw [hact u hu l hl v (hVL hv)]
    exact mul_mem (mul_mem (hlV u hu l hl) hv) (inv_mem (hlV u hu l hl))
  have hUV : U ≤ Subgroup.normalizer (V : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨hconjV u hu v, fun hv => ?_⟩
    have h1 := hconjV u⁻¹ (inv_mem hu) _ hv
    have e : u⁻¹ * (u * v * u⁻¹) * u⁻¹⁻¹ = v := by group
    rwa [e] at h1
  have hT2 : IsPGroup 2 (U ⊔ V : Subgroup G) := IsPGroup.to_sup_of_normal_right' hU2 hV2 hUV
  have hTQ : U ⊔ V ∈ scriptQ A (lB A) :=
    hmemQ _ (sup_le hUc (hVL.trans hLc)) hT2 (le_normalizer_sup hAU hAV)
  have hTN₁ : U ⊔ V ≤ Subgroup.normalizer (Y₁ : Set G) :=
    sup_le (inf_le_left.trans hS₁.1.2) (hVL.trans (hL₁.trans Subgroup.le_normalizer))
  have hTN₂ : U ⊔ V ≤ Subgroup.normalizer (Y₂ : Set G) :=
    sup_le (inf_le_right.trans hS₂.1.2) (hVL.trans (hL₂.trans Subgroup.le_normalizer))
  have hVU : V ≤ U := le_sup_right.trans (le_of_maxCE hmax hTQ hT2 hTN₁ hTN₂ le_sup_left)
  have hUV' : U ≤ V := by
    intro u hu
    obtain ⟨l, hl⟩ := hinner u hu
    have hz : (l : G)⁻¹ * u ∈ U ⊓ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hVU (hlV u hu l hl))) hu, hcent u hu l hl⟩
    rw [hUC, Subgroup.mem_bot, inv_mul_eq_one] at hz
    rw [← hz]
    exact hlV u hu l hl
  rw [hstar, le_antisymm hUV' hVU]
  exact hV

theorem false_of_le_normalizer_j2
    (hN : KS162J2NormSolv) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hO : CFSG.Open.pCoreOf 2 L = ⊥) {U : Subgroup G}
    (hU : U ∈ scriptQPiStar A (lB A) L (piOf 2)) {I : Subgroup G} (hLI : L ≤ I)
    (hIL : I ≤ L ⊔ CFSG.Open.pCoreOf 2 I) {J : Subgroup G} (hJ4 : J ∈ scriptY4 A (lB A))
    (hJI : J ≤ I) (hJU : J ≤ Subgroup.normalizer (U : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := hD.le_centralizer
  obtain ⟨φ⟩ := nonempty_mulEquiv_j2 h hJ hO
  obtain ⟨-, h9, hAc⟩ := j2_point_facts hD hJ
  have hE9 : Nat.card (A.subgroupOf L) = 9 := by
    rw [← Subgroup.inf_subgroupOf_right, ← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv
  have hmemQ : ∀ W ∈ invariantPiSubgroups L A (piOf 2), W ∈ scriptQ A (lB A) := fun W hW =>
    (mem_scriptQ_of_hj_point h.toSec14Std hJ ⟨(hW.1.trans hLc).trans
      (centralizer_singleton_le_normalizer_zpowers c),
      isPiSubgroup_piCompl_three_of_piOf_two hW.2.1, hW.2.2⟩).1
  have hstar : scriptQPiStar A (lB A) L (piOf 2) = maxInvariantPiSubgroups L A (piOf 2) :=
    scriptQPiStar_two_eq hmemQ
  have hAinv : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G) := by
    intro V hVL hV
    rw [hAc]
    refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (V : Set G) ?_)) hV
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc (hVL hv))
  have hUmax : U ∈ maxInvariantPiSubgroups L A (piOf 2) := hstar ▸ hU
  have hU' : U.subgroupOf L ∈ maxInvariantPiSubgroups ⊤ (A.subgroupOf L) (piOf 2) := by
    have h1 := ((maxInvariant_two_transport (MonoidHom.id ↥L) Function.surjective_id
      (by rw [MonoidHom.ker_id]; exact IsPGroup.of_bot) hAinv).1 U hUmax).1
    rwa [Subgroup.map_id, Subgroup.map_id] at h1
  have hsolv : Group.IsSolvable ↥(Subgroup.normalizer ((U.subgroupOf L : Subgroup ↥L) :
      Set ↥L)) := hN ↥L ⟨φ⟩ (A.subgroupOf L) hE9 _ hU'
  have hUL : U ≤ L := hU.prop.1.2
  set P := CFSG.pCore 2 ↥I with hPdef
  set ψ : ↥L →* ↥I ⧸ P := (QuotientGroup.mk' P).comp (Subgroup.inclusion hLI) with hψdef
  have hPmem : ∀ i : ↥I, i ∈ P → (i : G) ∈ CFSG.Open.pCoreOf 2 I := by
    intro i hi
    have h' : i ∈ CFSG.Open.pCore 2 ↥I := by exact hi
    exact Subgroup.mem_map_of_mem I.subtype h'
  have hLO : L ⊓ CFSG.Open.pCoreOf 2 I ≤ CFSG.Open.pCoreOf 2 L := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
    · exact (le_inf Subgroup.le_normalizer
        (hLI.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) I).to_le inf_le_right
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro l hl
    have h1 : Subgroup.inclusion hLI l ∈ P := by
      have := MonoidHom.mem_ker.mp hl
      rwa [hψdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at this
    have h2 : (l : G) ∈ CFSG.Open.pCoreOf 2 L := hLO ⟨l.2, hPmem _ h1⟩
    rw [hO, Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.mpr (Subtype.ext h2)
  have hψsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective P q
    have hi : (i : G) ∈ ((L ⊔ CFSG.Open.pCoreOf 2 I : Subgroup G) : Set G) := hIL i.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L _
      (hLI.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I))] at hi
    obtain ⟨l, hl, o, ho, hlo⟩ := hi
    obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.mp
      (show o ∈ (CFSG.Open.pCore 2 ↥I).map I.subtype from ho)
    have ho'P : o' ∈ P := by rwa [hPdef]
    have hi' : i = Subgroup.inclusion hLI ⟨l, hl⟩ * o' := Subtype.ext hlo.symm
    have h1 : QuotientGroup.mk' P o' = 1 := (QuotientGroup.eq_one_iff o').mpr ho'P
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hi', map_mul, h1, mul_one]
    try rfl
  set e := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩ with hedef
  set θ : ↥I →* ↥L := e.symm.toMonoidHom.comp (QuotientGroup.mk' P) with hθdef
  have hθL : ∀ l : ↥L, θ (Subgroup.inclusion hLI l) = l := by
    intro l
    rw [hθdef, MonoidHom.comp_apply]
    exact e.symm_apply_eq.mpr rfl
  have hθker : ∀ i : ↥I, θ i = 1 → i ∈ P := by
    intro i hi
    rw [hθdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hi
    exact hi
  have hconj : ∀ g : ↥I, (g : G) ∈ Subgroup.normalizer (U : Set G) →
      ∀ u ∈ U.subgroupOf L, θ g * u * (θ g)⁻¹ ∈ U.subgroupOf L := by
    intro g hg u hu
    have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have hguU : (g : G) * u * (g : G)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hg u).mp huU
    have hgu : g * Subgroup.inclusion hLI u * g⁻¹ =
        Subgroup.inclusion hLI ⟨(g : G) * u * (g : G)⁻¹, hUL hguU⟩ := Subtype.ext rfl
    have h1 : θ g * u * (θ g)⁻¹ = θ (g * Subgroup.inclusion hLI u * g⁻¹) := by
      rw [map_mul, map_mul, map_inv, hθL u]
    rw [h1, hgu, hθL]
    exact Subgroup.mem_subgroupOf.mpr hguU
  set f : ↥(I ⊓ Subgroup.normalizer (U : Set G)) →* ↥L :=
    θ.comp (Subgroup.inclusion (inf_le_left : I ⊓ Subgroup.normalizer (U : Set G) ≤ I))
    with hfdef
  have hfrange : f.range ≤ Subgroup.normalizer ((U.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    rintro _ ⟨x, rfl⟩
    have hx := hconj (Subgroup.inclusion inf_le_left x) (Subgroup.mem_inf.mp x.2).2
    exact Subgroup.mem_normalizer_fintype hx
  have hsolR : Group.IsSolvable ↥f.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hfrange)
  have hker2 : IsPGroup 2 ↥f.ker := by
    intro k
    have hkP : Subgroup.inclusion inf_le_left (k : ↥(I ⊓ Subgroup.normalizer (U : Set G))) ∈ P :=
      hθker _ (MonoidHom.mem_ker.mp k.2)
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥I) ⟨_, hkP⟩
    have h1 : (Subgroup.inclusion inf_le_left
        (k : ↥(I ⊓ Subgroup.normalizer (U : Set G)))) ^ 2 ^ n = 1 := by
      simpa using congrArg Subtype.val hn
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val h1
  have hnil : Group.IsNilpotent ↥f.ker := hker2.isNilpotent
  have hsolN : Group.IsSolvable ↥(I ⊓ Subgroup.normalizer (U : Set G)) :=
    Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  exact Proof162.not_isSolvable_of_mem_scriptY4 hJ4
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (le_inf hJI hJU)))

end Res162Six

open Res162Six in
theorem step162UJHJSimple_of_star
    (h155 : Item155R) (h153 : Item153MainR) (h1444 : Item1444S14) (h146 : Item146S14)
    (hbot : Item145BotS14) (h142 : Concl142S14) (hK : KS162J2TwoInner)
    (hS : Step162UJHJStar) : Step162UJHJSimple := by
  intro G _ _ A c L h hJ hO Y₁ Y₂ S₁ S₂ hmax _ h12 h21 hnt J hJ0 hJK hφ hnc hc₁ hc₂
  have h14 := h.toSec14Std
  have hD := h.toSec13Data
  have hLi : ∀ {Y : Subgroup G}, (Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∧
      L = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 L) → L ≤ Y ∧ Y = L ⊔ CFSG.Open.pCoreOf 2 Y := by
    intro Y hc
    have hLY : L ≤ Y := by
      have h2 := hc.2
      rw [hO, sup_bot_eq] at h2
      exact h2.le.trans inf_le_left
    refine ⟨hLY, ?_⟩
    have h1 := hc.1
    rwa [inf_eq_right.mpr hLY] at h1
  obtain ⟨hL₁, hY₁L⟩ := hLi hc₁
  obtain ⟨hL₂, hY₂L⟩ := hLi hc₂
  have hY₁ := hmax.1.mem₁
  have hY₂ := hmax.1.mem₂
  have hL4 : L ∈ scriptY4 A (lB A) :=
    Res162Six.mem_scriptY4_of_j2_cover h hJ hY₁.prop.1 hL₁ hY₁L.le
  have hL1 : L ≠ ⊥ := fun h0 => by
    have h3 := three_dvd_card_of_j2 hJ
    rw [h0, Subgroup.card_bot] at h3
    omega
  have hne : Y₁ ≠ Y₂ := fun h0 =>
    hmax.1.not_conj ⟨1, one_mem _, by rw [Late.map_conj_one, h0]⟩
  have hDbot := pCoreOf_inf_eq_bot h (h155 G A c L h) (h153 G A c L h) (h1444 G A c L h14)
    (h146 G A c L h14) (hbot G A c L h14) (h142 G A c L h14) hJ hL4 hY₁ hY₂ hL₁ hL₂ hc₁.1 hne
  have hYY := inf_eq_of_pCoreOf_inf hL₁ hL₂ hY₁L.le hY₂L.le hDbot
  have hUL : S₁ ⊓ S₂ ≤ Subgroup.normalizer (L : Set G) := by
    rw [← hYY]
    exact (inf_le_inf hmax.1.s₁.prop.1.2 hmax.1.s₂.prop.1.2).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hUC := inf_centralizer_eq_bot h (h155 G A c L h) (h153 G A c L h) hL4 hL1 hmax hL₁ hL₂
  have hUc : S₁ ⊓ S₂ ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_inf_centralizer
      (Late.le_normalizer_inf hmax.1.s₁.prop.1.1.1.2.2 hmax.1.s₂.prop.1.1.1.2.2 hD.mem_A)
      (Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hy))
      hUL hUC
  have hstar := mem_scriptQPiStar_of_faithful hK h hJ hO hmax hL₁ hL₂ hUL hUC hUc
  exact hS G A c L h hJ hO Y₁ Y₂ S₁ S₂ hmax h12 h21 hnt J hJ0 hJK hφ hnc hL₁ hL₂ hY₁L hY₂L hYY
    hstar

open Res162Six in
theorem step162UJHJStar_of_kfacts
    (h1523 : Item1523R) (hN : KS162J2NormSolv) :
    Step162UJHJStar := by
  intro G _ _ A c L h hJ hO Y₁ Y₂ S₁ S₂ hmax h12 h21 hnt J hJ0 hJK hφ hnc hL₁ hL₂ hY₁L hY₂L
    hYY hU
  exfalso
  obtain ⟨I, hJI, hI⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hJ0
  have hc := h1523 G A c L h hJ I hI
  have hLI : L ≤ I := by
    have h2 := hc.2
    rw [hO, sup_bot_eq] at h2
    exact h2.le.trans inf_le_left
  have hIL : I ≤ L ⊔ CFSG.Open.pCoreOf 2 I := by
    have h1 := hc.1
    rw [inf_eq_right.mpr hLI] at h1
    exact h1.le
  exact false_of_le_normalizer_j2 hN h hJ hO hU hLI hIL hJ0.1 hJI (hJK.trans (delta_le _))

theorem step162UJHJSimple_of_kfacts
    (h155 : Item155R) (h153 : Item153MainR)
    (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14) (h142 : Concl142S14)
    (h1523 : Item1523R) (hK : KS162J2TwoInner) (hN : KS162J2NormSolv) : Step162UJHJSimple :=
  step162UJHJSimple_of_star h155 h153 h1444 h146 hbot h142 hK (step162UJHJStar_of_kfacts h1523 hN)

end CFSG.RankThree.PartTwo.Sec16
