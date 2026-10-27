module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec16.Item167ProofCrit
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.RankThree.Classical.EvenSurvivingScalarRank
import CFSG.RankThree.GF2n.Tim78Normal
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.RankThree.PGroups.SolvableTrivialComplementCore
import CFSG.RankThree.PartTwo.Sec16.Item167ProofGL2
public import CFSG.RankThree.PartTwo.Sec14.Item146General
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oPrimeResidualOf_three_eq_bot_of_not_dvd {Y : Subgroup G}
    (hY : ¬ 3 ∣ Nat.card Y) : oPrimeResidualOf 3 Y = ⊥ := by
  rw [oPrimeResidualOf_eq_closure, eq_bot_iff, Subgroup.closure_le]
  rintro x ⟨hx, k, hk⟩
  have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card Y := by
    rw [← Subgroup.orderOf_mk (ha := hx)]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ k) (Nat.card Y) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY)
  have h3 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h3)

section One

variable {A : Subgroup G} {LB : Subgroup G → Subgroup G}

omit [Finite G] in
theorem deltaZero_eq_deltaZero_delta (Z : Subgroup G) :
    deltaZero A LB Z = deltaZero A LB (delta A LB Z) :=
  le_antisymm (sSup_le fun _ hQ => le_deltaZero hQ.1 (le_delta hQ.1.1 hQ.2))
    (deltaZero_mono (delta_le Z))

theorem exists_overgroup_of_mem_scriptY1 (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hchar : CFSG.Assembly.IsCharTwoType G) {Y : Subgroup G}
    (hY : Y ∈ scriptY1 A LB) :
    ∃ Z : Subgroup G, Y ≤ Z ∧ Z ∈ scriptY A ∧ generalizedFitting ↥Z = CFSG.pCore 2 ↥Z ∧
      delta A LB Z ∈ scriptY1 A LB := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hY2, hYΔ⟩, hY3⟩ := hY
  set P := CFSG.Open.pCoreOf 2 Y with hP
  set N := Subgroup.normalizer (P : Set G) with hN
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hN2 : N ∈ scriptY2 A := normalizer_pCoreOf_mem_scriptY2 hsimp hnab hY2
  have hYN : Y ≤ N := Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hloc : IsPLocal 2 N := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hP2 hY2.2
  have hcharN : IsCharacteristicP 2 ↥N :=
    CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal hchar hloc
  set T := CFSG.Open.pCoreOf 2 N with hT
  have hTN : T ≤ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N
  have hNT : N ≤ Subgroup.normalizer (T : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  set Z := Y ⊔ T with hZ
  have hZN : Z ≤ N := sup_le hYN hTN
  have hAN : A ≤ N := hY2.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_sup hY2.1.2 (hAN.trans hNT)
  have hZtop : Z ≠ ⊤ := fun h => hN2.1.1 (top_le_iff.mp (h ▸ hZN))
  have hcharZ : IsCharacteristicP 2 ↥Z := by
    have hle : CFSG.pCore 2 ↥N ≤ Z.subgroupOf N := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (le_sup_right (a := Y)
        ⟨x, by assumption, rfl⟩)
    exact isCharacteristicP_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hZN)
      (isCharacteristicP_of_pCore_le (Z.subgroupOf N) hcharN hle)
  have hFZ : generalizedFitting ↥Z = CFSG.pCore 2 ↥Z :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥Z 2).mp hcharZ
  have hZ3 : ¬ 3 ∣ Nat.card Z := by
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp
        (h3.trans (card_sup_dvd_card_mul (hYN.trans hNT))) with h | h
    · exact not_three_dvd_of_oPrimeResidualOf_eq_bot hY3 h
    · obtain ⟨k, hk⟩ := hT2.exists_card_eq
      rw [hk] at h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h)
      omega
  refine ⟨Z, le_sup_left, ⟨hZtop, hAZ⟩, hFZ, ⟨⟨⟨?_, le_normalizer_delta Z⟩, ?_⟩,
    (delta_delta Z).symm⟩, ?_⟩
  · exact fun h => hZtop (top_le_iff.mp (h ▸ delta_le Z))
  ·
    have hYD : Y ≤ delta A LB Z := hYΔ.le.trans (delta_mono le_sup_left)
    have hPO : P ≤ CFSG.Open.pCoreOf 2 (delta A LB Z) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYD) ((delta_le Z).trans hZN) hP2
    intro h0
    rw [h0] at hPO
    exact hY2.2 (le_bot_iff.mp hPO)
  · exact oPrimeResidualOf_three_eq_bot_of_not_dvd fun h3 =>
      hZ3 (h3.trans (Subgroup.card_dvd_of_le (delta_le Z)))

theorem rank3II_16_7_1 (hsimp : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hchar : CFSG.Assembly.IsCharTwoType G) (h149 : Item149 A LB) {Y : Subgroup G}
    (hY : Y ∈ scriptY1Star A LB) :
    generalizedFitting ↥(deltaZero A LB Y) = CFSG.pCore 2 ↥(deltaZero A LB Y) := by
  obtain ⟨Z, hYZ, hZ, hFZ, hD⟩ := exists_overgroup_of_mem_scriptY1 hsimp hnab hchar hY.prop
  have hYD : Y ≤ delta A LB Z := hY.prop.1.2.le.trans (delta_mono hYZ)
  have hDY : delta A LB Z = Y := le_antisymm (hY.2 hD hYD) hYD
  have h := ((h149 Z hZ).2.2.2 hFZ).2
  rwa [deltaZero_eq_deltaZero_delta Z, hDY] at h

end One

theorem commute_of_odd_of_commute_pCoreOf {Y : Subgroup G} {y : G}
    (hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y)
    (hyY : y ∈ Subgroup.normalizer (Y : Set G)) (hodd : Odd (orderOf y))
    (hyQ : ∀ q ∈ CFSG.Open.pCoreOf 2 Y, y * q = q * y) : ∀ g ∈ Y, y * g = g * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 Y with hQ
  have hQY : Q ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hYQ : Y ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hchar : IsCharacteristicP 2 ↥Y :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥Y 2).mpr hF
  have hCQ : ∀ k ∈ Y, (∀ q ∈ Q, k * q = q * k) → k ∈ Q := by
    intro k hk hkq
    have hmem : (⟨k, hk⟩ : ↥Y) ∈ CFSG.pCore 2 ↥Y := by
      refine hchar (Subgroup.mem_centralizer_iff.mpr fun q hq => ?_)
      have hq' : (q : G) ∈ Q := by
        rw [hQ, CFSG.Open.pCoreOf]
        exact ⟨q, hq, rfl⟩
      exact Subtype.ext (hkq q hq').symm
    rw [hQ, CFSG.Open.pCoreOf]
    exact ⟨_, hmem, rfl⟩
  have hcomm : ∀ g ∈ Y, g * y * g⁻¹ * y⁻¹ ∈ Q := by
    intro g hg
    have hk : y * g⁻¹ * y⁻¹ * g ∈ Y := by
      have h1 : y * g⁻¹ * y⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hyY _).mp (inv_mem hg)
      exact mul_mem h1 hg
    have hkQ : y * g⁻¹ * y⁻¹ * g ∈ Q := by
      refine hCQ _ hk fun q hq => ?_
      have hq' : g * q * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hYQ hg) q).mp hq
      have hyq' := hyQ _ hq'
      have hc' : y⁻¹ * (g * q * g⁻¹) = (g * q * g⁻¹) * y⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hyq', mul_inv_cancel_right]
      calc y * g⁻¹ * y⁻¹ * g * q = y * g⁻¹ * (y⁻¹ * (g * q * g⁻¹)) * g := by group
        _ = y * g⁻¹ * ((g * q * g⁻¹) * y⁻¹) * g := by rw [hc']
        _ = y * q * g⁻¹ * y⁻¹ * g := by group
        _ = q * y * g⁻¹ * y⁻¹ * g := by rw [hyQ q hq]
        _ = q * (y * g⁻¹ * y⁻¹ * g) := by group
    have := (Subgroup.mem_normalizer_iff.mp (hYQ hg) _).mp hkQ
    have heq : g * (y * g⁻¹ * y⁻¹ * g) * g⁻¹ = g * y * g⁻¹ * y⁻¹ := by group
    rwa [heq] at this
  intro g hg
  set q := g * y * g⁻¹ * y⁻¹ with hqdef
  have hqQ : q ∈ Q := hcomm g hg
  have hqy : Commute q y := (hyQ q hqQ).symm
  have hgy : g * y * g⁻¹ = q * y := by rw [hqdef]; group
  set n := orderOf y with hn
  have hpow : (g * y * g⁻¹) ^ n = 1 := by
    rw [show g * y * g⁻¹ = (MulAut.conj g) y from rfl, ← map_pow, pow_orderOf_eq_one, map_one]
  rw [hgy, hqy.mul_pow, pow_orderOf_eq_one, mul_one] at hpow
  have hq1 : q = 1 := by
    obtain ⟨k, hk⟩ := hQ2 ⟨q, hqQ⟩
    have hk' : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf q ∣ Nat.gcd (2 ^ k) n :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hpow)
    have hcop : Nat.Coprime (2 ^ k) n :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  have : g * y * g⁻¹ * y⁻¹ = 1 := hq1
  calc y * g = (g * y * g⁻¹ * y⁻¹)⁻¹ * (g * y) := by group
    _ = g * y := by rw [this, inv_one, one_mul]

section Steps

variable (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G) (L : Subgroup G)

@[expose] noncomputable def Hyp1673 (Y : Subgroup G) : Prop :=
  Y ∈ scriptY3Star A LB ∧ Group.IsSolvable ↥Y ∧ deltaZero A LB Y ≠ ⊥ ∧
    (scriptY0 A LB = ∅ →
      ∃ n : ℕ, 2 < n ∧ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n ∧
        Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L))

@[expose] noncomputable def Two167 (Y : Subgroup G) : Prop :=
  generalizedFitting (↥(deltaZero A LB Y) ⧸ CFSG.pCore 2 ↥(deltaZero A LB Y)) =
    oResidual 2 (↥(deltaZero A LB Y) ⧸ CFSG.pCore 2 ↥(deltaZero A LB Y))

@[expose] noncomputable def Step167TwoNonsolv : Prop :=
  ∀ Y ∈ scriptY1Star A LB, ¬ Group.IsSolvable ↥(deltaZero A LB Y) → Two167 A LB Y

@[expose] noncomputable def Step167TwoSolv : Prop :=
  ∀ Y ∈ scriptY1Star A LB, Group.IsSolvable ↥(deltaZero A LB Y) → Two167 A LB Y

@[expose] noncomputable def Step167Nil : Prop :=
  ∀ Y ∈ scriptY1Star A LB, Hyp1673 A LB c L Y → IsTwoNilpotent (↥Y ⧸ CFSG.pCore 2 ↥Y)

@[expose] noncomputable def Step167V : Prop :=
  ∀ Y ∈ scriptY1Star A LB, Hyp1673 A LB c L Y →
    generalizedFitting ↥Y ≠ CFSG.pCore 2 ↥Y → ∀ Y₀ ∈ scriptY0Star A LB,
      CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 Y : Set G) ≤ Y

@[expose] noncomputable def Step167O2 : Prop :=
  ∀ Y ∈ scriptY1Star A LB, Hyp1673 A LB c L Y →
    generalizedFitting ↥Y ≠ CFSG.pCore 2 ↥Y → ∀ Y₀ ∈ scriptY0Star A LB,
      pPrimeCoreOf 2 Y ≠ ⊥ → A ≤ Subgroup.centralizer (pPrimeCoreOf 2 Y : Set G) →
        Y₀ ≤ Subgroup.centralizer (pPrimeCoreOf 2 Y : Set G) →
          CFSG.Open.pCoreOf 2 (A ⊔ Y₀ ⊔ Y) ≠ ⊥

@[expose] noncomputable def Step167Empty : Prop :=
  ∀ Y ∈ scriptY1Star A LB, Hyp1673 A LB c L Y → scriptY0 A LB = ∅ →
    generalizedFitting ↥Y ≠ CFSG.pCore 2 ↥Y →
      generalizedFitting ↥Y = CFSG.pCore 2 ↥Y ⊔ Subgroup.center ↥Y

end Steps

section Three

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem pPrimeCoreOf_two_ne_bot {Y : Subgroup G} (hsol : Group.IsSolvable ↥Y)
    (hF : generalizedFitting ↥Y ≠ CFSG.pCore 2 ↥Y) : pPrimeCoreOf 2 Y ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h0
  have h1 : CFSG.pPrimeCore 2 ↥Y = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp h0
  exact hF ((isCharacteristicP_iff_generalizedFitting_eq_pCore ↥Y 2).mp
    (CFSG.RankThree.PGroups.solvable_trivial_complement_core Nat.prime_two h1))

theorem pPrimeCoreOf_inf_deltaZero_eq_bot {LB : Subgroup G → Subgroup G} {Y : Subgroup G}
    (hFX : generalizedFitting ↥(deltaZero A LB Y) = CFSG.pCore 2 ↥(deltaZero A LB Y)) :
    pPrimeCoreOf 2 Y ⊓ deltaZero A LB Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := deltaZero A LB Y with hX
  have hXY : X ≤ Y := deltaZero_le Y
  have hcharX : IsCharacteristicP 2 ↥X :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥X 2).mpr hFX
  have hOX : pPrimeCoreOf 2 X = ⊥ := by
    rw [pPrimeCoreOf, pPrimeCore_eq_bot_of_isCharacteristicP ↥X 2 hcharX, Subgroup.map_bot]
  rw [eq_bot_iff, ← hOX]
  refine le_pPrimeCoreOf inf_le_right ?_ ?_
  · exact Late.le_normalizer_inf (hXY.trans (le_normalizer_pPrimeCoreOf 2 Y))
      Subgroup.le_normalizer
  · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 2 Y)

theorem rank3II_16_7_3_of_nonempty (h : Sec15R G A c L) (h149 : Item149 A (lB A))
    (h163 : Item163 A (lB A) c L) (h146 : Item146 A (lB A)) (h153 : Item153Main A (lB A))
    (hM : Claim17M A (lB A)) (hV : Step167V A (lB A) c L) (hO2 : Step167O2 A (lB A) c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY1Star A (lB A)) (hH : Hyp1673 A (lB A) c L Y)
    (hne : (scriptY0 A (lB A)).Nonempty) :
    generalizedFitting ↥Y = CFSG.pCore 2 ↥Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hF
  obtain ⟨hY3s, hsol, -, -⟩ := id hH
  have hA : IsE27 A := h.toSec14Std.isE27
  have hA3 : IsPGroup 3 A := hA.isPGroup
  obtain ⟨⟨hY2, hYΔ⟩, hYo⟩ := hY.prop
  have hY3' : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_oPrimeResidualOf_eq_bot hYo
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY2.1.2
  have hYinv : Y ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three Y).mpr hY3', hAY⟩
  have hYQ : Y ∈ scriptQ A (lB A) := by
    have := delta_mem_scriptQ hA h146 hYinv
    rwa [← hYΔ] at this
  set X := deltaZero A (lB A) Y with hXdef
  have hYAX : ⁅Y, A⁆ ≤ X := by
    have hcomm : ⁅Y, A⁆ ≤ Y := Subgroup.le_normalizer_iff_commutator_le_left.mp hAY
    have hAcomm : A ≤ Subgroup.normalizer ((⁅Y, A⁆ : Subgroup G) : Set G) := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.normalizer_commutator_ge_left A Y
    exact le_deltaZero ⟨mem_scriptQ_of_le hYQ hcomm hAcomm,
      (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three
        A Y hA3 hY3' hAY).symm⟩ hcomm
  set Z := pPrimeCoreOf 2 Y with hZdef
  have hZ1 : Z ≠ ⊥ := pPrimeCoreOf_two_ne_bot hsol hF
  have hZY : Z ≤ Y := pPrimeCoreOf_le 2 Y
  have hYZ : Y ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_pPrimeCoreOf 2 Y
  have hZodd : Nat.Coprime 2 (Nat.card Z) := coprime_card_pPrimeCoreOf 2 Y
  have hFX : generalizedFitting ↥X = CFSG.pCore 2 ↥X :=
    rank3II_16_7_1 h.isSimpleGroup h.nonabelian h.charTwoType h149 hY
  have hZX : Z ⊓ X = ⊥ := pPrimeCoreOf_inf_deltaZero_eq_bot hFX
  have hZA : A ≤ Subgroup.centralizer (Z : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have haZ : a ∈ Subgroup.normalizer (Z : Set G) :=
      (hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 2 Y)) ha
    have hk1 : z * a * z⁻¹ * a⁻¹ ∈ Z := by
      have : a * z⁻¹ * a⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp haZ _).mp (inv_mem hz)
      have h2 := mul_mem hz this
      rwa [show z * (a * z⁻¹ * a⁻¹) = z * a * z⁻¹ * a⁻¹ by group] at h2
    have hk2 : z * a * z⁻¹ * a⁻¹ ∈ X := by
      apply hYAX
      have := Subgroup.commutator_mem_commutator (hZY hz) ha
      rwa [commutatorElement_def] at this
    have hk : z * a * z⁻¹ * a⁻¹ = 1 := by
      have : z * a * z⁻¹ * a⁻¹ ∈ Z ⊓ X := ⟨hk1, hk2⟩
      rwa [hZX, Subgroup.mem_bot] at this
    calc z * a = (z * a * z⁻¹ * a⁻¹) * (a * z) := by group
      _ = a * z := by rw [hk, one_mul]
  obtain ⟨Y₀, -, hY₀⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hne.some_mem
  obtain ⟨hW, hS, hstar, -, -⟩ := h163 Y₀ hY₀
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  obtain ⟨⟨hY₀Y, hY₀o, hY₀Δ, -⟩, hY₀2⟩ := hY₀.prop
  set Q := CFSG.Open.pCoreOf 2 Y₀ with hQdef
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀
  have hZM : Z ≤ M := (Subgroup.le_centralizer_iff.mp hZA).trans
    ((Subgroup.centralizer_le_normalizer (A : Set G)).trans hW)
  set B := CFSG.Open.pCoreOf 2 Y with hBdef
  have hB2 : IsPGroup 2 B := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hBY : B ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hBM : B ≤ M := by
    have hAB : A ≤ Subgroup.normalizer (B : Set G) :=
      hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
    have hBQ : B ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
      ⟨⟨mem_scriptQ_of_le hYQ hBY hAB, le_top⟩,
        (isPiSubgroup_piOf_iff Nat.prime_two B).mpr hB2⟩
    obtain ⟨S, hBS, hSmax⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2)))
      hBQ
    exact hBS.trans (hS S hSmax)
  have hVY := hV Y hY hH hF Y₀ hY₀
  have hZB : ∀ z ∈ Z, ∀ b ∈ B, z * b = b * z := by
    intro z hz b hb
    have hk1 : z * b * z⁻¹ * b⁻¹ ∈ B := by
      have : z * b * z⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp
        ((hZY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)) hz) b).mp hb
      exact mul_mem this (inv_mem hb)
    have hk2 : z * b * z⁻¹ * b⁻¹ ∈ Z := by
      have : b * z⁻¹ * b⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hYZ (hBY hb)) _).mp
        (inv_mem hz)
      have h2 := mul_mem hz this
      rwa [show z * (b * z⁻¹ * b⁻¹) = z * b * z⁻¹ * b⁻¹ by group] at h2
    have hBZ : B ⊓ Z = ⊥ := by
      obtain ⟨k, hk⟩ := hB2.exists_card_eq
      exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard
          (by rw [hk]; exact Nat.Coprime.pow_left k hZodd))
    have hk : z * b * z⁻¹ * b⁻¹ = 1 := by
      have : z * b * z⁻¹ * b⁻¹ ∈ B ⊓ Z := ⟨hk1, hk2⟩
      rwa [hBZ, Subgroup.mem_bot] at this
    calc z * b = (z * b * z⁻¹ * b⁻¹) * (b * z) := by group
      _ = b * z := by rw [hk, one_mul]
  have hFY₀ : generalizedFitting ↥Y₀ = CFSG.pCore 2 ↥Y₀ := (h153 Y₀ hY₀).2.2
  have hY₀Z : Y₀ ≤ Subgroup.centralizer (Z : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hodd : Odd (orderOf y) := by
      have h1 : orderOf y ∣ Nat.card Z := by
        rw [← Subgroup.orderOf_mk (ha := hy)]
        exact orderOf_dvd_natCard _
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 =>
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hZodd (h2.trans h1))
    have hyQ : y ∈ Subgroup.normalizer (Q : Set G) := hMQ (hZM hy)
    have hfix : ∀ q ∈ Q, (∀ b ∈ B, q * b = b * q) → y * q = q * y := by
      intro q hq hqB
      have hqV : q ∈ Q ⊓ Subgroup.centralizer (B : Set G) :=
        ⟨hq, Subgroup.mem_centralizer_iff.mpr fun b hb => (hqB b hb).symm⟩
      have hqY : q ∈ Y := hVY hqV
      have hyV : y * q * y⁻¹ ∈ Q ⊓ Subgroup.centralizer (B : Set G) := by
        refine ⟨(Subgroup.mem_normalizer_iff.mp hyQ q).mp hq,
          Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
        have hby : Commute b y := (hZB y hy b hb).symm
        have hbq : Commute b q := (hqB b hb).symm
        exact ((hby.mul_right hbq).mul_right hby.inv_right).eq
      have hk1 : y * q * y⁻¹ * q⁻¹ ∈ Q ⊓ Subgroup.centralizer (B : Set G) :=
        mul_mem hyV (inv_mem hqV)
      have hk2 : y * q * y⁻¹ * q⁻¹ ∈ Z := by
        have : q * y⁻¹ * q⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hYZ hqY) _).mp (inv_mem hy)
        have h2 := mul_mem hy this
        rwa [show y * (q * y⁻¹ * q⁻¹) = y * q * y⁻¹ * q⁻¹ by group] at h2
      have hQZ : Q ⊓ Z = ⊥ := by
        obtain ⟨k, hk⟩ := hQ2.exists_card_eq
        exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard
          (by rw [hk]; exact Nat.Coprime.pow_left k hZodd))
      have hk : y * q * y⁻¹ * q⁻¹ = 1 := by
        have : y * q * y⁻¹ * q⁻¹ ∈ Q ⊓ Z := ⟨hk1.1, hk2⟩
        rwa [hQZ, Subgroup.mem_bot] at this
      calc y * q = (y * q * y⁻¹ * q⁻¹) * (q * y) := by group
        _ = q * y := by rw [hk, one_mul]
    have hyQc := CFSG.RankThree.GF2n.Tim78.commute_of_thompson_A_times_B hQ2 hB2 hyQ
      (hBM.trans hMQ) hodd (fun b hb => hZB y hy b hb) hfix
    exact (commute_of_odd_of_commute_pCoreOf hFY₀ (hZM hy) hodd hyQc g hg)
  have hK := hO2 Y hY hH hF Y₀ hY₀ hZ1 hZA hY₀Z
  set K := A ⊔ Y₀ ⊔ Y with hKdef
  set P := CFSG.Open.pCoreOf 2 K with hPdef
  have hloc : IsPLocal 2 (Subgroup.normalizer (P : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hK
  have hKP : K ≤ Subgroup.normalizer (P : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hPM : Subgroup.normalizer (P : Set G) ≤ M := by
    obtain ⟨M', hPM', hM'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
    have hmem : M' ∈ CFSG.maximalTwoLocalsContaining ((Y₀ ⊔ A : Subgroup G) : Set G) :=
      ⟨hM', fun x hx => hPM' (hKP ((sup_le le_sup_right le_sup_left : Y₀ ⊔ A ≤ A ⊔ Y₀).trans
        le_sup_left hx))⟩
    rw [hM Y₀ hY₀ hstar, Set.mem_singleton_iff] at hmem
    calc Subgroup.normalizer (P : Set G) ≤ M' := hPM'
      _ = M := hmem
  have hYM : Y ≤ M := (le_sup_right.trans hKP).trans hPM
  have hY₀1 : Y₀ ≠ ⊥ := fun h0 => hY₀2.2 (by
    rw [eq_bot_iff, ← h0]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀)
  have hMtop : M ≠ ⊤ := by
    have : IsSimpleGroup G := h.isSimpleGroup
    intro htop
    rcases (Subgroup.normalizer_eq_top_iff.mp htop).eq_bot_or_eq_top with h0 | h1
    · exact hY₀1 h0
    · exact hY₀Y.1 h1
  have hmem3 : Y ⊔ Y₀ ∈ scriptY3 A (lB A) := by
    refine ⟨⟨⟨fun htop => hMtop (top_le_iff.mp (htop ▸ sup_le hYM Subgroup.le_normalizer)),
      le_normalizer_sup hAY hY₀Y.2⟩, fun h0 => hY₀2.2 ?_⟩, ?_⟩
    · have hle : Q ≤ CFSG.Open.pCoreOf 2 (Y ⊔ Y₀) :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀).trans le_sup_right)
          (sup_le (hYM.trans hMQ) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)) hQ2
      rw [h0] at hle
      exact le_bot_iff.mp hle
    · refine le_antisymm (sup_le ?_ ?_) (delta_le _)
      · exact hYΔ.le.trans (delta_mono le_sup_left)
      · exact hY₀Δ.le.trans (delta_mono le_sup_right)
  have hle := hY3s.2 hmem3 le_sup_left
  have hY₀le : Y₀ ≤ Y := le_sup_right.trans hle
  apply hY3'
  have hY₀3 : 3 ∣ Nat.card Y₀ := by
    by_contra h3
    exact hY₀1 (hY₀o.trans (oPrimeResidualOf_three_eq_bot_of_not_dvd h3))
  exact hY₀3.trans (Subgroup.card_dvd_of_le hY₀le)

end Three

section Crit

variable {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem pRank_quot_pCore_two_le (hG : TheoremFourHyp G) {Z T : Subgroup G} (hT1 : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hZT : Z ≤ Subgroup.normalizer (T : Set G)) {r : ℕ} (hr : r.Prime)
    (hr3 : 3 < r) : CFSG.Open.pRank r (⊤ : Subgroup (↥Z ⧸ CFSG.pCore 2 ↥Z)) ≤ 2 := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥Z) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Z)).exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)
    omega
  rw [CFSG.SectionRank.pRank_quotient_eq _ hN]
  have h1 : CFSG.Open.pRank r (⊤ : Subgroup ↥Z) = CFSG.Open.pRank r Z := by
    rw [← Crit167.pRank_map_eq_of_injective hr Z.subtype Z.subtype_injective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h1]
  have h2 : CFSG.Open.pRank r (Subgroup.normalizer (T : Set G)) ≤
      CFSG.Assembly.RankThreeEven.localRank r G :=
    CFSG.RankThree.Classical.pRank_le_localRank hr.one_lt
      (X := Subgroup.normalizer (T : Set G)) ⟨T, hT1, hT2, rfl⟩
  have h3 := hG.localRank_lt r hr hr3
  have h4 := CFSG.SectionRank.pRank_mono hr.one_lt hZT
  omega

theorem step167Nil_of (hG : TheoremFourHyp G) (c : G)
    (L : Subgroup G) : Step167Nil A LB c L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Y hY hH
  obtain ⟨-, hsol, -, -⟩ := hH
  obtain ⟨⟨hY2, -⟩, hYo⟩ := hY.prop
  have hY3 : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_oPrimeResidualOf_eq_bot hYo
  have hYP : Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have h3 : ¬ 3 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := fun h =>
    hY3 (h.trans (Subgroup.card_quotient_dvd_card _))
  have := Crit167.hasNormalPComplement_two_of_rank (H := ↥Y ⧸ CFSG.pCore 2 ↥Y)
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot h3 fun r hr hr3 =>
      pRank_quot_pCore_two_le hG hY2.2 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) hYP hr hr3
  obtain ⟨N, hN, hNodd, hq⟩ := this
  exact ⟨N, hN, Nat.coprime_two_left.mp hNodd, hq⟩

omit [Finite G] in
theorem le_normalizer_deltaZero (Y : Subgroup G) :
    A ≤ Subgroup.normalizer (deltaZero A LB Y : Set G) :=
  Sec14.le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2

omit [Finite G] in
theorem deltaZero_eq_commutator (Y : Subgroup G) :
    deltaZero A LB Y = ⁅deltaZero A LB Y, A⁆ := by
  refine le_antisymm (sSup_le fun Q hQ => ?_)
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_deltaZero Y))
  rw [hQ.1.2]
  exact Subgroup.commutator_mono (le_deltaZero hQ.1 hQ.2) le_rfl

theorem step167TwoSolv_of (hG : TheoremFourHyp G)
    (hA : IsPGroup 3 A) : Step167TwoSolv A LB := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Y hY hsolX
  obtain ⟨⟨hY2, -⟩, hYo⟩ := hY.prop
  set X := deltaZero A LB Y with hXdef
  have hXY : X ≤ Y := deltaZero_le Y
  have hY3 : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_oPrimeResidualOf_eq_bot hYo
  have hYP : Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have h2 : CFSG.pCore 2 (↥X ⧸ CFSG.pCore 2 ↥X) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have h3 : ¬ 3 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := fun h =>
    hY3 ((h.trans (Subgroup.card_quotient_dvd_card _)).trans (Subgroup.card_dvd_of_le hXY))
  have hrank := fun r hr hr3 => pRank_quot_pCore_two_le hG hY2.2
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) (hXY.trans hYP) (r := r) hr hr3
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := le_normalizer_deltaZero Y
  set β : ↥A →* MulAut (↥X ⧸ CFSG.pCore 2 ↥X) :=
    (Crit167.quotPCoreAut ↥X).comp (X.normalizerMonoidHom.comp (Subgroup.inclusion hAX)) with hβ
  set π : ↥X →* ↥X ⧸ CFSG.pCore 2 ↥X := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  have hgen : Subgroup.closure
      {z | ∃ x : ↥X ⧸ CFSG.pCore 2 ↥X, ∃ a : ↥A, z = x * (β a x)⁻¹} = ⊤ := by
    set S := {z | ∃ x : ↥X ⧸ CFSG.pCore 2 ↥X, ∃ a : ↥A, z = x * (β a x)⁻¹} with hS
    set K := ((Subgroup.closure S).comap π).map X.subtype with hK
    have hcomm : ⁅X, A⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro x hx a ha
      refine ⟨⟨⁅x, a⁆, (Subgroup.le_normalizer_iff_commutator_le_left.mp hAX)
        (Subgroup.commutator_mem_commutator hx ha)⟩, ?_, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨π ⟨x, hx⟩, ⟨a, ha⟩, ?_⟩
      simp only [hβ, hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        Crit167.quotPCoreAut_apply_mk]
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe,
        Subgroup.coe_inclusion, commutatorElement_def]
      group
    have hXK : X ≤ K := (deltaZero_eq_commutator Y).le.trans hcomm
    rw [eq_top_iff]
    intro q _
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) q
    obtain ⟨⟨g', hg'⟩, hg'S, hg'g⟩ := hXK hg
    have : (⟨g, hg⟩ : ↥X) = ⟨g', hg'⟩ := Subtype.ext hg'g.symm
    rw [this]
    exact hg'S
  have := hsolX
  have hle := Crit167.oResidual_le_fittingSubgroup Crit167.ks167GL2 h2 h3 hrank hA β hgen
  unfold Two167
  rw [CFSG.RankThree.PGroups.generalizedFitting_eq_fittingSubgroup_of_isSolvable]
  refine le_antisymm (fun f hf => ?_) hle
  apply Subgroup.subset_closure
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos f).ne'
  have hfm : (f ^ m) ^ 2 ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have hfm1 := Crit167.eq_one_of_mem_fittingSubgroup h2
    (Subgroup.pow_mem _ hf m) hfm
  have hdvd : orderOf f ∣ m := orderOf_dvd_of_pow_eq_one hfm1
  exact Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_two_right.mpr hm)

end Crit

section Item

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem rank3II_16_7_of (h : Sec15R G A c L)
    (h149 : Item149 A (lB A)) (h163 : Item163 A (lB A) c L)
    (h146 : Item146 A (lB A)) (h153 : Item153Main A (lB A)) (hM : Claim17M A (lB A))
    (hns : Step167TwoNonsolv A (lB A)) (hV : Step167V A (lB A) c L)
    (hO2 : Step167O2 A (lB A) c L) (hemp : Step167Empty A (lB A) c L) :
    Item167 A (lB A) c L := by
  have hs : Step167TwoSolv A (lB A) :=
    step167TwoSolv_of h.toTheoremFourHyp h.toSec14Std.isE27.isPGroup
  have hnil : Step167Nil A (lB A) c L := step167Nil_of h.toTheoremFourHyp c L
  intro Y hY
  refine ⟨rank3II_16_7_1 h.isSimpleGroup h.nonabelian h.charTwoType h149 hY, ?_, ?_⟩
  · by_cases hsol : Group.IsSolvable ↥(deltaZero A (lB A) Y)
    · exact hs Y hY hsol
    · exact hns Y hY hsol
  · intro hY3 hsolY hX hhyp
    have hH : Hyp1673 A (lB A) c L Y := ⟨hY3, hsolY, hX, hhyp⟩
    refine ⟨hnil Y hY hH, ?_⟩
    by_cases hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y
    · exact Or.inl hF
    · by_cases h0 : scriptY0 A (lB A) = ∅
      · exact Or.inr ⟨h0, hemp Y hY hH h0 hF⟩
      · exact absurd (rank3II_16_7_3_of_nonempty h h149 h163 h146 h153 hM hV hO2 hY hH
          (Set.nonempty_iff_ne_empty.mpr h0)) hF

end Item

@[expose] noncomputable def Item167R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item167 A (lB A) c L

@[expose] noncomputable def Item149S14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → Item149 A (lB A)

@[expose] noncomputable def Step167TwoNonsolvR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step167TwoNonsolv A (lB A)

@[expose] noncomputable def Step167VR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step167V A (lB A) c L

@[expose] noncomputable def Step167O2R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step167O2 A (lB A) c L

@[expose] noncomputable def Step167EmptyR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step167Empty A (lB A) c L

theorem item167R_of (h149 : Item149S14) (h146 : Sec14.Item146S14)
    (h153 : Sec15.Item153MainR) (h163 : Item163R) (hM : Claim17MR)
    (hns : Step167TwoNonsolvR) (hV : Step167VR) (hO2 : Step167O2R) (hemp : Step167EmptyR) :
    Item167R := fun G _ _ A c L h =>
  rank3II_16_7_of h (h149 G A c L h.toSec14Std) (h163 G A c L h)
    (h146 G A c L h.toSec14Std) (h153 G A c L h) (hM G A c L h) (hns G A c L h)
    (hV G A c L h) (hO2 G A c L h) (hemp G A c L h)

end CFSG.RankThree.PartTwo.Sec16
