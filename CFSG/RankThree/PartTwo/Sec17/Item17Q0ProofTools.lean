module

public import CFSG.RankThree.PartTwo.Sec14.Item1446
public import CFSG.RankThree.PartTwo.Sec15.Notation
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Q0

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutatorElement_mem_of_pow_three {Y V N : Subgroup G} {x y : G} (hVY : V ≤ Y)
    (hNY : N ≤ Y) (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (hVYN : ⁅V, Y⁆ ≤ N)
    (hV2 : IsPGroup 2 V) (hy : y ∈ Y) {k : ℕ} (hyk : y ^ 3 ^ k = 1) (hd : ⁅y, x⁆ ∈ V) :
    ⁅y, x⁆ ∈ N := by
  have : (N.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr hYN
  set π := QuotientGroup.mk' (N.subgroupOf Y) with hπ
  set dY : ↥Y := ⟨⁅y, x⁆, hVY hd⟩ with hdY
  set yY : ↥Y := ⟨y, hy⟩ with hyY
  have hker : ∀ z : ↥Y, π z = 1 ↔ (z : G) ∈ N := fun z => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcomm : Commute (π dY) (π yY) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, hker]
    exact hVYN (Subgroup.commutator_mem_commutator hd hy)
  have hconj : (dY⁻¹ * yY) ^ 3 ^ k = 1 := by
    apply Subtype.ext
    have e : (⁅y, x⁆)⁻¹ * y = x * y * x⁻¹ := by
      rw [commutatorElement_def]
      group
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, hdY, hyY]
    rw [e, conj_pow, hyk, mul_one, mul_inv_cancel]
  have hyY3 : yY ^ 3 ^ k = 1 := Subtype.ext (by simp [hyY, hyk])
  have h3 : π dY ^ 3 ^ k = 1 := by
    have h1 : ((π dY)⁻¹ * π yY) ^ 3 ^ k = 1 := by
      rw [← map_inv, ← map_mul, ← map_pow, hconj, map_one]
    rw [hcomm.inv_left.mul_pow, ← map_pow π yY, hyY3, map_one, mul_one, inv_pow,
      inv_eq_one] at h1
    exact h1
  obtain ⟨m, hm⟩ := hV2 ⟨⁅y, x⁆, hd⟩
  have h2 : π dY ^ 2 ^ m = 1 := by
    have : dY ^ 2 ^ m = 1 := Subtype.ext (by simpa [hdY] using congrArg Subtype.val hm)
    rw [← map_pow, this, map_one]
  exact (hker dY).mp (CFSG.RankThree.PartTwo.Sec16.Step163Alt.eq_one_of_two_three h2 h3)

omit [Finite G] in
theorem commutator_zpowers_le {Y V : Subgroup G} {x : G} (hVY : V ≤ Y)
    (hYV : Y ≤ Subgroup.normalizer (V : Set G)) (hV2 : IsPGroup 2 V)
    (hY3 : Y = oPrimeResidualOf 3 Y) (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hYx : ∀ y ∈ Y, ⁅y, x⁆ ∈ V) : ⁅V, Subgroup.zpowers x⁆ ≤ ⁅V, Y⁆ := by
  set N := ⁅V, Y⁆ with hN
  have hNV : N ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hYV
  have hNY : N ≤ Y := hNV.trans hVY
  have hYN : Y ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_commutator (A := Y) hYV Subgroup.le_normalizer
  have hxs : Subgroup.zpowers x ≤ commutatorInSubgroup Y V :=
    Subgroup.zpowers_le.mpr (mem_commutatorInSubgroup.mpr ⟨hxV, hYx⟩)
  have hYT : Y ≤ commutatorInSubgroup (Subgroup.zpowers x) N := by
    refine hY3.le.trans ?_
    rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
    rintro y ⟨hy, k, hyk⟩
    refine mem_commutatorInSubgroup.mpr ⟨hYN hy, fun q hq => ?_⟩
    have h := commutatorElement_mem_of_pow_three hVY hNY hYN le_rfl hV2 hy hyk
      ((mem_commutatorInSubgroup.mp (hxs hq)).2 y hy)
    rw [← commutatorElement_inv]
    exact N.inv_mem h
  rw [Subgroup.commutator_le]
  intro v hv q hq
  have h := (mem_commutatorInSubgroup.mp (hYT (hVY hv))).2 q hq
  rw [← commutatorElement_inv]
  exact N.inv_mem h

omit [Finite G] in
theorem commutatorElement_mem_of_eq_sup {Y V L : Subgroup G} {x : G} (hY : Y = L ⊔ V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) : ∀ y ∈ Y, ⁅y, x⁆ ∈ V := by
  have hxs : Subgroup.zpowers x ≤ Subgroup.normalizer (V : Set G) := Subgroup.zpowers_le.mpr hxV
  have hle : Y ≤ commutatorInSubgroup (Subgroup.zpowers x) V := by
    rw [hY]
    refine sup_le (fun l hl => mem_commutatorInSubgroup.mpr ⟨hLV hl, fun q hq => ?_⟩)
      (fun v hv => mem_commutatorInSubgroup.mpr ⟨Subgroup.le_normalizer hv, fun q hq => ?_⟩)
    ·
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
      have hc : Commute l x := Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
      rw [commutatorElement_eq_one_iff_commute.mpr (hc.zpow_right j).symm]
      exact V.one_mem
    ·
      rw [commutatorElement_def]
      exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hxs hq) v).mp hv) (V.inv_mem hv)
  intro y hy
  have h := (mem_commutatorInSubgroup.mp (hle hy)).2 x (Subgroup.mem_zpowers x)
  rw [← commutatorElement_inv]
  exact V.inv_mem h

variable {A : Subgroup G}

theorem pCoreOf_le_pPrimeCoreOf (Y : Subgroup G) :
    CFSG.Open.pCoreOf 2 Y ≤ pPrimeCoreOf 3 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pPrimeCoreOf (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y) ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

theorem isPiSubgroup_piCompl_pCoreOf (Y : Subgroup G) :
    IsPiSubgroup (piCompl 3) (CFSG.Open.pCoreOf 2 Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact isPiSubgroup_piCompl_of_le ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)))
    (pCoreOf_le_pPrimeCoreOf Y)

theorem pPrimeCoreOf_mem_invariantPiSubgroups {Y : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) :
    pPrimeCoreOf 3 Y ∈ invariantPiSubgroups ⊤ A (piCompl 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)),
    hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)⟩

theorem commutator_pCoreOf_mem_scriptQ_of_le (hA : IsE27 A) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {Y : Subgroup G}
    (hY : Y ∈ Sec15.scriptY4 A (lB A))
    (h147 : ⁅deltaZero A (lB A) Y, pPrimeCoreOf 3 Y⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 Y)) :
    ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ ∈ scriptQ A (lB A) := by
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.1.2
  have hK := pPrimeCoreOf_mem_invariantPiSubgroups hAY
  have hY0 : Y = deltaZero A (lB A) Y := rank3II_15_1_lB hA hbot hY
  have hle : ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 Y) :=
    calc ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ ≤ ⁅pPrimeCoreOf 3 Y, Y⁆ :=
          Subgroup.commutator_mono (pCoreOf_le_pPrimeCoreOf Y) le_rfl
      _ = ⁅Y, pPrimeCoreOf 3 Y⁆ := Subgroup.commutator_comm _ _
      _ = ⁅deltaZero A (lB A) Y, pPrimeCoreOf 3 Y⁆ :=
          congrArg (fun X => ⁅X, pPrimeCoreOf 3 Y⁆) hY0
      _ ≤ _ := h147
  have hAV : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  exact mem_scriptQ_of_le (delta_mem_scriptQ hA h146 hK) hle (le_normalizer_commutator hAV hAY)

theorem commutator_pCoreOf_mem_scriptQ (hA : IsE27 A) (h1444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {Y : Subgroup G}
    (hY : Y ∈ Sec15.scriptY4 A (lB A)) :
    ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ ∈ scriptQ A (lB A) := by
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.1.2
  have hK := pPrimeCoreOf_mem_invariantPiSubgroups hAY
  have hYN : Y ≤ Subgroup.normalizer (delta A (lB A) (pPrimeCoreOf 3 Y) : Set G) :=
    calc Y = delta A (lB A) Y := hY.2.2.1
      _ ≤ _ := delta_le_normalizer_delta (fun Z hZ => delta_mem_scriptQ hA h146 hZ) hK
          (le_normalizer_pPrimeCoreOf 3 Y)
  exact commutator_pCoreOf_mem_scriptQ_of_le hA h146 hbot hY
    (rank3II_14_7_reduction hA h1444 h146 hAY ((pPrimeCoreOf_le 3 Y).trans hYN))

theorem inf_centralizer_mem_scriptQ_of_concl142 (hA : IsE27 A) (h142 : Concl142 A (lB A))
    {c : G} (hc : Subgroup.zpowers c ∈ omegaA A) {X : Subgroup G}
    (hX3 : IsPiSubgroup (piCompl 3) X) (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    X ⊓ Subgroup.centralizer ({c} : Set G) ∈ scriptQ A (lB A) := by
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp hc).1
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hAXc : A ≤ Subgroup.normalizer
      ((X ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf hAX (hAc.trans Subgroup.le_normalizer)
  have hmem : X ⊓ Subgroup.centralizer ({c} : Set G) ∈
      invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piCompl 3) :=
    ⟨inf_le_right.trans (centralizer_singleton_le_normalizer_zpowers c),
      isPiSubgroup_piCompl_of_le hX3 inf_le_left, hAXc⟩
  obtain ⟨Q, hQ, hle⟩ := exists_le_mem_maxInvariantPiSubgroups hmem
  exact mem_scriptQ_of_le (h142 c hc Q hQ).1 hle hAXc

theorem pCoreOf_mem_scriptQ_of_le (hA : IsE27 A) (h146 : Item146 A (lB A)) {Y : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {c : G} (hcA : c ∈ A)
    (hN : ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ ∈ scriptQ A (lB A))
    (hc : ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ ≤ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆)
    (hC : CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({c} : Set G) ∈ scriptQ A (lB A)) :
    CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set V := CFSG.Open.pCoreOf 2 Y with hV
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hV3 : ¬ 3 ∣ Nat.card V := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (pCoreOf_le_pPrimeCoreOf Y))
        (coprime_card_pPrimeCoreOf 3 Y)) h3
  have hfac : V = ⁅V, Subgroup.zpowers c⁆ ⊔ (V ⊓ Subgroup.centralizer ({c} : Set G)) := by
    have h := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three (Subgroup.zpowers c) V (hA.isPGroup.to_le (Subgroup.zpowers_le.mpr hcA))
      hV3 (Subgroup.zpowers_le.mpr (hAV hcA))
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      ← Subgroup.zpowers_eq_closure] at h
  have hCN : V ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer ((⁅V, Y⁆ : Subgroup G) : Set G) :=
    (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)).trans
      (le_normalizer_commutator (A := Y) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
        Subgroup.le_normalizer)
  have hsup := sup_mem_scriptQ_of_item146 hA h146 hC hN hCN
  refine mem_scriptQ_of_le hsup ?_ hAV
  calc V = ⁅V, Subgroup.zpowers c⁆ ⊔ (V ⊓ Subgroup.centralizer ({c} : Set G)) := hfac
    _ ≤ (V ⊓ Subgroup.centralizer ({c} : Set G)) ⊔ ⁅V, Y⁆ :=
        sup_le (hc.trans le_sup_right) le_sup_left

theorem pCoreOf_mem_scriptQ_of_scriptY4 (hA : IsE27 A) (h146 : Item146 A (lB A))
    {Y : Subgroup G} (hY : Y ∈ Sec15.scriptY4 A (lB A))
    (hN : ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ ∈ scriptQ A (lB A)) {c : G} (hcA : c ∈ A)
    (hcY : c ∈ Y ∨ ∀ y ∈ Y, ⁅y, c⁆ ∈ CFSG.Open.pCoreOf 2 Y)
    (hC : CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({c} : Set G) ∈ scriptQ A (lB A)) :
    CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.1.2
  refine pCoreOf_mem_scriptQ_of_le hA h146 hAY hcA hN ?_ hC
  rcases hcY with hcY | hcY
  · exact Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hcY)
  · exact commutator_zpowers_le (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y) hY.2.1
      ((hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)) hcA) hcY

end CFSG.RankThree.PartTwo.Sec17.Proof17Q0
