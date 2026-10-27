module

public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofDefs
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
import CFSG.RankThree.PartTwo.Sec4.T444.Lift
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item146General

public section

namespace CFSG.RankThree.PartTwo.Sec15.Y4Core

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem open_pCoreOf_two_le_pPrimeCoreOf {Z J : Subgroup G} (hJ : J ∈ thetaComponentsIn Z) :
    CFSG.Open.pCoreOf 2 J ≤ pPrimeCoreOf 3 Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJZ, hJ'⟩ := mem_thetaComponentsIn_iff.mp hJ
  set O := CFSG.Open.pCoreOf 2 J with hOdef
  have hOJ : O ≤ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J
  have hOZ : O ≤ Z := hOJ.trans hJZ
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J
  have hJO : J ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J
  have hsub : (O.subgroupOf Z).IsSubnormal := by
    refine Subgroup.IsSubnormal.step _ (J.subgroupOf Z) (Subgroup.subgroupOf_mono Z hOJ)
      hJ'.2.1 ?_
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.subgroupOf_mono Z hOJ),
      ← Subgroup.subgroupOf_normalizer_eq hOZ]
    exact Subgroup.subgroupOf_mono Z hJO
  have h3 : ¬ 3 ∣ Nat.card (O.subgroupOf Z) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOZ).toEquiv]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hO2
    rw [hk]
    intro h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  rw [← Subgroup.map_subgroupOf_eq_of_le hOZ]
  exact Subgroup.map_mono (Sec4.le_pPrimeCore_of_isSubnormal hsub h3)

omit [Finite G] in
theorem pow_eq_one_map {Z : Subgroup G} (R : Subgroup ↥Z) [R.Normal] {x : G} (hx : x ∈ Z) {n : ℕ}
    (hn : x ^ n = 1) : (QuotientGroup.mk' R ⟨x, hx⟩) ^ n = 1 := by
  rw [← map_pow]
  have : (⟨x, hx⟩ : ↥Z) ^ n = 1 := Subtype.ext (by simpa using hn)
  rw [this, map_one]

theorem le_pPrimeCoreOf_of_commute {Z D P : Subgroup G} (hDZ : D ≤ Z)
    (hZD : Z ≤ Subgroup.normalizer (D : Set G)) (hPD : P ≤ D) {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) (hP : IsPGroup p P)
    (hcomm : ∀ x ∈ P, ∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ pPrimeCoreOf 3 Z) :
    P ≤ pPrimeCoreOf 3 Z := by
  classical
  set R := CFSG.pPrimeCore 3 ↥Z with hR
  set π := QuotientGroup.mk' R with hπ
  set Db := (D.subgroupOf Z).map π with hDb
  set Pb := (P.subgroupOf Z).map π with hPb
  have hD'n : (D.subgroupOf Z).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDZ).mpr hZD
  have hDbn : Db.Normal := hD'n.map π (QuotientGroup.mk'_surjective R)
  set Nb := Db ⊓ Subgroup.centralizer (Db : Set (↥Z ⧸ R)) with hNb
  have hNbn : Nb.Normal := by
    have : (Subgroup.centralizer (Db : Set (↥Z ⧸ R))).Normal := Subgroup.normal_centralizer
    exact Subgroup.normal_inf_normal _ _
  have hxd : ∀ (x : ↥Z), (x : G) ∈ P → ∀ (d : ↥Z), (d : G) ∈ D → π d * π x = π x * π d := by
    intro x hx d hd
    have hmem := hcomm x hx d hd
    obtain ⟨r, hr, hrx⟩ := hmem
    have hr' : r = x * d * x⁻¹ * d⁻¹ := Subtype.ext (by simpa using hrx)
    have h1 : π (x * d * x⁻¹ * d⁻¹) = 1 := by
      rw [← hr', hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hr
    have h2 : π x * π d = π d * π x := by
      have := h1
      simp only [map_mul, map_inv] at this
      calc π x * π d = π x * π d * (π x)⁻¹ * (π d)⁻¹ * (π d * π x) := by group
        _ = π d * π x := by rw [this, one_mul]
    exact h2.symm
  have hPNb : (Pb : Set (↥Z ⧸ R)) ⊆ Nb := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.mpr
      ⟨⟨x, Subgroup.mem_subgroupOf.mpr (hPD (Subgroup.mem_subgroupOf.mp hx)), rfl⟩,
        Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    exact hxd x (Subgroup.mem_subgroupOf.mp hx) d (Subgroup.mem_subgroupOf.mp hd)
  set Q := Subgroup.normalClosure (Pb : Set (↥Z ⧸ R))
  have hQN : Q ≤ Nb := Subgroup.normalClosure_le_normal hPNb
  have hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hQN hb).2 a (hQN ha).1)
  have hQp : ∀ q ∈ Q, ∃ k : ℕ, q ^ p ^ k = 1 := by
    intro q hq
    induction hq using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨z, hz, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
      obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨k, hk⟩ := hP ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩
      refine ⟨k, ?_⟩
      have hk' : (x : G) ^ p ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      rw [conj_pow, pow_eq_one_map R x.2 hk', mul_one, mul_inv_cancel]
    | one => exact ⟨0, by simp⟩
    | mul a b ha hb iha ihb =>
      obtain ⟨i, hi⟩ := iha
      obtain ⟨j, hj⟩ := ihb
      refine ⟨i + j, ?_⟩
      rw [(Commute.mul_pow (hQcomm a ha b hb) _), pow_add, pow_mul, hi, one_pow, one_mul,
        mul_comm (p ^ i), pow_mul, hj, one_pow]
    | inv a ha iha =>
      obtain ⟨i, hi⟩ := iha
      exact ⟨i, by rw [inv_pow, hi, inv_one]⟩
  have hQP : IsPGroup p Q := fun q => by
    obtain ⟨k, hk⟩ := hQp q q.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hQ3 : Nat.Coprime 3 (Nat.card Q) := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQP
    rw [hm]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
  have hQbot : Q = ⊥ := by
    have hle : Q ≤ CFSG.pPrimeCore 3 (↥Z ⧸ R) := le_sSup ⟨Subgroup.normalClosure_normal, hQ3⟩
    rw [CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three] at hle
    exact le_bot_iff.mp hle
  have hPb : Pb = ⊥ := le_bot_iff.mp (hQbot ▸ Subgroup.subset_normalClosure)
  intro x hx
  have hxZ : x ∈ Z := hDZ (hPD hx)
  have hxR : (⟨x, hxZ⟩ : ↥Z) ∈ R := by
    have : π ⟨x, hxZ⟩ ∈ Pb := ⟨⟨x, hxZ⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hPb, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  exact ⟨⟨x, hxZ⟩, hxR, rfl⟩

omit [Finite G] in
theorem deltaZero_le_deltaZero_delta {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (M : Subgroup G) : deltaZero A LB M ≤ deltaZero A LB (delta A LB M) :=
  sSup_le fun _ hQ => le_deltaZero hQ.1 (le_delta hQ.1.1 hQ.2)

omit [Finite G] in
theorem delta_mem_scriptY {A : Subgroup G} {LB : Subgroup G → Subgroup G} {M : Subgroup G}
    (hM : M ∈ scriptY A) : delta A LB M ∈ scriptY A :=
  ⟨fun h => hM.1 (top_le_iff.mp (h ▸ delta_le M)), le_normalizer_delta M⟩

theorem twoLocal_facts {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {Y : Subgroup G}
    (hY : Y ∈ scriptY2 A) :
    Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) ∈ scriptY2 A ∧
      generalizedFitting ↥(Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)) =
        CFSG.pCore 2 ↥(Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)) ∧
      Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) with hM
  have hM2 : M ∈ scriptY2 A :=
    Sec16.normalizer_pCoreOf_mem_scriptY2 h.isSimpleGroup h.nonabelian hY
  have hYM : Y ≤ M := Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hloc : IsPLocal 2 M :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y) hY.2
  have hF : generalizedFitting ↥M = CFSG.pCore 2 ↥M :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥M 2).mp
      (CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal h.toTheoremFourHyp.charTwoType hloc)
  exact ⟨hM2, hF, hYM⟩

theorem exists_mem_scriptY0 (hRead : Y4CoreReadR) (hMem : Y4CoreMemR) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {M : Subgroup G}
    (hM : M ∈ scriptY2 A) (hF : generalizedFitting ↥M = CFSG.pCore 2 ↥M) :
    (∃ J₁ J₂ : Subgroup G, ∀ J ∈ comp3In (delta A (lB A) M), J = J₁ ∨ J = J₂) ∧
      (∀ J ∈ comp3In (delta A (lB A) M), A ≤ Subgroup.normalizer (J : Set G) ∧
        J ∈ scriptY0 A (lB A)) ∧
      oPrimeResidualOf 3 (delta A (lB A) M) ≤ sSup (comp3In (delta A (lB A) M)) ∧
      deltaZero A (lB A) (delta A (lB A) M) ≤
        sSup (comp3In (delta A (lB A) M)) ⊔ pPrimeCoreOf 3 (delta A (lB A) M) := by
  set Z := delta A (lB A) M with hZ
  have hZY : Z ∈ scriptY A := delta_mem_scriptY hM.1
  have hZΔ : Z = delta A (lB A) Z := (delta_delta M).symm
  obtain ⟨⟨J₁, J₂, hS⟩, hD⟩ := hRead G A c L h Z hZY hZΔ
  have hA : ∀ J ∈ comp3In Z, A ≤ Subgroup.normalizer (J : Set G) := fun J hJ =>
    le_normalizer_of_isElemAbelian hS h.isElemAbelian hZY.2 hJ
  refine ⟨⟨J₁, J₂, hS⟩, fun J hJ => ⟨hA J hJ, hMem G A c L h M hM hF J hJ (hA J hJ)⟩,
    oPrimeResidualOf_le_sSup h.toSec14Std.isE27 hbot hZY.2 hZΔ hD, hD⟩

end CFSG.RankThree.PartTwo.Sec15.Y4Core
