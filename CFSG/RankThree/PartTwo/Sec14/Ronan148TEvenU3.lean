module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenDefs
public import Certificates.Certificate43
import CFSG.StronglyEmbedded
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.StronglyEmbedded.BenderBorelTransport
import CFSG.StronglyEmbedded.MatrixGroups.SzModel
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
import CFSG.CGT.PushingUp.BenderBridge
import CFSG.CGT.Timmesfeld75.ListWCSzU3
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.Timmesfeld.Orders.Bang
import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd
import CFSG.Adapters.RankThreeOutcomesReverse
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.CentralLiftU.UnitaryThreeEven
import CFSG.CharacterTheory.Burnside
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Certificates.CosetTableShort
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Transport
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddDefs
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47LThree
public import CFSG.RankThree.PartTwo.Sec4.Item47SpFour
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import Certificates.Certificate2201
public import Certificates.Certificate2202
public import Certificates.Certificate2326
public import Certificates.Certificate3171
public import Certificates.Certificate3171Base
public import Certificates.Certificate8166
public import Certificates.Certificate8169
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSU StatedLieAdmissible
  projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.Assembly.RankThreeEven (projSU projImage)

theorem card_statedProj_statedSU_three_two_mul {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (StatedProj (StatedSU 3 (2 ^ m) (GaloisField 2 (2 * m)))) * Nat.gcd 3 (2 ^ m + 1) =
      (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) :=
  CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSU_three_mul
    ⟨Nat.prime_two, hm, GaloisField.card 2 (2 * m) (by omega)⟩

theorem not_isSolvable_of_simple {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) : ¬ Group.IsSolvable G := by
  intro hsol
  obtain ⟨a, b, hab⟩ := hnab
  have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := G)).mpr hsol
  exact hab (hcomm a b)

theorem isStronglyEmbeddedOrder_inf {X : Type} [Group X] [Finite X] {Q : Subgroup X}
    (hSE : CFSG.Open.fusionStronglyEmbedded (Subgroup.normalizer (Q : Set X)))
    {K : Subgroup X} (hKs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    {t : K} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (htQ : (t : X) ∈ Q) (hQ2 : IsPGroup 2 Q) :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder
      ((Subgroup.normalizer (Q : Set X)).comap K.subtype) := by
  set M := Subgroup.normalizer (Q : Set X) with hM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_, ?_⟩
  ·
    intro htop
    have hKM : ∀ k : K, (k : X) ∈ M := fun k => by
      have : k ∈ M.comap K.subtype := htop ▸ Subgroup.mem_top k
      exact this
    have hN : (Q.comap K.subtype).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hg := hKM g
      rw [Subgroup.mem_comap] at hn ⊢
      have := (Subgroup.mem_normalizer_iff.mp hg ((K.subtype n))).mp hn
      simpa using this
    haveI := hN
    rcases hKs.eq_bot_or_eq_top_of_normal (Q.comap K.subtype) with h | h
    · have : t ∈ Q.comap K.subtype := htQ
      rw [h, Subgroup.mem_bot] at this
      exact ht1 this
    · apply not_isSolvable_of_simple hKs hnab
      have hP : IsPGroup 2 K := fun k => by
        have hk : (k : X) ∈ Q := by
          have : k ∈ Q.comap K.subtype := h ▸ Subgroup.mem_top k
          exact this
        obtain ⟨n, hn⟩ := hQ2 ⟨k, hk⟩
        refine ⟨n, Subtype.ext ?_⟩
        have h1 := congrArg Subtype.val hn
        rw [Subgroup.coe_pow, Subgroup.coe_one] at h1
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact h1
      have := hP.isNilpotent
      infer_instance
  ·
    have htM : t ∈ M.comap K.subtype :=
      (Subgroup.le_normalizer : Q ≤ Subgroup.normalizer (Q : Set X)) htQ
    have hord : orderOf (⟨t, htM⟩ : M.comap K.subtype) = 2 := by
      apply orderOf_eq_prime
      · apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact ht2
      · intro h
        exact ht1 (congrArg Subtype.val h)
    rw [even_iff_two_dvd, ← hord]
    exact orderOf_dvd_natCard _
  ·
    intro g hg
    have hg' : (g⁻¹ : X)⁻¹ ∉ M := by
      rw [inv_inv]
      exact hg
    have hginv : (g⁻¹ : X) ∉ M := fun h => hg' (inv_mem h)
    have hodd := hSE.2.2 (g⁻¹ : X) hginv
    rw [inv_inv] at hodd
    have hle : ((M.comap K.subtype) ⊓ (M.comap K.subtype).map (MulAut.conj g).toMonoidHom).map
        K.subtype ≤ M ⊓ M.map (MulAut.conj (g : X)).toMonoidHom := by
      rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine ⟨hx1, ?_⟩
      obtain ⟨y, hy, rfl⟩ := hx2
      refine ⟨(y : X), hy, ?_⟩
      simp [MulAut.conj_apply]
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective K.subtype_injective] at hdvd
    exact Odd.of_dvd_nat hodd hdvd

theorem not_five_dvd_of_odd {e : ℕ} (he : e % 2 = 1) :
    ¬ 5 ∣ (2 ^ e) ^ 3 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1) := by
  have hs : 2 ^ e % 5 = 2 ∨ 2 ^ e % 5 = 3 := by
    obtain ⟨j, hj⟩ : ∃ j, e = 4 * j + e % 4 := ⟨e / 4, by omega⟩
    have h16 : 16 ^ j % 5 = 1 := by rw [Nat.pow_mod]; norm_num
    have hr : e % 4 = 1 ∨ e % 4 = 3 := by omega
    rw [hj, pow_add, pow_mul]
    norm_num
    rcases hr with hr | hr <;> rw [hr] <;> norm_num [Nat.mul_mod, h16]
  set s := 2 ^ e with hsdef
  have hs1 : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num)))
  intro h5
  have h5p : Nat.Prime 5 := by norm_num
  rcases (Nat.Prime.dvd_mul h5p).mp h5 with h | h
  · rcases (Nat.Prime.dvd_mul h5p).mp h with h | h
    · have := h5p.dvd_of_dvd_pow h
      omega
    · have h2 : s ^ 2 % 5 = 4 := by
        rw [Nat.pow_mod]
        rcases hs with hs | hs <;> rw [hs] <;> norm_num
      omega
  · have h3 : s ^ 3 % 5 = 3 ∨ s ^ 3 % 5 = 2 := by
      rw [Nat.pow_mod]
      rcases hs with hs | hs <;> rw [hs] <;> norm_num
    omega

theorem five_dvd_card_suzuki {n : ℕ} (hn : 1 ≤ n) :
    5 ∣ Nat.card (CFSG.Theory.Comparator.SzModel n) := by
  rw [(show CFSG.Theory.Comparator.SzModel _ = _ from CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup _),
    CFSG.BenderSuzuki.lemma114_suzukiMatrixGroup_card_formula n (by omega)]
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
  have h16 : 16 ^ n % 5 = 1 := by rw [Nat.pow_mod]; norm_num
  have : (2 ^ (2 * n + 1)) ^ 2 + 1 = 4 * 16 ^ n + 1 := by
    rw [← pow_mul, show (2 * n + 1) * 2 = 4 * n + 2 by ring, pow_add, pow_mul]
    norm_num
    ring
  rw [this]
  omega

theorem evenSimpleList_unitary {X : Type} [Group X] [Finite X]
    {e : ℕ} (he : 1 ≤ e) (hq : 2 ^ e % 3 = 2) (φ : X ≃* projSU 3 2 e) (K : Subgroup X)
    (hKs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) :
    (∃ j : ℕ, 2 ≤ j ∧ StatedClassicalModel K .PSL 2 2 j) ∨
      (∃ f : ℕ, 1 ≤ f ∧ f ∣ e ∧
        (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; IsLThreeEpsAt K 2 f)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKns := not_isSolvable_of_simple hKs hnab
  have hodd : e % 2 = 1 := by
    by_contra h
    obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k := ⟨e / 2, by omega⟩
    rw [pow_mul, Nat.pow_mod] at hq
    norm_num at hq
  have hF : Sec4.PiField false 2 e (GaloisField 2 (2 * e)) := ⟨Nat.prime_two, he, by
    rw [GaloisField.card 2 (2 * e) (by omega)]
    change 2 ^ (2 * e) = (2 ^ e) ^ 2
    rw [← pow_mul, mul_comm]⟩
  have hX3 : Nat.card X * 3 = (2 ^ e) ^ 3 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1) := by
    have h := Sec13.card_projImage_slPi_mul_three hF hq
    rw [← Nat.card_congr (φ.trans (MulEquiv.subgroupCongr (Sec4.projSU_eq_projImage 2 e))).toEquiv]
      at h
    exact h
  rcases Nat.lt_or_ge e 2 with he1 | he2
  ·
    exfalso
    have he1' : e = 1 := by omega
    subst he1'
    apply hKns
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 (GaloisField 2 (2 * 1)) :=
      hF.unitary
    have hcard := CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
    have := Fintype.ofFinite (StatedSU 3 (2 ^ 1) (GaloisField 2 (2 * 1)))
    have hsolv : Group.IsSolvable (StatedSU 3 (2 ^ 1) (GaloisField 2 (2 * 1))) :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
        Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
    have hsolv' : Group.IsSolvable (Sec4.slPi false 3 (2 ^ 1) (GaloisField 2 (2 * 1))) := hsolv
    have h1 : Group.IsSolvable (projImage (Sec4.slPi false 3 (2 ^ 1) (GaloisField 2 (2 * 1)))) :=
      Group.isSolvable_of_surjective (Sec4.projOf_surjective _)
    have hX : Group.IsSolvable X := Group.isSolvable_of_surjective
      (f := (φ.trans (MulEquiv.subgroupCongr (Sec4.projSU_eq_projImage 2 1))).symm.toMonoidHom)
      (MulEquiv.surjective _)
    infer_instance
  have hadm : StatedLieAdmissible .PSU 3 2 e := ⟨Nat.prime_two, he, le_rfl, fun h => by
    have h2 : 2 ^ e = 2 ^ 1 := by simpa using congrArg Prod.snd h
    have := Nat.pow_right_injective (le_refl 2) h2
    omega⟩
  have hXm : StatedClassicalModel X .PSU 3 2 e :=
    CFSG.Assembly.RankThreeEven.statedClassicalModel_of_projSU hadm φ
  obtain ⟨ψ⟩ := CFSG.CGT.Timmesfeld75.exists_psu3_of_statedClassicalModel he2 hXm
  have : Finite (CFSG.Open.PSU3 2 e) := Finite.of_equiv X ψ.toEquiv
  have hB : CFSG.Open.fusionBenderBorel X (2 ^ e) 3 :=
    (CFSG.Open.bender_psu3_borel_full e he2).map_mulEquiv ψ.symm
  have h2K : 2 ∣ Nat.card K := by
    by_contra hodd2
    have hoddK : Odd (Nat.card K) := Nat.odd_iff.mpr (by omega)
    exact hKns (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hoddK)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2K
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    norm_num at ht
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have hP : IsPGroup 2 (Subgroup.zpowers (t : X)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht, pow_one]
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  have htQ : (t : X) ∈ (Q : Subgroup X) := hQ (Subgroup.mem_zpowers _)
  have hSE := (hB Q).1
  have hSEK := isStronglyEmbeddedOrder_inf hSE hKs hnab ht1 ht2 htQ Q.isPGroup'
  have hBK : CFSG.BenderSuzuki.IsBenderGroup K := CFSG.BenderSuzuki.bender_suzuki _ hSEK
  rcases hBK with ⟨n, hn, e'⟩ | ⟨n, hn, e'⟩ | ⟨n, hn, e'⟩
  ·
    refine Or.inl ⟨n, hn, ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, GaloisField 2 n,
      inferInstance, inferInstance, GaloisField.card 2 n (by omega),
      ⟨e'.trans (projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 n))⟩⟩
    · intro h
      have h2 : 2 ^ n = 2 ^ 1 := by simpa using congrArg Prod.snd h
      have := Nat.pow_right_injective (le_refl 2) h2
      omega
    · intro h
      have h2 : 2 ^ n = 3 := by simpa using congrArg Prod.snd h
      have : 2 ∣ 3 := h2 ▸ dvd_pow_self 2 (by omega)
      omega
  ·
    exfalso
    apply not_five_dvd_of_odd hodd
    rw [← hX3]
    refine Dvd.dvd.mul_right ?_ _
    have h5 := five_dvd_card_suzuki hn
    rw [← Nat.card_congr e'.toEquiv] at h5
    exact h5.trans (Subgroup.card_subgroup_dvd_card K)
  ·
    refine Or.inr ⟨n, by omega, ?_, Or.inr ⟨?_, CFSG.CGT.PushingUp.benderBridge_psu hn e'⟩⟩
    · have hmodel : CFSG.Theory.Comparator.PSU3Model n = CFSG.Open.PSU3 2 n :=
        CFSG.Models.benderPSU3Model_eq_psu3 n
      let eK : K ≃* StatedProj (StatedSU 3 (2 ^ n) (GaloisField 2 (2 * n))) :=
        (e'.trans (MulEquiv.subgroupCongr hmodel)).trans
          (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative n).symm
      have hK3 := card_statedProj_statedSU_three_two_mul (m := n) (by omega)
      rw [← Nat.card_congr eK.toEquiv] at hK3
      have hk : 0 < 6 * n := by omega
      obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 6 * n) (by omega)
        (by omega)
      have hrp := hr.prime
      have hr3 : r ≠ 3 := fun h3 => by
        have := hr.eq_two_of_dvd_three hk (by rw [h3])
        omega
      have hr2 := hr.ne_two hk
      have hrq : r ∣ 2 ^ (3 * n) + 1 := (hr.dvd_add_one_iff hk (3 * n)).mpr
        ⟨⟨1, by ring⟩, fun h => by
          have := Nat.le_of_dvd (by omega) h
          omega⟩
      have hrK : r ∣ Nat.card K := by
        have h1 : r ∣ Nat.card K * Nat.gcd 3 (2 ^ n + 1) := by
          rw [hK3, ← pow_mul, mul_comm n 3]
          exact Dvd.dvd.mul_left hrq _
        have hcop : Nat.Coprime r (Nat.gcd 3 (2 ^ n + 1)) :=
          Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _)
            ((Nat.coprime_primes hrp Nat.prime_three).mpr hr3)
        exact hcop.dvd_of_dvd_mul_right h1
      have hrX : r ∣ (2 ^ e) ^ 3 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1) := by
        rw [← hX3]
        exact (hrK.trans (Subgroup.card_subgroup_dvd_card K)).mul_right _
      rcases (Nat.Prime.dvd_mul hrp).mp hrX with h | h
      · rcases (Nat.Prime.dvd_mul hrp).mp h with h | h
        · exfalso
          have h2 := hrp.dvd_of_dvd_pow (hrp.dvd_of_dvd_pow h)
          exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp h2)
        · rw [← pow_mul, mul_comm e 2] at h
          have h6 := (hr.dvd_sub_one_iff hk (2 * e)).mp h
          obtain ⟨c, hc⟩ := h6
          exact ⟨3 * c, by linarith⟩
      · rw [← pow_mul, mul_comm e 3] at h
        have h6 := ((hr.dvd_add_one_iff hk (3 * e)).mp h).1
        obtain ⟨c, hc⟩ := h6
        exact ⟨c, by linarith⟩
    · calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

@[expose] def EvenSimpleListL3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (e : ℕ), 1 ≤ e → 2 ^ e % 3 = 1 →
    Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 e)) →
    ∀ K : Subgroup X, IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
      (∃ j : ℕ, 2 ≤ j ∧ StatedClassicalModel K .PSL 2 2 j) ∨
      StatedClassicalModel K .PSL 2 3 2 ∨
      (∃ f : ℕ, 1 ≤ f ∧ f ∣ e ∧
        (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; IsLThreeEpsAt K 2 f))

theorem evenSimpleList_of_L3 (hL3 : EvenSimpleListL3) :
    EvenSimpleList := by
  intro X _ _ e he hiso K hKs hnab
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hiso with ⟨hq, hφ⟩ | ⟨hq, ⟨φ⟩⟩
  · exact hL3 X e he hq hφ K hKs hnab
  · rcases evenSimpleList_unitary he hq φ K hKs hnab with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
