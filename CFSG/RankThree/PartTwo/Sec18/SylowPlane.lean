module

public import CFSG.RankThree.PartTwo.Sec18.SylowWStar
public import CFSG.RankThree.PartTwo.Sec18.Statements
import CFSG.RankThree.PartTwo.Sec20.OneBasics
import CFSG.RankThree.PartTwo.Sec20.Item203OneProof
import CFSG.RankThree.PartTwo.Sec18.Item18ResProofTools
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofHeis
import CFSG.RankThree.PartTwo.Sec13.Item133Mono
import CFSG.RankThree.PartTwo.Sec11.Item116H3Rank
import CFSG.RankThree.PartTwo.Sec4.T444.L34Shape
import CFSG.RankThree.PartTwo.KFacts.L34Automizer
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.PartTwo.Sec18.Claim184LcProof
import CFSG.RankThree.PartTwo.Sec18.Item184a
import CFSG.RankThree.PartTwo.Sec18.Item181
import CFSG.RankThree.PartTwo.Late.GammaZero
import CFSG.RankThree.PartTwo.Late.Transitivity
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec11.Theorem1134
import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRem
import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemHc
import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemRank
import CFSG.RankThree.PartTwo.Sec19.Item194Used
import CFSG.RankThree.PartTwo.Sec19.Steps195
import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner
import CFSG.RankThree.PartTwo.Sec4.T444.Step451
import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev lc (H : Subgroup G) (c : G) : Subgroup G :=
  inSubgroup perfectResidual ((inSubgroup perfectResidual H ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)))

theorem exists_quaternion_autIn {X B : Subgroup G}
    (e : X ⧸ CFSG.pCore 2 X ≃* projSL 3 (GaloisField 2 2)) (hBX : B ≤ X) (hB3 : IsPGroup 3 B)
    (hB9 : Nat.card B = 9) :
    ∃ f : QuaternionGroup 2 →* Sec4.autIn X B, Function.Injective f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  have hB3' : IsPGroup 3 (B.subgroupOf X) := hB3.comap_subtype
  have hinj : Function.Injective (π.comp (B.subgroupOf X).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have h1 : (x : ↥X) ∈ B.subgroupOf X ⊓ CFSG.pCore 2 ↥X := ⟨x.2, hx⟩
    have hbot : B.subgroupOf X ⊓ CFSG.pCore 2 ↥X = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ (Sec20.card_inf_eq_one_of_isPGroup hB3' CFSG.pCore_isPGroup)
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  set Bb := (B.subgroupOf X).map π with hBb
  set β := Sec20.quotientRestrictEquiv hBX hinj with hβ
  have hBb9 : Nat.card Bb = 9 := by
    rw [← Nat.card_congr β.toEquiv, hB9]
  set e' := e.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with he'
  have hBb' : Nat.card (Bb.map e'.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective, hBb9]
  obtain ⟨q⟩ := KFacts.L34.nonempty_automizer_of_card_eq_nine
    KFacts.L34.card_galoisField_two_two hBb'
  let qB : Sec4.autIn ⊤ Bb ≃* QuaternionGroup 2 :=
    (KFacts.L34.automizerEquivAutIn Bb).symm.trans
      ((CFSG.RankThree.Asc83Table.automizerCongr e' Bb).trans q)
  have hle : (Sec4.autIn ⊤ Bb).map (MulAut.congr β.symm).toMonoidHom ≤ Sec4.autIn X B := by
    rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨z, hzN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) z
    obtain ⟨y, hy, m, hm, rfl⟩ := Sec20.exists_mul_of_mk_mem_normalizer hBX hB3 hzN
    obtain ⟨b, hb, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    have hbB : ((b : ↥X) : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
    have hnN : ((b : G) * (m : G)) ∈ Subgroup.normalizer (B : Set G) :=
      mul_mem (Subgroup.le_normalizer hbB) hm
    refine Sec4.mem_autIn_iff.mpr ⟨(b : G) * m, hnN, X.mul_mem b.2 m.2, ?_⟩
    have ho1 : π o = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ho
    apply MulEquiv.ext
    intro w
    apply β.injective
    rw [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
      MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe, Sec20.quotientRestrictEquiv_apply,
      Sec20.quotientRestrictEquiv_apply]
    have hval : (⟨(B.normalizerMonoidHom ⟨(b : G) * m, hnN⟩ w : G),
        hBX (B.normalizerMonoidHom ⟨(b : G) * m, hnN⟩ w).2⟩ : ↥X) =
        b * m * ⟨w, hBX w.2⟩ * (b * m)⁻¹ := by
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hval, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_mul, ho1, mul_one]
  set ι := (Sec4.autIn ⊤ Bb).equivMapOfInjective (MulAut.congr β.symm).toMonoidHom
    (MulAut.congr β.symm).injective with hι
  exact ⟨(Subgroup.inclusion hle).comp (ι.toMonoidHom.comp qB.symm.toMonoidHom),
    (Subgroup.inclusion_injective hle).comp (ι.injective.comp qB.symm.injective)⟩

omit [Finite G] in
theorem mem_of_pow_two_pow_mem {X : Subgroup G} {c : G} (hc3 : c ^ 3 = 1) {k : ℕ}
    (h : c ^ 2 ^ k ∈ X) : c ∈ X := by
  have h4 : (2 ^ k * 2 ^ k) % 3 = 1 := by
    rw [← mul_pow, show (2 * 2 : ℕ) = 4 by norm_num, Nat.pow_mod]
    norm_num
  have hc : c = (c ^ 2 ^ k) ^ 2 ^ k := by
    rw [← pow_mul, pow_eq_pow_mod _ hc3, h4, pow_one]
  rw [hc]
  exact X.pow_mem h _

theorem mem_normalizer_zpowers_sup {B : Subgroup G} {c x : G} (hxc : x * c = c * x)
    (hxB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((Subgroup.zpowers c ⊔ B : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  have hle : Subgroup.zpowers c ⊔ B ≤
      (Subgroup.zpowers c ⊔ B).comap (MulAut.conj x).toMonoidHom := by
    refine sup_le ?_ fun b hb => ?_
    · rw [Subgroup.zpowers_le]
      show x * c * x⁻¹ ∈ Subgroup.zpowers c ⊔ B
      rw [hxc, mul_inv_cancel_right]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
    · show x * b * x⁻¹ ∈ Subgroup.zpowers c ⊔ B
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hxB b).mp hb)
  exact hle hy

section Notation

variable {A M H : Subgroup G} {c : G}

theorem mem_and_commutator_mem_of_sec18H (hH : Sec18H G A M H c) :
    c ∈ A ∧ ∀ x ∈ inSubgroup perfectResidual H,
      c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H) := by
  have hc : c ∈ sectionCentralizer A (inSubgroup perfectResidual H)
      (CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H)) := by
    rw [hH.centralizer_eq]
    exact Subgroup.mem_zpowers c
  exact hc

theorem pow_three_eq_one_of_sec18H (hH : Sec18H G A M H c) : c ^ 3 = 1 :=
  (isE27_of_mem_partTwoE hH.mem_partTwoE).1.2 c (mem_and_commutator_mem_of_sec18H hH).1

theorem orderOf_eq_three_of_sec18H (h184 : Item184_1) (hH : Sec18H G A M H c) :
    orderOf c = 3 := by
  obtain ⟨-, c', hc', hcen⟩ := h184 G A M hH.toSec18Std H hH.mem_scriptH
  have h : Subgroup.zpowers c = Subgroup.zpowers c' :=
    SetLike.coe_injective (hH.centralizer_eq.symm.trans hcen)
  rw [← Nat.card_zpowers, h, Nat.card_zpowers, hc']

theorem not_mem_of_sec18H (h184 : Item184_1) (hH : Sec18H G A M H c) :
    c ∉ inSubgroup perfectResidual H := by
  intro hcL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := inSubgroup perfectResidual H with hL
  obtain ⟨⟨e⟩, -⟩ := h184 G A M hH.toSec18Std H hH.mem_scriptH
  obtain ⟨-, hcc⟩ := mem_and_commutator_mem_of_sec18H hH
  have hord := orderOf_eq_three_of_sec18H h184 hH
  have hcen : ((⟨c, hcL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ∈
      Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 : (((⟨c, hcL⟩ : ↥L) * x * (⟨c, hcL⟩ : ↥L)⁻¹ * x⁻¹ : ↥L) :
        ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
      rw [QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
      exact hcc x x.2
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, ← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    have hmap := Subgroup.map_center_eq e
    rw [Sec4.center_projSL_eq_bot] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at hcen
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨c, hcen⟩
  have hck : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 : 3 ∣ 2 ^ k := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hck
  have := Nat.prime_three.dvd_of_dvd_pow h3
  norm_num at this

theorem le_sup_and_inf_le_of_sec18H (hH : Sec18H G A M H c) :
    inSubgroup perfectResidual H ≤
        inSubgroup perfectResidual (inSubgroup perfectResidual H ⊓
          Subgroup.centralizer ({c} : Set G)) ⊔
          CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H) ∧
      A ⊓ inSubgroup perfectResidual H ≤
        inSubgroup perfectResidual (inSubgroup perfectResidual H ⊓
          Subgroup.centralizer ({c} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := inSubgroup perfectResidual H with hL
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set P := L ⊓ C with hP
  set L₀ := inSubgroup perfectResidual P with hL₀
  obtain ⟨hcA, hcc⟩ := mem_and_commutator_mem_of_sec18H hH
  have hA := isE27_of_mem_partTwoE hH.mem_partTwoE
  have hc3 := pow_three_eq_one_of_sec18H hH
  have hAH : A ≤ H := le_of_mem_scriptH₀ (mem_scriptH_iff_mem_scriptH₀.mp hH.mem_scriptH).1
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual H
      (Subgroup.le_normalizer (hAH hcA))
  have hle : L ≤ L₀ ⊔ CFSG.Open.pCoreOf 2 L :=
    Item18ResProof.le_perfectResidual_inf_centralizer_sup
      (commutator_inSubgroup_perfectResidual H) hcN hc3 hcc
  refine ⟨hle, ?_⟩
  have hL₀P : L₀ ≤ P := Subgroup.map_subtype_le _
  have hL₀O : L₀ ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    (hL₀P.trans inf_le_left).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have : (perfectResidual ↥P).Characteristic :=
    (CFSG.perfect_residual_characterization (G := ↥P)).2.1
  have hq : IsPGroup 2 (↥P ⧸ perfectResidual ↥P) := by
    intro q
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
    have hp : (p : G) ∈ (L₀ : Set G) * (CFSG.Open.pCoreOf 2 L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hL₀O]
      exact hle p.2.1
    obtain ⟨l, hl, o, ho, hlo⟩ := hp
    have hl0 : l ∈ (perfectResidual ↥P).map P.subtype := hl
    obtain ⟨l', hl', hll⟩ := Subgroup.mem_map.mp hl0
    have hll' : (l' : G) = l := hll
    subst hll'
    have hoP : o ∈ P := by
      have e : o = (l' : G)⁻¹ * p := by rw [← hlo]; group
      rw [e]
      exact P.mul_mem (P.inv_mem l'.2) p.2
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨o, ho⟩
    refine ⟨k, ?_⟩
    have hpe : p = l' * ⟨o, hoP⟩ := Subtype.ext hlo.symm
    have hok : (⟨o, hoP⟩ : ↥P) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [hpe, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hl', one_mul,
      ← QuotientGroup.mk_pow, hok, QuotientGroup.mk_one]
  intro b hb
  have hbc : b * c = c * b :=
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨b, hb.1⟩ ⟨c, hcA⟩)
  have hbP : b ∈ P := ⟨hb.2, Subgroup.mem_centralizer_singleton_iff.mpr hbc⟩
  have hb3 : (⟨b, hbP⟩ : ↥P) ^ 3 ^ 1 = 1 := Subtype.ext (by simpa using hA.1.2 b hb.1)
  show b ∈ (perfectResidual ↥P).map P.subtype
  exact Subgroup.mem_map.mpr ⟨⟨b, hbP⟩, mem_of_isPGroup_quotient hq hb3, rfl⟩

theorem nonempty_quotient_perfectResidual_inf_centralizer (h184 : Item184_1)
    (hH : Sec18H G A M H c) :
    Nonempty (inSubgroup perfectResidual (inSubgroup perfectResidual H ⊓
        Subgroup.centralizer ({c} : Set G)) ⧸
      CFSG.pCore 2 (inSubgroup perfectResidual (inSubgroup perfectResidual H ⊓
        Subgroup.centralizer ({c} : Set G))) ≃* projSL 3 (GaloisField 2 2)) := by
  set L := inSubgroup perfectResidual H with hL
  set L₀ := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({c} : Set G)) with hL₀
  obtain ⟨⟨e⟩, -⟩ := h184 G A M hH.toSec18Std H hH.mem_scriptH
  have hL₀L : L₀ ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hLO : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  obtain ⟨⟨e₁⟩, -⟩ := Claim184LcProof.quotient_mulEquiv_of_le_sup (L := L₀)
    (R := CFSG.Open.pCoreOf 2 L) (N := L) hL₀L (le_sup_and_inf_le_of_sec18H hH).1
    (hL₀L.trans hLO) hLO (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  exact ⟨e₁.trans e⟩

theorem not_mem_lc (h184 : Item184_1) (hH : Sec18H G A M H c) : c ∉ lc H c := by
  intro hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := inSubgroup perfectResidual H with hL
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have hc3 := pow_three_eq_one_of_sec18H hH
  have hcR : c ∈ L ⊓ C ⊔ CFSG.Open.pCoreOf 2 C := Subgroup.map_subtype_le _ hc
  have hO : L ⊓ C ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 C : Set G) :=
    inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C)
  have hcR' : c ∈ ((L ⊓ C : Subgroup G) : Set G) * (CFSG.Open.pCoreOf 2 C : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hO]
    exact hcR
  obtain ⟨l, hl, o, ho, hlo⟩ := hcR'
  have hoC : o * c = c * o :=
    Subgroup.mem_centralizer_singleton_iff.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 C ho)
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C ⟨o, ho⟩
  have hok : o ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcomm : Commute c o⁻¹ := (Commute.inv_right (Commute.symm hoC))
  have hl' : l = c * o⁻¹ := by rw [← hlo]; group
  have hlk : l ^ 2 ^ k = c ^ 2 ^ k := by
    rw [hl', hcomm.mul_pow, inv_pow, hok, inv_one, mul_one]
  have hcL : c ^ 2 ^ k ∈ L := hlk ▸ L.pow_mem hl.1 _
  exact not_mem_of_sec18H h184 hH (mem_of_pow_two_pow_mem hc3 hcL)

theorem normalizer_zpowers_le_normalizer_lc (h1842 : Item184_2) (hH : Sec18H G A M H c) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (lc H c : Set G) := by
  obtain ⟨hLc, h3, huniq⟩ := h1842 G A M H c hH
  have hc3 := pow_three_eq_one_of_sec18H hH
  intro w hw
  have hwc : w * c * w⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hw c).mp (Subgroup.mem_zpowers c)
  have hmem := Sec11.map_conj_mem_thetaComponentsAt hc3 hLc hwc
  have hcard : 3 ∣ Nat.card ((lc H c).map (MulAut.conj w).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact h3
  have heq : (lc H c).map (MulAut.conj w).toMonoidHom = lc H c := huniq _ hmem hcard
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 : w * y * w⁻¹ ∈ (lc H c).map (MulAut.conj w).toMonoidHom := ⟨y, hy, rfl⟩
    rw [heq] at h1
    exact h1
  · intro hy
    have h1 : w * y * w⁻¹ ∈ (lc H c).map (MulAut.conj w).toMonoidHom := by
      rw [heq]
      exact hy
    obtain ⟨y', hy', hyy⟩ := h1
    have e : y' = y := by simpa using hyy
    rw [← e]
    exact hy'

theorem starNormalized_of_sec18H (h1842 : Item184_2) (hH : Sec18H G A M H c) :
    StarNormalized A (lc H c ⊓ Subgroup.normalizer (A : Set G)) c :=
  starNormalized_of_le (Late.le_normalizer_inf
    (inf_le_right.trans (normalizer_zpowers_le_normalizer_lc h1842 hH))
    (inf_le_left.trans Subgroup.le_normalizer))

section Certified


theorem card_inf_of_sec18H (h1812 : Item181_2) (h184 : Item184_1) (hH : Sec18H G A M H c) :
    Nat.card (A ⊓ inSubgroup perfectResidual H : Subgroup G) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨e⟩, -⟩ := h184 G A M hH.toSec18Std H hH.mem_scriptH
  rw [(Sec20.isSylowOf_three_inf_of_mem_scriptH h1812 h184 hH.toSec18Std hH.mem_scriptH).card_eq,
    Sec20.factorization_three_of_nonempty_quotient e]
  norm_num

theorem eq_zpowers_sup_of_sec18H (h1812 : Item181_2) (h184 : Item184_1)
    (hH : Sec18H G A M H c) :
    A = Subgroup.zpowers c ⊔ (A ⊓ inSubgroup perfectResidual H) := by
  set B := A ⊓ inSubgroup perfectResidual H with hB
  have hA := isE27_of_mem_partTwoE hH.mem_partTwoE
  have hcA := (mem_and_commutator_mem_of_sec18H hH).1
  have hcB : c ∉ B := fun h => not_mem_of_sec18H h184 hH h.2
  have hB9 := card_inf_of_sec18H h1812 h184 hH
  set S := Subgroup.zpowers c ⊔ B with hS
  have hSA : S ≤ A := sup_le (Subgroup.zpowers_le.mpr hcA) inf_le_left
  have hBS : B ≤ S := le_sup_right
  have h1 : 9 ∣ Nat.card S := hB9 ▸ Subgroup.card_dvd_of_le hBS
  have h2 : Nat.card S ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA.2]
    exact Subgroup.card_dvd_of_le hSA
  have h3 : Nat.card S ≠ 9 := by
    intro h
    have hBS' : B = S := Subgroup.eq_of_le_of_card_ge hBS (by rw [h, hB9])
    exact hcB (by rw [hBS']; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
  obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
  interval_cases j
  · rw [hjc] at h1
    norm_num at h1
  · rw [hjc] at h1
    norm_num at h1
  · exact absurd (by rw [hjc]; norm_num) h3
  · exact (Subgroup.eq_of_le_of_card_ge hSA (by norm_num [hjc, hA.2])).symm

theorem inf_lc_eq (h1812 : Item181_2) (h184 : Item184_1) (hH : Sec18H G A M H c) :
    A ⊓ lc H c = A ⊓ inSubgroup perfectResidual H := by
  set B := A ⊓ inSubgroup perfectResidual H with hB
  have hA := isE27_of_mem_partTwoE hH.mem_partTwoE
  have hcA := (mem_and_commutator_mem_of_sec18H hH).1
  have hB9 := card_inf_of_sec18H h1812 h184 hH
  have hL₀Lc : inSubgroup perfectResidual (inSubgroup perfectResidual H ⊓
      Subgroup.centralizer ({c} : Set G)) ≤ lc H c :=
    inSubgroup_perfectResidual_mono le_sup_left
  have hBle : B ≤ A ⊓ lc H c :=
    le_inf inf_le_left ((le_sup_and_inf_le_of_sec18H hH).2.trans hL₀Lc)
  refine (Subgroup.eq_of_le_of_card_ge hBle ?_).symm
  have hdvd : Nat.card (A ⊓ lc H c : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA.2]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h9 : 9 ∣ Nat.card (A ⊓ lc H c : Subgroup G) := hB9 ▸ Subgroup.card_dvd_of_le hBle
  have hne : Nat.card (A ⊓ lc H c : Subgroup G) ≠ 27 := by
    intro h27
    have hAeq : A ⊓ lc H c = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hA.2])
    exact not_mem_lc h184 hH (by rw [← hAeq] at hcA; exact hcA.2)
  obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rw [hB9]
  interval_cases j
  · rw [hjc] at h9
    norm_num at h9
  · rw [hjc] at h9
    norm_num at h9
  · rw [hjc]
    norm_num
  · exact absurd (by rw [hjc]; norm_num) hne

theorem planeQ8_of_sec18H (h1812 : Item181_2) (h184 : Item184_1) (hH : Sec18H G A M H c) :
    PlaneQ8 A (A ⊓ inSubgroup perfectResidual H) (lc H c ⊓ Subgroup.normalizer (A : Set G)) c := by
  set L := inSubgroup perfectResidual H with hL
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set L₀ := inSubgroup perfectResidual (L ⊓ C) with hL₀
  set B := A ⊓ L with hB
  set K := lc H c ⊓ Subgroup.normalizer (A : Set G) with hK
  have hA := isE27_of_mem_partTwoE hH.mem_partTwoE
  have hcA := (mem_and_commutator_mem_of_sec18H hH).1
  have hcB : c ∉ B := fun h => not_mem_of_sec18H h184 hH h.2
  have hB9 := card_inf_of_sec18H h1812 h184 hH
  have hAeq := eq_zpowers_sup_of_sec18H h1812 h184 hH
  have hBLc := inf_lc_eq h1812 h184 hH
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := Late.isElemAbelian_of_le hA.1 inf_le_left
  have hB3 : IsPGroup 3 B := hA.isPGroup.to_le inf_le_left
  have hLcC : lc H c ≤ C :=
    (Subgroup.map_subtype_le _).trans (sup_le inf_le_right (CFSG.LieType.BorelTits.pCoreOf_le 2 C))
  have hKc : ∀ k ∈ K, k * c = c * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLcC hk.1)
  have hKA : K ≤ Subgroup.normalizer (A : Set G) := inf_le_right
  have hKB : K ≤ Subgroup.normalizer (B : Set G) := by
    have h := Late.le_normalizer_inf (A := K) (X := A) (Y := lc H c) hKA
      (inf_le_left.trans Subgroup.le_normalizer)
    rwa [hBLc] at h
  obtain ⟨e₀⟩ := nonempty_quotient_perfectResidual_inf_centralizer h184 hH
  obtain ⟨f₀, hf₀⟩ := exists_quaternion_autIn e₀ (le_sup_and_inf_le_of_sec18H hH).2 hB3 hB9
  have hL₀Lc : L₀ ≤ lc H c := inSubgroup_perfectResidual_mono le_sup_left
  have hle : Sec4.autIn L₀ B ≤ Sec4.autIn K B := by
    intro σ hσ
    obtain ⟨x, hxN, hxL₀, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    have hxc : x * c = c * x :=
      Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.map_subtype_le _ hxL₀).2)
    have hxA : x ∈ Subgroup.normalizer (A : Set G) := by
      rw [hAeq]
      exact mem_normalizer_zpowers_sup hxc hxN
    exact Sec4.mem_autIn_iff.mpr ⟨x, hxN, ⟨hL₀Lc hxL₀, hxA⟩, rfl⟩
  set fB := (Subgroup.inclusion hle).comp f₀ with hfB
  have hfBi : Function.Injective fB := (Subgroup.inclusion_injective hle).comp hf₀
  have hρ4 : ((fB (QuaternionGroup.a 1) : Sec4.autIn K B) : MulAut B) ^ 4 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow,
      show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 by decide, map_one, Subgroup.coe_one]
  have hρ2 : ((fB (QuaternionGroup.a 1) : Sec4.autIn K B) : MulAut B) ^ 2 ≠ 1 := by
    intro h
    have h' : fB (QuaternionGroup.a 1 ^ 2) = fB 1 := by
      rw [map_pow, map_one]
      exact Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])
    exact (show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1 by decide) (hfBi h')
  have hirr : Sec21.IsIrreducibleOn (Sec4.autIn K B) :=
    Sec13.isIrreducibleOn_of_order_four hBe hB9 (fB _).2 hρ4 hρ2
  have hAK : A ⊓ K = B := by
    rw [hK, ← inf_assoc, hBLc]
    exact inf_eq_left.mpr (inf_le_left.trans Subgroup.le_normalizer)
  have hcK : c ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => hKc k hk
  have hAeq' : A = A ⊓ K ⊔ Subgroup.zpowers c := by
    rw [hAK, sup_comm]
    exact hAeq
  obtain ⟨φ⟩ : Nonempty (Sec4.autIn K A ≃* Sec4.autIn K B) := by
    have h := Sec4.Res423Four.nonempty_autIn_inf_equiv hcK hAeq'
    rwa [hAK] at h
  exact ⟨hA.1, hA.2, hcA, hAeq, hcB, hB9, hKc, hirr, hKA, hKB,
    ⟨φ.symm.toMonoidHom.comp fB, φ.symm.injective.comp hfBi⟩⟩

theorem wStar_structure_of_sec18H
    (h1812 : Item181_2) (h184 : Item184_1) (h1842 : Item184_2) (hH : Sec18H G A M H c) :
    Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer ((A ⊓ inSubgroup perfectResidual H : Subgroup G) : Set G) ∧
      (Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∨
        (Sec13.oThreeWStar A = Sec13.transvAxis A (A ⊓ inSubgroup perfectResidual H) ∧
          Nat.card (Sec13.oThreeWStar A) = 9 ∧
          Sec13.wStar A = Sec13.oThreeWStar A ⊔
            Sec4.autIn (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A ∧
          Sec13.orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c) =
            Sec13.pointsOff A (A ⊓ inSubgroup perfectResidual H) ∧
          (Sec13.orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c)).ncard = 9)) :=
  wStar_structure (planeQ8_of_sec18H h1812 h184 hH) (starNormalized_of_sec18H h1842 hH)

end Certified

end Notation

end CFSG.RankThree.PartTwo.Sec18
