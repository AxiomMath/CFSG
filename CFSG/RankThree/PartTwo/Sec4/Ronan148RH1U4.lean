module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1D4
public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4Inner
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofE27
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SU
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1Gen
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsU4Odd

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Criteria2

variable {X Y : Type} [Group X] [Group Y]

theorem OnFree.of_map (f : X →* Y) (hf : Function.Injective f) {C : Subgroup X} {y : X}
    (h : OnFree (C.map f) (f y)) : OnFree C y := by
  intro K hKC hKq hKs hyK hext
  have eK : K ≃* K.map f := K.equivMapOfInjective f hf
  refine h (K.map f) (Subgroup.map_mono hKC) (CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hKq) ?_
    ⟨y, hyK, rfl⟩ (Ronan148S.isExtOf_congr (quotPCoreTwoCongr eK) hext)
  let eC : C ≃* C.map f := C.equivMapOfInjective f hf
  have heC : ∀ x : C, ((eC x : C.map f) : Y) = f x := fun x =>
    Subgroup.coe_equivMapOfInjective_apply C f hf x
  have hsurj : Function.Surjective (eC : C →* C.map f) := eC.surjective
  have hmap := hKs.map hsurj
  have heq : (K.subgroupOf C).map (eC : C →* C.map f) = (K.map f).subgroupOf (C.map f) := by
    ext ⟨z, hz⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_coe]
    constructor
    · rintro ⟨x, hxK, hxy⟩
      refine ⟨x, hxK, ?_⟩
      rw [← heC x, hxy]
    · rintro ⟨x, hxK, rfl⟩
      refine ⟨⟨x, hKC hxK⟩, hxK, Subtype.ext ?_⟩
      rw [heC]
  rwa [heq] at hmap

theorem exists_ne_comm_of_isQuasisimple {K : Type*} [Group K] (hK : IsQuasisimple K) :
    ∃ a b : K, a * b ≠ b * a := by
  haveI : Group.IsPerfect K := hK.1
  haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK
  by_contra hcon
  push Not at hcon
  haveI : IsMulCommutative K := ⟨⟨hcon⟩⟩
  exact Group.IsPerfect.not_isMulCommutative K inferInstance

theorem ne_bot_of_isQuasisimple {K : Subgroup X} (hK : IsQuasisimple K) : K ≠ ⊥ := by
  haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK
  intro h
  have : Subsingleton K := by rw [h]; infer_instance
  exact not_subsingleton K inferInstance

variable [Finite X]

theorem good427_onFree_of_simple_qs {C : Subgroup X} {y : X} (hy1 : y ≠ 1)
    (hyC : ∀ c ∈ C, c * y = y * c)
    (hsimp : ∀ K : Subgroup X, K ≤ C → IsQuasisimple K → (K.subgroupOf C).IsSubnormal →
      IsSimpleGroup K ∧ Nat.card K ≠ 60) : Good427 C ∧ OnFree C y := by
  refine ⟨fun K hKC hKq hKs hA5 => ?_, fun K hKC hKq hKs hyK _ => ?_⟩
  · obtain ⟨hs, h60⟩ := hsimp K hKC hKq hKs
    haveI := hs
    exact not_isA5Type_of_simple (exists_ne_comm_of_isQuasisimple hKq) h60 hA5
  · obtain ⟨hs, -⟩ := hsimp K hKC hKq hKs
    have hZ : Subgroup.center K = ⊥ :=
      RonanK429.center_eq_bot_of_isSimpleGroup hs (exists_ne_comm_of_isQuasisimple hKq)
    have hc : (⟨y, hyK⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hyC g (hKC g.2))
    rw [hZ, Subgroup.mem_bot] at hc
    exact hy1 (congrArg Subtype.val hc)

theorem good427_onFree_of_perfect_le_simple {C S : Subgroup X} {y : X} (hy1 : y ≠ 1)
    (hyC : ∀ c ∈ C, c * y = y * c) [hS : IsSimpleGroup S] (h60 : Nat.card S ≠ 60) (hSC : S ≤ C)
    (hle : ∀ K : Subgroup X, K ≤ C → Group.IsPerfect K → K ≤ S) : Good427 C ∧ OnFree C y := by
  refine good427_onFree_of_simple_qs hy1 hyC fun K hKC hKq hKs => ?_
  have hKS := hle K hKC hKq.1
  have hKeq : K = S := RonanK429Lie.eq_of_subnormal_of_le_simple hKS hSC hKs hS
    (ne_bot_of_isQuasisimple hKq)
  subst hKeq
  exact ⟨hS, h60⟩

theorem good427_onFree_of_perfect_le_qs {C R : Subgroup X} {y : X}
    (hRC : R ≤ C) (hle : ∀ K : Subgroup X, K ≤ C → Group.IsPerfect K → K ≤ R)
    (hRq : IsQuasisimple R) (hodd : Odd (Nat.card (Subgroup.center R)))
    (h60 : Nat.card R ≠ 60) (hON : Nat.card R ≠ 460815505920 * 3) :
    Good427 C ∧ OnFree C y := by
  have hqs : QSList R R := eq_of_quasisimple_subnormal le_rfl
    (fun g hg s hs => mul_mem (mul_mem hg hs) (inv_mem hg)) hRq fun u _ v hv huT _ => huT v hv
  have key : ∀ K : Subgroup X, K ≤ C → IsQuasisimple K → (K.subgroupOf C).IsSubnormal →
      K = R := by
    intro K hKC hKq hKs
    have hKR := hle K hKC hKq.1
    exact hqs K hKR hKq (isSubnormal_subgroupOf_of_le hRC hKR hKs)
  have hP : CFSG.pCore 2 R = ⊥ := pCore_two_eq_bot_of_odd_center' hRq hodd
  have hcard : Nat.card R = Nat.card (R ⧸ CFSG.pCore 2 R) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 R)
    have h2 : Nat.card (CFSG.pCore 2 R) = 1 := by rw [hP, Subgroup.card_bot]
    rwa [h2, mul_one] at h1
  refine ⟨fun K hKC hKq hKs hA5 => ?_, fun K hKC hKq hKs _ hext => ?_⟩
  · have hKR := key K hKC hKq hKs
    subst hKR
    exact h60 (hcard.trans hA5.card)
  · have hKR := key K hKC hKq hKs
    subst hKR
    obtain ⟨N, _, ⟨eN⟩, ⟨eQ⟩⟩ := hext
    apply hON
    rw [hcard, Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr eQ.toEquiv,
      CFSG.Sporadic.ON.card_ON, Nat.card_congr eN.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]

theorem good427_onFree_of_perfect_eq_bot {C : Subgroup X} {y : X}
    (hle : ∀ K : Subgroup X, K ≤ C → Group.IsPerfect K → K = ⊥) : Good427 C ∧ OnFree C y :=
  ⟨fun K hKC hKq _ _ => ne_bot_of_isQuasisimple hKq (hle K hKC hKq.1),
    fun K hKC hKq _ _ _ => ne_bot_of_isQuasisimple hKq (hle K hKC hKq.1)⟩

theorem eq_bot_of_perfect_le_two_three {K B : Subgroup X} (hKB : K ≤ B) (hp : Group.IsPerfect K)
    {a b : ℕ} (hB : Nat.card B ∣ 2 ^ a * 3 ^ b) : K = ⊥ := by
  haveI := hp
  have hd : Nat.card K ∣ 2 ^ a * 3 ^ b := (Subgroup.card_dvd_of_le hKB).trans hB
  have hpf := RonanK429H.primeFactors_card_le_two_of_dvd Nat.prime_two Nat.prime_three hd
  haveI := RonanK429H.subsingleton_of_isPerfect_of_card_primeFactors hpf
  exact Subgroup.eq_bot_of_subsingleton K

end Criteria2

namespace U4

section Blocks

open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof (uS)
open CFSG.RankThree.PartOne.KFU (diagU diagU_val apply_eq_zero_of_commute_diagU)
open CFSG.RankThree.PartTwo.Sec21.Item2130Res4Proof (blk3SU blk3SUEquiv mem_blk3SU_of
  blk3SU_le_uS blk3SU_le_centralizer pattern_of_commute statedSU_eq_uS)
open CFSG.RankThree.PartTwo.Sec21.U4OddLines (blk2 blkGL2 coe_blkGL2 blkSU2 dvecD0
  blkSU2_le_centralizer nonempty_blkSU2_mulEquiv mem_blkSU2_of)
open CFSG.RankThree.PartTwo.Sec4.Item419Res3 (blk2L blkGL2L coe_blkGL2L blkSU2L dvecC centC
  blkSU2_le_centC blkSU2L_le_centC commutator_centC_le nonempty_blkSU2L_mulEquiv sl2_block_facts)

variable {L : Type} [Field L]

theorem su3_facts
    {f : ℕ} (h₀ : UnitaryFieldData 2 f L) (hf : 2 ≤ f) :
    IsQuasisimple (CFSG.Open.StatedSU 3 (2 ^ f) L) ∧
      Odd (Nat.card (Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ f) L))) ∧
      (Nat.card (CFSG.Open.StatedSU 3 (2 ^ f) L) : ℤ) =
        ((2 ^ f : ℕ) : ℤ) ^ 3 * ((((2 ^ f : ℕ) : ℤ) ^ 2 - 1) * (((2 ^ f : ℕ) : ℤ) ^ 3 + 1)) := by
  haveI := h₀.finite
  have hL : Nat.card L = (2 ^ f) ^ 2 := by rw [h₀.card, ← pow_mul, mul_comm]
  have hq : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro hq
    have h2 : 2 ^ f = 2 := (Prod.mk.inj hq).2
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨hSU, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hL le_rfl hq
  have hZcard : Nat.card (Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ f) L)) =
      Nat.gcd 3 (2 ^ f + 1) := by
    rw [hZ]
    exact (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hL (by norm_num)).2.2
  refine ⟨hSU, ?_, ?_⟩
  · rw [hZcard]
    exact (by decide : Odd 3).of_dvd_nat (Nat.gcd_dvd_left 3 _)
  · have hc := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int h₀ (n := 3) (by norm_num)
    have hp : ∏ i ∈ Finset.Icc 2 3, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
        (((2 ^ f : ℕ) : ℤ) ^ 2 - 1) * (((2 ^ f : ℕ) : ℤ) ^ 3 + 1) := by
      rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
      norm_num
    rw [hp] at hc
    exact hc

theorem card_su3_two (h₀ : UnitaryFieldData 2 1 L) :
    Nat.card (CFSG.Open.StatedSU 3 (2 ^ 1) L) = 2 ^ 3 * 3 ^ 3 := by
  have hc := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int h₀ (n := 3) (by norm_num)
  rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)] at hc
  norm_num at hc
  exact_mod_cast hc

theorem u4_caseA
    [Finite L] {n : ℕ}
    (h : UnitaryFieldData 2 n L) (hodd : Odd n) {ω : Lˣ} (hω1 : ω ≠ 1) :
    Good427 (unitarySU 2 n L 4 ⊓ Subgroup.centralizer {diagU ![ω, ω, ω, 1]}) ∧
      OnFree (unitarySU 2 n L 4 ⊓ Subgroup.centralizer {diagU ![ω, ω, ω, 1]})
        (diagU ![ω, ω, ω, 1]) := by
  have hωL1 : (ω : L) ≠ 1 := fun e => hω1 (Units.ext e)
  set D : GL (Fin 4) L := diagU ![ω, ω, ω, 1] with hDdef
  have hDm : (D : Matrix (Fin 4) (Fin 4) L) =
      Matrix.diagonal ![(ω : L), (ω : L), (ω : L), 1] := by
    rw [hDdef, RonanEps.u4OddEps_coe_diagU]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hBC : blk3SU h ≤ unitarySU 2 n L 4 ⊓ Subgroup.centralizer {D} :=
    le_inf (fun g hg => RonanEps.u4OddEps_mem_unitarySU_of_uS h (blk3SU_le_uS h hg))
      (blk3SU_le_centralizer h hDm)
  have hle : ∀ K : Subgroup (GL (Fin 4) L), K ≤ unitarySU 2 n L 4 ⊓ Subgroup.centralizer {D} →
      Group.IsPerfect K → K ≤ blk3SU h := by
    intro K hKC hKp k hk
    have hKp' : ⁅K, K⁆ = K := Subgroup.commutator_eq_self
    have hC : K ≤ Subgroup.centralizer {D} := fun k hk => (hKC hk).2
    have hkC := RonanEps.u4OddEps_mul_eq_of_mem_centralizer (hC hk)
    rw [hDm] at hkC
    exact mem_blk3SU_of h (RonanEps.u4OddEps_mem_uS_of_unitarySU h (hKC hk).1)
      (pattern_of_commute hωL1 hkC) (RonanEps.u4OddEps_entry33_eq_one hω1 hC hKp' hk)
  let E3 : blk3SU h ≃* CFSG.Open.StatedSU 3 (2 ^ n) L :=
    (blk3SUEquiv h).trans (MulEquiv.subgroupCongr (statedSU_eq_uS h 3)).symm
  rcases Nat.eq_or_lt_of_le (show 1 ≤ n from hodd.pos) with hn1 | hn3
  ·
    subst hn1
    refine good427_onFree_of_perfect_eq_bot fun K hKC hKp =>
      eq_bot_of_perfect_le_two_three (hle K hKC hKp) hKp (a := 3) (b := 3) ?_
    rw [Nat.card_congr E3.toEquiv, card_su3_two h]
  · have hn3' : 3 ≤ n := by
      obtain ⟨j, hj⟩ := hodd
      omega
    obtain ⟨hq, hoddZ, hcard⟩ := su3_facts h (by omega)
    have hcardB : (Nat.card (blk3SU h) : ℤ) =
        ((2 ^ n : ℕ) : ℤ) ^ 3 * ((((2 ^ n : ℕ) : ℤ) ^ 2 - 1) * (((2 ^ n : ℕ) : ℤ) ^ 3 + 1)) := by
      rw [Nat.card_congr E3.toEquiv]
      exact hcard
    have hdvd : (2 ^ n) ^ 3 ∣ Nat.card (blk3SU h) := by
      have : ((2 ^ n : ℕ) : ℤ) ^ 3 ∣ (Nat.card (blk3SU h) : ℤ) := by
        rw [hcardB]
        exact dvd_mul_right _ _
      exact_mod_cast this
    have h9 : 2 ^ 9 ∣ Nat.card (blk3SU h) :=
      (by rw [← pow_mul]; exact pow_dvd_pow 2 (by omega) : 2 ^ 9 ∣ (2 ^ n) ^ 3).trans hdvd
    refine good427_onFree_of_perfect_le_qs hBC hle
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv E3.symm hq) ?_ ?_ ?_
    · rwa [Nat.card_congr (Subgroup.centerCongr E3).toEquiv]
    · intro h60
      rw [h60] at h9
      norm_num at h9
    · intro hON
      rcases (show n = 3 ∨ 5 ≤ n by obtain ⟨j, hj⟩ := hodd; omega) with rfl | hn5
      · rw [hON] at hcardB
        norm_num at hcardB
      · have h15 : 2 ^ 15 ∣ Nat.card (blk3SU h) :=
          (by rw [← pow_mul]; exact pow_dvd_pow 2 (by omega) : 2 ^ 15 ∣ (2 ^ n) ^ 3).trans hdvd
        rw [hON] at h15
        norm_num at h15

theorem le_blkSU2_of_perfect {n : ℕ} (h : UnitaryFieldData 2 n L) {ω : Lˣ} (hω1 : ω ≠ 1)
    (hω2 : ω ≠ ω⁻¹) {K₂ : Subgroup (GL (Fin 4) L)}
    (hKC : K₂ ≤ unitarySU 2 n L 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)})
    (hKp : Group.IsPerfect K₂) : K₂ ≤ blkSU2 n L := by
  have hKp' : ⁅K₂, K₂⁆ = K₂ := Subgroup.commutator_eq_self
  have hC : K₂ ≤ Subgroup.centralizer {diagU (dvecD0 ω)} := fun k hk => (hKC hk).2
  have hU : K₂ ≤ unitarySU 2 n L 4 := fun k hk => (hKC hk).1
  have hω1' : ω⁻¹ ≠ 1 := fun e => hω1 (inv_eq_one.mp e)
  have hl2 : ∀ j : Fin 4, j ≠ 2 → dvecD0 ω 2 ≠ dvecD0 ω j := by
    intro j hj
    fin_cases j
    · simpa [dvecD0] using hω1
    · simpa [dvecD0] using hω1
    · exact absurd rfl hj
    · simpa [dvecD0] using hω2
  have hl3 : ∀ j : Fin 4, j ≠ 3 → dvecD0 ω 3 ≠ dvecD0 ω j := by
    intro j hj
    fin_cases j
    · simpa [dvecD0] using Ne.symm hω1'
    · simpa [dvecD0] using Ne.symm hω1'
    · simpa [dvecD0] using hω2.symm
    · exact absurd rfl hj
  have hK22 : ∀ k ∈ K₂, (k : Matrix (Fin 4) (Fin 4) L) 2 2 = 1 := fun k hk =>
    entry_eq_one_of_perfect hl2 hC hKp' hk
  have hK33 : ∀ k ∈ K₂, (k : Matrix (Fin 4) (Fin 4) L) 3 3 = 1 := fun k hk =>
    entry_eq_one_of_perfect hl3 hC hKp' hk
  have e01 : dvecD0 ω 0 ≠ dvecD0 ω 2 := by simpa [dvecD0] using Ne.symm hω1
  have e03 : dvecD0 ω 0 ≠ dvecD0 ω 3 := by simpa [dvecD0] using Ne.symm hω1'
  have e12 : dvecD0 ω 1 ≠ dvecD0 ω 2 := by simpa [dvecD0] using Ne.symm hω1
  have e13 : dvecD0 ω 1 ≠ dvecD0 ω 3 := by simpa [dvecD0] using Ne.symm hω1'
  have e20 : dvecD0 ω 2 ≠ dvecD0 ω 0 := by simpa [dvecD0] using hω1
  have e21 : dvecD0 ω 2 ≠ dvecD0 ω 1 := by simpa [dvecD0] using hω1
  have e23 : dvecD0 ω 2 ≠ dvecD0 ω 3 := by simpa [dvecD0] using hω2
  have e30 : dvecD0 ω 3 ≠ dvecD0 ω 0 := by simpa [dvecD0] using hω1'
  have e31 : dvecD0 ω 3 ≠ dvecD0 ω 1 := by simpa [dvecD0] using hω1'
  have e32 : dvecD0 ω 3 ≠ dvecD0 ω 2 := by simpa [dvecD0] using hω2.symm
  intro k hk
  have hz : ∀ i j : Fin 4, dvecD0 ω i ≠ dvecD0 ω j →
      (k : Matrix (Fin 4) (Fin 4) L) i j = 0 := fun i j hij =>
    apply_eq_zero_of_commute_diagU (Subgroup.mem_centralizer_singleton_iff.mp (hC hk)) hij
  exact mem_blkSU2_of h (hU hk) (hz 0 2 e01) (hz 0 3 e03) (hz 1 2 e12) (hz 1 3 e13)
    (hz 2 0 e20) (hz 2 1 e21) (hz 2 3 e23) (hz 3 0 e30) (hz 3 1 e31) (hz 3 2 e32)
    (hK22 k hk) (hK33 k hk)

theorem diagU_ne_one {d : Fin 4 → Lˣ} {i : Fin 4} (hi : d i ≠ 1) : diagU d ≠ 1 := by
  intro e
  apply hi
  apply Units.ext
  have := congrArg (fun g : GL (Fin 4) L => (g : Matrix (Fin 4) (Fin 4) L) i i) e
  simpa [RonanEps.u4OddEps_coe_diagU] using this

theorem u4_caseB [Finite L] {n : ℕ} (h : UnitaryFieldData 2 n L) (hodd : Odd n) {ω : Lˣ}
    (hω1 : ω ≠ 1) (hω2 : ω ≠ ω⁻¹) :
    Good427 (unitarySU 2 n L 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)}) ∧
      OnFree (unitarySU 2 n L 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)}) (diagU (dvecD0 ω)) := by
  have hle := fun K hKC hKp => le_blkSU2_of_perfect (K₂ := K) h hω1 hω2 hKC hKp
  rcases Nat.eq_or_lt_of_le (show 1 ≤ n from hodd.pos) with hn1 | hn3
  · subst hn1
    have hsol := (sl2_block_facts h (nonempty_blkSU2_mulEquiv h)).2 rfl
    exact good427_onFree_of_perfect_eq_bot fun K hKC hKp =>
      Ronan148L.eq_bot_of_le_solvable (hle K hKC hKp) hsol hKp
  · have hn2 : 2 ≤ n := by omega
    obtain ⟨hq, hcard⟩ := (sl2_block_facts h (nonempty_blkSU2_mulEquiv h)).1 hn2
    have hZ : Subgroup.center (blkSU2 n L) = ⊥ := by
      haveI : CharP h.fixedField 2 :=
        CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq h.card_fixedField
      obtain ⟨φ⟩ := nonempty_blkSU2_mulEquiv h
      exact center_eq_bot_of_mulEquiv φ Sec19.Item19Res2Proof.center_sl2_eq_bot
    haveI : IsSimpleGroup (blkSU2 n L) := RonanEps.isSimpleGroup_of_isQuasisimple_center hq hZ
    refine good427_onFree_of_perfect_le_simple (diagU_ne_one (i := 2) (by simpa [dvecD0] using hω1))
      (fun c hc => Subgroup.mem_centralizer_singleton_iff.mp hc.2) ?_ (blkSU2_le_centralizer h ω)
      hle
    rw [hcard]
    intro h60
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by obtain ⟨j, hj⟩ := hodd; omega)
    have h64 : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
    have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 (by omega)
    omega

theorem not_isQuasisimple_prod {A B : Type*} [Group A] [Group B] (hA : ∃ a a' : A, a * a' ≠ a' * a)
    [Nontrivial B] : ¬ IsQuasisimple (A × B) := by
  intro hq
  set N : Subgroup (A × B) := (⊤ : Subgroup A).prod ⊥ with hN
  have hmem : ∀ x : A × B, x ∈ N ↔ x.2 = 1 := by
    intro x
    rw [hN, Subgroup.mem_prod]
    simp
  have hNn : N.Normal := ⟨fun x hx g => by
    rw [hmem] at hx ⊢
    simp [hx]⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNn with htop | hcen
  · obtain ⟨b, hb⟩ := exists_ne (1 : B)
    have : ((1 : A), b) ∈ N := htop ▸ Subgroup.mem_top _
    exact hb ((hmem _).mp this)
  · obtain ⟨a, a', haa⟩ := hA
    have ha : ((a, 1) : A × B) ∈ Subgroup.center (A × B) := hcen ((hmem _).mpr rfl)
    have h1 := Subgroup.mem_center_iff.mp ha ((a', 1) : A × B)
    apply haa
    have := congrArg Prod.fst h1
    simpa using this.symm

theorem u4_caseC [Finite L] {n : ℕ} (h : UnitaryFieldData 2 n L) (hodd : Odd n) {ω : Lˣ}
    (hω1 : ω ≠ 1) (hω2 : ω ≠ ω⁻¹) :
    Good427 (centC n L ω) ∧ OnFree (centC n L ω) (diagU (dvecC ω)) := by
  haveI : CharP h.fixedField 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq h.card_fixedField
  have hM : blkSU2 n L ⊔ blkSU2L n L ≤ centC n L ω :=
    sup_le (blkSU2_le_centC h ω) (blkSU2L_le_centC h ω)
  have hle : ∀ K : Subgroup (GL (Fin 4) L), K ≤ centC n L ω → Group.IsPerfect K →
      K ≤ blkSU2 n L ⊔ blkSU2L n L := by
    intro K hKC hKp
    have hKp' : ⁅K, K⁆ = K := Subgroup.commutator_eq_self
    calc K = ⁅K, K⁆ := hKp'.symm
      _ ≤ ⁅centC n L ω, centC n L ω⁆ := Subgroup.commutator_mono hKC hKC
      _ ≤ blkSU2 n L ⊔ blkSU2L n L := commutator_centC_le h hω2
  have hcomm : ∀ a ∈ blkSU2 n L, ∀ b ∈ blkSU2L n L, a * b = b * a := by
    intro a ha b hb
    obtain ⟨X, -, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨Y, -, rfl⟩ := Subgroup.mem_map.mp hb
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_blkGL2, coe_blkGL2L]
    exact RonanK429Lie.blk2_mul_blk2L_comm _ _
  have hdisj : Disjoint (blkSU2 n L) (blkSU2L n L) := by
    rw [Subgroup.disjoint_def]
    intro g hg1 hg2
    obtain ⟨X, -, rfl⟩ := Subgroup.mem_map.mp hg1
    obtain ⟨Y, -, hY⟩ := Subgroup.mem_map.mp hg2
    have e := congrArg (fun g : GL (Fin 4) L => (g : Matrix (Fin 4) (Fin 4) L)) hY
    simp only [coe_blkGL2, coe_blkGL2L] at e
    have e00 : (X : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by
      simpa [blk2, blk2L] using (congrFun (congrFun e 0) 0).symm
    have e01 : (X : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
      simpa [blk2, blk2L] using (congrFun (congrFun e 0) 1).symm
    have e10 : (X : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
      simpa [blk2, blk2L] using (congrFun (congrFun e 1) 0).symm
    have e11 : (X : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by
      simpa [blk2, blk2L] using (congrFun (congrFun e 1) 1).symm
    have hX : X = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]
    rw [hX, map_one]
  have hcommΦ : ∀ (a : ↥(blkSU2 n L)) (b : ↥(blkSU2L n L)),
      Commute ((blkSU2 n L).subtype a) ((blkSU2L n L).subtype b) :=
    fun a b => hcomm a a.2 b b.2
  set Φ : ↥(blkSU2 n L) × ↥(blkSU2L n L) →* GL (Fin 4) L :=
    (blkSU2 n L).subtype.noncommCoprod (blkSU2L n L).subtype hcommΦ with hΦ
  have hΦinj : Function.Injective Φ := by
    rw [hΦ, MonoidHom.noncommCoprod_injective]
    refine ⟨Subgroup.subtype_injective _, Subgroup.subtype_injective _, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact hdisj
  have hΦrange : Φ.range = blkSU2 n L ⊔ blkSU2L n L := by
    rw [hΦ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rcases Nat.eq_or_lt_of_le (show 1 ≤ n from hodd.pos) with hn1 | hn3
  ·
    subst hn1
    haveI := (sl2_block_facts h (nonempty_blkSU2_mulEquiv h)).2 rfl
    haveI := (sl2_block_facts h (nonempty_blkSU2L_mulEquiv h)).2 rfl
    have hsol : Group.IsSolvable ↥(blkSU2 1 L ⊔ blkSU2L 1 L) := by
      rw [← hΦrange]
      exact solvable_of_surjective Φ.rangeRestrict_surjective
    exact good427_onFree_of_perfect_eq_bot fun K hKC hKp =>
      Ronan148L.eq_bot_of_le_solvable (hle K hKC hKp) hsol hKp
  · have hn2 : 2 ≤ n := by omega
    obtain ⟨hqN₁, hcardN₁⟩ := (sl2_block_facts h (nonempty_blkSU2_mulEquiv h)).1 hn2
    obtain ⟨hqN₂, hcardN₂⟩ := (sl2_block_facts h (nonempty_blkSU2L_mulEquiv h)).1 hn2
    have hZ₁ : Subgroup.center (blkSU2 n L) = ⊥ := by
      obtain ⟨φ⟩ := nonempty_blkSU2_mulEquiv h
      exact center_eq_bot_of_mulEquiv φ Sec19.Item19Res2Proof.center_sl2_eq_bot
    have hZ₂ : Subgroup.center (blkSU2L n L) = ⊥ := by
      obtain ⟨φ⟩ := nonempty_blkSU2L_mulEquiv h
      exact center_eq_bot_of_mulEquiv φ Sec19.Item19Res2Proof.center_sl2_eq_bot
    haveI hX : IsSimpleGroup (blkSU2 n L) := RonanEps.isSimpleGroup_of_isQuasisimple_center hqN₁ hZ₁
    haveI hY : IsSimpleGroup (blkSU2L n L) :=
      RonanEps.isSimpleGroup_of_isQuasisimple_center hqN₂ hZ₂
    have h60 : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 60 := by
      intro h60
      have h8 : 8 ≤ 2 ^ n := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by obtain ⟨j, hj⟩ := hodd; omega)
      have h64 : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
      have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 (by omega)
      omega
    have hD1 : diagU (dvecC ω) ≠ 1 := diagU_ne_one (i := 0) (by simpa [dvecC] using hω1)
    refine good427_onFree_of_simple_qs hD1
      (fun c hc => Subgroup.mem_centralizer_singleton_iff.mp hc.2) fun K hKC hKq hKs => ?_
    have hKM := hle K hKC hKq.1
    have hs' : (K.subgroupOf (blkSU2 n L ⊔ blkSU2L n L)).IsSubnormal :=
      RonanK429H.isSubnormal_subgroupOf_of_le hM hKM hKs
    have hmapK : (K.comap Φ).map Φ = K := Subgroup.map_comap_eq_self (hΦrange ▸ hKM)
    set H : Subgroup (↥(blkSU2 n L) × ↥(blkSU2L n L)) := K.comap Φ with hH
    have hHs : H.IsSubnormal := by
      have h1 : (K.subgroupOf Φ.range).IsSubnormal := by
        rw [hΦrange]
        exact hs'
      have h2 := Subgroup.IsSubnormal.comap Φ.rangeRestrict h1
      have e : H = (K.subgroupOf Φ.range).comap Φ.rangeRestrict := by
        ext x
        simp [hH, Subgroup.mem_subgroupOf]
      rw [e]
      exact h2
    have hHne : H ≠ ⊥ := by
      intro hb
      apply ne_bot_of_isQuasisimple hKq
      rw [← hmapK, hb, Subgroup.map_bot]
    let eH : ↥H ≃* ↥K :=
      (Subgroup.equivMapOfInjective H Φ hΦinj).trans (MulEquiv.subgroupCongr hmapK)
    rcases RonanEps.goursat_prod hX hY hHs hHne with hTop | hXH | hYH
    ·
      exfalso
      have eK : K ≃* (↥(blkSU2 n L) × ↥(blkSU2L n L)) :=
        eH.symm.trans ((MulEquiv.subgroupCongr hTop).trans Subgroup.topEquiv)
      haveI : Nontrivial (blkSU2L n L) := CFSG.LocalCores.isQuasisimple_nontrivial hqN₂
      exact not_isQuasisimple_prod (exists_ne_comm_of_isQuasisimple hqN₁)
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hKq)
    · obtain ⟨eX⟩ := hXH
      have eK : K ≃* ↥(blkSU2 n L) := eH.symm.trans eX
      exact ⟨eK.isSimpleGroup, by rw [Nat.card_congr eK.toEquiv, hcardN₁]; exact h60⟩
    · obtain ⟨eY⟩ := hYH
      have eK : K ≃* ↥(blkSU2L n L) := eH.symm.trans eY
      exact ⟨eK.isSimpleGroup, by rw [Nat.card_congr eK.toEquiv, hcardN₂]; exact h60⟩

end Blocks

section Main

open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Sec21.U4OddLines (dvecD0)
open CFSG.RankThree.PartTwo.Sec4.Item419Res3 (dvecC)
open CFSG.RankThree.PartOne.KFU (diagU diagU_one torusSU mem_torusSU_iff permGL permGL_conj_diagU
  permGL_mem_unitarySU exists_diag_iso_le_of_iso)

theorem u4Odd_transport {n : ℕ} (hodd : Odd n) {S : Type} [Group S] [Finite S]
    (eS : S ≃* projSU 4 2 n) (x : S) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ (ρ : S →* GL (Fin 4) (GaloisField 2 (2 * n))) (ω : (GaloisField 2 (2 * n))ˣ),
      Function.Injective ρ ∧ ω ^ 3 = 1 ∧ ω ≠ 1 ∧
      (Subgroup.centralizer ({x} : Set S)).map ρ =
        unitarySU 2 n (GaloisField 2 (2 * n)) 4 ⊓ Subgroup.centralizer {ρ x} ∧
      (ρ x = diagU ![ω, ω, ω, 1] ∨ ρ x = diagU (dvecD0 ω) ∨ ρ x = diagU (dvecC ω)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := hodd.pos
  have hxi3 : ∀ i : ℤ, (x ^ i) ^ 3 = 1 := by
    intro i
    calc (x ^ i) ^ 3 = (x ^ i) ^ ((3 : ℕ) : ℤ) := (zpow_natCast _ 3).symm
      _ = x ^ (i * 3) := (_root_.zpow_mul x i 3).symm
      _ = x ^ (3 * i) := congrArg (x ^ ·) (mul_comm i 3)
      _ = (x ^ (3 : ℤ)) ^ i := _root_.zpow_mul x 3 i
      _ = 1 := by
        rw [show x ^ (3 : ℤ) = 1 from (zpow_natCast x 3).trans hx3, _root_.one_zpow]
  set Lf := GaloisField 2 (2 * n) with hLf
  have hU : UnitaryFieldData 2 n Lf :=
    ⟨Nat.prime_two, hn1, GaloisField.card 2 (2 * n) (by omega)⟩
  have := hU.finite
  have h3 : 3 ∣ 2 ^ n + 1 := Res417Six.three_dvd_two_pow_add_one hodd
  have hFexp : ∀ y ∈ Subgroup.zpowers x, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hxi3 i
  have hFcomm : ∀ y ∈ Subgroup.zpowers x, ∀ z ∈ Subgroup.zpowers x, y * z = z * y := by
    intro y hy z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_zpow_self x i j).eq
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU Nat.prime_three h3
    ((Res417Six.unitarySUEquivProjSU hn1).trans eS.symm) (Subgroup.zpowers x) hFexp hFcomm
  have hFT : ∀ y ∈ Subgroup.zpowers x,
      ((ψ.symm y : unitarySU 2 n Lf 4) : GL (Fin 4) Lf) ∈ torusSU 3 4 Lf :=
    fun y hy => hψ _ (by rw [MulEquiv.apply_symm_apply]; exact hy)
  obtain ⟨v, hv3, hvp, hvx⟩ := mem_torusSU_iff.mp (hFT x (Subgroup.mem_zpowers x))
  have hv1 : v ≠ 1 := by
    rintro rfl
    apply hx1
    have h1 : ψ.symm x = 1 := Subtype.ext (by rw [← hvx, diagU_one]; rfl)
    rw [← ψ.apply_symm_apply x, h1, map_one]
  have hdvd : 3 ∣ Nat.card Lf - 1 := by
    rw [hU.card]
    have h4 := Res419Two.three_dvd_two_pow_sq_sub_one n
    rwa [← pow_mul, mul_comm] at h4
  obtain ⟨ζ, hζ⟩ := Res417Six.exists_primitiveRoot_three hdvd
  obtain ⟨π, ω, hω3, hω1, hnf⟩ := Item419Res3.exists_perm_normal_form hζ hv3 hvp hv1
  set P : GL (Fin 4) Lf := permGL π with hP
  have hPU : P ∈ unitarySU 2 n Lf 4 := permGL_mem_unitarySU hU π
  set ρ : S →* GL (Fin 4) Lf := (MulAut.conj P).toMonoidHom.comp
    ((unitarySU 2 n Lf 4).subtype.comp ψ.symm.toMonoidHom) with hρ
  have hρapp : ∀ y, ρ y = P * ((ψ.symm y : unitarySU 2 n Lf 4) : GL (Fin 4) Lf) * P⁻¹ :=
    fun y => rfl
  have hρinj : Function.Injective ρ := by
    intro y z h'
    rw [hρapp, hρapp] at h'
    exact ψ.symm.injective (Subtype.ext (mul_left_cancel (mul_right_cancel h')))
  have hρU : ∀ y, ρ y ∈ unitarySU 2 n Lf 4 := fun y =>
    mul_mem (mul_mem hPU (ψ.symm y).2) (inv_mem hPU)
  have hρx : ρ x = diagU (v ∘ π.symm) := by
    rw [hρapp, ← hvx]
    exact permGL_conj_diagU π v
  have hρsurj : ∀ g ∈ unitarySU 2 n Lf 4, ∃ y : S, ρ y = g := by
    intro g hg
    refine ⟨ψ ⟨P⁻¹ * g * P, mul_mem (mul_mem (inv_mem hPU) hg) hPU⟩, ?_⟩
    rw [hρapp, MulEquiv.symm_apply_apply]
    group
  have hmapC : (Subgroup.centralizer ({x} : Set S)).map ρ =
      unitarySU 2 n Lf 4 ⊓ Subgroup.centralizer {ρ x} := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hxy : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hy
      refine ⟨hρU y, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← map_mul, ← map_mul, hxy]
    · rintro ⟨hgU, hgC⟩
      obtain ⟨y, rfl⟩ := hρsurj _ hgU
      have hgC' := Subgroup.mem_centralizer_singleton_iff.mp hgC
      rw [← map_mul, ← map_mul] at hgC'
      exact ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr (hρinj hgC'), rfl⟩
  refine ⟨ρ, ω, hρinj, hω3, hω1, hmapC, ?_⟩
  rcases hnf with hA | hB | hC
  · exact Or.inl (by rw [hρx, hA])
  · exact Or.inr (Or.inl (by rw [hρx, hB]))
  · exact Or.inr (Or.inr (by rw [hρx, hC]))


theorem good427_onFree_inner_odd {n : ℕ} (hodd : Odd n) {S : Type} [Group S] [Finite S]
    (eS : S ≃* projSU 4 2 n) {x : S} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Good427 (Subgroup.centralizer ({x} : Set S)) ∧
      OnFree (Subgroup.centralizer ({x} : Set S)) x := by
  obtain ⟨ρ, ω, hρinj, hω3, hω1, hmap, hnf⟩ := u4Odd_transport hodd eS x hx3 hx1
  have hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
    ⟨Nat.prime_two, hodd.pos, GaloisField.card 2 (2 * n) (by have := hodd.pos; omega)⟩
  haveI := hU.finite
  have hω2 : ω ≠ ω⁻¹ := by
    intro hh
    apply hω1
    have h2' : ω ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [hh]; exact mul_inv_cancel ω
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
      _ = 1 := by rw [hω3, h2', inv_one, one_mul]
  suffices h : Good427 (unitarySU 2 n (GaloisField 2 (2 * n)) 4 ⊓ Subgroup.centralizer {ρ x}) ∧
      OnFree (unitarySU 2 n (GaloisField 2 (2 * n)) 4 ⊓ Subgroup.centralizer {ρ x}) (ρ x) by
    rw [← hmap] at h
    exact ⟨Good427.of_map ρ hρinj h.1, OnFree.of_map ρ hρinj h.2⟩
  rcases hnf with hA | hB | hC
  · rw [hA]
    exact u4_caseA hU hodd hω1
  · rw [hB]
    exact u4_caseB hU hodd hω1 hω2
  · rw [hC]
    exact u4_caseC hU hodd hω1 hω2

theorem good427_onFree_inner_even {n : ℕ} (hev : Even n) (hn4 : 4 ≤ n) {S : Type} [Group S]
    [Finite S] (eS : S ≃* projSU 4 2 n) {x : S} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Good427 (Subgroup.centralizer ({x} : Set S)) ∧
      OnFree (Subgroup.centralizer ({x} : Set S)) x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hℓ : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxo]
  have hcz : (⊤ : Subgroup S) ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup S) :
      Set S) = Subgroup.centralizer ({x} : Set S) := by
    rw [top_inf_eq]
    ext y
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, SetLike.mem_coe]
    constructor
    · intro h
      exact h x (Subgroup.mem_zpowers x)
    · intro h z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (Commute.zpow_left (show Commute x y from h) k).eq
  have hres := Sec21.ks222U4Even S ⊤ (Subgroup.zpowers x) n (by omega) hev
    ⟨Subgroup.topEquiv.trans eS⟩ le_top hℓ
  rw [hcz] at hres
  set N := inSubgroup perfectResidual (Subgroup.centralizer ({x} : Set S)) with hN
  have hNC : N ≤ Subgroup.centralizer ({x} : Set S) := Subgroup.map_subtype_le _
  have hle : ∀ K : Subgroup S, K ≤ Subgroup.centralizer ({x} : Set S) → Group.IsPerfect K →
      K ≤ N := fun K hKC hKp => KFacts.le_inSubgroup_perfectResidual hKp hKC
  have key : ∀ m : ℕ, 4 ≤ m → Nonempty (N ≃* projSL 2 (GaloisField 2 m)) →
      Good427 (Subgroup.centralizer ({x} : Set S)) ∧
        OnFree (Subgroup.centralizer ({x} : Set S)) x := by
    intro m hm ⟨ι⟩
    have hFm : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
    obtain ⟨ι₂⟩ := KFacts.nonempty_sl2_mulEquiv_projSL hFm
    have h16 : 16 ≤ Nat.card (GaloisField 2 m) := by
      rw [hFm]
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    obtain ⟨hs, -, hcard⟩ := sl2_char_two_data (by omega) (ι₂.trans ι.symm)
    haveI := hs
    refine good427_onFree_of_perfect_le_simple hx1
      (fun c hc => Subgroup.mem_centralizer_singleton_iff.mp hc) ?_ hNC hle
    rw [hcard]
    intro h60
    have h256 : 256 ≤ Nat.card (GaloisField 2 m) ^ 2 := by nlinarith
    have : 16 * 255 ≤ Nat.card (GaloisField 2 m) * (Nat.card (GaloisField 2 m) ^ 2 - 1) :=
      Nat.mul_le_mul h16 (by omega)
    omega
  rcases hres with h | h
  · exact key n hn4 h
  · exact key (2 * n) (by omega) h

theorem finite_projSU_four {n : ℕ} (hn : 1 ≤ n) : Finite (projSU 4 2 n) :=
  Finite.of_equiv _ (Res417Six.unitarySUEquivProjSU hn).toEquiv

theorem good427_onFree_inner {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≠ 2) {S : Type} [Group S] [Finite S]
    (eS : S ≃* projSU 4 2 n) {x : S} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Good427 (Subgroup.centralizer ({x} : Set S)) ∧
      OnFree (Subgroup.centralizer ({x} : Set S)) x := by
  rcases Nat.even_or_odd n with hev | hodd
  · exact good427_onFree_inner_even hev (by obtain ⟨k, hk⟩ := hev; omega) eS hx3 hx1
  · exact good427_onFree_inner_odd hodd eS hx3 hx1

theorem card_unitarySU_four_ne_sixty {k : ℕ} {F : Type} [Field F] (h₀ : UnitaryFieldData 2 k F) :
    Nat.card (unitarySU 2 k F 4) ≠ 60 := by
  rw [Item419Res3.card_unitarySU_four h₀]
  intro h
  have h64 : 2 ^ 6 ∣ (2 ^ k) ^ 6 :=
    pow_dvd_pow_of_dvd (dvd_pow_self 2 (by have := h₀.one_le; omega)) 6
  have : 2 ^ 6 ∣ 60 := h ▸ h64.mul_right _
  norm_num at this


theorem noCfgS427_su4 {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≠ 2) : NoCfgS427 (projSU 4 2 n) := by
  haveI := finite_projSU_four hn1
  intro α hα3 h1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf α = 3 := orderOf_eq_prime hα3 h1
  have hZ : Subgroup.center (projSU 4 2 n) = ⊥ := Sec4.RonanK432.center_projSU_four_two_eq_bot hn1
  by_cases hin : KFacts.IsInnerAut α
  · obtain ⟨x, rfl, hx3, hx1⟩ := RonanKChevTwo.exists_conj_of_isInnerAut
      (RonanKChevTwo.conj_injective_of_center_eq_bot hZ) hord hin
    rw [autFix_conj]
    exact (good427_onFree_inner hn1 hn2 (MulEquiv.refl _) hx3 hx1).1
  · obtain ⟨k, -, -, F, _, h₀, ⟨eα⟩⟩ := exists_autFix_mulEquiv_unitarySU_four hn1 hα3 hin
    haveI := RonanEps.isSimpleGroup_unitarySU_four' h₀
    haveI : IsSimpleGroup (Sec4.autFix α) := eα.isSimpleGroup
    have h60 : Nat.card (Sec4.autFix α) ≠ 60 := by
      rw [Nat.card_congr eα.toEquiv]
      exact card_unitarySU_four_ne_sixty h₀
    have h4 : 4 ∣ Nat.card (Sec4.autFix α) := by
      rw [Nat.card_congr eα.toEquiv, Item419Res3.card_unitarySU_four h₀]
      refine Dvd.dvd.mul_right ?_ _
      exact (by norm_num : 4 ∣ 2 ^ 6).trans
        (pow_dvd_pow_of_dvd (dvd_pow_self 2 (by have := h₀.one_le; omega)) 6)
    exact good427_of_le_simple le_rfl (exists_ne_comm_of_simple h4) h60 fun _ hKC _ => hKC

theorem center_eq_bot_su4 {n : ℕ} (hn : 1 ≤ n) {L : Type} [Group L] [Finite L]
    (hL : IsQuasisimple L) (hZ3 : IsPGroup 3 (Subgroup.center L))
    (e : L ⧸ Subgroup.center L ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU 4 (2 ^ n) (GaloisField 2 (2 * n)))) :
    Subgroup.center L = ⊥ := by
  haveI : Group.IsPerfect L := hL.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (Subgroup.center L)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
    rw [hk]
    exact Odd.pow (by decide)
  have hK : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 := by
    rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul, mul_comm]
  obtain ⟨φ, -, -, hmap⟩ := Sec19.Census194.RonanC194.evenSU_perfect_odd_cover_map (n := 4) hK
    (by norm_num) (by decide) hodd e
  rw [CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSU_four_eq_bot
    (K := GaloisField 2 (2 * n)) (2 ^ n), Subgroup.map_bot] at hmap
  exact hmap.symm

end Main

end U4

open U4

section Rows


theorem rowOf427_su4
    : ∀ n : ℕ, 1 ≤ n → n ≠ 2 → RowOf427 (projSU 4 2 n) := by
  intro n hn hn2 S _ _ _ _ ⟨eSX⟩
  refine row427_of_noCfg_on ?_ ?_ ?_
  · intro L _ _ _ hL hZ3 ⟨e'⟩
    exact center_eq_bot_su4 hn hL hZ3
      ((e'.trans eSX).trans (CFSG.PGLModel.projSUEquivStatedProj 4 2 n))
  · intro S' _ _ ⟨e'⟩
    exact NoCfgS427.of_mulEquiv (e'.trans eSX) (noCfgS427_su4 hn hn2)
  · intro S' _ _ ⟨e'⟩ y hy1 hy3
    exact (good427_onFree_inner hn hn2 (e'.trans eSX) hy3 hy1).2

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
