module

public import CFSG.RankThree.PartTwo.Sec4.Item49Tools
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
public import CFSG.RankThree.PartTwo.KFacts.K72OutL3
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item49CharTwo

open CFSG CFSG.RankThree.PartTwo.Sec4.Item49Tools
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem finite_mulAut (X : Type*) [Group X] [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun α : MulAut X => (α : X → X)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem finite_outer (X : Type*) [Group X] [Finite X] : Finite (Outer X) :=
  have := finite_mulAut X
  inferInstance

theorem odd_card_oThreePrime_of_commutator_mem {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) (hN : Odd (Nat.card N)) (hcomm : ∀ a b : H, a * b * a⁻¹ * b⁻¹ ∈ N) :
    Odd (Nat.card (oThreePrime H)) := by
  have : N.Normal := ⟨fun n hn g => by
    have e : g * n * g⁻¹ = g * n * g⁻¹ * n⁻¹ * n := by group
    rw [e]
    exact N.mul_mem (hcomm g n) hn⟩
  refine odd_card_oThreePrime_of_comm_quotient N hN fun a b => ?_
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have e : (x * y)⁻¹ * (y * x) = y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ := by group
      rw [e]
      exact hcomm _ _

theorem outer_mul_comm {X : Type*} [Group X]
    (h : ∀ σ τ : MulAut X, σ * τ * σ⁻¹ * τ⁻¹ ∈ inner X) (a b : Outer X) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with
  | H σ =>
    induction b using QuotientGroup.induction_on with
    | H τ =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have e : (σ * τ)⁻¹ * (τ * σ) = τ⁻¹ * σ⁻¹ * τ⁻¹⁻¹ * σ⁻¹⁻¹ := by group
      rw [e]
      exact h _ _

theorem odd_card_oThreePrime_outer_of_comm {X : Type*} [Group X] [Finite X]
    (h : ∀ a b : Outer X, a * b = b * a) : Odd (Nat.card (oThreePrime (Outer X))) :=
  have := finite_outer X
  odd_card_oThreePrime_of_comm h

theorem odd_card_oThreePrime_outer_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (h : Odd (Nat.card (oThreePrime (Outer Y)))) :
    Odd (Nat.card (oThreePrime (Outer X))) :=
  have : Finite Y := Finite.of_equiv X e.toEquiv
  have := finite_outer Y
  odd_card_oThreePrime_of_injective (equivalence e).toMonoidHom (equivalence e).injective h

theorem odd_card_oThreePrime_outer_of_diag {X : Type*} [Group X] [Finite X]
    (D : Subgroup (MulAut X)) (hD : Odd (Nat.card (D ⧸ (inner X).subgroupOf D)))
    (hcomm : ∀ α β : MulAut X, α * β * α⁻¹ * β⁻¹ ∈ D) :
    Odd (Nat.card (oThreePrime (Outer X))) := by
  have := finite_outer X
  set φ : D →* Outer X := (QuotientGroup.mk' (inner X)).comp D.subtype with hφ
  have hrange : φ.range = D.map (QuotientGroup.mk' (inner X)) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker = (inner X).subgroupOf D := by
    ext d
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcard : Nat.card (D.map (QuotientGroup.mk' (inner X))) =
      Nat.card (D ⧸ (inner X).subgroupOf D) := by
    rw [← hrange, ← hker]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm
  refine odd_card_oThreePrime_of_commutator_mem (D.map (QuotientGroup.mk' (inner X)))
    (hcard ▸ hD) fun a b => ?_
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner X) a
  obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective (inner X) b
  exact ⟨α * β * α⁻¹ * β⁻¹, hcomm α β, by simp only [map_mul, map_inv]⟩

section Classical

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL conjAut mem_linearAutGroup_iff)
open CFSG.ClassicalGroups.UnitaryFlag

theorem odd_card_oThreePrime_outer_projectiveSL {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 3 ≤ n) (hodd : Odd n) : Odd (Nat.card (oThreePrime (Outer (projectiveSL n K)))) := by
  have := finite_outer (projectiveSL n K)
  set φ := (QuotientGroup.mk' (inner (projectiveSL n K))).comp (conjAut n K) with hφ
  refine odd_card_oThreePrime_of_commutator_mem φ.range
    (Odd.of_dvd_nat (Odd.of_dvd_nat hodd (Nat.gcd_dvd_left _ _))
      (OuterDerived.linear_diagonal_outer (by omega)).2) fun a b => ?_
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner _) a
  obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective (inner _) b
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp
    (OuterDerived.commutator_mem_linearAutGroup hn α β)
  exact ⟨A, by rw [hφ, MonoidHom.comp_apply, hA]; simp only [map_mul, map_inv]⟩

theorem odd_card_oThreePrime_outer_psl2 (K : Type) [Field K] [Finite K] :
    Odd (Nat.card (oThreePrime (Outer (CFSG.GorensteinWalter.PSL2 K)))) :=
  odd_card_oThreePrime_outer_of_comm (OuterDerived.outer_psl2_mul_comm K)

theorem odd_card_oThreePrime_outer_primeFormP {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) {n : ℕ} (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ m = 2)) :
    Odd (Nat.card (oThreePrime
      (Outer (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))) := by
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hFker, -, -, hcard⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  refine odd_card_oThreePrime_outer_of_diag _ (Odd.of_dvd_nat ?_ hcard) fun α β => ?_
  · exact (Nat.even_pow.mpr ⟨even_two, by have := h.one_le; omega⟩).add_one
  · rw [← hFker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [ringAut_mul_comm K (primeFormFieldFactor h hC hn hq α)]
    group

theorem odd_card_oThreePrime_outer_of_projSU {X : Type} [Group X] [Finite X] {n m : ℕ}
    (hn : 3 ≤ n) (hm : 1 ≤ m) (hq : ¬(n = 3 ∧ 2 ^ m = 2)) (e : X ≃* projSU n 2 m) :
    Odd (Nat.card (oThreePrime (Outer X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := unitaryFieldData_galoisField 2 m hm
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := n)) hn hq
  exact odd_card_oThreePrime_outer_of_mulEquiv
    ((e.trans (projSUEquivStatedProj n 2 m)).trans
      ((unitaryPSUEquiv hU (by omega)).symm.trans eT.symm))
    (odd_card_oThreePrime_outer_primeFormP hU hn hq)

end Classical

section Symplectic

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp)

theorem odd_card_oThreePrime_outer_statedSp_two {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    Odd (Nat.card (oThreePrime (Outer (StatedProj (StatedSp 2 K))))) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hm hK
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hm hK
  obtain ⟨-, -, -, -, hcyc, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure hm hFr hord
      hzp
  exact odd_card_oThreePrime_outer_of_comm fun a b => hcyc.commGroup.mul_comm a b

theorem odd_card_oThreePrime_outer_statedSp {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}
    (hr : 3 ≤ r) : Odd (Nat.card (oThreePrime (Outer (StatedProj (StatedSp r K))))) := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) hr
  refine odd_card_oThreePrime_outer_of_comm (outer_mul_comm fun σ τ => ?_)
  refine CFSG.RankThree.PartTwo.KFacts.commutator_mem_of_forall_eq_mul
    (R := Set.range (fieldAut r K)) (fun x hx y hy => ?_) (fun g => ?_) σ τ
  · obtain ⟨s, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := hy
    change fieldAut r K s * fieldAut r K t = fieldAut r K t * fieldAut r K s
    rw [← map_mul, ← map_mul, ringAut_mul_comm K s t]
  · obtain ⟨A, s, rfl⟩ := hgen g
    exact ⟨_, conjAut_mem_inner_of_isSquare
      (FiniteField.isSquare_of_char_two (ringChar.eq K 2) (multiplier r K A : K)), _, ⟨s, rfl⟩,
      rfl⟩

end Symplectic

section Exceptional

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog

theorem odd_card_oThreePrime_outer_of_G2
    {X : Type} [Group X] [Finite X] {f : ℕ} (h : ChevalleyExceptionalModel X .G2 2 f) :
    Odd (Nat.card (oThreePrime (Outer X))) := by
  have hf2 : 2 ≤ f := by
    obtain ⟨⟨-, hf1, -, h3⟩, -⟩ := h
    by_contra hlt
    obtain rfl : f = 1 := by omega
    norm_num at h3
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_G2 h
  obtain ⟨-, Θ, -, -, hker, -⟩ := even_G2_exact_automorphism_normal_form hf2 K hK
  have : Finite (adjointGroup .G2 K) := Finite.of_equiv X e.toEquiv
  refine odd_card_oThreePrime_outer_of_mulEquiv e
    (odd_card_oThreePrime_outer_of_comm (outer_mul_comm fun α β => ?_))
  change _ ∈ (MulAut.conj : adjointGroup .G2 K →* _).range
  rw [← hker, MonoidHom.mem_ker]
  simp only [map_mul, map_inv]
  rw [CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K (Θ α)]
  group

theorem odd_card_oThreePrime_outer_of_trialityD4
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : ChevalleyExceptionalModel X .trialityD4 2 f) :
    Odd (Nat.card (oThreePrime (Outer X))) := by
  have hf1 : 1 ≤ f := h.1.2.1
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_D4 h
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    even_triality_exact_automorphism_normal_form hf1 K hcard σ hσ
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv X e.toEquiv
  refine odd_card_oThreePrime_outer_of_mulEquiv e
    (odd_card_oThreePrime_outer_of_comm (outer_mul_comm fun α β => ?_))
  change _ ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* _).range
  rw [← hker, MonoidHom.mem_ker]
  simp only [map_mul, map_inv]
  rw [CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K (Θ α)]
  group

theorem odd_card_oThreePrime_outer_of_suzuki {X : Type} [Group X]
    [Finite X] {f : ℕ} (h : SuzukiModel X 2 f) : Odd (Nat.card (oThreePrime (Outer X))) := by
  obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hcyc := (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK').1
  have : Finite (suzukiGroup a K) := Finite.of_equiv X e.toEquiv
  exact odd_card_oThreePrime_outer_of_mulEquiv e
    (odd_card_oThreePrime_outer_of_comm fun x y => hcyc.commGroup.mul_comm x y)

theorem odd_card_oThreePrime_outer_of_twistedF4
    {X : Type} [Group X] [Finite X] {f : ℕ} (h : ReeTitsModel X .twistedF4 2 f) :
    Odd (Nat.card (oThreePrime (Outer X))) := by
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_reeGamma h
  obtain ⟨-, -, -, hcyc, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  have : Finite (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) := Finite.of_equiv X e.toEquiv
  exact odd_card_oThreePrime_outer_of_mulEquiv e
    (odd_card_oThreePrime_outer_of_comm fun x y => hcyc.commGroup.mul_comm x y)

theorem odd_card_oThreePrime_outer_of_tits
    {X : Type} [Group X] [Finite X] {f : ℕ} (h : ReeTitsModel X .Tits 2 f) :
    Odd (Nat.card (oThreePrime (Outer X))) := by
  have h2 := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier X 2 f h).1
  have := finite_outer X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine odd_card_oThreePrime_of_not_dvd fun h3 => ?_
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  rw [hk] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

end Exceptional

section Covers

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL scalars_eq_center)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (center_map_equiv)

theorem odd_card_oThreePrime_outer_of_isSLThreeEpsAt {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) {n : ℕ} (hn : 1 ≤ n) (h : IsSLThreeEpsAt X (2 ^ n)) :
    Odd (Nat.card (oThreePrime (Outer X))) := by
  have : Group.IsPerfect X := hq.1
  have := finite_outer (X ⧸ Subgroup.center X)
  obtain ⟨K, _, _, ⟨hK, ⟨e₁⟩⟩ | ⟨hK, ⟨e₁⟩⟩⟩ := h
  ·
    refine odd_card_oThreePrime_outer_of_center X ?_
    let E : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
      e₁.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
    exact odd_card_oThreePrime_outer_of_mulEquiv
      ((QuotientGroup.congr _ _ E (center_map_equiv E)).trans
        (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 K)).symm)
      (odd_card_oThreePrime_outer_projectiveSL le_rfl (by decide))
  ·
    have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    ·
      obtain rfl : n = 1 := by omega
      exfalso
      have hcard := CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
      have := Fintype.ofFinite (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K)
      have hsolv : Group.IsSolvable (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K) :=
        CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3)
          (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
          (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
      exact false_of_isQuasisimple_of_isSolvable hq
        (Group.isSolvable_of_surjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective)
    · have h4 : 4 ≤ 2 ^ n :=
        le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2 : 2 ^ 2 ≤ 2 ^ n)
      have hq2 : 2 < 2 ^ n := by omega
      have hq3 : ¬(3 = 3 ∧ 2 ^ n = 2) := fun h3 => by omega
      refine odd_card_oThreePrime_outer_of_center X ?_
      let E : X ≃* unitarySU 2 n K 3 := e₁
      obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
        (isPrimeFormGram_one (n := 3)) le_rfl hq3
      exact odd_card_oThreePrime_outer_of_mulEquiv
        (((QuotientGroup.congr _ _ E (center_map_equiv E)).trans
          (CFSG.RankThree.PartTwo.KFacts.suCenterEquiv hU hq2)).trans eT.symm)
        (odd_card_oThreePrime_outer_primeFormP hU le_rfl hq3)

end Covers

end CFSG.RankThree.PartTwo.Sec4.Item49CharTwo

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open Item49CharTwo

theorem oddOThreePrime_charTwo_six
    (X : Type) [Group X] [Finite X]
    (hX : IsChevTwoRankTwoModel X ∨ ∃ n : ℕ, 1 ≤ n ∧ IsSLThreeEpsAt X (2 ^ n))
    (hq : CFSG.IsQuasisimple X) : Odd (Nat.card (oThreePrime (Outer X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hX with (⟨n, hn, he | he | he | he | he⟩ | ⟨f, h | h | h | h | h⟩) | ⟨n, hn, h⟩
  ·
    obtain ⟨e⟩ := he
    exact odd_card_oThreePrime_outer_of_mulEquiv (e.trans (projSLEquivPSL _))
      (odd_card_oThreePrime_outer_psl2 _)
  ·
    obtain ⟨e⟩ := he
    exact odd_card_oThreePrime_outer_of_mulEquiv (e.trans (projSLEquivProjectiveSL 3 _))
      (odd_card_oThreePrime_outer_projectiveSL le_rfl (by decide))
  ·
    obtain ⟨e⟩ := he
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · obtain rfl : n = 1 := by omega
      exfalso
      have := Sec13.isSolvable_projSU_two
      exact false_of_isQuasisimple_of_isSolvable hq
        (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
    · have h4 : 4 ≤ 2 ^ n :=
        le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2 : 2 ^ 2 ≤ 2 ^ n)
      exact odd_card_oThreePrime_outer_of_projSU le_rfl hn (fun h3 => by omega) e
  ·
    obtain ⟨e⟩ := he
    exact odd_card_oThreePrime_outer_of_mulEquiv (e.trans (projSpEquivStatedProj 2 _))
      (odd_card_oThreePrime_outer_statedSp_two hn (card_galoisField 2 n hn))
  ·
    obtain ⟨e⟩ := he
    exact odd_card_oThreePrime_outer_of_projSU (by norm_num) hn
      (fun h3 => absurd h3.1 (by norm_num)) e
  · exact odd_card_oThreePrime_outer_of_G2 h
  · exact odd_card_oThreePrime_outer_of_trialityD4 h
  · exact odd_card_oThreePrime_outer_of_suzuki h
  · exact odd_card_oThreePrime_outer_of_twistedF4 h
  · exact odd_card_oThreePrime_outer_of_tits h
  · exact odd_card_oThreePrime_outer_of_isSLThreeEpsAt hq hn h

theorem oddOThreePrime_charTwo_seven (X : Type) [Group X] [Finite X]
    (hX : Nonempty (X ≃* projSL 5 (GaloisField 2 1)) ∨
      Nonempty (X ≃* projSp 3 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSU 5 2 2)) :
    Odd (Nat.card (oThreePrime (Outer X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hX with he | he | he <;> obtain ⟨e⟩ := he
  ·
    exact odd_card_oThreePrime_outer_of_mulEquiv (e.trans (projSLEquivProjectiveSL 5 _))
      (odd_card_oThreePrime_outer_projectiveSL (by norm_num) (by decide))
  ·
    exact odd_card_oThreePrime_outer_of_mulEquiv (e.trans (projSpEquivStatedProj 3 _))
      (odd_card_oThreePrime_outer_statedSp (by norm_num))
  ·
    exact odd_card_oThreePrime_outer_of_projSU (by norm_num) (by norm_num)
      (fun h3 => absurd h3.1 (by norm_num)) e

theorem oddOThreePrime_charTwo
    (X : Type) [Group X] [Finite X]
    (hX : (IsChevTwoRankTwoModel X ∨ ∃ n : ℕ, 1 ≤ n ∧ IsSLThreeEpsAt X (2 ^ n)) ∨
      (Nonempty (X ≃* projSL 5 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSp 3 (GaloisField 2 1)) ∨
        Nonempty (X ≃* projSU 5 2 2)))
    (hq : CFSG.IsQuasisimple X) : Odd (Nat.card (oThreePrime (Outer X))) :=
  hX.elim (fun h => oddOThreePrime_charTwo_six X h hq) fun h => oddOThreePrime_charTwo_seven X h

end CFSG.RankThree.PartTwo.Sec4
