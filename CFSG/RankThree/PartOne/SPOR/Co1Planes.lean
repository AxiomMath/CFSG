module

public import CFSG.RankThree.PartOne.SPOR.Co1PlanesSound
public import CFSG.RankThree.PartOne.SPOR.Co1PlanesCheck
public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.RankThree.PartOne.KS.Arith
public import CFSG.Sporadic.Co1Block.TwoACent
public import CFSG.Sporadic.Co1Block.TwoCCent
public import CFSG.Sporadic.Co1Block.TwoBCentBase2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartOne.SPOR

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] noncomputable def co1Iota :
    CFSG.Blueprint.NativeSporadic.Co1 →* GL24 where
  toFun a := ((co1MatEquiv a : GA) : GL24)
  map_one' := by rw [map_one]; rfl
  map_mul' a b := by rw [map_mul]; rfl

theorem co1Iota_apply (a : CFSG.Blueprint.NativeSporadic.Co1) :
    co1Iota a = ((co1MatEquiv a : GA) : GL24) := rfl

theorem co1Iota_injective : Function.Injective co1Iota :=
  fun _ _ h => co1MatEquiv.injective (Subtype.ext h)

theorem co1_center_trivial :
    TrivialCenter CFSG.Blueprint.NativeSporadic.Co1 := by
  have hfin := CFSG.Sporadic.Co1.fam_co1_simplicity
  have : Finite CFSG.Blueprint.NativeSporadic.Co1 := hfin.1
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.Co1 := hfin.2.2
  refine trivial_center_of_simple (not_commutative_of_simple_of_not_prime ?_)
  rw [CFSG.Sporadic.Co1.card_Co1]
  norm_num

theorem co1_base_rep :
    List.Forall₂ MRep co1PlaneBase [A₁, A₂, (iotaA : GL24), (iotaC : GL24)] :=
  .cons rep_A₁ (.cons rep_A₂ (.cons rep_iotaA (.cons rep_iotaC .nil)))

theorem co1_base_mem :
    ∀ g ∈ [A₁, A₂, (iotaA : GL24), (iotaC : GL24)], ∃ a : CFSG.Blueprint.NativeSporadic.Co1,
      co1Iota a = g := by
  intro g hg
  have hGA : g ∈ GA := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h
    · rw [h]; exact A₁_mem
    · rw [h]; exact A₂_mem
    · rw [h]; exact iotaA_mem_GA
    · rw [h]; exact iotaC_mem_GA
  refine ⟨co1MatEquiv.symm ⟨g, hGA⟩, ?_⟩
  rw [co1Iota_apply, MulEquiv.apply_symm_apply]

theorem co1_exists_conj (a b : CFSG.Blueprint.NativeSporadic.Co1)
    (c : GA) (hc : c * co1MatEquiv a * c⁻¹ = co1MatEquiv b) :
    ∃ d : CFSG.Blueprint.NativeSporadic.Co1, d * a * d⁻¹ = b := by
  refine ⟨co1MatEquiv.symm c, ?_⟩
  apply co1MatEquiv.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hc

theorem co1PlaneA_t : co1PlaneA.t = 3 := rfl

theorem co1PlaneC_t : co1PlaneC.t = 4 := rfl

theorem co1PlaneB_t : co1PlaneB.t = 1 := rfl

theorem co1_cover_data :
    ∃ t : Fin 3 → CFSG.Blueprint.NativeSporadic.Co1, InvolutionReps t ∧
      (∀ j, CoverP 5 (t j)) ∧ (∀ j, CoverP 7 (t j)) := by
  have hfin := CFSG.Sporadic.Co1.fam_co1_simplicity
  have : Finite CFSG.Blueprint.NativeSporadic.Co1 := hfin.1
  have hι := co1Iota_injective
  have hc := co1_center_trivial
  have hbase := co1_base_rep
  have hmem := co1_base_mem
  obtain ⟨tA, htA, hA1, hA2⟩ := co1Class_cover co1Iota hbase hmem hι hc co1_plane_check_a
  obtain ⟨tC, htC, hC1, hC2⟩ := co1Class_cover co1Iota hbase hmem hι hc co1_plane_check_c
  obtain ⟨tB, htB, hB1, hB2⟩ := co1Class_cover co1Iota hbase hmem hι hc co1_plane_check_b
  have htA' : co1Iota tA = (iotaA : GL24) := by
    rw [htA, co1PlaneA_t]
    simp only [Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero]
  have htC' : co1Iota tC = (iotaC : GL24) := by
    rw [htC, co1PlaneC_t]
    simp only [Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero]
  have htB' : co1Iota tB = A₁ := by
    rw [htB, co1PlaneB_t]
    simp only [Nat.sub_self, List.getD_cons_zero]
  have eA : co1MatEquiv tA = aC := Subtype.ext (htA'.trans coe_aC.symm)
  have eC : co1MatEquiv tC = cC := Subtype.ext (htC'.trans coe_cC.symm)
  have eB : co1MatEquiv tB = a₁ := Subtype.ext (htB'.trans coe_a₁.symm)
  have hNA : Nat.card (Subgroup.centralizer ({tA} : Set CFSG.Blueprint.NativeSporadic.Co1)) =
      89181388800 := by
    rw [card_centralizer_co1, eA, card_centralizer_GA, coe_aC]
    exact card_cent_aG
  have hNC : Nat.card (Subgroup.centralizer ({tC} : Set CFSG.Blueprint.NativeSporadic.Co1)) =
      389283840 := by
    rw [card_centralizer_co1, eC, card_centralizer_GA, coe_cC]
    exact card_cent_cG
  have hNB : Nat.card (Subgroup.centralizer ({tB} : Set CFSG.Blueprint.NativeSporadic.Co1)) =
      2012774400 := by
    rw [card_centralizer_co1, eB]
    exact card_cent_a₁
  have c5A : CoverP 5 tA := by
    obtain ⟨b, hb, hbp⟩ : ∃ b ∈ co1PlaneA.b2, b.p = 5 := ⟨_, List.mem_singleton_self _, rfl⟩
    have h := @hA2 b hb (by rw [hbp]; norm_num) 89181388800 3567255552 hNA
      (by rw [hbp]; norm_num) (by rw [hbp]; norm_num)
    rw [hbp] at h
    exact h
  have c5C : CoverP 5 tC := by
    obtain ⟨b, hb, hbp⟩ : ∃ b ∈ co1PlaneC.b1, b.p = 5 := ⟨_, List.mem_singleton_self _, rfl⟩
    have h := @hC1 b hb (by rw [hbp]; norm_num) 389283840 77856768 hNC
      (by rw [hbp]; norm_num) (by rw [hbp]; norm_num)
    rw [hbp] at h
    exact h
  have c5B : CoverP 5 tB := by
    obtain ⟨b, hb, hbp⟩ : ∃ b ∈ co1PlaneB.b2, b.p = 5 := ⟨_, List.mem_singleton_self _, rfl⟩
    have h := @hB2 b hb (by rw [hbp]; norm_num) 2012774400 80510976 hNB
      (by rw [hbp]; norm_num) (by rw [hbp]; norm_num)
    rw [hbp] at h
    exact h
  have c7A : CoverP 7 tA := by
    obtain ⟨b, hb, hbp⟩ : ∃ b ∈ co1PlaneA.b1, b.p = 7 := ⟨_, List.mem_singleton_self _, rfl⟩
    have h := @hA1 b hb (by rw [hbp]; norm_num) 89181388800 12740198400 hNA
      (by rw [hbp]; norm_num) (by rw [hbp]; norm_num)
    rw [hbp] at h
    exact h
  have c7B : CoverP 7 tB := by
    obtain ⟨b, hb, hbp⟩ : ∃ b ∈ co1PlaneB.b1, b.p = 7 := ⟨_, List.mem_singleton_self _, rfl⟩
    have h := @hB1 b hb (by rw [hbp]; norm_num) 2012774400 287539200 hNB
      (by rw [hbp]; norm_num) (by rw [hbp]; norm_num)
    rw [hbp] at h
    exact h
  have c7C : CoverP 7 tC :=
    cover_of_none_inner tC (by rw [hNC]; norm_num)
  refine ⟨![tA, tC, tB], ?_, ?_, ?_⟩
  · intro s hs
    have h2 : orderOf (co1MatEquiv s) = 2 := by rw [orderOf_co1MatEquiv]; exact hs
    rcases involution_classes.1 (co1MatEquiv s) h2 with h | h | h
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      exact ⟨0, co1_exists_conj s tA c (by rw [eA]; exact hc)⟩
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      exact ⟨1, co1_exists_conj s tC c (by rw [eC]; exact hc)⟩
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      exact ⟨2, co1_exists_conj s tB c (by rw [eB]; exact hc)⟩
  · intro j
    fin_cases j
    exacts [c5A, c5C, c5B]
  · intro j
    fin_cases j
    exacts [c7A, c7C, c7B]

theorem conjWitness_Co1 :
    ConjWitness (CFSG.Blueprint.NativeSporadic.Carrier .Co1) 5 ∧
      ConjWitness (CFSG.Blueprint.NativeSporadic.Carrier .Co1) 7 := by
  obtain ⟨t, hr, h5, h7⟩ := co1_cover_data
  have hc := co1_center_trivial
  have hin : ∀ φ : MulAut CFSG.Blueprint.NativeSporadic.Co1,
      ∃ a : CFSG.Blueprint.NativeSporadic.Co1, φ = MulAut.conj a := fun φ => allInner_Co1 φ
  exact ⟨conjWitness_of_covers hc hin t hr h5, conjWitness_of_covers hc hin t hr h7⟩

theorem sporadicPlaneOdd_Co1 :
    SporadicPlaneOdd (CFSG.Blueprint.NativeSporadic.Carrier .Co1) := by
  have hW := conjWitness_Co1
  refine sporadicPlaneOdd_of_conjWitness {5, 7} ?_ ?_ ?_
  · intro q hq _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    exacts [hW.1, hW.2]
  · intro T _ _ _ _ he q hq hqp
    obtain ⟨e⟩ := he
    rw [Nat.card_congr (equivalence e).toEquiv, card_outer_Co1]
    exact fun h => hqp.one_lt.ne' (Nat.dvd_one.1 h)
  · intro T _ _ _ hnab he p hp hp3 hpS
    obtain ⟨e⟩ := he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpS
    refine not_sq_dvd_card_mulAut_of_outer_le hnab e (N := 4157776806543360000) (k := 1)
      CFSG.Sporadic.Co1.card_Co1 (card_outer_Co1.le) hp (by omega) ?_
    have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
    have h3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
    have h5 : Nat.Coprime p 5 := (Nat.coprime_primes hp Nat.prime_five).mpr hpS.1
    have h7 : Nat.Coprime p 7 := (Nat.coprime_primes hp (by norm_num)).mpr hpS.2
    have hs : Nat.Coprime p (2 ^ 21 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2) :=
      ((((Nat.Coprime.pow_right 21 h2).mul_right (Nat.Coprime.pow_right 9 h3)).mul_right
        (Nat.Coprime.pow_right 4 h5)).mul_right (Nat.Coprime.pow_right 2 h7))
    have hN : (4157776806543360000 : ℕ) = (2 ^ 21 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2) * 3289 := by norm_num
    rw [hN]
    exact not_sq_dvd_mul_of_coprime hp hs (B := 57) (by norm_num) (by decide) (by norm_num)

end CFSG.RankThree.PartOne.SPOR
