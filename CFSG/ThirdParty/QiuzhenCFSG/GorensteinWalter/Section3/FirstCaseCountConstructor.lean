module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseJNCoset
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseIndexCoset
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseOrderInfra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionFive
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenCardThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenExact
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinHighFiber
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCommutingPairs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCountDerived
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionCountInSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinDataComplete
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private abbrev localPairFiber {Ω α : Type u} (π : α → Ω) (ω : Ω) :=
  {p : {a : α // π a = ω} × {a : α // π a = ω} // p.1 ≠ p.2}

private theorem sum_local_coset_pair_counts
    {Ω α : Type u} [Finite Ω] [Finite α]
    (π : α → Ω) (ω0 : Ω)
    (hbound : ∀ ω : {ω : Ω // ω ≠ ω0},
      Nat.card {a : α // π a = ω.1} ≤ 4)
    (hlocal : ∀ ω : {ω : Ω // ω ≠ ω0},
      Nat.card (localPairFiber π ω.1) = if Nat.card {a : α // π a = ω.1} = 2 then 2
        else if Nat.card {a : α // π a = ω.1} = 4 then 6 else 0) :
    Nat.card (Σ ω : {ω : Ω // ω ≠ ω0},
      localPairFiber π ω.1) =
      2 * Nat.card {ω : {ω : Ω // ω ≠ ω0} //
        Nat.card {a : α // π a = ω.1} = 2} +
      6 * Nat.card {ω : {ω : Ω // ω ≠ ω0} //
        Nat.card {a : α // π a = ω.1} = 4} := by
  classical
  let Nonbase := {ω : Ω // ω ≠ ω0}
  let : Fintype Nonbase := Fintype.ofFinite _
  calc
    Nat.card (Σ ω : Nonbase,
        localPairFiber π ω.1) =
        ∑ ω : Nonbase, Nat.card (localPairFiber π ω.1) := by
          rw [Nat.card_sigma]
    _ = ∑ ω : Nonbase,
        (if Nat.card {a : α // π a = ω.1} = 2 then 2
         else if Nat.card {a : α // π a = ω.1} = 4 then 6 else 0) := by
          apply Finset.sum_congr rfl
          intro ω _
          exact hlocal ω
    _ = 2 * Nat.card {ω : Nonbase //
          Nat.card {a : α // π a = ω.1} = 2} +
        6 * Nat.card {ω : Nonbase //
          Nat.card {a : α // π a = ω.1} = 4} := by
      have hsplit : ∀ ω : Nonbase,
          (if Nat.card {a : α // π a = ω.1} = 2 then 2
           else if Nat.card {a : α // π a = ω.1} = 4 then 6 else 0) =
          (if Nat.card {a : α // π a = ω.1} = 2 then 2 else 0) +
          (if Nat.card {a : α // π a = ω.1} = 4 then 6 else 0) := by
        intro ω
        by_cases h2 : Nat.card {a : α // π a = ω.1} = 2 <;>
          by_cases h4 : Nat.card {a : α // π a = ω.1} = 4 <;>
            simp [h2, h4]
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib]
      have h2sum :
          (∑ ω : Nonbase, if Nat.card {a : α // π a = ω.1} = 2 then 2 else 0) =
            2 * Nat.card {ω : Nonbase //
               Nat.card {a : α // π a = ω.1} = 2} := by
        rw [Nat.card_eq_fintype_card]
        calc
          (∑ ω : Nonbase, if Nat.card {a : α // π a = ω.1} = 2 then 2 else 0) =
              2 * ∑ ω : Nonbase,
              if Nat.card {a : α // π a = ω.1} = 2 then 1 else 0 := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro ω _
                by_cases h : Nat.card {a : α // π a = (ω : Ω)} = 2 <;> simp [h]
          _ = 2 *
              (Finset.univ.filter fun ω : Nonbase =>
                Nat.card {a : α // π a = ω.1} = 2).card := by
                rw [Finset.sum_boole]
                simp
          _ = 2 * Fintype.card {ω : Nonbase //
                Nat.card {a : α // π a = ω.1} = 2} := by
                rw [Fintype.card_subtype]
      have h4sum :
          (∑ ω : Nonbase, if Nat.card {a : α // π a = ω.1} = 4 then 6 else 0) =
            6 * Nat.card {ω : Nonbase //
               Nat.card {a : α // π a = ω.1} = 4} := by
        rw [Nat.card_eq_fintype_card]
        calc
          (∑ ω : Nonbase, if Nat.card {a : α // π a = ω.1} = 4 then 6 else 0) =
              6 * ∑ ω : Nonbase,
              if Nat.card {a : α // π a = ω.1} = 4 then 1 else 0 := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro ω _
                by_cases h : Nat.card {a : α // π a = (ω : Ω)} = 4 <;> simp [h]
          _ = 6 *
              (Finset.univ.filter fun ω : Nonbase =>
                Nat.card {a : α // π a = ω.1} = 4).card := by
                rw [Finset.sum_boole]
                simp
          _ = 6 * Fintype.card {ω : Nonbase //
                Nat.card {a : α // π a = ω.1} = 4} := by
                rw [Fintype.card_subtype]
      rw [h2sum, h4sum]

/-! ## Source restrictions (5)--(7) -/

/-- The restriction-(7) field of `FirstCaseCountData` follows by combining
the exact fibre endpoint with the landed card-three transfer.  The source's
printed full-intersection `D₆` assertion is deliberately not used here; the
consistent endpoint is the index-six quotient retained by
`firstCase_klein_restrictionSeven_card_three`. -/
public theorem firstCase_klein_restriction_seven_data
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    ∀ (n : ℕ) (y : G) (X : Subgroup G),
      4 ≤ n → y ∈ firstCaseJ c n → X ≠ ⊥ → X ≤ c.Hhat →
      Nat.Coprime 2 (Nat.card X) →
      (∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y) →
      Even (Nat.card (Subgroup.centralizer (X : Set G))) →
      Even (Nat.card ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G))) →
      Nat.card c.U = Nat.card X ∧ Nat.card X = 3 ∧ n = 4 ∧
        (let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
         let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
         (N.subgroupOf D).index = 6) := by
  intro n y X hn hyJ hXne hXle hXodd hXinv hC_even hN_even
  have hn4 := firstCase_klein_restrictionSeven_exact
    hmin c hfirst hklein hyJ hn hXne hXle hXodd hXinv hC_even hN_even
  have hcard := firstCase_klein_restrictionSeven_card_three
    hmin c hfirst hklein hyJ hn hXne hXle hXodd hXinv hC_even hN_even
  have hXcard := (firstCase_klein_restrictionSeven_core
    hmin c hfirst hklein hyJ hXne hXle hXodd hXinv hC_even hN_even).1
  exact ⟨by omega, hXcard, hn4, hcard.2⟩

/-- The high-fibre vanishing theorem in the exact form consumed by the
finite-support reduction. -/
public theorem firstCase_klein_high_fiber_vanish_of_n_eq_four
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (h7 : ∀ (n : ℕ) (y : G) (X : Subgroup G),
      4 ≤ n → y ∈ firstCaseJ c n → X ≠ ⊥ → X ≤ c.Hhat →
      Nat.Coprime 2 (Nat.card X) →
      (∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y) →
      Even (Nat.card (Subgroup.centralizer (X : Set G))) →
      Even (Nat.card ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G))) →
      Nat.card c.U = Nat.card X ∧ Nat.card X = 3 ∧ n = 4 ∧
        (let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
         let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
         (N.subgroupOf D).index = 6)) :
    ∀ n : ℕ, 5 ≤ n → cosetInvolution_b c.Hhat n = 0 := by
  exact firstCase_klein_high_fiber_vanish_of_restrictionSeven hmin c hfirst hklein h7

/-! ## Product bookkeeping for the fixed centralizer -/

public theorem firstCase_H_product_equiv
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) :
    Nonempty (c.S × c.U ≃ c.H) := by
  classical
  have hSU : (c.S : Subgroup G) ⊔ c.U = c.H :=
    fact_2_preamble_H_eq_SU hmin c
  have hUnorm : IsNormalIn c.U c.H := by
    change IsNormalIn (oddCoreOf c.H) c.H
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.2
    · intro h hh x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      refine Subgroup.mem_map.mpr ⟨
        (⟨h, hh⟩ : c.H) * y * (⟨h, hh⟩ : c.H)⁻¹, ?_, by simp⟩
      exact (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
        y hy (⟨h, hh⟩ : c.H)
  have hSleH : (c.S : Subgroup G) ≤ c.H := centralizerSetup_S_le_H c
  have hSnormU : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) :=
    hSleH.trans (le_normalizer_of_isNormalIn hUnorm)
  have hUcop : Nat.Coprime 2 (Nat.card c.U) := by
    change Nat.Coprime 2 (Nat.card (oddCoreOf c.H))
    rw [show Nat.card (oddCoreOf c.H) = Nat.card (pPrimeCore 2 c.H) by
      simpa [oddCoreOf] using
        (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.H)
          c.H.subtype_injective)]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hScop : Nat.Coprime (Nat.card (c.S : Subgroup G)) (Nat.card c.U) := by
    have hSpow : ∃ n : ℕ, Nat.card (c.S : Subgroup G) = 2 ^ n := by
      have hcard : Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := by
        obtain ⟨e⟩ := c.dihedralEquiv
        simpa using (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
      refine ⟨c.m + 1, ?_⟩
      calc
        Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := hcard
        _ = 2 ^ (c.m + 1) := by rw [pow_succ]; ring
    obtain ⟨n, hn⟩ := hSpow
    rw [hn]
    exact hUcop.pow_left _
  have hdisj : Disjoint (c.S : Subgroup G) c.U :=
    Subgroup.disjoint_of_coprime_natCard hScop
  have hset : (c.H : Set G) = (c.S : Set G) * (c.U : Set G) := by
    rw [← hSU, Subgroup.coe_mul_of_left_le_normalizer_right c.S c.U hSnormU]
    rfl
  let f : c.S × c.U → c.H := fun z =>
    ⟨(z.1 : G) * (z.2 : G), by
      rw [← hSU]
      exact Subgroup.mul_mem_sup z.1.2 z.2.2⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisj
    exact congrArg Subtype.val hxy
  have hf_surj : Function.Surjective f := by
    intro z
    have hz : (z : G) ∈ (c.S : Set G) * (c.U : Set G) := by
      rw [← hset]
      exact z.2
    rcases Set.mem_mul.mp hz with ⟨s, hs, u, hu, hsu⟩
    exact ⟨⟨⟨s, hs⟩, ⟨u, hu⟩⟩, Subtype.ext hsu⟩
  exact ⟨Equiv.ofBijective f ⟨hf_inj, hf_surj⟩⟩

/-- In the Klein-four branch, `|H| = |S| * |U| = 8 * |U|`. -/
public theorem firstCase_klein_H_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    Nat.card c.H = 8 * Nat.card c.U := by
  classical
  obtain ⟨e⟩ := firstCase_H_product_equiv hmin c
  have hS8 := firstCase_klein_S_card hmin c hfirst hklein
  calc
    Nat.card c.H = Nat.card (c.S × c.U) := Nat.card_congr e.symm
    _ = Nat.card (c.S : Subgroup G) * Nat.card c.U := Nat.card_prod _ _
    _ = 8 * Nat.card c.U := by rw [hS8]

/-- Assemble a concrete `FirstCaseCountData` from the equations package,
restrictions (5)--(7), and the four remaining arithmetic/group facts.  This
is the constructor boundary: the caller still has to supply identity (8),
`12 ∣ b₄`, `b₃ = 0`, and `8 ∣ b₁`, all of which are genuine theorem goals
in the active route. -/
public theorem firstCase_klein_count_data_of_count_package
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (K : Subgroup G) (b0 b1 b2 b3 b4 : ℕ)
    (hKHall : IsHallIn K c.FU) (hKne : K ≠ ⊥)
    (hJn : ∀ n : ℕ, n ≤ 4 →
      Nat.card {x : G // x ∈ firstCaseJ c n} =
        n * firstCaseBn b0 b1 b2 b3 b4 n)
    (hHcount : Nat.card {x : G // IsInvolution x ∧ x ∈ c.H} = 3 + 2 * Nat.card K)
    (hHhatcount : Nat.card {x : G // IsInvolution x ∧ x ∈ c.Hhat} =
      3 + 6 * Nat.card K)
    (hindex : c.H.index = 3 * c.Hhat.index)
    (htotal : Nat.card {x : G // IsInvolution x} =
      3 + 6 * Nat.card K + b1 + 2 * b2 + 3 * b3 + 4 * b4)
    (hsum : c.Hhat.index = 1 + b0 + b1 + b2 + b3 + b4)
    (h4 : 6 * Nat.card K + b4 = 3 * b0 + 2 * b1 + b2)
    (h8 : 3 * b4 + b2 = 6 * (Nat.card K) ^ 2)
    (h4dvd : 12 ∣ b4) (h3zero : b3 = 0) (h1dvd : 8 ∣ b1)
    (hUcard : Nat.card c.U = 3) :
    Nonempty (FirstCaseCountData c) := by
  classical
  have hKcard : Nat.card K = 3 :=
    firstCase_klein_K_card_eq_three_of_U_card_three c hKHall hKne hUcard
  have hKge2 : 2 ≤ Nat.card K := by omega
  have h4ne : b4 ≠ 0 :=
    firstCase_klein_b4_ne_zero_of_equations (Nat.card K) b0 b1 b2 b4
      h8 h4 hKge2
  have hHcard : Nat.card c.H = 8 * Nat.card K := by
    have hh := firstCase_klein_H_card hmin c hfirst hklein
    rw [hUcard] at hh
    simpa [hKcard] using hh
  have h7 : ∀ (n : ℕ) (y : G) (X : Subgroup G),
      4 ≤ n → y ∈ firstCaseJ c n → X ≠ ⊥ → X ≤ c.Hhat →
      Nat.Coprime 2 (Nat.card X) →
      (∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y) →
      Even (Nat.card (Subgroup.centralizer (X : Set G))) →
      Even (Nat.card ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G))) →
      Nat.card c.U = Nat.card K ∧ Nat.card K = 3 ∧ n = 4 ∧
        (let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
         let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
         (N.subgroupOf D).index = 6) := by
    intro n y X hn hyJ hXne hXle hXodd hXinv hC_even hN_even
    have hd := firstCase_klein_restriction_seven_data
      hmin c hfirst hklein n y X hn hyJ hXne hXle hXodd hXinv hC_even hN_even
    have hUK : Nat.card c.U = Nat.card K := by
      calc
        Nat.card c.U = Nat.card X := hd.1
        _ = 3 := hd.2.1
        _ = Nat.card K := hKcard.symm
    exact ⟨hUK, hKcard, hd.2.2.1, hd.2.2.2⟩
  exact ⟨{
    k := Nat.card K
    b0 := b0
    b1 := b1
    b2 := b2
    b3 := b3
    b4 := b4
    h1_Jn := hJn
    h1_H := hHcount
    h1_Hhat := hHhatcount
    h2_index := hindex
    h2_total := htotal
    h3 := hsum
    h4 := h4
    h5 := firstCase_klein_restrictionFive hmin c hfirst hklein
    h6 := fun y hy hyH hI =>
      firstCase_klein_restrictionSix hmin c hfirst hklein (y := y) hy hyH hI
    h7 := h7
    h8 := h8
    h9 := h4
    hK := hKcard
    h4ne := h4ne
    h4dvd := h4dvd
    h3zero := h3zero
    h1dvd := h1dvd
    hH_card := hHcard }⟩

end CFSG.GorensteinWalter
