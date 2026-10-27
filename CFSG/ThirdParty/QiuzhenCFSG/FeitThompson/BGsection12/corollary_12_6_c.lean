module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_6_b

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Corollary 12.6(c). -/
public theorem CFSG.corollary_12_6_c
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    ∀ X : Subgroup G, X ∈ section10PrimeOrderSubgroupsIn p A →
      subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ →
        section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  classical
  intro X hX hCX
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  have hCproper : Subgroup.centralizer (X : Set G) ≠ ⊤ := by
    intro hCtop
    have htop_le_norm :
        (⊤ : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := by
      simpa [hCtop] using (centralizer_le_normalizer X)
    exact section12_normalizer_ne_top_of_ne_bot_ne_top_pre
      (section12_primeOrder_ne_bot hX) (section12_primeOrder_ne_top_pre hX)
      (top_le_iff.mp htop_le_norm)
  obtain ⟨M₀, hM₀⟩ :=
    section12_exists_maximalSubgroupsContaining_of_ne_top_pre (G := G) hCproper
  have huniq :
      ∀ L : Subgroup G,
        L ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) →
          L = M := by
    intro L hL
    by_contra hLM
    have hA_le_L : A ≤ L := by
      intro a ha
      have haC : a ∈ Subgroup.centralizer (X : Set G) :=
        section12_rankTwo_le_centralizer_of_primeOrder_pre
          (section12_rankTwo_elementary hA_M) hX ha
      exact hL.2 haC
    have hL_A : L ∈ section9MaximalSubgroupsContaining A := ⟨hL.1, hA_le_L⟩
    have hSinf : section10Msigma M ⊓ L = ⊥ :=
      theorem_12_5_e hM hp hA_M L hL_A hLM
    have hCX_le_inf :
        subgroupCentralizerIn (section10Msigma M) X ≤ section10Msigma M ⊓ L := by
      intro x hx
      exact ⟨hx.1, hL.2 hx.2⟩
    have hCXbot : subgroupCentralizerIn (section10Msigma M) X = ⊥ :=
      le_bot_iff.mp (by
        rw [← hSinf]
        exact hCX_le_inf)
    exact hCX hCXbot
  have hM₀_eq : M₀ = M := huniq M₀ hM₀
  have hM_mem :
      M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
    simpa [hM₀_eq] using hM₀
  ext L
  constructor
  · intro hL
    simpa using huniq L hL
  · intro hL
    simpa [Set.mem_singleton_iff.mp hL] using hM_mem

omit [IsMinCE G] in
public theorem CFSG.section12_exists_primeOrder_zpowers_in_pre
    {B : Subgroup G} {x : G} (hxB : x ∈ B) (hxne : x ≠ 1) :
    ∃ q : Nat.Primes, ∃ z : G,
      z ∈ Subgroup.zpowers x ∧ z ∈ B ∧ z ≠ 1 ∧
        Subgroup.zpowers z ∈ section10PrimeOrderSubgroupsIn q B := by
  classical
  have hcard_ne_one : Nat.card (Subgroup.zpowers x) ≠ 1 := by
    intro hcard
    have hzbot : Subgroup.zpowers x = ⊥ :=
      (Subgroup.card_eq_one (H := Subgroup.zpowers x)).1 hcard
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hzbot] using (Subgroup.mem_zpowers x)
    exact hxne (by simpa using hxbot)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨q, hqprime, hqdiv⟩
  let q' : Nat.Primes := ⟨q, hqprime⟩
  haveI : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨z₀, hz₀_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers x) q hqdiv
  let z : G := z₀
  have hz_zpowx : z ∈ Subgroup.zpowers x := z₀.property
  have hzB : z ∈ B := (Subgroup.zpowers_le.2 hxB) hz_zpowx
  have hz_order : orderOf z = q := by
    simpa [z, Subgroup.orderOf_coe] using hz₀_order
  have hz_ne : z ≠ 1 := by
    intro hz1
    have hq_one : q = 1 := by
      rw [← hz_order, hz1, orderOf_one]
    exact hqprime.ne_one hq_one
  have hX_le_B : Subgroup.zpowers z ≤ B := Subgroup.zpowers_le.2 hzB
  have hX_card : Nat.card (Subgroup.zpowers z) = q'.val := by
    rw [Nat.card_zpowers]
    exact hz_order
  exact ⟨q', z, hz_zpowx, hzB, hz_ne,
    by simpa [section10PrimeOrderSubgroupsIn, Nat.card_zpowers] using ⟨hzB, hz_order⟩⟩

omit [IsMinCE G] in
public theorem CFSG.section12_exists_primeOrder_zpowers_of_prime_dvd_card_pre
    {B : Subgroup G} {q : Nat.Primes} (hqB : q.val ∣ Nat.card B) :
    ∃ z : G, z ∈ B ∧ z ≠ 1 ∧
      Subgroup.zpowers z ∈ section10PrimeOrderSubgroupsIn q B := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  obtain ⟨z₀, hz₀_order⟩ := exists_prime_orderOf_dvd_card' (G := B) q.val hqB
  let z : G := z₀
  have hzB : z ∈ B := z₀.property
  have hz_order : orderOf z = q.val := by
    simpa [z, Subgroup.orderOf_coe] using hz₀_order
  have hz_ne : z ≠ 1 := by
    intro hz1
    have hq_one : q.val = 1 := by
      rw [← hz_order, hz1, orderOf_one]
    exact q.property.ne_one hq_one
  have hX_card : Nat.card (Subgroup.zpowers z) = q.val := by
    rw [Nat.card_zpowers]
    exact hz_order
  exact ⟨z, hzB, hz_ne,
    by
      simpa [section10PrimeOrderSubgroupsIn] using
        (⟨Subgroup.zpowers_le.2 hzB, hX_card⟩ :
          Subgroup.zpowers z ≤ B ∧ Nat.card (Subgroup.zpowers z) = q.val)⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_elementCentralizerIn_le_subgroupCentralizerIn_zpowers_of_mem_zpowers_pre
    {H : Subgroup G} {x z : G} (hz : z ∈ Subgroup.zpowers x) :
    elementCentralizerIn H x ≤ subgroupCentralizerIn H (Subgroup.zpowers z) := by
  intro y hy
  rcases (by simpa [elementCentralizerIn] using hy) with ⟨hyH, hyCx⟩
  refine ⟨hyH, ?_⟩
  have hyCxpow : y ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    section12_centralizer_singleton_le_centralizer_zpowers_pre (G := G) (a := x) hyCx
  have hZle : (Subgroup.zpowers z : Set G) ⊆ (Subgroup.zpowers x : Set G) :=
    Subgroup.zpowers_le.2 hz
  exact (Subgroup.centralizer_le hZle) hyCxpow

public theorem CFSG.section12_not_normalizer_primeOrder_le_M_of_tau13_pre
    {M X : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hXp : IsPGroup q.val X) (hXne : X ≠ ⊥) (hXM : X ≤ M)
    (hqτ13 : q ∈ section12Tau1Primes M ∪ section12Tau3Primes M) :
    ¬ Subgroup.normalizer (X : Set G) ≤ M := by
  intro hNXM
  have hMcont :
      M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) :=
    ⟨hM, hNXM⟩
  have hnot : section12NotConjugate M M :=
    lemma_12_2_b (G := G) (M := M) (Mstar := M) (X := X) (p := q)
      hM hXp hXne hXM hMcont (Or.inr hqτ13)
  exact hnot 1 (section8_conjBy_one M)

public theorem CFSG.section12_subgroupCentralizerIn_primeOrder_eq_bot_of_tau13_pre
    {M E E₁₂ E₁ E₂ E₃ A X : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hXM : X ≤ M) (hXcard : Nat.card X = q.val)
    (hqτ13 : q ∈ section12Tau1Primes M ∪ section12Tau3Primes M)
    (hA_normX : A ≤ Subgroup.normalizer (X : Set G)) :
    subgroupCentralizerIn (section10Msigma M) X = ⊥ := by
  classical
  haveI : Fact q.val.Prime := ⟨q.2⟩
  have hX_M : X ∈ section10PrimeOrderSubgroupsIn q M := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hXM, hXcard⟩
  have hXp : IsPGroup q.val X := by
    refine IsPGroup.of_card (p := q.val) (G := X) (n := 1) ?_
    simpa [pow_one] using hXcard
  have hXne : X ≠ ⊥ := section12_primeOrder_ne_bot hX_M
  have hXtop : X ≠ ⊤ := section12_primeOrder_ne_top_pre hX_M
  have hnotN :
      ¬ Subgroup.normalizer (X : Set G) ≤ M :=
    section12_not_normalizer_primeOrder_le_M_of_tau13_pre hM hXp hXne hXM hqτ13
  have hNproper : Subgroup.normalizer (X : Set G) ≠ ⊤ :=
    section12_normalizer_ne_top_of_ne_bot_ne_top_pre hXne hXtop
  obtain ⟨Mstar, hMstar⟩ :=
    section12_exists_maximalSubgroupsContaining_of_ne_top_pre (G := G) hNproper
  have hMstar_ne : Mstar ≠ M := by
    intro hEq
    apply hnotN
    simpa [hEq] using hMstar.2
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  have hA_le_Mstar : A ≤ Mstar := hA_normX.trans hMstar.2
  have hσinf :
      section10Msigma M ⊓ Mstar = ⊥ :=
    theorem_12_5_e hM hp hA_M Mstar ⟨hMstar.1, hA_le_Mstar⟩ hMstar_ne
  have hC_le_inf :
      subgroupCentralizerIn (section10Msigma M) X ≤ section10Msigma M ⊓ Mstar := by
    intro y hy
    exact ⟨hy.1, hMstar.2 ((centralizer_le_normalizer X) hy.2)⟩
  exact le_bot_iff.mp (by
    rw [← hσinf]
    exact hC_le_inf)

public theorem CFSG.section12_rankTwo_le_normalizer_of_le_E3_pre
    {M E E₁₂ E₁ E₂ E₃ A X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hXE3 : X ≤ E₃) :
    A ≤ Subgroup.normalizer (X : Set G) := by
  classical
  have hE3cyc : IsCyclic E₃ := (lemma_12_1_d hM hE).2
  haveI : IsCyclic E₃ := hE3cyc
  have hXchar : (X.subgroupOf E₃).Characteristic :=
    section12_subgroup_characteristic_of_cyclic (X.subgroupOf E₃)
  have hNormE3_le_NormX :
      Subgroup.normalizer (E₃ : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    haveI : (X.subgroupOf E₃).Characteristic := hXchar
    have hle :
        Subgroup.normalizer (E₃ : Set G) ≤
          Subgroup.normalizer ((X.subgroupOf E₃).map E₃.subtype : Set G) :=
      section8_normalizer_map_subtype_le_of_characteristic
        (H := E₃) (K := X.subgroupOf E₃)
    have hmap : (X.subgroupOf E₃).map E₃.subtype = X :=
      Subgroup.map_subgroupOf_eq_of_le hXE3
    simpa [hmap] using hle
  have hE3norm : section10NormalIn E₃ E := (lemma_12_1_b hM hE).2
  have hE_le_normE3 : E ≤ Subgroup.normalizer (E₃ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE3norm.1).1 hE3norm.2
  exact (section12_rankTwo_le hA).trans (hE_le_normE3.trans hNormE3_le_NormX)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwo_le_normalizer_of_le_centralizerIn_pre
    {E₁ A X : Subgroup G} (hX : X ≤ subgroupCentralizerIn E₁ A) :
    A ≤ Subgroup.normalizer (X : Set G) := by
  intro a ha
  apply centralizer_le_normalizer X
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxCentA : x ∈ Subgroup.centralizer (A : Set G) := (hX hx).2
  exact (Subgroup.mem_centralizer_iff.mp hxCentA a ha).symm


end Section12
