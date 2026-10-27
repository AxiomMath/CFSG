module

public import CFSG.RankThree.PartTwo.Sec18.Item187Syl
public import CFSG.RankThree.PartTwo.Sec18.Item187F0Basic
public import CFSG.LocalAnalysis.ABGTheoremB.V4Hall

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools CFSG.ABGTheoremB.TotallyInverted
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G} {X : Subgroup G}

theorem exists_invariant_hall_of_coprime {p : ℕ} [Fact p.Prime] {A X U : Subgroup G}
    (hA : IsPGroup p A) (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hX : ¬ p ∣ Nat.card X)
    (hsol : Group.IsSolvable X) (hUX : U ≤ X) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (π : Set Nat.Primes) (hUπ : ∀ q : Nat.Primes, (q : ℕ) ∣ Nat.card U → q ∈ π) :
    ∃ P : Subgroup G, P ≤ X ∧ U ≤ P ∧ A ≤ Subgroup.normalizer (P : Set G) ∧
      (∀ q : Nat.Primes, (q : ℕ) ∣ Nat.card P → q ∈ π) ∧
      (∀ q : Nat.Primes, q ∈ π → ¬ (q : ℕ) ∣ P.relIndex X) := by
  let _ := Omnibus.conjActOn A X hAX
  have hUπ' : CFSG.IsPiSubgroup π (U.subgroupOf X) := by
    intro q hq
    apply hUπ q
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv] at hq
  have hU' : ∀ a : A, ∀ x ∈ U.subgroupOf X, a • x ∈ U.subgroupOf X := by
    intro a x hx
    exact (Subgroup.mem_normalizer_iff.mp (hAU a.2) x).mp hx
  obtain ⟨P₀, hP₀, hP₀inv, hUP₀⟩ := CFSG.SolvableHall.coprime_invariant_hall_containment
    hA hX hsol π (U.subgroupOf X) hUπ' hU'
  refine ⟨P₀.map X.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hUX]
    exact Subgroup.map_mono hUP₀
  · intro a ha
    apply DataConstruction.mem_normalizer_of_conj_mem
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨_, hP₀inv ⟨a, ha⟩ z hz, rfl⟩
  · intro q hq
    rw [Subgroup.card_map_of_injective X.subtype_injective] at hq
    exact hP₀.p_in_pi_of_p_dvd_card q hq
  · intro q hqπ hq
    have : (P₀.map X.subtype).subgroupOf X = P₀ := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    rw [Subgroup.relIndex, this] at hq
    exact hP₀.p_in_pi_of_p_dvd_index q hq hqπ

private theorem exists_isSylowOf_of_index_coprime {r : ℕ} [Fact r.Prime] {K X : Subgroup G}
    (hKX : K ≤ X) (hK : ¬ r ∣ K.relIndex X) : ∃ Q : Subgroup G, IsSylowOf r Q X ∧ Q ≤ K := by
  obtain ⟨Q, hQ⟩ := exists_isSylowOf r K
  obtain ⟨hQK, hQp, hQdvd⟩ := isSylowOf_iff.mp hQ
  refine ⟨Q, isSylowOf_iff.mpr ⟨hQK.trans hKX, hQp, ?_⟩, hQK⟩
  rw [← Subgroup.relIndex_mul_relIndex Q K X hQK hKX]
  intro h
  rcases (Nat.Prime.dvd_mul (Fact.out : Nat.Prime r)).mp h with h1 | h1
  · exact hQdvd h1
  · exact hK h1

theorem MinCex.card_primeFactors_subset (h186 : Item186H) (hX : MinCex A M H c X)
    (hsol : Group.IsSolvable ↥X) (h5 : 5 ∣ Nat.card X) :
    ∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M) with hS
  have hSyl : IsSylowOf 2 S X := isSylowOf_of_mem_scriptX h186 hX.sec18H hX.hyp187 hX.mem
  have hSX : S ≤ X := hSyl.le
  have hS2 : IsPGroup 2 S := hSyl.isPGroup
  have hA3 : IsPGroup 3 A := (isE27_of_mem_partTwoE hX.sec18H.mem_partTwoE).isPGroup
  have hAS : A ≤ Subgroup.normalizer (S : Set G) :=
    le_sup_left.trans (le_normalizer_pCoreOf hX.sec18H)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := le_sup_left.trans hX.le_normalizer
  have h3 : ¬ 3 ∣ Nat.card X := hX.not_three_dvd
  have hSq : ∀ q : Nat.Primes, (q : ℕ) ∣ Nat.card S → (q : ℕ) = 2 := by
    intro q hq
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
    rw [hk] at hq
    exact (Nat.prime_dvd_prime_iff_eq q.2 Nat.prime_two).mp (q.2.dvd_of_dvd_pow hq)
  have hK : ∀ r : ℕ, r.Prime → r ≠ 2 → ∃ K : Subgroup G, K ≤ X ∧ S ≤ K ∧ K ∈ scriptX A M H ∧
      (∀ q : ℕ, q.Prime → q ∣ Nat.card K → q = 2 ∨ q = r) ∧ ¬ r ∣ K.relIndex X := by
    intro r hr hr2
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨K, hKX, hSK, hAK, hKπ, hKidx⟩ := exists_invariant_hall_of_coprime (p := 3) hA3 hAX
      h3 hsol hSX hAS ({(⟨2, Nat.prime_two⟩ : Nat.Primes), ⟨r, hr⟩} : Set Nat.Primes)
      (fun q hq => Set.mem_insert_iff.mpr (Or.inl (Subtype.ext (hSq q hq))))
    refine ⟨K, hKX, hSK, ⟨⟨le_top, isPiSubgroup_of_le hX.isPiSubgroup hKX,
      sup_le hAK (hSK.trans Subgroup.le_normalizer)⟩, hSK⟩, ?_, ?_⟩
    · intro q hq hqK
      rcases Set.mem_insert_iff.mp (hKπ ⟨q, hq⟩ hqK) with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val (Set.mem_singleton_iff.mp h))
    · exact hKidx ⟨r, hr⟩ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  by_cases hA : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ ∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = r
  ·
    obtain ⟨r, -, -, hr⟩ := hA
    have h5r : r = 5 := ((hr 5 Nat.prime_five h5).resolve_left (by norm_num)).symm
    intro q hq hqX
    rcases hr q hq hqX with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans h5r)
  exfalso
  have hlt : ∀ r : ℕ, r.Prime → r ≠ 2 → ∃ K : Subgroup G, K < X ∧ S ≤ K ∧ K ∈ scriptX A M H ∧
      ∃ Q : Subgroup G, IsSylowOf r Q X ∧ Q ≤ K := by
    intro r hr hr2
    obtain ⟨K, hKX, hSK, hKsc, hKπ, hKidx⟩ := hK r hr hr2
    haveI : Fact r.Prime := ⟨hr⟩
    have hKlt : K < X := by
      refine lt_of_le_of_ne hKX fun hKeq => hA ⟨r, hr, hr2, fun q hq hqX => hKπ q hq ?_⟩
      rw [hKeq]
      exact hqX
    exact ⟨K, hKlt, hSK, hKsc, exists_isSylowOf_of_index_coprime hKX hKidx⟩
  set T : Subgroup G := sSup {K : Subgroup G | K ∈ scriptX A M H ∧ K < X} with hT
  have hmemT : ∀ K : Subgroup G, K ∈ scriptX A M H → K < X → K ≤ T :=
    fun K h1 h2 => le_sSup ⟨h1, h2⟩
  have hTX : T ≤ X := sSup_le fun K hK' => (show K ∈ scriptX A M H ∧ K < X from hK').2.le
  have hTN : T ≤ Subgroup.normalizer (inSubgroup perfectResidual H : Set G) :=
    sSup_le fun K hK' => hX.min K (show K ∈ scriptX A M H ∧ K < X from hK').1
      (show K ∈ scriptX A M H ∧ K < X from hK').2
  have hST : S ≤ T := by
    obtain ⟨K, hKlt, hSK, hKsc, -⟩ := hlt 5 Nat.prime_five (by norm_num)
    exact hSK.trans (hmemT K hKsc hKlt)
  have hTeq : T = X := CFSG.ABGTheoremB.V4.eq_of_forall_exists_isSylowOf_le hTX
    fun q hq _ => by
      by_cases hq2 : q = 2
      · subst hq2
        exact ⟨S, hSyl, hST⟩
      · obtain ⟨K, hKlt, -, hKsc, Q, hQ, hQK⟩ := hlt q hq hq2
        exact ⟨Q, hQ, hQK.trans (hmemT K hKsc hKlt)⟩
  exact hX.not_le (hTeq.symm.le.trans hTN)

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
