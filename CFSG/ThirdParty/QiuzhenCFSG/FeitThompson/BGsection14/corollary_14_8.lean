module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection14.theorem_14_7

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Corollary 14 8 from BG Section 14 -/

section Section14

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_subgroupPrimeSet_conjBy
    (M : Subgroup G) (a : G) :
    subgroupPrimeSet (M.conjBy a) = subgroupPrimeSet M := by
  ext p
  rw [subgroupPrimeSet, subgroupPrimeSet]
  simp [section14_card_conjBy (G := G) M a]

omit [IsMinCE G] in
public theorem CFSG.section14_primeRank_conjBy_eq
    (M : Subgroup G) (q : ℕ) (a : G) :
    primeRank q (M.conjBy a) = primeRank q M := by
  let e : M ≃* M.conjBy a := (MulAut.conj a).subgroupMap M
  exact le_antisymm
    (section14_primeRank_le_of_equiv (q := q) e)
    (section14_primeRank_le_of_equiv (q := q) e.symm)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_derived_card_conjBy
    (M : Subgroup G) (a : G) :
    Nat.card (derivedSubgroup (M.conjBy a)) = Nat.card (derivedSubgroup M) := by
  let e : M ≃* M.conjBy a := (MulAut.conj a).subgroupMap M
  have hmap :
      (derivedSubgroup M).map e.toMonoidHom = derivedSubgroup (M.conjBy a) := by
    change (derivedSeries M 1).map e.toMonoidHom = derivedSeries (M.conjBy a) 1
    exact map_derivedSeries_eq (f := e.toMonoidHom) e.surjective 1
  calc
    Nat.card (derivedSubgroup (M.conjBy a)) =
        Nat.card ((derivedSubgroup M).map e.toMonoidHom) := by
          rw [← hmap]
    _ = Nat.card (derivedSubgroup M) :=
      Subgroup.card_map_of_injective e.injective

omit [IsMinCE G] in
private theorem CFSG.section14_tau1Primes_conjBy
    (M : Subgroup G) (a : G) :
    section12Tau1Primes (M.conjBy a) = section12Tau1Primes M := by
  ext p
  constructor <;> intro hp
  · rw [section12Tau1Primes] at hp ⊢
    refine ⟨?_, ?_, ?_⟩
    · intro hpσ
      exact hp.1 (section14_sigma_mem_conjBy (L := M) hpσ a)
    · intro hpder
      have hpder' : p ∈ subgroupPrimeSet (derivedSubgroup (M.conjBy a)) := by
        rw [subgroupPrimeSet]
        rw [section14_derived_card_conjBy (G := G) M a]
        simpa [subgroupPrimeSet] using hpder
      exact hp.2.1 hpder'
    · simpa [section14_primeRank_conjBy_eq (G := G) M p.val a] using hp.2.2
  · rw [section12Tau1Primes] at hp ⊢
    refine ⟨?_, ?_, ?_⟩
    · intro hpσ
      have hpBack := section14_sigma_mem_conjBy (L := M.conjBy a) hpσ a⁻¹
      exact hp.1 (by simpa [section11_conjBy_inv] using hpBack)
    · intro hpder
      have hpder' : p ∈ subgroupPrimeSet (derivedSubgroup M) := by
        rw [subgroupPrimeSet] at hpder ⊢
        rw [section14_derived_card_conjBy (G := G) M a] at hpder
        exact hpder
      exact hp.2.1 hpder'
    · simpa [section14_primeRank_conjBy_eq (G := G) M p.val a] using hp.2.2

omit [IsMinCE G] in
private theorem CFSG.section14_tau3Primes_conjBy
    (M : Subgroup G) (a : G) :
    section12Tau3Primes (M.conjBy a) = section12Tau3Primes M := by
  ext p
  constructor <;> intro hp
  · rw [section12Tau3Primes] at hp ⊢
    refine ⟨?_, ?_, ?_⟩
    · intro hpσ
      exact hp.1 (section14_sigma_mem_conjBy (L := M) hpσ a)
    · rw [subgroupPrimeSet]
      rw [← section14_derived_card_conjBy (G := G) M a]
      simpa [subgroupPrimeSet] using hp.2.1
    · simpa [section14_primeRank_conjBy_eq (G := G) M p.val a] using hp.2.2
  · rw [section12Tau3Primes] at hp ⊢
    refine ⟨?_, ?_, ?_⟩
    · intro hpσ
      have hpBack := section14_sigma_mem_conjBy (L := M.conjBy a) hpσ a⁻¹
      exact hp.1 (by simpa [section11_conjBy_inv] using hpBack)
    · rw [subgroupPrimeSet]
      rw [section14_derived_card_conjBy (G := G) M a]
      simpa [subgroupPrimeSet] using hp.2.1
    · simpa [section14_primeRank_conjBy_eq (G := G) M p.val a] using hp.2.2

omit [IsMinCE G] in
public theorem CFSG.section14_tau2Primes_conjBy
    (M : Subgroup G) (a : G) :
    section12Tau2Primes (M.conjBy a) = section12Tau2Primes M := by
  ext p
  constructor <;> intro hp
  · rw [section12Tau2Primes] at hp ⊢
    refine ⟨?_, ?_⟩
    · intro hpσ
      exact hp.1 (section14_sigma_mem_conjBy (L := M) hpσ a)
    · simpa [section14_primeRank_conjBy_eq (G := G) M p.val a] using hp.2
  · rw [section12Tau2Primes] at hp ⊢
    refine ⟨?_, ?_⟩
    · intro hpσ
      have hpBack := section14_sigma_mem_conjBy (L := M.conjBy a) hpσ a⁻¹
      exact hp.1 (by simpa [section11_conjBy_inv] using hpBack)
    · simpa [section14_primeRank_conjBy_eq (G := G) M p.val a] using hp.2

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_primeOrderSubgroupsIn_conjBy
    {M X : Subgroup G} {p : Nat.Primes}
    (a : G) (hX : X ∈ section10PrimeOrderSubgroupsIn p M) :
    X.conjBy a ∈ section10PrimeOrderSubgroupsIn p (M.conjBy a) := by
  refine ⟨Subgroup.map_mono hX.1, ?_⟩
  simpa [section14_card_conjBy (G := G) X a] using hX.2

omit [IsMinCE G] in
private theorem CFSG.section14_mem_kappaPrimes_conjBy
    {M : Subgroup G} {p : Nat.Primes}
    (a : G) (hp : p ∈ section14KappaPrimes M) :
    p ∈ section14KappaPrimes (M.conjBy a) := by
  rcases hp with ⟨hpτ, P, hP, hC⟩
  refine ⟨?_, P.conjBy a, section14_primeOrderSubgroupsIn_conjBy (G := G) a hP, ?_⟩
  · rcases hpτ with hpτ1 | hpτ3
    · exact Or.inl <| by
        simpa [section14_tau1Primes_conjBy (G := G) M a] using hpτ1
    · exact Or.inr <| by
        simpa [section14_tau3Primes_conjBy (G := G) M a] using hpτ3
  · simpa [section14_msigma_conjBy (G := G) M a] using
      (section11_subgroupCentralizerIn_conjBy_ne_bot
        (R := section10Msigma M) (X := P) (g := a) hC)

omit [IsMinCE G] in
public theorem CFSG.section14_kappaPrimes_conjBy
    (M : Subgroup G) (a : G) :
    section14KappaPrimes (M.conjBy a) = section14KappaPrimes M := by
  ext p
  constructor
  · intro hp
    have hp' :=
      section14_mem_kappaPrimes_conjBy
        (G := G) (M := M.conjBy a) (p := p) a⁻¹ hp
    simpa [section11_conjBy_inv] using hp'
  · intro hp
    exact section14_mem_kappaPrimes_conjBy (G := G) (M := M) (p := p) a hp

omit [IsMinCE G] in
public theorem CFSG.section14_mem_P_conjBy
    {M : Subgroup G}
    (a : G) (hM : M ∈ section14MFamilyP G) :
    M.conjBy a ∈ section14MFamilyP G := by
  rcases hM with ⟨hMmax, hp⟩
  rcases hp with ⟨p, hp⟩
  exact ⟨section14_maximal_conjBy (G := G) hMmax a,
    ⟨p, section14_mem_kappaPrimes_conjBy (G := G) (M := M) (p := p) a hp⟩⟩


omit [IsMinCE G] in
private theorem CFSG.section14_mem_P2_conjBy
    {M : Subgroup G}
    (a : G) (hM : M ∈ section14MFamilyP2 G) :
    M.conjBy a ∈ section14MFamilyP2 G := by
  refine ⟨section14_mem_P_conjBy (G := G) (M := M) a hM.1, ?_⟩
  intro hEq
  apply hM.2
  calc
    section14KappaPrimes M = section14KappaPrimes (M.conjBy a) := by
      symm
      exact section14_kappaPrimes_conjBy (G := G) M a
    _ = subgroupPrimeSet (M.conjBy a) \ section10SigmaPrimes (M.conjBy a) := hEq
    _ = subgroupPrimeSet M \ section10SigmaPrimes M := by
      rw [section14_subgroupPrimeSet_conjBy (G := G) M a,
        section14_sigmaPrimes_conjBy (G := G) M a]

omit [IsMinCE G] in
public theorem CFSG.section14_mem_P2_of_conjugate
    {H M : Subgroup G}
    (hHM : section14ConjugateSubgroups H M)
    (hM : M ∈ section14MFamilyP2 G) :
    H ∈ section14MFamilyP2 G := by
  rcases hHM with ⟨a, rfl⟩
  exact section14_mem_P2_conjBy (G := G) (M := M) a hM


end Section14
