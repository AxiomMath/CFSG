module

public import CFSG.RankThree.PartOne.Mult.PPart
public import CFSG.RankThree.PartOne.S11c.Sec68
public import CFSG.RankThree.OddKernel.SporadicKernelRestrictionB

public section

namespace CFSG.RankThree.PartOne.Mult

open CFSG CFSG.Blueprint Subgroup CFSG.RankThree.OddKernel CFSG.RankThree.PartOne

@[expose] def SporadicKernelTrivial (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (S : Type) [Group S] (π : E →* S),
    NativeSporadic.IsSporadic S s → Function.Surjective π → π.ker ≤ Subgroup.center E →
      IsPGroup p π.ker → π.ker = ⊥

structure SporadicResidualKernels : Prop where
  co1_five : SporadicKernelTrivial .Co1 5
  co1_seven : SporadicKernelTrivial .Co1 7
  fi24_five : SporadicKernelTrivial .Fi24Prime 5
  fi24_seven : SporadicKernelTrivial .Fi24Prime 7
  th_five : SporadicKernelTrivial .Th 5
  th_seven : SporadicKernelTrivial .Th 7
  b_five : SporadicKernelTrivial .B 5
  b_seven : SporadicKernelTrivial .B 7
  co2_five : SporadicKernelTrivial .Co2 5
  co3_five : SporadicKernelTrivial .Co3 5
  fi22_five : SporadicKernelTrivial .Fi22 5
  fi23_five : SporadicKernelTrivial .Fi23 5
  mcl_five : SporadicKernelTrivial .McL 5
  suz_five : SporadicKernelTrivial .Suz 5
  hn_five : SporadicKernelTrivial .HN 5
  ly_five : SporadicKernelTrivial .Ly 5
  on_seven : SporadicKernelTrivial .ONan 7
  monster : ∀ p : ℕ, p.Prime → 3 < p → SporadicKernelTrivial .M p

@[expose] def SporadicResidualPair (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  (p = 5 ∧ s ∈ ({.Co1, .Fi24Prime, .Th, .B, .Co2, .Co3, .Fi22, .Fi23, .McL, .Suz, .HN, .Ly} :
      Set TauCeti.SporadicName)) ∨
    (p = 7 ∧ s ∈ ({.Co1, .Fi24Prime, .Th, .B, .ONan} : Set TauCeti.SporadicName)) ∨ s = .M

theorem SporadicResidualKernels.trivial_of_pair (hres : SporadicResidualKernels)
    {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : SporadicResidualPair s p) :
    SporadicKernelTrivial s p := by
  rcases h with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | rfl
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hres.co1_five
    · exact hres.fi24_five
    · exact hres.th_five
    · exact hres.b_five
    · exact hres.co2_five
    · exact hres.co3_five
    · exact hres.fi22_five
    · exact hres.fi23_five
    · exact hres.mcl_five
    · exact hres.suz_five
    · exact hres.hn_five
    · exact hres.ly_five
  · rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact hres.co1_seven
    · exact hres.fi24_seven
    · exact hres.th_seven
    · exact hres.b_seven
    · exact hres.on_seven
  · exact hres.monster p hp hp3

theorem sporadic_residual_of_center
    
    {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {s : TauCeti.SporadicName}
    (e : K ⧸ center K ≃* NativeSporadic.Carrier s) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpZ : p ∣ Nat.card (center K)) :
    SporadicResidualPair s p ∧ (SporadicKernelTrivial s p → False) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨N, hNn, π, hperf, -, hsurj, hker, hpg, hne⟩ := exists_central_p_extension (K := K) hpZ
  have : Group.IsPerfect (K ⧸ N) := hperf
  have hcop := coprime_six_card_of_isPGroup hp hp3 hpg
  obtain ⟨h1, h2, h3, h4, -⟩ :=
    twenty_five_sporadic_central_prime_to_six_kernel_restriction π hsurj hker hcop
  have hS : NativeSporadic.IsSporadic (K ⧸ center K) s := ⟨e⟩
  have hpk : p ∣ Nat.card π.ker := by
    obtain ⟨k, hk⟩ := hpg.exists_card_eq
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact absurd (Subgroup.card_eq_one.mp hk) hne
    · rw [hk]
      exact dvd_pow_self p k.succ_ne_zero
  have hnot : SporadicKernelTrivial s p → False := fun htr =>
    hne (htr (K ⧸ N) (K ⧸ center K) π hS hsurj hker hpg)
  refine ⟨?_, hnot⟩
  have hcases : s ∈ ({.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .HS, .He, .Ru} :
        Set TauCeti.SporadicName) ∨ s ∈ ({.Co1, .Fi24Prime, .Th, .B} : Set TauCeti.SporadicName) ∨
      s ∈ ({.Co2, .Co3, .Fi22, .Fi23, .McL, .Suz, .HN, .Ly} : Set TauCeti.SporadicName) ∨
      s = .ONan ∨ s = .M := by
    cases s <;> simp
  rcases hcases with hs | hs | hs | rfl | rfl
  · exact absurd (h1 s hs hS) hne
  · have h57 := h2 s hs hS p hp hpk
    rcases h57 with rfl | rfl
    · exact Or.inl ⟨rfl, by rcases hs with rfl | rfl | rfl | rfl <;> simp⟩
    · exact Or.inr (Or.inl ⟨rfl, by rcases hs with rfl | rfl | rfl | rfl <;> simp⟩)
  · have h5 := h3 s hs hS p hp hpk
    subst h5
    exact Or.inl ⟨rfl, by rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp⟩
  · have h7 := h4 hS p hp hpk
    subst h7
    exact Or.inr (Or.inl ⟨rfl, by simp⟩)
  · exact Or.inr (Or.inr rfl)

theorem sporadicCenterSmallPrimes_of_residual
    
    (hres : SporadicResidualKernels) : SporadicCenterSmallPrimes := by
  intro K _ _ hK hrep p hp hp3 hpZ
  obtain ⟨s, ⟨e⟩⟩ := hrep
  have : Group.IsPerfect K := hK.1
  obtain ⟨hpair, hnot⟩ := sporadic_residual_of_center e hp hp3 hpZ
  exact hnot (hres.trivial_of_pair hp hp3 hpair)

end CFSG.RankThree.PartOne.Mult
