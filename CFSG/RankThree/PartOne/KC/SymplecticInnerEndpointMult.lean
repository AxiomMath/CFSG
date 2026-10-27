module

public import CFSG.RankThree.PartOne.KC.SymplecticMultiplicity

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

@[expose] def SpLiftMultiplicitiesCoprime {r : ℕ} {K : Type} [Field K] (p : ℕ)
    (A : Subgroup (MulAut (StatedProj (StatedSp r K)))) : Prop :=
  ∀ x : StatedSp r K, orderOf x = p → MulAut.conj (proj r K x) ∈ A →
    MulAut.conj (proj r K x) ≠ 1 →
      ∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
        ¬ p ∣ primaryMultiplicity (spEnd x) (h : K[X])

theorem spLiftMultiplicitiesCoprime_of_cover {G : Type*} [Group G] [Finite G] (Y : Subgroup G)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = ℓ ^ f)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) {r : ℕ} (hr : 2 ≤ r)
    (hrank : localRank p G ≤ 3) (φ : Y →* StatedProj (StatedSp r K))
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (A : Subgroup (MulAut (StatedProj (StatedSp r K)))) : SpLiftMultiplicitiesCoprime p A := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro x hxp _ hx1 h hh hdvd
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero f hℓ.ne_zero
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  have hcharK : CharP K ℓ := by
    have := Fintype.ofFinite K
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hK])
  have hpK : (p : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K ℓ] at h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h0).symm
  have hxpow : x ^ p = 1 := by
    rw [← hxp]
    exact pow_orderOf_eq_one x
  have hproj1 : proj r K x ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
  have ha : orderOf (proj r K x) = p :=
    orderOf_eq_prime (by rw [← map_pow, hxpow, map_one]) hproj1
  have hmain := symplectic_primary_multiplicity_actual_central_cover_local_rank Y hℓ hf hK hp hp3
    hpℓ hr φ hφ hker (proj r K x) ha x rfl hxp h hh
  have hlt : primaryMultiplicity (spEnd x) (h : K[X]) < p := (hmain.2 hrank).2
  have hsq : Squarefree (minpoly K (spEnd x)) := (altPrimaryData_spLin hpK hxpow).squarefree
  have hpos : 0 < primaryMultiplicity (spEnd x) (h : K[X]) := by
    have hne' := primaryComponent_ne_bot hsq h.2
    have : Nontrivial ↥(primaryComponent (spEnd x) (h : K[X])) :=
      Submodule.nontrivial_iff_ne_bot.mpr hne'
    have : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors h.2⟩
    exact Module.finrank_pos
  have := Nat.le_of_dvd hpos hdvd
  omega

end CFSG.RankThree.PartOne
