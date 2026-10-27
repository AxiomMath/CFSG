module

public import CFSG.RankThree.PartOne.KE.CTCasesBasic
public import CFSG.RankThree.PartOne.KE.CTCasesE6Arith
public import CFSG.RankThree.SteinbergR3EOrdinaryECrossPrimeParts
public import CFSG.RankThree.PartOne.KE.CTStatement

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix Module

theorem exists_annihilator_of_index {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (Λ : Submodule ℤ (Fin n → ℤ)) {p : ℕ} (x : ℤ)
    (h : ¬ (p : ℤ) ∣ (Λ.toAddSubgroup.index : ℤ)) :
    ∃ A : ℤ[X], (∀ β, (aeval M A) *ᵥ β ∈ Λ) ∧ ¬ (p : ℤ) ∣ A.eval x :=
  ⟨C (Λ.toAddSubgroup.index : ℤ), fun β => annihilator_of_index M Λ rfl β, by simpa using h⟩

theorem exists_annihilator_of_quotient {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (Λ : Submodule ℤ (Fin n → ℤ)) (h : ratSpan Λ ≤ (ratSpan Λ).comap (ratEnd M)) (g : ℤ[X])
    (hg : ((ratSpan Λ).mapQ _ (ratEnd M) h).charpoly = g.map (Int.castRingHom ℚ)) {p : ℕ}
    (x : ℤ) (hx : ¬ (p : ℤ) ∣ (satIndex Λ : ℤ) * g.eval x) :
    ∃ A : ℤ[X], (∀ β, (aeval M A) *ᵥ β ∈ Λ) ∧ ¬ (p : ℤ) ∣ A.eval x := by
  have hd : satIndex Λ ≠ 0 := fun h0 => hx (by simp [h0])
  exact ⟨C (satIndex Λ : ℤ) * g, fun β => annihilator_of_quotient_charpoly M Λ h g hg hd β,
    by simpa using hx⟩

theorem saturation_eq_top_of_basis {n k : ℕ} (hk : k = n) {Λ : Submodule ℤ (Fin n → ℤ)}
    {f : Fin k → (Fin n → ℤ)} (hf : LinearIndependent ℤ f)
    (hspan : Submodule.span ℤ (Set.range f) = Λ) : saturation Λ = ⊤ := by
  subst hk
  have h1 : LinearIndependent ℤ (castLin k ∘ f) :=
    hf.map' (castLin k) (LinearMap.ker_eq_bot.2 castLin_injective)
  have h2 : LinearIndependent ℚ (castLin k ∘ f) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 h1
  have h3 : Submodule.span ℚ (Set.range (castLin k ∘ f)) = ⊤ :=
    h2.span_eq_top_of_card_eq_finrank' (by simp)
  have h4 : Submodule.span ℚ (Set.range (castLin k ∘ f)) ≤ ratSpan Λ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨f j, hspan ▸ Submodule.subset_span ⟨j, rfl⟩, rfl⟩
  rw [h3, top_le_iff] at h4
  refine eq_top_iff.2 fun v _ => ?_
  rw [mem_saturation, h4]
  exact Submodule.mem_top

theorem ordProj_card_adjointGroup_E6 {K : Type} [Field K] [Finite K] {p m d₀ n₀ : ℕ} {R : ℤ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = m)
    (hd₀ : d₀ ∈ ([2, 5, 6, 8, 9, 12] : List ℕ))
    (hrest : ∀ d ∈ ([2, 5, 6, 8, 9, 12] : List ℕ), d ≠ d₀ → ¬ m ∣ d)
    (hn₀ : n₀ ≠ 0) (hfac : ((Nat.card K ^ d₀ - 1 : ℕ) : ℤ) = n₀ * R) (hR : ¬ (p : ℤ) ∣ R) :
    ordProj[p] (Nat.card (adjointGroup .E6 K)) = ordProj[p] n₀ := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hd₀pos : 0 < d₀ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd₀
    omega
  have hN : Nat.card K ^ d₀ - 1 ≠ 0 := by
    have : 1 < Nat.card K ^ d₀ := Nat.one_lt_pow hd₀pos.ne' (by omega)
    omega
  rw [(CFSG.RankThree.OrdinaryECrossPrime.ordinary_E_exact_cross_prime_order_parts hp hp3 hpq).1,
    CTE6.prod_map_ordProj_eq_single (by omega) hord (by decide) hd₀ hrest]
  exact CTE6.ordProj_eq_of_int_factor hn₀ hN hfac hR

theorem ordProj_card_adjointGroup_E7 {K : Type} [Field K] [Finite K] {p m d₀ n₀ : ℕ} {R : ℤ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = m)
    (hd₀ : d₀ ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ))
    (hrest : ∀ d ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ), d ≠ d₀ → ¬ m ∣ d)
    (hn₀ : n₀ ≠ 0) (hfac : ((Nat.card K ^ d₀ - 1 : ℕ) : ℤ) = n₀ * R) (hR : ¬ (p : ℤ) ∣ R) :
    ordProj[p] (Nat.card (adjointGroup .E7 K)) = ordProj[p] n₀ := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hd₀pos : 0 < d₀ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd₀
    omega
  have hN : Nat.card K ^ d₀ - 1 ≠ 0 := by
    have : 1 < Nat.card K ^ d₀ := Nat.one_lt_pow hd₀pos.ne' (by omega)
    omega
  rw [(CFSG.RankThree.OrdinaryECrossPrime.ordinary_E_exact_cross_prime_order_parts hp hp3 hpq).2.1,
    CTE6.prod_map_ordProj_eq_single (by omega) hord (by decide) hd₀ hrest]
  exact CTE6.ordProj_eq_of_int_factor hn₀ hN hfac hR

theorem cyclic_sylow_of_inputs (hmain : CyclicTorusTheorem) {τ : Tag} {d : ℕ}
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hM : IsWeylMatrix τ M) {v : Fin τ.rank → ℤ}
    (hv1 : LinearIndependent ℤ (fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v))
    (hv2 : Submodule.span ℤ (Set.range fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v) = ⊤)
    (hc0 : M.charpoly.coeff 0 = 1 ∨ M.charpoly.coeff 0 = -1)
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hpq : ¬ p ∣ Nat.card K) {n₀ : ℕ} (hn₀ : n₀ ≠ 0)
    (hev : M.charpoly.eval (Nat.card K : ℤ) = (n₀ : ℤ))
    (hann : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → ∃ A : ℤ[X],
      (∀ β, (aeval M A) *ᵥ β ∈ orbitLattice M α) ∧ ¬ (p : ℤ) ∣ A.eval (Nat.card K : ℤ))
    (hpart : ordProj[p] (Nat.card (adjointGroup τ K)) = ordProj[p] n₀) :
    CyclicSylowConclusion τ K p n₀ d := by
  have hnat : (M.charpoly.eval (Nat.card K : ℤ)).natAbs = n₀ := by
    rw [hev, Int.natAbs_natCast]
  have hne : M.charpoly.eval (Nat.card K : ℤ) ≠ 0 := by
    rw [hev]
    exact_mod_cast hn₀
  have key := hmain τ d hτ M hM v hv1 hv2 hc0 K p hp hp7 hpq hne hann (by rw [hnat]; exact hpart)
  rwa [hnat] at key

end CFSG.RankThree.PartOne.KE
