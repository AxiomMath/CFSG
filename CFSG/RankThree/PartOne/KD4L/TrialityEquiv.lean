module

public import CFSG.RankThree.PartOne.KD4L.TrialityLayer

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

section Equiv

variable {τ : Tag} [hτ : E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ] {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)} {e : ℕ}

theorem StdTwist.exists_graph_equiv (h : StdTwist n₁ π e) (hf : 1 ≤ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (ℓ ^ f) ^ 3 ∧
      (∀ c, σ c = c ^ ((ℓ ^ f) ^ e)) ∧
      Nonempty (stdLayer ℓ f n₁ ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hℓ : ℓ.Prime := Fact.out
  set K := frobeniusFixedField L ℓ (3 * f) with hKdef
  have hKc : Nat.card K = (ℓ ^ f) ^ 3 := by
    rw [card_frobeniusFixedField (by omega), ← pow_mul, mul_comm]
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hKc]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  let σ₀ : K →+* K := iterateFrobenius K ℓ (f * e)
  have hσ₀ : ∀ c, σ₀ c = c ^ ((ℓ ^ f) ^ e) := fun c => by
    rw [iterateFrobenius_def, ← pow_mul]
  obtain ⟨φ, -⟩ := exists_d4ThetaFixed_equiv' (K := K) (Ω := L) (σ := σ₀)
    (Fr := iterateFrobenius L ℓ f) hℓ hf hKc h.he hσ₀ (fun c => iterateFrobenius_def ℓ f c)
  have hbij : Function.Bijective σ₀ := Finite.injective_iff_bijective.1 σ₀.injective
  refine ⟨K, inferInstance, hKfin, RingEquiv.ofBijective σ₀ hbij, hKc, hσ₀, ⟨?_⟩⟩
  exact h.layerEquiv.trans φ

theorem layer_graph_equiv_of_standard (hf : 1 ≤ f) (hstd : StdTwist n₁ π e) {h n : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (ℓ ^ f) ^ 3 ∧
      (∀ c, σ c = c ^ ((ℓ ^ f) ^ e)) ∧
      Nonempty (P ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hmem : ∀ g : ModGL τ L, g ∈ P ↔ h * g * h⁻¹ ∈ stdLayer ℓ f n₁ := fun g => by
    rw [hP, Subgroup.mem_inf, mem_stdLayer, mem_twistedFixedPoints, hlang g]
    refine and_congr_left fun _ => ⟨fun hg => mul_mem (mul_mem hh hg) (inv_mem hh), fun hg => ?_⟩
    have := mul_mem (mul_mem (inv_mem hh) hg) hh
    simpa [mul_assoc] using this
  let eP : P ≃* stdLayer ℓ f n₁ :=
    { toFun := fun g => ⟨h * g * h⁻¹, (hmem g).1 g.2⟩
      invFun := fun u => ⟨h⁻¹ * u * h, (hmem _).2 (by simp [mul_assoc])⟩
      left_inv := fun g => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  obtain ⟨K, hK, hKf, σ, hKc, hσ, ⟨e'⟩⟩ := hstd.exists_graph_equiv (ℓ := ℓ) hf
  exact ⟨K, hK, hKf, σ, hKc, hσ, ⟨eP.trans e'⟩⟩

theorem triality_layer_graph_equiv (hf : 1 ≤ f) (π : Equiv.Perm (Fin τ.rank)) (e : ℕ)
    (he : e = 1 ∨ e = 2) (hπe : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (rhoE e k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (ℓ ^ f) ^ 3 ∧
      (∀ c, σ c = c ^ ((ℓ ^ f) ^ e)) ∧
      Nonempty (P ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdTwist n₁ π e := ⟨he, hπe, hπ, hπ', hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact layer_graph_equiv_of_standard hf hstd hh hlang hP

end Equiv

section Final

theorem d4_layer_equiv_E8 {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (hf : 1 ≤ f) (a b c : Fin Tag.E8.rank) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ha : a.val ∈ ({1, 2, 4} : Set ℕ)) (hb : b.val ∈ ({1, 2, 4} : Set ℕ))
    (hc : c.val ∈ ({1, 2, 4} : Set ℕ)) (n : ModGL Tag.E8 L) (hn : n ∈ monomialSubgroup Tag.E8 L)
    (hact : ∃ u ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8),
      ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
        weylQuotientHom Tag.E8 L ⟨n, hn⟩ • α = u • permLattice (List.formPerm [a, b, c]) α)
    (P : Subgroup (ModGL Tag.E8 L))
    (hP : P = rootSpan Tag.E8 L (parabolicRoots Tag.E8 (d4Nodes Tag.E8)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (ℓ ^ f) ^ 3 ∧
      ((∀ c, σ c = c ^ ℓ ^ f) ∨ ∀ c, σ c = c ^ (ℓ ^ f) ^ 2) ∧
      Nonempty (P ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have ha' : a.val = 1 ∨ a.val = 2 ∨ a.val = 4 := by simpa using ha
  have hb' : b.val = 1 ∨ b.val = 2 ∨ b.val = 4 := by simpa using hb
  have hc' : c.val = 1 ∨ c.val = 2 ∨ c.val = 4 := by simpa using hc
  obtain ⟨hcyc, hπ, hπ'⟩ := leafCycle_E8 a b c ha' hb' hc' hab hbc hac
  rcases hcyc with h1 | h2
  · obtain ⟨K, hK, hKf, σ, hKc, hσ, hE⟩ := triality_layer_graph_equiv hf (List.formPerm [a, b, c])
      1 (Or.inl rfl) h1 (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact P hP
    exact ⟨K, hK, hKf, σ, hKc, Or.inl (fun x => by simpa using hσ x), hE⟩
  · obtain ⟨K, hK, hKf, σ, hKc, hσ, hE⟩ := triality_layer_graph_equiv hf (List.formPerm [a, b, c])
      2 (Or.inr rfl) h2 (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact P hP
    exact ⟨K, hK, hKf, σ, hKc, Or.inr hσ, hE⟩

end Final

end CFSG.RankThree.PartOne.KD4L
