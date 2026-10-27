module

public import CFSG.RankThree.PartOne.TCX.E.ExchangeFamily
public import CFSG.RankThree.PartOne.TCX.E.AnFamily
public import CFSG.RankThree.PartOne.KE.FiniteFieldAlgClosure
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family
public import CFSG.RankThree.PartOne.TCX.E.ExchangeBlock

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.E

open Matrix CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KLCE
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups Pointwise

section Fields

theorem exists_frobenius_aut {k : Type} [Field k] [Finite k] {p g : ℕ} (hp : p.Prime) (hg : 1 ≤ g)
    (hk : Nat.card k = 2 ^ (p * g)) : ∃ σ : k ≃+* k, orderOf σ = p ∧ ∀ a, σ a = a ^ 2 ^ g := by
  have hpg : 1 ≤ p * g := Nat.mul_pos hp.pos hg
  obtain ⟨φ, hφ, hφord, -, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hpg hk
  refine ⟨φ ^ g, ?_, pow_apply_of_squaring hφ g⟩
  rw [orderOf_pow' _ (by omega : g ≠ 0), hφord, Nat.gcd_eq_right (dvd_mul_left g p)]
  exact Nat.mul_div_cancel p hg

theorem exists_squared_fields {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L 2] {p f₀ : ℕ} (hp : p.Prime) (hf₀ : 1 ≤ f₀) :
    ∃ (K₀' : Type) (_ : Field K₀') (_ : Algebra K₀' L) (K₂ : Type) (_ : Field K₂)
      (_ : Finite K₂) (_ : Algebra K₂ L) (σ : K₂ ≃+* K₂),
      IsAlgClosure K₀' L ∧ IsAlgClosure K₂ L ∧ Nat.card K₀' = 2 ^ (2 * f₀) ∧
      Nat.card K₂ = 2 ^ (p * (2 * f₀)) ∧ orderOf σ = p ∧
      ∀ c, iterateFrobenius L 2 (2 * f₀) (algebraMap K₂ L c) = algebraMap K₂ L (σ c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K₀', h₀, a₀, hac₀, hc₀⟩ := exists_finite_field_isAlgClosure 2 (2 * f₀) (by omega) K L
  obtain ⟨K₂, h₂, a₂, hac₂, hc₂⟩ :=
    exists_finite_field_isAlgClosure 2 (p * (2 * f₀)) (Nat.mul_pos hp.pos (by omega)) K L
  have hfin : Finite K₂ := Nat.finite_of_card_ne_zero (by rw [hc₂]; positivity)
  obtain ⟨σ, hσord, hσ⟩ := exists_frobenius_aut (k := K₂) hp (by omega : 1 ≤ 2 * f₀) hc₂
  refine ⟨K₀', h₀, a₀, K₂, h₂, hfin, a₂, σ, hac₀, hac₂, hc₀, hc₂, hσord, fun c => ?_⟩
  rw [iterateFrobenius_def, ← map_pow, hσ]

end Fields

section Block

variable {τ : Tag} {S : Set (Fin τ.rank → ℤ)} {m : ℕ}

theorem an_block (E : AnEmbedding τ (m + 3) S) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (π : Equiv.Perm (Fin (m + 3))) {k L : Type} [Field k] [Field L] [Algebra k L]
    [IsAlgClosure k L] [CharP L 2] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hq2 : δ = -1 → m + 3 ≠ 3 ∨ 2 < 2 ^ f) (n : ModGL τ L) (hnm : n ∈ monomialSubgroup τ L)
    (hWs : δ = 1 → ∀ i j, i ≠ j → weylQuotientHom τ L ⟨n, hnm⟩ • E.r i j = E.r (π i) (π j))
    (hWu : δ = -1 → ∀ i j, i ≠ j → weylQuotientHom τ L ⟨n, hnm⟩ • E.r i j = E.r (π j) (π i)) :
    Finite ↥(rootSpan τ L S ⊓ twistedFixedPoints n
        (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) ∧
      CFSG.IsQuasisimple ↥(rootSpan τ L S ⊓ twistedFixedPoints n
        (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) ∧
      ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S,
        (∀ u ∈ rootSpan τ L S ⊓ twistedFixedPoints n
          (Units.map (entrywiseHom (iterateFrobenius L 2 f))), y * u = u * y) →
        y ∈ torusGroup τ L ∧ y ∈ Subgroup.centralizer (rootSpan τ L S : Set (ModGL τ L)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  set Fr : L →+* L := iterateFrobenius L 2 f with hFrdef
  have hFrc : ∀ c, Fr c = c ^ 2 ^ f := fun c => iterateFrobenius_def 2 f c
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < 2 ^ f by positivity)
    exact ⟨x, by rw [hFrc, hx]⟩⟩
  have hS3 : ∀ r ∈ S, IsRoot τ r := fun x hx => by
    obtain ⟨i, j, hij, rfl⟩ := (E.mem x).1 hx
    exact E.isRoot i j hij
  choose! ε hε using fun (i j : Fin (m + 3)) (hij : i ≠ j) => E.gen L i j hij
  rcases hδ with rfl | rfl
  · have hconj : ∀ i j : Fin (m + 3), i ≠ j → ∃ b : Lˣ, ∀ c : L,
        n * pinnedX τ L (E.r i j) c * n⁻¹ = pinnedX τ L (E.r (π i) (π j)) ((b : L) * c) :=
      fun i j hij => by
        obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (E.isRoot i j hij)
        exact ⟨μ, fun c => by rw [hμ c, hWs rfl i j hij]⟩
    obtain ⟨Θ', hΘ', b, hshape⟩ := exists_aut_of_rootData_n (E.ρ L) (E.inj L) E.r ε hε Fr hFrbij
      n (fun i j => (π i, π j)) (fun i j hij => π.injective.ne hij)
      (fun i j hij => ⟨π.symm i, π.symm j, π.symm.injective.ne hij, by simp⟩) hconj
    have hshape' : ∀ (i j : Fin (m + 3)) (hij : i ≠ j) (t : L),
        ((Θ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(m + 3, L)) :
          Matrix (Fin (m + 3)) (Fin (m + 3)) L) =
        1 + single (π i) (π j) ((b i j : L) * t ^ 2 ^ f) :=
      fun i j hij t => by rw [hshape i j hij t, hFrc]
    have := an_block_split Nat.prime_two hf hk (by omega : 3 ≤ m + 3) hS3 (E.ρ L) (E.inj L)
      (E.range L) (E.tor L) (E.diag L) Fr n Θ' hΘ' π b hshape'
    rwa [E.range L] at this
  · have hconj : ∀ i j : Fin (m + 3), i ≠ j → ∃ b : Lˣ, ∀ c : L,
        n * pinnedX τ L (E.r i j) c * n⁻¹ = pinnedX τ L (E.r (π j) (π i)) ((b : L) * c) :=
      fun i j hij => by
        obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (E.isRoot i j hij)
        exact ⟨μ, fun c => by rw [hμ c, hWu rfl i j hij]⟩
    obtain ⟨Θ', hΘ', b, hshape⟩ := exists_aut_of_rootData_n (E.ρ L) (E.inj L) E.r ε hε Fr hFrbij
      n (fun i j => (π j, π i)) (fun i j hij => π.injective.ne hij.symm)
      (fun i j hij => ⟨π.symm j, π.symm i, π.symm.injective.ne hij.symm, by simp⟩) hconj
    have hshape' : ∀ (i j : Fin (m + 3)) (hij : i ≠ j) (t : L),
        ((Θ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(m + 3, L)) :
          Matrix (Fin (m + 3)) (Fin (m + 3)) L) =
        1 + single (π j) (π i) ((b i j : L) * t ^ 2 ^ f) :=
      fun i j hij t => by rw [hshape i j hij t, hFrc]
    have := an_block_unitary Nat.prime_two hf hk (hq2 rfl) (by omega : 3 ≤ m + 3) hS3 (E.ρ L)
      (E.inj L) (E.range L) (E.tor L) (E.diag L) Fr n Θ' hΘ' π b hshape'
    rwa [E.range L] at this

end Block

section Twist

variable {τ : Tag} {L : Type} [Field L]

theorem twist_pinnedX_w (Fr : L →+* L) (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ μ : Lˣ, ∀ c : L, n * Units.map (entrywiseHom Fr) (pinnedX τ L α c) * n⁻¹ =
      pinnedX τ L (weylQuotientHom τ L ⟨n, hn⟩ • α) ((μ : L) * Fr c) := by
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn hα
  refine ⟨μ, fun c => ?_⟩
  rw [units_map_entrywiseHom_pinnedX, hμ]

theorem twist_rootSpan_le_w (Fr : L →+* L) (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    {S S' : Set (Fin τ.rank → ℤ)} (hS : ∀ r ∈ S, IsRoot τ r)
    (hmap : ∀ α ∈ S, weylQuotientHom τ L ⟨n, hn⟩ • α ∈ S') :
    ∀ x ∈ rootSpan τ L S, n * Units.map (entrywiseHom Fr) x * n⁻¹ ∈ rootSpan τ L S' := by
  set Tm : ModGL τ L →* ModGL τ L :=
    (MulAut.conj n).toMonoidHom.comp (Units.map (entrywiseHom Fr)) with hTm
  have hle : rootSpan τ L S ≤ (rootSpan τ L S').comap Tm :=
    iSup₂_le fun α hα x hx => by
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
      obtain ⟨μ, hμ⟩ := twist_pinnedX_w Fr n hn (hS α hα)
      have h1 : Tm (pinnedX τ L α c) =
          pinnedX τ L (weylQuotientHom τ L ⟨n, hn⟩ • α) ((μ : L) * Fr c) := by
        rw [← hμ c]
        simp [hTm, MulAut.conj_apply]
      rw [Subgroup.mem_comap, h1]
      exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem (hmap α hα)
        (mem_rootSubgroup.2 ⟨_, rfl⟩))
  intro x hx
  have := hle hx
  rw [Subgroup.mem_comap] at this
  simpa [hTm, MulAut.conj_apply] using this

theorem pow_smul_mem {w : WeylGroup τ} {S : Set (Fin τ.rank → ℤ)}
    (h : ∀ r ∈ S, w • r ∈ S) : ∀ (k : ℕ), ∀ r ∈ S, (w ^ k) • r ∈ S := by
  intro k
  induction k with
  | zero => intro r hr; simpa using hr
  | succ k ih =>
    intro r hr
    rw [pow_succ, mul_smul]
    exact ih _ (h r hr)

theorem odd_pow_smul_mem {w : WeylGroup τ} {S₁ S₂ : Set (Fin τ.rank → ℤ)}
    (h₁₂ : ∀ r ∈ S₁, w • r ∈ S₂) (hsq : ∀ r ∈ S₁, (w ^ 2) • r ∈ S₁) {p : ℕ} (hp : Odd p) :
    ∀ r ∈ S₁, (w ^ p) • r ∈ S₂ := by
  obtain ⟨k, rfl⟩ := hp
  intro r hr
  have h2 : ∀ k : ℕ, ∀ r ∈ S₁, ((w ^ 2) ^ k) • r ∈ S₁ := pow_smul_mem hsq
  rw [pow_succ', pow_mul, mul_smul]
  exact h₁₂ _ (h2 k r hr)

end Twist

section Exchange

variable {τ : Tag}

theorem exchange_hfamily (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {m : ℕ}
    (hodd : Odd (m + 3)) {S₁ S₂ : Set (Fin τ.rank → ℤ)} (E₁ : AnEmbedding τ (m + 3) S₁)
    (E₂ : AnEmbedding τ (m + 3) S₂) (δ' : ℤ) (hδ' : δ' = 1 ∨ δ' = -1)
    (π₁ π₂ : Equiv.Perm (Fin (m + 3))) {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L 2] {f₀ p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀)
    (n₀ : ModGL τ L) (hn₀m : n₀ ∈ monomialSubgroup τ L)
    (hn₀fix : Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀)
    (hex₁₂ : ∀ i j, i ≠ j → ∃ i' j', i' ≠ j' ∧
      weylQuotientHom τ L ⟨n₀, hn₀m⟩ • E₁.r i j = E₂.r i' j')
    (hex₂₁ : ∀ i j, i ≠ j → ∃ i' j', i' ≠ j' ∧
      weylQuotientHom τ L ⟨n₀, hn₀m⟩ • E₂.r i j = E₁.r i' j')
    (hsq₁s : δ' = 1 → ∀ i j, i ≠ j →
      (weylQuotientHom τ L ⟨n₀, hn₀m⟩ ^ 2) • E₁.r i j = E₁.r (π₁ i) (π₁ j))
    (hsq₁u : δ' = -1 → ∀ i j, i ≠ j →
      (weylQuotientHom τ L ⟨n₀, hn₀m⟩ ^ 2) • E₁.r i j = E₁.r (π₁ j) (π₁ i))
    (hsq₂s : δ' = 1 → ∀ i j, i ≠ j →
      (weylQuotientHom τ L ⟨n₀, hn₀m⟩ ^ 2) • E₂.r i j = E₂.r (π₂ i) (π₂ j))
    (hsq₂u : δ' = -1 → ∀ i j, i ≠ j →
      (weylQuotientHom τ L ⟨n₀, hn₀m⟩ ^ 2) • E₂.r i j = E₂.r (π₂ j) (π₂ i))
    (horth : ∀ α ∈ S₁, ∀ β ∈ S₂, α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β) = 0) :
    ∃ P : Subgroup (ModGL τ L),
      IsSigmaFamily (n₀ ^ p) (iterateFrobenius L 2 (f₀ * p)) (S₁ ∪ S₂) (fun _ : Unit => P) ∧
      OddJoin (rootSpan τ L (S₁ ∪ S₂) ⊓ twistedFixedPoints (n₀ ^ p)
        (Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p))))) P ∧
      LayerDatum2 p
        (fun u => n₀ * Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) u * n₀⁻¹) P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLc : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hp0 := hp.pos
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀
  set Fr : L →+* L := iterateFrobenius L 2 (f₀ * p) with hFr
  set Φ : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr) with hΦdef
  set n : ModGL τ L := n₀ ^ p with hn
  set w₀ : WeylGroup τ := weylQuotientHom τ L ⟨n₀, hn₀m⟩ with hw₀
  have hΦK : ∀ u : ModGL τ L, Φ u = (⇑(Units.map (entrywiseHom Φ₀)))^[p] u :=
    units_map_entrywiseHom_iterateFrobenius_mul f₀ p
  have hΦn₀ : Φ n₀ = n₀ := by rw [hΦK]; exact Function.iterate_fixed hn₀fix p
  have hΦn : Φ n = n := by rw [hn, map_pow, hΦn₀]
  have hnm : n ∈ monomialSubgroup τ L := pow_mem hn₀m p
  have hwn : weylQuotientHom τ L ⟨n, hnm⟩ = w₀ ^ p := by
    have : (⟨n, hnm⟩ : ↥(monomialSubgroup τ L)) = ⟨n₀, hn₀m⟩ ^ p := rfl
    rw [this, map_pow]
  have hS₁ : ∀ r ∈ S₁, IsRoot τ r := fun x hx => by
    obtain ⟨i, j, hij, rfl⟩ := (E₁.mem x).1 hx
    exact E₁.isRoot i j hij
  have hS₂ : ∀ r ∈ S₂, IsRoot τ r := fun x hx => by
    obtain ⟨i, j, hij, rfl⟩ := (E₂.mem x).1 hx
    exact E₂.isRoot i j hij
  have hmap₁₂ : ∀ r ∈ S₁, w₀ • r ∈ S₂ := fun r hr => by
    obtain ⟨i, j, hij, rfl⟩ := (E₁.mem r).1 hr
    obtain ⟨i', j', hij', h⟩ := hex₁₂ i j hij
    rw [h]
    exact (E₂.mem _).2 ⟨i', j', hij', rfl⟩
  have hmap₂₁ : ∀ r ∈ S₂, w₀ • r ∈ S₁ := fun r hr => by
    obtain ⟨i, j, hij, rfl⟩ := (E₂.mem r).1 hr
    obtain ⟨i', j', hij', h⟩ := hex₂₁ i j hij
    rw [h]
    exact (E₁.mem _).2 ⟨i', j', hij', rfl⟩
  have hsq₁ : ∀ r ∈ S₁, (w₀ ^ 2) • r ∈ S₁ := fun r hr => by
    obtain ⟨i, j, hij, rfl⟩ := (E₁.mem r).1 hr
    rcases hδ' with h | h
    · rw [hsq₁s h i j hij]
      exact (E₁.mem _).2 ⟨π₁ i, π₁ j, π₁.injective.ne hij, rfl⟩
    · rw [hsq₁u h i j hij]
      exact (E₁.mem _).2 ⟨π₁ j, π₁ i, π₁.injective.ne hij.symm, rfl⟩
  have hsq₂ : ∀ r ∈ S₂, (w₀ ^ 2) • r ∈ S₂ := fun r hr => by
    obtain ⟨i, j, hij, rfl⟩ := (E₂.mem r).1 hr
    rcases hδ' with h | h
    · rw [hsq₂s h i j hij]
      exact (E₂.mem _).2 ⟨π₂ i, π₂ j, π₂.injective.ne hij, rfl⟩
    · rw [hsq₂u h i j hij]
      exact (E₂.mem _).2 ⟨π₂ j, π₂ i, π₂.injective.ne hij.symm, rfl⟩
  have hT₁₂ : ∀ x ∈ rootSpan τ L S₁, n * Φ x * n⁻¹ ∈ rootSpan τ L S₂ :=
    twist_rootSpan_le_w Fr n hnm hS₁ (fun α hα => by
      rw [hwn]; exact odd_pow_smul_mem hmap₁₂ hsq₁ hpodd α hα)
  have hT₂₁ : ∀ x ∈ rootSpan τ L S₂, n * Φ x * n⁻¹ ∈ rootSpan τ L S₁ :=
    twist_rootSpan_le_w Fr n hnm hS₂ (fun α hα => by
      rw [hwn]; exact odd_pow_smul_mem hmap₂₁ hsq₂ hpodd α hα)
  have hcomm : ∀ x ∈ rootSpan τ L S₁, ∀ y ∈ rootSpan τ L S₂, x * y = y * x :=
    KE.rootSpan_commute_of_orth hτ hS₁ hS₂ horth
  set Fr₂ : L →+* L := iterateFrobenius L 2 (2 * f₀ * p) with hFr₂
  set Φ₂ : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr₂) with hΦ₂
  set n₂ : ModGL τ L := (n₀ ^ 2) ^ p with hn₂
  have hn₂' : n * Φ n = n₂ := by
    rw [hΦn, hn, hn₂, ← pow_add, ← pow_mul, two_mul]
  have hFr₂comp : Fr₂ = Fr.comp Fr := RingHom.ext fun c => by
    rw [RingHom.comp_apply, hFr₂, hFr, iterateFrobenius_def, iterateFrobenius_def,
      iterateFrobenius_def, ← pow_mul, ← pow_add]
    congr 2
    ring
  have hΦΦ : ∀ x, Φ (Φ x) = Φ₂ x := fun x => by
    refine Units.ext ?_
    simp only [hΦdef, hΦ₂, Units.coe_map, hFr₂comp]
    exact entrywise_entrywise Fr Fr _
  have hT2 : ∀ x, n₂ * Φ₂ x * n₂⁻¹ = n * Φ (n * Φ x * n⁻¹) * n⁻¹ := fun x => by
    rw [← hΦΦ, ← hn₂', map_mul, map_mul, map_inv]
    group
  have hn₂m : n₂ ∈ monomialSubgroup τ L := pow_mem (pow_mem hn₀m 2) p
  have hwn₂ : weylQuotientHom τ L ⟨n₂, hn₂m⟩ = (w₀ ^ 2) ^ p := by
    have : (⟨n₂, hn₂m⟩ : ↥(monomialSubgroup τ L)) = (⟨n₀, hn₀m⟩ ^ 2) ^ p := rfl
    rw [this, map_pow, map_pow]
  obtain ⟨K₀', _, _, K₂, _, _, _, σ₂, hK₀'ac, hK₂ac, hK₀'c, hK₂c, hσ₂ord, hσ₂⟩ :=
    exists_squared_fields (K := K) (L := L) (p := p) (f₀ := f₀) hp hf₀
  have : CharP K₂ 2 := ⟨fun x => by
    rw [← (algebraMap K₂ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  have hK₂c' : Nat.card K₂ = 2 ^ (2 * f₀ * p) := by
    rw [hK₂c, show p * (2 * f₀) = 2 * f₀ * p by ring]
  have hq2 : δ' = -1 → m + 3 ≠ 3 ∨ 2 < 2 ^ (2 * f₀ * p) := fun _ => Or.inr (by
    have : 2 ^ 1 < 2 ^ (2 * f₀ * p) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
    simpa using this)
  have hWs₁ : δ' = 1 → ∀ i j, i ≠ j →
      weylQuotientHom τ L ⟨n₂, hn₂m⟩ • E₁.r i j = E₁.r ((π₁ ^ p) i) ((π₁ ^ p) j) :=
    fun h i j hij => by
      rw [hwn₂]; exact weyl_pow_smul_perm E₁.r (w₀ ^ 2) π₁ (hsq₁s h) p i j hij
  have hWu₁ : δ' = -1 → ∀ i j, i ≠ j →
      weylQuotientHom τ L ⟨n₂, hn₂m⟩ • E₁.r i j = E₁.r ((π₁ ^ p) j) ((π₁ ^ p) i) :=
    fun h i j hij => by
      rw [hwn₂]; exact weyl_pow_smul_perm_unitary E₁.r (w₀ ^ 2) π₁ (hsq₁u h) hpodd i j hij
  have hWs₂ : δ' = 1 → ∀ i j, i ≠ j →
      weylQuotientHom τ L ⟨n₂, hn₂m⟩ • E₂.r i j = E₂.r ((π₂ ^ p) i) ((π₂ ^ p) j) :=
    fun h i j hij => by
      rw [hwn₂]; exact weyl_pow_smul_perm E₂.r (w₀ ^ 2) π₂ (hsq₂s h) p i j hij
  have hWu₂ : δ' = -1 → ∀ i j, i ≠ j →
      weylQuotientHom τ L ⟨n₂, hn₂m⟩ • E₂.r i j = E₂.r ((π₂ ^ p) j) ((π₂ ^ p) i) :=
    fun h i j hij => by
      rw [hwn₂]; exact weyl_pow_smul_perm_unitary E₂.r (w₀ ^ 2) π₂ (hsq₂u h) hpodd i j hij
  obtain ⟨hfin₁, hq₁, hc₁⟩ := an_block E₁ δ' hδ' (π₁ ^ p) (k := K₂) (L := L)
    (f := 2 * f₀ * p) (Nat.mul_pos (Nat.mul_pos (by norm_num) hf₀) hp0) hK₂c' hq2 n₂ hn₂m hWs₁ hWu₁
  obtain ⟨-, -, hc₂⟩ := an_block E₂ δ' hδ' (π₂ ^ p) (k := K₂) (L := L)
    (f := 2 * f₀ * p) (Nat.mul_pos (Nat.mul_pos (by norm_num) hf₀) hp0) hK₂c' hq2 n₂ hn₂m hWs₂ hWu₂
  obtain ⟨P, hfam, hPmem⟩ := two_family_exchange' Fr n hS₁ hS₂ hT₁₂ hT₂₁ hcomm n₂ Φ₂ hT2
    hfin₁ hq₁ hc₁ hc₂
  set Tm : ModGL τ L →* ModGL τ L := (MulAut.conj n).toMonoidHom.comp Φ with hTm
  have hTapp : ∀ x, Tm x = n * Φ x * n⁻¹ := fun x => by simp [hTm, MulAut.conj_apply]
  set Q₁ := rootSpan τ L S₁ with hQ₁
  set Q₂ := rootSpan τ L S₂ with hQ₂
  refine ⟨P, hfam, ?_, ?_⟩
  ·
    intro y hy
    obtain ⟨hyQ, hyR⟩ := Subgroup.mem_inf.1 hy
    have hyT : n * Φ y * n⁻¹ = y := mem_twistedFixedPoints.1 hyR
    have hQ₁N₂ : Q₁ ≤ Subgroup.normalizer (Q₂ : Set (ModGL τ L)) := fun x hx =>
      mem_normalizer_of_forall_commute fun k hk => hcomm x hx k hk
    rw [rootSpan_union_eq] at hyQ
    have hyQ' : y ∈ ((Q₁ ⊔ Q₂ : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := hyQ
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Q₁ Q₂ hQ₁N₂] at hyQ'
    obtain ⟨a, ha, b, hb, rfl⟩ := hyQ'
    have hTa : Tm a ∈ Q₂ := by rw [hTapp]; exact hT₁₂ a ha
    have hTb : Tm b ∈ Q₁ := by rw [hTapp]; exact hT₂₁ b hb
    have hyT' : Tm a * Tm b = a * b := by
      rw [← map_mul, hTapp]; exact hyT
    have hc : (Tm b)⁻¹ * b = b * (Tm b)⁻¹ := hcomm _ (inv_mem hTb) b hb
    have hz : a * (Tm b)⁻¹ = Tm a * b⁻¹ :=
      calc a * (Tm b)⁻¹ = a * ((Tm b)⁻¹ * b) * b⁻¹ := by group
        _ = a * (b * (Tm b)⁻¹) * b⁻¹ := by rw [hc]
        _ = (a * b) * (Tm b)⁻¹ * b⁻¹ := by group
        _ = (Tm a * Tm b) * (Tm b)⁻¹ * b⁻¹ := by rw [hyT']
        _ = Tm a * b⁻¹ := by group
    set z : ModGL τ L := a * (Tm b)⁻¹ with hzdef
    have hz₁ : z ∈ Q₁ := mul_mem ha (inv_mem hTb)
    have hz₂ : z ∈ Q₂ := by rw [hz]; exact mul_mem hTa (inv_mem hb)
    have hzpow : z ^ (m + 3) = 1 := by
      obtain ⟨A, hA⟩ : z ∈ (E₁.ρ L).range := by rw [E₁.range L]; exact hz₁
      have hAc : A ∈ Subgroup.center (SL(m + 3, L)) := by
        rw [Subgroup.mem_center_iff]
        intro X
        apply E₁.inj L
        rw [map_mul, map_mul, hA]
        exact hcomm _ (by rw [hQ₁, ← E₁.range L]; exact ⟨X, rfl⟩) z hz₂
      have hApow : A ^ (m + 3) = 1 := sl_center_pow (m := m + 1) A hAc
      rw [← hA, ← map_pow, hApow, map_one]
    have hTa' : Tm a = z * b :=
      calc Tm a = Tm a * b⁻¹ * b := by group
        _ = z * b := by rw [← hz]
    have hTb' : Tm b = z⁻¹ * a :=
      calc Tm b = (a * (Tm b)⁻¹)⁻¹ * a := by group
        _ = z⁻¹ * a := rfl
    have hzb : Commute z b := hcomm z hz₁ b hb
    have hza : Commute z a := (hcomm a ha z hz₂).symm
    have hab : Commute a b := hcomm a ha b hb
    have hTg : Tm (a ^ (m + 3)) = b ^ (m + 3) := by
      rw [map_pow, hTa', hzb.mul_pow, hzpow, one_mul]
    have hTTg : Tm (Tm (a ^ (m + 3))) = a ^ (m + 3) := by
      rw [hTg, map_pow, hTb', (hza.inv_left).mul_pow, inv_pow, hzpow, inv_one, one_mul]
    have hgFix : a ^ (m + 3) ∈ twistedFixedPoints n₂ Φ₂ :=
      mem_twistedFixedPoints.2 (by rw [hT2, ← hTapp, ← hTapp]; exact hTTg)
    refine ⟨m + 3, hodd, (hPmem _).2 ⟨a ^ (m + 3), Subgroup.mem_inf.2 ⟨pow_mem ha _, hgFix⟩, ?_⟩⟩
    rw [hab.mul_pow, ← hTapp, hTg]
  ·
    have hw2 : weylQuotientHom τ L ⟨n₀ ^ 2, pow_mem hn₀m 2⟩ = w₀ ^ 2 := by
      have : (⟨n₀ ^ 2, pow_mem hn₀m 2⟩ : ↥(monomialSubgroup τ L)) = ⟨n₀, hn₀m⟩ ^ 2 := rfl
      rw [this, map_pow]
    have hWs₀ : δ' = 1 → ∀ i j, i ≠ j →
        weylQuotientHom τ L ⟨n₀ ^ 2, pow_mem hn₀m 2⟩ • E₁.r i j = E₁.r (π₁ i) (π₁ j) :=
      fun h i j hij => by rw [hw2]; exact hsq₁s h i j hij
    have hWu₀ : δ' = -1 → ∀ i j, i ≠ j →
        weylQuotientHom τ L ⟨n₀ ^ 2, pow_mem hn₀m 2⟩ • E₁.r i j = E₁.r (π₁ j) (π₁ i) :=
      fun h i j hij => by rw [hw2]; exact hsq₁u h i j hij
    have hn₀₂fix : Units.map (entrywiseHom (iterateFrobenius L 2 (2 * f₀))) (n₀ ^ 2) = n₀ ^ 2 := by
      rw [mul_comm 2 f₀, units_map_entrywiseHom_iterateFrobenius_mul]
      exact Function.iterate_fixed (by rw [map_pow, hn₀fix]) 2
    obtain ⟨D, _, ρ', τ', hinj, hrange, hcompat, hclaims⟩ := an_model E₁ δ' hδ' π₁
      (K₀ := K₀') (K := K₂) (L := L) (f₀ := 2 * f₀) (p := p) (by omega) hK₀'c hp hp5 hK₂c σ₂
      hσ₂ord hσ₂ (n₀ ^ 2) hn₀₂fix (pow_mem hn₀m 2) hWs₀ hWu₀
    have hP₁ : ρ'.range = Q₁ ⊓ twistedFixedPoints n₂ Φ₂ := by
      rw [hrange, hQ₁, ← E₁.range L]
    set F₀m : ModGL τ L →* ModGL τ L :=
      (MulAut.conj n₀).toMonoidHom.comp (Units.map (entrywiseHom Φ₀)) with hF₀m
    have hF₀app : ∀ u, F₀m u = n₀ * Units.map (entrywiseHom Φ₀) u * n₀⁻¹ := fun u => by
      simp [hF₀m, MulAut.conj_apply]
    have hfun : (⇑F₀m) = fun v => n₀ * Units.map (entrywiseHom Φ₀) v * n₀⁻¹ := funext hF₀app
    have hTF : ∀ u, Tm u = (⇑F₀m)^[p] u := fun u => by
      rw [hTapp, hfun, iterate_F0 (Units.map (entrywiseHom Φ₀)) hn₀fix p u, hΦK u]
    have hF₀₂ : ∀ u, (⇑F₀m)^[2] u = n₀ ^ 2 *
        Units.map (entrywiseHom (iterateFrobenius L 2 (2 * f₀))) u * (n₀ ^ 2)⁻¹ := fun u => by
      rw [hfun, iterate_F0 (Units.map (entrywiseHom Φ₀)) hn₀fix 2 u, mul_comm 2 f₀,
        units_map_entrywiseHom_iterateFrobenius_mul]
    have hcompat₂ : ∀ d, (⇑F₀m)^[2] (ρ' d) = ρ' (τ' d) := fun d => by
      rw [hF₀₂]; exact hcompat d
    have hρiter : ∀ (j : ℕ) (d : D), (⇑F₀m)^[2 * j] (ρ' d) = ρ' ((⇑τ')^[j] d) := by
      intro j
      induction j with
      | zero => intro d; rfl
      | succ j ih =>
        intro d
        rw [show 2 * (j + 1) = 2 * j + 2 by ring, Function.iterate_add_apply, hcompat₂, ih,
          Function.iterate_succ_apply]
    have hρQ : ∀ d, ρ' d ∈ Q₁ := fun d => by
      have : ρ' d ∈ ρ'.range := ⟨d, rfl⟩
      rw [hP₁] at this
      exact this.1
    have hρFix : ∀ d, Tm (Tm (ρ' d)) = ρ' d := fun d => by
      have : ρ' d ∈ ρ'.range := ⟨d, rfl⟩
      rw [hP₁] at this
      have h := mem_twistedFixedPoints.1 this.2
      rw [hT2, ← hTapp, ← hTapp] at h
      exact h
    have hρT : ∀ d, Tm (ρ' d) ∈ Q₂ := fun d => by rw [hTapp]; exact hT₁₂ _ (hρQ d)
    let ρP : D →* ModGL τ L :=
      { toFun := fun d => ρ' d * Tm (ρ' d)
        map_one' := by simp
        map_mul' := fun a b => by
          have hc : ρ' b * Tm (ρ' a) = Tm (ρ' a) * ρ' b := hcomm (ρ' b) (hρQ b) _ (hρT a)
          show ρ' (a * b) * Tm (ρ' (a * b)) = ρ' a * Tm (ρ' a) * (ρ' b * Tm (ρ' b))
          rw [map_mul, map_mul]
          calc ρ' a * ρ' b * (Tm (ρ' a) * Tm (ρ' b))
              = ρ' a * (ρ' b * Tm (ρ' a)) * Tm (ρ' b) := by group
            _ = ρ' a * (Tm (ρ' a) * ρ' b) * Tm (ρ' b) := by rw [hc]
            _ = ρ' a * Tm (ρ' a) * (ρ' b * Tm (ρ' b)) := by group }
    have hρP : ∀ d, ρP d = ρ' d * Tm (ρ' d) := fun d => rfl
    have hPrange : ρP.range = P := by
      ext x
      rw [hPmem]
      constructor
      · rintro ⟨d, rfl⟩
        refine ⟨ρ' d, ?_, by rw [hρP, hTapp]⟩
        have : ρ' d ∈ ρ'.range := ⟨d, rfl⟩
        rwa [hP₁] at this
      · rintro ⟨g, hg, rfl⟩
        have hg' : g ∈ ρ'.range := by rw [hP₁]; exact hg
        obtain ⟨d, rfl⟩ := hg'
        exact ⟨d, by rw [hρP, hTapp]⟩
    have hker : ∀ d, ρP d = 1 → d ∈ Subgroup.center D := fun d hd => by
      have h1 : ρ' d * Tm (ρ' d) = 1 := hd
      have h2 : ρ' d = (Tm (ρ' d))⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : ρ' d ∈ Q₂ := by rw [h2]; exact inv_mem (hρT d)
      rw [Subgroup.mem_center_iff]
      intro d'
      apply hinj
      rw [map_mul, map_mul]
      exact hcomm _ (hρQ d') _ h3
    obtain ⟨j, hj⟩ := hpodd
    have hk : (p + 1) / 2 = j + 1 := by omega
    have hcompatP : ∀ d, (⇑F₀m) (ρP d) = ρP ((⇑τ')^[j + 1] d) := fun d => by
      set g := ρ' d with hg
      set g' := ρ' ((⇑τ')^[j + 1] d) with hg'
      have hg'iter : g' = (⇑F₀m)^[p + 1] g := by
        rw [hg', ← hρiter, hg]; congr 1; omega
      have hg'Q : g' ∈ Q₁ := hρQ _
      have hF₀T : F₀m (Tm g) = g' := by
        rw [hTF, ← Function.iterate_succ_apply' (⇑F₀m) p g, hg'iter]
      have hTg' : Tm g' = F₀m g := by
        rw [hTF g', hg'iter, ← Function.iterate_add_apply, show p + (p + 1) = (p + p) + 1 by ring,
          Function.iterate_succ_apply', Function.iterate_add_apply, ← hTF, ← hTF, hρFix]
      have hcg : g' * Tm g' = Tm g' * g' := hcomm g' hg'Q _ (by rw [hTapp]; exact hT₁₂ _ hg'Q)
      show F₀m (ρ' d * Tm (ρ' d)) = ρ' ((⇑τ')^[j + 1] d) * Tm (ρ' ((⇑τ')^[j + 1] d))
      rw [map_mul, hF₀T, ← hTg', hcg]
    have hkp : ¬ p ∣ j + 1 := by
      refine Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    rw [← hPrange]
    refine layerDatum2_of_model' _ ρP (⇑τ')^[j + 1] hker ?_ ?_
    · intro d
      exact (hF₀app (ρP d)).symm.trans (hcompatP d)
    · intro G _ α φ hkerφ hαφ Q hQ
      exact hclaims (j + 1) hkp α φ hkerφ hαφ Q hQ

end Exchange

end CFSG.RankThree.PartOne.TCX.E
