module

public import CFSG.RankThree.PartOne.TCX.E.AnModel

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.E

open Matrix CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KLCE
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section Weyl

variable {τ : Tag} {ν : ℕ}

theorem weyl_pow_smul_perm (r : Fin ν → Fin ν → (Fin τ.rank → ℤ)) (w : WeylGroup τ)
    (π : Equiv.Perm (Fin ν)) (hW : ∀ i j, i ≠ j → w • r i j = r (π i) (π j)) :
    ∀ (k : ℕ) (i j : Fin ν), i ≠ j → (w ^ k) • r i j = r ((π ^ k) i) ((π ^ k) j) := by
  intro k
  induction k with
  | zero => intro i j _; simp
  | succ k ih =>
    intro i j hij
    rw [pow_succ', mul_smul, ih i j hij, hW _ _ ((π ^ k).injective.ne hij), pow_succ',
      Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

theorem weyl_pow_smul_perm_unitary (r : Fin ν → Fin ν → (Fin τ.rank → ℤ)) (w : WeylGroup τ)
    (π : Equiv.Perm (Fin ν)) (hW : ∀ i j, i ≠ j → w • r i j = r (π j) (π i)) {p : ℕ}
    (hp : Odd p) (i j : Fin ν) (hij : i ≠ j) :
    (w ^ p) • r i j = r ((π ^ p) j) ((π ^ p) i) := by
  have h2 : ∀ i j : Fin ν, i ≠ j → (w ^ 2) • r i j = r ((π ^ 2) i) ((π ^ 2) j) := by
    intro i j hij
    rw [pow_two, mul_smul, hW i j hij, hW _ _ (π.injective.ne hij.symm), pow_two,
      Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  have hev : ∀ (k : ℕ) (i j : Fin ν), i ≠ j →
      (w ^ (2 * k)) • r i j = r ((π ^ (2 * k)) i) ((π ^ (2 * k)) j) := by
    intro k
    induction k with
    | zero => intro i j _; simp
    | succ k ih =>
      intro i j hij
      rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add, pow_add, mul_smul,
        ih i j hij, h2 _ _ ((π ^ (2 * k)).injective.ne hij), Equiv.Perm.mul_apply,
        Equiv.Perm.mul_apply]
  obtain ⟨k, rfl⟩ := hp
  rw [pow_succ', mul_smul, hev k i j hij, hW _ _ ((π ^ (2 * k)).injective.ne hij), pow_succ',
    Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

end Weyl

section Family

variable {τ : Tag} {S : Set (Fin τ.rank → ℤ)} {m : ℕ}

theorem an_family (E : AnEmbedding τ (m + 3) S) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (π : Equiv.Perm (Fin (m + 3))) {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L 2] {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = 2 ^ (p * f₀)) (n₀ : ModGL τ L) (hn₀m : n₀ ∈ monomialSubgroup τ L)
    (hWs : δ = 1 → ∀ i j, i ≠ j →
      weylQuotientHom τ L ⟨n₀, hn₀m⟩ • E.r i j = E.r (π i) (π j))
    (hWu : δ = -1 → ∀ i j, i ≠ j →
      weylQuotientHom τ L ⟨n₀, hn₀m⟩ • E.r i j = E.r (π j) (π i)) :
    ∃ P : Subgroup (ModGL τ L),
      IsSigmaFamily (n₀ ^ p) (iterateFrobenius L 2 (f₀ * p)) S (fun _ : Unit => P) ∧
      P = (E.ρ L).range ⊓ twistedFixedPoints (n₀ ^ p)
        (Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hp0 := hp.pos
  set Fr : L →+* L := iterateFrobenius L 2 (f₀ * p) with hFrdef
  have hFrc : ∀ c, Fr c = c ^ 2 ^ (p * f₀) := fun c => by
    rw [mul_comm p f₀]
    exact iterateFrobenius_def 2 (f₀ * p) c
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < 2 ^ (p * f₀) by positivity)
    exact ⟨x, by rw [hFrc, hx]⟩⟩
  have hNm : n₀ ^ p ∈ monomialSubgroup τ L := pow_mem hn₀m p
  have hWN : ∀ γ : Fin τ.rank → ℤ, weylQuotientHom τ L ⟨n₀ ^ p, hNm⟩ • γ =
      ((weylQuotientHom τ L ⟨n₀, hn₀m⟩) ^ p) • γ := fun γ => by
    have : (⟨n₀ ^ p, hNm⟩ : ↥(monomialSubgroup τ L)) = ⟨n₀, hn₀m⟩ ^ p := rfl
    rw [this, map_pow]
  have hS3 : ∀ r ∈ S, IsRoot τ r := fun x hx => by
    obtain ⟨i, j, hij, rfl⟩ := (E.mem x).1 hx
    exact E.isRoot i j hij
  choose! ε hε using fun (i j : Fin (m + 3)) (hij : i ≠ j) => E.gen L i j hij
  have hfun : ∀ P : Unit → Subgroup (ModGL τ L), P = fun _ : Unit => P () := fun P =>
    funext fun u => by cases u; rfl
  rcases hδ with rfl | rfl
  · have hconj : ∀ i j : Fin (m + 3), i ≠ j → ∃ b : Lˣ, ∀ c : L,
        n₀ ^ p * pinnedX τ L (E.r i j) c * (n₀ ^ p)⁻¹ =
          pinnedX τ L (E.r ((π ^ p) i) ((π ^ p) j)) ((b : L) * c) := fun i j hij => by
      obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hNm (E.isRoot i j hij)
      exact ⟨μ, fun c => by
        rw [hμ c, hWN, weyl_pow_smul_perm E.r _ π (hWs rfl) p i j hij]⟩
    obtain ⟨Θ', hΘ', b, hshape⟩ := exists_aut_of_rootData_n (E.ρ L) (E.inj L) E.r ε hε Fr hFrbij
      (n₀ ^ p) (fun i j => ((π ^ p) i, (π ^ p) j)) (fun i j hij => (π ^ p).injective.ne hij)
      (fun i j hij => ⟨(π ^ p).symm i, (π ^ p).symm j, (π ^ p).symm.injective.ne hij, by simp⟩)
      hconj
    have hshape' : ∀ (i j : Fin (m + 3)) (hij : i ≠ j) (t : L),
        ((Θ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(m + 3, L)) :
          Matrix (Fin (m + 3)) (Fin (m + 3)) L) =
        1 + single ((π ^ p) i) ((π ^ p) j) ((b i j : L) * t ^ 2 ^ (p * f₀)) :=
      fun i j hij t => by rw [hshape i j hij t, hFrc]
    obtain ⟨P, hP, hP1, -⟩ := an_family_split (ℓ := 2) (f := p * f₀) Nat.prime_two
      (Nat.mul_pos hp0 hf₀) (k := K) hK (by omega : 3 ≤ m + 3) hS3 (E.ρ L) (E.inj L) (E.range L)
      (E.tor L) (E.diag L) Fr (n₀ ^ p) Θ' hΘ' (π ^ p) b hshape'
    refine ⟨P (), ?_, hP1⟩
    rw [← hfun P]
    exact hP
  · have hconj : ∀ i j : Fin (m + 3), i ≠ j → ∃ b : Lˣ, ∀ c : L,
        n₀ ^ p * pinnedX τ L (E.r i j) c * (n₀ ^ p)⁻¹ =
          pinnedX τ L (E.r ((π ^ p) j) ((π ^ p) i)) ((b : L) * c) := fun i j hij => by
      obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hNm (E.isRoot i j hij)
      exact ⟨μ, fun c => by
        rw [hμ c, hWN, weyl_pow_smul_perm_unitary E.r _ π (hWu rfl)
          (hp.odd_of_ne_two (by omega)) i j hij]⟩
    obtain ⟨Θ', hΘ', b, hshape⟩ := exists_aut_of_rootData_n (E.ρ L) (E.inj L) E.r ε hε Fr hFrbij
      (n₀ ^ p) (fun i j => ((π ^ p) j, (π ^ p) i)) (fun i j hij => (π ^ p).injective.ne hij.symm)
      (fun i j hij => ⟨(π ^ p).symm j, (π ^ p).symm i, (π ^ p).symm.injective.ne hij.symm,
        by simp⟩) hconj
    have hshape' : ∀ (i j : Fin (m + 3)) (hij : i ≠ j) (t : L),
        ((Θ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(m + 3, L)) :
          Matrix (Fin (m + 3)) (Fin (m + 3)) L) =
        1 + single ((π ^ p) j) ((π ^ p) i) ((b i j : L) * t ^ 2 ^ (p * f₀)) :=
      fun i j hij t => by rw [hshape i j hij t, hFrc]
    obtain ⟨P, hP, hP1, -⟩ := an_family_unitary (ℓ := 2) (f := p * f₀) Nat.prime_two
      (Nat.mul_pos hp0 hf₀) (k := K) hK (Or.inr (by
        have : 2 ^ 1 < 2 ^ (p * f₀) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
        simpa using this)) (by omega : 3 ≤ m + 3) hS3 (E.ρ L) (E.inj L) (E.range L)
      (E.tor L) (E.diag L) Fr (n₀ ^ p) Θ' hΘ' (π ^ p) b hshape'
    refine ⟨P (), ?_, hP1⟩
    rw [← hfun P]
    exact hP

end Family

section HFamily

variable {τ : Tag} {S : Set (Fin τ.rank → ℤ)} {m : ℕ}

theorem an_hfamily (E : AnEmbedding τ (m + 3) S) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (π : Equiv.Perm (Fin (m + 3))) {K₀ K L : Type} [Field K₀] [Finite K₀] [Field K] [Finite K]
    [CharP K 2] [Field L] [Algebra K₀ K] [Algebra K L] [Algebra K₀ L] [IsScalarTower K₀ K L]
    [IsAlgClosure K L] [IsAlgClosure K₀ L] [CharP L 2] {f₀ p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hf₀ : 1 ≤ f₀) (hK : Nat.card K = 2 ^ (p * f₀)) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (σ : K ≃+* K) (hσord : orderOf σ = p) (hσ : ∀ a, σ a = a ^ 2 ^ f₀)
    (n₀ : ModGL τ L) (hn₀fix : Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀)
    (hn₀m : n₀ ∈ monomialSubgroup τ L)
    (hWs : δ = 1 → ∀ i j, i ≠ j →
      weylQuotientHom τ L ⟨n₀, hn₀m⟩ • E.r i j = E.r (π i) (π j))
    (hWu : δ = -1 → ∀ i j, i ≠ j →
      weylQuotientHom τ L ⟨n₀, hn₀m⟩ • E.r i j = E.r (π j) (π i)) :
    ∃ P : Subgroup (ModGL τ L),
      IsSigmaFamily (n₀ ^ p) (iterateFrobenius L 2 (f₀ * p)) S (fun _ : Unit => P) ∧
      OddJoin (rootSpan τ L S ⊓ twistedFixedPoints (n₀ ^ p)
        (Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p))))) P ∧
      LayerDatum2 p
        (fun u => n₀ * Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) u * n₀⁻¹) P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ' : ∀ c : K, iterateFrobenius L 2 f₀ (algebraMap K L c) = algebraMap K L (σ c) :=
    fun c => by rw [iterateFrobenius_def, ← map_pow, hσ]
  obtain ⟨P, hfam, hPeq⟩ := an_family E δ hδ π (K := K) (L := L) hf₀ hp hp5 hK n₀ hn₀m hWs hWu
  obtain ⟨D, _, ρ', τ', hinj, hrange, hcompat, hclaims⟩ := an_model E δ hδ π (K₀ := K₀)
    (K := K) (L := L) hf₀ hK₀ hp hp5 hK σ hσord hσ' n₀ hn₀fix hn₀m hWs hWu
  have hP : ρ'.range = P := by rw [hrange, hPeq]
  refine ⟨P, hfam, ?_, ?_⟩
  · rw [← E.range L] at *
    exact OddJoin.of_le hPeq.ge
  · rw [← hP]
    refine layerDatum2_of_model' _ ρ' (⇑τ') (fun d hd => ?_) hcompat ?_
    · have : d = 1 := hinj (hd.trans (map_one ρ').symm)
      rw [this]
      exact one_mem _
    · intro G _ α φ hkerφ hαφ Q hQ
      exact hclaims 1 hp.not_dvd_one α φ hkerφ
        (fun d => by rw [Function.iterate_one]; exact hαφ d) Q hQ

end HFamily

end CFSG.RankThree.PartOne.TCX.E
