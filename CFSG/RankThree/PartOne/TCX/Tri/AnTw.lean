module

public import CFSG.RankThree.PartOne.TCX.E.AnModel

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Matrix CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.TCX.E
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section Pow

variable {τ : Tag} {L : Type} [Field L] {ν : ℕ}

theorem pow_conj_pinnedX_perm (r : Fin ν → Fin ν → (Fin τ.rank → ℤ)) (π : Equiv.Perm (Fin ν))
    (n₀ : ModGL τ L)
    (hc : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n₀ * pinnedX τ L (r i j) c * n₀⁻¹ = pinnedX τ L (r (π i) (π j)) ((b : L) * c)) (k : ℕ) :
    ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n₀ ^ k * pinnedX τ L (r i j) c * (n₀ ^ k)⁻¹ =
        pinnedX τ L (r ((π ^ k) i) ((π ^ k) j)) ((b : L) * c) := by
  induction k with
  | zero => intro i j _; exact ⟨1, fun c => by simp⟩
  | succ k ih =>
    intro i j hij
    obtain ⟨b₁, hb₁⟩ := ih i j hij
    obtain ⟨b₂, hb₂⟩ := hc ((π ^ k) i) ((π ^ k) j) ((π ^ k).injective.ne hij)
    refine ⟨b₂ * b₁, fun c => ?_⟩
    have h1 : n₀ ^ (k + 1) * pinnedX τ L (r i j) c * (n₀ ^ (k + 1))⁻¹ =
        n₀ * (n₀ ^ k * pinnedX τ L (r i j) c * (n₀ ^ k)⁻¹) * n₀⁻¹ := by
      rw [pow_succ']
      group
    rw [h1, hb₁, hb₂, pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Units.val_mul,
      mul_assoc]

theorem pow_conj_pinnedX_perm_unitary (r : Fin ν → Fin ν → (Fin τ.rank → ℤ))
    (π : Equiv.Perm (Fin ν)) (n₀ : ModGL τ L)
    (hc : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n₀ * pinnedX τ L (r i j) c * n₀⁻¹ = pinnedX τ L (r (π j) (π i)) ((b : L) * c)) (k : ℕ)
    (hk : Odd k) :
    ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n₀ ^ k * pinnedX τ L (r i j) c * (n₀ ^ k)⁻¹ =
        pinnedX τ L (r ((π ^ k) j) ((π ^ k) i)) ((b : L) * c) := by
  have h2 : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n₀ ^ 2 * pinnedX τ L (r i j) c * (n₀ ^ 2)⁻¹ =
        pinnedX τ L (r ((π ^ 2) i) ((π ^ 2) j)) ((b : L) * c) := by
    intro i j hij
    obtain ⟨b₁, hb₁⟩ := hc i j hij
    obtain ⟨b₂, hb₂⟩ := hc (π j) (π i) (π.injective.ne hij.symm)
    refine ⟨b₂ * b₁, fun c => ?_⟩
    have h1 : n₀ ^ 2 * pinnedX τ L (r i j) c * (n₀ ^ 2)⁻¹ =
        n₀ * (n₀ * pinnedX τ L (r i j) c * n₀⁻¹) * n₀⁻¹ := by
      rw [pow_two]
      group
    rw [h1, hb₁, hb₂, pow_two, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Units.val_mul, mul_assoc]
  intro i j hij
  obtain ⟨m, rfl⟩ := hk
  obtain ⟨b₁, hb₁⟩ := pow_conj_pinnedX_perm r (π ^ 2) (n₀ ^ 2) h2 m i j hij
  obtain ⟨b₂, hb₂⟩ := hc (((π ^ 2) ^ m) i) (((π ^ 2) ^ m) j) (((π ^ 2) ^ m).injective.ne hij)
  refine ⟨b₂ * b₁, fun c => ?_⟩
  have h1 : n₀ ^ (2 * m + 1) * pinnedX τ L (r i j) c * (n₀ ^ (2 * m + 1))⁻¹ =
      n₀ * ((n₀ ^ 2) ^ m * pinnedX τ L (r i j) c * ((n₀ ^ 2) ^ m)⁻¹) * n₀⁻¹ := by
    rw [pow_succ', pow_mul]
    group
  have e : ∀ x, (π ^ (2 * m + 1)) x = π (((π ^ 2) ^ m) x) := fun x => by
    rw [pow_succ', pow_mul, Equiv.Perm.mul_apply]
  rw [h1, hb₁, hb₂, e, e, Units.val_mul, mul_assoc]

end Pow

section Family

variable {τ : Tag} {S : Set (Fin τ.rank → ℤ)} {m : ℕ}

theorem an_family' (E : AnEmbedding τ (m + 3) S) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (π : Equiv.Perm (Fin (m + 3))) {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L 2] {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = 2 ^ (p * f₀)) (n₀ : ModGL τ L)
    (hcs : δ = 1 → ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n₀ * pinnedX τ L (E.r i j) c * n₀⁻¹ = pinnedX τ L (E.r (π i) (π j)) ((b : L) * c))
    (hcu : δ = -1 → ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n₀ * pinnedX τ L (E.r i j) c * n₀⁻¹ = pinnedX τ L (E.r (π j) (π i)) ((b : L) * c)) :
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
  have hS3 : ∀ r ∈ S, IsRoot τ r := fun x hx => by
    obtain ⟨i, j, hij, rfl⟩ := (E.mem x).1 hx
    exact E.isRoot i j hij
  choose! ε hε using fun (i j : Fin (m + 3)) (hij : i ≠ j) => E.gen L i j hij
  have hfun : ∀ P : Unit → Subgroup (ModGL τ L), P = fun _ : Unit => P () := fun P =>
    funext fun u => by cases u; rfl
  rcases hδ with rfl | rfl
  · have hconj := pow_conj_pinnedX_perm E.r π n₀ (hcs rfl) p
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
  · have hconj := pow_conj_pinnedX_perm_unitary E.r π n₀ (hcu rfl) p
      (hp.odd_of_ne_two (by omega))
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

section Model

variable {τ : Tag} {S : Set (Fin τ.rank → ℤ)} {m : ℕ}

theorem an_model' (E : AnEmbedding τ (m + 3) S) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (π : Equiv.Perm (Fin (m + 3))) {K₀ K L : Type} [Field K₀] [Field K] [Finite K] [CharP K 2]
    [Field L] [Algebra K₀ L] [IsAlgClosure K₀ L] [Algebra K L] [CharP L 2] {f₀ p : ℕ}
    (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = 2 ^ (p * f₀)) (σ : K ≃+* K) (hσord : orderOf σ = p)
    (hσ : ∀ c : K, iterateFrobenius L 2 f₀ (algebraMap K L c) = algebraMap K L (σ c))
    (n₀ : ModGL τ L) (hn₀fix : Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀)
    (hcs : δ = 1 → ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n₀ * pinnedX τ L (E.r i j) c * n₀⁻¹ = pinnedX τ L (E.r (π i) (π j)) ((b : L) * c))
    (hcu : δ = -1 → ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n₀ * pinnedX τ L (E.r i j) c * n₀⁻¹ = pinnedX τ L (E.r (π j) (π i)) ((b : L) * c)) :
    ∃ (D : Type) (_ : Group D) (ρ' : D →* ModGL τ L) (τ' : D →* D), Function.Injective ρ' ∧
      ρ'.range = (E.ρ L).range ⊓ twistedFixedPoints (n₀ ^ p)
        (Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p)))) ∧
      (∀ d, n₀ * Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) (ρ' d) * n₀⁻¹ = ρ' (τ' d)) ∧
      ∀ k : ℕ, ¬ p ∣ k → ∀ {G : Type} [Group G] (α : MulAut G) (φ : D →* G),
        (∀ d, φ d = 1 → d ∈ Subgroup.center D) → (∀ d, α (φ d) = φ ((⇑τ')^[k] d)) →
        ∀ Q : Subgroup G, φ.range = Q → LayerClaims2 p α Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have hp0 := hp.pos
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσord
    exact hp.one_lt.ne hσord
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀def
  set Fr : L →+* L := iterateFrobenius L 2 (f₀ * p) with hFrdef
  have hΦ₀c : ∀ c, Φ₀ c = c ^ 2 ^ f₀ := fun c => iterateFrobenius_def 2 f₀ c
  have hΦ₀bij : Function.Bijective Φ₀ := ⟨Φ₀.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < 2 ^ f₀ by positivity)
    exact ⟨x, by rw [hΦ₀c, hx]⟩⟩
  have hΦK : ∀ u : ModGL τ L, Units.map (entrywiseHom Fr) u =
      (⇑(Units.map (entrywiseHom Φ₀)))^[p] u := units_map_entrywiseHom_iterateFrobenius_mul f₀ p
  choose! ε hε using fun (i j : Fin (m + 3)) (hij : i ≠ j) => E.gen L i j hij
  rcases hδ with rfl | rfl
  ·
    have hconj := hcs rfl
    obtain ⟨Θ₀, hΘ₀, b, hshape⟩ := exists_aut_of_rootData_n (E.ρ L) (E.inj L) E.r ε hε Φ₀ hΦ₀bij
      n₀ (fun i j => (π i, π j)) (fun i j hij => π.injective.ne hij)
      (fun i j hij => ⟨π.symm i, π.symm j, π.symm.injective.ne hij, by simp⟩) hconj
    obtain ⟨ψ, hψinj, hψcompat, hψfix⟩ := an_split_model (by omega : 3 ≤ m + 3) hf₀ hK₀ hp.one_le
      hK σ hσ π Θ₀ b hshape
    obtain ⟨hinj, hrange, hcompat⟩ := an_bridge E hn₀fix hΦK Θ₀ hΘ₀ ψ
      (Matrix.SpecialLinearGroup.map σ.toRingHom) hψinj hψcompat hψfix
    refine ⟨SL(m + 3, K), inferInstance, (E.ρ L).comp ψ, Matrix.SpecialLinearGroup.map σ.toRingHom,
      hinj, hrange, hcompat, ?_⟩
    intro k hk G _ α φ hkerφ hαφ Q hQ
    have hσk : σ ^ k ≠ 1 := fun h => hk (hσord ▸ orderOf_dvd_of_pow_eq_one h)
    refine sl_claims2' (m := m + 1) hp5 hf₀ hK hσk α φ hkerφ (fun B => ?_) Q hQ
    rw [hαφ, iterate_map_sl_ringAut]
  ·
    have hconj := hcu rfl
    obtain ⟨Θ₀, hΘ₀, b, hshape⟩ := exists_aut_of_rootData_n (E.ρ L) (E.inj L) E.r ε hε Φ₀ hΦ₀bij
      n₀ (fun i j => (π j, π i)) (fun i j hij => π.injective.ne hij.symm)
      (fun i j hij => ⟨π.symm j, π.symm i, π.symm.injective.ne hij.symm, by simp⟩) hconj
    obtain ⟨K'', _, _, _, σ'', ψ, τ', hK'', hσ''ord, hτ', hψinj, hψcompat, hψfix⟩ :=
      an_unitary_model (by omega : 3 ≤ m + 3) hf₀ hK₀ hp (hp.odd_of_ne_two (by omega)) π Θ₀ b hshape
    obtain ⟨hinj, hrange, hcompat⟩ := an_bridge E hn₀fix hΦK Θ₀ hΘ₀ ψ τ' hψinj hψcompat hψfix
    refine ⟨↥(StatedSU (m + 3) (2 ^ (p * f₀)) K''), inferInstance, (E.ρ L).comp ψ, τ', hinj,
      hrange, hcompat, ?_⟩
    intro k hk G _ α φ hkerφ hαφ Q hQ
    have hσk : orderOf (σ'' ^ k) = p := by
      rw [Nat.Coprime.orderOf_pow (by rw [hσ''ord]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hk),
        hσ''ord]
    let τk : ↥(StatedSU (m + 3) (2 ^ (p * f₀)) K'') →* ↥(StatedSU (m + 3) (2 ^ (p * f₀)) K'') :=
      { toFun := (⇑τ')^[k]
        map_one' := Function.iterate_fixed (map_one τ') k
        map_mul' := fun a b => iterate_map_mul τ' k a b }
    have hτk : ∀ A, (((τk A : ↥(StatedSU (m + 3) (2 ^ (p * f₀)) K'')) : GL (Fin (m + 3)) K'') :
        Matrix (Fin (m + 3)) (Fin (m + 3)) K'') =
        (((A : ↥(StatedSU (m + 3) (2 ^ (p * f₀)) K'')) : GL (Fin (m + 3)) K'') :
          Matrix (Fin (m + 3)) (Fin (m + 3)) K'').map (σ'' ^ k) := fun A =>
      iterate_coe_map (fun A : ↥(StatedSU (m + 3) (2 ^ (p * f₀)) K'') =>
        ((A : GL (Fin (m + 3)) K'') : Matrix (Fin (m + 3)) (Fin (m + 3)) K'')) τ' σ'' hτ' k A
    exact su_claims2' hp hp5 hf₀ hK'' hσk α φ hkerφ τk hτk hαφ Q hQ

end Model

end CFSG.RankThree.PartOne.TCX.Tri
