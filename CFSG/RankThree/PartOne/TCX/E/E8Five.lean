module

public import CFSG.RankThree.PartOne.TCX.E.AnFamily
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KLCE.A2Sector

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.E

open Matrix CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KLCE
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (chainRoot weylMatrix weylMatrix_mulVec)

open CFSG.RankThree.Chevalley (exhaustionPhi)

open scoped MatrixGroups Matrix

section Defs


@[expose] def e8A4Embedding (v : WeylGroup Tag.E8) : AnEmbedding Tag.E8 (2 + 3) (sigmaSetE8A4 v) where
  ρ L _ := rhoSigmaE8A4 L v
  r := sigmaRootE8A4 v
  mem _ := mem_sigmaSetE8A4_iff
  isRoot _ _ hij := isRoot_sigmaRootE8A4 v hij
  neg := sigmaRootE8A4_neg v
  inj _ _ := rhoSigmaE8A4_injective v
  range _ _ := rhoSigmaE8A4_range v
  gen _ _ i j hij := rhoSigmaE8A4_transvection v i j hij
  tor _ _ b := ⟨fun i => rootChar b (wbE8A4 v i), fun A => rhoSigmaE8A4_torus v b A⟩
  diag _ _ A hA := rhoSigmaE8A4_diagonal v A hA

@[expose] def E8FiveR (δ : ℤ) (L : Type) [Field L] (n : ModGL Tag.E8 L) : Prop :=
  ∃ hnm : n ∈ monomialSubgroup Tag.E8 L, ∀ u : Fin Tag.E8.rank → ℤ,
    weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • u = (δ • weylMatrix e8F5U) *ᵥ u

@[expose] def e8Five𝒮 (δ : ℤ) : Set (Set (Fin Tag.E8.rank → ℤ)) :=
  {S | ∃ v : WeylGroup Tag.E8, S = sigmaSetE8A4 v ∧
    (δ = 1 → ∃ π : Equiv.Perm (Fin 5), ∀ i j : Fin 5, i ≠ j →
      weylMatrix e8F5U *ᵥ sigmaRootE8A4 v i j = sigmaRootE8A4 v (π i) (π j)) ∧
    (δ = -1 → ∃ π : Equiv.Perm (Fin 5), ∀ i j : Fin 5, i ≠ j →
      (-weylMatrix e8F5U) *ᵥ sigmaRootE8A4 v i j = sigmaRootE8A4 v (π j) (π i))}

theorem e8Five𝒮_ok (δ : ℤ) : ∀ S ∈ e8Five𝒮 δ, (∀ α ∈ S, IsRoot Tag.E8 α) ∧ ∀ α ∈ S, -α ∈ S := by
  rintro S ⟨v, rfl, -, -⟩
  exact ⟨sigmaSetE8A4_isRoot v, sigmaSetE8A4_neg v⟩

end Defs

section Frame


theorem e8Five_frame (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (e : ℕ) (he : (δ = 1 ∧ e = 5) ∨ (δ = -1 ∧ e = 10))
    {K₀ L : Type} [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L] [IsAlgClosure K₀ L] [CharP L 2]
    {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀) (hp : p.Prime) (hp0 : 5 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K₀ : ℤ)) :
    ∃ n₀ : ModGL Tag.E8 L, n₀ ∈ adjointGroup Tag.E8 L ∧
      Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ ∧ E8FiveR δ L n₀ ∧
      (∀ a : Fin Tag.E8.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
        rootDiagUnit Tag.E8 a ∈ twistedTorusOf (n₀ ^ p)
          (Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p)))) →
        rootCharStabilizer a ⊆ (Subgroup.closure
          {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup Tag.E8))) ∧
      ∃ (Z : Subgroup (ModGL Tag.E8 L)),
        Z ≤ twistedTorusOf n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) ∧
        ∃ N₀ : ℕ, N₀ ≠ 0 ∧ Nat.card Z = N₀ ∧
          p ^ (Nat.card (adjointGroup Tag.E8 K₀)).factorization p = p ^ N₀.factorization p ∧
          (∀ a : Fin Tag.E8.rank → Lˣ, rootDiagUnit Tag.E8 a ∈ Z →
            orderOf (rootDiagUnit Tag.E8 a) = p →
            rootCharKernel a = ∅ ∨ rootCharKernel a ∈ e8Five𝒮 δ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have : CharP K₀ 2 := ⟨fun x => by
    rw [← (algebraMap K₀ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K₀ := Fintype.ofFinite K₀
  set Fr : L →+* L := iterateFrobenius L 2 f₀ with hFrdef
  have hFr' : ∀ c, Fr c = c ^ (2 ^ f₀) := fun c => iterateFrobenius_def 2 f₀ c
  have hFr : ∀ c, Fr c = c ^ Nat.card K₀ := fun c => by
    rw [hK₀]
    exact hFr' c
  have hq2 : 2 ≤ Nat.card K₀ := Finite.one_lt_card
  have hℓq : 2 ∣ Nat.card K₀ := by
    rw [hK₀]
    exact dvd_pow_self _ (by omega)
  have hℓ : Nat.Prime 2 := Nat.prime_two
  obtain ⟨w, hw, hp7, hpq, m, hm, hordq, hΦ⟩ : ∃ w : WeylGroup Tag.E8,
      (∀ u : Fin Tag.E8.rank → ℤ, w • u = (δ • weylMatrix e8F5U) *ᵥ u) ∧ 7 < p ∧
      ¬ p ∣ Nat.card K₀ ∧ ∃ m : ℕ, (m = 5 ∨ m = 10) ∧
        orderOf ((Nat.card K₀ : ℕ) : ZMod p) = m ∧
        (((δ : ℤ) : ZMod p) * ((Nat.card K₀ : ℕ) : ZMod p)) ^ 4 +
          (((δ : ℤ) : ZMod p) * ((Nat.card K₀ : ℕ) : ZMod p)) ^ 3 +
          (((δ : ℤ) : ZMod p) * ((Nat.card K₀ : ℕ) : ZMod p)) ^ 2 +
          (((δ : ℤ) : ZMod p) * ((Nat.card K₀ : ℕ) : ZMod p)) + 1 = 0 := by
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have h5' : (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 4 + (Nat.card K₀ : ℤ) ^ 3 + (Nat.card K₀ : ℤ) ^ 2 +
          (Nat.card K₀ : ℤ) + 1 := by simpa [exhaustionPhi] using hpf
      obtain ⟨hp7, hpq, hord⟩ := CTE6.e6Five_data hp hp0 h5'
      have hΦ5 : ((Nat.card K₀ : ℕ) : ZMod p) ^ 4 + ((Nat.card K₀ : ℕ) : ZMod p) ^ 3 +
          ((Nat.card K₀ : ℕ) : ZMod p) ^ 2 + ((Nat.card K₀ : ℕ) : ZMod p) + 1 = 0 := by
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K₀ : ℤ) ^ 4 +
          (Nat.card K₀ : ℤ) ^ 3 + (Nat.card K₀ : ℤ) ^ 2 + (Nat.card K₀ : ℤ) + 1) p).2 h5'
        simpa using this
      exact ⟨e8F5U, fun u => by rw [one_smul, weylMatrix_mulVec], hp7, hpq, 5, Or.inl rfl, hord,
        e8Five_hΦ_one _ hΦ5⟩
    · have h10' : (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 4 - (Nat.card K₀ : ℤ) ^ 3 +
          (Nat.card K₀ : ℤ) ^ 2 - (Nat.card K₀ : ℤ) + 1 := by simpa [exhaustionPhi] using hpf
      obtain ⟨hp7, hpq, hord, hΦ10⟩ := CTE6.twE6Ten_data hp hp0 h10'
      exact ⟨e8F5C ^ 21, fun u => by
        rw [← weylMatrix_mulVec, weylMatrix_e8F5C_21, neg_one_smul], hp7, hpq, 10, Or.inr rfl,
        hord, e8Five_hΦ_neg _ hΦ10⟩
  have hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E8) :=
    not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inr rfl))
  have hcm := canonicalRep_mem_monomialSubgroup L w
  have hπ : weylQuotientHom Tag.E8 L ⟨canonicalRep (coxeterSystem Tag.E8) L w, hcm⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hnW : ∀ u, weylQuotientHom Tag.E8 L ⟨canonicalRep (coxeterSystem Tag.E8) L w, hcm⟩ • u =
      (δ • weylMatrix e8F5U) *ᵥ u := fun u => by rw [hπ]; exact hw u
  set n : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L w with hndef
  refine ⟨n, monomialSubgroup_le_adjointGroup' hcm, canonicalRep_frobenius_fixed f₀ w,
    ⟨hcm, hnW⟩, fun a hap ha1 _ => rootCharStabilizer_subset_closure hp hordW hap ha1, ?_⟩
  have hinj0 : Function.Injective (rootDiagUnitHom Tag.E8 L) := rootDiagUnit_injective
  have hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples (e8FiveM δ) Fr).map (rootDiagUnitHom Tag.E8 L) := by
    have h := twistedFixedTuples_eq_fixedCharTuples hnW Fr
    rw [show e8FiveM δ = δ • weylMatrix e8F5U from rfl, ← h]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hcm _ rfl Fr
  set G4 := fixedBlockTuples (e8FiveM δ) Fr
    (e8FiveCols 4 δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG4
  set G0 := fixedBlockTuples (e8FiveM δ) Fr
    (e8FiveCols 0 δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG0
  set N : ℕ := (((Nat.card K₀ : ℤ) ^ 4 + δ * (Nat.card K₀ : ℤ) ^ 3 + (Nat.card K₀ : ℤ) ^ 2 +
    δ * (Nat.card K₀ : ℤ) + 1).natAbs) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL Tag.E8 L) := (G4 ⊔ G0).map (rootDiagUnitHom Tag.E8 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n (Units.map (entrywiseHom Fr)) := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact e8Five_card_sup δ hδ Fr hFr hℓ hℓq hq2
  have hN : N ≠ 0 := by
    refine pow_ne_zero 2 (Int.natAbs_ne_zero.2 ?_)
    have := e8FiveP_eval_ne_zero δ hδ hq2
    rwa [e8FiveP_eval] at this
  have hord : p ^ (Nat.card (adjointGroup Tag.E8 K₀)).factorization p = p ^ N.factorization p :=
    e8Five_ordProj K₀ δ hδ hp hp0 hm hordq hpq hΦ
  refine ⟨Z0, hZ0le, N, hN, hZ0card, hord, ?_⟩
  intro a hZ hap
  have hTa := hZ0le hZ
  rw [hT] at hTa
  obtain ⟨b, hb, hba⟩ := hTa
  have hab : b = a := hinj0 hba
  subst hab
  rcases e8Five_kernel_of_fixed δ hδ Fr hFr hp hp0 hΦ hb (pow_eq_one_of_orderOf_rootDiagUnit hap)
    (ne_one_of_orderOf_rootDiagUnit hp hap) with h0 | ⟨v, hv, hs, hu⟩
  · exact Or.inl h0
  · exact Or.inr ⟨v, hv, hs, hu⟩

end Frame

section Family


theorem e8Five_hfamily (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {K₀ K L : Type} [Field K₀] [Finite K₀]
    [Field K] [Finite K] [CharP K 2] [Field L] [Algebra K₀ K] [Algebra K L] [Algebra K₀ L]
    [IsScalarTower K₀ K L] [IsAlgClosure K L] [IsAlgClosure K₀ L] [CharP L 2] {f₀ p : ℕ}
    (hp : p.Prime) (hp0 : 5 < p) (hf₀ : 1 ≤ f₀) (hK : Nat.card K = 2 ^ (p * f₀))
    (hK₀ : Nat.card K₀ = 2 ^ f₀) (σ : K ≃+* K) (hσord : orderOf σ = p)
    (hσ : ∀ a, σ a = a ^ 2 ^ f₀) (n₀ : ModGL Tag.E8 L)
    (hn₀fix : Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀)
    (hR : E8FiveR δ L n₀) (S : Set (Fin Tag.E8.rank → ℤ)) (hS : S ∈ e8Five𝒮 δ) :
    ∃ P : Subgroup (ModGL Tag.E8 L),
      IsSigmaFamily (n₀ ^ p) (iterateFrobenius L 2 (f₀ * p)) S (fun _ : Unit => P) ∧
      OddJoin (rootSpan Tag.E8 L S ⊓ twistedFixedPoints (n₀ ^ p)
        (Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p))))) P ∧
      LayerDatum2 p
        (fun u => n₀ * Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) u * n₀⁻¹) P := by
  obtain ⟨v, rfl, hs, hu⟩ := hS
  obtain ⟨hnm, hnW⟩ := hR
  rcases hδ with rfl | rfl
  · obtain ⟨π, hπ⟩ := hs rfl
    exact an_hfamily (m := 2) (e8A4Embedding v) 1 (Or.inl rfl) π (K₀ := K₀) (K := K) (L := L)
      hp hp0.le hf₀ hK hK₀ σ hσord hσ n₀ hn₀fix hnm
      (fun _ i j hij => by
        change weylQuotientHom Tag.E8 L ⟨n₀, hnm⟩ • sigmaRootE8A4 v i j = _
        rw [hnW, one_smul, hπ i j hij]
        rfl)
      (fun h => absurd h (by norm_num))
  · obtain ⟨π, hπ⟩ := hu rfl
    exact an_hfamily (m := 2) (e8A4Embedding v) (-1) (Or.inr rfl) π (K₀ := K₀) (K := K) (L := L)
      hp hp0.le hf₀ hK hK₀ σ hσord hσ n₀ hn₀fix hnm
      (fun h => absurd h (by norm_num))
      (fun _ i j hij => by
        change weylQuotientHom Tag.E8 L ⟨n₀, hnm⟩ • sigmaRootE8A4 v i j = _
        rw [hnW, neg_one_smul, hπ i j hij]
        rfl)

end Family

section Sectors


theorem frobSector2_E8_five : FrobSector2 Tag.E8 5 5 :=
  frobSector2_of_families (τ := Tag.E8) (d := 1) (Or.inr (Or.inr ⟨rfl, rfl⟩)) (e := 5) (p₀ := 5)
    (by norm_num) (e8Five𝒮 1) (e8Five𝒮_ok 1) (fun L _ n => E8FiveR 1 L n)
    (fun K₀ L _ _ _ _ _ _ f₀ p hf₀ hK₀ hp hp0 hpf =>
      e8Five_frame 1 (Or.inl rfl) 5 (Or.inl ⟨rfl, rfl⟩) hf₀ hK₀ hp hp0 hpf)
    (fun K₀ K L _ _ _ _ _ _ _ _ _ _ _ _ _ f₀ p hp hp0 hf₀ hK hK₀ _ _ σ hσord hσ n₀ _ hn₀fix hRn₀ S hS =>
      e8Five_hfamily 1 (Or.inl rfl) hp hp0 hf₀ hK hK₀ σ hσord hσ n₀ hn₀fix hRn₀ S hS)

theorem frobSector2_E8_ten : FrobSector2 Tag.E8 10 5 :=
  frobSector2_of_families (τ := Tag.E8) (d := 1) (Or.inr (Or.inr ⟨rfl, rfl⟩)) (e := 10) (p₀ := 5)
    (by norm_num) (e8Five𝒮 (-1)) (e8Five𝒮_ok (-1)) (fun L _ n => E8FiveR (-1) L n)
    (fun K₀ L _ _ _ _ _ _ f₀ p hf₀ hK₀ hp hp0 hpf =>
      e8Five_frame (-1) (Or.inr rfl) 10 (Or.inr ⟨rfl, rfl⟩) hf₀ hK₀ hp hp0 hpf)
    (fun K₀ K L _ _ _ _ _ _ _ _ _ _ _ _ _ f₀ p hp hp0 hf₀ hK hK₀ _ _ σ hσord hσ n₀ _ hn₀fix hRn₀ S hS =>
      e8Five_hfamily (-1) (Or.inr rfl) hp hp0 hf₀ hK hK₀ σ hσord hσ n₀ hn₀fix hRn₀ S hS)

end Sectors

end CFSG.RankThree.PartOne.TCX.E
