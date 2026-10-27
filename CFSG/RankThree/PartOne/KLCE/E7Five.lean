module

public import CFSG.RankThree.PartOne.KLCE.A2Sector
public import CFSG.RankThree.PartOne.KE.E7FiveData
public import CFSG.RankThree.PartOne.KLC.EigE7
public import CFSG.RankThree.PartOne.KLC.Degenerate

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open CFSG.RankThree.Chevalley (exhaustionPhi)

open scoped Matrix Polynomial MatrixGroups

section Embedding


@[expose] def e7Embedding : A2Embedding Tag.E7 (sigmaSet vE7) where
  ρ L _ := rhoSigma L vE7
  r := sigmaRoot vE7
  mem _ := mem_sigmaSet_iff
  isRoot _ _ hij := isRoot_sigmaRoot vE7 hij
  neg i j := sigmaRoot_neg vE7 i j
  inj _ _ := rhoSigma_injective vE7
  range _ _ := rhoSigma_range vE7
  gen L _ i j hij := rhoSigma_transvection (L := L) vE7 i j hij
  tor _ _ b := ⟨fun i => rootChar b (wbE7 vE7 i), fun A => rhoSigma_torus vE7 b A⟩
  diag _ _ A hA := rhoSigma_diagonal vE7 A hA

end Embedding

section Frame


theorem e7Five_frame {K₀ L : Type} [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
    [IsAlgClosure K₀ L] [CharP L 2] {f₀ : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) {m : ℕ}
    (hm : m = 5 ∨ m = 10) (hordq : orderOf ((Nat.card K₀ : ℕ) : ZMod p) = m)
    (hpq : ¬ p ∣ Nat.card K₀) (hR : ¬ (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 5 + δ)
    (hΦ : ((δ : ZMod p) * ((Nat.card K₀ : ℕ) : ZMod p)) ^ 4 +
      ((δ : ZMod p) * ((Nat.card K₀ : ℕ) : ZMod p)) ^ 3 +
      ((δ : ZMod p) * ((Nat.card K₀ : ℕ) : ZMod p)) ^ 2 +
      ((δ : ZMod p) * ((Nat.card K₀ : ℕ) : ZMod p)) + 1 = 0)
    (n : ModGL .E7 L) (hnm : n ∈ monomialSubgroup .E7 L)
    (hnW : ∀ u, weylQuotientHom .E7 L ⟨n, hnm⟩ • u = (δ • e7O5W) *ᵥ u) :
    ¬ p ∣ Nat.card (WeylGroup .E7) ∧ ∃ N₀ : ℕ, N₀ ≠ 0 ∧
      Nat.card (subtorusSigma n (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
        (sigmaSet vE7)) = N₀ ∧
      p ^ (Nat.card (adjointGroup .E7 K₀)).factorization p = p ^ N₀.factorization p ∧
      (∀ b : Fin Tag.E7.rank → Lˣ,
        rootDiagUnit .E7 b ∈ subtorusSigma n (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
          (sigmaSet vE7) →
        orderOf (rootDiagUnit .E7 b) = p → rootCharKernel b ⊆ sigmaSet vE7) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K₀ 2 := ⟨fun x => by
    rw [← (algebraMap K₀ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K₀ := Finite.one_lt_card
  have : Fintype K₀ := Fintype.ofFinite K₀
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  set Fr : L →+* L := iterateFrobenius L 2 f₀ with hFrdef
  have hFr' : ∀ c, Fr c = c ^ (2 ^ f₀) := fun c => iterateFrobenius_def 2 f₀ c
  have hFr : ∀ c, Fr c = c ^ Nat.card K₀ := fun c => by
    rw [hK₀]
    exact hFr' c
  have hℓq : 2 ∣ Nat.card K₀ := by
    rw [hK₀]
    exact dvd_pow_self _ (by omega)
  have hℓ : Nat.Prime 2 := Nat.prime_two
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E7) :=
    not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inl rfl))
  have hnC : n ∈ adjointGroup .E7 L := monomialSubgroup_le_adjointGroup' hnm
  have hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples (δ • e7O5W) Fr).map (rootDiagUnitHom .E7 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hnW Fr]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  have hZeq := subtorusSigma_vE7_eq_map hT
  have hinj0 : Function.Injective (rootDiagUnitHom .E7 L) := rootDiagUnit_injective
  have hδle : δ ≤ 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hδge : -1 ≤ δ := by rcases hδ with rfl | rfl <;> norm_num
  have hq5 : (1 : ℤ) < (Nat.card K₀ : ℤ) ^ 5 := by
    have : (2 : ℤ) ≤ Nat.card K₀ := by exact_mod_cast hq2
    calc (1 : ℤ) < 2 := by norm_num
      _ ≤ 2 ^ 5 := by norm_num
      _ ≤ (Nat.card K₀ : ℤ) ^ 5 := pow_le_pow_left₀ (by norm_num) this 5
  obtain ⟨hcycB, hcardB⟩ := e7Five_block_cyclic δ hδ Fr hFr hℓ hℓq hq2
  set N : ℕ := ((Nat.card K₀ : ℤ) ^ 5 - δ).natAbs with hNdef
  have hNint : (N : ℤ) = (Nat.card K₀ : ℤ) ^ 5 - δ := by
    rw [hNdef]
    exact Int.natAbs_of_nonneg (by omega)
  have hZcard : Nat.card (subtorusSigma n (Units.map (entrywiseHom Fr)) (sigmaSet vE7)) = N := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0, hcardB]
  have hN : N ≠ 0 := by
    intro h0
    rw [h0] at hNint
    push_cast at hNint
    omega
  have hord : p ^ (Nat.card (adjointGroup .E7 K₀)).factorization p =
      p ^ N.factorization p := by
    have h1 : 1 ≤ Nat.card K₀ ^ 10 := Nat.one_le_pow _ _ (by omega)
    have hrest : ∀ d ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ), d ≠ 10 → ¬ m ∣ d := by
      intro d hd hd10
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hm with rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    refine ordProj_card_adjointGroup_E7 hp (by omega) hpq hordq (d₀ := 10) (by decide) hrest hN
      (R := (Nat.card K₀ : ℤ) ^ 5 + δ) ?_ hR
    push_cast [Nat.cast_sub h1]
    rw [hNint]
    rcases hδ with rfl | rfl <;> ring
  refine ⟨hordW, N, hN, hZcard, hord, ?_⟩
  intro b hb hbp
  rw [hZeq] at hb
  obtain ⟨b', hb', hbb'⟩ := hb
  have : b' = b := hinj0 hbb'
  subst this
  rw [e7Five_rootCharKernel δ hδ Fr hFr hp (by omega) hΦ hb'.1
    (pow_eq_one_of_orderOf_rootDiagUnit hbp) (ne_one_of_orderOf_rootDiagUnit hp hbp)]
  exact six_subset_sigmaSet

end Frame


section Wrappers


theorem e7_hW {L : Type} [Field L] {n : ModGL .E7 L} (hnm : n ∈ monomialSubgroup .E7 L) (δ : ℤ)
    (hnW : ∀ u, weylQuotientHom .E7 L ⟨n, hnm⟩ • u = (δ • e7O5W) *ᵥ u) :
    ∀ i j, i ≠ j → weylQuotientHom .E7 L ⟨n, hnm⟩ • sigmaRoot vE7 i j = δ • sigmaRoot vE7 i j :=
  fun i j hij => by
    rw [hnW, Matrix.smul_mulVec, e7O5W_mulVec_sigmaRoot i j hij]

theorem e7Five_frame_plus {K₀ L : Type} [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
    [IsAlgClosure K₀ L] [CharP L 2] {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (hp : p.Prime) (hp5 : 5 < p) (hpf : (p : ℤ) ∣ (exhaustionPhi 5).eval (Nat.card K₀ : ℤ)) :
    ¬ p ∣ Nat.card (WeylGroup .E7) ∧
      ∃ n₀ : ModGL .E7 L, ∃ hn₀m : n₀ ∈ monomialSubgroup .E7 L,
        Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ ∧
        (∀ i j, i ≠ j → weylQuotientHom .E7 L ⟨n₀, hn₀m⟩ • sigmaRoot vE7 i j =
          (1 : ℤ) • sigmaRoot vE7 i j) ∧
        ∃ N₀ : ℕ, N₀ ≠ 0 ∧
          Nat.card (subtorusSigma n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
            (sigmaSet vE7)) = N₀ ∧
          p ^ (Nat.card (adjointGroup .E7 K₀)).factorization p = p ^ N₀.factorization p ∧
          (∀ b : Fin Tag.E7.rank → Lˣ,
            rootDiagUnit .E7 b ∈ subtorusSigma n₀
              (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) (sigmaSet vE7) →
            orderOf (rootDiagUnit .E7 b) = p → rootCharKernel b ⊆ sigmaSet vE7) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have h5' : (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 4 + (Nat.card K₀ : ℤ) ^ 3 + (Nat.card K₀ : ℤ) ^ 2 +
      (Nat.card K₀ : ℤ) + 1 := by simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord⟩ := CTE6.e6Five_data hp hp5 h5'
  have hΦ : ((Nat.card K₀ : ℕ) : ZMod p) ^ 4 + ((Nat.card K₀ : ℕ) : ZMod p) ^ 3 +
      ((Nat.card K₀ : ℕ) : ZMod p) ^ 2 + ((Nat.card K₀ : ℕ) : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K₀ : ℤ) ^ 4 + (Nat.card K₀ : ℤ) ^ 3 +
      (Nat.card K₀ : ℤ) ^ 2 + (Nat.card K₀ : ℤ) + 1) p).2 h5'
    simpa using this
  have hdvd : (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 5 - 1 := by
    have h := Dvd.dvd.mul_left h5' ((Nat.card K₀ : ℤ) - 1)
    have e : ((Nat.card K₀ : ℤ) - 1) * ((Nat.card K₀ : ℤ) ^ 4 + (Nat.card K₀ : ℤ) ^ 3 +
        (Nat.card K₀ : ℤ) ^ 2 + (Nat.card K₀ : ℤ) + 1) = (Nat.card K₀ : ℤ) ^ 5 - 1 := by ring
    rwa [e] at h
  set w : WeylGroup .E7 := (coxeterSystem .E7).wordProd [0, 2, 3, 4] with hwdef
  have hw : ∀ u, w • u = e7O5W *ᵥ u := wordProd_smul_eq_wordMat_mulVec .E7 [0, 2, 3, 4]
  have hcm := canonicalRep_mem_monomialSubgroup L w
  have hπ : weylQuotientHom .E7 L ⟨canonicalRep (coxeterSystem .E7) L w, hcm⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hnW : ∀ u, weylQuotientHom .E7 L ⟨canonicalRep (coxeterSystem .E7) L w, hcm⟩ • u =
      ((1 : ℤ) • e7O5W) *ᵥ u := fun u => by
    rw [hπ, one_smul]
    exact hw u
  obtain ⟨hordW, N₀, hN₀, hZcard, hord', hker⟩ := e7Five_frame hf₀ hK₀ 1 (Or.inl rfl) hp hp7
    (m := 5) (Or.inl rfl) hord hpq (fun h => CTE8.not_dvd_add_of_dvd_sub hp7 hdvd h)
    (by simpa using hΦ) _ hcm hnW
  exact ⟨hordW, canonicalRep (coxeterSystem .E7) L w, hcm,
    canonicalRep_frobenius_fixed f₀ w, e7_hW hcm 1 hnW, N₀, hN₀, hZcard, hord', hker⟩

theorem e7Five_frame_minus {K₀ L : Type} [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
    [IsAlgClosure K₀ L] [CharP L 2] {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (hp : p.Prime) (hp5 : 5 < p) (hpf : (p : ℤ) ∣ (exhaustionPhi 10).eval (Nat.card K₀ : ℤ)) :
    ¬ p ∣ Nat.card (WeylGroup .E7) ∧
      ∃ n₀ : ModGL .E7 L, ∃ hn₀m : n₀ ∈ monomialSubgroup .E7 L,
        Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ ∧
        (∀ i j, i ≠ j → weylQuotientHom .E7 L ⟨n₀, hn₀m⟩ • sigmaRoot vE7 i j =
          (-1 : ℤ) • sigmaRoot vE7 i j) ∧
        ∃ N₀ : ℕ, N₀ ≠ 0 ∧
          Nat.card (subtorusSigma n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
            (sigmaSet vE7)) = N₀ ∧
          p ^ (Nat.card (adjointGroup .E7 K₀)).factorization p = p ^ N₀.factorization p ∧
          (∀ b : Fin Tag.E7.rank → Lˣ,
            rootDiagUnit .E7 b ∈ subtorusSigma n₀
              (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) (sigmaSet vE7) →
            orderOf (rootDiagUnit .E7 b) = p → rootCharKernel b ⊆ sigmaSet vE7) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have h10' : (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 4 - (Nat.card K₀ : ℤ) ^ 3 + (Nat.card K₀ : ℤ) ^ 2 -
      (Nat.card K₀ : ℤ) + 1 := by simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord, hΦ⟩ := CTE6.twE6Ten_data hp hp5 h10'
  have hdvd : (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 5 + 1 := by
    have h := Dvd.dvd.mul_left h10' ((Nat.card K₀ : ℤ) + 1)
    have e : ((Nat.card K₀ : ℤ) + 1) * ((Nat.card K₀ : ℤ) ^ 4 - (Nat.card K₀ : ℤ) ^ 3 +
        (Nat.card K₀ : ℤ) ^ 2 - (Nat.card K₀ : ℤ) + 1) = (Nat.card K₀ : ℤ) ^ 5 + 1 := by ring
    rwa [e] at h
  set w : WeylGroup .E7 := (coxeterSystem .E7).wordProd [0, 2, 3, 4] with hwdef
  have hw : ∀ u, w • u = e7O5W *ᵥ u := wordProd_smul_eq_wordMat_mulVec .E7 [0, 2, 3, 4]
  obtain ⟨w₀, hw₀⟩ := exists_weyl_neg_one
  have hcm := canonicalRep_mem_monomialSubgroup L (w * w₀)
  have hπ : weylQuotientHom .E7 L ⟨canonicalRep (coxeterSystem .E7) L (w * w₀), hcm⟩ =
      w * w₀ := weylQuotientHom_eq (mapsRootLines_canonicalRep (w * w₀))
  have hnW : ∀ u, weylQuotientHom .E7 L
      ⟨canonicalRep (coxeterSystem .E7) L (w * w₀), hcm⟩ • u =
        ((-1 : ℤ) • e7O5W) *ᵥ u := fun u => by
    rw [hπ, mul_smul, hw₀, smul_neg, hw u, neg_one_smul, Matrix.neg_mulVec]
  obtain ⟨hordW, N₀, hN₀, hZcard, hord', hker⟩ := e7Five_frame hf₀ hK₀ (-1) (Or.inr rfl) hp hp7
    (m := 10) (Or.inr rfl) hord hpq
    (fun h => CTE8.not_dvd_add_of_dvd_sub hp7 (by simpa [sub_eq_add_neg] using h) hdvd)
    (by simpa using hΦ) _ hcm hnW
  exact ⟨hordW, canonicalRep (coxeterSystem .E7) L (w * w₀), hcm,
    canonicalRep_frobenius_fixed f₀ (w * w₀), e7_hW hcm (-1) hnW, N₀, hN₀, hZcard, hord', hker⟩

end Wrappers

section Sectors


theorem frobSector_E7_5 : FrobSector .E7 5 :=
  frobSector_of_a2Frame (τ := .E7) (d := 2) (Or.inr (Or.inl ⟨rfl, rfl⟩)) (e := 5) (p₀ := 5)
    e7Embedding 1 (Or.inl rfl)
    (fun K _ _ p f₀ hp hp5 hf₀ hK hΦ hpr => by
      by_contra hle
      have h5 : p = 5 := le_antisymm (not_lt.1 hle) hp5
      subst h5
      have hpK : ¬ 5 ∣ Nat.card K := by
        intro h
        rw [hK] at h
        have := Nat.le_of_dvd (by norm_num) (Nat.prime_five.dvd_of_dvd_pow h)
        omega
      have h1 : (5 : ℤ) ∣ (Nat.card K : ℤ) - 1 :=
        KLC.dvd_sub_one_of_dvd_phi_five (by exact_mod_cast hΦ)
      have h2 := KLC.two_le_pRank_E7_of_sector hp hp5 hpK (e := 1) (Or.inl rfl)
        (by simpa [exhaustionPhi] using h1)
      omega)
    (fun K₀ L _ _ _ _ _ _ f₀ p hf₀ hK₀ hp hp5 hpf =>
      e7Five_frame_plus (K₀ := K₀) (L := L) hf₀ hK₀ hp hp5 hpf)

theorem layerSector_E7_5 : KLC.LayerSector .E7 5 := layerSector_of_frob frobSector_E7_5

theorem frobSector_E7_10 : FrobSector .E7 10 :=
  frobSector_of_a2Frame (τ := .E7) (d := 2) (Or.inr (Or.inl ⟨rfl, rfl⟩)) (e := 10) (p₀ := 5)
    e7Embedding (-1) (Or.inr rfl)
    (fun K _ _ p f₀ hp hp5 hf₀ hK hΦ hpr => by
      by_contra hle
      have h5 : p = 5 := le_antisymm (not_lt.1 hle) hp5
      subst h5
      have hpK : ¬ 5 ∣ Nat.card K := by
        intro h
        rw [hK] at h
        have := Nat.le_of_dvd (by norm_num) (Nat.prime_five.dvd_of_dvd_pow h)
        omega
      have h1 : (5 : ℤ) ∣ (Nat.card K : ℤ) + 1 :=
        KLC.dvd_add_one_of_dvd_phi_ten (by exact_mod_cast hΦ)
      have h2 := KLC.two_le_pRank_E7_of_sector hp hp5 hpK (e := 2) (Or.inr (Or.inl rfl))
        (by simpa [exhaustionPhi] using h1)
      omega)
    (fun K₀ L _ _ _ _ _ _ f₀ p hf₀ hK₀ hp hp5 hpf =>
      e7Five_frame_minus (K₀ := K₀) (L := L) hf₀ hK₀ hp hp5 hpf)

theorem layerSector_E7_10 : KLC.LayerSector .E7 10 := layerSector_of_frob frobSector_E7_10

end Sectors

end CFSG.RankThree.PartOne.KLCE
