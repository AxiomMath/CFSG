module

public import CFSG.RankThree.PartOne.KLCE.A2Sector
public import CFSG.RankThree.PartOne.KE.E8NineData

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open CFSG.RankThree.Chevalley (exhaustionPhi)

open scoped Matrix Polynomial MatrixGroups

section Embedding


@[expose] def e8Embedding : A2Embedding Tag.E8 (sigmaSetE8 vE8) where
  ρ L _ := rhoSigmaE8 L vE8
  r := sigmaRootE8 vE8
  mem _ := mem_sigmaSetE8_iff
  isRoot _ _ hij := isRoot_sigmaRootE8 vE8 hij
  neg i j := sigmaRootE8_neg vE8 i j
  inj _ _ := rhoSigmaE8_injective vE8
  range _ _ := rhoSigmaE8_range vE8
  gen L _ i j hij := rhoSigmaE8_transvection (L := L) vE8 i j hij
  tor _ _ b := ⟨fun i => rootChar b (wbE8 vE8 i), fun A => rhoSigmaE8_torus vE8 b A⟩
  diag _ _ A hA := rhoSigmaE8_diagonal vE8 A hA

end Embedding

section Frame


theorem e8Nine_frame {K₀ L : Type} [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
    [IsAlgClosure K₀ L] [CharP L 2] {f₀ : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp7 : 7 < p) {m : ℕ}
    (hm : m = 9 ∨ m = 18) (hordq : orderOf ((Nat.card K₀ : ℕ) : ZMod p) = m)
    (hpq : ¬ p ∣ Nat.card K₀)
    (hR : ¬ (p : ℤ) ∣ ((Nat.card K₀ : ℤ) ^ 3 - δ) * ((Nat.card K₀ : ℤ) ^ 9 + δ))
    (hΦ : ((δ : ZMod p) * ((Nat.card K₀ : ℕ) : ZMod p)) ^ 6 +
      ((δ : ZMod p) * ((Nat.card K₀ : ℕ) : ZMod p)) ^ 3 + 1 = 0)
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = (δ • e8O9W) *ᵥ u) :
    ¬ p ∣ Nat.card (WeylGroup .E8) ∧ ∃ N₀ : ℕ, N₀ ≠ 0 ∧
      Nat.card (subtorusSigma n (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
        (sigmaSetE8 vE8)) = N₀ ∧
      p ^ (Nat.card (adjointGroup .E8 K₀)).factorization p = p ^ N₀.factorization p ∧
      (∀ b : Fin Tag.E8.rank → Lˣ,
        rootDiagUnit .E8 b ∈ subtorusSigma n (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
          (sigmaSetE8 vE8) →
        orderOf (rootDiagUnit .E8 b) = p → rootCharKernel b ⊆ sigmaSetE8 vE8) := by
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
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E8) :=
    not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inr rfl))
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples (δ • e8O9W) Fr).map (rootDiagUnitHom .E8 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hnW Fr]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  have hZeq := subtorusSigma_vE8_eq_map hT
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hδle : δ ≤ 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hδge : -1 ≤ δ := by rcases hδ with rfl | rfl <;> norm_num
  have hq3 : (8 : ℤ) ≤ (Nat.card K₀ : ℤ) ^ 3 := by
    have : (2 : ℤ) ≤ Nat.card K₀ := by exact_mod_cast hq2
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ (Nat.card K₀ : ℤ) ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
  obtain ⟨hcycB, hcardB⟩ := e8Nine_block_cyclic δ hδ Fr hFr hℓ hℓq hq2
  set N : ℕ := ((Nat.card K₀ : ℤ) ^ 6 + δ * (Nat.card K₀ : ℤ) ^ 3 + 1).natAbs with hNdef
  have hpos : 0 < (Nat.card K₀ : ℤ) ^ 6 + δ * (Nat.card K₀ : ℤ) ^ 3 + 1 := by
    have h6 : (Nat.card K₀ : ℤ) ^ 6 = (Nat.card K₀ : ℤ) ^ 3 * (Nat.card K₀ : ℤ) ^ 3 := by ring
    rcases hδ with rfl | rfl <;> nlinarith
  have hNint : (N : ℤ) = (Nat.card K₀ : ℤ) ^ 6 + δ * (Nat.card K₀ : ℤ) ^ 3 + 1 := by
    rw [hNdef]
    exact Int.natAbs_of_nonneg hpos.le
  have hZcard : Nat.card (subtorusSigma n (Units.map (entrywiseHom Fr)) (sigmaSetE8 vE8)) = N := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0, hcardB]
  have hN : N ≠ 0 := by
    intro h0
    rw [h0] at hNint
    push_cast at hNint
    omega
  have hord : p ^ (Nat.card (adjointGroup .E8 K₀)).factorization p =
      p ^ N.factorization p := by
    have h1 : 1 ≤ Nat.card K₀ ^ 18 := Nat.one_le_pow _ _ (by omega)
    have hrest : ∀ d ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ), d ≠ 18 → ¬ m ∣ d := by
      intro d hd hd18
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hm with rfl | rfl <;>
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    refine ordProj_card_adjointGroup_E8 hp hp3 hpq hordq (d₀ := 18) (by decide) hrest hN
      (R := ((Nat.card K₀ : ℤ) ^ 3 - δ) * ((Nat.card K₀ : ℤ) ^ 9 + δ)) ?_ hR
    push_cast [Nat.cast_sub h1]
    rw [hNint]
    rcases hδ with rfl | rfl <;> ring
  refine ⟨hordW, N, hN, hZcard, hord, ?_⟩
  intro b hb hbp
  rw [hZeq] at hb
  obtain ⟨b', hb', hbb'⟩ := hb
  have : b' = b := hinj0 hbb'
  subst this
  rw [e8Nine_rootCharKernel δ hδ Fr hFr hp hp3 hΦ hb'.1
    (pow_eq_one_of_orderOf_rootDiagUnit hbp) (ne_one_of_orderOf_rootDiagUnit hp hbp)]
  exact six_subset_sigmaSetE8

end Frame

section Wrappers


theorem e8_hW {L : Type} [Field L] {n : ModGL .E8 L} (hnm : n ∈ monomialSubgroup .E8 L) (δ : ℤ)
    (hnW : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = (δ • e8O9W) *ᵥ u) :
    ∀ i j, i ≠ j → weylQuotientHom .E8 L ⟨n, hnm⟩ • sigmaRootE8 vE8 i j =
      δ • sigmaRootE8 vE8 i j :=
  fun i j hij => by
    rw [hnW, Matrix.smul_mulVec, e8O9W_mulVec_sigmaRootE8 i j hij]

theorem e8Nine_frame_plus {K₀ L : Type} [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
    [IsAlgClosure K₀ L] [CharP L 2] {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (hp : p.Prime) (hp3 : 3 < p) (hpf : (p : ℤ) ∣ (exhaustionPhi 9).eval (Nat.card K₀ : ℤ)) :
    ¬ p ∣ Nat.card (WeylGroup .E8) ∧
      ∃ n₀ : ModGL .E8 L, ∃ hn₀m : n₀ ∈ monomialSubgroup .E8 L,
        Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ ∧
        (∀ i j, i ≠ j → weylQuotientHom .E8 L ⟨n₀, hn₀m⟩ • sigmaRootE8 vE8 i j =
          (1 : ℤ) • sigmaRootE8 vE8 i j) ∧
        ∃ N₀ : ℕ, N₀ ≠ 0 ∧
          Nat.card (subtorusSigma n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
            (sigmaSetE8 vE8)) = N₀ ∧
          p ^ (Nat.card (adjointGroup .E8 K₀)).factorization p = p ^ N₀.factorization p ∧
          (∀ b : Fin Tag.E8.rank → Lˣ,
            rootDiagUnit .E8 b ∈ subtorusSigma n₀
              (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) (sigmaSetE8 vE8) →
            orderOf (rootDiagUnit .E8 b) = p → rootCharKernel b ⊆ sigmaSetE8 vE8) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h9' : (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 6 + (Nat.card K₀ : ℤ) ^ 3 + 1 := by
    simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord, hdvd⟩ := CTE8N.phi9_data hp hp3 h9'
  have hΦ : (((1 : ℤ) : ZMod p) * ((Nat.card K₀ : ℕ) : ZMod p)) ^ 6 +
      (((1 : ℤ) : ZMod p) * ((Nat.card K₀ : ℕ) : ZMod p)) ^ 3 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K₀ : ℤ) ^ 6 + (Nat.card K₀ : ℤ) ^ 3 + 1)
      p).2 h9'
    simpa using this
  set w : WeylGroup .E8 := (coxeterSystem .E8).wordProd [4, 5, 2, 1, 3, 4, 1, 3, 1, 0] with hwdef
  have hw : ∀ u, w • u = e8O9W *ᵥ u :=
    wordProd_smul_eq_wordMat_mulVec .E8 [4, 5, 2, 1, 3, 4, 1, 3, 1, 0]
  have hcm := canonicalRep_mem_monomialSubgroup L w
  have hπ : weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L w, hcm⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hnW : ∀ u, weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L w, hcm⟩ • u =
      ((1 : ℤ) • e8O9W) *ᵥ u := fun u => by
    rw [hπ, one_smul]
    exact hw u
  have hR : ¬ (p : ℤ) ∣ ((Nat.card K₀ : ℤ) ^ 3 - 1) * ((Nat.card K₀ : ℤ) ^ 9 + 1) :=
    hpz.not_dvd_mul (CTTw.not_dvd_pow_sub_one hord (by norm_num))
      fun h => CTE8.not_dvd_add_of_dvd_sub hp7 hdvd h
  obtain ⟨hordW, N₀, hN₀, hZcard, hord', hker⟩ := e8Nine_frame hf₀ hK₀ 1 (Or.inl rfl) hp hp3 hp7
    (m := 9) (Or.inl rfl) hord hpq hR hΦ _ hcm hnW
  exact ⟨hordW, canonicalRep (coxeterSystem .E8) L w, hcm, canonicalRep_frobenius_fixed f₀ w,
    e8_hW hcm 1 hnW, N₀, hN₀, hZcard, hord', hker⟩

theorem e8Nine_frame_minus {K₀ L : Type} [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
    [IsAlgClosure K₀ L] [CharP L 2] {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (hp : p.Prime) (hp3 : 3 < p) (hpf : (p : ℤ) ∣ (exhaustionPhi 18).eval (Nat.card K₀ : ℤ)) :
    ¬ p ∣ Nat.card (WeylGroup .E8) ∧
      ∃ n₀ : ModGL .E8 L, ∃ hn₀m : n₀ ∈ monomialSubgroup .E8 L,
        Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ ∧
        (∀ i j, i ≠ j → weylQuotientHom .E8 L ⟨n₀, hn₀m⟩ • sigmaRootE8 vE8 i j =
          (-1 : ℤ) • sigmaRootE8 vE8 i j) ∧
        ∃ N₀ : ℕ, N₀ ≠ 0 ∧
          Nat.card (subtorusSigma n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
            (sigmaSetE8 vE8)) = N₀ ∧
          p ^ (Nat.card (adjointGroup .E8 K₀)).factorization p = p ^ N₀.factorization p ∧
          (∀ b : Fin Tag.E8.rank → Lˣ,
            rootDiagUnit .E8 b ∈ subtorusSigma n₀
              (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) (sigmaSetE8 vE8) →
            orderOf (rootDiagUnit .E8 b) = p → rootCharKernel b ⊆ sigmaSetE8 vE8) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h18' : (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 6 - (Nat.card K₀ : ℤ) ^ 3 + 1 := by
    simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord, hdvd⟩ := CTE8N.phi18_data hp hp3 h18'
  have hΦ : (((-1 : ℤ) : ZMod p) * ((Nat.card K₀ : ℕ) : ZMod p)) ^ 6 +
      (((-1 : ℤ) : ZMod p) * ((Nat.card K₀ : ℕ) : ZMod p)) ^ 3 + 1 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K₀ : ℤ) ^ 6 - (Nat.card K₀ : ℤ) ^ 3 +
      1) p).2 h18'
    push_cast at h ⊢
    linear_combination h
  set w : WeylGroup .E8 := (coxeterSystem .E8).wordProd [4, 5, 2, 1, 3, 4, 1, 3, 1, 0] with hwdef
  have hw : ∀ u, w • u = e8O9W *ᵥ u :=
    wordProd_smul_eq_wordMat_mulVec .E8 [4, 5, 2, 1, 3, 4, 1, 3, 1, 0]
  obtain ⟨w₀, hw₀⟩ := exists_weyl_neg_one_E8
  have hcm := canonicalRep_mem_monomialSubgroup L (w * w₀)
  have hπ : weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L (w * w₀), hcm⟩ =
      w * w₀ := weylQuotientHom_eq (mapsRootLines_canonicalRep (w * w₀))
  have hnW : ∀ u, weylQuotientHom .E8 L
      ⟨canonicalRep (coxeterSystem .E8) L (w * w₀), hcm⟩ • u =
        ((-1 : ℤ) • e8O9W) *ᵥ u := fun u => by
    rw [hπ, mul_smul, hw₀, smul_neg, hw u, neg_one_smul, Matrix.neg_mulVec]
  have hR : ¬ (p : ℤ) ∣ ((Nat.card K₀ : ℤ) ^ 3 - (-1)) * ((Nat.card K₀ : ℤ) ^ 9 + (-1)) := by
    have h1 : ¬ (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 3 - (-1) := by
      rw [sub_neg_eq_add]
      exact CTTw.not_dvd_pow_add_one hord (by norm_num)
    have h2 : ¬ (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 9 + (-1) := by
      rw [← sub_eq_add_neg]
      exact CTTw.not_dvd_pow_sub_one hord (by norm_num)
    exact hpz.not_dvd_mul h1 h2
  obtain ⟨hordW, N₀, hN₀, hZcard, hord', hker⟩ := e8Nine_frame hf₀ hK₀ (-1) (Or.inr rfl) hp hp3
    hp7 (m := 18) (Or.inr rfl) hord hpq hR hΦ _ hcm hnW
  exact ⟨hordW, canonicalRep (coxeterSystem .E8) L (w * w₀), hcm,
    canonicalRep_frobenius_fixed f₀ (w * w₀), e8_hW hcm (-1) hnW, N₀, hN₀, hZcard, hord', hker⟩

end Wrappers

section Sectors


theorem frobSector_E8_9 : FrobSector .E8 9 :=
  frobSector_of_a2Frame (τ := .E8) (d := 1) (Or.inr (Or.inr ⟨rfl, rfl⟩)) (e := 9) (p₀ := 4)
    e8Embedding 1 (Or.inl rfl)
    (fun K _ _ p f₀ hp hp5 hf₀ hK hΦ hpr => by omega)
    (fun K₀ L _ _ _ _ _ _ f₀ p hf₀ hK₀ hp hp0 hpf =>
      e8Nine_frame_plus (K₀ := K₀) (L := L) hf₀ hK₀ hp (by omega) hpf)

theorem layerSector_E8_9 : KLC.LayerSector .E8 9 := layerSector_of_frob frobSector_E8_9

theorem frobSector_E8_18 : FrobSector .E8 18 :=
  frobSector_of_a2Frame (τ := .E8) (d := 1) (Or.inr (Or.inr ⟨rfl, rfl⟩)) (e := 18) (p₀ := 4)
    e8Embedding (-1) (Or.inr rfl)
    (fun K _ _ p f₀ hp hp5 hf₀ hK hΦ hpr => by omega)
    (fun K₀ L _ _ _ _ _ _ f₀ p hf₀ hK₀ hp hp0 hpf =>
      e8Nine_frame_minus (K₀ := K₀) (L := L) hf₀ hK₀ hp (by omega) hpf)

theorem layerSector_E8_18 : KLC.LayerSector .E8 18 := layerSector_of_frob frobSector_E8_18

end Sectors

end CFSG.RankThree.PartOne.KLCE
