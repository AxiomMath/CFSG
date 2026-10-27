module

public import CFSG.RankThree.PartOne.KE.E7A2Sigma
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.A1E6Five
public import CFSG.RankThree.PartOne.KE.A1TwE6Ten
public import CFSG.RankThree.PartOne.KE.A1E8Seven
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (chainRoot)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)
open scoped Matrix Polynomial MatrixGroups

section Sigma

@[expose] def vE7 : WeylGroup Tag.E7 :=
  (coxeterSystem Tag.E7).wordProd [1, 3, 4, 5, 6, 2, 3, 4, 5, 0, 2, 3, 4, 2, 3, 0, 2, 1, 3]

theorem vE7_smul (u : Fin Tag.E7.rank → ℤ) : vE7 • u = e7O5V *ᵥ u :=
  wordProd_smul_eq_wordMat_mulVec .E7 [1, 3, 4, 5, 6, 2, 3, 4, 5, 0, 2, 3, 4, 2, 3, 0, 2, 1, 3] u

theorem sigmaRoot_vE7_01 : sigmaRoot vE7 0 1 = e7O5Alpha := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hVα, -⟩ :=
    E7_order_five_lattice_and_exact_A2_prime_root_kernel
  rw [sigmaRoot_eq_smul, chainRoot13_values.1, vE7_smul]
  exact hVα

theorem sigmaRoot_vE7_12 : sigmaRoot vE7 1 2 = e7O5Theta := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hVθ, -⟩ :=
    E7_order_five_lattice_and_exact_A2_prime_root_kernel
  rw [sigmaRoot_eq_smul, chainRoot13_values.2.1, vE7_smul]
  exact hVθ

theorem sigmaRoot_vE7_10 : sigmaRoot vE7 1 0 = -e7O5Alpha := by
  rw [← sigmaRoot_neg, sigmaRoot_vE7_01]

theorem sigmaRoot_vE7_21 : sigmaRoot vE7 2 1 = -e7O5Theta := by
  rw [← sigmaRoot_neg, sigmaRoot_vE7_12]

theorem sigmaRoot_vE7_02 : sigmaRoot vE7 0 2 = e7O5Alpha + e7O5Theta := by
  rw [← sigmaRoot_add vE7 0 1 2, sigmaRoot_vE7_01, sigmaRoot_vE7_12]

theorem sigmaRoot_vE7_20 : sigmaRoot vE7 2 0 = -(e7O5Alpha + e7O5Theta) := by
  rw [← sigmaRoot_neg, sigmaRoot_vE7_02]

theorem e7O5W_mulVec_sigmaRoot (i j : Fin 3) (hij : i ≠ j) :
    e7O5W *ᵥ sigmaRoot vE7 i j = sigmaRoot vE7 i j := by
  obtain ⟨-, -, -, -, -, hWα, hWθ, -⟩ := E7_order_five_lattice_and_exact_A2_prime_root_kernel
  have hWαθ : e7O5W *ᵥ (e7O5Alpha + e7O5Theta) = e7O5Alpha + e7O5Theta := by
    rw [Matrix.mulVec_add, hWα, hWθ]
  have hWna : e7O5W *ᵥ (-e7O5Alpha) = -e7O5Alpha := by rw [Matrix.mulVec_neg, hWα]
  have hWnθ : e7O5W *ᵥ (-e7O5Theta) = -e7O5Theta := by rw [Matrix.mulVec_neg, hWθ]
  have hWnαθ : e7O5W *ᵥ (-(e7O5Alpha + e7O5Theta)) = -(e7O5Alpha + e7O5Theta) := by
    rw [Matrix.mulVec_neg, hWαθ]
  match i, j, hij with
  | 0, 0, h => exact absurd rfl h
  | 0, 1, _ => rw [sigmaRoot_vE7_01]; exact hWα
  | 0, 2, _ => rw [sigmaRoot_vE7_02]; exact hWαθ
  | 1, 0, _ => rw [sigmaRoot_vE7_10]; exact hWna
  | 1, 1, h => exact absurd rfl h
  | 1, 2, _ => rw [sigmaRoot_vE7_12]; exact hWθ
  | 2, 0, _ => rw [sigmaRoot_vE7_20]; exact hWnαθ
  | 2, 1, _ => rw [sigmaRoot_vE7_21]; exact hWnθ
  | 2, 2, h => exact absurd rfl h

theorem mem_sigmaSet_iff {r : Fin Tag.E7.rank → ℤ} :
    r ∈ sigmaSet vE7 ↔ ∃ i j : Fin 3, i ≠ j ∧ r = sigmaRoot vE7 i j := by
  rw [sigmaSet_eq]
  rfl

theorem sigmaRoot_mem_sigmaSet {i j : Fin 3} (hij : i ≠ j) : sigmaRoot vE7 i j ∈ sigmaSet vE7 :=
  mem_sigmaSet_iff.2 ⟨i, j, hij, rfl⟩

theorem sigmaSet_isRoot : ∀ r ∈ sigmaSet vE7, IsRoot Tag.E7 r := fun r hr => by
  obtain ⟨i, j, hij, rfl⟩ := mem_sigmaSet_iff.1 hr
  exact isRoot_sigmaRoot vE7 hij

theorem sigmaSet_neg : ∀ r ∈ sigmaSet vE7, -r ∈ sigmaSet vE7 := fun r hr => by
  obtain ⟨i, j, hij, rfl⟩ := mem_sigmaSet_iff.1 hr
  rw [sigmaRoot_neg]
  exact sigmaRoot_mem_sigmaSet hij.symm

theorem six_subset_sigmaSet :
    ({e7O5Alpha, -e7O5Alpha, e7O5Theta, -e7O5Theta, e7O5Alpha + e7O5Theta,
      -(e7O5Alpha + e7O5Theta)} : Set (Fin Tag.E7.rank → ℤ)) ⊆ sigmaSet vE7 := by
  intro r hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · have := sigmaRoot_mem_sigmaSet (show (0 : Fin 3) ≠ 1 by decide)
    rwa [sigmaRoot_vE7_01] at this
  · have := sigmaRoot_mem_sigmaSet (show (1 : Fin 3) ≠ 0 by decide)
    rwa [sigmaRoot_vE7_10] at this
  · have := sigmaRoot_mem_sigmaSet (show (1 : Fin 3) ≠ 2 by decide)
    rwa [sigmaRoot_vE7_12] at this
  · have := sigmaRoot_mem_sigmaSet (show (2 : Fin 3) ≠ 1 by decide)
    rwa [sigmaRoot_vE7_21] at this
  · have := sigmaRoot_mem_sigmaSet (show (0 : Fin 3) ≠ 2 by decide)
    rwa [sigmaRoot_vE7_02] at this
  · have := sigmaRoot_mem_sigmaSet (show (2 : Fin 3) ≠ 0 by decide)
    rwa [sigmaRoot_vE7_20] at this

end Sigma


section Centralizer

variable {L : Type} [Field L]

theorem rootChar_sigmaRoot_vE7 {a : Fin Tag.E7.rank → Lˣ} (h1 : rootChar a e7O5Alpha = 1)
    (h2 : rootChar a e7O5Theta = 1) (i j : Fin 3) : rootChar a (sigmaRoot vE7 i j) = 1 := by
  have e1 : rootChar a (wbE7 vE7 0) = rootChar a (wbE7 vE7 1) := by
    have h := h1
    rw [← sigmaRoot_vE7_01, sigmaRoot, rootChar_sub] at h
    exact mul_inv_eq_one.1 h
  have e2 : rootChar a (wbE7 vE7 1) = rootChar a (wbE7 vE7 2) := by
    have h := h2
    rw [← sigmaRoot_vE7_12, sigmaRoot, rootChar_sub] at h
    exact mul_inv_eq_one.1 h
  have hc : ∀ k : Fin 3, rootChar a (wbE7 vE7 k) = rootChar a (wbE7 vE7 0) := fun k => by
    match k with
    | 0 => rfl
    | 1 => exact e1.symm
    | 2 => exact e2.symm.trans e1.symm
  rw [sigmaRoot, rootChar_sub, hc i, hc j, mul_inv_cancel]

theorem rootDiagUnit_mem_centralizer_sigma_iff (a : Fin Tag.E7.rank → Lˣ) :
    rootDiagUnit Tag.E7 a ∈ Subgroup.centralizer
        ((rootSpan Tag.E7 L (sigmaSet vE7) : Subgroup (ModGL Tag.E7 L)) :
          Set (ModGL Tag.E7 L)) ↔
      rootChar a e7O5Alpha = 1 ∧ rootChar a e7O5Theta = 1 := by
  constructor
  · intro h
    have key : ∀ r : Fin Tag.E7.rank → ℤ, r ∈ sigmaSet vE7 → -r ∈ sigmaSet vE7 →
        IsRoot Tag.E7 r → rootChar a r = 1 := fun r hr hnr hrt => by
      have hle := rootRankOneGroup_le_rootSpan (L := L) hrt hr hnr
      refine (rootDiagUnit_mem_centralizer_iff hrt a).1 ?_
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact Subgroup.mem_centralizer_iff.1 h g (hle hg)
    have hα : e7O5Alpha ∈ sigmaSet vE7 := six_subset_sigmaSet (by simp)
    have hnα : -e7O5Alpha ∈ sigmaSet vE7 := six_subset_sigmaSet (by simp)
    have hθ : e7O5Theta ∈ sigmaSet vE7 := six_subset_sigmaSet (by simp)
    have hnθ : -e7O5Theta ∈ sigmaSet vE7 := six_subset_sigmaSet (by simp)
    exact ⟨key _ hα hnα (sigmaSet_isRoot _ hα), key _ hθ hnθ (sigmaSet_isRoot _ hθ)⟩
  · rintro ⟨h1, h2⟩
    have hsub : sigmaSet vE7 ⊆ rootCharKernel a := fun r hr => by
      obtain ⟨i, j, hij, rfl⟩ := mem_sigmaSet_iff.1 hr
      exact ⟨isRoot_sigmaRoot vE7 hij, rootChar_sigmaRoot_vE7 h1 h2 i j⟩
    have hle := rootSpan_le_centralizer (K := L) a hsub
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

theorem subtorusSigma_vE7_eq_map [IsAlgClosed L] {n : ModGL Tag.E7 L}
    {Φ : ModGL Tag.E7 L →* ModGL Tag.E7 L}
    {M : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ} {Fr : L →+* L}
    (hT : twistedTorusOf n Φ = (fixedCharTuples M Fr).map (rootDiagUnitHom Tag.E7 L)) :
    subtorusSigma n Φ (sigmaSet vE7) =
      (fixedBlockTuples M Fr {e7O5Alpha, e7O5Theta}).map (rootDiagUnitHom Tag.E7 L) := by
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    rw [hT] at hx1
    obtain ⟨a, ha, rfl⟩ := hx1
    have h := (rootDiagUnit_mem_centralizer_sigma_iff a).1 hx2
    refine ⟨a, ⟨ha, fun u hu => ?_⟩, rfl⟩
    rcases hu with rfl | rfl
    exacts [h.1, h.2]
  · rintro ⟨a, ⟨ha, hrt⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hT]
      exact ⟨a, ha, rfl⟩
    · exact (rootDiagUnit_mem_centralizer_sigma_iff a).2 ⟨hrt _ (by simp), hrt _ (by simp)⟩

end Centralizer


section Family

theorem e7_five_family {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {L : Type} [Field L] [IsAlgClosed L]
    {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f)
    (hq : 2 < ℓ ^ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) (n : ModGL Tag.E7 L) (hnm : n ∈ monomialSubgroup Tag.E7 L)
    (hnW : ∀ u, weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • u = (δ • e7O5W) *ᵥ u) :
    ∃ P : Unit → Subgroup (ModGL Tag.E7 L), IsSigmaFamily n Fr (sigmaSet vE7) P := by
  classical
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f by omega)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  choose! ε hε using fun (i j : Fin 3) (hij : i ≠ j) =>
    rhoSigma_transvection (L := L) vE7 i j hij
  have htor : ∀ b : Fin Tag.E7.rank → Lˣ, ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
      rootDiagUnit Tag.E7 b * rhoSigma L vE7 A * (rootDiagUnit Tag.E7 b)⁻¹ =
        rhoSigma L vE7 (conjDiag3 d A) := fun b =>
    ⟨fun i => rootChar b (wbE7 vE7 i), fun A => rhoSigma_torus vE7 b A⟩
  have hdiag : ∀ A : SL(3, L), (∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) →
      rhoSigma L vE7 A ∈ torusGroup Tag.E7 L := fun A hA => rhoSigma_diagonal vE7 A hA
  rcases hδ with rfl | rfl
  ·
    have hconj : ∀ i j : Fin 3, i ≠ j → ∃ b : Lˣ, ∀ c : L,
        n * pinnedX Tag.E7 L (sigmaRoot vE7 i j) c * n⁻¹ =
          pinnedX Tag.E7 L (sigmaRoot vE7 i j) ((b : L) * c) := fun i j hij => by
      obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (isRoot_sigmaRoot vE7 hij)
      refine ⟨μ, fun c => ?_⟩
      rw [hμ c, hnW, one_smul, e7O5W_mulVec_sigmaRoot i j hij]
    obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData (τ := Tag.E7) (rhoSigma L vE7)
      (rhoSigma_injective vE7) (sigmaRoot vE7) ε hε Fr hFrbij n (fun i j => (i, j))
      (fun i j hij => hij) (fun i j hij => ⟨i, j, hij, rfl⟩) hconj
    exact a2_family_split hℓ hf hk sigmaSet_isRoot (rhoSigma L vE7) (rhoSigma_injective vE7)
      (rhoSigma_range vE7) htor hdiag Fr n Φ' hΦ' (Equiv.refl _) b fun i j hij t => by
        rw [hshape i j hij t, hFr]
        rfl
  ·
    have hconj : ∀ i j : Fin 3, i ≠ j → ∃ b : Lˣ, ∀ c : L,
        n * pinnedX Tag.E7 L (sigmaRoot vE7 i j) c * n⁻¹ =
          pinnedX Tag.E7 L (sigmaRoot vE7 j i) ((b : L) * c) := fun i j hij => by
      obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (isRoot_sigmaRoot vE7 hij)
      refine ⟨μ, fun c => ?_⟩
      rw [hμ c, hnW, neg_one_smul, Matrix.neg_mulVec, e7O5W_mulVec_sigmaRoot i j hij,
        sigmaRoot_neg]
    obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData (τ := Tag.E7) (rhoSigma L vE7)
      (rhoSigma_injective vE7) (sigmaRoot vE7) ε hε Fr hFrbij n (fun i j => (j, i))
      (fun i j hij => hij.symm) (fun i j hij => ⟨j, i, hij.symm, rfl⟩) hconj
    exact a2_family_unitary hℓ hf hk hq sigmaSet_isRoot (rhoSigma L vE7) (rhoSigma_injective vE7)
      (rhoSigma_range vE7) htor hdiag Fr n Φ' hΦ' (Equiv.refl _) b fun i j hij t => by
        rw [hshape i j hij t, hFr]
        rfl

end Family


section Main

theorem exists_weyl_neg_one :
    ∃ w₀ : WeylGroup Tag.E7, ∀ u : Fin Tag.E7.rank → ℤ, w₀ • u = -u := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ :=
    E7_order_five_lattice_and_exact_A2_prime_root_kernel
  rw [← range_weylToAut] at h
  obtain ⟨w₀, hw₀⟩ := h
  refine ⟨w₀, fun u => ?_⟩
  rw [← weylToAut_apply, hw₀]
  simp

theorem E7_five_aux (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {p : ℕ}
    (hp : p.Prime) (hp7 : 7 < p) {m : ℕ} (hm : m = 5 ∨ m = 10)
    (hordq : orderOf ((Nat.card K : ℕ) : ZMod p) = m) (hpq : ¬ p ∣ Nat.card K)
    (hR : ¬ (p : ℤ) ∣ (Nat.card K : ℤ) ^ 5 + δ)
    (hΦ : ((δ : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 4 +
      ((δ : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 3 +
      ((δ : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 2 +
      ((δ : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E7 L) (hnm : n ∈ monomialSubgroup .E7 L)
    (hnW : ∀ u, weylQuotientHom .E7 L ⟨n, hnm⟩ • u = (δ • e7O5W) *ᵥ u) :
    (∀ Q : Subgroup (adjointGroup .E7 K), IsPGroup p Q → IsCyclic Q) ∧
      (4 ≤ Nat.card K → ∀ x : adjointGroup .E7 K, orderOf x = p →
        ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))), V.Normal →
          Group.IsSolvable V → IsCyclic V) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hℓ : ℓ.Prime := Fact.out
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
  have hq5 : (1 : ℤ) < (Nat.card K : ℤ) ^ 5 := by
    have : (2 : ℤ) ≤ Nat.card K := by exact_mod_cast hq2
    calc (1 : ℤ) < 2 := by norm_num
      _ ≤ 2 ^ 5 := by norm_num
      _ ≤ (Nat.card K : ℤ) ^ 5 := pow_le_pow_left₀ (by norm_num) this 5
  obtain ⟨hcycB, hcardB⟩ := e7Five_block_cyclic δ hδ Fr hFr hℓ hℓq hq2
  set N : ℕ := ((Nat.card K : ℤ) ^ 5 - δ).natAbs with hNdef
  have hNint : (N : ℤ) = (Nat.card K : ℤ) ^ 5 - δ := by
    rw [hNdef]
    exact Int.natAbs_of_nonneg (by omega)
  have hZcyc : IsCyclic (subtorusSigma n (Units.map (entrywiseHom Fr)) (sigmaSet vE7)) := by
    rw [hZeq]
    exact (Subgroup.equivMapOfInjective _ (rootDiagUnitHom .E7 L) hinj0).isCyclic.1 hcycB
  have hZcard : Nat.card (subtorusSigma n (Units.map (entrywiseHom Fr)) (sigmaSet vE7)) = N := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0, hcardB]
  have hN : N ≠ 0 := by
    intro h0
    rw [h0] at hNint
    push_cast at hNint
    omega
  have hord : p ^ (Nat.card (adjointGroup .E7 K)).factorization p =
      p ^ N.factorization p := by
    have h1 : 1 ≤ Nat.card K ^ 10 := Nat.one_le_pow _ _ (by omega)
    have hrest : ∀ d ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ), d ≠ 10 → ¬ m ∣ d := by
      intro d hd hd10
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hm with rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    refine ordProj_card_adjointGroup_E7 hp (by omega) hpq hordq (d₀ := 10) (by decide) hrest hN
      (R := (Nat.card K : ℤ) ^ 5 + δ) ?_ hR
    push_cast [Nat.cast_sub h1]
    rw [hNint]
    rcases hδ with rfl | rfl <;> ring
  have hkerZ : ∀ b : Fin Tag.E7.rank → Lˣ,
      rootDiagUnit .E7 b ∈ subtorusSigma n (Units.map (entrywiseHom Fr)) (sigmaSet vE7) →
      orderOf (rootDiagUnit .E7 b) = p → rootCharKernel b ⊆ sigmaSet vE7 := by
    intro b hb hbp
    rw [hZeq] at hb
    obtain ⟨b', hb', hbb'⟩ := hb
    have : b' = b := hinj0 hbb'
    subst this
    rw [e7Five_rootCharKernel δ hδ Fr hFr hp (by omega) hΦ hb'.1
      (pow_eq_one_of_orderOf_rootDiagUnit hbp) (ne_one_of_orderOf_rootDiagUnit hp hbp)]
    exact six_subset_sigmaSet
  obtain ⟨hcyc, hsolv⟩ := sigma_untwisted_data .E7 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hf hK L hp
    (by omega) hordW n hnC sigmaSet_isRoot sigmaSet_neg hZcyc hN hZcard hord hkerZ
  refine ⟨hcyc, fun hK4 => ?_⟩
  obtain ⟨P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ :=
    e7_five_family hℓ hf (k := K) hK (by omega) Fr hFr' δ hδ n hnm hnW
  exact hsolv P hPfin hPq hPQ hPR hPadj hPnorm hPcent

theorem E7_five_data (K : Type) [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 5).eval (Nat.card K : ℤ) ∨
      (p : ℤ) ∣ (exhaustionPhi 10).eval (Nat.card K : ℤ)) :
    (∀ Q : Subgroup (adjointGroup .E7 K), IsPGroup p Q → IsCyclic Q) ∧
      (4 ≤ Nat.card K → ∀ x : adjointGroup .E7 K, orderOf x = p →
        ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))), V.Normal →
          Group.IsSolvable V → IsCyclic V) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set w : WeylGroup .E7 := (coxeterSystem .E7).wordProd [0, 2, 3, 4] with hwdef
  have hw : ∀ u, w • u = e7O5W *ᵥ u := wordProd_smul_eq_wordMat_mulVec .E7 [0, 2, 3, 4]
  rcases hpf with h5 | h10
  ·
    have h5' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 + (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 +
        (Nat.card K : ℤ) + 1 := by simpa [exhaustionPhi] using h5
    obtain ⟨hp7, hpq, hord⟩ := CTE6.e6Five_data hp hp5 h5'
    have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 4 + ((Nat.card K : ℕ) : ZMod p) ^ 3 +
        ((Nat.card K : ℕ) : ZMod p) ^ 2 + ((Nat.card K : ℕ) : ZMod p) + 1 = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 4 + (Nat.card K : ℤ) ^ 3 +
        (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1) p).2 h5'
      simpa using this
    have hdvd : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 5 - 1 := by
      have h := Dvd.dvd.mul_left h5' ((Nat.card K : ℤ) - 1)
      have e : ((Nat.card K : ℤ) - 1) * ((Nat.card K : ℤ) ^ 4 + (Nat.card K : ℤ) ^ 3 +
          (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1) = (Nat.card K : ℤ) ^ 5 - 1 := by ring
      rwa [e] at h
    have hcm := canonicalRep_mem_monomialSubgroup L w
    have hπ : weylQuotientHom .E7 L ⟨canonicalRep (coxeterSystem .E7) L w, hcm⟩ = w :=
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)
    have hnW : ∀ u, weylQuotientHom .E7 L ⟨canonicalRep (coxeterSystem .E7) L w, hcm⟩ • u =
        ((1 : ℤ) • e7O5W) *ᵥ u := fun u => by
      rw [hπ, one_smul]
      exact hw u
    exact E7_five_aux K hf hK 1 (Or.inl rfl) hp hp7 (m := 5) (Or.inl rfl) hord hpq
      (fun h => CTE8.not_dvd_add_of_dvd_sub hp7 hdvd h) (by simpa using hΦ) L _ hcm hnW
  ·
    have h10' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 - (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 -
        (Nat.card K : ℤ) + 1 := by simpa [exhaustionPhi] using h10
    obtain ⟨hp7, hpq, hord, hΦ⟩ := CTE6.twE6Ten_data hp hp5 h10'
    have hdvd : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 5 + 1 := by
      have h := Dvd.dvd.mul_left h10' ((Nat.card K : ℤ) + 1)
      have e : ((Nat.card K : ℤ) + 1) * ((Nat.card K : ℤ) ^ 4 - (Nat.card K : ℤ) ^ 3 +
          (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1) = (Nat.card K : ℤ) ^ 5 + 1 := by ring
      rwa [e] at h
    obtain ⟨w₀, hw₀⟩ := exists_weyl_neg_one
    have hcm := canonicalRep_mem_monomialSubgroup L (w * w₀)
    have hπ : weylQuotientHom .E7 L ⟨canonicalRep (coxeterSystem .E7) L (w * w₀), hcm⟩ =
        w * w₀ := weylQuotientHom_eq (mapsRootLines_canonicalRep (w * w₀))
    have hnW : ∀ u, weylQuotientHom .E7 L
        ⟨canonicalRep (coxeterSystem .E7) L (w * w₀), hcm⟩ • u =
          ((-1 : ℤ) • e7O5W) *ᵥ u := fun u => by
      rw [hπ, mul_smul, hw₀, smul_neg, hw u, neg_one_smul, Matrix.neg_mulVec]
    exact E7_five_aux K hf hK (-1) (Or.inr rfl) hp hp7 (m := 10) (Or.inr rfl) hord hpq
      (fun h => CTE8.not_dvd_add_of_dvd_sub hp7 (by simpa [sub_eq_add_neg] using h) hdvd)
      (by simpa using hΦ) L _ hcm hnW

theorem oddEndpoint_E7_phi5Phi10 :
    OddEndpoint .E7 fun p ℓ f =>
      5 < p ∧ ((p : ℤ) ∣ cycloVal 5 ℓ f ∨ (p : ℤ) ∣ cycloVal 10 ℓ f) := by
  refine oddEndpoint_E7_of_solvable_cyclic ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact E7_five_data K hℓ hf hK hp hc.1 (by simpa [cycloVal, hK] using hc.2)

end Main

end CFSG.RankThree.PartOne.KE
