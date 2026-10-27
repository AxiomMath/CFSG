module

public import CFSG.RankThree.PartOne.KE.E8A2Sigma
public import CFSG.RankThree.PartOne.KE.E8NineBlock
public import CFSG.RankThree.PartOne.KE.A1E8Seven
public import CFSG.RankThree.PartOne.KE.CTTwistedArith
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

@[expose] def vE8 : WeylGroup Tag.E8 :=
  (coxeterSystem Tag.E8).wordProd
    [6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6,
      3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3]

theorem vE8_smul (u : Fin Tag.E8.rank → ℤ) : vE8 • u = e8O9V *ᵥ u :=
  wordProd_smul_eq_wordMat_mulVec .E8
    [6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6,
      3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3] u

theorem sigmaRootE8_vE8_01 : sigmaRootE8 vE8 0 1 = e8O9Alpha := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hVα, -⟩ :=
    E8_order_nine_lattice_coupled_torus_and_exact_A2_root_kernel
  rw [sigmaRootE8_eq_smul, e8chainRoot13_values.1, vE8_smul]
  exact hVα

theorem sigmaRootE8_vE8_12 : sigmaRootE8 vE8 1 2 = e8O9Theta := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hVθ⟩ :=
    E8_order_nine_lattice_coupled_torus_and_exact_A2_root_kernel
  rw [sigmaRootE8_eq_smul, e8chainRoot13_values.2.1, vE8_smul]
  exact hVθ

theorem sigmaRootE8_vE8_10 : sigmaRootE8 vE8 1 0 = -e8O9Alpha := by
  rw [← sigmaRootE8_neg, sigmaRootE8_vE8_01]

theorem sigmaRootE8_vE8_21 : sigmaRootE8 vE8 2 1 = -e8O9Theta := by
  rw [← sigmaRootE8_neg, sigmaRootE8_vE8_12]

theorem sigmaRootE8_vE8_02 : sigmaRootE8 vE8 0 2 = e8O9Alpha + e8O9Theta := by
  rw [← sigmaRootE8_add vE8 0 1 2, sigmaRootE8_vE8_01, sigmaRootE8_vE8_12]

theorem sigmaRootE8_vE8_20 : sigmaRootE8 vE8 2 0 = -(e8O9Alpha + e8O9Theta) := by
  rw [← sigmaRootE8_neg, sigmaRootE8_vE8_02]

theorem e8O9W_mulVec_sigmaRootE8 (i j : Fin 3) (hij : i ≠ j) :
    e8O9W *ᵥ sigmaRootE8 vE8 i j = sigmaRootE8 vE8 i j := by
  obtain ⟨-, -, -, -, hWα, hWθ, -⟩ := E8_order_nine_lattice_coupled_torus_and_exact_A2_root_kernel
  have hWαθ : e8O9W *ᵥ (e8O9Alpha + e8O9Theta) = e8O9Alpha + e8O9Theta := by
    rw [Matrix.mulVec_add, hWα, hWθ]
  have hWna : e8O9W *ᵥ (-e8O9Alpha) = -e8O9Alpha := by rw [Matrix.mulVec_neg, hWα]
  have hWnθ : e8O9W *ᵥ (-e8O9Theta) = -e8O9Theta := by rw [Matrix.mulVec_neg, hWθ]
  have hWnαθ : e8O9W *ᵥ (-(e8O9Alpha + e8O9Theta)) = -(e8O9Alpha + e8O9Theta) := by
    rw [Matrix.mulVec_neg, hWαθ]
  match i, j, hij with
  | 0, 0, h => exact absurd rfl h
  | 0, 1, _ => rw [sigmaRootE8_vE8_01]; exact hWα
  | 0, 2, _ => rw [sigmaRootE8_vE8_02]; exact hWαθ
  | 1, 0, _ => rw [sigmaRootE8_vE8_10]; exact hWna
  | 1, 1, h => exact absurd rfl h
  | 1, 2, _ => rw [sigmaRootE8_vE8_12]; exact hWθ
  | 2, 0, _ => rw [sigmaRootE8_vE8_20]; exact hWnαθ
  | 2, 1, _ => rw [sigmaRootE8_vE8_21]; exact hWnθ
  | 2, 2, h => exact absurd rfl h

theorem mem_sigmaSetE8_iff {r : Fin Tag.E8.rank → ℤ} :
    r ∈ sigmaSetE8 vE8 ↔ ∃ i j : Fin 3, i ≠ j ∧ r = sigmaRootE8 vE8 i j := by
  rw [sigmaSetE8_eq]
  rfl

theorem sigmaRootE8_mem_sigmaSetE8 {i j : Fin 3} (hij : i ≠ j) :
    sigmaRootE8 vE8 i j ∈ sigmaSetE8 vE8 :=
  mem_sigmaSetE8_iff.2 ⟨i, j, hij, rfl⟩

theorem sigmaSetE8_isRoot : ∀ r ∈ sigmaSetE8 vE8, IsRoot Tag.E8 r := fun r hr => by
  obtain ⟨i, j, hij, rfl⟩ := mem_sigmaSetE8_iff.1 hr
  exact isRoot_sigmaRootE8 vE8 hij

theorem sigmaSetE8_neg : ∀ r ∈ sigmaSetE8 vE8, -r ∈ sigmaSetE8 vE8 := fun r hr => by
  obtain ⟨i, j, hij, rfl⟩ := mem_sigmaSetE8_iff.1 hr
  rw [sigmaRootE8_neg]
  exact sigmaRootE8_mem_sigmaSetE8 hij.symm

theorem six_subset_sigmaSetE8 :
    ({e8O9Alpha, -e8O9Alpha, e8O9Theta, -e8O9Theta, e8O9Alpha + e8O9Theta,
      -(e8O9Alpha + e8O9Theta)} : Set (Fin Tag.E8.rank → ℤ)) ⊆ sigmaSetE8 vE8 := by
  intro r hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · have := sigmaRootE8_mem_sigmaSetE8 (show (0 : Fin 3) ≠ 1 by decide)
    rwa [sigmaRootE8_vE8_01] at this
  · have := sigmaRootE8_mem_sigmaSetE8 (show (1 : Fin 3) ≠ 0 by decide)
    rwa [sigmaRootE8_vE8_10] at this
  · have := sigmaRootE8_mem_sigmaSetE8 (show (1 : Fin 3) ≠ 2 by decide)
    rwa [sigmaRootE8_vE8_12] at this
  · have := sigmaRootE8_mem_sigmaSetE8 (show (2 : Fin 3) ≠ 1 by decide)
    rwa [sigmaRootE8_vE8_21] at this
  · have := sigmaRootE8_mem_sigmaSetE8 (show (0 : Fin 3) ≠ 2 by decide)
    rwa [sigmaRootE8_vE8_02] at this
  · have := sigmaRootE8_mem_sigmaSetE8 (show (2 : Fin 3) ≠ 0 by decide)
    rwa [sigmaRootE8_vE8_20] at this

end Sigma


section Centralizer

variable {L : Type} [Field L]

theorem rootChar_sigmaRootE8_vE8 {a : Fin Tag.E8.rank → Lˣ} (h1 : rootChar a e8O9Alpha = 1)
    (h2 : rootChar a e8O9Theta = 1) (i j : Fin 3) : rootChar a (sigmaRootE8 vE8 i j) = 1 := by
  have e1 : rootChar a (wbE8 vE8 0) = rootChar a (wbE8 vE8 1) := by
    have h := h1
    rw [← sigmaRootE8_vE8_01, sigmaRootE8, rootChar_sub] at h
    exact mul_inv_eq_one.1 h
  have e2 : rootChar a (wbE8 vE8 1) = rootChar a (wbE8 vE8 2) := by
    have h := h2
    rw [← sigmaRootE8_vE8_12, sigmaRootE8, rootChar_sub] at h
    exact mul_inv_eq_one.1 h
  have hc : ∀ k : Fin 3, rootChar a (wbE8 vE8 k) = rootChar a (wbE8 vE8 0) := fun k => by
    match k with
    | 0 => rfl
    | 1 => exact e1.symm
    | 2 => exact e2.symm.trans e1.symm
  rw [sigmaRootE8, rootChar_sub, hc i, hc j, mul_inv_cancel]

theorem rootDiagUnit_mem_centralizer_sigmaE8_iff (a : Fin Tag.E8.rank → Lˣ) :
    rootDiagUnit Tag.E8 a ∈ Subgroup.centralizer
        ((rootSpan Tag.E8 L (sigmaSetE8 vE8) : Subgroup (ModGL Tag.E8 L)) :
          Set (ModGL Tag.E8 L)) ↔
      rootChar a e8O9Alpha = 1 ∧ rootChar a e8O9Theta = 1 := by
  constructor
  · intro h
    have key : ∀ r : Fin Tag.E8.rank → ℤ, r ∈ sigmaSetE8 vE8 → -r ∈ sigmaSetE8 vE8 →
        IsRoot Tag.E8 r → rootChar a r = 1 := fun r hr hnr hrt => by
      have hle := rootRankOneGroup_le_rootSpan (L := L) hrt hr hnr
      refine (rootDiagUnit_mem_centralizer_iff hrt a).1 ?_
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact Subgroup.mem_centralizer_iff.1 h g (hle hg)
    have hα : e8O9Alpha ∈ sigmaSetE8 vE8 := six_subset_sigmaSetE8 (by simp)
    have hnα : -e8O9Alpha ∈ sigmaSetE8 vE8 := six_subset_sigmaSetE8 (by simp)
    have hθ : e8O9Theta ∈ sigmaSetE8 vE8 := six_subset_sigmaSetE8 (by simp)
    have hnθ : -e8O9Theta ∈ sigmaSetE8 vE8 := six_subset_sigmaSetE8 (by simp)
    exact ⟨key _ hα hnα (sigmaSetE8_isRoot _ hα), key _ hθ hnθ (sigmaSetE8_isRoot _ hθ)⟩
  · rintro ⟨h1, h2⟩
    have hsub : sigmaSetE8 vE8 ⊆ rootCharKernel a := fun r hr => by
      obtain ⟨i, j, hij, rfl⟩ := mem_sigmaSetE8_iff.1 hr
      exact ⟨isRoot_sigmaRootE8 vE8 hij, rootChar_sigmaRootE8_vE8 h1 h2 i j⟩
    have hle := rootSpan_le_centralizer (K := L) a hsub
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

theorem subtorusSigma_vE8_eq_map [IsAlgClosed L] {n : ModGL Tag.E8 L}
    {Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L}
    {M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ} {Fr : L →+* L}
    (hT : twistedTorusOf n Φ = (fixedCharTuples M Fr).map (rootDiagUnitHom Tag.E8 L)) :
    subtorusSigma n Φ (sigmaSetE8 vE8) =
      (fixedBlockTuples M Fr {e8O9Alpha, e8O9Theta}).map (rootDiagUnitHom Tag.E8 L) := by
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    rw [hT] at hx1
    obtain ⟨a, ha, rfl⟩ := hx1
    have h := (rootDiagUnit_mem_centralizer_sigmaE8_iff a).1 hx2
    refine ⟨a, ⟨ha, fun u hu => ?_⟩, rfl⟩
    rcases hu with rfl | rfl
    exacts [h.1, h.2]
  · rintro ⟨a, ⟨ha, hrt⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hT]
      exact ⟨a, ha, rfl⟩
    · exact (rootDiagUnit_mem_centralizer_sigmaE8_iff a).2 ⟨hrt _ (by simp), hrt _ (by simp)⟩

end Centralizer


section Family

theorem e8_nine_family {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {L : Type} [Field L] [IsAlgClosed L]
    {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f)
    (hq : 2 < ℓ ^ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : ∀ u, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • u = (δ • e8O9W) *ᵥ u) :
    ∃ P : Unit → Subgroup (ModGL Tag.E8 L), IsSigmaFamily n Fr (sigmaSetE8 vE8) P := by
  classical
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f by omega)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  choose! ε hε using fun (i j : Fin 3) (hij : i ≠ j) =>
    rhoSigmaE8_transvection (L := L) vE8 i j hij
  have htor : ∀ b : Fin Tag.E8.rank → Lˣ, ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
      rootDiagUnit Tag.E8 b * rhoSigmaE8 L vE8 A * (rootDiagUnit Tag.E8 b)⁻¹ =
        rhoSigmaE8 L vE8 (conjDiag3 d A) := fun b =>
    ⟨fun i => rootChar b (wbE8 vE8 i), fun A => rhoSigmaE8_torus vE8 b A⟩
  have hdiag : ∀ A : SL(3, L), (∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) →
      rhoSigmaE8 L vE8 A ∈ torusGroup Tag.E8 L := fun A hA => rhoSigmaE8_diagonal vE8 A hA
  rcases hδ with rfl | rfl
  ·
    have hconj : ∀ i j : Fin 3, i ≠ j → ∃ b : Lˣ, ∀ c : L,
        n * pinnedX Tag.E8 L (sigmaRootE8 vE8 i j) c * n⁻¹ =
          pinnedX Tag.E8 L (sigmaRootE8 vE8 i j) ((b : L) * c) := fun i j hij => by
      obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (isRoot_sigmaRootE8 vE8 hij)
      refine ⟨μ, fun c => ?_⟩
      rw [hμ c, hnW, one_smul, e8O9W_mulVec_sigmaRootE8 i j hij]
    obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData (τ := Tag.E8) (rhoSigmaE8 L vE8)
      (rhoSigmaE8_injective vE8) (sigmaRootE8 vE8) ε hε Fr hFrbij n (fun i j => (i, j))
      (fun i j hij => hij) (fun i j hij => ⟨i, j, hij, rfl⟩) hconj
    exact a2_family_split hℓ hf hk sigmaSetE8_isRoot (rhoSigmaE8 L vE8) (rhoSigmaE8_injective vE8)
      (rhoSigmaE8_range vE8) htor hdiag Fr n Φ' hΦ' (Equiv.refl _) b fun i j hij t => by
        rw [hshape i j hij t, hFr]
        rfl
  ·
    have hconj : ∀ i j : Fin 3, i ≠ j → ∃ b : Lˣ, ∀ c : L,
        n * pinnedX Tag.E8 L (sigmaRootE8 vE8 i j) c * n⁻¹ =
          pinnedX Tag.E8 L (sigmaRootE8 vE8 j i) ((b : L) * c) := fun i j hij => by
      obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (isRoot_sigmaRootE8 vE8 hij)
      refine ⟨μ, fun c => ?_⟩
      rw [hμ c, hnW, neg_one_smul, Matrix.neg_mulVec, e8O9W_mulVec_sigmaRootE8 i j hij,
        sigmaRootE8_neg]
    obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData (τ := Tag.E8) (rhoSigmaE8 L vE8)
      (rhoSigmaE8_injective vE8) (sigmaRootE8 vE8) ε hε Fr hFrbij n (fun i j => (j, i))
      (fun i j hij => hij.symm) (fun i j hij => ⟨j, i, hij.symm, rfl⟩) hconj
    exact a2_family_unitary hℓ hf hk hq sigmaSetE8_isRoot (rhoSigmaE8 L vE8)
      (rhoSigmaE8_injective vE8)
      (rhoSigmaE8_range vE8) htor hdiag Fr n Φ' hΦ' (Equiv.refl _) b fun i j hij t => by
        rw [hshape i j hij t, hFr]
        rfl

end Family


namespace CTE8N

theorem phi9_data {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 6 + (q : ℤ) ^ 3 + 1) :
    7 < p ∧ ¬ p ∣ q ∧ orderOf (q : ZMod p) = 9 ∧ (p : ℤ) ∣ (q : ℤ) ^ 9 - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx : (q : ZMod p) ^ 6 + (q : ZMod p) ^ 3 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 6 + (q : ℤ) ^ 3 + 1) p).2 h
    simpa using this
  have hq0 : ¬ p ∣ q := by
    intro hdvd
    have hq0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 hdvd
    rw [hq0] at hx
    simp at hx
  obtain ⟨x, hxdef⟩ : ∃ x : ZMod p, x = (q : ZMod p) := ⟨_, rfl⟩
  rw [← hxdef] at hx
  have h9 : x ^ 9 = 1 := by linear_combination (x ^ 3 - 1) * hx
  have h3ne : ((3 : ℕ) : ZMod p) ≠ 0 := CTE6.natCast_ne_zero_of_lt (by norm_num) hp3
  have hx3 : x ^ 3 ≠ 1 := by
    intro h1
    apply h3ne
    push_cast
    linear_combination hx - (x ^ 3 + 2) * h1
  have hord : orderOf x = 9 := by
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h9 fun ℓ hℓ hdvd => ?_
    have h9' : ℓ ∣ 3 ^ 2 := by simpa using hdvd
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 (hℓ.dvd_of_dvd_pow h9')
    simpa using hx3
  have hx0 : x ≠ 0 := fun h0 => by rw [h0] at h9; simp at h9
  have hdvd := ZMod.orderOf_dvd_card_sub_one hx0
  rw [hord] at hdvd
  refine ⟨by omega, hq0, by rw [← hxdef]; exact hord, ?_⟩
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 9 - 1) p).1 ?_
  push_cast
  rw [← hxdef, h9]
  ring

theorem phi18_data {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 6 - (q : ℤ) ^ 3 + 1) :
    7 < p ∧ ¬ p ∣ q ∧ orderOf (q : ZMod p) = 18 ∧ (p : ℤ) ∣ (q : ℤ) ^ 9 + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx : (q : ZMod p) ^ 6 - (q : ZMod p) ^ 3 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 6 - (q : ℤ) ^ 3 + 1) p).2 h
    simpa using this
  have hq0 : ¬ p ∣ q := by
    intro hdvd
    have hq0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 hdvd
    rw [hq0] at hx
    simp at hx
  obtain ⟨x, hxdef⟩ : ∃ x : ZMod p, x = (q : ZMod p) := ⟨_, rfl⟩
  rw [← hxdef] at hx
  have h9 : x ^ 9 + 1 = 0 := by linear_combination (x ^ 3 + 1) * hx
  have h18 : x ^ 18 = 1 := by linear_combination (x ^ 9 - 1) * h9
  have h2ne : ((2 : ℕ) : ZMod p) ≠ 0 := CTE6.natCast_ne_zero_of_lt (by norm_num) (by omega)
  have h3ne : ((3 : ℕ) : ZMod p) ≠ 0 := CTE6.natCast_ne_zero_of_lt (by norm_num) hp3
  have hord : orderOf x = 18 := by
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h18 fun ℓ hℓ hdvd => ?_
    have h18' : ℓ ∣ 2 * 3 ^ 2 := by simpa using hdvd
    rcases (Nat.Prime.dvd_mul hℓ).1 h18' with h2 | h3
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h2
      intro h1
      have h1' : x ^ 9 = 1 := by simpa using h1
      apply h2ne
      push_cast
      linear_combination h9 - h1'
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1
        (hℓ.dvd_of_dvd_pow h3)
      intro h1
      have h6 : x ^ 6 = 1 := by simpa using h1
      apply h3ne
      push_cast
      linear_combination (x ^ 3 + 2) * hx - (x ^ 3 + 1) * h6
  have hx0 : x ≠ 0 := fun h0 => by rw [h0] at h18; simp at h18
  have hdvd := ZMod.orderOf_dvd_card_sub_one hx0
  rw [hord] at hdvd
  refine ⟨by omega, hq0, by rw [← hxdef]; exact hord, ?_⟩
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 9 + 1) p).1 ?_
  push_cast
  rw [← hxdef]
  exact h9

end CTE8N


section Main

theorem exists_weyl_neg_one_E8 :
    ∃ w₀ : WeylGroup Tag.E8, ∀ u : Fin Tag.E8.rank → ℤ, w₀ • u = -u :=
  ⟨_, e8Frame_reflection_smul⟩

theorem E8_nine_aux (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hp7 : 7 < p) {m : ℕ} (hm : m = 9 ∨ m = 18)
    (hordq : orderOf ((Nat.card K : ℕ) : ZMod p) = m) (hpq : ¬ p ∣ Nat.card K)
    (hR : ¬ (p : ℤ) ∣ ((Nat.card K : ℤ) ^ 3 - δ) * ((Nat.card K : ℤ) ^ 9 + δ))
    (hΦ : ((δ : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 6 +
      ((δ : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 3 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = (δ • e8O9W) *ᵥ u) :
    (∀ Q : Subgroup (adjointGroup .E8 K), IsPGroup p Q → IsCyclic Q) ∧
      (4 ≤ Nat.card K → ∀ x : adjointGroup .E8 K, orderOf x = p →
        ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
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
  have hq3 : (8 : ℤ) ≤ (Nat.card K : ℤ) ^ 3 := by
    have : (2 : ℤ) ≤ Nat.card K := by exact_mod_cast hq2
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ (Nat.card K : ℤ) ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
  obtain ⟨hcycB, hcardB⟩ := e8Nine_block_cyclic δ hδ Fr hFr hℓ hℓq hq2
  set N : ℕ := ((Nat.card K : ℤ) ^ 6 + δ * (Nat.card K : ℤ) ^ 3 + 1).natAbs with hNdef
  have hpos : 0 < (Nat.card K : ℤ) ^ 6 + δ * (Nat.card K : ℤ) ^ 3 + 1 := by
    have h6 : (Nat.card K : ℤ) ^ 6 = (Nat.card K : ℤ) ^ 3 * (Nat.card K : ℤ) ^ 3 := by ring
    rcases hδ with rfl | rfl <;> nlinarith
  have hNint : (N : ℤ) = (Nat.card K : ℤ) ^ 6 + δ * (Nat.card K : ℤ) ^ 3 + 1 := by
    rw [hNdef]
    exact Int.natAbs_of_nonneg hpos.le
  have hZcyc : IsCyclic (subtorusSigma n (Units.map (entrywiseHom Fr)) (sigmaSetE8 vE8)) := by
    rw [hZeq]
    exact (Subgroup.equivMapOfInjective _ (rootDiagUnitHom .E8 L) hinj0).isCyclic.1 hcycB
  have hZcard : Nat.card (subtorusSigma n (Units.map (entrywiseHom Fr)) (sigmaSetE8 vE8)) = N := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0, hcardB]
  have hN : N ≠ 0 := by
    intro h0
    rw [h0] at hNint
    push_cast at hNint
    omega
  have hord : p ^ (Nat.card (adjointGroup .E8 K)).factorization p =
      p ^ N.factorization p := by
    have h1 : 1 ≤ Nat.card K ^ 18 := Nat.one_le_pow _ _ (by omega)
    have hrest : ∀ d ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ), d ≠ 18 → ¬ m ∣ d := by
      intro d hd hd18
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hm with rfl | rfl <;>
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    refine ordProj_card_adjointGroup_E8 hp hp3 hpq hordq (d₀ := 18) (by decide) hrest hN
      (R := ((Nat.card K : ℤ) ^ 3 - δ) * ((Nat.card K : ℤ) ^ 9 + δ)) ?_ hR
    push_cast [Nat.cast_sub h1]
    rw [hNint]
    rcases hδ with rfl | rfl <;> ring
  have hkerZ : ∀ b : Fin Tag.E8.rank → Lˣ,
      rootDiagUnit .E8 b ∈ subtorusSigma n (Units.map (entrywiseHom Fr)) (sigmaSetE8 vE8) →
      orderOf (rootDiagUnit .E8 b) = p → rootCharKernel b ⊆ sigmaSetE8 vE8 := by
    intro b hb hbp
    rw [hZeq] at hb
    obtain ⟨b', hb', hbb'⟩ := hb
    have : b' = b := hinj0 hbb'
    subst this
    rw [e8Nine_rootCharKernel δ hδ Fr hFr hp hp3 hΦ hb'.1
      (pow_eq_one_of_orderOf_rootDiagUnit hbp) (ne_one_of_orderOf_rootDiagUnit hp hbp)]
    exact six_subset_sigmaSetE8
  obtain ⟨hcyc, hsolv⟩ := sigma_untwisted_data .E8 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hf hK L hp
    hp3 hordW n hnC sigmaSetE8_isRoot sigmaSetE8_neg hZcyc hN hZcard hord hkerZ
  refine ⟨hcyc, fun hK4 => ?_⟩
  obtain ⟨P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ :=
    e8_nine_family hℓ hf (k := K) hK (by omega) Fr hFr' δ hδ n hnm hnW
  exact hsolv P hPfin hPq hPQ hPR hPadj hPnorm hPcent

theorem E8_nine_data (K : Type) [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 9).eval (Nat.card K : ℤ) ∨
      (p : ℤ) ∣ (exhaustionPhi 18).eval (Nat.card K : ℤ)) :
    (∀ Q : Subgroup (adjointGroup .E8 K), IsPGroup p Q → IsCyclic Q) ∧
      (4 ≤ Nat.card K → ∀ x : adjointGroup .E8 K, orderOf x = p →
        ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
          Group.IsSolvable V → IsCyclic V) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set w : WeylGroup .E8 := (coxeterSystem .E8).wordProd [4, 5, 2, 1, 3, 4, 1, 3, 1, 0] with hwdef
  have hw : ∀ u, w • u = e8O9W *ᵥ u :=
    wordProd_smul_eq_wordMat_mulVec .E8 [4, 5, 2, 1, 3, 4, 1, 3, 1, 0]
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpf with h9 | h18
  ·
    have h9' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 6 + (Nat.card K : ℤ) ^ 3 + 1 := by
      simpa [exhaustionPhi] using h9
    obtain ⟨hp7, hpq, hord, hdvd⟩ := CTE8N.phi9_data hp hp3 h9'
    have hΦ : (((1 : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 6 +
        (((1 : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 3 + 1 = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 6 + (Nat.card K : ℤ) ^ 3 + 1)
        p).2 h9'
      simpa using this
    have hcm := canonicalRep_mem_monomialSubgroup L w
    have hπ : weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L w, hcm⟩ = w :=
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)
    have hnW : ∀ u, weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L w, hcm⟩ • u =
        ((1 : ℤ) • e8O9W) *ᵥ u := fun u => by
      rw [hπ, one_smul]
      exact hw u
    have hR : ¬ (p : ℤ) ∣ ((Nat.card K : ℤ) ^ 3 - 1) * ((Nat.card K : ℤ) ^ 9 + 1) :=
      hpz.not_dvd_mul (CTTw.not_dvd_pow_sub_one hord (by norm_num))
        fun h => CTE8.not_dvd_add_of_dvd_sub hp7 hdvd h
    exact E8_nine_aux K hf hK 1 (Or.inl rfl) hp hp3 hp7 (m := 9) (Or.inl rfl) hord hpq hR hΦ
      L _ hcm hnW
  ·
    have h18' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 6 - (Nat.card K : ℤ) ^ 3 + 1 := by
      simpa [exhaustionPhi] using h18
    obtain ⟨hp7, hpq, hord, hdvd⟩ := CTE8N.phi18_data hp hp3 h18'
    have hΦ : (((-1 : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 6 +
        (((-1 : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 3 + 1 = 0 := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 6 - (Nat.card K : ℤ) ^ 3 +
        1) p).2 h18'
      push_cast at h ⊢
      linear_combination h
    obtain ⟨w₀, hw₀⟩ := exists_weyl_neg_one_E8
    have hcm := canonicalRep_mem_monomialSubgroup L (w * w₀)
    have hπ : weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L (w * w₀), hcm⟩ =
        w * w₀ := weylQuotientHom_eq (mapsRootLines_canonicalRep (w * w₀))
    have hnW : ∀ u, weylQuotientHom .E8 L
        ⟨canonicalRep (coxeterSystem .E8) L (w * w₀), hcm⟩ • u =
          ((-1 : ℤ) • e8O9W) *ᵥ u := fun u => by
      rw [hπ, mul_smul, hw₀, smul_neg, hw u, neg_one_smul, Matrix.neg_mulVec]
    have hR : ¬ (p : ℤ) ∣ ((Nat.card K : ℤ) ^ 3 - (-1)) * ((Nat.card K : ℤ) ^ 9 + (-1)) := by
      have h1 : ¬ (p : ℤ) ∣ (Nat.card K : ℤ) ^ 3 - (-1) := by
        rw [sub_neg_eq_add]
        exact CTTw.not_dvd_pow_add_one hord (by norm_num)
      have h2 : ¬ (p : ℤ) ∣ (Nat.card K : ℤ) ^ 9 + (-1) := by
        rw [← sub_eq_add_neg]
        exact CTTw.not_dvd_pow_sub_one hord (by norm_num)
      exact hpz.not_dvd_mul h1 h2
    exact E8_nine_aux K hf hK (-1) (Or.inr rfl) hp hp3 hp7 (m := 18) (Or.inr rfl) hord hpq hR hΦ
      L _ hcm hnW

theorem oddEndpoint_E8_phi9Phi18 :
    OddEndpoint .E8 fun p ℓ f => (p : ℤ) ∣ cycloVal 9 ℓ f ∨ (p : ℤ) ∣ cycloVal 18 ℓ f := by
  refine oddEndpoint_E8_of_solvable_cyclic ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact E8_nine_data K hℓ hf hK hp hp3 (by simpa [cycloVal, hK] using hc)

end Main

end CFSG.RankThree.PartOne.KE
