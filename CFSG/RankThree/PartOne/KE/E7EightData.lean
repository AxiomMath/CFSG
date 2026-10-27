module

public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KE.E7EightBlock
public import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.CTTwistedArith
public import CFSG.RankThree.PartOne.KE.NativeSolvCyclicE
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.RankThree.PartOne.KE.CTCasesE6Glue
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)
open CFSG.RankThree.Classical (conjSL conjSL_one)
open scoped Matrix Polynomial MatrixGroups

theorem E7_eight_data (K : Type) [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 8).eval (Nat.card K : ℤ)) :
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
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hpf' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 + 1 := by simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord8⟩ := CTE6.e6Eight_data hp hp3 hpf'
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E7) :=
    not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inl rfl))
  obtain ⟨hk, -, -, -, hΩ⟩ := E7_three_A1_native_product_scalar_kernel_and_exact_Frobenius_swap
  obtain ⟨-, hc12, hc13, hc23, -, -, -, hbg, hbginj, -⟩ := hk L
  obtain ⟨z, hz, n, hndef, hnG, ⟨hnm, hw⟩, hα, hβ, hγ, -⟩ := hΩ L
  obtain ⟨hαr, hβr, hγr⟩ := e7A1_isRoot
  have hinj23 : ∀ B C B' C' : SL2 L,
      rootSL2 .E7 L e7O8Beta B * rootSL2 .E7 L e7O8Gamma C =
        rootSL2 .E7 L e7O8Beta B' * rootSL2 .E7 L e7O8Gamma C' → B = B' ∧ C = C' := by
    intro B C B' C' h
    rw [← hbg, ← hbg] at h
    have := hbginj h
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hnW : ∀ u, weylQuotientHom .E7 L ⟨n, hnm⟩ • u = e7O8W *ᵥ u := fun u => by
    rw [hw]
    exact wordProd_smul_eq_wordMat_mulVec .E7 [0, 1, 2, 3, 4] u
  have hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples e7O8W Fr).map (rootDiagUnitHom .E7 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hnW Fr]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  have hZeq := subtorusSigma_eq_map_fixedBlockTuples_three hc12 hc13 hc23 hT hαr hβr hγr
  have hinj0 : Function.Injective (rootDiagUnitHom .E7 L) := rootDiagUnit_injective
  obtain ⟨hcycB, hcardB⟩ := e7Eight_block_cyclic Fr hFr hℓ hℓq
  have hZcyc : IsCyclic (subtorusSigma n (Units.map (entrywiseHom Fr))
      (threeRootSet e7O8Alpha e7O8Beta e7O8Gamma)) := by
    rw [hZeq]
    exact (Subgroup.equivMapOfInjective _ (rootDiagUnitHom .E7 L) hinj0).isCyclic.1 hcycB
  have hZcard : Nat.card (subtorusSigma n (Units.map (entrywiseHom Fr))
      (threeRootSet e7O8Alpha e7O8Beta e7O8Gamma)) = Nat.card K ^ 4 + 1 := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0]
    exact hcardB
  have hN : Nat.card K ^ 4 + 1 ≠ 0 := by omega
  have hR : ¬ (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 - 1 :=
    CTTw.not_dvd_pow_sub_one hord8 (by norm_num)
  have hord : p ^ (Nat.card (adjointGroup .E7 K)).factorization p =
      p ^ (Nat.card K ^ 4 + 1).factorization p := by
    have hrest : ∀ d ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ), d ≠ 8 → ¬ 8 ∣ d := by decide
    have h1 : 1 ≤ Nat.card K ^ 8 := Nat.one_le_pow _ _ (by omega)
    refine ordProj_card_adjointGroup_E7 hp hp3 hpq hord8 (d₀ := 8) (by decide) hrest hN
      (R := (Nat.card K : ℤ) ^ 4 - 1) ?_ hR
    push_cast [Nat.cast_sub h1]
    ring
  have hkerZ : ∀ b : Fin Tag.E7.rank → Lˣ,
      rootDiagUnit .E7 b ∈ subtorusSigma n (Units.map (entrywiseHom Fr))
        (threeRootSet e7O8Alpha e7O8Beta e7O8Gamma) →
      orderOf (rootDiagUnit .E7 b) = p →
      rootCharKernel b ⊆ threeRootSet e7O8Alpha e7O8Beta e7O8Gamma := by
    intro b hb hbp
    rw [hZeq] at hb
    obtain ⟨b', hb', hbb'⟩ := hb
    have : b' = b := hinj0 hbb'
    subst this
    rw [e7Eight_rootCharKernel Fr hFr hp (by omega) hord8 hb'.1
      (pow_eq_one_of_orderOf_rootDiagUnit hbp) (ne_one_of_orderOf_rootDiagUnit hp hbp)]
    exact Set.Subset.rfl
  have hS3root : ∀ r ∈ threeRootSet e7O8Alpha e7O8Beta e7O8Gamma, IsRoot .E7 r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hαr, IsRoot.neg hαr, hβr, IsRoot.neg hβr, hγr, IsRoot.neg hγr]
  have hS3neg : ∀ r ∈ threeRootSet e7O8Alpha e7O8Beta e7O8Gamma,
      -r ∈ threeRootSet e7O8Alpha e7O8Beta e7O8Gamma := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [threeRootSet]
  have hnC : n ∈ adjointGroup .E7 L := hnG
  obtain ⟨hcyc, hsolv⟩ := sigma_untwisted_data .E7 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hf hK L hp hp3
    hordW n hnC hS3root hS3neg hZcyc hN hZcard hord hkerZ
  refine ⟨hcyc, fun hK4 => ?_⟩
  obtain ⟨k₂, _, _, _, hk₂card⟩ := exists_finite_field_into ℓ (2 * f) (by omega) L
  have hk₂ : Nat.card k₂ = Nat.card K ^ 2 := by
    rw [hk₂card, hK, ← pow_mul, mul_comm]
  have hk4 : 4 ≤ Nat.card k₂ := by
    rw [hk₂]
    nlinarith
  let Fr2 : L →+* L := Fr.comp Fr
  have hFr2 : ∀ c, Fr2 c = c ^ Nat.card k₂ := fun c => by
    show Fr (Fr c) = c ^ Nat.card k₂
    rw [hk₂, hFr, hFr, ← pow_mul, sq]
  have hfix2 : ∀ c, Fr2 c = c ↔ c ∈ Set.range (algebraMap k₂ L) := fun c =>
    frobenius_fixed_iff Fr2 hFr2 c
  have hnc : n ∈ Subgroup.centralizer
      (rootRankOneGroup .E7 L e7O8Alpha : Set (ModGL .E7 L)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    exact (mul_inv_eq_iff_eq_mul.1 (hα A)).symm
  have hS₁ : ∀ B : SL2 L, n * Units.map (entrywiseHom Fr) (rootSL2 .E7 L e7O8Alpha B) * n⁻¹ =
      rootSL2 .E7 L e7O8Alpha B ↔
        B ∈ (SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL (1 : GL (Fin 2) L)) :=
    fun B => a1_typeI_action Fr hFr hnc B
  have hS₂ : ∀ B : SL2 L, B ∈ (SpecialLinearGroup.map (algebraMap k₂ L)).range.map
      (conjSL (1 : GL (Fin 2) L)) ↔
        SpecialLinearGroup.map Fr (SpecialLinearGroup.map Fr B) = B := by
    intro B
    have hcomp : SpecialLinearGroup.map Fr2 B =
        SpecialLinearGroup.map Fr (SpecialLinearGroup.map Fr B) := by
      ext i j
      simp [Fr2]
    rw [← hcomp, sl2_map_fixed_iff Fr2 hfix2 B]
    constructor
    · rintro ⟨C, hC, rfl⟩
      rwa [conjSL_one]
    · intro hB
      exact ⟨B, hB, conjSL_one B⟩
  obtain ⟨hfin₁, hq₁⟩ := sl2_conj_range_quasisimple (L := L) (K := K) hK4 (1 : GL (Fin 2) L)
  obtain ⟨hfin₂, hq₂⟩ := sl2_conj_range_quasisimple (L := L) (K := k₂) hk4 (1 : GL (Fin 2) L)
  have hz₁ := sl2_conj_range_centralizer (K := K) (L := L) (1 : GL (Fin 2) L)
  have hz₂ := sl2_conj_range_centralizer (K := k₂) (L := L) (1 : GL (Fin 2) L)
  obtain ⟨P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent, -, -⟩ := three_A1_family hc12 hc13 hc23
    hαr hβr hγr hinj23 Fr n hβ hγ _ _ hS₁ hS₂ hq₁ hq₂ hz₁ hz₂
  exact hsolv P hPfin hPq hPQ hPR hPadj hPnorm hPcent

theorem oddEndpoint_E7_phi8 : OddEndpoint .E7 fun p ℓ f => (p : ℤ) ∣ cycloVal 8 ℓ f := by
  refine oddEndpoint_E7_of_solvable_cyclic ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact E7_eight_data K hℓ hf hK hp hp3 (by simpa [cycloVal, hK] using hc)

end CFSG.RankThree.PartOne.KE
