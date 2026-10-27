module

public import CFSG.RankThree.PartOne.KE.E7TwelveBlock
public import CFSG.RankThree.PartOne.KE.E7TwelveNative
public import CFSG.RankThree.PartOne.KE.E7TwelveFamily
public import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.NativeSolvCyclicE
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

theorem E7_twelve_data {ℓ f : ℕ} (hℓ : ℓ.Prime) (K : Type) [Field K] [Finite K] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 12).eval (Nat.card K : ℤ)) :
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
  have hpf' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 - (Nat.card K : ℤ) ^ 2 + 1 := by
    simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord12⟩ := CTE6.e6Twelve_data hp hp3 hpf'
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E7) :=
    not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inl rfl))
  obtain ⟨hαr, hβr, hγr⟩ := e7T12_isRoot
  obtain ⟨z, hz, hn, hw, hα, hβ, hγ⟩ := e7T12_exists_cycle L
  set n : ModGL Tag.E7 L := z * e7T12M L with hndef
  have hzG : z ∈ adjointGroup Tag.E7 L :=
    (Subgroup.closure_le _).2 (by rintro _ ⟨⟨i, t⟩, rfl⟩; exact torusElt_mem_adjointGroup i t) hz
  have hnC : n ∈ adjointGroup .E7 L := mul_mem hzG e7T12M_mem_adjointGroup
  have hnW : ∀ u, weylQuotientHom .E7 L ⟨n, hn⟩ • u = e7T12W *ᵥ u := fun u => by
    rw [hw]
    exact wordProd_smul_eq_wordMat_mulVec .E7 [0, 1, 2, 3, 4, 5] u
  have hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples e7T12W Fr).map (rootDiagUnitHom .E7 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hnW Fr]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hn _ rfl Fr
  have hZeq := subtorusSigma_eq_map_fixedBlockTuples_three e7T12_commute_alpha_beta
    e7T12_commute_alpha_gamma e7T12_commute_beta_gamma hT hαr hβr hγr
  have hinj0 : Function.Injective (rootDiagUnitHom .E7 L) := rootDiagUnit_injective
  obtain ⟨hcycB, hcardB⟩ := e7Twelve_block_cyclic Fr hFr hℓ hℓq
  have hZcyc : IsCyclic (subtorusSigma n (Units.map (entrywiseHom Fr))
      (threeRootSet e7T12Alpha e7T12Beta e7T12Gamma)) := by
    rw [hZeq]
    exact (Subgroup.equivMapOfInjective _ (rootDiagUnitHom .E7 L) hinj0).isCyclic.1 hcycB
  have h24 : Nat.card K ^ 2 ≤ Nat.card K ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hN : Nat.card K ^ 4 - Nat.card K ^ 2 + 1 ≠ 0 := by omega
  have hZcard : Nat.card (subtorusSigma n (Units.map (entrywiseHom Fr))
      (threeRootSet e7T12Alpha e7T12Beta e7T12Gamma)) =
        Nat.card K ^ 4 - Nat.card K ^ 2 + 1 := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0]
    exact hcardB
  have hord : p ^ (Nat.card (adjointGroup .E7 K)).factorization p =
      p ^ (Nat.card K ^ 4 - Nat.card K ^ 2 + 1).factorization p := by
    have hrest : ∀ d ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ), d ≠ 12 → ¬ 12 ∣ d := by decide
    obtain ⟨hg, -, hR⟩ := CTE6.e6Twelve_factors hp hord12
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have h1 : 1 ≤ Nat.card K ^ 12 := Nat.one_le_pow _ _ (by omega)
    refine ordProj_card_adjointGroup_E7 hp hp3 hpq hord12 (d₀ := 12) (by decide) hrest hN
      (R := ((Nat.card K : ℤ) - 1) * ((Nat.card K : ℤ) ^ 3 + 1) * ((Nat.card K : ℤ) ^ 2 + 1) *
        ((Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1)) ?_ ?_
    · push_cast [Nat.cast_sub h1, Nat.cast_sub h24]
      ring
    · intro hdvd
      rcases hpz.dvd_or_dvd hdvd with h | h
      · exact hR h
      · exact hg h
  have hkerZ : ∀ b : Fin Tag.E7.rank → Lˣ,
      rootDiagUnit .E7 b ∈ subtorusSigma n (Units.map (entrywiseHom Fr))
        (threeRootSet e7T12Alpha e7T12Beta e7T12Gamma) →
      orderOf (rootDiagUnit .E7 b) = p →
      rootCharKernel b ⊆ threeRootSet e7T12Alpha e7T12Beta e7T12Gamma := by
    intro b hb hbp
    rw [hZeq] at hb
    obtain ⟨b', hb', hbb'⟩ := hb
    have : b' = b := hinj0 hbb'
    subst this
    rw [e7Twelve_rootCharKernel Fr hFr hp (by omega) hord12 hb'.1
      (pow_eq_one_of_orderOf_rootDiagUnit hbp) (ne_one_of_orderOf_rootDiagUnit hp hbp)]
    exact Set.Subset.rfl
  have hS3root : ∀ r ∈ threeRootSet e7T12Alpha e7T12Beta e7T12Gamma, IsRoot .E7 r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hαr, IsRoot.neg hαr, hβr, IsRoot.neg hβr, hγr, IsRoot.neg hγr]
  have hS3neg : ∀ r ∈ threeRootSet e7T12Alpha e7T12Beta e7T12Gamma,
      -r ∈ threeRootSet e7T12Alpha e7T12Beta e7T12Gamma := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [threeRootSet]
  obtain ⟨hcyc, hsolv⟩ := sigma_untwisted_data .E7 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hf hK L hp
    hp3 hordW n hnC hS3root hS3neg hZcyc hN hZcard hord hkerZ
  refine ⟨hcyc, fun hK4 => ?_⟩
  obtain ⟨k₃, _, _, _, hk₃card⟩ := exists_finite_field_into ℓ (3 * f) (by omega) L
  have hk₃ : Nat.card k₃ = Nat.card K ^ 3 := by
    rw [hk₃card, hK, ← pow_mul, mul_comm]
  have hk4 : 4 ≤ Nat.card k₃ := by
    rw [hk₃]
    nlinarith [Nat.pow_le_pow_left (show 4 ≤ Nat.card K from hK4) 3]
  let Fr3 : L →+* L := Fr.comp (Fr.comp Fr)
  have hFr3 : ∀ c, Fr3 c = c ^ Nat.card k₃ := fun c => by
    show Fr (Fr (Fr c)) = c ^ Nat.card k₃
    rw [hk₃, hFr, hFr, hFr, ← pow_mul, ← pow_mul]
    ring_nf
  have hfix3 : ∀ c, Fr3 c = c ↔ c ∈ Set.range (algebraMap k₃ L) := fun c =>
    frobenius_fixed_iff Fr3 hFr3 c
  have hS₃ : ∀ B : SL2 L, B ∈ (SpecialLinearGroup.map (algebraMap k₃ L)).range.map
      (conjSL (1 : GL (Fin 2) L)) ↔
        SpecialLinearGroup.map Fr (SpecialLinearGroup.map Fr (SpecialLinearGroup.map Fr B)) =
          B := by
    intro B
    have hcomp : SpecialLinearGroup.map Fr3 B =
        SpecialLinearGroup.map Fr (SpecialLinearGroup.map Fr (SpecialLinearGroup.map Fr B)) := by
      ext i j
      simp [Fr3]
    rw [← hcomp, sl2_map_fixed_iff Fr3 hfix3 B]
    constructor
    · rintro ⟨C, hC, rfl⟩
      rwa [conjSL_one]
    · intro hB
      exact ⟨B, hB, conjSL_one B⟩
  obtain ⟨hfin₃, hq₃⟩ := sl2_conj_range_quasisimple (L := L) (K := k₃) hk4 (1 : GL (Fin 2) L)
  have hz₃ := sl2_conj_range_centralizer (K := k₃) (L := L) (1 : GL (Fin 2) L)
  obtain ⟨P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent, -⟩ := three_A1_cyclic_family
    e7T12_commute_alpha_beta e7T12_commute_alpha_gamma e7T12_commute_beta_gamma hαr hβr hγr
    (e7T12Mul L) e7T12Mul_apply (fun A B C h => (e7T12Mul_eq_one_iff A B C).1 h) Fr n
    (fun A B C => e7T12_conj_entrywise hα hβ hγ Fr A B C) _ hS₃ hq₃ hz₃
  exact hsolv (ι' := Unit) (fun _ => P) (fun _ => hPfin) (fun _ => hPq) (fun _ => hPQ)
    (fun _ => hPR) (fun _ => hPadj) (fun _ => hPnorm)
    (fun y hy hyR hc => hPcent y hy hyR (hc ()))

theorem oddEndpoint_E7_phi12 :
    OddEndpoint .E7 fun p ℓ f => (p : ℤ) ∣ cycloVal 12 ℓ f := by
  refine oddEndpoint_E7_of_solvable_cyclic ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact E7_twelve_data hℓ K hf hK hp hp3 (by simpa [cycloVal, hK] using hc)

end CFSG.RankThree.PartOne.KE
