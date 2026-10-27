module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructureBasic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootSylow
public import CFSG.StronglyEmbedded.BenderBorelTransport

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.GorensteinWalter
open scoped LinearAlgebra.Projectivization MatrixGroups

universe u

variable {K : Type u} [Field K] [Finite K]

theorem charP_two_of_card {f : ℕ} (hcard : Nat.card K = 2 ^ f) : CharP K 2 := by
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hcard)

omit [Finite K] in
theorem infinity_ne_zero : psl2ProjectiveInfinity K ≠ psl2ProjectiveZero K := by
  intro h
  exact psl2AffinePoint_ne_infinity (0 : K) (by rw [psl2AffinePoint_zero]; exact h.symm)

theorem exists_sylow_eq_rootGroup {f : ℕ} (hcard : Nat.card K = 2 ^ f) :
    ∃ S : Sylow 2 (PSL2MatrixGroup K), (S : Subgroup (PSL2MatrixGroup K)) =
      psl2UpperUnipotentSubgroup K := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact psl2UpperUnipotent_isSylow K hcard

omit [Finite K] in
theorem rootGroup_isElemAbelian [CharP K 2] :
    CFSG.Open.IsElemAbelian 2 (psl2UpperUnipotentSubgroup K) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (rootGroup_commute x.property y.property).eq⟩⟩, ?_⟩
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1, one_pow]
  · have h := pow_orderOf_eq_one x
    rwa [orderOf_eq_two_of_mem_rootGroup hx hx1] at h

theorem twoRank_eq {f : ℕ} (hcard : Nat.card K = 2 ^ f) :
    CFSG.Open.twoRank (PSL2MatrixGroup K) = f := by
  let : CharP K 2 := charP_two_of_card hcard
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup hcard
  have hScard : Nat.card S = 2 ^ f := by
    rw [← hcard, ← psl2UpperUnipotentSubgroup_card K]
    exact congrArg (fun H : Subgroup (PSL2MatrixGroup K) => Nat.card H) hS
  apply IsGreatest.csSup_eq
  refine ⟨⟨psl2UpperUnipotentSubgroup K, le_top, rootGroup_isElemAbelian,
    (psl2UpperUnipotentSubgroup_card K).trans hcard⟩, ?_⟩
  rintro k ⟨E, -, -, hEcard⟩
  have hE : IsPGroup 2 E := IsPGroup.of_card hEcard
  obtain ⟨P, hEP⟩ := hE.exists_le_sylow
  have hPcard : Nat.card P = 2 ^ f := by
    rw [Sylow.card_eq_multiplicity, ← hScard, Sylow.card_eq_multiplicity]
  have hdvd : 2 ^ k ∣ 2 ^ f := hEcard ▸ hPcard ▸ Subgroup.card_dvd_of_le hEP
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd

omit [Finite K] in
theorem borel_orderOf_eq_two_iff [CharP K 2] {x : PSL2MatrixGroup K} (hx : x ∈ psl2Borel K) :
    orderOf x = 2 ↔ x ∈ psl2UpperUnipotentSubgroup K ∧ x ≠ 1 := by
  refine ⟨fun h => ⟨mem_rootGroup_of_orderOf_eq_two hx h, ?_⟩,
    fun h => orderOf_eq_two_of_mem_rootGroup h.1 h.2⟩
  rintro rfl
  rw [orderOf_one] at h
  exact absurd h (by norm_num)

theorem psl2Borel_stronglyEmbedded {f : ℕ} (hcard : Nat.card K = 2 ^ f) :
    CFSG.Open.fusionStronglyEmbedded (psl2Borel K) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup hcard
  have hN : Subgroup.normalizer ((S : Subgroup (PSL2MatrixGroup K)) : Set (PSL2MatrixGroup K)) =
      MulAction.stabilizer (PSL2MatrixGroup K) (psl2ProjectiveInfinity K) := by
    rw [hS]
    exact psl2UpperUnipotent_normalizer_eq_borel K
  have hmove : ∃ g : PSL2MatrixGroup K,
      g • psl2ProjectiveInfinity K ≠ psl2ProjectiveInfinity K :=
    ⟨standardSwap K, by rw [standardSwap_smul_infinity]; exact infinity_ne_zero.symm⟩
  have heven : Even (Nat.card (S : Subgroup (PSL2MatrixGroup K))) := by
    rw [hS, psl2UpperUnipotentSubgroup_card, hcard]
    exact (Nat.even_pow' (BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero
      hcard)).mpr even_two
  have hregS : ∀ b c : ℙ K (Fin 2 → K), b ≠ psl2ProjectiveInfinity K →
      c ≠ psl2ProjectiveInfinity K → ∃! s : S, (s : PSL2MatrixGroup K) • b = c := by
    intro b c hb hc
    obtain ⟨u, hu, huniq⟩ := rootGroup_regular hb hc
    refine ⟨⟨u, by
      change (u : PSL2MatrixGroup K) ∈ (S : Subgroup (PSL2MatrixGroup K))
      rw [hS]; exact u.property⟩, hu, fun s hs => ?_⟩
    have h := huniq ⟨s, by
      rw [← hS]; exact s.property⟩ hs
    exact Subtype.ext (congrArg Subtype.val h : (s : PSL2MatrixGroup K) = u)
  have h := CFSG.Open.fusionStronglyEmbedded_of_sylow_regular_compl S
    (psl2ProjectiveInfinity K) hN hmove heven hregS
  rwa [hN] at h

theorem linear_rank_one_point_structure (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ f) :
    (∀ (A : SL(2, K)) (z : ℙ K (Fin 2 → K)), psl2QuotientMap K A • z =
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin 2) K)).toLinearEquiv • z) ∧
    MulAction.IsMultiplyPretransitive (PSL2MatrixGroup K) (ℙ K (Fin 2 → K)) 2 ∧
    Nat.card (ℙ K (Fin 2 → K)) = Nat.card K + 1 ∧
    psl2UpperUnipotentSubgroup K ≤ psl2Borel K ∧ torus K ≤ psl2Borel K ∧
    ((psl2UpperUnipotentSubgroup K).subgroupOf (psl2Borel K)).Normal ∧
    psl2UpperUnipotentSubgroup K ⊓ torus K = ⊥ ∧
    psl2UpperUnipotentSubgroup K ⊔ torus K = psl2Borel K ∧
    torus K = psl2Borel K ⊓
      MulAction.stabilizer (PSL2MatrixGroup K) (psl2ProjectiveZero K) ∧
    IsCyclic (torus K) ∧ Nat.card (torus K) = Nat.card K - 1 ∧
    (∃ S : Sylow 2 (PSL2MatrixGroup K),
      (S : Subgroup (PSL2MatrixGroup K)) = psl2UpperUnipotentSubgroup K) ∧
    Nat.card (psl2UpperUnipotentSubgroup K) = Nat.card K ∧
    (∀ γ δ : ℙ K (Fin 2 → K), γ ≠ psl2ProjectiveInfinity K → δ ≠ psl2ProjectiveInfinity K →
      ∃! u : psl2UpperUnipotentSubgroup K, (u : PSL2MatrixGroup K) • γ = δ) ∧
    CFSG.Open.fusionStronglyEmbedded (psl2Borel K) ∧
    CFSG.Open.twoRank (PSL2MatrixGroup K) = f ∧ 2 ≤ CFSG.Open.twoRank (PSL2MatrixGroup K) ∧
    (∀ x ∈ psl2Borel K, orderOf x = 2 ↔ x ∈ psl2UpperUnipotentSubgroup K ∧ x ≠ 1) ∧
    (∀ x ∈ psl2Borel K, ∀ y ∈ psl2Borel K, orderOf x = 2 → orderOf y = 2 → Commute x y) ∧
    (∀ w : PSL2MatrixGroup K, w • psl2ProjectiveInfinity K = psl2ProjectiveZero K →
      w • psl2ProjectiveZero K = psl2ProjectiveInfinity K →
      orderOf w = 2 ∧ (∀ t ∈ torus K, w⁻¹ * t * w = t⁻¹) ∧
        {x | x ∈ torus K ∧ w⁻¹ * x * w = x⁻¹} = (torus K : Set (PSL2MatrixGroup K))) ∧
    (orderOf (standardSwap K) = 2 ∧
      standardSwap K • psl2ProjectiveInfinity K = psl2ProjectiveZero K ∧
      standardSwap K • psl2ProjectiveZero K = psl2ProjectiveInfinity K) := by
  let : CharP K 2 := charP_two_of_card hcard
  refine ⟨smul_eq_toLin, psl2_projectiveLine_two_pretransitive K,
    Projectivization.card_of_finrank_two K (Fin 2 → K) (by simp),
    psl2UpperUnipotent_le_borel, torus_le_borel, psl2UpperUnipotent_normal_in_borel,
    rootGroup_inf_torus, rootGroup_sup_torus, torus_eq_borel_inf_stabilizer_zero,
    torus_isCyclic, card_torus, exists_sylow_eq_rootGroup hcard,
    psl2UpperUnipotentSubgroup_card K, fun _ _ hγ hδ => rootGroup_regular hγ hδ,
    psl2Borel_stronglyEmbedded hcard, twoRank_eq hcard, (twoRank_eq hcard).symm ▸ hf,
    fun x hx => borel_orderOf_eq_two_iff hx, ?_, ?_,
    ⟨orderOf_standardSwap, standardSwap_smul_infinity, standardSwap_smul_zero⟩⟩
  · intro x hx y hy hx2 hy2
    exact rootGroup_commute ((borel_orderOf_eq_two_iff hx).mp hx2).1
      ((borel_orderOf_eq_two_iff hy).mp hy2).1
  · intro w hα hβ
    refine ⟨orderOf_eq_two_of_swap hα hβ, fun t ht => (torus_conj_of_swap hα hβ ht).1, ?_⟩
    ext x
    exact ⟨fun h => h.1, fun h => ⟨h, (torus_conj_of_swap hα hβ h).1⟩⟩

end CFSG.ShultStronglyClosedTI.LinearModel
