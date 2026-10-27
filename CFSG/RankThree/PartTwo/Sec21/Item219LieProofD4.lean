module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res7ProofCensus
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofD4
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4A
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofLayer
import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Odd
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.LayerCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Subgroup

@[expose] def KS219D4ThreeCentral :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ) (σ : K ≃+* K), 0 < n → Even n →
    Nat.card K = (2 ^ n) ^ 3 → (∀ c, σ c = c ^ (2 ^ n)) →
    ∀ z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, z ≠ 1 →
      IsCentral218 (⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) z →
      z ^ 3 = 1 ∧ ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        g * z * g⁻¹ ∈ Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom

namespace Item219LieProof


theorem ks219D4_of (h : KS219D4ThreeCentral) : KS219D4 := by
  intro X _ _ n hn hev hX x hx1 hxc
  obtain ⟨K, _, _, _, σ, hK, hσ, -, hf1, -, ⟨φ⟩⟩ :=
    Sec4.Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hX
  have hz1 : φ x ≠ 1 := fun h' => hx1 (φ.injective (h'.trans (map_one φ).symm))
  have hzc := (CFSG.AGLEmbeddingD2.Wilson.Proving.isCentral218_top_map_iff φ x).mp hxc
  obtain ⟨hz3, g, hgS⟩ := h K n σ hn hev hK hσ (φ x) hz1 hzc
  have hq1 : 2 ^ n % 3 = 1 := by
    obtain ⟨r, hr⟩ := hev
    rw [hr, ← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have hs3 : (g * φ x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hz3, mul_one, mul_inv_cancel]
  have hs1 : g * φ x * g⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    calc φ x = g⁻¹ * (g * φ x * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨c, R, hR1, hR2, hR3, hRq, F, _, _, hF, ⟨eF⟩⟩ :=
    d4_threeA_model Nat.prime_two hf1 (by decide) hq1 hK hσ hgS hs3 hs1
  let e' : X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := φ.trans (MulAut.conj (c * g))
  have he' : e' x = c * (g * φ x * g⁻¹) * c⁻¹ := by
    simp only [e', MulEquiv.trans_apply, MulAut.conj_apply]
    group
  rw [← he'] at hR1 hR2 hR3
  exact census_of_model e' x hR1 hR2 hR3 hRq (eF.trans (sl3EquivOfCard (by omega) hF))

end Item219LieProof

end CFSG.RankThree.PartTwo.Sec21
