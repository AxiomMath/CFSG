module

public import CFSG.Quasithin.Background.GoldschmidtM12SylowCore
public import CFSG.GH74.KGroups.Sz8
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCoverRootData
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.GoldschmidtAutM12Orders
public import CFSG.Quasithin.Background.GoldschmidtAutM12Transfer
public import CFSG.Quasithin.Background.GoldschmidtZ2D8Sylow
public import CFSG.Quasithin.H13.Statements
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ShultStronglyClosedTI
  CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External

namespace M12Sylow

theorem excl64_of_exponent_four {K : Type} [Group K] [Finite K]
    (hK : ∃ m : ℕ, Odd m ∧ Nat.card K = 2 ^ 6 * m)
    (h4 : ∀ (Q : Sylow 2 K) (x : ↥(Q : Subgroup K)), x ^ 4 = 1) : Excl64 K := by
  intro T _ _ hT Q n N hQN hcard hA
  obtain ⟨m, hm, hK⟩ := hK
  have h1 := card_sylow_eq hm hK Q
  have h3 := card_mul_two_pow hT (Q : Subgroup K) n N hQN hcard
  rw [h1] at h3
  have hn : 2 ^ n = 1 := by
    have : 2 ^ 6 * 2 ^ n = 2 ^ 6 * 1 := by rw [h3, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hNc : Nat.card N = Nat.card T := by rw [hcard, hn, mul_one]
  have hNtop : N = ⊤ := Subgroup.eq_top_of_card_eq N hNc
  obtain ⟨x, hx⟩ := hT.order8
  have hxN : x ∈ N := by rw [hNtop]; exact Subgroup.mem_top x
  let y : ↥(Q : Subgroup K) := hQN.some.symm ⟨x, hxN⟩
  have hy : y ^ 4 = 1 := h4 Q y
  have h5 : (hQN.some y) ^ 4 = 1 := by rw [← map_pow, hy, map_one]
  have h6 : (hQN.some y : T) ^ 4 = 1 := by
    have := congrArg Subtype.val h5
    simpa using this
  have h7 : (hQN.some y : T) = x := by simp [y]
  rw [h7] at h6
  exact hx h6

theorem suzukiRoot_pow_four (z : suzukiCoverRoot 1) : z ^ 4 = 1 := by
  rcases huppert_blackburn_XI_3_1 1 one_pos (suzukiCoverTits 1) (suzukiCoverTits_square 1) with
    ⟨_, _, _, hpow, _⟩
  exact (suzukiCoverRootBridge 1).injective (by rw [map_pow, map_one]; exact hpow _)

theorem suzuki_sylow_pow_four (Q : Sylow 2 (SuzukiMatrixGroup 1))
    (x : ↥(Q : Subgroup (SuzukiMatrixGroup 1))) : x ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let θ := Sylow.equiv (suzukiCoverSylow 1 one_pos) Q
  have hy : (θ.symm x) ^ 4 = 1 := suzukiRoot_pow_four (θ.symm x)
  have h1 : θ ((θ.symm x) ^ 4) = 1 := by rw [hy, map_one]
  rwa [map_pow, MulEquiv.apply_symm_apply] at h1

theorem nonempty_equiv_suzukiMatrix {S : Type} [Group S] (h : SuzukiModel S 2 3) :
    Nonempty (S ≃* SuzukiMatrixGroup 1) := by
  obtain ⟨-, a, ha, F, _, _, hf, hF, ⟨e⟩⟩ := h
  have ha1 : a = 1 := by omega
  subst ha1
  obtain ⟨e1⟩ := CFSG.GH74.KGroups.Sz8.suz_equiv_matrix F hF
  exact ⟨e.trans e1⟩

theorem excl64_suzuki_eight {S : Type} [Group S] [Finite S] (h : SuzukiModel S 2 3) :
    Excl64 S := by
  obtain ⟨e⟩ := nonempty_equiv_suzukiMatrix h
  have : Finite (SuzukiMatrixGroup 1) := Finite.of_equiv S e.toEquiv
  refine Excl64.of_equiv ?_ e
  refine excl64_of_exponent_four ⟨455, by decide, ?_⟩ suzuki_sylow_pow_four
  rw [suzukiCover_native_card 1 one_pos]
  norm_num

end M12Sylow

end CFSG.Quasithin.F6
