module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2NoDih
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Res
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairSuzukiCenter
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2DihB

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.BenderSuzuki.MatrixGroups

namespace S143

namespace InspW2

theorem noD8_suzukiMatrixGroup (m : ℕ) (hm : 1 ≤ m) : NoD8 (SuzukiMatrixGroup m) :=
  noD8_of_sylow_involutions_central fun S x h1 h2 =>
    CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair.suzuki_sylow_involutions_mem_center m hm S x
      ⟨h1, by simpa [pow_two] using h2⟩

theorem noD8_suzukiGroup {a : ℕ} {K : Type} [Field K] [Finite K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : NoD8 (suzukiGroup a K) :=
  NoD8.of_mulEquiv (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)
    (noD8_suzukiMatrixGroup a ha)

theorem resW_sz8 : ResW fun L _ => SuzukiModel L 2 3 := by
  intro L _ _ _ hF Gc _ _ ρ ž Ŝ Kh hin _
  obtain ⟨-, a, ha, K, _, hKfin, hf, hKc, ⟨e⟩⟩ := hF
  have ha1 : a = 1 := by omega
  subst ha1
  have hK : Nat.card K = 2 ^ (2 * 1 + 1) := hKc
  have hcard : Nat.card L = 29120 := by
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
    norm_num
  have hsimple := (CFSG.LieType.Ree.suzuki_simple (a := 1) (K := K) le_rfl hK).2.2
  have hZ : Subgroup.center L = ⊥ := by
    have := hsimple
    exact center_eq_bot_of_simple e.isSimpleGroup (by rw [hcard]; norm_num)
  have h6 : 2 ^ 6 ∣ Nat.card L := ⟨455, by rw [hcard]; norm_num⟩
  obtain ⟨-, a', b', -, -, -, ha', hb', hab, hab4⟩ := exists_dihedral_in_inn hZ h6 hin
  exact hab (NoD8.of_mulEquiv e (noD8_suzukiGroup le_rfl hK) a' b' ha' hb' hab4)

end InspW2

end S143

end CFSG.Quasithin
