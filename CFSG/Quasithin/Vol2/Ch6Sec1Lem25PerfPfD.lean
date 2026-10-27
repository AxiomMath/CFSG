module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25PerfPfB
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4

public section

namespace CFSG.Quasithin.H13.LiePerf

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L

theorem hasBenderLevi_g2
    {S : Type} [Group S] [Finite S] {k : ℕ} (hk : 2 ≤ k) (hS : IsG2 2 k S) : HasBenderLevi S := by
  intro U hU
  obtain ⟨K, _, _, _, φ, hK, -, hres, -⟩ := even_rank_two_residual_G2 hS hU
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  refine ⟨_, hres, fun j => benderLevi_map_equiv φ.symm ?_⟩
  obtain ⟨g, hg, hker⟩ := exists_levi_hom_adjoint (τ := Tag.G2) (K := K) hK hk (g2Index j)
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have := sl2_isSimple hK4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Or.inr ⟨_, inferInstance, inferInstance, g, hg, by
    have := hker.isNilpotent
    infer_instance, k, isBenderOf_sl2 hK hk⟩

theorem hasBenderLevi_d4
    {S : Type} [Group S] [Finite S] {k : ℕ} (hk : 1 ≤ k) (hS : Is3D4 2 k S) :
    HasBenderLevi S := by
  intro U hU
  obtain ⟨K, _, _, σ, φ, hK, -, hφ, hres, -⟩ := even_rank_two_residual_triality hS hU
  have hK3 : Nat.card K = 2 ^ (3 * k) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUp : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) := by
    have h1 := hU.2.1.map φ.toMonoidHom
    rw [hφ] at h1
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe hUC)
  refine ⟨_, hres, fun j => benderLevi_map_equiv φ.symm ?_⟩
  exact benderLevi_of_leviData (fixed_leviData σ (d4Index j) hUp)

end CFSG.Quasithin.H13.LiePerf
