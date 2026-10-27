module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Defs
public import CFSG.Milestones.ASVolI.F45.D4
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207RankTwo
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenRee

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Blueprint (LieModel)


section TwoF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.Quasithin.H13.F431.TwoF4 CFSG.ASVolI.ChF.ExceptionalRoots

theorem uc22sp207_noStrongParabolic_2F4 {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : LieModel X .twistedF4 0 2 n) : NoStrongParabolic X := by
  rcases h with ⟨h0, -⟩ | ⟨-, h0, -⟩ |
    ⟨-, -, ⟨-, -, -, -, -, hn3⟩, a, hna, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h0, -⟩
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
    have : CharP K F4.prime := inferInstanceAs (CharP K 2)
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hna]
    let E' : ↥⁅reeGroup K a, reeGroup K a⁆ ≃* ↥(reeGroup K a) := MulEquiv.subgroupCongr
      (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPGen.commutator_reeGroup_eq (by omega) hK')
    let iso : DerivedCentralQuotient (reeGroup K a) ≃*
        (↥(reeGroup K a) ⧸ Subgroup.center ↥(reeGroup K a)) :=
      QuotientGroup.congr _ _ E' (Subgroup.map_center_eq E')
    obtain ⟨Φ, -⟩ := CFSG.ASVolI.burnsideF4h_ree_exists_iso hK'
    have : Finite (ModGL F4.tag K) := finite_modGL
    have : Finite (Gm K a) := Subtype.finite
    have hU := isSylowTwoOf_Ug hK'
    exact (uc22sp207_noStrongParabolic_of_rankTwo (CFSG.ASVolI.burnsideF4h_ree_system hK')
      ⟨4, rfl⟩ hU.2.1 (by rw [← Subgroup.relIndex_top_right]; exact hU.2.2)).of_mulEquiv
      ((e.trans iso).trans Φ.symm).symm
  · exact absurd h0 (by decide)

end TwoF4

theorem uc22sp207_noStrongParabolic_G2
    {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsG2 X n) : NoStrongParabolic X := by
  rcases h with ⟨h0, -⟩ | ⟨-, -, ⟨-, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h0, -⟩ | ⟨-, h0, -⟩
  · exact absurd h0 (by decide)
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn hK
    have : Finite (CFSG.Blueprint.AdjointQuotient .G2 K) := Finite.of_equiv X e.toEquiv
    have hU := CFSG.ASVolI.burnsideF4h_g2_sys_U_sylow (K := K) 2
    exact (uc22sp207_noStrongParabolic_of_rankTwo (CFSG.ASVolI.burnsideF4h_g2_sys K) ⟨3, rfl⟩
      hU.2.1 (by rw [← Subgroup.relIndex_top_right]; exact hU.2.2)).of_mulEquiv e.symm
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)

section ThreeD4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.Stage4.Hex CFSG.ASVolI

theorem uc22sp207_noStrongParabolic_3D4
    {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : Is3D4 X n) : NoStrongParabolic X := by
  rcases h with ⟨h0, -⟩ | ⟨-, -, ⟨-, hn, -⟩, K, _, _, hK, sigma, hσ, ⟨e⟩⟩ | ⟨-, h0, -⟩ |
    ⟨-, h0, -⟩
  · exact absurd h0 (by decide)
  · obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = sigma :=
      ⟨RingEquiv.ofBijective sigma ⟨sigma.injective,
        Finite.surjective_of_injective sigma.injective⟩, rfl⟩
    have hσ' : ∀ c, σ.toRingHom c = c ^ (2 ^ n) := hσ
    have hq : 2 ≤ 2 ^ n := burnsideF45_two_le_q σ Nat.prime_two hn hK hσ'
    obtain ⟨f₀, hf₀, hrange, -⟩ := burnsideF4h_tri_exists_embedding Nat.prime_two hn hK σ hσ
    let e₁ : DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ.toRingHom) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      (MonoidHom.ofInjective hf₀).trans (MulEquiv.subgroupCongr hrange)
    obtain ⟨e₂⟩ := burnsideF45_d4Model_equiv σ Nat.prime_two hn hK hσ'
    let e₃ := e.trans (e₁.trans e₂.symm)
    have : Finite (twistedGroup σ.toRingHom ⧸ Subgroup.center (twistedGroup σ.toRingHom)) :=
      Finite.of_equiv X e₃.toEquiv
    have hU := burnsideF45_d4ModelSystem_isSylow σ Nat.prime_two hn hK hσ' hq
    exact (uc22sp207_noStrongParabolic_of_rankTwo (d4ModelSystem σ.toRingHom hq hK hσ') ⟨3, rfl⟩
      hU.2.1 (by rw [← Subgroup.relIndex_top_right]; exact hU.2.2)).of_mulEquiv e₃.symm
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)

end ThreeD4

end CFSG.LocalAnalysis.UniquenessCase.UC22
