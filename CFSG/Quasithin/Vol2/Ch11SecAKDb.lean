module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts15
public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.Quasithin.Background.A3Structure312Iso

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

namespace C10KH

theorem isPSp4_quot_center {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    IsPSp4 2 n (↥(StatedSp 2 K) ⧸ Subgroup.center ↥(StatedSp 2 K)) := by
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, fun h => ?_⟩, K, inferInstance, inferInstance, hK,
    ⟨QuotientGroup.quotientMulEquivOfEq (CFSG.LieType.Universal.Symplectic.center_eq 2 K)⟩⟩
  have h2 : 2 ^ n = 2 := (Prod.mk.inj h).2
  omega

theorem isG2_quot_center {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    IsG2 2 n (↥⁅quasithinG2 K, quasithinG2 K⁆ ⧸
      Subgroup.center ↥⁅quasithinG2 K, quasithinG2 K⁆) := by
  have := B42G2Id.charP_two_of_card hK
  obtain ⟨c, hc0, hc1⟩ :=
    B42G2Id.exists_ne_zero_ne_one_of_three_le (K := K) (hK ▸ B42G2Id.three_le_two_pow hn)
  have hc : ⁅quasithinG2 K, quasithinG2 K⁆ = cayleyGroup K := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
      cayley_commutator_eq hc0 hc1]
  have hZ : Subgroup.center ↥(cayleyGroup K) = ⊥ := A318Excl.center_cayleyGroup_eq_bot hc0 hc1
  let e₀ : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥(cayleyGroup K) := MulEquiv.subgroupCongr hc
  let e₁ : ↥⁅quasithinG2 K, quasithinG2 K⁆ ⧸ Subgroup.center ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃*
      ↥(cayleyGroup K) ⧸ Subgroup.center ↥(cayleyGroup K) :=
    QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)
  let e₂ : ↥(cayleyGroup K) ⧸ Subgroup.center ↥(cayleyGroup K) ≃* ↥(cayleyGroup K) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact IsG2.of_mulEquiv (e₁.trans e₂).symm (B42G2Id.chevalleyExceptionalModel_cayleyGroup hK hn)

end C10KH

theorem factRankTwoLieSp4G2_holds : FactRankTwoLieSp4G2 := fun _ _ _ _ hn hK =>
  ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨_, C10KH.isPSp4_quot_center hn hK⟩))),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, C10KH.isG2_quot_center hn hK⟩)))))⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
