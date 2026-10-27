module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qModelHex
public import CFSG.GH74.GLS.Stage4.HexCoordD4
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality

public section

namespace CFSG.Quasithin.RonanE114Low

open CFSG.GH74.BNPair CFSG.GH74.GLS.Stage4.Hex CFSG.Timmesfeld.RankTwo
  CFSG.LieType.Steinberg.TwistedD4 CFSG.Open CFSG.Quasithin


theorem exists_model_data {G : Type} [Group G] [Finite G] {L T : Subgroup G} [hLn : L.Normal]
    (hT : IsSylowIn 2 T ⊤) {n : ℕ} (hL : Is3D4 2 n ↥L) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (K : Type) (_ : Field K) (_ : CharP K 2)
      (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c) (D : RankTwoSystem X 6)
      (ψ : ∀ i : Fin 6, d43Par σ i → X),
      D4Coords D hσ ψ ∧ CFSG.QuasithinUnique.IsSylowTwoOf D.U ⊤ ∧ (∃ c : K, σ c ≠ c) ∧
        CFSG.LieType.BorelTits.Holds X 2 ∧ Nat.card K = 2 ^ (3 * n) ∧
        ∃ φ : ↥L ≃* X, ((T ⊓ L).subgroupOf L).map φ.toMonoidHom = D.U := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hn, K, hF, hFin, σ, hK, hσ, ⟨e₀⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model hL
  have hq : 2 ≤ 2 ^ n :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ n) := hσ
  obtain ⟨e₁⟩ := CFSG.Quasithin.H13.F431.D4q.Hex.exists_d4Model_equiv σ hn hK hσq
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  let φ₀ : ↥L ≃* (twistedGroup σ.toRingHom ⧸ Subgroup.center (twistedGroup σ.toRingHom)) :=
    e₀.trans e₁.symm
  haveI : Finite (twistedGroup σ.toRingHom ⧸ Subgroup.center (twistedGroup σ.toRingHom)) :=
    Finite.of_equiv _ φ₀.toEquiv
  have hU := CFSG.Quasithin.H13.F431.D4q.Hex.d4ModelSystem_isSylow σ hn hK hσq hq
  have hψ := d4Coords_model (σ := σ.toRingHom) hq hK hσq
  have hσ1 : ∃ c : K, σ.toRingHom c ≠ c := by
    by_contra hcon
    push Not at hcon
    have hfix := card_fixedField_of_cube σ.toRingHom hq hK hσq
    have hall : Nat.card (fixedField σ.toRingHom) = Nat.card K := by
      have : ∀ c : K, c ∈ fixedField σ.toRingHom := fun c => hcon c
      exact Nat.card_congr ((Equiv.subtypeUnivEquiv this))
    rw [hfix, hK] at hall
    have h1 : 2 ^ n < (2 ^ n) ^ 3 := by
      calc 2 ^ n = (2 ^ n) ^ 1 := (pow_one _).symm
        _ < (2 ^ n) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  have hBT : CFSG.LieType.BorelTits.Holds
      (twistedGroup σ.toRingHom ⧸ Subgroup.center (twistedGroup σ.toRingHom)) 2 :=
    (CFSG.LieType.BorelTits.holds_of_chevalleyExceptionalModel hL).of_mulEquiv φ₀
  have hTsyl : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ := ⟨le_top, hT.2.1, hT.2.2⟩
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hTsyl le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have hSL : CFSG.QuasithinUnique.IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_subgroupOf_top hS
  set S₀ := ((T ⊓ L).subgroupOf L).map φ₀.toMonoidHom with hS₀
  have hS₀2 : IsPGroup 2 S₀ := hSL.2.1.map _
  have hidx₀ : ¬ 2 ∣ S₀.index := by
    have e := Subgroup.index_map_equiv ((T ⊓ L).subgroupOf L) φ₀
    rw [hS₀, show ((T ⊓ L).subgroupOf L).map φ₀.toMonoidHom =
      ((T ⊓ L).subgroupOf L).map (φ₀ : ↥L →* _) from rfl, e, ← Subgroup.relIndex_top_right]
    exact hSL.2.2
  have hidxU : ¬ 2 ∣ (d4ModelSystem σ.toRingHom hq hK hσq).U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hU.2.2
  let SS : Sylow 2 _ := hS₀2.toSylow hidx₀
  let SU : Sylow 2 _ := hU.2.1.toSylow hidxU
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq
    (twistedGroup σ.toRingHom ⧸ Subgroup.center (twistedGroup σ.toRingHom)) SS SU
  have hcU : S₀.map (MulAut.conj c).toMonoidHom = (d4ModelSystem σ.toRingHom hq hK hσq).U := by
    have := congrArg Sylow.toSubgroup hc
    exact this
  refine ⟨_, inferInstance, inferInstance, K, hF, inferInstance, σ.toRingHom,
    sigma_three_of_card hK hσq, d4ModelSystem σ.toRingHom hq hK hσq, _, hψ, hU, hσ1, hBT, hK3,
    φ₀.trans (MulAut.conj c), ?_⟩
  rw [← hcU, hS₀, Subgroup.map_map]
  rfl

end CFSG.Quasithin.RonanE114Low
