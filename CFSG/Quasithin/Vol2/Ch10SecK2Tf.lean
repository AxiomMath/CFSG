module

public import CFSG.Quasithin.Vol2.Ch10SecK2Te
public import CFSG.Quasithin.Vol2.Ch11SecAKA1
public import CFSG.Quasithin.Vol2.Ch11SecAKA20
public import CFSG.Quasithin.Vol2.Ch11SecAKC8
public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch11.SecA

theorem isPSp4_of_equiv_statedSp {X : Type} [Group X] {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m) (e : X ≃* ↥(Assembly.LowTwoRank.StatedSp 2 K)) :
    IsPSp4 2 m X := by
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, fun h => ?_⟩, K, inferInstance, inferInstance, hK,
    ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq
      (SectionRank.EvenCover.statedScalars_subgroupOf_statedSp_eq_bot 2)).trans
      QuotientGroup.quotientBot).symm⟩⟩
  have h2 : 2 ^ m = 2 := (Prod.mk.inj h).2
  have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

theorem four_le_card {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 2 ≤ m)
    (hK : Nat.card K = 2 ^ m) : 4 ≤ Nat.card K := by
  rw [hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm


variable {K : Type} [Field K] [Finite K] {m : ℕ} {W : Type} [CommGroup W] [Finite W]
  {H : Subgroup (MulAut W)} {Z : Subgroup W}

theorem perfectCore_eq_flag_Sp4 (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    (hW2 : ∀ w : W, w ^ 2 = 1) {π : ↥(Assembly.LowTwoRank.StatedSp 2 K) →* ↥H}
    (hR : (FFModel.nat (Assembly.LowTwoRank.StatedSp 2 K)).RealizesVia H ⊤ Z π)
    (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) {Pst : Subgroup ↥H} (hPst : IsMaxParabolic2 ⊤ Pst)
    {S₀ : Subgroup ↥H} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hPS : Subgroup.normalizer (S₀ : Set ↥H) ≤ Pst) :
    ∃ (U : Subgroup W) (i : ℕ), (i = 1 ∨ i = 2) ∧ IsFlagW H (S₀.map H.subtype) Z (2 ^ m) i U ∧
      (perfectCore Pst).map H.subtype = perfectCore (H ⊓ stabW U) := by
  have hπb : Function.Bijective π := ⟨injective_of_realizesVia_nat hR, hR.1⟩
  let e : ↥H ≃* ↥(Assembly.LowTwoRank.StatedSp 2 K) := (MulEquiv.ofBijective π hπb).symm
  have : Group.IsPerfect ↥(Assembly.LowTwoRank.StatedSp 2 K) :=
    LieType.Steinberg.CentralExt.SpClosed.isPerfect_statedSp 2 K (four_le_card hm hK)
  have hHp : Group.IsPerfect ↥H := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  have hcard : ∀ k : ℕ, Nat.card ↥H ≠ 2 ^ m * ((2 ^ m) ^ 2 - 1) * 2 ^ k := fun k => by
    rw [Nat.card_congr e.toEquiv, Ch11.SecC.B51.card_Sp4_eq_pow hK, mul_comm (2 ^ (2 * m) - 1)]
    exact card_ne_levi (by omega) (by omega)
  have htype : IsPSp4 2 m ↥H := isPSp4_of_equiv_statedSp hm hK e
  exact perfectCore_eq_flag_of hm hK hHZ (Subgroup.isPerfect_iff.mp hHp) hcard
    (fun S₀ hS₀ => SecB.Rank2.exists_residualOvergroupsAt (by omega : 1 ≤ m)
      (Or.inr (Or.inr (Or.inl htype))) hS₀)
    (fun S hS => KGNat.factFlagSp4_holds K m hm hK W hW2 H Z π hR S hS)
    (fun S hS => KGNat.factLeviSp4_holds K m hm hK W hW2 H Z π hR S hS)
    (fun S hS => KGNat.factPointSp4_holds K m hm hK W hW2 H Z π hR S hS)
    (fun S hS U hU => (KGNat.factLineSp4_holds K m hm hK W hW2 H Z π hR hHZ S hS U hU).1) hPst
    hS₀ hPS


theorem perfectCore_eq_flag_G2 (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    (hW2 : ∀ w : W, w ^ 2 = 1) {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H}
    (hR : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π)
    (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) {Pst : Subgroup ↥H} (hPst : IsMaxParabolic2 ⊤ Pst)
    {S₀ : Subgroup ↥H} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hPS : Subgroup.normalizer (S₀ : Set ↥H) ≤ Pst) :
    ∃ (U : Subgroup W) (i : ℕ), (i = 1 ∨ i = 2) ∧ IsFlagW H (S₀.map H.subtype) Z (2 ^ m) i U ∧
      (perfectCore Pst).map H.subtype = perfectCore (H ⊓ stabW U) := by
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have hπb : Function.Bijective π :=
    ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ (A3.commutator_self_le _)) hR, hR.1⟩
  obtain ⟨c, hc0, hc1⟩ :=
    B42G2Id.exists_ne_zero_ne_one_of_three_le (K := K) (hK ▸ B42G2Id.three_le_two_pow hm)
  have hc : ⁅quasithinG2 K, quasithinG2 K⁆ = Explicit.cayleyGroup K := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
      JonesParshall.cayley_commutator_eq hc0 hc1]
  let e : ↥H ≃* ↥(Explicit.cayleyGroup K) :=
    (MulEquiv.ofBijective π hπb).symm.trans (MulEquiv.subgroupCongr hc)
  have : Group.IsPerfect ↥(Explicit.cayleyGroup K) :=
    Subgroup.isPerfect_iff.mpr (JonesParshall.cayley_commutator_eq hc0 hc1)
  have hHp : Group.IsPerfect ↥H := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  have hcard : ∀ k : ℕ, Nat.card ↥H ≠ 2 ^ m * ((2 ^ m) ^ 2 - 1) * 2 ^ k := fun k => by
    rw [Nat.card_congr (MulEquiv.ofBijective π hπb).symm.toEquiv,
      Ch11.SecC.B51.card_G2_eq_pow KGNat.factG2DerivedOrder_holds hm hK]
    exact card_ne_levi (by omega) (by omega)
  have htype : IsG2 2 m ↥H :=
    IsG2.of_mulEquiv e.symm (B42G2Id.chevalleyExceptionalModel_cayleyGroup hK hm)
  exact perfectCore_eq_flag_of hm hK hHZ (Subgroup.isPerfect_iff.mp hHp) hcard
    (fun S₀ hS₀ => SecB.Rank2.exists_residualOvergroupsAt (by omega : 1 ≤ m)
      (Or.inr (Or.inr (Or.inr htype))) hS₀)
    (fun S hS => Ch11.G2Q8.factFlagG2_holds K m hm hK W hW2 H Z π hR S hS)
    (fun S hS => Ch11.G2Q8.factLeviG2_holds K m hm hK W hW2 H Z π hR S hS)
    (fun S hS => Ch11.G2Q8.factPointG2A_holds K m hm hK W hW2 H Z π hR S hS)
    (fun S hS U hU => (factLineG2_holds K m hm hK W hW2 H Z π hR hHZ S hS U hU).1) hPst
    hS₀ hPS

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
