module

public import CFSG.RankThree.PartTwo.Sec8.Item89Res2ProofJType
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag

namespace Item89Res2

theorem three_dvd_ordTwistedF4 (f : ℕ) : 3 ∣ CFSG.Open.ordTwistedF4 (2 ^ f) := by
  unfold CFSG.Open.ordTwistedF4
  have h4 : (2 ^ f) ^ 4 = 4 ^ (2 * f) := by
    rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring_nf
  have h3 : 3 ∣ (2 ^ f) ^ 4 - 1 := by
    rw [h4]
    exact Item87Proof.three_dvd_four_pow_sub_one (2 * f)
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h3 _) _) _


theorem reeTitsModel_reeGamma {b : ℕ} (hb : 1 ≤ b) {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    ReeTitsModel (ReeTag.F4.reeGamma k b) .twistedF4 2 (2 * b + 1) := by
  obtain ⟨iso⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma (K := k) (a := b) hb hk
  have hfx : reeFixedGroup .F4 k reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ b else 2 ^ (b + 1)) = ReeTag.F4.reeGamma k b :=
    (ReeTag.reeGamma_eq_reeFixedGroup (t := ReeTag.F4) (K := k) (a := b)).symm
  refine ⟨⟨Nat.prime_two, by omega, rfl, rfl, odd_two_mul_add_one b, by omega⟩, b, rfl, k,
    inferInstance, inferInstance, hk, ?_⟩
  let iso' : DerivedCentralQuotient (reeFixedGroup .F4 k reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ b else 2 ^ (b + 1))) ≃*
      DerivedCentralQuotient (ReeTag.F4.reeGamma k b) :=
    CFSG.RankThree.PartOne.Sec66T.centerQuotientCongr
      (MulEquiv.subgroupCongr (by rw [hfx]; rfl))
  exact ⟨iso.symm.trans iso'.symm⟩

theorem reeTitsModel_perfectResidual_two {C : Type} [Group C] {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk2 : Nat.card k = 2) (φ : C ≃* ReeTag.F4.reeGamma k 0) :
    ReeTitsModel (perfectResidual C) .Tits 2 1 := by
  let W₂ := reeFixed ReeTag.F4 k 0
  let ψ : C ≃* W₂ := φ.trans (ReeTag.reeFixedEquivReeGamma k 0).symm
  have hT := CFSG.LieType.Simplicity.titsData k hk2
  have hperf : Group.IsPerfect (commutator W₂) := hT.isPerfect hk2
  have hres : perfectResidual W₂ = commutator W₂ := perfectResidual_eq_commutator hperf
  let eR1 : perfectResidual C ≃* commutator W₂ :=
    (perfectResidualEquiv ψ).trans (MulEquiv.subgroupCongr hres)
  let H := reeFixedGroup .F4 k reeF4Perm (fun i => if i ∈ reeF4Long then 2 ^ 0 else 2 ^ (0 + 1))
  let eH : H ≃* W₂ :=
    (MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.F4 k 0)).trans
      ((reeFixed ReeTag.F4 k 0).equivMapOfInjective _ Subtype.val_injective).symm
  let e' : DerivedCentralQuotient H ≃* commutator W₂ ⧸ Subgroup.center (commutator W₂) :=
    CFSG.LieType.BorelTits.derivedCentralQuotientEquiv H eH
  have hTits : ReeTitsModel (DerivedCentralQuotient H) .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_refl 1, rfl, rfl, rfl⟩, 0, rfl, k, inferInstance, inferInstance, hk2,
      ⟨MulEquiv.refl _⟩⟩
  have hL : CFSG.Blueprint.LieModel (DerivedCentralQuotient H) .Tits 0 2 1 :=
    Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hTits⟩))
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.Tits.multiplier_Tits _ hL
  have : Finite (ModGL ReeTag.F4.tag k) := finite_modGL
  let q : commutator W₂ →* DerivedCentralQuotient H :=
    e'.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (commutator W₂)))
  have hqs : Function.Surjective q := e'.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = Subgroup.center (commutator W₂) := by
    ext x
    change e'.symm (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [map_eq_one_iff e'.symm e'.symm.injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hperf q hqs hqker.le
  have hU1 : Nat.card Unit = 1 := Nat.card_unique
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
    Nat.card_congr eM.toEquiv, hU1, Nat.dvd_one, hqker] at hd
  have hZ : Subgroup.center (commutator W₂) = ⊥ := Subgroup.card_eq_one.mp hd
  let eZ : commutator W₂ ⧸ Subgroup.center (commutator W₂) ≃* commutator W₂ :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨⟨Nat.prime_two, le_refl 1, rfl, rfl, rfl⟩, 0, rfl, k, inferInstance, inferInstance, hk2,
    ⟨(eR1.trans eZ.symm).trans e'.symm⟩⟩

theorem type_of_reeGamma {C : Type} [Group C] {b : ℕ} {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1))
    (φ : C ≃* ReeTag.F4.reeGamma k b) :
    Sec4.IsType419Theta (perfectResidual C) ∧ 3 ∣ Nat.card (perfectResidual C) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  ·
    have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
    have hTC := reeTitsModel_perfectResidual_two hk2 φ
    refine ⟨Or.inr (Or.inr (Or.inr (Or.inl hTC))), ?_⟩
    obtain ⟨eD⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hTC
    rw [Nat.card_congr eD.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]
    norm_num
  ·
    have hperf : Group.IsPerfect (ReeTag.F4.reeGamma k b) :=
      ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hk⟩
    have hperfC : Group.IsPerfect C :=
      Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    have hRC : ReeTitsModel (perfectResidual C) .twistedF4 2 (2 * b + 1) :=
      CFSG.SectionRank.reeTitsModel_of_mulEquiv ((perfectResidualEquivSelf hperfC).trans φ)
        (reeTitsModel_reeGamma hb hk)
    refine ⟨Or.inr (Or.inr (Or.inl ⟨2 * b + 1, hRC⟩)), ?_⟩
    rw [CFSG.AGLEmbedding.card_of_reeTitsModel_twistedF4_exact hRC]
    exact three_dvd_ordTwistedF4 _

end Item89Res2


theorem kF89JCentTypeRee_holds : KF89JCentTypeRee := by
  intro G _ _ X a m hm htype ha3 hk
  obtain ⟨k, hk', hkm, ⟨e₀⟩⟩ := htype
  have hout : Sec4.InducesOuterTheta a X := by
    rcases hk with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta X h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X h (by decide)
  have hR := (Sec4.Census.bridgeExceptional46).reeF4 k hk'
  obtain ⟨-, k', hk'1, -, K, _, _, _, hK, ⟨e₁⟩⟩ := Sec4.exists_mulEquiv_reeGamma hR
  obtain ⟨b, k₀, _, _, _, hk₀, ⟨φ⟩⟩ :=
    Item812Res2.exists_barCentralizer_mulEquiv_reeGamma hk'1 hK (e₀.trans e₁) ha3 hout
  exact Item89Res2.type_of_reeGamma hk₀ φ

end CFSG.RankThree.PartTwo.Sec8
