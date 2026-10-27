module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowG2
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowAut
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projImage)

theorem false_of_perfect_le_solvable {G : Type*} [Group G] {H K : Subgroup G}
    [Group.IsSolvable H] [Group.IsPerfect K] [Nontrivial K] (hKH : K ≤ H) : False := by
  haveI : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKH)
      (Subgroup.inclusion_injective hKH)
  exact (Group.IsPerfect.not_isSolvable K) inferInstance

theorem pCore_eq_bot_of_isSubnormal_bot {Y : Type} [Group Y] [Finite Y] {W : Subgroup Y}
    (hW : W.IsSubnormal) (h : CFSG.pCore 2 Y = ⊥) : CFSG.pCore 2 W = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Late.pCoreOf_le_pCore_of_isSubnormal 2 hW
  rw [h] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective).mp (le_bot_iff.mp h1)


section Main


theorem false_of_cfgSEps_conj_d4 {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hf1 : 1 ≤ f) (hF : Nat.card F = (2 ^ f) ^ 3) {σ : F ≃+* F} (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hσ3 : σ ^ 3 = 1) [Finite (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)]
    {A : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 F σ.toRingHom))}
    {z : graphFixedRootGroup TwistTag.D4 F σ.toRingHom}
    {K : Subgroup (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)}
    (hc : CfgSEps (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) A (MulAut.conj z) K)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : False := by
  have h3f : ¬ 3 ∣ 2 ^ f := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at this
  have h2f : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  have hK4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left h2f 3
  obtain ⟨g, hg⟩ := Sec11.KS11Lie6Proof.d4ThreeConj_holds F (2 ^ f) σ hF hσ h3f z hz3 hz1
  have hc2 := hc.map (MulAut.conj g)
  rw [congr_conj_conj] at hc2
  generalize hz' : g * z * g⁻¹ = z' at hg hc2
  have hz'3 : z' ^ 3 = 1 := by rw [← hz', conj_pow, hz3, mul_one, mul_inv_cancel]
  have hz'1 : z' ≠ 1 := fun h => hc2.ne_one (by rw [h, map_one])
  have hfix : Sec4.autFix (MulAut.conj z') =
      Subgroup.centralizer ({z'} : Set (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)) :=
    RowV.autFix_conj_eq_centralizer z'
  have hKC := hc2.le_autFix
  rw [hfix] at hKC
  haveI := hc2.isPerfect
  haveI := hc2.nontrivial
  rcases hg with hS | hM
  ·
    rcases Sec11.KS11Lie6Proof.d4ThreeACent_holds F (2 ^ f) σ hF hσ h3f z' hS hz'3 hz'1 with
      hsolv | ⟨N, hNC, hcomm, hNq, x, hxN, hxc, hx1, hx3⟩
    · haveI : Group.IsSolvable (Subgroup.centralizer
          ({z'} : Set (graphFixedRootGroup TwistTag.D4 F σ.toRingHom))) := hsolv
      exact false_of_perfect_le_solvable hKC
    · have hKN := le_of_isPerfect_of_commutators hKC hcomm
      have hNC' : N ≤ Sec4.autFix (MulAut.conj z') := by rw [hfix]; exact hNC
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact hc2.false_of_le_quasisimple_central hKN hNC' hNq hxN
        (fun n hn => (hxc n hn).symm) (orderOf_eq_prime hx3 hx1)
  ·
    obtain ⟨hcomm, -⟩ :=
      Sec11.KS11Lie6Proof.d4ThreeBCent_holds F (2 ^ f) σ hF hσ h3f z' hM hz'3 hz'1
    have hKS := le_of_isPerfect_of_commutators hKC hcomm
    have hSC : Sec11.KS11Lie4Proof.d4ShortSL2 F σ.toRingHom ≤ Sec4.autFix (MulAut.conj z') := by
      rw [hfix]
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hM) s hs
    have hSq := Sec11.KS11Lie4Proof.isQuasisimple_d4ShortSL2 hσ3 hK4
    have hSZ : Subgroup.center (Sec11.KS11Lie4Proof.d4ShortSL2 F σ.toRingHom) = ⊥ := by
      obtain ⟨ι⟩ := Sec11.KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2 hσ3
      exact center_eq_bot_of_mulEquiv ι.symm Sec19.Item19Res2Proof.center_sl2_eq_bot
    have hcube := hc2.isTypeEpsCube_of_le hKS hSC hSq hSZ
    refine (not_isTypeEpsCube_of_card_sl2_even (n := 3 * f) (by omega) ?_) hcube
    rw [Sec11.KS11Lie4Proof.card_d4ShortSL2 hσ3, hF,
      show (2 : ℕ) ^ (3 * f) = (2 ^ f) ^ 3 by rw [← pow_mul, mul_comm]]



theorem noCfgSEps_trialityD4 {S : Type} [Group S] [Finite S]
    (hna : ∃ a b : S, a * b ≠ b * a) {f : ℕ}
    (hm : Blueprint.ChevalleyExceptionalModel S .trialityD4 2 f) : NoCfgSEps S := by
  intro A σ K hc
  obtain ⟨F, _, _, hcharF, σF, hF, hσF, hσ3F, hf1, hsimp, ⟨φ⟩⟩ :=
    Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hm
  haveI : Finite (graphFixedRootGroup TwistTag.D4 F σF.toRingHom) :=
    Finite.of_equiv _ φ.toEquiv
  haveI := hc.isPerfect
  have hnaC : ∃ a b : graphFixedRootGroup TwistTag.D4 F σF.toRingHom, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨φ a, φ b, fun h => hab (φ.injective (by rw [map_mul, map_mul, h]))⟩
  have hZ := center_trivial_of_isSimpleGroup hsimp hnaC
  have hα3 : (MulAut.congr φ σ) ^ 3 = 1 := by rw [← map_pow, hc.pow_three, map_one]
  have hc1 := hc.map φ
  by_cases hin : IsInnerAut (MulAut.congr φ σ)
  ·
    obtain ⟨z, hz⟩ := hin
    rw [← hz] at hc1
    have hz3 : z ^ 3 = 1 :=
      (conj_injective_of_center hZ) (by rw [map_pow, map_one, hz, hα3])
    have hz1 : z ≠ 1 := fun h => hc1.ne_one (by rw [h, map_one])
    exact false_of_cfgSEps_conj_d4 hf1 hF hσF hσ3F hc1 hz3 hz1
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hεσ : Sec4.autFix σ ≃* Sec4.autFix (MulAut.congr φ σ) :=
      (Sec4.autFixCongrEquiv φ σ).symm
    by_cases hstd : Sec4.IsStdGraphFieldConj σF (MulAut.congr φ σ)
    ·
      have hchar : ringChar F = 2 := ringChar.eq F 2
      obtain ⟨eG⟩ := nonempty_fixedPoints_fieldActor_mulEquiv_g2 (σ := σF) hchar
      have hγ : Sec4.autFix (fieldActor (t := TwistTag.D4) σF σF) =
          (fieldActor (t := TwistTag.D4) σF σF).toMonoidHom.eqLocus (MonoidHom.id _) := rfl
      have hfixG : Nonempty (Sec4.autFix (MulAut.congr φ σ) ≃*
          adjointGroup Tag.G2 (fixSubfield σF)) := by
        obtain ⟨β, hβ | hβ⟩ := hstd
        · rw [hβ]
          exact ⟨((autFixConjEquiv β _).trans (MulEquiv.subgroupCongr hγ)).trans eG⟩
        · rw [hβ]
          exact ⟨(((autFixConjEquiv β _).trans
            (MulEquiv.subgroupCongr (autFix_inv _))).trans (MulEquiv.subgroupCongr hγ)).trans eG⟩
      obtain ⟨eα⟩ := hfixG
      exact hc.false_of_autFix_g2 (card_fixSubfield_of_cube hf1 hF hσF) hf1 (hεσ.trans eα)
    ·
      have hPGL : ∃ (π : Bool) (F' : Type) (_ : Field F') (_ : Finite F'), PiField π 2 f F' ∧
          ModThree π (2 ^ f) ∧
            Nonempty (Sec4.autFix (MulAut.congr φ σ) ≃* projImage (glPi π 3 (2 ^ f) F')) := by
        rcases Nat.even_or_odd f with hev | hodd
        · obtain ⟨F', _, _, hF'c, ⟨e⟩⟩ :=
            Sec8.kF89D4SecondCentEven_holds f hev hf1 F σF hF hσF (MulAut.congr φ σ) hα3 hin hstd
          refine ⟨true, F', inferInstance, inferInstance,
            ⟨Nat.prime_two, hf1, by simpa [piCard] using hF'c⟩, ?_, ⟨e⟩⟩
          obtain ⟨j, rfl⟩ := hev
          change (2 ^ (j + j)) % 3 = 1
          rw [← two_mul, pow_mul]
          norm_num [Nat.pow_mod]
        · rcases Sec8.inputs47ClassesD4_of_lang Sec8.kF82D4LangCoset_holds
            Sec8.kF82D4SecondCent_holds f hodd F σF hF hσF (MulAut.congr φ σ) hα3 hin with hstd' |
            ⟨γ, y, -, -, -, -, F', _, _, hF'c, ⟨e⟩⟩
          · exact absurd hstd' hstd
          · refine ⟨false, F', inferInstance, inferInstance,
              ⟨Nat.prime_two, hf1, by simpa [piCard] using hF'c⟩, ?_, ⟨e⟩⟩
            obtain ⟨j, rfl⟩ := hodd
            change (2 ^ (2 * j + 1)) % 3 = 2
            rw [pow_succ, pow_mul]
            norm_num [Nat.mul_mod, Nat.pow_mod]
      obtain ⟨π, F', _, _, hPi, hq, ⟨e⟩⟩ := hPGL
      have h3 : ∃ k ∈ K, k ≠ 1 ∧ k ^ 3 = 1 := by
        haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have hd : 3 ∣ Nat.card K :=
          (three_dvd_card_of_isTypeEpsCube (isTypeEpsCube_of_cfgSEps hc)).trans
            (Subgroup.card_quotient_dvd_card _)
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 hd
        have hx1 : x ≠ 1 := fun h => by
          rw [h, orderOf_one] at hx
          norm_num at hx
        have hx3 : x ^ 3 = 1 := by
          rw [← hx]
          exact pow_orderOf_eq_one x
        exact ⟨x, x.2, fun h => hx1 (Subtype.ext h), by simpa using congrArg Subtype.val hx3⟩
      obtain ⟨hIso, hO2⟩ := pglCase hPi hq (hεσ.trans e) hc.le_autFix hc.isSubnormal h3
      have hO2K : CFSG.pCore 2 K = ⊥ := by
        have hW := pCore_eq_bot_of_isSubnormal_bot hc.isSubnormal hO2
        have h := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2
          (Subgroup.subgroupOfEquivOfLe hc.le_autFix)
        rw [hW, Subgroup.map_bot] at h
        exact h.symm
      exact false_of_isTypeEps_of_isoLThreePi hc.isType hf1
        (RonanK429.isoLThreePi_of_mulEquiv
          ((QuotientGroup.quotientMulEquivOfEq hO2K).trans QuotientGroup.quotientBot) hIso)

theorem rowSEpsOf_seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    q.p = 2 → RowSEpsOf (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group := by
  intro q hq hq2 S _ _ _ hna ⟨e⟩
  have hm : Blueprint.ChevalleyExceptionalModel S .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hq hq2 (by decide) e⟩
  rw [hq2] at hm
  exact noCfgSEps_trialityD4 hna hm

end Main

end CFSG.RankThree.PartTwo.Sec4.RonanEps
