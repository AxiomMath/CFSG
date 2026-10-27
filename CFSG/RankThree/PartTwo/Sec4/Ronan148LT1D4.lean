module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1Gen
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14.Ronan148K
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)

section PGL

variable {π : Bool} {n : ℕ} {K : Type} [Field K]

theorem pgl_noSz (hK : PiField π 2 n K) (hq : ModThree π (2 ^ n)) {G : Type} [Group G]
    [Finite G] {C Y : Subgroup G} (ε : ↥C ≃* ↥(projImage (glPi π 3 (2 ^ n) K))) (hYC : Y ≤ C)
    (hsub : (Y.subgroupOf C).IsSubnormal) (hp : Group.IsPerfect ↥Y)
    (h3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  have hle : projImage (slPi π 3 (2 ^ n) K) ≤ projImage (glPi π 3 (2 ^ n) K) := by
    refine Subgroup.map_mono ?_
    cases π with
    | true => exact fun A _ => mem_glPi_true _ A
    | false =>
      intro A hA
      exact (mem_glPi_false hK.unitary).mpr ((mem_slPi_false hK.unitary).mp hA).2
  set Q : Subgroup ↥(projImage (glPi π 3 (2 ^ n) K)) :=
    (projImage (slPi π 3 (2 ^ n) K)).subgroupOf (projImage (glPi π 3 (2 ^ n) K)) with hQ
  have hQe : ↥Q ≃* ↥(projImage (slPi π 3 (2 ^ n) K)) := Subgroup.subgroupOfEquivOfLe hle
  have hcomm : ∀ x y : ↥(projImage (glPi π 3 (2 ^ n) K)), x * y * x⁻¹ * y⁻¹ ∈ Q := by
    intro x y
    rw [hQ, Subgroup.mem_subgroupOf]
    have h := commutator_mem_projImage_slPi hK x.2 y.2
    rw [commutatorElement_def] at h
    simpa using h
  by_cases hq2 : π = true ∨ 2 < 2 ^ n
  · haveI := isSimpleGroup_projImage_slPi hK hq2
    have hQs : IsSimpleGroup ↥Q := hQe.isSimpleGroup
    have hiso : IsoLThreePi ↥Q 2 n := isoLThreePi_of_projImage_slPi hK hq hq2 hQe
    have h3Q : 3 ∣ Nat.card ↥Q := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
      · exact KFacts.three_dvd_card_of_mulEquiv_projSL φ
      · exact KFacts.three_dvd_card_of_mulEquiv_projSU (by have := hK.one_le; omega) φ
    exact eq_bot_of_equiv_comm_simple ε hQs h3Q hcomm hYC hsub hp h3
  · push Not at hq2
    obtain ⟨hπ, hq2⟩ := hq2
    have hπ' : π = false := by simpa using hπ
    subst hπ'
    have h2 : 2 ^ n = 2 := by
      have : 2 ≤ 2 ^ n := Nat.le_self_pow (by have := hK.one_le; omega) 2
      omega
    have hsol : Group.IsSolvable ↥(projImage (slPi false 3 (2 ^ n) K)) :=
      Sec13.isSolvable_projImage_slPi_two hK h2
    have hQsol : Group.IsSolvable ↥Q :=
      solvable_of_surjective (f := hQe.symm.toMonoidHom) hQe.symm.surjective
    exact eq_bot_of_equiv_comm_solvable ε hQsol hcomm hYC hp

end PGL

section D4


theorem d4Two_noSz {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (σF : F ≃+* F)
    (hF : Nat.card F = (2 ^ f) ^ 3) (hσF : ∀ c, σF c = c ^ (2 ^ f)) (hσ3 : σF ^ 3 = 1)
    (hf1 : 1 ≤ f) (hsimp : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 F σF.toRingHom))
    (hnc : ∃ a b : graphFixedRootGroup TwistTag.D4 F σF.toRingHom, a * b ≠ b * a)
    (h3S : 3 ∣ Nat.card (graphFixedRootGroup TwistTag.D4 F σF.toRingHom)) :
    ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 F σF.toRingHom), α ^ 3 = 1 →
      ∀ C Y : Subgroup (graphFixedRootGroup TwistTag.D4 F σF.toRingHom),
        (∀ z, z ∈ C ↔ α z = z) → Y ≤ C → (Y.subgroupOf C).IsSubnormal → Group.IsPerfect ↥Y →
        ¬ 3 ∣ Nat.card Y → Y = ⊥ := by
  intro α hα3 C Y hC hYC hsub hp h3
  have hCeq : C = Sec4.autFix α := Subgroup.ext fun z => (hC z).trans Sec4.mem_autFix.symm
  subst hCeq
  have h3q : ¬ 3 ∣ 2 ^ f := by
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  by_cases hα1 : α = 1
  · subst hα1
    have htop : Sec4.autFix (1 : MulAut (graphFixedRootGroup TwistTag.D4 F σF.toRingHom)) = ⊤ :=
      Subgroup.ext fun x => ⟨fun _ => Subgroup.mem_top x, fun _ => Sec4.mem_autFix.2 rfl⟩
    exact eq_bot_of_equiv_simple ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) hsimp h3S
      hYC hsub h3
  by_cases hin : IsInnerAut α
  ·
    obtain ⟨z, rfl⟩ := hin
    have hZ := center_trivial_of_isSimpleGroup hsimp hnc
    have hz1 : z ≠ 1 := by
      rintro rfl
      exact hα1 (map_one _)
    have hz3 : z ^ 3 = 1 := by
      apply hZ
      intro t
      have hc : MulAut.conj (z ^ 3) = 1 := by rw [map_pow, hα3]
      have h1 := congrArg (fun φ : MulAut (graphFixedRootGroup TwistTag.D4 F σF.toRingHom) => φ t)
        hc
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc z ^ 3 * t = z ^ 3 * t * (z ^ 3)⁻¹ * z ^ 3 := by group
        _ = t * z ^ 3 := by rw [h1]
    have hCz : Sec4.autFix (MulAut.conj z) =
        Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 F σF.toRingHom)) := by
      ext x
      rw [Sec4.mem_autFix, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
      constructor
      · intro h
        calc x * z = z * x * z⁻¹ * z := by rw [h]
          _ = z * x := by group
      · intro h
        rw [← h]
        group
    rw [hCz] at hYC hsub
    obtain ⟨g, hg⟩ := Sec11.KS11Lie6Proof.d4ThreeConj_holds F (2 ^ f) σF hF hσF h3q z hz3 hz1
    refine noSz_centralizer_of_conj g z ?_ Y hYC hsub hp h3
    intro Y' hY' hsn' hp' h3'
    have hz'3 : (g * z * g⁻¹) ^ 3 = 1 := by
      rw [show g * z * g⁻¹ = MulAut.conj g z from rfl, ← map_pow, hz3, map_one]
    have hz'1 : g * z * g⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have : MulAut.conj g z = MulAut.conj g 1 := by rw [map_one]; exact h
      exact (MulAut.conj g).injective this
    rcases hg with hS | hM
    ·
      rcases Sec11.KS11Lie6Proof.d4ThreeACent_holds F (2 ^ f) σF hF hσF h3q _ hS hz'3 hz'1 with
        hsol | ⟨N, hNC, hcomm, hNq, x, hxN, hxc, hx1, hx3⟩
      · exact eq_bot_of_le_solvable hY' hsol hp'
      · have hYN := le_of_commutators_mem hY' hp' hcomm
        have h3N : 3 ∣ Nat.card N := by
          have hxo : orderOf (⟨x, hxN⟩ : ↥N) = 3 := by
            have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
            refine orderOf_eq_prime
              (Subtype.ext ((SubgroupClass.coe_pow (⟨x, hxN⟩ : ↥N) 3).trans hx3)) ?_
            intro h
            exact hx1 (congrArg Subtype.val h)
          rw [← hxo]
          exact orderOf_dvd_natCard _
        exact eq_bot_of_le_quasisimple hYN hNC hsn' hNq h3N hp' h3'
    ·
      obtain ⟨hcomm, -⟩ :=
        Sec11.KS11Lie6Proof.d4ThreeBCent_holds F (2 ^ f) σF hF hσF h3q _ hM hz'3 hz'1
      have hYM := le_of_commutators_mem hY' hp' hcomm
      obtain ⟨e⟩ := Sec11.KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2 hσ3
      haveI : Finite ↥(orbitField TwistTag.D4 F σF.toRingHom Sec11.KS11Lie4Proof.d4Outer) :=
        Subtype.finite
      exact eq_bot_of_le_sl2 e hYM hp' h3'
  ·
    by_cases hstd : Sec4.IsStdGraphFieldConj σF α
    ·
      have hchar : ringChar F = 2 := ringChar.eq F 2
      obtain ⟨eG⟩ := nonempty_fixedPoints_fieldActor_mulEquiv_g2 (σ := σF) hchar
      have hγ : Sec4.autFix (fieldActor (t := TwistTag.D4) σF σF) =
          (fieldActor (t := TwistTag.D4) σF σF).toMonoidHom.eqLocus (MonoidHom.id _) := rfl
      have hfixG : Nonempty (Sec4.autFix α ≃* adjointGroup Tag.G2 (fixSubfield σF)) := by
        obtain ⟨β, hβ | hβ⟩ := hstd
        · rw [hβ]
          exact ⟨((autFixConjEquiv β _).trans (MulEquiv.subgroupCongr hγ)).trans eG⟩
        · rw [hβ]
          exact ⟨(((autFixConjEquiv β _).trans
            (MulEquiv.subgroupCongr (autFix_inv _))).trans (MulEquiv.subgroupCongr hγ)).trans eG⟩
      obtain ⟨eα⟩ := hfixG
      exact eq_bot_of_le_g2Two (card_fixSubfield_of_cube hf1 hF hσF) hf1 eα hYC hsub hp h3
    ·
      have hPGL : ∃ (π : Bool) (F' : Type) (_ : Field F') (_ : Finite F'), PiField π 2 f F' ∧
          ModThree π (2 ^ f) ∧ Nonempty (Sec4.autFix α ≃* projImage (glPi π 3 (2 ^ f) F')) := by
        rcases Nat.even_or_odd f with hev | hodd
        · obtain ⟨F', _, _, hF'c, ⟨e⟩⟩ :=
            Sec8.kF89D4SecondCentEven_holds f hev hf1 F σF hF hσF α hα3 hin hstd
          refine ⟨true, F', inferInstance, inferInstance,
            ⟨Nat.prime_two, hf1, by simpa [piCard] using hF'c⟩, ?_, ⟨e⟩⟩
          obtain ⟨j, rfl⟩ := hev
          change (2 ^ (j + j)) % 3 = 1
          rw [← two_mul, pow_mul]
          norm_num [Nat.pow_mod]
        · rcases Sec8.inputs47ClassesD4_of_lang Sec8.kF82D4LangCoset_holds
            Sec8.kF82D4SecondCent_holds f hodd F σF hF hσF α hα3 hin with hstd' |
            ⟨γ, y, -, -, -, -, F', _, _, hF'c, ⟨e⟩⟩
          · exact absurd hstd' hstd
          · refine ⟨false, F', inferInstance, inferInstance,
              ⟨Nat.prime_two, hf1, by simpa [piCard] using hF'c⟩, ?_, ⟨e⟩⟩
            obtain ⟨j, rfl⟩ := hodd
            change (2 ^ (2 * j + 1)) % 3 = 2
            rw [pow_succ, pow_mul]
            norm_num [Nat.mul_mod, Nat.pow_mod]
      obtain ⟨π, F', _, _, hPi, hq, ⟨e⟩⟩ := hPGL
      exact pgl_noSz hPi hq e hYC hsub hp h3

theorem kT1_seven_D4 (q : PrimePower) (hq : (LieTypeIndex.trialityD4 q).Valid) (hq2 : q.p = 2) :
    RowOf143 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group := by
  intro S _ _ hs hna ⟨e⟩ h3
  have hm : Blueprint.ChevalleyExceptionalModel S .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hq hq2 (by decide) e⟩
  rw [hq2] at hm
  have hOut : Group.IsSolvable (Outer S) :=
    (exceptional_Chevalley_model_Schreier S .trialityD4 2 q.exponent (by decide) hm).1
  obtain ⟨F, _, _, _, σF, hF, hσF, hσ3, hf1, hsimp, ⟨φ⟩⟩ :=
    Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hm
  have hnc : ∃ a b : graphFixedRootGroup TwistTag.D4 F σF.toRingHom, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨φ a, φ b, fun h => hab (φ.injective (by rw [map_mul, map_mul, h]))⟩
  have h3S : 3 ∣ Nat.card (graphFixedRootGroup TwistTag.D4 F σF.toRingHom) := by
    rw [← Nat.card_congr φ.toEquiv]
    exact h3
  refine row143_of_inner_kgroup hs hna
    (fun P _ hPp _ => le_inner_of_perfect_outSolvable hOut P hPp)
    fun β hβ Y hY hsn _ hp h3Y => ?_
  exact sp4R148_bot_of_mulEquiv φ (d4Two_noSz σF hF hσF hσ3 hf1 hsimp hnc h3S) β hβ
    (Sec4.autFix β) Y (fun z => Iff.rfl) hY hsn hp h3Y

end D4

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
