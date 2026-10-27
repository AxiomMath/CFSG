module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LRowCover
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieD4
public import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofOdd

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projImage projSU)

section D4


theorem rowU3_D4 {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {f : ℕ} (hm : ChevalleyExceptionalModel S .trialityD4 2 f)
    {σ : MulAut S} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) {Y : Subgroup S} (hYC : Y ≤ Sec4.autFix σ)
    [Group.IsPerfect Y] (hsub : (Y.subgroupOf (Sec4.autFix σ)).IsSubnormal) {m : ℕ}
    (hmo : Odd m) (hm1 : 1 < m) (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (hker : Nat.Coprime (Nat.card π.ker) 3) : f = m ∧ ¬ IsInnerAut σ := by
  obtain ⟨F, _, _, _, σF, hF, hσF, -, hf1, hsimp, ⟨φ⟩⟩ :=
    Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hm
  obtain ⟨E, hEY, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_cover hmo hm1 π hπ hker
  have hfix : ∀ k ∈ Y, σ k = k := fun k hk => Sec4.mem_autFix.mp (hYC hk)
  obtain ⟨k₀, hk₀E, hk₀1, hk₀3⟩ := exists_ne_one_pow_three_of_card hE3 hE9
  have h3 : ∃ k ∈ Y, k ≠ 1 ∧ k ^ 3 = 1 := ⟨k₀, hEY hk₀E, hk₀1, hk₀3⟩
  have hnaC : ∃ a b : graphFixedRootGroup TwistTag.D4 F σF.toRingHom, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨φ a, φ b, fun h => hab (φ.injective (by rw [map_mul, map_mul, h]))⟩
  have hZ := RonanK429Lie.center_trivial_of_isSimpleGroup hsimp hnaC
  have hF' : Nat.card F = (2 ^ f) ^ TwistTag.D4.order := hF
  set α := MulAut.congr φ σ with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hσ3, map_one]
  by_cases hin : IsInnerAut α
  ·
    exfalso
    refine RonanK429Lie.false_of_fix_e9_of_mulEquiv φ
      (MulAut.conj : graphFixedRootGroup TwistTag.D4 F σF.toRingHom →* MulAut _).range ?_
      (fun s => ⟨s, rfl⟩) hZ hin hσ3 hσ1 hEY hEc hE3 hE9 hfix hEZ
    intro B hB h3B hcB
    have hinj := RonanK429Lie.conj_injective_of_center hZ
    set B' := B.comap
      (MulAut.conj : graphFixedRootGroup TwistTag.D4 F σF.toRingHom →* MulAut _) with hB'
    have hmap : B'.map
        (MulAut.conj : graphFixedRootGroup TwistTag.D4 F σF.toRingHom →* MulAut _) = B := by
      rw [hB', Subgroup.map_comap_eq, inf_eq_right.mpr hB]
    have hcard : Nat.card B' = Nat.card B := by
      rw [← hmap, Subgroup.card_map_of_injective hinj]
    have hB'e : CFSG.Assembly.IsElemAbelian 3 B' := by
      refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun a ha => hinj ?_⟩
      · simp only [Subgroup.coe_mul, map_mul]
        exact hcB _ a.2 _ b.2
      · rw [map_pow, map_one]
        exact h3B _ ha
    rw [← hcard]
    exact Sec21.Item223Rank2Proof.card_le_nine_of_graphFixedRootGroup hf1 hF' hσF B' hB'e
  · have hout : ¬ IsInnerAut σ := fun h => hin ((isInnerAut_congr φ σ).mpr h)
    refine ⟨?_, hout⟩
    have hεσ : Sec4.autFix σ ≃* Sec4.autFix α := (Sec4.autFixCongrEquiv φ σ).symm
    by_cases hstd : Sec4.IsStdGraphFieldConj σF α
    ·
      exfalso
      have hchar : ringChar F = 2 := ringChar.eq F 2
      obtain ⟨eG⟩ := nonempty_fixedPoints_fieldActor_mulEquiv_g2 (σ := σF) hchar
      have hγ : Sec4.autFix (fieldActor (t := TwistTag.D4) σF σF) =
          (fieldActor (t := TwistTag.D4) σF σF).toMonoidHom.eqLocus (MonoidHom.id _) := rfl
      have hfixG : Nonempty (Sec4.autFix α ≃* adjointGroup Tag.G2 (fixSubfield σF)) := by
        obtain ⟨β, hβ | hβ⟩ := hstd
        · rw [hβ]
          exact ⟨((RonanK429Lie.autFixConjEquiv β _).trans (MulEquiv.subgroupCongr hγ)).trans eG⟩
        · rw [hβ]
          exact ⟨(((RonanK429Lie.autFixConjEquiv β _).trans
            (MulEquiv.subgroupCongr (RonanK429Lie.autFix_inv _))).trans
              (MulEquiv.subgroupCongr hγ)).trans eG⟩
      obtain ⟨eα⟩ := hfixG
      exact false_of_g2_cover (card_fixSubfield_of_cube hf1 hF hσF) hf1 (hεσ.trans eα) hYC hsub
        hmo hm1 π hπ
    ·
      have hPGL : ∃ (ε : Bool) (F' : Type) (_ : Field F') (_ : Finite F'), PiField ε 2 f F' ∧
          ModThree ε (2 ^ f) ∧ Nonempty (Sec4.autFix α ≃* projImage (glPi ε 3 (2 ^ f) F')) := by
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
      obtain ⟨ε, F', _, _, hPi, hq, ⟨e⟩⟩ := hPGL
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨hiso, -⟩ := RonanK429Lie.pglCase hPi hq (hεσ.trans e) hYC hsub h3
      haveI : IsSimpleGroup Y := (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi hf1 hiso).1
      have hcY := card_eq_of_isSimpleGroup_surj π hπ (one_lt_card_projSU (by omega : 1 ≤ m))
      have hU := padicValNat_card_projSU (by omega : 1 ≤ m)
      rcases hiso with ⟨hq1, ⟨φY⟩⟩ | ⟨-, ⟨φY⟩⟩
      ·
        exfalso
        have hL := Sec8.Item812Res5.padicValNat_card_projSL_three hf1
        rw [← Nat.card_congr φY.toEquiv, hcY, hU] at hL
        have hmf : f = m := by omega
        subst hmf
        obtain ⟨j, rfl⟩ := hmo
        rw [pow_succ, pow_mul] at hq1
        norm_num [Nat.mul_mod, Nat.pow_mod] at hq1
      ·
        have hV := padicValNat_card_projSU hf1
        rw [← Nat.card_congr φY.toEquiv, hcY, hU] at hV
        omega

end D4

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
