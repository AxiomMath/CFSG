module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6FiveAut
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6Tools
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6FiveFix
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6SplitFive
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveConjClass

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Open

namespace ExcFrames

section FiveHolds


theorem twistedE6FiveRefFrame_holds : TwistedE6FiveRefFrame := by
  intro f hf h5
  obtain ⟨ζK, hζ, g₀, T, ι₀, hζKord, hg₀C, hι₀, hbase, hTcomm, hrangeT, htors, hcardT, hcent,
    haut⟩ := exists_fiveLangFrame_aut hf h5
  letI modulePi : Module (ZMod 5) (Fin 6 → ZMod 5) := inferInstance
  have hXel : IsElemAbelian 5 ι₀.range :=
    @NoOffE8Five.isElemAbelian_range_of_module 5 (Fact.mk Nat.prime_five)
      (Fin 6 → ZMod 5) ↥(graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQ 2 f)) inferInstance modulePi inferInstance ι₀
  have hcard : Nat.card ι₀.range = 5 ^ 6 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hι₀).toEquiv,
      Nat.card_congr Multiplicative.toAdd]
    simp [ZMod.card]
  have hSC : ∀ c ∈ Subgroup.centralizer (ι₀.range : Set ↥(graphFixedRootGroup TwistTag.E6
      (GaloisField 2 (2 * f)) (frobQ 2 f))), c ^ 5 = 1 → c ∈ ι₀.range := by
    intro c hc hc5
    exact htors c (hcent c (fun x hx =>
      (Subgroup.mem_centralizer_iff.mp hc x hx).symm)) hc5
  refine ⟨ι₀.range, ι₀, ?_, ?_, ?_, hι₀, rfl, ?_⟩
  · exact hXel
  · rw [hcard]
    norm_num
  · exact hSC
  · intro β hβ hstab
    exact haut β hβ hstab

theorem twistedE6FiveSCUnique_holds : TwistedE6FiveSCUnique := by
  intro f hf h5 A A' hA hA4 hSC hA' hA4' hSC'
  obtain ⟨ζK, hζ, g₀, T, ι₀, hζKord, hg₀C, hι₀, hbase, hTcomm, hrangeT, htors, hcardT, hcent,
    haut⟩ := exists_fiveLangFrame_aut hf h5
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : NeZero (5 : ℕ) := ⟨by norm_num⟩
  letI modulePi : Module (ZMod 5) (Fin 6 → ZMod 5) := inferInstance
  have hXel : IsElemAbelian 5 ι₀.range :=
    @NoOffE8Five.isElemAbelian_range_of_module 5 (Fact.mk Nat.prime_five)
      (Fin 6 → ZMod 5) ↥(graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQ 2 f)) inferInstance modulePi inferInstance ι₀
  have hXp : ∀ x ∈ ι₀.range, x ^ 5 = 1 := fun x hx => hXel.2 x hx
  have hord : (Nat.card ↥(graphFixedRootGroup TwistTag.E6
      (GaloisField 2 (2 * f)) (frobQ 2 f))).factorization 5 =
      (Nat.card ↥T).factorization 5 + 1 := by
    have hcardH : Nat.card ↥(graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQ 2 f)) =
        Nat.card ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)) := rfl
    rw [hcardH,
      CFSG.HardMathSupport.Timmesfeld.CrossChar.factorization_five_card_twistedE6_of_dvd_add_one
        Nat.prime_two hf _ (TwE6Toral.card_galoisField_two_mul f hf) (frobQEquiv hf)
        (fun c => by change frobQ 2 f c = c ^ 2 ^ f; exact frobQ_apply 2 f c) h5,
      hcardT, Nat.factorization_pow, Finsupp.smul_apply]
    norm_num
  have hfix : ∀ a ∈ Subgroup.normalizer (ι₀.range : Set ↥(graphFixedRootGroup TwistTag.E6
      (GaloisField 2 (2 * f)) (frobQ 2 f))),
      a ^ 5 = 1 → (∃ x ∈ ι₀.range, a * x ≠ x * a) →
      Nat.card {x : ι₀.range // a * (x : ↥(graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQ 2 f))) =
          (x : ↥(graphFixedRootGroup TwistTag.E6
            (GaloisField 2 (2 * f)) (frobQ 2 f))) * a} < 5 ^ 3 := by
    intro a ha ha5 hnc
    have hβ5 : (MulAut.conj a : MulAut ↥(graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQ 2 f))) ^ 5 = 1 := by
      rw [← map_pow, ha5, map_one]
    have hstab : ∀ b ∈ ι₀.range, (MulAut.conj a) b ∈ ι₀.range := by
      intro b hb
      simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp ha b).mp hb
    obtain ⟨w, hw⟩ := haut (MulAut.conj a) hβ5 hstab
    have hwT : ∀ s : Fin Tag.E6.rank → ZMod 5,
        (MulAut.conj a) (ι₀ (Multiplicative.ofAdd s)) =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 5 w s)) := fun s => hw s
    have hwne : w ≠ 1 := by
      intro hw1
      obtain ⟨x, hx, hne⟩ := hnc
      obtain ⟨s, rfl⟩ := hx
      let sT : Fin Tag.E6.rank → ZMod 5 := Multiplicative.toAdd s
      have hconj : a * ι₀ (Multiplicative.ofAdd sT) * a⁻¹ =
          ι₀ (Multiplicative.ofAdd sT) := by
        have h := hwT sT
        rw [hw1, TableBExc.torusAct_one (τ := Tag.E6) (p := 5)] at h
        simpa only [MulAut.conj_apply] using h
      apply hne
      have h2 : a * ι₀ (Multiplicative.ofAdd sT) =
          ι₀ (Multiplicative.ofAdd sT) * a := by
        calc a * ι₀ (Multiplicative.ofAdd sT)
            = (a * ι₀ (Multiplicative.ofAdd sT) * a⁻¹) * a := by group
          _ = ι₀ (Multiplicative.ofAdd sT) * a := by rw [hconj]
      exact h2
    have hw5 : w ^ 5 = 1 := by
      apply NoOffExc.eq_one_of_torusAct (p := 5) (by norm_num)
      intro x
      have hiter : ∀ k : ℕ, ∀ s : Fin Tag.E6.rank → ZMod 5,
          ((MulAut.conj a) ^ k) (ι₀ (Multiplicative.ofAdd s)) =
            ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 5 (w ^ k) s)) := by
        intro k
        induction k with
        | zero =>
          intro s
          rw [pow_zero, MulAut.one_apply, pow_zero,
            TableBExc.torusAct_one (τ := Tag.E6) (p := 5)]
        | succ k ih =>
          intro s
          rw [pow_succ, MulAut.mul_apply, hwT s, ih (TableBExc.torusAct .E6 5 w s),
            ← TableBExc.torusAct_mul, ← pow_succ]
      have h1 : ((MulAut.conj a) ^ 5) (ι₀ (Multiplicative.ofAdd x)) =
          ι₀ (Multiplicative.ofAdd x) := by
        rw [hβ5, MulAut.one_apply]
      rw [hiter 5 x] at h1
      exact Multiplicative.ofAdd.injective (hι₀ h1)
    have hworder : orderOf w = 5 := orderOf_eq_prime hw5 hwne
    let e : ι₀.range ≃ (Fin Tag.E6.rank → ZMod 5) :=
      (MonoidHom.ofInjective hι₀).toEquiv.symm.trans Multiplicative.toAdd
    have he : ∀ y : ι₀.range,
        ι₀ (Multiplicative.ofAdd (e y)) =
          (y : ↥(graphFixedRootGroup TwistTag.E6
            (GaloisField 2 (2 * f)) (frobQ 2 f))) := by
      intro y
      change ι₀ (Multiplicative.ofAdd (Multiplicative.toAdd
        ((MonoidHom.ofInjective hι₀).symm y))) = (y : ↥(graphFixedRootGroup TwistTag.E6
          (GaloisField 2 (2 * f)) (frobQ 2 f)))
      rw [ofAdd_toAdd]
      exact MonoidHom.apply_ofInjective_symm hι₀ y
    have hcardFix : Nat.card {x : ι₀.range // a * (x : ↥(graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQ 2 f))) =
          (x : ↥(graphFixedRootGroup TwistTag.E6
            (GaloisField 2 (2 * f)) (frobQ 2 f))) * a} ≤
        Nat.card {s : Fin Tag.E6.rank → ZMod 5 // TableBExc.torusAct .E6 5 w s = s} := by
      refine Nat.card_le_card_of_injective (fun y => ⟨e y.1, ?_⟩) ?_
      · have hy : (MulAut.conj a) (y.1 : ↥(graphFixedRootGroup TwistTag.E6
            (GaloisField 2 (2 * f)) (frobQ 2 f))) =
            (y.1 : ↥(graphFixedRootGroup TwistTag.E6
              (GaloisField 2 (2 * f)) (frobQ 2 f))) := by
          rw [MulAut.conj_apply]
          calc a * (y.1 : ↥(graphFixedRootGroup TwistTag.E6
                (GaloisField 2 (2 * f)) (frobQ 2 f))) * a⁻¹ =
              ((y.1 : ↥(graphFixedRootGroup TwistTag.E6
                (GaloisField 2 (2 * f)) (frobQ 2 f))) * a) * a⁻¹ := by rw [← y.2]
            _ = (y.1 : ↥(graphFixedRootGroup TwistTag.E6
                (GaloisField 2 (2 * f)) (frobQ 2 f))) := by group
        have h2 : ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 5 w (e y.1))) =
            ι₀ (Multiplicative.ofAdd (e y.1)) := by
          rw [← hwT (e y.1), he y.1, hy]
        exact Multiplicative.ofAdd.injective (hι₀ h2)
      · intro y1 y2 h
        apply Subtype.ext
        exact e.injective (congrArg Subtype.val h)
    calc Nat.card {x : ι₀.range // a * (x : ↥(graphFixedRootGroup TwistTag.E6
            (GaloisField 2 (2 * f)) (frobQ 2 f))) =
              (x : ↥(graphFixedRootGroup TwistTag.E6
                (GaloisField 2 (2 * f)) (frobQ 2 f))) * a}
        ≤ Nat.card {s : Fin Tag.E6.rank → ZMod 5 // TableBExc.torusAct .E6 5 w s = s} := hcardFix
      _ ≤ 5 ^ 2 := card_fix_torusAct_E6_five hworder
      _ < 5 ^ 3 := by norm_num
  obtain ⟨c₁, hc₁⟩ := exists_conj_map_eq_of_SC (p := 5) (T := T) (X := ι₀.range)
    hTcomm hrangeT hXp htors hord hcent hfix hA hA4 hSC
  obtain ⟨c₂, hc₂⟩ := exists_conj_map_eq_of_SC (p := 5) (T := T) (X := ι₀.range)
    hTcomm hrangeT hXp htors hord hcent hfix hA' hA4' hSC'
  refine ⟨c₂ * c₁⁻¹, ?_⟩
  calc A' = ι₀.range.map (MulAut.conj c₂).toMonoidHom := hc₂.symm
    _ = (ι₀.range.map (MulAut.conj c₁).toMonoidHom).map
        (MulAut.conj (c₂ * c₁⁻¹)).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        refine MonoidHom.ext fun z => ?_
        simp [MulAut.conj_apply]
        group
    _ = A.map (MulAut.conj (c₂ * c₁⁻¹)).toMonoidHom := by rw [hc₁]

end FiveHolds

end ExcFrames

end CFSG.StandardType
