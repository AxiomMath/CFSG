module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairRee
import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofPGL3
import CFSG.RankThree.PartTwo.Sec21.LangTwisted3ProofD4Even

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item84KFacts4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups


@[expose] def KF84D4OuterSU3Std : Prop :=
  ∀ (m : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = (2 ^ m) ^ 3 →
    (∀ c, σ c = c ^ 2 ^ m) →
    ∀ τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), τ ^ 3 = 1 → ¬ IsInnerAut τ →
    Sec4.IsStdGraphFieldConj σ τ →
    ∀ w ∈ Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom, w ^ 3 = 1 → w ≠ 1 → τ w = w →
      (∀ x ∈ inSubgroup perfectResidual
          (Subgroup.centralizer ({w} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))),
        τ x = x) ∨
      ∀ x ∈ inSubgroup perfectResidual
          (Subgroup.centralizer ({w} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))),
        τ x = x → (∃ e : ℕ, x ^ 2 ^ e = 1) → x ^ 2 = 1

theorem sq_eq_one_of_mulEquiv_pgl3 {X : Type*} [Group X] {K' : Type} [Field K'] [Finite K']
    [CharP K' 2] {H : Subgroup PGL(3, K')} (e : X ≃* H) {x w : X} (hx : ∃ n : ℕ, x ^ 2 ^ n = 1)
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (hxw : x * w = w * x) : x ^ 2 = 1 := by
  set f : X →* PGL(3, K') := H.subtype.comp e.toMonoidHom with hf
  have hfinj : Function.Injective f := Subtype.val_injective.comp e.injective
  obtain ⟨n, hn⟩ := hx
  apply hfinj
  rw [map_pow, map_one]
  exact sq_eq_one_of_commute_orderThree ⟨n, by rw [← map_pow, hn, map_one]⟩
    (by rw [← map_pow, hw3, map_one]) (fun h => hw1 (hfinj (h.trans (map_one f).symm)))
    (by rw [← map_mul, hxw, map_mul])

theorem sq_eq_one_of_autFix_mulEquiv {Y : Type*} [Group Y] {τ : MulAut Y} {K' : Type} [Field K']
    [Finite K'] [CharP K' 2] {H : Subgroup PGL(3, K')} (e : Sec4.autFix τ ≃* H) {x w : Y}
    (hτx : τ x = x) (hτw : τ w = w) (hx : ∃ n : ℕ, x ^ 2 ^ n = 1) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (hxw : x * w = w * x) : x ^ 2 = 1 := by
  obtain ⟨n, hn⟩ := hx
  have h := sq_eq_one_of_mulEquiv_pgl3 e (x := ⟨x, Sec4.mem_autFix.mpr hτx⟩)
    (w := ⟨w, Sec4.mem_autFix.mpr hτw⟩) ⟨n, Subtype.ext (by simpa using hn)⟩
    (Subtype.ext (by simpa using hw3)) (fun h1 => hw1 (by simpa using congrArg Subtype.val h1))
    (Subtype.ext (by simpa using hxw))
  simpa using congrArg Subtype.val h


theorem sq_eq_one_of_mem_residual_of_not_std {m : ℕ} {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hK : Nat.card K = (2 ^ m) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ m)
    {τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hτ3 : τ ^ 3 = 1)
    (hτin : ¬ IsInnerAut τ) (hstd : ¬ Sec4.IsStdGraphFieldConj σ τ)
    {w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (hτw : τ w = w) {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hx : x ∈ inSubgroup perfectResidual
      (Subgroup.centralizer ({w} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))))
    (hτx : τ x = x) (h2 : ∃ e : ℕ, x ^ 2 ^ e = 1) : x ^ 2 = 1 := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK] at h1
      norm_num at h1
    · exact hm
  have hxw : x * w = w * x := by
    obtain ⟨y, -, rfl⟩ := hx
    exact Subgroup.mem_centralizer_singleton_iff.mp y.2
  rcases Nat.even_or_odd m with hev | hodd
  · obtain ⟨K', _, _, hK', ⟨e⟩⟩ :=
      kF89D4SecondCentEven_holds m hev hm K σ hK hσ τ hτ3 hτin hstd
    have : CharP K' 2 := ringChar.of_eq (Item8KFacts3.ringChar_eq_two_of_card hK')
    exact sq_eq_one_of_autFix_mulEquiv e hτx hτw h2 hw3 hw1 hxw
  · rcases inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds m hodd K σ hK
      hσ τ hτ3 hτin with hs | ⟨-, -, -, -, -, -, K', _, _, hK', ⟨e⟩⟩
    · exact absurd hs hstd
    · have hK'2 : Nat.card K' = 2 ^ (m * 2) := by rw [hK', ← pow_mul]
      have : CharP K' 2 := ringChar.of_eq (Item8KFacts3.ringChar_eq_two_of_card hK'2)
      exact sq_eq_one_of_autFix_mulEquiv e hτx hτw h2 hw3 hw1 hxw

theorem kF84D4OuterSU3_of (hStd : KF84D4OuterSU3Std) : Item8KFacts3.KF84D4OuterSU3 := by
  intro m K _ _ σ hK hσ τ hτ3 hτin w hwS hw3 hw1 hτw
  by_cases hstd : Sec4.IsStdGraphFieldConj σ τ
  · exact hStd m K σ hK hσ τ hτ3 hτin hstd w hwS hw3 hw1 hτw
  · exact Or.inr fun x hx hτx h2 =>
      sq_eq_one_of_mem_residual_of_not_std hK hσ hτ3 hτin hstd hw3 hw1 hτw hx hτx h2

end CFSG.RankThree.PartTwo.Sec8.Item84KFacts4
