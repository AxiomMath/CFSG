module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
public import CFSG.LocalAnalysis.StandardType.GGAssemblySixDefs
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDesc

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTwE6SplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1

theorem dvd_two_pow_add_one_of_split_twE6 {p : ℕ} {lab : LargeEvenLabel} (ht : lab.tag = .twE6)
    (hs : LargeEvenSplit p lab) : p ∣ 2 ^ lab.n + 1 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht ⊢
  subst ht
  rcases hs with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨hn, hp⟩
  · simp [LargeEvenUntwisted] at h
  · exact h
  · rcases h with h | h <;> simp at h
  · dsimp only at hn
    subst hn hp
    norm_num

theorem ggTwE6SplitLabel_of_round6 {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBOtherRound6 p lab) (hs : LargeEvenSplit p lab) :
    GGTwE6SplitLabel p lab :=
  have ht := ggTableBOtherRound6_twE6 hp hlab h hs
  ⟨ht, dvd_two_pow_add_one_of_split_twE6 ht hs⟩

namespace TwE6Delta

@[expose] def liftRank (p : ℕ) : ℕ := if p = 3 then 4 else 5

theorem liftRank_of_ne {p : ℕ} (hp3 : p ≠ 3) : liftRank p = 5 := by
  simp [liftRank, hp3]

theorem liftRank_three : liftRank 3 = 4 := rfl

end TwE6Delta

@[expose] def GGTwE6All (P : ℕ → ℕ → (R : Type) → [Group R] → Set (MulAut R) → Prop) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime →
    p ∣ 2 ^ n + 1 → P p (TwE6Delta.liftRank p) (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

@[expose] def GGTwE6TorusLiftInput : Prop :=
  GGTwE6All fun p r R _ _ => GGTorusLift p r R

@[expose] def GGTwE6BstarInput : Prop :=
  GGTwE6All fun p r R _ I => p ≠ 3 → GGBstarBoundInnR p r R I

@[expose] def GGTwE6BstarThreeInput : Prop :=
  GGTwE6All fun p r R _ I => p = 3 → GGBstarBoundInnR p r R I ∧ GGBstarBoundDelta p r R I

@[expose] def GGTwE6EndNodeInput : Prop :=
  GGTwE6All fun p r R _ _ => p ≠ 3 → TableBUR.GGEndNodeEltAdm p r R

@[expose] def GGTwE6EndNodeThreeInput : Prop :=
  GGTwE6All fun p r R _ I => p = 3 → GGEndNodeAdm p r R I

namespace TwE6Delta

theorem ggEndNodeAdm_of_pow_eq_one {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGEndNodeAdm p r R {φ | φ ∈ I ∧ φ ^ p = 1}) : GGEndNodeAdm p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hadm
  refine h L' ψ hψ hker hperf A hA (fun a ha => ?_) hr h3 hadm
  obtain ⟨φ, hφI, hφ⟩ := hAI a ha
  refine ⟨φ, ⟨hφI, ?_⟩, hφ⟩
  have h1 : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
    intro k
    induction k with
    | zero => intro l; rfl
    | succ k ih =>
      intro l
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
  ext x
  obtain ⟨l, rfl⟩ := hψ x
  rw [MulAut.one_apply, h1 p l, hA.2 a ha, MulAut.one_apply]

theorem labelAll {lab : LargeEvenLabel} (ht : lab.tag = .twE6)
    {Q : (R : Type) → [Group R] → Set (MulAut R) → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ lab.n) ^ 2 →
      Q (RecipeR K lab.n) (RecipeI K lab.n)) :
    LargeEvenLabelAll lab fun R _ I _ => Q R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h
  subst ht
  intro C hC
  exact recipeTwisted_and (P := fun R _ I _ => Q R I) (fun K _ _ hK => h K hK) hC


variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem bstar_data (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 2 ^ n + 1) (hT : GGTorusLift p (liftRank p) (RecipeR K n))
    (hB : p ≠ 3 → GGBstarBoundInnR p (liftRank p) (RecipeR K n) (RecipeI K n))
    (hB3 : p = 3 → GGBstarBoundInnR p (liftRank p) (RecipeR K n) (RecipeI K n) ∧
      GGBstarBoundDelta p (liftRank p) (RecipeR K n) (RecipeI K n)) :
    GGOutdiagOdd p (RecipeR K n) (RecipeI K n) ∧ ∃ r, GGTorusLift p r (RecipeR K n) ∧
      GGBstarBoundInn p r (RecipeR K n) (RecipeI K n) ∧
      (GGDeltaLocal p r (RecipeR K n) (RecipeI K n) ∨
        GGBstarBoundDelta p r (RecipeR K n) (RecipeI K n)) := by
  have hZ := center_recipeR_eq_bot hn hK
  refine ⟨ggOutdiagOdd_twE6 hn hK p, liftRank p, hT, ?_⟩
  by_cases h3 : p = 3
  · exact ⟨ggBstarBoundInn_of_R hp hZ (hB3 h3).1, Or.inr (hB3 h3).2⟩
  · exact ⟨ggBstarBoundInn_of_R hp hZ (hB h3), Or.inl (ggDeltaLocal_twE6 hn hK hp
      (TableBU.ne_two_of_dvd_two_pow_add_one hn hpn) h3 _)⟩

theorem endNode_data (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 2 ^ n + 1) (hT : GGTorusLift p (liftRank p) (RecipeR K n))
    (hE : p ≠ 3 → TableBUR.GGEndNodeEltAdm p (liftRank p) (RecipeR K n))
    (hE3 : p = 3 → GGEndNodeAdm p (liftRank p) (RecipeR K n) (RecipeI K n)) :
    ∃ r, GGTorusLift p r (RecipeR K n) ∧ GGEndNodeAdm p r (RecipeR K n) (RecipeI K n) := by
  refine ⟨liftRank p, hT, ?_⟩
  by_cases h3 : p = 3
  · exact hE3 h3
  · have hZ := center_recipeR_eq_bot hn hK
    refine ggEndNodeAdm_of_pow_eq_one (TableBUR.ggEndNodeAdm_of_eltAdm
      (fun φ hφ => ggOutdiagPrime_twE6 hn hK hp h3 φ hφ.1 hφ.2) hZ ?_ (hE h3))
    intro L' _ _ ψ hψ hker hperf
    rw [TableBUR.ker_eq_center_of_surjective hψ hker hZ]
    exact ggCenterPrime_twE6 hn hK hp (TableBU.ne_two_of_dvd_two_pow_add_one hn hpn) h3 L' ψ hψ
      hker hperf

end TwE6Delta

section Main


theorem ggBstarInputOn_twE6Split (hT : GGTwE6TorusLiftInput) (hB : GGTwE6BstarInput)
    (hB3 : GGTwE6BstarThreeInput) : GGBstarInputOn GGTwE6SplitLabel :=
  ggBstarInputOn_of_labels_delta ggLNoncyclicInput_holds fun p lab hp hlab hS _ =>
    TwE6Delta.labelAll hS.1 fun K _ _ hK => TwE6Delta.bstar_data hlab.1 hK hp hS.2
      (hT K lab.n p hlab.1 hK hp hS.2) (hB K lab.n p hlab.1 hK hp hS.2)
      (hB3 K lab.n p hlab.1 hK hp hS.2)

theorem ggStdSubPreInputOn_twE6Split (hT : GGTwE6TorusLiftInput) (hE : GGTwE6EndNodeInput)
    (hE3 : GGTwE6EndNodeThreeInput) : GGStdSubPreInputOn GGTwE6SplitLabel :=
  ggStdSubPreInputOn_of_labels_adm ggLNoncyclicInput_holds fun p lab hp hlab hS =>
    TwE6Delta.labelAll hS.1 fun K _ _ hK => TwE6Delta.endNode_data hlab.1 hK hp hS.2
      (hT K lab.n p hlab.1 hK hp hS.2) (hE K lab.n p hlab.1 hK hp hS.2)
      (hE3 K lab.n p hlab.1 hK hp hS.2)

end Main

theorem ggBstarInputOn_round6_of_split (h : GGBstarInputOn GGTwE6SplitLabel) :
    GGBstarInputOn GGTableBOtherRound6 := by
  intro G _ _ p B x L hI hM
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  exact h G p B x L hI ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ', hS, hP⟩ =>
      ⟨hs, hna, θ', ggTwE6SplitLabel_of_round6 hp hlab hS hP.1, hP⟩) hraw⟩

theorem ggStdSubPreInputOn_round6_of_split (h : GGStdSubPreInputOn GGTwE6SplitLabel) :
    GGStdSubPreInputOn GGTableBOtherRound6 := by
  intro G _ _ p B x L hI hM
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  exact h G p B x L hI ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ', hS, hP⟩ =>
      ⟨hs, hna, θ', ggTwE6SplitLabel_of_round6 hp hlab hS hP.1, hP⟩) hraw⟩

section Round6


theorem ggBstarInputOn_round6_of_twE6 (hT : GGTwE6TorusLiftInput) (hB : GGTwE6BstarInput)
    (hB3 : GGTwE6BstarThreeInput) : GGBstarInputOn GGTableBOtherRound6 :=
  ggBstarInputOn_round6_of_split (ggBstarInputOn_twE6Split hT hB hB3)

theorem ggStdSubPreInputOn_round6_of_twE6 (hT : GGTwE6TorusLiftInput) (hE : GGTwE6EndNodeInput)
    (hE3 : GGTwE6EndNodeThreeInput) : GGStdSubPreInputOn GGTableBOtherRound6 :=
  ggStdSubPreInputOn_round6_of_split (ggStdSubPreInputOn_twE6Split hT hE hE3)

end Round6

end CFSG.StandardType
