module

public import CFSG.LocalAnalysis.StandardType.GGIOneExcLift
public import CFSG.LocalAnalysis.StandardType.GGIOneExcRootAs
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwE6Field
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift

public section

namespace CFSG.StandardType

open CFSG.Assembly
open scoped commutatorElement

@[expose] def GGTwE6RootAsInnInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime →
    p ∣ 2 ^ n + 1 → p ≠ 3 →
    GGEndNodeRootAsInn p (TwE6Delta.liftRank p) (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

@[expose] def GGTwE6RootAsInnThreeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    GGEndNodeRootAsInn 3 (TwE6Delta.liftRank 3) (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

@[expose] def GGTwE6OuterPowInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime →
    p ∣ 2 ^ n + 1 → ∀ φ : MulAut (TwE6Delta.RecipeR K n), φ ^ p = 1 →
      φ ∉ TwE6Delta.RecipeI K n → p ∣ n

@[expose] def GGTwE6CenterPrimeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime →
    p ∣ 2 ^ n + 1 → p ≠ 3 → GGCenterPrime p (TwE6Delta.RecipeR K n)

@[expose] def GGTwE6DeltaInput3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    GGEndNodeIOneDelta 3 (TwE6Delta.liftRank 3) (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

section Certs


theorem ggIE_innerAll_of_bound2L {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (hZ : Subgroup.center R = ⊥)
    (hB : (∃ φ : MulAut R, φ ^ p = 1 ∧ φ ∉ I) → GGInnerDiagBound2L p r R I)
    (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (A As : Subgroup (MulAut L')) (hA : IsElemAbelian p A) (hAAs : A < As)
    (hAs : IsElemAbelian p As) (hcard : Nat.card As ≤ p * Nat.card A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l))
    (hr : p ^ r ≤ Nat.card A) (h3 : p ^ 3 ≤ Nat.card A) (hα : GGNormTwoR ψ A)
    (hnone : GGNoTwoBetween A As) : ∀ a ∈ As, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a₀, ha₀, hnI⟩ := hcon
  have hinj : Function.Injective (ggIE_indAutHom hψ hZ hker) :=
    ggIE_indAutHom_injective hψ hZ hker hperf
  have hEbA : IsElemAbelian p (A.map (ggIE_indAutHom hψ hZ hker)) := ggIE_isElemAbelian_map _ hA
  have hEhA : IsElemAbelian p (As.map (ggIE_indAutHom hψ hZ hker)) :=
    ggIE_isElemAbelian_map _ hAs
  have hEbEh : A.map (ggIE_indAutHom hψ hZ hker) ≤ As.map (ggIE_indAutHom hψ hZ hker) :=
    Subgroup.map_mono hAAs.le
  have hcardb : Nat.card (A.map (ggIE_indAutHom hψ hZ hker)) = Nat.card A :=
    Subgroup.card_map_of_injective hinj
  have hcardh : Nat.card (As.map (ggIE_indAutHom hψ hZ hker)) = Nat.card As :=
    Subgroup.card_map_of_injective hinj
  have hcardle : Nat.card (As.map (ggIE_indAutHom hψ hZ hker)) ≤
      p * Nat.card (A.map (ggIE_indAutHom hψ hZ hker)) := by
    rw [hcardh, hcardb]
    exact hcard
  have hEbI : ((A.map (ggIE_indAutHom hψ hZ hker) : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hφa := ggIE_eq_indAut_of_forall hψ hZ hker hφ
    show ggIE_indAut hψ hZ hker a ∈ I
    rw [← hφa]
    exact hφI
  have hρI : ggIE_indAutHom hψ hZ hker a₀ ∉ I := fun h => by
    obtain ⟨l, hl⟩ := hnI _ h
    exact hl (ggIE_indAut_apply hψ hZ hker a₀ l)
  have hpow : ggIE_indAutHom hψ hZ hker a₀ ^ p = 1 := by
    rw [← map_pow, hAs.2 a₀ ha₀, map_one]
  have hnotI : ¬ ((As.map (ggIE_indAutHom hψ hZ hker) : Subgroup (MulAut R)) :
      Set (MulAut R)) ⊆ I :=
    fun hsub => hρI (hsub (Subgroup.mem_map_of_mem _ ha₀))
  obtain ⟨U, hU1, hU2, hUA⟩ := hα
  have hEbU : ∀ φ ∈ A.map (ggIE_indAutHom hψ hZ hker), ∀ u ∈ U, φ u ∈ U := by
    rintro _ ⟨a, ha, rfl⟩ u hu
    obtain ⟨l, rfl⟩ := hψ u
    have h2 : ggIE_indAutHom hψ hZ hker a (ψ l) = ψ (a l) :=
      ggIE_indAut_apply hψ hZ hker a l
    rw [h2]
    exact hUA a ha l hu
  obtain ⟨U', hU'1, hU'2, hU'E⟩ := hB ⟨_, hpow, hρI⟩ _ _ hEbI hEbA
    (by rw [hcardb]; exact hr) (by rw [hcardb]; exact h3) hEbEh hEhA hcardle hnotI
    ⟨U, hU1, hU2, hEbU⟩
  refine (ggIE_false_of_noTwoBetween hAAs hnone ψ hψ hker hU'1 hU'2
    (fun a ha l hl => ?_)).elim
  have h1 := hU'E (ggIE_indAutHom hψ hZ hker a) (Subgroup.mem_map_of_mem _ ha) (ψ l) hl
  have h2 : ggIE_indAutHom hψ hZ hker a (ψ l) = ψ (a l) := ggIE_indAut_apply hψ hZ hker a l
  rwa [h2] at h1

theorem ggIE_endNodeIOne_twE6 {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hdvd : p ∣ 2 ^ n + 1)
    (hR : GGEndNodeRootAsInn p (TwE6Delta.liftRank p) (TwE6Delta.RecipeR K n)
      (TwE6Delta.RecipeI K n))
    (hδ : GGEndNodeIOneDelta p (TwE6Delta.liftRank p) (TwE6Delta.RecipeR K n)
      (TwE6Delta.RecipeI K n))
    (hX : GGTwE6InnerDiagBound2LInput) (hO : GGTwE6OuterPowInput) :
    GGEndNodeIOne p (TwE6Delta.liftRank p) (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) :=
  ggIE_endNodeIOne_of_rootAsInn_cases hR hδ fun L' _ _ ψ hψ hker hperf A As hA hAAs hAs hcard hAI
      hr h3 hα hnone =>
    ggIE_innerAll_of_bound2L hp (TwE6Delta.center_recipeR_eq_bot hn hK)
      (fun ⟨φ, hφp, hφI⟩ => hX K n p hn hK hp hdvd (hO K n p hn hK hp hdvd φ hφp hφI))
      L' ψ hψ hker hperf A As hA hAAs hAs hcard hAI hr h3 hα hnone

theorem ggIE_labelAll_twE6 (hX : GGTwE6InnerDiagBound2LInput)
    (hR : GGTwE6RootAsInnInput) (hR3 : GGTwE6RootAsInnThreeInput)
    (hδ3 : GGTwE6DeltaInput3) (hC : GGTwE6CenterPrimeInput) (hO : GGTwE6OuterPowInput)
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (htag : lab.tag = .twE6)
    (hlab : LargeEvenInLambda2 lab) (hdvd : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
      ∃ r, GGTorusLift p r R ∧ GGEndNodeIOne p r R I := by
  refine TwE6Delta.labelAll htag fun K _ _ hK => ?_
  refine ⟨TwE6Delta.ggOutdiagOdd_twE6 hlab.1 hK p, _,
    ggTorusLift_twE6Add_holds hlab.1 hK hp hdvd, ?_⟩
  by_cases h3 : p = 3
  · subst h3
    exact ggIE_endNodeIOne_twE6 Nat.prime_three hlab.1 hK hdvd
      (hR3 K lab.n hlab.1 hK hdvd) (hδ3 K lab.n hlab.1 hK hdvd) hX hO
  · exact ggIE_endNodeIOne_twE6 hp hlab.1 hK hdvd (hR K lab.n p hlab.1 hK hp hdvd h3)
      (ggEndNodeIOneDelta_of_prime (TwE6Delta.ggOutdiagPrime_twE6 hlab.1 hK hp h3)
        (hC K lab.n p hlab.1 hK hp hdvd h3)) hX hO

end Certs

end CFSG.StandardType
