module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Levi
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviFive
public import CFSG.LocalAnalysis.StandardType.GGTBJSpPlus
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGResJPrimeLarge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def GGTBJTwE6LeviAt (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Bs X J : Subgroup G), ∀ [Fact p.Prime],
    IsElemAbelian p Bs →
    (∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) →
    ∀ (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (ψ₀ : X →* R),
    GGTorusTBGroup p 5 R I X ψ₀ (ggGamma X hN).range →
    ∀ (g : G), g ∈ Bs → (∃ x ∈ X, g * x * g⁻¹ ≠ x) →
    IsComponentOf J (X ⊓ Subgroup.centralizer ({g} : Set G)) →
    ∀ bX : Bs, bX ≠ 1 → (bX : G) ∈ Subgroup.centralizer (X : Set G) →
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3 →
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J


theorem ggTBJTwE6LeviAt_recipe {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hp5 : 5 < p) (hpq : p ∣ 2 ^ n + 1) :
    GGTBJTwE6LeviAt p (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  intro G _ _ Bs X J _ hBs hSC hN ψ₀ hTB g hgBs hgX hcomp bX hbX1 hbXC hcount
  let y : MulAut X := ggGamma X hN ⟨g, hgBs⟩
  have hy1 : y ≠ 1 := by
    intro h1
    have hgC := (ggGamma_eq_one_iff X hN ⟨g, hgBs⟩).mp h1
    obtain ⟨x, hx, hne⟩ := hgX
    have hc := Subgroup.mem_centralizer_iff.mp hgC x hx
    exact hne (by rw [← hc, mul_inv_cancel_right])
  have hJX : J ≤ X := hcomp.1.trans inf_le_left
  have hJ := isComponentOf_subgroupOf_fixSubgroup hN ⟨g, hgBs⟩ hcomp
  exact ggTBJ_twE6_levi_side hn hK hp5 hpq hBs hSC hN ψ₀ hTB y ⟨⟨g, hgBs⟩, rfl⟩
    hy1 hJX hJ bX hbX1 hbXC hcount

theorem ggTBJTwE6Levi_of_innerDiag (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs X J : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hI : GGInnerDiagOn Bs X) (hp5 : 5 < p) {n : ℕ} (hpq : p ∣ 2 ^ n + 1)
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hX : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (X ⧸ Subgroup.center X))
    (hcard : commutator X = ⊤ → ∀ {R : Type} [Group R]
      (θ : X ⧸ Subgroup.center X ≃* R) (hN : Bs ≤ Subgroup.normalizer (X : Set G)),
      GGTorusLift p 5 R →
        p ^ 5 ≤ Nat.card (ggGamma X hN).range ∧ p ^ 3 ≤ Nat.card (ggGamma X hN).range)
    (g : G) (hgBs : g ∈ Bs) (hgX : ∃ x ∈ X, g * x * g⁻¹ ≠ x)
    (hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({g} : Set G)))
    (bX : Bs) (hbX1 : bX ≠ 1) (hbXC : (bX : G) ∈ Subgroup.centralizer (X : Set G))
    (hcount : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  have hp : p.Prime := Fact.out
  have hmark := ggInnerDiagOn_relabel hRig hI hΛ hX
  have hall : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab = ⟨.twE6, 0, n⟩ →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard
        fun R _ I _ => GGTorusLift p 5 R ∧ GGTBJTwE6LeviAt p R I) := by
    intro lab hlab he
    subst he
    refine nbrC_labelAll_guard ?_
    have h1 := largeEvenLabelAll_torusLift_twE6Add_holds hp hlab ⟨rfl, hpq⟩
    have h2 : LargeEvenLabelAll (⟨.twE6, 0, n⟩ : LargeEvenLabel)
        fun R _ I _ => GGTBJTwE6LeviAt p R I :=
      TwE6Delta.labelAll rfl fun K _ _ hK => ggTBJTwE6LeviAt_recipe hlab.1 hK hp5 hpq
    refine (largeEvenLabelAll_and h1 h2).mono fun _ _ _ _ ⟨hL, hF⟩ => ⟨?_, hF⟩
    rwa [TwE6Delta.liftRank_of_ne (by omega)] at hL
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => lab = (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (P' := fun R _ I _ => GGTorusLift p 5 R ∧ GGTBJTwE6LeviAt p R I) hall
    (fun _ _ _ _ _ _ hP => hP.1) hmark
  obtain ⟨R, _, I, Fm, -, -, θ, ⟨-, hN, h3I⟩, hlift, hLevi⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN h3I hb
  obtain ⟨hr, h3⟩ := hcard hXc θ hN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hN hBsI hr h3
  exact hLevi G Bs X J hBs hSC hN (ggQuotHom θ) hTB g hgBs hgX hcomp bX hbX1 hbXC hcount

theorem ggTBJTwE6LeviL_large_prime (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (L ⧸ Subgroup.center L))
    (hp5 : 5 < p) (hpq : p ∣ 2 ^ n + 1) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  by_cases h3 : 3 ∣ 2 ^ n + 1
  · refine ggTBJE6LeviL_of_cellFn hH fun hBs hSC hJL hyBs hJg hgX hcomp bX hbX1 hbXC hcount => ?_
    exact ggTBJTwE6Levi_of_innerDiag hRig hBs hSC hH.2.2.1.1 hp5 hpq hΛ hL
      (fun hXc {R} [Group R] θ hN hlift => card_range_ggGamma_bstar_ge hH.1 hXc θ hN hlift)
      y hyBs hgX hcomp bX hbX1 hbXC hcount
  · exact ggTBJTwE6LeviL_ge5 hRig hH hΛ hL (by omega) hpq h3

theorem ggTBJTwE6LeviK_large_prime (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K))
    (hp5 : 5 < p) (hpq : p ∣ 2 ^ n + 1) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  by_cases h3 : 3 ∣ 2 ^ n + 1
  · refine ggTBJE6LeviK_of_cellFn hH hJK fun hBs hSC hJK' hxBs hJg hgX hcomp bX hbX1 hbXC hcount => ?_
    exact ggTBJTwE6Levi_of_innerDiag hRig hBs hSC (hH.2.2.1.2 y K hH.2.2.2.2.1)
      hp5 hpq hΛ hK
      (fun hXc {R} [Group R] θ hN hlift =>
        ⟨pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hH.2.2.2.2.1 hXc θ hN hlift,
          pow_three_le_card_range_ggGamma_bstar hH.1 hH.2.2.2.2.1 hN⟩)
      x hxBs hgX hcomp bX hbX1 hbXC hcount
  · exact ggTBJTwE6LeviK_ge5 hRig hH hJK hΛ hK (by omega) hpq h3


theorem ggTBJLeftOn_twE6_large_prime :
    GGTBJLeftOn (fun p lab => lab.tag = .twE6 ∧ 5 < p ∧ p ∣ 2 ^ lab.n + 1) := by
  intro G _ _ p B Bs x L D J y K hH _ hmark _
  obtain ⟨lab, hΛ, hhas, R, hR, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hmark
  obtain ⟨tag, r, n⟩ := lab
  obtain ⟨htag, hp5, hpq⟩ := hP.1
  subst htag
  have hr : r = 0 := hΛ.2
  subst hr
  exact (ggTBJTwE6LeviL_large_prime ggLabelRigidInput_holds hH hΛ hhas hp5 hpq).elim
    Or.inl (fun h => Or.inr (Or.inl h))


theorem ggTBJNbrOn_twE6_large_prime :
    GGTBJNbrOn (fun p lab => lab.tag = .twE6 ∧ 5 < p ∧ p ∣ 2 ^ lab.n + 1) := by
  intro G _ _ p B Bs x L D J y K hH _ hmark _
  obtain ⟨lab, hΛ, hhas, R, hR, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hmark
  obtain ⟨tag, r, n⟩ := lab
  obtain ⟨htag, hp5, hpq⟩ := hP.1
  subst htag
  have hr : r = 0 := hΛ.2
  subst hr
  have hJK : J ≤ K := hH.J_le_K_of_twE6_plus hmark
  exact (ggTBJTwE6LeviK_large_prime ggLabelRigidInput_holds hH hJK hΛ hhas hp5 hpq).elim
    Or.inl (fun h => Or.inr (Or.inl h))

end CFSG.StandardType

end
