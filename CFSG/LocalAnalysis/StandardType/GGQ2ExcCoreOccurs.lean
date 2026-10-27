module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreOccursDict
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNegLabel
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreRawBot
public import CFSG.LocalAnalysis.StandardType.GGFamSubnormal
public import CFSG.LocalAnalysis.StandardType.GGLangGammaComponent
public import CFSG.LocalAnalysis.StandardType.GGFamTameSharp
public import CFSG.LocalAnalysis.StandardType.GGFamComponent
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
public import CFSG.LocalAnalysis.StandardType.GGFamTrivialGamma
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.LocalAnalysis.StandardType.GGFamTame
import CFSG.LocalAnalysis.StandardType.GGLangCoroot

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav

noncomputable section

theorem excRaw_label_eq_labelSL {m : Fin 6} (hm : 2 ≤ m.val) (c : Finset (ExcRaw.Root m)) :
    ExcRaw.label m c = ExcRaw.labelSL c.card (ExcRaw.orthCount m c) := by
  unfold ExcRaw.label
  split
  · omega
  · omega
  · rfl

theorem componentOrbitLength_componentRoots_eq_one_of_neg
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} {S : LangSetup τ L p} (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (j : KernelComponent χ) :
    componentOrbitLength S.ρ (componentRoots χ j) = 1 := by
  have hfin : (componentRoots χ j).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => (isRootComponent_componentRoots j).isRoot γ hγ
  refine componentOrbitLength_eq_one hfin fun γ hγ => ?_
  rw [hρ γ ((isRootComponent_componentRoots j).isRoot γ hγ)]
  exact (isRootComponent_componentRoots j).neg_mem γ hγ

theorem eq_bot_of_forall_rootDiagUnit_eq_one {τ : Tag} {L : Type} [Field L]
    {A : Subgroup (ModGL τ L)} {a : ↥A → Fin τ.rank → Lˣ}
    (ha : ∀ u, rootDiagUnit τ (a u) = u) (h : ∀ u, rootDiagUnit τ (a u) = 1) : A = ⊥ :=
  (Subgroup.eq_bot_iff_forall A).2 fun x hx => (ha ⟨x, hx⟩).symm.trans (h ⟨x, hx⟩)

theorem ggLinImage_bot {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) :
    ggLinImage (p := p) ι (⊥ : Subgroup G) = ⊥ := by
  ext v
  rw [mem_ggLinImage]
  simp

theorem codeComponent_univ
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    {S : LangSetup τ L p} {T₀ : Subgroup (ModGL τ L)} {m : Fin 6}
    (d : ExcCoordDatum S T₀ m) (hΓ : CFSG.Open.IsQuasisimple ↥S.Γ) :
    codeComponent S d.γ Finset.univ = S.Γ := by
  have hroots : codeRoots d.γ Finset.univ = {δ | IsRoot τ δ} := by
    ext δ
    simp only [codeRoots, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, h | h⟩
      · rw [h]; exact d.isRoot i
      · rw [h]; exact IsRoot.neg (d.isRoot i)
    · intro hδ
      obtain ⟨i, h | h⟩ := d.exists_eq δ hδ
      · exact ⟨i, Or.inl h⟩
      · exact ⟨i, Or.inr h⟩
  have hcomm : ⁅S.Γ, S.Γ⁆ = S.Γ := by
    have h := congrArg (Subgroup.map S.Γ.subtype) hΓ.1
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  rw [codeComponent, hroots]
  exact TableCRes.commutator_rootSpan_inf_Γ_eq S (fun γ hγ => hγ) hcomm

theorem isComponentOf_codeComponent_of_occurs
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {m : Fin 6} (hm : 2 ≤ m.val)
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p} (hS : NegLangTwo S)
    {T₀ : Subgroup (ModGL τ L)} (d : ExcCoordDatum S T₀ m) {A : Subgroup (ModGL τ L)}
    (hA : A ≤ T₀) {c : Finset (ExcRaw.Root m)} (hadm : ExcRaw.admissible m c)
    (hc : ExcRaw.occurs m (ggLinImage (p := 3) d.coord A) c) :
    CFSG.Assembly.IsComponentOf (codeComponent S d.γ c)
      (S.Γ ⊓ Subgroup.centralizer (A : Set (ModGL τ L))) := by
  have hchar : CharP L 2 :=
    LangRat.charP_two_of_langSetup_q_eq_two_pow S (f := 1) (hS.1.trans (pow_one 2).symm)
  obtain ⟨a, ha, hT, hap⟩ := exists_excFamily d hA
  by_cases h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1
  · obtain ⟨j, hj⟩ := exists_kernelComponent_of_occurs d hA ha hc
    have hΨ : IsRootComponent (codeRoots d.γ c) := by
      rw [← hj]
      exact isRootComponent_componentRoots j
    have hq := TableCRes.isQuasisimple_rationalComponentM_of_lambda2 hτ S Nat.prime_three
      (by norm_num) hT hap h1 j (n := 1)
      (by rw [componentOrbitLength_componentRoots_eq_one_of_neg hS.2.2 j, hS.1])
      (by
        rw [hj, componentLabel_codeRoots_eq_labelSL hτ d hS.2.2 hΨ hc.1,
          ← excRaw_label_eq_labelSL hm c]
        exact hadm.2)
    obtain ⟨hle, hsub⟩ := TableCRes.langFamSubnormal_of_mem_torus S hT j
    rw [← rationalComponentM_eq_codeComponent hS.2.2 d.γ j hj, ← centralizer_range_excFamily ha]
    exact ⟨hle, (CFSG.Assembly.IsSubnormal.iff_subgroupOf hle).2 hsub,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hq⟩
  · have hAbot : A = ⊥ :=
      eq_bot_of_forall_rootDiagUnit_eq_one ha fun u => not_not.1 fun hu => h1 ⟨u, hu⟩
    rw [hAbot] at hc ⊢
    rw [ggLinImage_bot] at hc
    obtain rfl : c = Finset.univ := (ExcRaw.occurs_bot_iff m c).1 hc
    obtain ⟨-, -, -, -, hΓ, -⟩ := TableCRes.famTrivial_Γ_data hτ S
    rw [codeComponent_univ d hΓ]
    exact (TableCRes.isComponentOf_Γ_inf_centralizer_bot_iff S hΓ S.Γ).2 rfl

theorem exists_code_of_isComponentOf
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {m : Fin 6} (hm : 2 ≤ m.val)
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p} (hS : NegLangTwo S)
    {T₀ : Subgroup (ModGL τ L)} (d : ExcCoordDatum S T₀ m) {A : Subgroup (ModGL τ L)}
    (hA : A ≤ T₀) {X : Subgroup (ModGL τ L)}
    (hX : CFSG.Assembly.IsComponentOf X (S.Γ ⊓ Subgroup.centralizer (A : Set (ModGL τ L)))) :
    ∃ c : Finset (ExcRaw.Root m), ExcRaw.admissible m c ∧
      ExcRaw.occurs m (ggLinImage (p := 3) d.coord A) c ∧ X = codeComponent S d.γ c := by
  have hchar : CharP L 2 :=
    LangRat.charP_two_of_langSetup_q_eq_two_pow S (f := 1) (hS.1.trans (pow_one 2).symm)
  obtain ⟨a, ha, hT, hap⟩ := exists_excFamily d hA
  by_cases h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1
  · have hX' : CFSG.Open.IsComponentOf X
        (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u))) := by
      rw [← isComponentOf_iff_open, centralizer_range_excFamily ha]
      exact hX
    obtain ⟨j, hXj, -⟩ := TableCRes.exists_eq_rationalComponentM_of_isComponentOf S
      Nat.prime_three hτ (by norm_num) hT hap h1
      (fun i => TableCRes.langFamTame_of_prime hτ S Nat.prime_three (by norm_num) hT hap h1 i) hX'
    obtain ⟨c, hocc, hroots⟩ := exists_occurs_of_kernelComponent d hA ha j
    have hKspan : X ≤ rootSpan τ L {γ | ∃ (k : ℕ) (δ : Fin τ.rank → ℤ),
        δ ∈ componentRoots (TableCRes.famCharHom a) j ∧
          γ = (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ} := by
      rw [hXj]
      exact (Subgroup.commutator_le_self _).trans inf_le_left
    obtain ⟨n, hn, hlab⟩ := TableCRes.langFamilyCompLabel_exc hτ S (p := 3) (by norm_num)
      (by norm_num) a hT hap hX' j hKspan
    have hΨ : IsRootComponent (codeRoots d.γ c) := by
      rw [← hroots]
      exact isRootComponent_componentRoots j
    have hn1 : n = 1 := by
      have h2 : 2 ^ n = 2 ^ 1 := by
        rw [hn, componentOrbitLength_componentRoots_eq_one_of_neg hS.2.2 j, hS.1]
      exact Nat.pow_right_injective (le_refl 2) h2
    have hΛ : LargeEvenInLambda2 (ExcRaw.label m c) := by
      have h := hlab.1
      rw [hn1, hroots, componentLabel_codeRoots_eq_labelSL hτ d hS.2.2 hΨ hocc.1] at h
      rwa [excRaw_label_eq_labelSL hm c]
    refine ⟨c, ⟨⟨_, hocc⟩, hΛ⟩, hocc, ?_⟩
    rw [hXj, rationalComponentM_eq_codeComponent hS.2.2 d.γ j hroots]
  · have hAbot : A = ⊥ :=
      eq_bot_of_forall_rootDiagUnit_eq_one ha fun u => not_not.1 fun hu => h1 ⟨u, hu⟩
    rw [hAbot] at hX ⊢
    obtain ⟨-, -, -, -, hΓ, -⟩ := TableCRes.famTrivial_Γ_data hτ S
    refine ⟨Finset.univ, ExcRaw.admissible_univ m, ?_, ?_⟩
    · rw [ggLinImage_bot]
      exact (ExcRaw.occurs_bot_iff m _).2 rfl
    · rw [(TableCRes.isComponentOf_Γ_inf_centralizer_bot_iff S hΓ X).1 hX, codeComponent_univ d hΓ]

theorem excCoreOccurs
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {m : Fin 6} (hm : 2 ≤ m.val) :
    ExcCoreOccurs m τ := by
  intro L _ _ p S hS T₀ d A hA X
  refine ⟨exists_code_of_isComponentOf hτ hm hS d hA, ?_⟩
  rintro ⟨c, hadm, hc, rfl⟩
  exact isComponentOf_codeComponent_of_occurs hτ hm hS d hA hadm hc

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
