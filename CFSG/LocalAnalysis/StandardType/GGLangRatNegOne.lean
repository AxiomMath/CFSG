module

public import CFSG.LocalAnalysis.StandardType.GGLangRatFixedChassis
public import Certificates.Certificate13659
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyStep
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
import CFSG.LocalAnalysis.StandardType.GGLangCoroot
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
import CFSG.LieType.Chevalley.WeylRoots
import CFSG.LieType.Chevalley.KernelComponentRoots
import CFSG.HardMathSupport.Timmesfeld.RootAut.Orbit
import CFSG.LocalAnalysis.StandardType.GGLangRatCentreSqInner
import CFSG.LocalAnalysis.StandardType.GGLangRatNegOneFrame
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartOne.KE.ThreeA1Group

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped TensorProduct commutatorElement

theorem langRatNegOne_norm_mem
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hq : S.D.q = 2 ^ f) (hAlg : S.IsAlgebraic)
    {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom b)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom b) i =
      componentRoots (rootCharHom b) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom b) i ≠
        componentRoots (rootCharHom b) i)
    {P : CycFamily S.D.step s} (hP : P = outerOrbitFamily S hb i hs hmin) (x g : P.S 0)
    (hx : iterHom S.D.step s (x : ModGL τ L) = x) (hg : iterHom S.D.step s (g : ModGL τ L) = g)
    (hg2 : g * g = 1) (hinv : g * x * g⁻¹ = x⁻¹) :
    P.norm (x * x) ∈ rationalComponent S.ρ S.Γ (rootCharHom b) i := by
  have hτ' : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hXA : P.norm x ∈ P.Afix := P.norm_mem_Afix hx
  have hGA : P.norm g ∈ P.Afix := P.norm_mem_Afix hg
  have hAmodel : ∀ y ∈ P.Afix, y ∈ S.D.model := by
    intro y hy
    refine ⟨?_, hy.2⟩
    have : P.A ≤ adjointGroup τ L := by
      rw [hP]
      refine iSup_le fun k => iSup₂_le fun γ _ => ?_
      rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      exact pinnedX_mem_adjointGroup _ _
    exact this hy.1
  have hXM := hAmodel _ hXA
  have hGM := hAmodel _ hGA
  have hGG : P.norm g * P.norm g = 1 := by rw [← map_mul, hg2, map_one]
  have hGXG : P.norm g * P.norm x * (P.norm g)⁻¹ = (P.norm x)⁻¹ := by
    have := congrArg P.norm hinv
    simpa only [map_mul, map_inv] using this
  have hD : P.norm (x * x) = ⁅P.norm x, P.norm g⁆ := by
    have h1 : P.norm g * (P.norm x)⁻¹ * (P.norm g)⁻¹ = P.norm x := by
      have h := congrArg (fun y => y⁻¹) hGXG
      simpa [mul_assoc] using h
    have h2 : ⁅P.norm x, P.norm g⁆ = P.norm x * (P.norm g * (P.norm x)⁻¹ * (P.norm g)⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [map_mul, h2, h1]
  have hDΓ : P.norm (x * x) ∈ S.Γ := by
    rw [hD]
    exact Subgroup.commutator_mem_commutator hXM hGM
  have hXΓ : P.norm x ∈ S.Γ :=
    langModel_mem_Γ_of_sq_mem S hτ' hq hAlg hXM (by rw [pow_two, ← map_mul]; exact hDΓ)
  have hGΓ : P.norm g ∈ S.Γ :=
    langModel_mem_Γ_of_sq_eq_one S hτ' hq hAlg hGM (by rw [pow_two]; exact hGG)
  have hAr : ∀ y ∈ P.Afix, y ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom b) i) := by
    intro y hy
    have := hy.1
    rw [hP, outerOrbitFamily_A] at this
    exact this
  have hXR : P.norm x ∈ rationalSpan S.ρ S.Γ (rootCharHom b) i :=
    Subgroup.mem_inf.2 ⟨hAr _ hXA, hXΓ⟩
  have hGR : P.norm g ∈ rationalSpan S.ρ S.Γ (rootCharHom b) i :=
    Subgroup.mem_inf.2 ⟨hAr _ hGA, hGΓ⟩
  rw [hD]
  exact Subgroup.commutator_mem_commutator hXR hGR

private theorem langRatNO_smul_sub_mem_span
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : ∀ δ ∈ Ψ, IsRoot τ δ) {a : WeylGroup τ}
    (ha : a ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ}) :
    (∀ x : Fin τ.rank → ℤ, a • x - x ∈ Submodule.span ℤ Ψ) ∧
      (∀ y ∈ Submodule.span ℤ Ψ, a • y ∈ Submodule.span ℤ Ψ) := by
  induction ha using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨δ, hδ, rfl⟩ := hs
    have hδr := hΨ δ hδ
    refine ⟨fun x => ?_, fun y hy => ?_⟩
    · rw [rootReflection_smul hδr, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span hδ))
    · rw [rootReflection_smul hδr]
      exact Submodule.sub_mem _ hy (Submodule.smul_mem _ _ (Submodule.subset_span hδ))
  | one => exact ⟨fun x => by simp, fun y hy => by simpa using hy⟩
  | mul a b _ _ iha ihb =>
    refine ⟨fun x => ?_, fun y hy => ?_⟩
    · have h1 := iha.1 (b • x)
      have h2 := ihb.1 x
      rw [mul_smul]
      simpa using Submodule.add_mem _ h1 h2
    · rw [mul_smul]
      exact iha.2 _ (ihb.2 y hy)
  | inv a _ iha =>
    refine ⟨fun x => ?_, fun y hy => ?_⟩
    · have h := iha.1 (a⁻¹ • x)
      rw [smul_inv_smul] at h
      simpa using Submodule.neg_mem _ h
    · have h := iha.1 (a⁻¹ • y)
      rw [smul_inv_smul] at h
      simpa using Submodule.sub_mem _ hy h

private theorem langRatNO_eq_one_of_fix
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : ∀ δ ∈ Ψ, IsRoot τ δ) {a : WeylGroup τ}
    (ha : a ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ})
    (hfix : ∀ γ ∈ Ψ, a • γ = γ) : a = 1 := by
  have hfixΛ : ∀ y ∈ Submodule.span ℤ Ψ, a • y = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact hfix x hx
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add, hx, hy]
    | smul c x _ hx => rw [smul_comm, hx]
  have hall : ∀ x : Fin τ.rank → ℤ, a • x = x := by
    intro x
    have hy : x - a • x ∈ Submodule.span ℤ Ψ := by
      have := Submodule.neg_mem _ ((langRatNO_smul_sub_mem_span hΨ ha).1 x)
      simpa using this
    have hay : a • (x - a • x) = x - a • x := hfixΛ _ hy
    have hpow : ∀ k : ℕ, (a ^ k) • x = x - k • (x - a • x) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', mul_smul, ih, smul_sub, smul_comm a k (x - a • x), hay, succ_nsmul]
        abel
    have hN : 0 < orderOf a := (isOfFinOrder_of_finite a).orderOf_pos
    have h2 := hpow (orderOf a)
    rw [pow_orderOf_eq_one, one_smul] at h2
    have h3 : orderOf a • (x - a • x) = 0 := by
      have := congrArg (fun v => x - v) h2
      simpa using this.symm
    have h4 : x - a • x = 0 := by
      rcases smul_eq_zero.1 h3 with h | h
      · omega
      · exact h
    exact (sub_eq_zero.1 h4).symm
  exact ext_single fun i => by rw [hall, one_smul]

private theorem langRatNO_conj_mem
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : ∀ δ ∈ Ψ, IsRoot τ δ) {u : WeylGroup τ}
    (hu : ∀ δ ∈ Ψ, u • δ ∈ Ψ) {a : WeylGroup τ}
    (ha : a ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ}) :
    u * a * u⁻¹ ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} := by
  induction ha using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨δ, hδ, rfl⟩ := hs
    rw [← rootReflection_smul_root u (hΨ δ hδ)]
    exact Subgroup.subset_closure ⟨u • δ, hu δ hδ, rfl⟩
  | one => simp
  | mul a b _ _ iha ihb =>
    have h : u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
    rw [h]
    exact mul_mem iha ihb
  | inv a _ iha =>
    have h : u * a⁻¹ * u⁻¹ = (u * a * u⁻¹)⁻¹ := by group
    rw [h]
    exact inv_mem iha

private theorem langRatNO_conj_eq
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : ∀ δ ∈ Ψ, IsRoot τ δ) {a u : WeylGroup τ}
    (ha : a ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ})
    (haneg : ∀ γ ∈ Ψ, a • γ = -γ) (hu : ∀ δ ∈ Ψ, u • δ ∈ Ψ) (hu' : ∀ δ ∈ Ψ, u⁻¹ • δ ∈ Ψ) :
    u * a * u⁻¹ = a := by
  have hb : a⁻¹ * (u * a * u⁻¹) ∈
      Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} :=
    mul_mem (inv_mem ha) (langRatNO_conj_mem hΨ hu ha)
  have hfix : ∀ γ ∈ Ψ, (a⁻¹ * (u * a * u⁻¹)) • γ = γ := by
    intro γ hγ
    have h1 : (u * a * u⁻¹) • γ = -γ := by
      rw [mul_smul, mul_smul, haneg _ (hu' γ hγ), smul_neg, smul_inv_smul]
    have h2 : a⁻¹ • γ = -γ := by
      have h3 : a • (-γ) = γ := by rw [smul_neg, haneg γ hγ, neg_neg]
      calc a⁻¹ • γ = a⁻¹ • (a • (-γ)) := by rw [h3]
        _ = -γ := inv_smul_smul a _
    rw [mul_smul, h1, smul_neg, h2, neg_neg]
  exact (inv_mul_eq_one.1 (langRatNO_eq_one_of_fix hΨ hb hfix)).symm

private theorem langRatNO_step_canonicalRep
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (c : WeylGroup τ) :
    S.D.step (canonicalRep (coxeterSystem τ) L c) =
      canonicalRep (coxeterSystem τ) L (w * c * w⁻¹) := by
  let σ : L ≃+* L := RingEquiv.ofBijective Fr (S.frobenius_bijective hFr)
  have hσ : σ.toRingHom = Fr := RingHom.ext fun c => rfl
  have h1 : Units.map (entrywiseHom Fr) (canonicalRep (coxeterSystem τ) L c) =
      canonicalRep (coxeterSystem τ) L c := by
    rw [← hσ]
    exact entrywise_canonicalRep σ c
  show S.D.n * S.D.Φ (canonicalRep (coxeterSystem τ) L c) * S.D.n⁻¹ = _
  rw [hΦ, h1, hn, CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
    CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
    ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_inv_of_charTwo]

private theorem langRatNO_iterHom_canonicalRep
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (c : WeylGroup τ)
    (k : ℕ) :
    iterHom S.D.step k (canonicalRep (coxeterSystem τ) L c) =
      canonicalRep (coxeterSystem τ) L (w ^ k * c * (w ^ k)⁻¹) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterHom_succ, ih, langRatNO_step_canonicalRep S hFr hΦ hn]
    congr 1
    group

private theorem langRatNO_canonicalRep_mem_rootSpan
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : ∀ δ ∈ Ψ, IsRoot τ δ) (hneg : ∀ δ ∈ Ψ, -δ ∈ Ψ) {a : WeylGroup τ}
    (ha : a ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ}) :
    canonicalRep (coxeterSystem τ) L a ∈ rootSpan τ L Ψ := by
  induction ha using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨δ, hδ, rfl⟩ := hs
    rw [← CFSG.RankThree.Chevalley.EvenF4QPlus.rootWeylSL2_one_eq_canonicalRep_of_charTwo
      (M := L) (hΨ δ hδ)]
    have h := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_mem_rootSpan_pair (L := L)
      (hΨ δ hδ) (nSL (1 : Lˣ))
    refine (iSup₂_le fun α hα => ?_ : rootSpan τ L {δ, -δ} ≤ rootSpan τ L Ψ) h
    rcases hα with rfl | rfl
    · exact le_iSup₂_of_le α hδ le_rfl
    · exact le_iSup₂_of_le (-δ) (hneg δ hδ) le_rfl
  | one => simp [canonicalRep_one]
  | mul a b _ _ iha ihb =>
    rw [CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo]
    exact mul_mem iha ihb
  | inv a _ iha =>
    rw [← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_inv_of_charTwo]
    exact inv_mem iha

private theorem langRatNO_Hchar_neg
    {τ : Tag} {L : Type} [Field L] (x : Fin τ.rank → ℤ) (u : Lˣ) :
    Hchar (τ := τ) (-x) u = (Hchar x u)⁻¹ := by
  have h0 : Hchar (τ := τ) (0 : Fin τ.rank → ℤ) u = 1 := by
    funext l
    simp [Hchar, iform]
  have h1 : Hchar (τ := τ) (-x) u * Hchar x u = 1 := by
    rw [Hchar_add, neg_add_cancel]
    exact h0
  exact eq_inv_of_mul_eq_one_left h1

private theorem langRatNO_conj_prod
    {τ : Tag} {L : Type} [Field L] {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    {w : WeylGroup τ} (hw : MapsRootLines n w) (δ : ℕ → Fin τ.rank → ℤ) (c : ℕ → Lˣ) (r : ℕ) :
    n * rootDiagUnit τ (∏ t ∈ Finset.range r, Hchar (δ t) (c t)) * n⁻¹ =
      rootDiagUnit τ (∏ t ∈ Finset.range r, Hchar (w • δ t) (c t)) := by
  induction r with
  | zero => simp [CFSG.LieType.Chevalley.rootDiagUnit_one]
  | succ r ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, CFSG.LieType.Chevalley.rootDiagUnit_mul,
      CFSG.LieType.Chevalley.rootDiagUnit_mul, ← ih]
    have h := conj_Hel hn hw (δ r) (c r)
    unfold Hel at h
    rw [← h]
    group

private theorem langRatNO_conj_inv
    {τ : Tag} {L : Type} [Field L] {a : WeylGroup τ} (δ : ℕ → Fin τ.rank → ℤ) (c : ℕ → Lˣ)
    (r : ℕ) (hδ : ∀ t < r, a • δ t = -δ t) :
    canonicalRep (coxeterSystem τ) L a *
        rootDiagUnit τ (∏ t ∈ Finset.range r, Hchar (δ t) (c t)) *
        (canonicalRep (coxeterSystem τ) L a)⁻¹ =
      (rootDiagUnit τ (∏ t ∈ Finset.range r, Hchar (δ t) (c t)))⁻¹ := by
  rw [langRatNO_conj_prod (canonicalRep_mem_monomialSubgroup L a) (mapsRootLines_canonicalRep a),
    CFSG.LieType.Chevalley.rootDiagUnit_inv]
  congr 1
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [hδ t (Finset.mem_range.1 ht), langRatNO_Hchar_neg]

private theorem langRatNO_prod_mem_rootSpan
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] (hτ : SimplyLacedTag τ)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : ∀ δ ∈ Ψ, IsRoot τ δ) (hneg : ∀ δ ∈ Ψ, -δ ∈ Ψ)
    (δ : ℕ → Fin τ.rank → ℤ) (c : ℕ → Lˣ) (r : ℕ) (hδ : ∀ t < r, δ t ∈ Ψ) :
    rootDiagUnit τ (∏ t ∈ Finset.range r, Hchar (δ t) (c t)) ∈ rootSpan τ L Ψ := by
  induction r with
  | zero => simp [CFSG.LieType.Chevalley.rootDiagUnit_one]
  | succ r ih =>
    rw [Finset.prod_range_succ, CFSG.LieType.Chevalley.rootDiagUnit_mul]
    have hr : δ r ∈ Ψ := hδ r (Nat.lt_succ_self r)
    refine mul_mem (ih fun t ht => hδ t (Nat.lt_succ_of_lt ht)) ?_
    have h := Hel_root_mem_rootSpan hτ (L := L) (hΨ _ hr) (c r)
    refine (iSup₂_le fun α hα => ?_ : rootSpan τ L {δ r, -δ r} ≤ rootSpan τ L Ψ) h
    rcases hα with rfl | rfl
    · exact le_iSup₂_of_le _ hr le_rfl
    · exact le_iSup₂_of_le _ (hneg _ hr) le_rfl

theorem langRatNegOne_localNorm_of_twistInner
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .E7 ∨ τ = .E8) (hAlg : S.IsAlgebraic)
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom b))
    (hneg : twistInner (componentRoots (rootCharHom b) i) (fun γ => -γ))
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom b) i) (u : Lˣ) (r : ℕ)
    (hwr : (w ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r)) • γ = γ)
    (hur : u ^ (S.D.q ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r)) = u) :
    rootDiagUnit τ (∏ j ∈ Finset.range
        (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r),
      Hchar ((w ^ j) • γ) (u ^ S.D.q ^ j)) ∈
      rationalComponent S.ρ S.Γ (rootCharHom b) i := by
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    intro t
    rcases hτ with rfl | rfl <;> cases t <;> decide
  have hSL : SimplyLacedTag τ := by
    rcases hτ with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted hτ'
  obtain ⟨hm0, hs, hmin⟩ := outer_componentOrbitLength_spec S hb i
  set m := componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) with hmdef
  haveI : NeZero m := ⟨hm0.ne'⟩
  obtain ⟨e, hqe⟩ : ∃ e : ℕ, S.D.q = 2 ^ e := by
    obtain ⟨ℓ, e, -, hchar, -, hqe'⟩ := exists_char_pow S
    exact ⟨e, by rw [hqe', CharP.eq L hchar ‹CharP L 2›]⟩
  have hΨ₁ : IsRootComponent (componentRoots (rootCharHom b) i) := isRootComponent_componentRoots i
  have hroot : ∀ δ ∈ componentRoots (rootCharHom b) i, IsRoot τ δ := hΨ₁.isRoot
  have hnegΨ : ∀ δ ∈ componentRoots (rootCharHom b) i, -δ ∈ componentRoots (rootCharHom b) i :=
    hΨ₁.neg_mem
  obtain ⟨a, ha, hna⟩ := hneg
  have haneg : ∀ δ ∈ componentRoots (rootCharHom b) i, a • δ = -δ := fun δ hδ => (hna δ hδ).symm
  have hρ : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → S.ρ δ = w • δ := fun δ hδ =>
    S.rho_eq_smul_of_frob hFr hΦ hn hδ
  have hiter : ∀ δ ∈ componentRoots (rootCharHom b) i, ∀ j : ℕ,
      (S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ = (w ^ j) • δ := by
    intro δ hδ j
    induction j with
    | zero => simp
    | succ j ih =>
      have hrt : IsRoot τ ((S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ) :=
        langRatFC_isRoot_of_mem_rationalRoots S i ⟨j, δ, hδ, rfl⟩
      rw [Function.iterate_succ_apply', hρ _ hrt, ih, pow_succ', mul_smul]
  have hwm : ∀ δ ∈ componentRoots (rootCharHom b) i,
      (w ^ m) • δ ∈ componentRoots (rootCharHom b) i := by
    intro δ hδ
    rw [← hiter δ hδ m]
    exact hs.subset (Set.mem_image_of_mem _ hδ)
  have hwm' : ∀ δ ∈ componentRoots (rootCharHom b) i,
      (w ^ m)⁻¹ • δ ∈ componentRoots (rootCharHom b) i := by
    intro δ hδ
    obtain ⟨δ', hδ', hδδ⟩ := hs.superset hδ
    rw [hiter δ' hδ'] at hδδ
    rw [← hδδ, inv_smul_smul]
    exact hδ'
  have horb : ∀ t : ℕ, (w ^ (m * t)) • γ ∈ componentRoots (rootCharHom b) i := by
    intro t
    induction t with
    | zero => simpa using hγ
    | succ t ih =>
      have h := hwm _ ih
      rwa [← mul_smul, ← pow_add, show m + m * t = m * (t + 1) by ring] at h
  have hg₀mem : canonicalRep (coxeterSystem τ) L a ∈
      rootSpan τ L (componentRoots (rootCharHom b) i) :=
    langRatNO_canonicalRep_mem_rootSpan hroot hnegΨ ha
  have haa : a * a = 1 := by
    refine langRatNO_eq_one_of_fix hroot (mul_mem ha ha) fun δ hδ => ?_
    rw [mul_smul, haneg δ hδ, smul_neg, haneg δ hδ, neg_neg]
  have hg₀sq : canonicalRep (coxeterSystem τ) L a * canonicalRep (coxeterSystem τ) L a = 1 := by
    rw [← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo, haa, canonicalRep_one]
  have hg₀fix : iterHom S.D.step m (canonicalRep (coxeterSystem τ) L a) =
      canonicalRep (coxeterSystem τ) L a := by
    rw [langRatNO_iterHom_canonicalRep S hFr hΦ hn a m,
      langRatNO_conj_eq hroot ha haneg hwm hwm']
  obtain ⟨e', he'⟩ : ∃ e' : ℕ, e = e' + 1 := by
    refine ⟨e - 1, ?_⟩
    have h1 := S.hqpow.1.one_lt
    rw [hqe] at h1
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h] at h1
      simp at h1
    · omega
  obtain ⟨v₀, hv₀, hv₀fix⟩ := langRatFC_exists_unit_root_fixed e hqe u 1 (m * r) hur
  set v : Lˣ := v₀ ^ (2 ^ e') with hvdef
  have hv2 : v * v = u := by
    rw [hvdef, ← pow_add, ← hv₀, pow_one, hqe, he', pow_succ]
    congr 1
    ring
  have hvr : v ^ (S.D.q ^ (m * r)) = v := by
    rw [hvdef, ← pow_mul, mul_comm, pow_mul, hv₀fix]
  set x₀ : ModGL τ L := rootDiagUnit τ (∏ t ∈ Finset.range r,
      Hchar ((w ^ (m * t)) • γ) (v ^ S.D.q ^ (m * t))) with hx₀
  have hx₀mem : x₀ ∈ rootSpan τ L (componentRoots (rootCharHom b) i) :=
    langRatNO_prod_mem_rootSpan hSL hroot hnegΨ (fun t => (w ^ (m * t)) • γ)
      (fun t => v ^ S.D.q ^ (m * t)) r (fun t _ => horb t)
  have hper : ∀ t, (fun t => Hchar ((w ^ (m * t)) • γ) (v ^ S.D.q ^ (m * t))) (t + r) =
      (fun t => Hchar ((w ^ (m * t)) • γ) (v ^ S.D.q ^ (m * t))) t := by
    intro t
    show Hchar ((w ^ (m * (t + r))) • γ) (v ^ S.D.q ^ (m * (t + r))) =
      Hchar ((w ^ (m * t)) • γ) (v ^ S.D.q ^ (m * t))
    rw [mul_add, pow_add, mul_smul, hwr, pow_add, mul_comm (S.D.q ^ (m * t)), pow_mul v, hvr]
  have hx₀fix : iterHom S.D.step m x₀ = x₀ := by
    rw [hx₀, langRatFC_iterHom_step_prod_stride S hFr hΦ hn γ v m r m]
    congr 1
    have h2 := langRatFC_prod_range_shift_period
      (fun t => Hchar ((w ^ (m * t)) • γ) (v ^ S.D.q ^ (m * t))) r hper 1
    refine Eq.trans (Finset.prod_congr rfl fun t _ => ?_) h2
    show Hchar ((w ^ (m + m * t)) • γ) (v ^ S.D.q ^ (m + m * t)) =
      Hchar ((w ^ (m * (t + 1))) • γ) (v ^ S.D.q ^ (m * (t + 1)))
    rw [show m * (t + 1) = m + m * t by ring]
  have hconj : canonicalRep (coxeterSystem τ) L a * x₀ *
      (canonicalRep (coxeterSystem τ) L a)⁻¹ = x₀⁻¹ :=
    langRatNO_conj_inv (a := a) (fun t => (w ^ (m * t)) • γ) (fun t => v ^ S.D.q ^ (m * t)) r
      (fun t _ => haneg _ (horb t))
  have hS0 : (outerOrbitFamily S hb i hs hmin).S 0 =
      rootSpan τ L (componentRoots (rootCharHom b) i) := by
    show rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[(0 : ZMod m).val] ''
      componentRoots (rootCharHom b) i) = _
    rw [ZMod.val_zero]
    simp
  let x : (outerOrbitFamily S hb i hs hmin).S 0 := ⟨x₀, by rw [hS0]; exact hx₀mem⟩
  let g : (outerOrbitFamily S hb i hs hmin).S 0 :=
    ⟨canonicalRep (coxeterSystem τ) L a, by rw [hS0]; exact hg₀mem⟩
  have hkey := langRatNegOne_norm_mem S hτ hqe hAlg hb i hs hmin (P := outerOrbitFamily S hb i hs hmin)
    rfl x g hx₀fix hg₀fix (Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one]; exact hg₀sq))
    (Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
      exact hconj))
  have hc : ∀ j, iterHom S.D.step j (((x * x : (outerOrbitFamily S hb i hs hmin).S 0)) :
      ModGL τ L) = rootDiagUnit τ (∏ t ∈ Finset.range r,
        Hchar ((w ^ (j + m * t)) • γ) (u ^ S.D.q ^ (j + m * t))) := by
    intro j
    rw [Subgroup.coe_mul, map_mul]
    show iterHom S.D.step j x₀ * iterHom S.D.step j x₀ = _
    rw [hx₀, langRatFC_iterHom_step_prod_stride S hFr hΦ hn γ v m r j,
      ← CFSG.LieType.Chevalley.rootDiagUnit_mul, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [Hchar_mul, ← mul_pow, hv2]
  rw [langRatFC_norm_eq_rootDiagUnit_prod S hb i hs hmin (x * x) _ hc] at hkey
  rw [langRatFC_prod_range_mul_regroup (fun k => Hchar ((w ^ k) • γ) (u ^ S.D.q ^ k)) m r]
  exact hkey

theorem langRatNegOne_twistInner_of_rigid
    {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) {t : TauCeti.DynkinType}
    (e : simpleRoots Ψ ≃ Fin t.rank)
    (he' : ∀ β γ : simpleRoots Ψ,
      corootPair (β : Fin τ.rank → ℤ) γ = t.cartanMatrix (e β) (e γ))
    (ht : t ∈ rigidTypes) : twistInner Ψ (fun γ => -γ) := by
  have hok : rigidOK t = true := List.all_eq_true.1 Certificates.certificate13659.1 t ht
  refine langRatCI_twistInner_of_sepB hΨ ?_ ?_ ?_ e he' hok
  · exact ⟨fun γ hγ => hΨ.neg_mem γ hγ, fun γ _ δ _ h => neg_injective h,
      fun γ hγ => ⟨-γ, hΨ.neg_mem γ hγ, neg_neg γ⟩⟩
  · intro γ _ δ _
    show iform (-γ) (-δ) = iform γ δ
    rw [← neg_one_smul ℤ γ, ← neg_one_smul ℤ δ, iform_smul_left, iform_smul_right]
    ring
  · intro γ _
    rfl

theorem langRatNegOne_twistInner_of_type
    {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) {t : TauCeti.DynkinType}
    (e : simpleRoots Ψ ≃ Fin t.rank)
    (he' : ∀ β γ : simpleRoots Ψ,
      corootPair (β : Fin τ.rank → ℤ) γ = t.cartanMatrix (e β) (e γ))
    (ht : t ∈ rigidTypes ∨ t = .D 4 ∨ t = .D 6 ∨ t = .D 8) :
    twistInner Ψ (fun γ => -γ) := by
  rcases ht with ht | rfl | rfl | rfl
  · exact langRatNegOne_twistInner_of_rigid hΨ e he' ht
  · exact langRatNegOne_twistInner_of_cartanD (n := 4) hΨ (Or.inl rfl) e (fun β γ => by
      have h := he' β γ
      rwa [TauCeti.DynkinType.cartanMatrix_D] at h)
  · exact langRatNegOne_twistInner_of_cartanD (n := 6) hΨ (Or.inr (Or.inl rfl)) e (fun β γ => by
      have h := he' β γ
      rwa [TauCeti.DynkinType.cartanMatrix_D] at h)
  · exact langRatNegOne_twistInner_of_cartanD (n := 8) hΨ (Or.inr (Or.inr rfl)) e (fun β γ => by
      have h := he' β γ
      rwa [TauCeti.DynkinType.cartanMatrix_D] at h)

theorem langRatNegOne_localNorm_of_type
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .E7 ∨ τ = .E8) (hAlg : S.IsAlgebraic)
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom b)) {t : TauCeti.DynkinType}
    (e : simpleRoots (componentRoots (rootCharHom b) i) ≃ Fin t.rank)
    (he' : ∀ β γ : simpleRoots (componentRoots (rootCharHom b) i),
      corootPair (β : Fin τ.rank → ℤ) γ = t.cartanMatrix (e β) (e γ))
    (ht : t ∈ rigidTypes ∨ t = .D 4 ∨ t = .D 6 ∨ t = .D 8)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom b) i) (u : Lˣ) (r : ℕ)
    (hwr : (w ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r)) • γ = γ)
    (hur : u ^ (S.D.q ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r)) = u) :
    rootDiagUnit τ (∏ j ∈ Finset.range
        (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r),
      Hchar ((w ^ j) • γ) (u ^ S.D.q ^ j)) ∈
      rationalComponent S.ρ S.Γ (rootCharHom b) i :=
  langRatNegOne_localNorm_of_twistInner S hτ hAlg hn hb i
    (langRatNegOne_twistInner_of_type (isRootComponent_componentRoots i) e he' ht) hγ u r hwr hur

end CFSG.StandardType.LangRat
