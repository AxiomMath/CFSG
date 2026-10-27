module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5LangTor
public import CFSG.LocalAnalysis.StandardType.GGLangRatComp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcSetup
public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreHom
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenPin
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourCore
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidAssembly
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TBlock

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc CFSG.StandardType.LangRat
  TableBExc TableBExcTwo TableBExcTwoFusion

section Defs

variable
  {τ : Tag} {d : ℕ} {K : Type} [Field K] [CharP K 2]
  {ω : (AlgebraicClosure K)ˣ}

structure FrameLang (F : OrthFrame τ d) (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0) {p₀ : ℕ}
    (S : LangSetup τ (AlgebraicClosure K) p₀) : Prop where
  range : (langEmb F hω).range = S.Γ
  torus : ∀ a : Fin τ.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
    rootDiagUnit τ a ∈ S.D.torus
  rho : ∀ γ, IsRoot τ γ → S.ρ γ = -γ
  weyl : ∀ γ, IsRoot τ γ → rootSL2 τ (AlgebraicClosure K) γ WSL ∈ S.Γ

end Defs

section Step

variable
  {τ : Tag} {L : Type} [Field L] [CharP L 2]

theorem conj_pinnedX_charTwo (w : WeylGroup τ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : L) :
    canonicalRep (coxeterSystem τ) L w * pinnedX τ L γ c * (canonicalRep (coxeterSystem τ) L w)⁻¹ =
      pinnedX τ L (w • γ) c := by
  obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hγ
  have hε1 : ε = 1 := by
    have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
    have : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  rw [hεc, hε1, one_mul]

theorem step_pinnedX_one (D : LangDatum τ L) (Fr : L →+* L)
    (hΦ : D.Φ = Units.map (entrywiseHom Fr)) (w : WeylGroup τ)
    (hn : D.n = canonicalRep (coxeterSystem τ) L w) (hw : ∀ v : Fin τ.rank → ℤ, w • v = -v)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    D.step (pinnedX τ L γ 1) = pinnedX τ L (-γ) 1 ∧
      D.step (pinnedX τ L (-γ) 1) = pinnedX τ L γ 1 := by
  have key : ∀ {δ : Fin τ.rank → ℤ}, IsRoot τ δ →
      D.step (pinnedX τ L δ 1) = pinnedX τ L (-δ) 1 := fun {δ} hδ => by
    have h := conj_pinnedX_charTwo (L := L) w hδ 1
    rw [hw] at h
    change D.n * D.Φ (pinnedX τ L δ 1) * D.n⁻¹ = _
    rw [hΦ, units_map_entrywiseHom_pinnedX, map_one, hn]
    exact h
  refine ⟨key hγ, ?_⟩
  have h := key (IsRoot.neg hγ)
  rwa [neg_neg] at h

end Step

section Exists

variable
  {τ : Tag} {d : ℕ} {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem model_le_Γ_of_descent [Finite K] (hK : Nat.card K = 2)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hd : LangDescent (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0) 7
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype)) :
    (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0).model ≤
      (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0).Γ := by
  classical
  set D := LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 with hDdef
  have hD : D.Φ = Units.map (entrywiseHom Fr) := rfl
  have hrange : ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      (adjointGroup τ K).subtype).range =
      (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hfixle : D.fix ≤ ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      (adjointGroup τ K).subtype).range := by
    have hfin := hd.finite_fix
    have h := relIndex_dvd_one_of_card_two (τ := τ) K hK (AlgebraicClosure K) Fr hFr D.fix
      (fun x hx => ((LangDatum.mem_fix D).1 hx).1)
      (fun x hx => by have := ((LangDatum.mem_fix D).1 hx).2; rwa [hD] at this)
    rw [Nat.dvd_one] at h
    rw [hrange]
    exact Subgroup.relIndex_eq_one.1 h
  rw [LangDescent.model_eq, hd.Γ_eq]
  exact Subgroup.map_mono hfixle

theorem exists_frameLang_of_perfect (hτ : (τ = .E7 ∧ d = 6) ∨ (τ = .E8 ∧ d = 7))
    (F : OrthFrame τ d)
    (hw : ∀ v : Fin τ.rank → ℤ, (List.ofFn fun i => rootReflection (F.root i)).prod • v = -v)
    [Finite K] (hK : Nat.card K = 2) (hcomm : commutator ↥(adjointGroup τ K) = ⊤) :
    ∃ (ω : (AlgebraicClosure K)ˣ) (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0)
      (S : LangSetup τ (AlgebraicClosure K) 7), FrameLang F hω S := by
  classical
  obtain ⟨ω, hω⟩ := exists_omega K
  obtain ⟨w, hwn, hg0⟩ := langG_frob F hω hw
  have hg0C : ((langG F hω : adjointGroup τ (AlgebraicClosure K)) : ModGL τ (AlgebraicClosure K))
      ∈ adjointGroup τ (AlgebraicClosure K) := (langG F hω).2
  have hFr : ∀ c, frobK K c = c ^ Nat.card K := frobK_apply_card hK
  obtain ⟨dl, hdl⟩ : ∃ dl : ℕ,
      (τ = .E6 ∧ dl = 3) ∨ (τ = .E7 ∧ dl = 2) ∨ (τ = .E8 ∧ dl = 1) := by
    rcases hτ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨2, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨1, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  obtain ⟨S, hSD, hd⟩ := exists_langSetup_untw_of_datum frobeniusOnRoots_proved dl hdl
    (K := K) (L := AlgebraicClosure K) Nat.prime_seven (by norm_num) (by rw [hK]; norm_num)
    ⟨hcomm⟩ hFr w hg0C hg0
  have hq : S.D.q = 2 := by rw [hSD]; exact hK
  have hΦ : S.D.Φ = Units.map (entrywiseHom (frobK K)) := by rw [hSD]; rfl
  have hn : S.D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w := by rw [hSD]; rfl
  have hg : S.D.g0 =
      ((langG F hω : adjointGroup τ (AlgebraicClosure K)) : ModGL τ (AlgebraicClosure K)) := by
    rw [hSD]; rfl
  have hFr2 : ∀ c, frobK K c = c ^ 2 := frobK_apply
  have hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ := fun γ hγ => by
    rw [S.rho_eq_smul_of_frob (Fr := frobK K) (fun c => by rw [hq]; exact hFr2 c) hΦ hn hγ, hwn]
  refine ⟨ω, hω, S, ?_, fun a ha => ?_, hρ, fun γ hγ => ?_⟩
  · rw [LangSetup.Γ, hd.Γ_eq, hg, langEmb, MonoidHom.range_comp]
  · exact rootDiagUnit_mem_langTorus S (frobK K) hFr2 w hΦ hn hwn ha
  · have hmodel : S.D.model ≤ S.D.Γ := by
      have hd' := hd
      rw [hSD] at hd' ⊢
      exact model_le_Γ_of_descent hK hFr hg0C hg0 hd'
    obtain ⟨h₁, h₂⟩ := step_pinnedX_one S.D (frobK K) hΦ w hn hwn hγ
    exact hmodel (rootSL2_WSL_mem_model S.D hγ h₁ h₂)

end Exists

end CFSG.StandardType.SmallExc

end
