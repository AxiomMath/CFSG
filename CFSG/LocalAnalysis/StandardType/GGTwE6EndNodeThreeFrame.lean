module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsLangCube
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernelCount

public section

namespace CFSG.StandardType.TwE6EndNode3

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.NoOffTwE6Three CFSG.RankThree.Classical2
  CFSG.LieType.Steinberg.Adjoint

section Frame


theorem exists_coroot_data_of_mem (hCore : TwE6RootAs.TwE6CorootCore) {n : ℕ} (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {g : ModGL Tag.E6 (AlgebraicClosure K)} (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K))
    {Y : Subgroup (MulAut ↥(twistedE6RootGroup K σ))} (hY : IsElemAbelian 3 Y)
    (hS : Y ≤ TwE6DD2.langCube hn hK σ hσ Fr hFr g) {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    (hd : g * rootDiagUnit Tag.E6 (TwE6RootAs.corootTuple γ ζ) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    (hτ : rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩ ∈ Y) :
    ∃ τ ∈ Y, τ ≠ 1 ∧ ∃ X D : Subgroup ↥(twistedE6RootGroup K σ), ggFix τ = X ⊔ D ∧
      IsCyclic X ∧ X ≤ Subgroup.centralizer (D : Set ↥(twistedE6RootGroup K σ)) ∧
      CFSG.IsQuasisimple D ∧ 7 ∣ Nat.card D ∧ (2 ^ n) ^ 15 ∣ Nat.card D ∧
      ∀ y ∈ Y, (∀ x ∈ D, y x = x) → ∃ x ∈ X, y = MulAut.conj x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ := TwE6RootAs.corootTuple γ ζ with hb
  have hb1 : b ≠ 1 := by
    intro h
    obtain ⟨j, hj⟩ := CFSG.LieType.Steinberg.Adjoint.iform_self_of_isRoot hγ
    have hγγ : iform γ γ = 2 := by
      rw [hj, show TwistTag.E6.tag.symmetrizer = 1 from rfl, Matrix.one_apply_eq, mul_one]
    have h3' := TwE6RootKill.rootChar_corootTuple γ γ ζ
    rw [← hb, h, hγγ] at h3'
    have h4 : rootChar (1 : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ) γ = 1 := by
      simp [rootChar]
    have h2 : ζ ^ (2 : ℤ) = 1 := h3'.symm.trans h4
    apply hζ1
    calc ζ = ζ ^ 3 * (ζ ^ (2 : ℤ))⁻¹ := by group
      _ = 1 := by rw [h2, hζ]; simp
  obtain ⟨w, hw⟩ : ∃ w : ↥(RecipeExcLang.twInndiagGroup K σ),
      twInndiagEquivRgrp hn hK σ hσ Fr hFr w = ⟨_, hd⟩ :=
    ⟨(twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm ⟨_, hd⟩, MulEquiv.apply_symm_apply _ _⟩
  have hιw : baseChangeGL (algebraMap K (AlgebraicClosure K)) (w : ModGL TwistTag.E6.tag K) =
      g * rootDiagUnit Tag.E6 b * g⁻¹ :=
    (twInndiagEquivRgrp_apply hn hK σ hσ Fr hFr w).symm.trans (congrArg Subtype.val hw)
  have htI : (w : ModGL TwistTag.E6.tag K) ∈ twistedE6InndiagGL K σ :=
    twInndiagGroup_le_twistedE6InndiagGL σ w.2
  have hτY : RecipeExcLang.twConj K σ w ∈ Y := by
    rw [← rgrpConjAut_apply_baseChange hn hK σ hσ Fr hFr w, hw]
    exact hτ
  obtain ⟨X, D, hfix, hXc, -, hXD, hDq, -, h7, h15, hcentr⟩ := hCore K σ (2 ^ n) hK hσ
    (ringChar.eq K 2) 3 Nat.prime_three h3 Fr hFr _
    (TwE6RootAs.langCubeData_v hn hK σ hσ Fr hFr h3 hg hgn hS)
    g hg (TwE6RootAs.langCubeData hn hK σ hσ Fr hFr h3 hg hgn hS).hg0
    (w : ModGL TwistTag.E6.tag K) htI γ hγ ζ hζ hζ1 (by
      rw [hιw]
      change g⁻¹ * (g * rootDiagUnit Tag.E6 b * g⁻¹) * g = rootDiagUnit Tag.E6 b
      group)
  refine ⟨RecipeExcLang.twConj K σ w, hτY, ?_, X, D, ?_, hXc, hXD, hDq, h7, h15, ?_⟩
  ·
    intro h1
    have hw1 : w = 1 := twConj_injective hn hK σ hσ (by rw [h1, map_one])
    have h2 : g * rootDiagUnit Tag.E6 b * g⁻¹ = 1 := by
      rw [← hιw, hw1]
      exact map_one _
    have h3' : rootDiagUnit Tag.E6 b = 1 :=
      mul_left_cancel (a := g) (by rw [mul_one]; exact mul_inv_eq_one.1 h2)
    exact hb1 (CFSG.LieType.Chevalley.rootDiagUnit_injective (h3'.trans rootDiagUnit_one.symm))
  ·
    rw [← hfix]
    ext c
    rw [mem_ggFix, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hc h' hh'
      rw [Set.mem_singleton_iff] at hh'
      subst hh'
      have h := congrArg Subtype.val hc
      change (w : ModGL TwistTag.E6.tag K) * (c : ModGL TwistTag.E6.tag K) *
        (w : ModGL TwistTag.E6.tag K)⁻¹ = c at h
      calc (w : ModGL TwistTag.E6.tag K) * c
          = (w : ModGL TwistTag.E6.tag K) * c * (w : ModGL TwistTag.E6.tag K)⁻¹ * w := by group
        _ = c * w := by rw [h]
    · intro hc
      apply Subtype.ext
      change (w : ModGL TwistTag.E6.tag K) * (c : ModGL TwistTag.E6.tag K) *
        (w : ModGL TwistTag.E6.tag K)⁻¹ = c
      rw [hc _ rfl]
      group
  ·
    intro y hy hyD
    obtain ⟨s, rfl⟩ := TwE6DD2.langCube_le_range hn hK σ hσ Fr hFr g (hS hy)
    have hcomm : (s : ModGL TwistTag.E6.tag K) * w = w * s := by
      have h1 := TableB.IsElemAbelian.comm hY hy hτY
      have h2 : s * w = w * s :=
        twConj_injective hn hK σ hσ (by rw [map_mul, map_mul]; exact h1)
      exact congrArg Subtype.val h2
    have hcommD : ∀ d ∈ D, (s : ModGL TwistTag.E6.tag K) * (d : ModGL TwistTag.E6.tag K) =
        (d : ModGL TwistTag.E6.tag K) * s := by
      intro d hd
      have h := congrArg Subtype.val (hyD d hd)
      change (s : ModGL TwistTag.E6.tag K) * (d : ModGL TwistTag.E6.tag K) *
        (s : ModGL TwistTag.E6.tag K)⁻¹ = d at h
      calc (s : ModGL TwistTag.E6.tag K) * d
          = (s : ModGL TwistTag.E6.tag K) * d * (s : ModGL TwistTag.E6.tag K)⁻¹ * s := by group
        _ = d * s := by rw [h]
    obtain ⟨x, hxX, hxs⟩ := Subgroup.mem_map.1
      (hcentr s (twInndiagGroup_le_twistedE6InndiagGL σ s.2) hcomm hcommD)
    refine ⟨x, hxX, ?_⟩
    have hs : s = ⟨(x : ModGL TwistTag.E6.tag K),
        RecipeExcLang.graphFixedRootGroup_le_twInndiag σ x.2⟩ := Subtype.ext hxs.symm
    rw [hs]
    exact RecipeExcLang.twConj_of_mem_C0 σ x

end Frame

end CFSG.StandardType.TwE6EndNode3

end
