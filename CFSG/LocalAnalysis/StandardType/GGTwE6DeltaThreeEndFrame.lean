module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsLangCube
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.NoOffTwE6Three

section Frame


theorem exists_coroot_data (hCore : TwE6RootAs.TwE6CorootCore) {n : ℕ} (hn : 1 ≤ n) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    {Y : Subgroup (MulAut ↥(twistedE6RootGroup K σ))} (hY : IsElemAbelian 3 Y)
    (hYI : Y ≤ (RecipeExcLang.twConj K σ).range) (hYc : Nat.card Y = 3 ^ 6) :
    ∃ τ ∈ Y, τ ≠ 1 ∧ ∃ X D : Subgroup ↥(twistedE6RootGroup K σ), ggFix τ = X ⊔ D ∧
      IsCyclic X ∧ X ≤ Subgroup.centralizer (D : Set ↥(twistedE6RootGroup K σ)) ∧
      CFSG.IsQuasisimple D ∧ 7 ∣ Nat.card D ∧ (2 ^ n) ^ 15 ∣ Nat.card D ∧
      ∀ y ∈ Y, (∀ x ∈ D, y x = x) → ∃ x ∈ X, y = MulAut.conj x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) 2 n
    with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨g, hg, hgn, hYeq⟩ := TwE6DD2.exists_eq_langCube hn hK σ hσ h3 Fr hFr hY hYI hYc
  have hS : Y ≤ TwE6DD2.langCube hn hK σ hσ Fr hFr g := hYeq.le
  have h30 : (3 : AlgebraicClosure K) ≠ 0 := three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  obtain ⟨ζ, hζ, hζo⟩ := TwistedDiag.exists_cube_root (Ω := AlgebraicClosure K) h30
  have hζ1 : ζ ≠ 1 := fun h => by rw [h, orderOf_one] at hζo; omega
  set i0 : Fin TwistTag.E6.tag.rank := ⟨0, by decide⟩ with hi0
  set γ : Fin TwistTag.E6.tag.rank → ℤ := Pi.single i0 1 with hγdef
  have hγ : IsRoot TwistTag.E6.tag γ := isRoot_single TwistTag.E6.tag i0
  set b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ := TwE6RootAs.corootTuple γ ζ with hb
  have hbi : ∀ i, b i = ζ ^ (∑ l, TwistTag.E6.tag.cartan i l * γ l) := fun i => rfl
  have hb3 : ∀ i, b i ^ 3 = 1 := fun i => by
    rw [hbi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow]
  have hb1 : b ≠ 1 := by
    intro h
    have h0 : b i0 = ζ ^ (2 : ℤ) := by
      refine (hbi i0).trans ?_
      rw [Finset.sum_eq_single i0]
      · simp [hγdef, Tag.cartan_self]
      · intro l _ hl
        simp [hγdef, Pi.single_apply, hl]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have h2 : ζ ^ (2 : ℤ) = 1 := h0.symm.trans (congrFun h i0)
    apply hζ1
    calc ζ = ζ ^ 3 * (ζ ^ (2 : ℤ))⁻¹ := by group
      _ = 1 := by rw [h2, hζ]; simp
  have hd : rootDiagUnit Tag.E6 b ∈ (cubeRootTuples (AlgebraicClosure K)).map
      (rootDiagUnitHom Tag.E6 (AlgebraicClosure K)) := TwE6DD2.rootDiagUnit_mem_cubeTorus hb3
  have hx : g * rootDiagUnit Tag.E6 b * g⁻¹ ∈ TwistedDiag.Rgrp (AlgebraicClosure K) Fr :=
    TwE6DD2.conj_cubeTorus_le_Rgrp Fr hFr h3 hg hgn ⟨_, hd, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ↥(RecipeExcLang.twInndiagGroup K σ),
      twInndiagEquivRgrp hn hK σ hσ Fr hFr w = ⟨_, hx⟩ :=
    ⟨(twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm ⟨_, hx⟩, MulEquiv.apply_symm_apply _ _⟩
  have hιw : baseChangeGL (algebraMap K (AlgebraicClosure K)) (w : ModGL TwistTag.E6.tag K) =
      g * rootDiagUnit Tag.E6 b * g⁻¹ :=
    (twInndiagEquivRgrp_apply hn hK σ hσ Fr hFr w).symm.trans (congrArg Subtype.val hw)
  have htI : (w : ModGL TwistTag.E6.tag K) ∈ twistedE6InndiagGL K σ :=
    twInndiagGroup_le_twistedE6InndiagGL σ w.2
  have hτY : RecipeExcLang.twConj K σ w ∈ Y := by
    rw [hYeq]
    refine (TwE6DD2.mem_langCube hn hK σ hσ Fr hFr).2 ⟨b, hb3, hx, ?_⟩
    rw [← rgrpConjAut_apply_baseChange hn hK σ hσ Fr hFr w, hw]
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
    obtain ⟨s, rfl⟩ := hYI hy
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

end CFSG.StandardType.TwE6D3
