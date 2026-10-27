module

public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeMat
import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernelCount
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Datum
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.TwE6EndNode3

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TwE6RootAs
  CFSG.LieType.Steinberg.Adjoint

section Gen


theorem exists_coroot_data_of_datum (hGen : TwE6CorootCoreGen) {n : ℕ} (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    {Y : Subgroup (MulAut ↥(twistedE6RootGroup K σ))} (hY : IsElemAbelian 3 Y)
    (hYI : Y ≤ (RecipeExcLang.twConj K σ).range)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (D : TwLangData K σ (2 ^ n) A)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) {x : ModGL TwistTag.E6.tag K}
    (hxA : x ∈ twMatPre K σ Y)
    (hx : rootDiagUnit TwistTag.E6.tag (corootTuple γ ζ) =
      D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * D.g0) :
    ∃ τ ∈ Y, τ ≠ 1 ∧ ∃ X D' : Subgroup ↥(twistedE6RootGroup K σ), ggFix τ = X ⊔ D' ∧
      IsCyclic X ∧ X ≤ Subgroup.centralizer (D' : Set ↥(twistedE6RootGroup K σ)) ∧
      CFSG.IsQuasisimple D' ∧ 7 ∣ Nat.card D' ∧
      ∀ y ∈ Y, (∀ d ∈ D', y d = d) → ∃ d ∈ X, y = MulAut.conj d := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have hb1 : corootTuple γ ζ ≠ 1 := by
    intro h
    obtain ⟨j, hj⟩ := CFSG.LieType.Steinberg.Adjoint.iform_self_of_isRoot hγ
    have hγγ : iform γ γ = 2 := by
      rw [hj, show TwistTag.E6.tag.symmetrizer = 1 from rfl, Matrix.one_apply_eq, mul_one]
    have h3' := TwE6RootKill.rootChar_corootTuple γ γ ζ
    rw [h, hγγ] at h3'
    have h4 : rootChar (1 : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ) γ = 1 := by
      simp [rootChar]
    have h2 : ζ ^ (2 : ℤ) = 1 := h3'.symm.trans h4
    apply hζ1
    calc ζ = ζ ^ 3 * (ζ ^ (2 : ℤ))⁻¹ := by group
      _ = 1 := by rw [h2, hζ]; simp
  obtain ⟨w, hwY, rfl⟩ := hxA
  have htI : (w : ModGL TwistTag.E6.tag K) ∈ twistedE6InndiagGL K σ :=
    NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ w.2
  obtain ⟨X, D', hfix, hXc, -, hXD, hDq, -, h7, -, hcentr⟩ := hGen K σ (2 ^ n) hK hσ
    (ringChar.eq K 2) 3 Nat.prime_three h3 D.Fr D.hFr D.v D.g0 D.hg0C D.hg0 _ htI γ hγ ζ hζ hζ1
    hx.symm
  refine ⟨RecipeExcLang.twConj K σ w, hwY, ?_, X, D', ?_, hXc, hXD, hDq, h7, ?_⟩
  ·
    intro h1
    have hw1 : w = 1 := NoOffTwE6Three.twConj_injective hn hK σ hσ (by rw [h1, map_one])
    have h2 : rootDiagUnit TwistTag.E6.tag (corootTuple γ ζ) = 1 := by
      rw [hx, hw1]
      simp
    exact hb1 (CFSG.LieType.Chevalley.rootDiagUnit_injective (h2.trans rootDiagUnit_one.symm))
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
      have h1 := CFSG.Open.IsElemAbelian.comm hY hy hwY
      have h2 : s * w = w * s :=
        NoOffTwE6Three.twConj_injective hn hK σ hσ (by rw [map_mul, map_mul]; exact h1)
      exact congrArg Subtype.val h2
    have hcommD : ∀ d ∈ D', (s : ModGL TwistTag.E6.tag K) * (d : ModGL TwistTag.E6.tag K) =
        (d : ModGL TwistTag.E6.tag K) * s := by
      intro d hd
      have h := congrArg Subtype.val (hyD d hd)
      change (s : ModGL TwistTag.E6.tag K) * (d : ModGL TwistTag.E6.tag K) *
        (s : ModGL TwistTag.E6.tag K)⁻¹ = d at h
      calc (s : ModGL TwistTag.E6.tag K) * d
          = (s : ModGL TwistTag.E6.tag K) * d * (s : ModGL TwistTag.E6.tag K)⁻¹ * s := by group
        _ = d * s := by rw [h]
    obtain ⟨x, hxX, hxs⟩ := Subgroup.mem_map.1
      (hcentr s (NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ s.2) hcomm hcommD)
    refine ⟨x, hxX, ?_⟩
    have hs : s = ⟨(x : ModGL TwistTag.E6.tag K),
        RecipeExcLang.graphFixedRootGroup_le_twInndiag σ x.2⟩ := Subtype.ext hxs.symm
    rw [hs]
    exact RecipeExcLang.twConj_of_mem_C0 σ x

end Gen

end CFSG.StandardType.TwE6EndNode3

end
