module

public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType.TwE6EndNode3

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.TableBExc.E6Three CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three

section Coords


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)

theorem exists_cube_coord (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω}
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω)
    {y : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hy : y ∈ TwE6DD2.langCube hn hK σ hσ Fr hFr g) (hy1 : y ≠ 1) :
    ∃ (ζ : Ωˣ) (hζ : ζ ^ 3 = 1), ζ ≠ 1 ∧ ∃ v : Fin Tag.E6.rank → ZMod 3, v ≠ 0 ∧
      ∃ hd : g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr,
        y = rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have h30 : (3 : Ω) ≠ 0 := three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  obtain ⟨ζ, hζ, hζo⟩ := TwistedDiag.exists_cube_root (Ω := Ω) h30
  obtain ⟨Ψ, -, hΨrange, hΨ⟩ := exists_cubeHom hn hK σ hσ Fr hFr h3 hg hgn hζ hζo
  obtain ⟨x, rfl⟩ := hΨrange y hy
  obtain ⟨hd, hΨx⟩ := hΨ x
  refine ⟨ζ, hζ, fun h => by rw [h, orderOf_one] at hζo; omega, Multiplicative.toAdd x, ?_,
    hd, hΨx⟩
  intro h0
  apply hy1
  have hx : x = 1 := Multiplicative.toAdd.injective (by rw [h0]; rfl)
  rw [hx, map_one]

theorem exists_matrix_of_cube {g : ModGL Tag.E6 Ω} {d : Fin Tag.E6.rank → Ωˣ}
    (hd : g * rootDiagUnit Tag.E6 d * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr) :
    ∃ w : ↥(RecipeExcLang.twInndiagGroup K σ),
      (w : ModGL TwistTag.E6.tag K) ∈ twistedE6InndiagGL K σ ∧
      baseChangeGL (algebraMap K Ω) (w : ModGL TwistTag.E6.tag K) =
        g * rootDiagUnit Tag.E6 d * g⁻¹ ∧
      rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩ = RecipeExcLang.twConj K σ w := by
  obtain ⟨w, hw⟩ : ∃ w : ↥(RecipeExcLang.twInndiagGroup K σ),
      twInndiagEquivRgrp hn hK σ hσ Fr hFr w = ⟨_, hd⟩ :=
    ⟨(twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm ⟨_, hd⟩, MulEquiv.apply_symm_apply _ _⟩
  refine ⟨w, twInndiagGroup_le_twistedE6InndiagGL σ w.2,
    (twInndiagEquivRgrp_apply hn hK σ hσ Fr hFr w).symm.trans (congrArg Subtype.val hw), ?_⟩
  rw [← rgrpConjAut_apply_baseChange hn hK σ hσ Fr hFr w, hw]

end Coords

section Fix


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem ggFix_twConj_eq (w : ↥(RecipeExcLang.twInndiagGroup K σ)) :
    ggFix (RecipeExcLang.twConj K σ w) =
      (Subgroup.centralizer
        ({(w : ModGL TwistTag.E6.tag K)} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
          (twistedE6RootGroup K σ) := by
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

end Fix

end CFSG.StandardType.TwE6EndNode3

end
