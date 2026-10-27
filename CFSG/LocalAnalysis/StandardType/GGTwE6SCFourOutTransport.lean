module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourOutAd
public import CFSG.LieType.Seitz.Defs
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldMark
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverMark

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.NoOffTwE6Three

section Transport

variable {C R : Type} [Group C] [Group R] (ε : C ≃* R)

private theorem congr_symm_apply_symm (b : MulAut R) (m : R) :
    (MulAut.congr ε).symm b (ε.symm m) = ε.symm (b m) := by
  rw [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]

private theorem map_ggFix_symm (b : MulAut R) :
    (ggFix b).map ε.symm.toMonoidHom = ggFix ((MulAut.congr ε).symm b) := by
  ext c
  obtain ⟨m, rfl⟩ := ε.symm.surjective c
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, MulEquiv.apply_symm_apply, mem_ggFix, mem_ggFix,
    congr_symm_apply_symm, ε.symm.injective.eq_iff]

private theorem ggFix_eq_fixedPoints (a : MulAut C) :
    ggFix a = CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers a) := by
  ext c
  rw [mem_ggFix, CFSG.LieType.Seitz.mem_fixedPoints]
  refine ⟨fun hc φ hφ => ?_, fun hc => hc a (Subgroup.mem_zpowers a)⟩
  have hle : Subgroup.zpowers a ≤ MulAction.stabilizer (MulAut C) c :=
    Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hc)
  exact MulAction.mem_stabilizer_iff.1 (hle hφ)

private theorem map_map_symm_eq {A : Subgroup (MulAut R)} {J₁ : Subgroup R}
    (hnorm : ∀ a ∈ A, ∀ m ∈ J₁, a m ∈ J₁) :
    ∀ e ∈ A.map (MulAut.congr ε).symm.toMonoidHom,
      (J₁.map ε.symm.toMonoidHom).map e.toMonoidHom = J₁.map ε.symm.toMonoidHom := by
  rintro _ ⟨a, ha, rfl⟩
  refine le_antisymm ?_ fun c hc => ?_
  · rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨a m, hnorm a ha m hm, (congr_symm_apply_symm ε a m).symm⟩
  · obtain ⟨m, hm, rfl⟩ := hc
    refine ⟨ε.symm (a⁻¹ m), ⟨a⁻¹ m, hnorm _ (inv_mem ha) m hm, rfl⟩, ?_⟩
    change (MulAut.congr ε).symm a (ε.symm (a⁻¹ m)) = ε.symm m
    rw [congr_symm_apply_symm, MulAut.apply_inv_self]

private theorem mem_zpowers_of_fix_map {A : Subgroup (MulAut R)} {J₁ : Subgroup R}
    {a₀ : MulAut R} (hcent : ∀ a ∈ A, (∀ m ∈ J₁, a m = m) → a ∈ Subgroup.zpowers a₀) :
    ∀ e ∈ A.map (MulAut.congr ε).symm.toMonoidHom,
      (∀ c ∈ J₁.map ε.symm.toMonoidHom, e c = c) →
        e ∈ Subgroup.zpowers ((MulAut.congr ε).symm a₀) := by
  rintro _ ⟨a, ha, rfl⟩ hfix
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hcent a ha fun m hm => ε.symm.injective (by
    rw [← congr_symm_apply_symm]
    exact hfix _ ⟨m, hm, rfl⟩))
  exact Subgroup.mem_zpowers_iff.2
    ⟨k, (map_zpow (MulAut.congr ε).symm a₀ k).symm.trans (congrArg _ hk)⟩

end Transport


private theorem twConj_mem_range {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (w : RecipeExcLang.twInndiagGroup K σ) :
    RecipeExcLang.twConj K σ w ∈ (twistedE6InndiagConj K σ).range :=
  ⟨⟨w.1, twInndiagGroup_le_twistedE6InndiagGL σ w.2⟩, MulEquiv.ext fun _ => Subtype.ext rfl⟩

@[expose] def GGTwE6SCFourOutLine : Prop :=
  ∀ n : ℕ, 1 ≤ n → 3 ∣ 2 ^ n + 1 → ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ n) ^ 2 → (∀ c, σ c = c ^ 2 ^ n) →
    ∀ h : twistedE6InndiagGL K σ, h ≠ 1 → h ^ 3 = 1 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)), CFSG.Open.IsElemAbelian 3 E →
      Nat.card E = 3 ^ 4 → twistedE6InndiagConj K σ h ∈ E →
      E ≤ (twistedE6InndiagConj K σ).range →
      ¬ E6AdToral (((E.comap (twistedE6InndiagConj K σ)).map
        (twistedE6InndiagGL K σ).subtype).map
          (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)))) →
      ∀ J : Subgroup (twistedE6RootGroup K σ),
        CFSG.Open.IsComponentOf J
          (CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) →
        (∀ e ∈ E, J.map e.toMonoidHom = J) →
        (∀ e ∈ E, (∀ c ∈ J, e c = c) → e ∈ Subgroup.zpowers (twistedE6InndiagConj K σ h)) →
        LargeEvenMarking ↥J (fun lab' _ _ _ _ _ =>
          lab' = ⟨.D, 4, n⟩ ∨ lab' = ⟨.triD4, 0, n⟩ ∨ lab' = ⟨.A, 2, 3 * n⟩ ∨
            lab' = ⟨.twA, 2, 3 * n⟩) →
        ∃ e ∈ E, GGOutsideInndiag J e

private theorem rgrpModel_le_baseChange {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (A : Subgroup (MulAut (TwE6Delta.RecipeR K n))) :
    rgrpModel hn hK σ hσ Fr hFr ε A ≤
      (((A.map (MulAut.congr ε).symm.toMonoidHom).comap (twistedE6InndiagConj K σ)).map
        (twistedE6InndiagGL K σ).subtype).map
          (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))) := by
  intro x hx
  obtain ⟨hxR, hxA⟩ := (mem_rgrpModel hn hK σ hσ Fr hFr ε).1 hx
  obtain ⟨w, hw⟩ := (twInndiagEquivRgrp hn hK σ hσ Fr hFr).surjective ⟨x, hxR⟩
  have h1 : rgrpRecipeAut hn hK σ hσ Fr hFr ε ⟨x, hxR⟩ =
      MulAut.congr ε (RecipeExcLang.twConj K σ w) := by
    rw [← hw]
    exact congrArg (MulAut.congr ε) (rgrpConjAut_apply_baseChange hn hK σ hσ Fr hFr w)
  refine ⟨w.1, ⟨⟨w.1, twInndiagGroup_le_twistedE6InndiagGL σ w.2⟩, ?_, rfl⟩,
    congrArg Subtype.val hw⟩
  refine ⟨MulAut.congr ε (RecipeExcLang.twConj K σ w), by rw [← h1]; exact hxA, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  exact MulEquiv.ext fun _ => Subtype.ext rfl

theorem ggTwE6SCFourOutAd_of_line (h : GGTwE6SCFourOutLine) : GGTwE6SCFourOutAd := by
  intro n hn K _ _ hK σ hσ Fr hFr ε hε h3 _ _ A a₀ J₁ hset hnt hmark
  obtain ⟨hA, hAI, hcard, ha₀, ha₁, hcomp, hnorm, hcent⟩ := hset
  have hinj : Function.Injective (twistedE6InndiagConj K σ) :=
    twistedE6InndiagConj_injective Nat.prime_two hn hK σ hσ
  have hEI : A.map (MulAut.congr ε).symm.toMonoidHom ≤ (twistedE6InndiagConj K σ).range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨w, hw⟩ := (hε ((MulAut.congr ε).symm a)).1 (by
      rw [MulEquiv.apply_symm_apply]
      exact hAI a ha)
    rw [MulEquiv.coe_toMonoidHom, ← hw]
    exact twConj_mem_range σ w
  obtain ⟨g, hg⟩ := hEI ⟨a₀, ha₀, rfl⟩
  replace hg : twistedE6InndiagConj K σ g = (MulAut.congr ε).symm a₀ := hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply ha₁
    apply (MulAut.congr ε).symm.injective
    rw [← hg, map_one, map_one]
  have hg3 : g ^ 3 = 1 := hinj (by rw [map_pow, hg, ← map_pow, hA.2 a₀ ha₀, map_one, map_one])
  have hJ : CFSG.Open.IsComponentOf (J₁.map ε.symm.toMonoidHom)
      (CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ g))) := by
    rw [hg, ← ggFix_eq_fixedPoints, ← map_ggFix_symm]
    exact isComponentOf_iff_open.1 (isComponentOf_map_mulEquiv ε.symm hcomp)
  have hfE : twistedE6InndiagConj K σ g ∈ A.map (MulAut.congr ε).symm.toMonoidHom := by
    rw [hg]
    exact ⟨a₀, ha₀, rfl⟩
  have hCJ : ∀ e ∈ A.map (MulAut.congr ε).symm.toMonoidHom,
      (∀ c ∈ J₁.map ε.symm.toMonoidHom, e c = c) →
        e ∈ Subgroup.zpowers (twistedE6InndiagConj K σ g) := by
    rw [hg]
    exact mem_zpowers_of_fix_map ε hcent
  obtain ⟨e, ⟨a, ha, rfl⟩, hout⟩ := h n hn h3 K σ hK hσ g hg1 hg3 _
    (TableB.isElemAbelian_map hA _)
    ((Subgroup.card_map_of_injective (MulAut.congr ε).symm.injective).trans hcard) hfE hEI
    (fun htor => hnt (e6AdToral_mono (rgrpModel_le_baseChange hn hK σ hσ Fr hFr ε A) htor))
    _ hJ (map_map_symm_eq ε hnorm) hCJ
    (largeEvenMarking_of_mulEquiv
      (J₁.equivMapOfInjective ε.symm.toMonoidHom ε.symm.injective).symm hmark)
  have hker : ε.symm.toMonoidHom.ker ≤ Subgroup.center (TwE6Delta.RecipeR K n) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 ε.symm.injective]
    exact bot_le
  exact ⟨a, ha, (ggOutsideInndiag_map_iff hker (congr_symm_apply_symm ε a)
    (commutator_eq_self_of_isComponentOf hcomp)).2 hout⟩

end CFSG.StandardType.SCFourCover

end
