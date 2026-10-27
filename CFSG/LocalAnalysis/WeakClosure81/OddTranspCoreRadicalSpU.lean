module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
import CFSG.OddTranspositions.PartFour.UnitaryClass
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsI
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpSL
import CFSG.RankThree.PartOne.SEITZ2.SUnPlane
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField
import CFSG.LieType.SeitzGeneration.RootPairSL2
import CFSG.OddTranspositions.PartFour.SpPlaneSL2

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreRadical

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open CFSG.LieType.SeitzGeneration CFSG.OddTranspositions.PartFour
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull
open CFSG.RankThree.PartOne.SEITZ2
open scoped Matrix

variable {Y : Type} [Group Y] {t : Y}

theorem radicalOutcome_of_isSymplecticTransvection (hZ : Subgroup.center Y = ⊥) {m n : ℕ}
    (hn : 2 ≤ n) (h : IsSymplecticTransvection Y m n t) : RadicalOutcome Y t := by
  obtain ⟨k, rfl, F, hF, hFfin, hFcard, e, he⟩ := h
  let ψ : Y ≃* Y ⧸ Subgroup.center Y :=
    (QuotientGroup.quotientBot (G := Y)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hψ : ∀ x : Y, ψ x = QuotientGroup.mk x := by intro x; simp [ψ]
  let Φ : Y ≃* ↥(StatedSp k F) := ψ.trans e
  have hΦt : Φ t = e (QuotientGroup.mk t) := by simp [Φ, hψ t]
  let t₀ : ↥(StatedSp k F) := e (QuotientGroup.mk t)
  have ht₀ : IsSymplecticTransvectionIn k t₀ := by simpa [t₀] using he
  obtain ⟨a, c, ha, hc, ht₀eq⟩ := borel86_spn_eq_spTransvection ht₀
  have hbex : ∃ b : Fin k ⊕ Fin k → F, spForm k F a b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (spForm_nondegenerate.1 a hcon)
  obtain ⟨b₀, hb₀⟩ := hbex
  let b : Fin k ⊕ Fin k → F := (spForm k F a b₀)⁻¹ • b₀
  have hab : spForm k F a b = 1 := by
    dsimp [b]
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hb₀]
  have hinj : Function.Injective (RootPair.spSL2Hom hab) :=
    spPlane_spSL2Hom_injective hab
  let Φ₂ : Matrix.SpecialLinearGroup (Fin 2) F →* Y :=
    Φ.symm.toMonoidHom.comp (RootPair.spSL2Hom hab)
  have hΦ₂inj : Function.Injective Φ₂ := Φ.symm.injective.comp hinj
  have hsp : spTransvection a c = RootPair.spSL2Hom hab (u2 (-c)) := by
    rw [RootPair.spSL2Hom_u2]
    simp
  have htmem : t ∈ Φ₂.range := by
    refine ⟨u2 (-c), ?_⟩
    show Φ.symm (RootPair.spSL2Hom hab (u2 (-c))) = t
    rw [← hsp, ← ht₀eq, show t₀ = Φ t from hΦt.symm, Φ.symm_apply_apply]
  have htne : t ≠ 1 := by
    intro ht1
    have h1 : t₀ = 1 := by
      rw [show t₀ = Φ t from hΦt.symm, ht1, map_one]
    have hone : (((1 : ↥(StatedSp k F)) : GL (Fin k ⊕ Fin k) F) :
        Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) - 1 = 0 := by
      ext i j
      simp [Units.val_one]
    have hrank : Matrix.rank (((t₀ : GL (Fin k ⊕ Fin k) F) :
        Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) - 1) = 1 := by
      simpa [IsSymplecticTransvectionIn] using ht₀
    rw [h1, hone, Matrix.rank_zero] at hrank
    omega
  exact RadicalOutcome.of_injective_sl2 (F := F) hFcard (by omega) Φ₂ hΦ₂inj htmem htne

theorem radicalOutcome_of_isUnitaryTransvection (hZ : Subgroup.center Y = ⊥) {m n : ℕ}
    (hn : 2 ≤ n) (h : IsUnitaryTransvection Y m n t) : RadicalOutcome Y t := by
  obtain ⟨K, hKfield, hKfin, hKchar, hKcard, eu, e₀, he₀0, he₀, heu⟩ :=
    exists_mulEquiv_of_isUnitaryTransvection hZ h
  have hK : Nat.card K = (2 ^ n) ^ 2 := hKcard
  obtain ⟨b, hb, hab⟩ :=
    exists_partner (isUnitaryInvolution_unitaryInvolution hK) he₀0 he₀
  let σ := unitaryInvolution K 2 n
  let Φ₀ : Matrix.SpecialLinearGroup (Fin 2) (fixSub σ) →*
      StatedProj (StatedSU m (2 ^ n) K) :=
    (kFactsSuProj hK m).comp (planeSUN (unitaryInvolution_involutive hK) he₀ hb hab)
  let Φ : Matrix.SpecialLinearGroup (Fin 2) (fixSub σ) →* Y :=
    eu.symm.toMonoidHom.comp Φ₀
  have hsu : planeSUN (unitaryInvolution_involutive hK) he₀ hb hab
      (u2 (1 : fixSub σ)) = suTv (isUnitaryInvolution_unitaryInvolution hK) e₀ (1 : K) := by
    refine IsTv.unique (isTv_planeSUN_u2 (unitaryInvolution_involutive hK) he₀ hb hab
      (1 : fixSub σ)) ?_
    exact suTv_smul (isUnitaryInvolution_unitaryInvolution hK) he₀
      (by rw [map_one]; exact CharTwo.add_self_eq_zero 1)
  have hΦu2 : Φ (u2 (1 : fixSub σ)) = t := by
    show eu.symm (kFactsSuProj hK m (planeSUN (unitaryInvolution_involutive hK) he₀ hb hab
      (u2 (1 : fixSub σ)))) = t
    rw [hsu]
    change eu.symm (kFactsSuProjTv hK m e₀ 1) = t
    rw [← heu, eu.symm_apply_apply]
  have hTne : kFactsSuProjTv hK m e₀ 1 ≠ 1 := by
    intro h1
    have h0 : kFactsSuProjTv hK m e₀ 0 = 1 := by
      unfold kFactsSuProjTv
      rw [kFacts_suTv_zero_param hK he₀]
      exact map_one _
    have hEq : kFactsSuProjTv hK m e₀ (1 : K) = kFactsSuProjTv hK m e₀ (0 : K) := by
      rw [h1, h0]
    have h10 : (1 : K) = 0 :=
      kFacts_suProjTv_injective (s := (1 : K)) (s' := (0 : K)) hK he₀0 he₀
        (by rw [map_one]; exact CharTwo.add_self_eq_zero 1) (by simp) hEq
    exact one_ne_zero h10
  have htne : t ≠ 1 := by
    intro ht1
    apply hTne
    rw [← heu, ht1, map_one]
  have hfixcard : Nat.card (fixSub σ) = 2 ^ n := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    simpa [σ, fixSub, CFSG.LieType.Steinberg.fixedSubfield] using
      CFSG.LieType.Steinberg.card_fixedSubfield (F := K) (p := 2) (f := n) hK
  have h4 : 4 ≤ Nat.card (fixSub σ) := by
    rw [hfixcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (fixSub σ)) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K421SpSLProof.isSimpleGroup_sl2_charTwo h4
  have hker : Φ.ker = ⊥ := by
    have hnormal : Φ.ker.Normal := MonoidHom.normal_ker Φ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Φ.ker with hbot | htop
    · exact hbot
    · exfalso
      have hmem : u2 (1 : fixSub σ) ∈ Φ.ker := by
        rw [htop]
        exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hΦu2] at hmem
      exact htne hmem
  have hΦinj : Function.Injective Φ := (MonoidHom.ker_eq_bot_iff Φ).mp hker
  have htmem : t ∈ Φ.range := ⟨u2 (1 : fixSub σ), hΦu2⟩
  exact RadicalOutcome.of_injective_sl2 (F := fixSub σ) hfixcard (by omega) Φ hΦinj htmem htne

end CFSG.LocalAnalysis.WeakClosure81.CoreRadical
