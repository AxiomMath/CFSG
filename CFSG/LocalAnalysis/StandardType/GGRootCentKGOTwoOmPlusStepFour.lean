module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialitySpin
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusLevi
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaFrame
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAutUBasic
import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityModel
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmModel
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmHyp
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmFour
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthModel
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Card

public section

namespace CFSG.StandardType.KGOm

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  CFSG.StandardType.RootCentOmega CFSG.StandardType.RCSTOm CFSG.LieType.Universal.Spin
open CFSG.StandardType.Triality

@[expose] noncomputable def plusLeviFour (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup (Triality.Sp8 K) :=
  (leviFix (elementaryGroup (quadPlus 4 K))
      (framePair (plusFrame 4 K Triality.three_le_four) ⟨2, by omega⟩ true)
      (smulPair (framePair (plusFrame 4 K Triality.three_le_four) ⟨1, by omega⟩ true)
        one_ne_zero)).comap (spinAction (quadPlus 4 K)) ⊔
    ((leviFix (elementaryGroup (quadPlus 4 K))
        (framePair (plusFrame 4 K Triality.three_le_four) ⟨3, by omega⟩ true)
        (framePair (plusFrame 4 K Triality.three_le_four) ⟨0, by omega⟩ true)).comap
          (spinAction (quadPlus 4 K)) ⊔
      (leviFix (elementaryGroup (quadPlus 4 K))
        (framePair (plusFrame 4 K Triality.three_le_four) ⟨3, by omega⟩ true)
        (flipPair (framePair (plusFrame 4 K Triality.three_le_four) ⟨0, by omega⟩ true))).comap
          (spinAction (quadPlus 4 K)))

theorem c_longRoot_highest_of_tri {K : Type} [Field K] [Finite K] [CharP K 2]
    {c : Triality.Sp8 K →* Triality.Sp8 K} {k : ℕ} {ε : Bool} {τ : K ≃+* K}
    (hcA : ∀ δ ∈ Triality.rootsD4, ∀ b : K,
      c (Triality.xr δ b) =
        Triality.xr ((⇑Triality.tri)^[k] (if ε then Triality.refl0 δ else δ)) (τ b)) :
    c ((plusFrame 4 K Triality.three_le_four).longRoot (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩)
      (by simp) true true (.ofAdd 1)) =
      (plusFrame 4 K Triality.three_le_four).longRoot (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩)
        (by simp) true true (.ofAdd 1) := by
  have hγ : (![0, 1, 1, 1] : Fin 4 → ℤ) ∈ Triality.rootsD4 :=
    Triality.mem_rootsD4_iff.2 ⟨1, 2, by decide, true, true, by decide⟩
  have hfix : (⇑Triality.tri) (![0, 1, 1, 1] : Fin 4 → ℤ) = ![0, 1, 1, 1] := by decide
  have hiter : ∀ n : ℕ, (⇑Triality.tri)^[n] (![0, 1, 1, 1] : Fin 4 → ℤ) = ![0, 1, 1, 1] := by
    intro n
    induction n with
    | zero => rw [Function.iterate_zero, id_eq]
    | succ n ih => rw [Function.iterate_succ_apply', ih, hfix]
  have hrefl : Triality.refl0 (![0, 1, 1, 1] : Fin 4 → ℤ) = ![0, 1, 1, 1] := by decide
  have hphi : (⇑Triality.tri)^[k]
      (if ε then Triality.refl0 (![0, 1, 1, 1] : Fin 4 → ℤ) else ![0, 1, 1, 1]) =
      ![0, 1, 1, 1] := by
    cases ε with
    | false => simpa using hiter k
    | true => rw [if_pos rfl, hrefl]; exact hiter k
  have hxr : Triality.xr (![0, 1, 1, 1] : Fin 4 → ℤ) (1 : K) =
      (plusFrame 4 K Triality.three_le_four).longRoot (i := ⟨1, by omega⟩)
        (j := ⟨2, by omega⟩) (by simp) true true (.ofAdd 1) :=
    Triality.xr_eq_longRoot (γ := ![0, 1, 1, 1]) (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩)
      (s := true) (t := true) (by simp) (by decide) 1
  have h := hcA (![0, 1, 1, 1] : Fin 4 → ℤ) hγ 1
  rw [hphi, map_one, hxr] at h
  exact h

theorem eq_self_of_plusLeviFour_conj {K : Type} [Field K] [Finite K] [CharP K 2]
    {c : Triality.Sp8 K →* Triality.Sp8 K} {k : ℕ} {ε : Bool} {τ : K ≃+* K}
    (hcA : ∀ δ ∈ Triality.rootsD4, ∀ b : K,
      c (Triality.xr δ b) =
        Triality.xr ((⇑Triality.tri)^[k] (if ε then Triality.refl0 δ else δ)) (τ b))
    {h : Triality.Sp8 K} (hh : h ∈ plusLeviFour K)
    (hkey : ∀ z ∈ plusLeviFour K, c z ∈ plusLeviFour K → h * c z * h⁻¹ = z) :
    ∀ z, c z = z := by
  classical
  let F : HypFrame (quadPlus 4 K) 4 := plusFrame 4 K Triality.three_le_four
  let Q : QuadraticForm K (Fin 4 ⊕ Fin 4 → K) := quadPlus 4 K
  let H : Subgroup ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := elementaryGroup Q
  let σ : Triality.Sp8 K →* ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := spinAction Q
  have hE : ∀ u w : Fin 4 ⊕ Fin 4 → K, eichler Q u w ∈ H :=
    fun u w => eichler_mem_elementaryGroup Q u w
  have hσinj : Function.Injective σ := RootCentOmega.spinAction_quadPlus_injective
  let P1 : HypPair Q := framePair F (2 : Fin 4) true
  let P2 : HypPair Q := smulPair (framePair F (1 : Fin 4) true) (one_ne_zero : (1 : K) ≠ 0)
  let P3 : HypPair Q := framePair F (3 : Fin 4) true
  let P4 : HypPair Q := framePair F (0 : Fin 4) true
  let P5 : HypPair Q := flipPair P4
  let LA : Subgroup (Triality.Sp8 K) := (leviFix H P1 P2).comap σ
  let LC : Subgroup (Triality.Sp8 K) := (leviFix H P3 P4).comap σ
  let LD : Subgroup (Triality.Sp8 K) := (leviFix H P3 P5).comap σ
  have hplus : plusLeviFour K = LA ⊔ (LC ⊔ LD) := rfl
  have hLA : LA ≤ plusLeviFour K := by rw [hplus]; exact le_sup_left
  have hLC : LC ≤ plusLeviFour K := by
    rw [hplus]; exact (le_sup_left : LC ≤ LC ⊔ LD).trans le_sup_right
  have hLD : LD ≤ plusLeviFour K := by
    rw [hplus]; exact (le_sup_right : LD ≤ LC ⊔ LD).trans le_sup_right
  have h12A : P1.Orth P2 := orth₁₂ F (by decide) true true (one_ne_zero : (1 : K) ≠ 0)
  have h12C : P3.Orth P4 := orth₁₃ F (by decide) true true
  have h12D : P3.Orth P5 := by
    have h' : P3.Orth P4 := h12C
    exact ⟨h'.ef, h'.ee, h'.ff, h'.fe⟩
  have hP1P3 : P1.Orth P3 := orth₁₃ F (by decide) true true
  have hP1P4 : P1.Orth P4 := orth₁₃ F (by decide) true true
  have hP2P3 : P2.Orth P3 := orth₂₃ F (by decide) true true (one_ne_zero : (1 : K) ≠ 0)
  have hP2P4 : P2.Orth P4 := orth₂₃ F (by decide) true true (one_ne_zero : (1 : K) ≠ 0)
  have hP1P5 : P1.Orth P5 := by
    have h' : P1.Orth P4 := hP1P4
    exact ⟨h'.ef, h'.ee, h'.ff, h'.fe⟩
  have hP2P5 : P2.Orth P5 := by
    have h' : P2.Orth P4 := hP2P4
    exact ⟨h'.ef, h'.ee, h'.ff, h'.fe⟩
  have hpull : ∀ (X Y : Subgroup ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))),
      X ≤ Subgroup.centralizer (Y : Set _) →
      X.comap σ ≤ Subgroup.centralizer (Y.comap σ : Set (Triality.Sp8 K)) := by
    intro X Y hXY x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hσinj (by
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp (hXY (Subgroup.mem_comap.mp hx)) (σ y)
        (Subgroup.mem_comap.mp hy))
  have hcommAC : LA ≤ Subgroup.centralizer (LC : Set (Triality.Sp8 K)) :=
    hpull (leviFix H P1 P2) (leviFix H P3 P4)
      (leviFix_le_centralizer_of_orth h12A hP1P3 hP1P4 hP2P3 hP2P4 H H)
  have hcommAD : LA ≤ Subgroup.centralizer (LD : Set (Triality.Sp8 K)) :=
    hpull (leviFix H P1 P2) (leviFix H P3 P5)
      (leviFix_le_centralizer_of_orth h12A hP1P3 hP1P5 hP2P3 hP2P5 H H)
  have hcommCD : LC ≤ Subgroup.centralizer (LD : Set (Triality.Sp8 K)) :=
    hpull (leviFix H P3 P4) (leviFix H P3 P5) (leviFix_le_centralizer_flip h12C hE hE)
  have hnormA : plusLeviFour K ≤ Subgroup.normalizer (LA : Set (Triality.Sp8 K)) := by
    rw [hplus]
    refine sup_le Subgroup.le_normalizer (sup_le ?_ ?_)
    · exact (Subgroup.le_centralizer_iff.mp hcommAC).trans (Subgroup.centralizer_le_normalizer _)
    · exact (Subgroup.le_centralizer_iff.mp hcommAD).trans (Subgroup.centralizer_le_normalizer _)
  have hnormC : plusLeviFour K ≤ Subgroup.normalizer (LC : Set (Triality.Sp8 K)) := by
    rw [hplus]
    refine sup_le ?_ (sup_le Subgroup.le_normalizer ?_)
    · exact hcommAC.trans (Subgroup.centralizer_le_normalizer _)
    · exact (Subgroup.le_centralizer_iff.mp hcommCD).trans
        (Subgroup.centralizer_le_normalizer _)
  have hnormD : plusLeviFour K ≤ Subgroup.normalizer (LD : Set (Triality.Sp8 K)) := by
    rw [hplus]
    refine sup_le ?_ (sup_le ?_ Subgroup.le_normalizer)
    · exact hcommAD.trans (Subgroup.centralizer_le_normalizer _)
    · exact hcommCD.trans (Subgroup.centralizer_le_normalizer _)
  have hconjA : ∀ y ∈ LA, h * y * h⁻¹ ∈ LA := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hnormA hh) y).mp hy
  have hconjC : ∀ y ∈ LC, h * y * h⁻¹ ∈ LC := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hnormC hh) y).mp hy
  have hconjD : ∀ y ∈ LD, h * y * h⁻¹ ∈ LD := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hnormD hh) y).mp hy
  have hdisjAC : Disjoint LA LC := by
    rw [Subgroup.disjoint_def]
    intro x hxA hxC
    have hxL : σ x ∈ leviFix H P1 P2 := hxA
    have hxO : σ x ∈ omFix Q P1 P2 := leviFix_le_omFix hP1P3 hP1P4 hP2P3 hP2P4 hxC
    have hmem : σ x ∈ leviFix H P1 P2 ⊓ omFix Q P1 P2 := ⟨hxL, hxO⟩
    rw [disjoint_iff.mp (disjoint_leviFix_omFix h12A), Subgroup.mem_bot] at hmem
    exact hσinj (by rw [hmem, map_one])
  have hdisjAD : Disjoint LA LD := by
    rw [Subgroup.disjoint_def]
    intro x hxA hxD
    have hxL : σ x ∈ leviFix H P1 P2 := hxA
    have hxO : σ x ∈ omFix Q P1 P2 := leviFix_le_omFix hP1P3 hP1P5 hP2P3 hP2P5 hxD
    have hmem : σ x ∈ leviFix H P1 P2 ⊓ omFix Q P1 P2 := ⟨hxL, hxO⟩
    rw [disjoint_iff.mp (disjoint_leviFix_omFix h12A), Subgroup.mem_bot] at hmem
    exact hσinj (by rw [hmem, map_one])
  have hdisjCD : Disjoint LC LD := by
    rw [Subgroup.disjoint_def]
    intro x hxC hxD
    have hmem : σ x ∈ leviFix H P3 P4 ⊓ leviFix H P3 (flipPair P4) := ⟨hxC, hxD⟩
    rw [leviFix_inf_flip_eq_bot h12C, Subgroup.mem_bot] at hmem
    exact hσinj (by rw [hmem, map_one])
  have hσA : ∀ b : K, σ (Triality.xr Triality.rootA b) =
      eichler Q (F.vec (1 : Fin 4) true) (b • F.vec (2 : Fin 4) false) := by
    intro b
    rw [Triality.xr_eq_longRoot (γ := Triality.rootA) (i := (1 : Fin 4)) (j := (2 : Fin 4))
      (s := true) (t := false) (by decide) Triality.toStdD_rootA b]
    rw [HypFrame.longRoot_swap (F := F) (i := (1 : Fin 4)) (j := (2 : Fin 4))
      (hij := by decide) (s := true) (t := false) b]
    rw [RootCentOmega.spinAction_longRoot_eq_eichler (F := F) (i := (2 : Fin 4))
      (j := (1 : Fin 4)) (hij := by decide) (s := false) (t := true) (-b)]
    rw [CharTwo.neg_eq]
  have hσC : ∀ b : K, σ (Triality.xr Triality.rootC b) =
      eichler Q (F.vec (3 : Fin 4) true) (b • F.vec (0 : Fin 4) false) := by
    intro b
    rw [Triality.xr_eq_longRoot (γ := Triality.rootC) (i := (0 : Fin 4)) (j := (3 : Fin 4))
      (s := false) (t := true) (by decide) Triality.toStdD_rootC b]
    exact RootCentOmega.spinAction_longRoot_eq_eichler F (i := (0 : Fin 4))
      (j := (3 : Fin 4)) (s := false) (t := true) (by decide) b
  have hσD : ∀ b : K, σ (Triality.xr Triality.rootD b) =
      eichler Q (F.vec (3 : Fin 4) true) (b • F.vec (0 : Fin 4) true) := by
    intro b
    rw [Triality.xr_eq_longRoot (γ := Triality.rootD) (i := (0 : Fin 4)) (j := (3 : Fin 4))
      (s := true) (t := true) (by decide) Triality.toStdD_rootD b]
    exact RootCentOmega.spinAction_longRoot_eq_eichler F (i := (0 : Fin 4))
      (j := (3 : Fin 4)) (s := true) (t := true) (by decide) b
  have hAx : ∀ b : K, Triality.xr Triality.rootA b ∈ LA := by
    intro b
    show Triality.xr Triality.rootA b ∈ (leviFix H P1 P2).comap σ
    rw [Subgroup.mem_comap, hσA b]
    have hmem := (eichler_mem_leviFix h12A hE b).2
    rw [show P2.e = (1 : K) • F.vec (1 : Fin 4) true from rfl,
      show P1.f = F.vec (2 : Fin 4) false from rfl, eichler_smul_left, one_smul] at hmem
    exact hmem
  have hCx : ∀ b : K, Triality.xr Triality.rootC b ∈ LC := by
    intro b
    show Triality.xr Triality.rootC b ∈ (leviFix H P3 P4).comap σ
    rw [Subgroup.mem_comap, hσC b]
    exact (eichler_mem_leviFix h12C hE b).1
  have hDx : ∀ b : K, Triality.xr Triality.rootD b ∈ LD := by
    intro b
    show Triality.xr Triality.rootD b ∈ (leviFix H P3 P5).comap σ
    rw [Subgroup.mem_comap, hσD b]
    exact (eichler_mem_leviFix h12D hE b).1
  have hiter : (⇑Triality.tri)^[k] = (⇑Triality.tri)^[k % 3] := by
    have h3 : (⇑Triality.tri)^[3] = id := funext Triality.tri_tri_tri
    have h3m : (⇑Triality.tri)^[3 * (k / 3)] = id := by
      rw [Function.iterate_mul, h3, Function.iterate_id]
    conv_lhs => rw [show k = 3 * (k / 3) + k % 3 from (Nat.div_add_mod k 3).symm]
    rw [Function.iterate_add, h3m, Function.id_comp]
  have hneOf : ∀ (δ : Fin 4 → ℤ) (i j : Fin 4) (hij : i ≠ j) (s t : Bool),
      toStdD 4 δ = Triality.lv i j s t → Triality.xr δ (1 : K) ≠ 1 := by
    intro δ i j hij s t hδ h1
    have hx := Triality.xr_eq_longRoot (γ := δ) (i := i) (j := j) (s := s) (t := t) hij hδ
      (1 : K)
    have h0 : F.longRoot hij s t (Multiplicative.ofAdd (0 : K)) = 1 :=
      map_one (F.longRoot hij s t)
    have hinj : Function.Injective ⇑(F.longRoot hij s t) := F.longRoot_injective hij s t
    exact one_ne_zero (Multiplicative.ofAdd.injective (hinj (hx.symm.trans h1 |>.trans h0.symm)))
  have hneC : Triality.xr Triality.rootC (1 : K) ≠ 1 :=
    hneOf Triality.rootC (0 : Fin 4) (3 : Fin 4) (by decide) false true Triality.toStdD_rootC
  have hneD : Triality.xr Triality.rootD (1 : K) ≠ 1 :=
    hneOf Triality.rootD (0 : Fin 4) (3 : Fin 4) (by decide) true true Triality.toStdD_rootD
  have hkeyC : (⇑Triality.tri)^[k] (if ε then Triality.refl0 Triality.rootC else Triality.rootC)
      = Triality.rootC := by
    set δ' := (⇑Triality.tri)^[k] (if ε then Triality.refl0 Triality.rootC else Triality.rootC)
      with hδ'def
    have hδ'h : δ' = Triality.rootA ∨ δ' = Triality.rootC ∨ δ' = Triality.rootD := by
      rw [hδ'def, hiter]
      have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hk with h0 | h1 | h2
      · rw [h0]; cases ε <;> decide
      · rw [h1]; cases ε <;> decide
      · rw [h2]; cases ε <;> decide
    have hδ'mem : ∀ b : K, Triality.xr δ' b ∈ plusLeviFour K := by
      intro b
      rcases hδ'h with h' | h' | h'
      · rw [h']; exact hLA (hAx b)
      · rw [h']; exact hLC (hCx b)
      · rw [h']; exact hLD (hDx b)
    have hcz : c (Triality.xr Triality.rootC 1) = Triality.xr δ' 1 := by
      simpa [← hδ'def] using hcA Triality.rootC Triality.rootC_mem 1
    have hkey1 : h * Triality.xr δ' 1 * h⁻¹ = Triality.xr Triality.rootC 1 := by
      have hP : c (Triality.xr Triality.rootC 1) ∈ plusLeviFour K := by
        rw [hcz]; exact hδ'mem 1
      have hthis := hkey (Triality.xr Triality.rootC 1) (hLC (hCx 1)) hP
      rwa [hcz] at hthis
    rcases hδ'h with h' | h' | h'
    · rw [h'] at hkey1
      have hmem : Triality.xr Triality.rootC 1 ∈ LA := by
        rw [← hkey1]; exact hconjA _ (hAx 1)
      have hbot : LA ⊓ LC = ⊥ := disjoint_iff.mp hdisjAC
      have hmem' : Triality.xr Triality.rootC 1 ∈ (⊥ : Subgroup (Triality.Sp8 K)) := by
        rw [← hbot]; exact ⟨hmem, hCx 1⟩
      exact absurd (Subgroup.mem_bot.mp hmem') hneC
    · exact h'
    · rw [h'] at hkey1
      have hmem : Triality.xr Triality.rootC 1 ∈ LD := by
        rw [← hkey1]; exact hconjD _ (hDx 1)
      have hbot : LC ⊓ LD = ⊥ := disjoint_iff.mp hdisjCD
      have hmem' : Triality.xr Triality.rootC 1 ∈ (⊥ : Subgroup (Triality.Sp8 K)) := by
        rw [← hbot]; exact ⟨hCx 1, hmem⟩
      exact absurd (Subgroup.mem_bot.mp hmem') hneC
  have hkeyD : (⇑Triality.tri)^[k] (if ε then Triality.refl0 Triality.rootD else Triality.rootD)
      = Triality.rootD := by
    set δ' := (⇑Triality.tri)^[k] (if ε then Triality.refl0 Triality.rootD else Triality.rootD)
      with hδ'def
    have hδ'h : δ' = Triality.rootA ∨ δ' = Triality.rootC ∨ δ' = Triality.rootD := by
      rw [hδ'def, hiter]
      have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hk with h0 | h1 | h2
      · rw [h0]; cases ε <;> decide
      · rw [h1]; cases ε <;> decide
      · rw [h2]; cases ε <;> decide
    have hδ'mem : ∀ b : K, Triality.xr δ' b ∈ plusLeviFour K := by
      intro b
      rcases hδ'h with h' | h' | h'
      · rw [h']; exact hLA (hAx b)
      · rw [h']; exact hLC (hCx b)
      · rw [h']; exact hLD (hDx b)
    have hcz : c (Triality.xr Triality.rootD 1) = Triality.xr δ' 1 := by
      simpa [← hδ'def] using hcA Triality.rootD Triality.rootD_mem 1
    have hkey1 : h * Triality.xr δ' 1 * h⁻¹ = Triality.xr Triality.rootD 1 := by
      have hP : c (Triality.xr Triality.rootD 1) ∈ plusLeviFour K := by
        rw [hcz]; exact hδ'mem 1
      have hthis := hkey (Triality.xr Triality.rootD 1) (hLD (hDx 1)) hP
      rwa [hcz] at hthis
    rcases hδ'h with h' | h' | h'
    · rw [h'] at hkey1
      have hmem : Triality.xr Triality.rootD 1 ∈ LA := by
        rw [← hkey1]; exact hconjA _ (hAx 1)
      have hbot : LA ⊓ LD = ⊥ := disjoint_iff.mp hdisjAD
      have hmem' : Triality.xr Triality.rootD 1 ∈ (⊥ : Subgroup (Triality.Sp8 K)) := by
        rw [← hbot]; exact ⟨hmem, hDx 1⟩
      exact absurd (Subgroup.mem_bot.mp hmem') hneD
    · rw [h'] at hkey1
      have hmem : Triality.xr Triality.rootD 1 ∈ LC := by
        rw [← hkey1]; exact hconjC _ (hCx 1)
      have hbot : LC ⊓ LD = ⊥ := disjoint_iff.mp hdisjCD
      have hmem' : Triality.xr Triality.rootD 1 ∈ (⊥ : Subgroup (Triality.Sp8 K)) := by
        rw [← hbot]; exact ⟨hmem, hDx 1⟩
      exact absurd (Subgroup.mem_bot.mp hmem') hneD
    · exact h'
  have hkε : k % 3 = 0 ∧ ε = false := by
    rw [hiter] at hkeyC hkeyD
    have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk with h0 | h1 | h2
    · cases ε with
      | false => exact ⟨h0, rfl⟩
      | true => rw [h0] at hkeyC; exact absurd hkeyC (by decide)
    · cases ε with
      | false => rw [h1] at hkeyC; exact absurd hkeyC (by decide)
      | true => rw [h1] at hkeyC; exact absurd hkeyC (by decide)
    · cases ε with
      | false => rw [h2] at hkeyC; exact absurd hkeyC (by decide)
      | true => rw [h2] at hkeyD; exact absurd hkeyD (by decide)
  have htri_id : (⇑Triality.tri)^[k] = id := by
    rw [hiter, hkε.1, Function.iterate_zero]
  have hc_root : ∀ δ ∈ Triality.rootsD4, ∀ b : K,
      c (Triality.xr δ b) = Triality.xr δ (τ b) := by
    intro δ hδ b
    simpa [htri_id, hkε.2] using hcA δ hδ b
  set u : Fin 4 ⊕ Fin 4 → K := F.vec (3 : Fin 4) true with hu
  set w : Fin 4 ⊕ Fin 4 → K := F.vec (0 : Fin 4) false with hw
  have hQu : Q u = 0 := by rw [hu]; exact F.map_vec _ _
  have hQw : Q w = 0 := by rw [hw]; exact F.map_vec _ _
  have huw : polar Q u w = 0 := by
    rw [hu, hw]; exact F.polar_vec_of_ne (by decide) true false
  have hwne : w ≠ 0 := by
    rw [hw]; exact HypPair.f_ne_zero (framePair F (0 : Fin 4) true)
  have hσz : ∀ b : K, σ (Triality.xr Triality.rootC b) = eichler Q u (b • w) := by
    intro b
    rw [hu, hw]
    exact hσC b
  have hσH : σ h ∈ H := by
    have hle : plusLeviFour K ≤ H.comap σ := by
      rw [hplus]
      refine sup_le ?_ (sup_le ?_ ?_)
      · intro x hx
        exact Subgroup.mem_comap.mpr (mem_leviFix.mp (Subgroup.mem_comap.mp hx)).1
      · intro x hx
        exact Subgroup.mem_comap.mpr (mem_leviFix.mp (Subgroup.mem_comap.mp hx)).1
      · intro x hx
        exact Subgroup.mem_comap.mpr (mem_leviFix.mp (Subgroup.mem_comap.mp hx)).1
    exact hle hh
  have hTO : σ h ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q hσH
  have hUO : (σ h)⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem hTO
  have hmain : ∀ b : K, eichler Q u ((τ b) • w) =
      eichler Q ((σ h)⁻¹ u) (b • ((σ h)⁻¹ w)) := by
    intro b
    have hE1 : σ (c (Triality.xr Triality.rootC b)) =
        (σ h)⁻¹ * σ (Triality.xr Triality.rootC b) * σ h := by
      have hP : c (Triality.xr Triality.rootC b) ∈ plusLeviFour K := by
        rw [hc_root Triality.rootC Triality.rootC_mem b]
        exact hLC (hCx (τ b))
      have hthis := hkey (Triality.xr Triality.rootC b) (hLC (hCx b)) hP
      have h2 : c (Triality.xr Triality.rootC b) =
          h⁻¹ * Triality.xr Triality.rootC b * h := by
        calc c (Triality.xr Triality.rootC b)
            = h⁻¹ * (h * c (Triality.xr Triality.rootC b) * h⁻¹) * h := by group
          _ = h⁻¹ * Triality.xr Triality.rootC b * h := by rw [hthis]
      rw [h2, map_mul, map_mul, map_inv]
    have hE2 : σ (c (Triality.xr Triality.rootC b)) = eichler Q u ((τ b) • w) := by
      rw [hc_root Triality.rootC Triality.rootC_mem b]
      exact hσz (τ b)
    have hE3 : (σ h)⁻¹ * σ (Triality.xr Triality.rootC b) * σ h =
        eichler Q ((σ h)⁻¹ u) (b • ((σ h)⁻¹ w)) := by
      rw [hσz b]
      have hconj := eichler_conj (Q := Q) hUO u (b • w)
      rw [inv_inv] at hconj
      rw [hconj, LinearEquiv.map_smul]
    exact hE2.symm.trans (hE1.trans hE3)
  have hincr : ∀ {u' w' : Fin 4 ⊕ Fin 4 → K}, Q u' = 0 → Q w' = 0 → polar Q u' w' = 0 →
      ∀ (d : K) (x : Fin 4 ⊕ Fin 4 → K),
        eichler Q u' (d • w') x = x + d • (eichler Q u' w' x - x) := by
    intro u' w' h1 h2 h3 d x
    have hdw : polar Q u' (d • w') = 0 := by rw [polar_smul_right_eq, h3, mul_zero]
    have hQdw : Q (d • w') = 0 := by rw [QuadraticMap.map_smul, h2, smul_zero]
    rw [eichler_apply h1 hdw, eichler_apply h1 h3]
    simp only [polar_smul_right_eq, h2, hQdw, zero_mul, add_zero, smul_sub, smul_smul]
    module
  have hUu : Q ((σ h)⁻¹ u) = 0 := by
    rw [map_of_mem hUO, hQu]
  have hUw : Q ((σ h)⁻¹ w) = 0 := by
    rw [map_of_mem hUO, hQw]
  have hUuw : polar Q ((σ h)⁻¹ u) ((σ h)⁻¹ w) = 0 := by
    rw [polar_map_of_mem hUO, huw]
  have h1eq : eichler Q ((σ h)⁻¹ u) ((σ h)⁻¹ w) = eichler Q u w := by
    have h := hmain 1
    rw [map_one, one_smul, one_smul] at h
    exact h.symm
  have hτw : ∀ b : K, (τ b) • w = b • w := by
    intro b
    set x₀ : Fin 4 ⊕ Fin 4 → K := F.vec (3 : Fin 4) false with hx₀
    have hx₀u : polar Q x₀ u = 1 := by
      rw [hx₀, hu]; exact F.polar_vec_not (3 : Fin 4) false
    have hx₀w : polar Q x₀ w = 0 := by
      rw [hx₀, hw]; exact F.polar_vec_of_ne (by decide) false false
    have h := congrArg (fun (g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) => g x₀)
      (hmain b)
    rw [hincr hQu hQw huw (τ b) x₀, hincr hUu hUw hUuw b x₀, h1eq] at h
    have hRw : eichler Q u w x₀ - x₀ = w := by
      rw [eichler_apply hQu huw]
      simp only [hQw, zero_mul, add_zero, hx₀u, hx₀w, one_smul, zero_smul, sub_zero]
      rw [add_sub_cancel_left]
    rw [hRw] at h
    exact add_left_cancel h
  have hτ : τ = 1 := by
    refine RingEquiv.ext fun b => ?_
    have h := hτw b
    have hsub : (τ b - b) • w = 0 := by rw [sub_smul, h, sub_self]
    have hzero : τ b - b = 0 := by
      by_contra hc
      have h3 : w = 0 := by
        calc w = ((τ b - b)⁻¹ * (τ b - b)) • w := by rw [inv_mul_cancel₀ hc, one_smul]
          _ = (τ b - b)⁻¹ • ((τ b - b) • w) := by rw [smul_smul]
          _ = 0 := by rw [hsub, smul_zero]
      exact hwne h3
    exact sub_eq_zero.mp hzero
  have hc_id : c = MonoidHom.id (Triality.Sp8 K) := by
    refine Triality.ext_xr (f := c) (g := MonoidHom.id (Triality.Sp8 K)) ?_
    intro δ hδ b
    simpa [htri_id, hkε.2, hτ] using hcA δ hδ b
  intro z
  rw [hc_id]
  rfl

end CFSG.StandardType.KGOm
