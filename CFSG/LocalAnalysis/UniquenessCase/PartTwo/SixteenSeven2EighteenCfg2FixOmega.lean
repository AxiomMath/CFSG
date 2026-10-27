module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthRat
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallCases
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.ClassicalGroups.Orthogonal.Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement Matrix

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.SignalizerFunctorTheorem.NonLocal.Orth

private theorem elemGroup_submodule_eq_bot_or_top
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (hP : ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j))
    (W : Submodule K V) (hW : ∀ g ∈ elementaryGroup Q, ∀ x ∈ W, g x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨P, hPorth⟩ := hP
  have hWe : ∀ u w : V, ∀ x ∈ W, eichler Q u w x ∈ W :=
    fun u w x hx => hW _ (eichler_mem_elementaryGroup Q u w) x hx
  have htwo : ∀ i : Fin 2, ∃ j : Fin 2, j ≠ i := by
    intro i
    fin_cases i
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
  have hsing : ∃ u : V, u ≠ 0 ∧ Q u = 0 ∧ u ∈ W := by
    obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    by_cases hA : ∃ i : Fin 2, polar Q x (P i).e ≠ 0
    · obtain ⟨i, hi⟩ := hA
      obtain ⟨j, hji⟩ := htwo i
      exact ⟨(P i).e, (P i).e_ne_zero, (P i).Q_e,
        exchange_mem (P i) (P j) (hPorth i j (Ne.symm hji)) W (hWe _ _) (hWe _ _) hxW hi⟩
    by_cases hB : ∃ i : Fin 2, polar Q x (P i).f ≠ 0
    · obtain ⟨i, hi⟩ := hB
      obtain ⟨j, hji⟩ := htwo i
      exact ⟨(P i).f, (P i).f_ne_zero, (P i).Q_f,
        exchange_mem (swapPair (P i)) (P j) (orth_swapPair_left (hPorth i j (Ne.symm hji))) W
          (hWe _ _) (hWe _ _) hxW hi⟩
    push Not at hA hB
    obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hx0
    set w : V := y - (polar Q y (P 0).f) • (P 0).e - (polar Q y (P 0).e) • (P 0).f with hw
    have hwe : polar Q (P 0).e w = 0 := by
      rw [hw, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_comm Q y (P 0).e, polar_self_eq_zero (P 0).Q_e, (P 0).polar_ef]
      ring
    have hwf : polar Q (P 0).f w = 0 := by
      rw [hw, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_comm Q y (P 0).f, (P 0).polar_fe, polar_self_eq_zero (P 0).Q_f]
      ring
    have hxw : polar Q x w ≠ 0 := by
      rw [hw, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
        hA 0, hB 0]
      simpa using hy
    exact ⟨(P 0).e, (P 0).e_ne_zero, (P 0).Q_e,
      perp_extract_mem (P 0) W hxW (hA 0) (HypPair.mem_perp.2 ⟨hwe, hwf⟩)
        (hWe (P 0).e w x hxW) hxw⟩
  obtain ⟨u₀, hu₀0, hu₀Q, hu₀W⟩ := hsing
  have hall : ∀ v : V, Q v = 0 → v ∈ W := by
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]; exact W.zero_mem
    obtain ⟨g, hg, hgv⟩ :=
      exists_mem_elementaryGroup_apply_eq hQ (hPorth 0 1 (by decide)) hu₀0 hv0
        (by rw [hu₀Q, hv])
    rw [← hgv]
    exact hW g hg u₀ hu₀W
  rw [eq_top_iff]
  intro v _
  have hle : Submodule.span K {u : V | Q u = 0} ≤ W := by
    rw [Submodule.span_le]
    rintro u hu
    exact hall u hu
  exact hle (by rw [span_singular_eq_top (P 0)]; exact Submodule.mem_top)

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.SignalizerFunctorTheorem.NonLocal.Orth
  CFSG.LieType.Universal.Spin

private theorem fixV_eq_bot_omegaMinus_of_eichler {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {U : Subgroup W} {d : ℕ} (hd : 3 ≤ d)
    {K : Type} [Field K] [Finite K] (b c : K) (hK2 : Nat.card K = 2)
    (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hE : ∀ g ∈ elementaryGroup (quadMinus d K b c),
      (toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g ∈
        StatedOmega (StatedQuadMinus d K b c))
    (hReal : (FFModel.nat (StatedOmega (StatedQuadMinus d K b c))).Realizes H U ⊥) :
    U ⊓ fixV H = ⊥ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨π, hπ⟩ := hReal
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, hβsurj, hβker, hβe⟩ := R.exists_β
  have hstab : ∀ x : ↥H, ∀ u ∈ U, (x : MulAut W) u ∈ U := R.U_inv
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥U) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  have htwo : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    have h2 : x ^ 2 = x := by
      have := FiniteField.pow_card x
      rwa [← Nat.card_eq_fintype_card, hK2] at this
    have h3 : x * (x - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, h2, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hQ : (polarBilin (quadMinus d K b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite d K hpoly
  have hP : ∃ P : Fin 2 → HypPair (quadMinus d K b c), ∀ i j, i ≠ j → (P i).Orth (P j) := by
    refine ⟨fun i => minusPair K b c (Fin.castLE (by omega : 2 ≤ d - 1) i), ?_⟩
    intro i j hij
    exact minusPair_orth (fun h => hij (Fin.castLE_injective _ h))
  obtain ⟨P, hPorth⟩ := hP
  refine le_bot_iff.1 fun w hw => ?_
  obtain ⟨hwI, hwfix⟩ := Subgroup.mem_inf.1 hw
  have hbeta : β ⟨w, hwI⟩ = 1 := by
    by_contra hbne
    set v : Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K :=
      Multiplicative.toAdd (β ⟨w, hwI⟩) with hv
    have hv0 : v ≠ 0 := fun h =>
      hbne (Multiplicative.toAdd.injective (by rw [← hv, h, toAdd_one]))
    have hline : ∀ g ∈ elementaryGroup (quadMinus d K b c),
        ∀ x ∈ Submodule.span K ({v} : Set _), g x ∈ Submodule.span K ({v} : Set _) := by
      intro g hg x hx
      obtain ⟨cc, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul]
      refine Submodule.smul_mem _ cc ?_
      have hmem := hE g hg
      have hfixw : ((π ⟨(toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g, hmem⟩ :
          ↥H) : MulAut W) w = w := (mem_fixV.1 hwfix) _ (π _).2
      have h3 := hβe ⟨(toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g, hmem⟩
        ⟨w, hwI⟩ (hstab _ w hwI)
      have h4 : β ⟨((π ⟨(toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g, hmem⟩ :
          ↥H) : MulAut W) w, hstab _ w hwI⟩ = β ⟨w, hwI⟩ :=
        congrArg β (Subtype.ext hfixw)
      have h5 := congrArg Multiplicative.toAdd (h3.symm.trans h4)
      have hgv : g v = v := by
        have h5' : ((toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g :
            GL (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K) *ᵥ v = v := h5
        rw [← toLinEquiv_apply
          (A := (toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g)] at h5'
        rwa [MulEquiv.apply_symm_apply] at h5'
      rw [hgv]
      exact Submodule.subset_span (Set.mem_singleton v)
    rcases elemGroup_submodule_eq_bot_or_top hQ ⟨P, hPorth⟩
        (Submodule.span K ({v} : Set _)) hline with hbot | htop
    · have : v ∈ (⊥ : Submodule K _) := hbot ▸ Submodule.subset_span (Set.mem_singleton v)
      exact hv0 (by simpa using this)
    · have h0 : (P 0).e ∈ Submodule.span K ({v} : Set _) := htop ▸ Submodule.mem_top
      have h1 : (P 1).e ∈ Submodule.span K ({v} : Set _) := htop ▸ Submodule.mem_top
      obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp h0
      obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp h1
      have hc₀0 : c₀ ≠ 0 := fun h => (P 0).e_ne_zero (by rw [← hc₀, h, zero_smul])
      have hkey : c₁ * polar (quadMinus d K b c) v (P 0).f = 0 := by
        have hfe : polar (quadMinus d K b c) (P 1).e (P 0).f = 0 := by
          have h := (hPorth 0 1 (by decide)).fe
          rwa [polar_comm] at h
        rw [← hc₁] at hfe
        rwa [polar_smul_left_eq] at hfe
      have hone : c₀ * polar (quadMinus d K b c) v (P 0).f = 1 := by
        have hef : polar (quadMinus d K b c) (P 0).e (P 0).f = 1 := (P 0).polar_ef
        rw [← hc₀] at hef
        rwa [polar_smul_left_eq] at hef
      have hc₁0 : c₁ = 0 := by
        rcases mul_eq_zero.mp hkey with h | h
        · exact h
        · exfalso
          rw [h, mul_zero] at hone
          exact one_ne_zero hone.symm
      exact (P 1).e_ne_zero (by rw [← hc₁, hc₁0, zero_smul])
  have h6 : (⟨w, hwI⟩ : ↥U) = 1 := hβinj (by rw [hbeta]; exact (map_one β).symm)
  simpa using congrArg Subtype.val h6

private theorem elementaryGroup_le_commutator_of_perfect {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (hperf : Group.IsPerfect ↥(elementaryGroup Q)) :
    elementaryGroup Q ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  haveI := hperf
  calc elementaryGroup Q = ⁅elementaryGroup Q, elementaryGroup Q⁆ :=
        (Subgroup.commutator_eq_self).symm
    _ ≤ _ := Subgroup.commutator_mono (elementaryGroup_le_orthogonalGroup Q)
        (elementaryGroup_le_orthogonalGroup Q)

private theorem eichler_mem_statedOmega {d : ℕ} (hd : 3 ≤ d) {K : Type} [Field K] (b c : K)
    (hK2 : Nat.card K = 2) (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K)}
    (hg : g ∈ elementaryGroup (quadMinus d K b c)) :
    (toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g ∈
      StatedOmega (StatedQuadMinus d K b c) := by
  haveI : CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2 K :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2.of_natCard_eq_two hK2
  have hQ : (polarBilin (quadMinus d K b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite d K hpoly
  have hfr : 6 ≤ Module.finrank K (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum]
    omega
  have hperf : Group.IsPerfect ↥(elementaryGroup (quadMinus d K b c)) :=
    Group.isPerfect_def.mpr
      (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.commutator_elementaryGroup_eq_top_f2
        hQ hfr)
  have hle : elementaryGroup (quadMinus d K b c) ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus d K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus d K b c)⁆ :=
    elementaryGroup_le_commutator_of_perfect hperf
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
    (CFSG.LieType.Universal.Spin.coe_quadMinus d K b c), Subgroup.mem_comap]
  change (toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K)
    ((toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g) ∈
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus d K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus d K b c)⁆
  rw [MulEquiv.apply_symm_apply]
  exact hle hg

theorem s16c167_cfg2_fix_omegaMinus {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {U : Subgroup W} {n : ℕ} (hn : n = 6 ∨ n = 8) (h : NatOmegaMinus H U ⊥ n 1) :
    U ⊓ fixV H = ⊥ := by
  rcases hn with rfl | rfl
  · obtain ⟨-, K, hK, hKf, b, c, hK2, hpoly, π, hπ⟩ := h
    letI := hK
    haveI : Finite K := hKf
    exact fixV_eq_bot_omegaMinus_of_eichler (d := 3) (by norm_num) b c hK2 hpoly
      (fun g hg => eichler_mem_statedOmega (by norm_num) b c hK2 hpoly hg) ⟨π, hπ⟩
  · obtain ⟨-, K, hK, hKf, b, c, hK2, hpoly, π, hπ⟩ := h
    letI := hK
    haveI : Finite K := hKf
    exact fixV_eq_bot_omegaMinus_of_eichler (d := 4) (by norm_num) b c hK2 hpoly
      (fun g hg => eichler_mem_statedOmega (by norm_num) b c hK2 hpoly hg) ⟨π, hπ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
