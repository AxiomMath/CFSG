module

public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenKGDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeElt

public section

namespace CFSG.StandardType

namespace SuNsRootGen

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2

variable {K : Type} [Field K] {n d p : ℕ} (h : UnitaryFieldData 2 n K)
  {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'} {A : Subgroup (MulAut L')}

theorem conj_swapU_comm_conj_iff
    (hφker : ∀ g, φ g = 1 → g ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker) (i j : Fin d)
    {D : ↥(unitarySU 2 n K d)} {σ : Fin d → Kˣ} (hD : (D : GL (Fin d) K) = diagHom d σ) :
    MulAut.conj (φ (SURep.swapU h i j)) * MulAut.conj (φ D) =
      MulAut.conj (φ D) * MulAut.conj (φ (SURep.swapU h i j)) ↔ σ i = σ j := by
  haveI : CharP K 2 := h.charP
  constructor
  · intro hcomm
    by_cases hij : i = j
    · rw [hij]
    let w : ↥(unitarySU 2 n K d) := SURep.swapU h i j
    let τ : Fin d → Kˣ := fun k => σ (Equiv.swap i j k) * (σ k)⁻¹
    let y : ↥(unitarySU 2 n K d) := w * D * w⁻¹ * D⁻¹
    have hwcoe : (w : GL (Fin d) K) = permGL (Equiv.swap i j) := by
      simp [w, coe_swapU_eq_permGL]
    have hyD : (y : GL (Fin d) K) = diagHom d τ := by
      rw [show (y : GL (Fin d) K) = (w : GL (Fin d) K) * (D : GL (Fin d) K) *
          (w : GL (Fin d) K)⁻¹ * (D : GL (Fin d) K)⁻¹ by simp [y]]
      rw [hwcoe, hD, permGL_mul_diagHom_mul_inv, Equiv.symm_swap, ← map_inv, ← map_mul]
      rfl
    have hcentral : φ y ∈ Subgroup.center L' := by
      have hcomm' : MulAut.conj (φ w * φ D) = MulAut.conj (φ D * φ w) := by
        simpa only [map_mul] using hcomm
      have hconj : MulAut.conj (φ y) = 1 := by
        rw [show φ y = (φ w * φ D) * (φ D * φ w)⁻¹ by
          simp [y, map_mul]
          group]
        rw [map_mul, map_inv, hcomm']
        group
      rw [Subgroup.mem_center_iff]
      intro x
      have hx := congrArg (fun f : MulAut L' => f x) hconj
      rw [MulAut.conj_apply, MulAut.one_apply] at hx
      calc x * φ y = (φ y * x * (φ y)⁻¹) * φ y := by rw [hx]
        _ = φ y * x := by group
    let e : ↥(unitarySU 2 n K d) := y * (w * y⁻¹ * w⁻¹)
    have hφe : φ e = 1 := by
      have hcy : φ w * φ y = φ y * φ w :=
        Subgroup.mem_center_iff.mp hcentral (φ w)
      have hφe_eq : φ e = φ y * φ w * (φ y)⁻¹ * (φ w)⁻¹ := by
        simp [e, map_mul]
        group
      rw [hφe_eq]
      calc φ y * φ w * (φ y)⁻¹ * (φ w)⁻¹
          = φ w * φ y * (φ y)⁻¹ * (φ w)⁻¹ := by rw [← hcy]
        _ = 1 := by group
    have hesc : (e : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K := by
      have heker : e ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker := hφker e hφe
      rw [LargeEvenProjMk, QuotientGroup.ker_mk'] at heker
      exact Subgroup.mem_subgroupOf.mp heker
    have hwyw : ((w * y⁻¹ * w⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
        diagHom d (fun k => (τ (Equiv.swap i j k))⁻¹) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hwcoe,
        hyD, ← map_inv, permGL_mul_diagHom_mul_inv, Equiv.symm_swap]
      rfl
    have heD : (e : GL (Fin d) K) =
        diagHom d (fun k => τ k * (τ (Equiv.swap i j k))⁻¹) := by
      calc (e : GL (Fin d) K) = (y : GL (Fin d) K) *
            ((w * y⁻¹ * w⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) := by
            simp [e]
        _ = diagHom d τ * diagHom d (fun k => (τ (Equiv.swap i j k))⁻¹) := by
            rw [hyD, hwyw]
        _ = diagHom d (fun k => τ k * (τ (Equiv.swap i j k))⁻¹) := by
            rw [← map_mul]
            rfl
    have hscalarCenter : LargeEvenScalars (Fin d) K = Subgroup.center (GL (Fin d) K) :=
      largeEvenScalars_def.trans Matrix.GeneralLinearGroup.center_eq_range_scalar.symm
    have hcenter : diagHom d (fun k => τ k * (τ (Equiv.swap i j k))⁻¹) ∈
        Subgroup.center (GL (Fin d) K) := by
      rw [← heD]
      rw [hscalarCenter] at hesc
      exact hesc
    have hratio : τ i * (τ j)⁻¹ = τ j * (τ i)⁻¹ := by
      simpa [Equiv.swap_apply_left, Equiv.swap_apply_right] using
        TableBU.diagHom_eq_of_mem_center hcenter i j
    have hτj : τ j = (τ i)⁻¹ := by
      have hi : τ i = σ j * (σ i)⁻¹ := by simp only [τ, Equiv.swap_apply_left]
      have hj : τ j = σ i * (σ j)⁻¹ := by simp only [τ, Equiv.swap_apply_right]
      rw [hi, hj]
      group
    have hratio' : τ i * τ i = (τ i)⁻¹ * (τ i)⁻¹ := by
      have h := hratio
      rw [hτj] at h
      simpa using h
    have h2 : (τ i) ^ 2 = (τ i)⁻¹ * (τ i)⁻¹ := by
      rw [pow_two]
      exact hratio'
    have h4 : (τ i) ^ 4 = 1 := by
      calc (τ i) ^ 4 = ((τ i) ^ 2) * ((τ i) ^ 2) := by
            rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
        _ = ((τ i)⁻¹ * (τ i)⁻¹) * ((τ i)⁻¹ * (τ i)⁻¹) := by rw [h2]
        _ = ((τ i)⁻¹ * (τ i)⁻¹) * ((τ i) * (τ i)) := by rw [← h2, pow_two]
        _ = 1 := by group
    have hone : (τ i : K) = 1 := by
      have h4K : (τ i : K) ^ 4 = 1 := by
        rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]
      have hsq2 : ((τ i : K) ^ 2) ^ 2 = 1 := by
        rw [← pow_mul]
        norm_num
        exact h4K
      have hsq : (τ i : K) ^ 2 = 1 := by
        rcases sq_eq_one_iff.mp hsq2 with h1 | h1
        · exact h1
        · rwa [CharTwo.neg_eq] at h1
      rcases sq_eq_one_iff.mp hsq with h1 | h1
      · exact h1
      · rwa [CharTwo.neg_eq] at h1
    have hτ1 : τ i = 1 := Units.ext hone
    have hσji : σ j = σ i := by
      have h : τ i = σ j * (σ i)⁻¹ := by simp only [τ, Equiv.swap_apply_left]
      rw [h] at hτ1
      exact mul_inv_eq_one.mp hτ1
    exact hσji.symm
  · intro hσij
    have hcomp : σ ∘ Equiv.swap i j = σ := by
      funext x
      rw [Function.comp_apply, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1]
        exact hσij.symm
      · rw [h2]
        exact hσij
      · rfl
    set w : ↥(unitarySU 2 n K d) := SURep.swapU h i j
    have hwDw : w * D * w⁻¹ = D := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_swapU_eq_permGL, hD,
        permGL_mul_diagHom_mul_inv, Equiv.symm_swap, hcomp]
    have hcomm : w * D = D * w := by
      calc w * D = w * D * w⁻¹ * w := by group
        _ = D * w := by rw [hwDw]
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hcomm]

theorem ggHypCent_swapU_eq (hp : p.Prime) (hpd : ¬ p ∣ d)
    (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → g ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker)
    (hM : IsDiagTorusModelU p φ A) (i j : Fin d) :
    ggHypCent A (φ (SURep.swapU h i j)) = (pairCentU n p K i j).map φ := by
  haveI : CharP K 2 := h.charP
  have hker_center : φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) :=
    (show φ.ker ≤ (LargeEvenProjMk (unitarySU 2 n K d)).ker from
      fun z hz => hφker z hz).trans TableBUE.ker_projMk_le_center
  have hnp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1 := fun z hz hzp =>
    TableBUE.eq_one_of_mem_suScalars h hp hpd (hφker z hz) hzp
  ext l
  obtain ⟨s, rfl⟩ := hφs l
  constructor
  · intro hl
    simp only [ggHypCent, Subgroup.mem_iInf, mem_ggFix] at hl
    refine Subgroup.mem_map.mpr ⟨s, ?_, rfl⟩
    unfold pairCentU
    rw [Subgroup.mem_centralizer_iff]
    intro D' hD'mem
    obtain ⟨σ', hD'σ', hσ'ij, hσ'p⟩ := hD'mem
    have hD'p : D' ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hD'σ', ← map_pow, Subgroup.coe_one,
        show σ' ^ p = 1 by funext k; simpa using hσ'p k, map_one]
    have hcomm := (conj_swapU_comm_conj_iff h hφker i j hD'σ').mpr hσ'ij
    have hmem : MulAut.conj (φ D') ∈ A :=
      (hM _).mpr ⟨D', ⟨σ', hD'σ'⟩, hD'p, rfl⟩
    have hfix : MulAut.conj (φ D') (φ s) = φ s := hl _ ⟨hmem, hcomm⟩
    have hC := TableBUE.centralizer_map_eq_of_noTorsion φ hφs hker_center hnp hD'p
    have hφs_mem : φ s ∈ Subgroup.centralizer ({φ D'} : Set L') := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [MulAut.conj_apply] at hfix
      calc φ s * φ D' = (φ D' * φ s * (φ D')⁻¹) * φ D' := by rw [hfix]
        _ = φ D' * φ s := by group
    rw [hC] at hφs_mem
    obtain ⟨s₀, hs₀, hφs₀⟩ := Subgroup.mem_map.mp hφs_mem
    have hz₀ker : s₀⁻¹ * s ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφs₀]
      group
    have hz₀center : s₀⁻¹ * s ∈ Subgroup.center (↥(unitarySU 2 n K d)) :=
      hker_center hz₀ker
    have hz₀D : D' * (s₀⁻¹ * s) = (s₀⁻¹ * s) * D' :=
      Subgroup.mem_center_iff.mp hz₀center D'
    have hs_eq : s₀ * (s₀⁻¹ * s) = s := by group
    calc D' * s = D' * (s₀ * (s₀⁻¹ * s)) := by rw [hs_eq]
      _ = (D' * s₀) * (s₀⁻¹ * s) := by group
      _ = (s₀ * D') * (s₀⁻¹ * s) := by
            rw [Subgroup.mem_centralizer_iff.mp hs₀ D' (by simp)]
      _ = s₀ * (D' * (s₀⁻¹ * s)) := by group
      _ = s₀ * ((s₀⁻¹ * s) * D') := by rw [hz₀D]
      _ = s * D' := by
            rw [← hs_eq]
            group
  · intro hl
    simp only [ggHypCent, Subgroup.mem_iInf]
    intro a ha
    rw [mem_ggFix]
    obtain ⟨haA, hcomm⟩ := ha
    obtain ⟨D, ⟨σ, hDσ⟩, hDp, haeq⟩ := (hM a).mp haA
    obtain ⟨s, hs, hφs_eq⟩ := Subgroup.mem_map.mp hl
    have hcomm' := hcomm
    rw [haeq] at hcomm'
    have hσij : σ i = σ j :=
      (conj_swapU_comm_conj_iff h hφker i j hDσ).mp hcomm'
    have hσp : ∀ k, σ k ^ p = 1 := by
      have h2 : σ ^ p = 1 := by
        apply diagHom_injective d
        rw [map_one]
        have h : (D : GL (Fin d) K) ^ p = 1 := by
          rw [← Subgroup.coe_pow, hDp, Subgroup.coe_one]
        rwa [hDσ, ← map_pow] at h
      simpa using congrFun h2
    have hDs : D * s = s * D := by
      refine Subgroup.mem_centralizer_iff.mp hs D ?_
      exact ⟨σ, hDσ, hσij, hσp⟩
    rw [haeq]
    rw [← hφs_eq]
    calc MulAut.conj (φ D) (φ s) = φ (D * s * D⁻¹) := by
          rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
      _ = φ (s * D * D⁻¹) := by rw [hDs]
      _ = φ s := by rw [mul_assoc, mul_inv_cancel, mul_one]

end SuNsRootGen

end CFSG.StandardType
