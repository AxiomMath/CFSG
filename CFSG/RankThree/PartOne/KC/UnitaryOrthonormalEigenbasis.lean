module

public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.KCUnitaryPlane

open Module Module.End CFSG.LocalAnalysis.ComponentInitial

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem bar_eq_inv_of_pow_eq_one {p : ℕ} (hpq : p ∣ ℓ ^ f + 1) {μ : K} (hμ : μ ^ p = 1) :
    h.bar μ * μ = 1 := by
  have h1 : μ ^ (ℓ ^ f + 1) = 1 := by
    obtain ⟨k, hk⟩ := hpq
    rw [hk, pow_mul, hμ, one_pow]
  rw [UnitaryFieldData.bar_apply, ← pow_succ]
  exact h1

theorem exists_orthonormal_common_eigenbasis {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpq : p ∣ ℓ ^ f + 1) {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {ι : Type*} [Finite ι] (g : ι → End K V) (hcomm : ∀ i j, Commute (g i) (g j))
    (hpow : ∀ i, g i ^ p = 1) (hiso : ∀ i v w, B (g i v) (g i w) = B v w) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (μ : ι → Fin (finrank K V) → K),
      (∀ i j, g i (b j) = μ i j • b j) ∧ ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
  classical
  have hss := fun i => isSemisimple_of_pow_eq_one hζ (hpow i)
  have hspan : ∀ i, ⨆ μ, (g i).maxGenEigenspace μ = ⊤ := fun i =>
    ((hss i).iSup_maxGenEigenspace_eq_top_iff).2 (iSup_eigenspace_eq_top_of_pow_eq_one hζ (hpow i))
  set W : (ι → K) → Submodule K V := fun χ => ⨅ i, (g i).maxGenEigenspace (χ i) with hWdef
  have hW : ∀ (χ : ι → K) (i : ι), (g i).maxGenEigenspace (χ i) = (g i).eigenspace (χ i) :=
    fun χ i => (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace _
  have htop : ⨆ χ, W χ = ⊤ :=
    iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute g
      (fun i j _ => hcomm i j) hspan
  have hind : iSupIndep W :=
    independent_iInf_maxGenEigenspace_of_forall_mapsTo g
      fun i j φ => mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have hmem : ∀ (χ : ι → K) (i : ι) {v : V}, v ∈ W χ → g i v = χ i • v := fun χ i v hv => by
    have hi := (Submodule.mem_iInf _).mp hv i
    rw [hW] at hi
    exact mem_eigenspace_iff.mp hi
  have horth : ∀ {χ ψ : ι → K}, χ ≠ ψ → ∀ {v w : V}, v ∈ W χ → w ∈ W ψ → B v w = 0 := by
    intro χ ψ hne v w hv hw
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    by_cases hv0 : v = 0
    · rw [hv0, map_zero, LinearMap.zero_apply]
    have hev : (g i).HasEigenvector (χ i) v := ⟨mem_eigenspace_iff.mpr (hmem χ i hv), hv0⟩
    have hpv : χ i ^ p = 1 := by
      have h1 := hev.pow_apply p
      rw [hpow i, Module.End.one_apply] at h1
      have h2 : (χ i ^ p - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv0)
    have e1 : B v w = h.bar (χ i) * ψ i * B v w := by
      have h3 := hiso i v w
      rw [hmem χ i hv, hmem ψ i hw] at h3
      simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] at h3
      linear_combination -h3
    have hbar := bar_eq_inv_of_pow_eq_one h hpq hpv
    have h4 : (χ i - ψ i) * B v w = 0 := by
      linear_combination (χ i) * e1 + (ψ i * B v w) * hbar
    exact (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hi)
  have hsep : ∀ χ, (B.domRestrict₁₂ (W χ) (W χ)).SeparatingLeft := by
    intro χ x hx
    have hxz : ∀ w : V, B (x : V) w = 0 := by
      intro w
      have hw : w ∈ ⨆ ψ, W ψ := by rw [htop]; trivial
      refine Submodule.iSup_induction W (motive := fun w => B (x : V) w = 0) hw ?_ ?_ ?_
      · intro ψ w hwψ
        by_cases hψ : ψ = χ
        · subst hψ
          exact hx ⟨w, hwψ⟩
        · rw [← (LinearMap.isSymm_def.mp hB) w (x : V), horth hψ hwψ x.2, map_zero]
      · rw [map_zero]
      · intro a b ha hb
        rw [map_add, ha, hb, add_zero]
    exact Subtype.ext (hBl (x : V) hxz)
  choose e he using fun χ => h.exists_orthonormal_basis
    (B := B.domRestrict₁₂ (W χ) (W χ)) (hB.domRestrict (W χ)) (hsep χ)
  let b₀ := hint.collectedBasis e
  have : Finite (Σ χ, Fin (finrank K (W χ))) := Module.Finite.finite_basis b₀
  let e₀ : (Σ χ, Fin (finrank K (W χ))) ≃ Fin (finrank K V) :=
    (Finite.equivFin _).trans (finCongr (finrank_eq_nat_card_basis b₀).symm)
  refine ⟨b₀.reindex e₀, fun i j => (e₀.symm j).1 i, fun i j => ?_, fun i j => ?_⟩
  · have hm : b₀ (e₀.symm j) ∈ W (e₀.symm j).1 := hint.collectedBasis_mem e (e₀.symm j)
    rw [Basis.reindex_apply]
    exact hmem _ i hm
  · rw [Basis.reindex_apply, Basis.reindex_apply]
    obtain ⟨⟨χ, a⟩, hχa⟩ : ∃ z, z = e₀.symm i := ⟨_, rfl⟩
    obtain ⟨⟨ψ, c⟩, hψc⟩ : ∃ z, z = e₀.symm j := ⟨_, rfl⟩
    rw [← hχa, ← hψc]
    have hb1 : b₀ ⟨χ, a⟩ = (e χ a : V) := by
      rw [DirectSum.IsInternal.collectedBasis_coe]
    have hb2 : b₀ ⟨ψ, c⟩ = (e ψ c : V) := by
      rw [DirectSum.IsInternal.collectedBasis_coe]
    rw [hb1, hb2]
    by_cases hχψ : χ = ψ
    · subst hχψ
      have := he χ a c
      simp only [LinearMap.domRestrict₁₂_apply] at this
      rw [this]
      have hij : (⟨χ, a⟩ : Σ χ, Fin (finrank K (W χ))) = ⟨χ, c⟩ ↔ a = c := by simp
      by_cases hac : a = c
      · subst hac
        have : i = j := by
          apply e₀.symm.injective
          rw [← hχa, ← hψc]
        simp [this]
      · have hij' : i ≠ j := by
          intro hij
          apply hac
          have := hχa.trans (hij ▸ hψc.symm)
          simpa using this
        simp [hac, hij']
    · have hij' : i ≠ j := by
        intro hij
        apply hχψ
        have := hχa.trans (hij ▸ hψc.symm)
        simpa using congrArg Sigma.fst this
      rw [horth hχψ (e χ a).2 (e ψ c).2]
      simp [hij']

theorem exists_orthonormal_common_eigenbasis_of_pow_eq_scalar {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hpq : p ∣ ℓ ^ f + 1)
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {ι : Type*} [Finite ι] (g : ι → End K V) (r : ι → K)
    (hcomm : ∀ i j, Commute (g i) (g j)) (hr : ∀ i, r i ≠ 0)
    (hnorm : ∀ i, h.bar (r i) * r i = 1)
    (hpow : ∀ i, g i ^ p = (r i ^ p) • (1 : End K V))
    (hiso : ∀ i v w, B (g i v) (g i w) = B v w) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (μ : ι → Fin (finrank K V) → K),
      (∀ i j, g i (b j) = μ i j • b j) ∧
      (∀ i j, μ i j ^ p = r i ^ p) ∧
      (∀ i j, μ i j ≠ 0) ∧
      (∀ i j, B (b i) (b j) = if i = j then 1 else 0) := by
  classical
  let g' : ι → End K V := fun i => (r i)⁻¹ • g i
  have hg'pow : ∀ i, g' i ^ p = 1 := by
    intro i
    dsimp only [g']
    rw [_root_.smul_pow, hpow i, smul_smul, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero p (hr i)), one_smul]
  have hg'comm : ∀ i j, Commute (g' i) (g' j) := by
    intro i j
    exact ((hcomm i j).smul_left (r i)⁻¹).smul_right (r j)⁻¹
  have hg'iso : ∀ i v w, B (g' i v) (g' i w) = B v w := by
    intro i v w
    have hcoef : h.bar ((r i)⁻¹) * (r i)⁻¹ = 1 := by
      rw [map_inv₀, ← mul_inv_rev, mul_comm (r i) (h.bar (r i)), hnorm i, inv_one]
    calc
      B (g' i v) (g' i w)
          = B ((r i)⁻¹ • g i v) ((r i)⁻¹ • g i w) := rfl
      _ = h.bar ((r i)⁻¹) • B (g i v) ((r i)⁻¹ • g i w) :=
            LinearMap.map_smulₛₗ₂ B ((r i)⁻¹) (g i v) ((r i)⁻¹ • g i w)
      _ = h.bar ((r i)⁻¹) • ((r i)⁻¹ • B (g i v) (g i w)) := by
            rw [LinearMap.map_smul]
      _ = (h.bar ((r i)⁻¹) * (r i)⁻¹) • B (g i v) (g i w) := by
            rw [smul_smul]
      _ = B (g i v) (g i w) := by rw [hcoef, one_smul]
      _ = B v w := hiso i v w
  obtain ⟨b, μ, hb, horth⟩ :=
    exists_orthonormal_common_eigenbasis (h := h) (hζ := hζ) (hpq := hpq)
      (B := B) (hB := hB) (hBl := hBl) (g := g') (hcomm := hg'comm)
      (hpow := hg'pow) (hiso := hg'iso)
  have hμ : ∀ i j, μ i j ^ p = 1 := by
    intro i j
    have hev : (g' i).HasEigenvector (μ i j) (b j) :=
      Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (hb i j), b.ne_zero j⟩
    have hp := hev.pow_apply p
    rw [hg'pow i] at hp
    have h1 : μ i j ^ p • b j = (1 : K) • b j := by
      rw [one_smul]
      simpa using hp.symm
    exact smul_left_injective K (b.ne_zero j) h1
  refine ⟨b, fun i j => r i * μ i j, ?_, ?_, ?_, horth⟩
  · intro i j
    have hfg : r i • g' i = g i := by
      dsimp only [g']
      rw [smul_smul, mul_inv_cancel₀ (hr i), one_smul]
    calc
      g i (b j) = (r i • g' i) (b j) := by rw [hfg]
      _ = r i • g' i (b j) := rfl
      _ = r i • (μ i j • b j) := by rw [hb i j]
      _ = (r i * μ i j) • b j := smul_smul ..
  · intro i j
    rw [mul_pow, hμ i j, mul_one]
  · intro i j
    exact mul_ne_zero (hr i) (by
      intro h0
      have hμij := hμ i j
      rw [h0, zero_pow (NeZero.ne p)] at hμij
      exact zero_ne_one hμij)

end CFSG.RankThree.PartOne.KCUnitaryPlane
