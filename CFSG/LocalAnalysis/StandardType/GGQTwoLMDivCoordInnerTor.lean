module

import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTorMono

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix Multiplicative

open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)
open CFSG.RankThree.Classical (permGL)
open CFSG.RankThree.Classical2 (permGL_mul_diagHom_mul_inv)
open CFSG.StandardType.UModel (uvec uvec_apply prod_uvec crd_eq_of_uvec_eq uvec_injective
  uvec_permAutV exists_uvec_eq uvec_pow_eq_one)

private theorem qTwoLMDivCoordInner_tor_conjTr_diagonal {F0 : Type} [Field F0] [Finite F0]
    [CharP F0 2] {m : ℕ} (d : Fin m → F0) :
    conjTr (CFSG.LieType.BorelTits.unitaryInvolution F0 2 1) (Matrix.diagonal d) =
      Matrix.diagonal fun k => CFSG.LieType.BorelTits.unitaryInvolution F0 2 1 (d k) := by
  rw [conjTr, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]

private theorem qTwoLMDivCoordInner_tor_diagHom_mem {F0 : Type} [Field F0] [Finite F0]
    [CharP F0 2] {m : ℕ} {t : Fin m → F0ˣ} (ht : ∀ k, t k ^ 3 = 1)
    (hprod : ∏ k, t k = 1) :
    diagHom m t ∈ SUid (CFSG.LieType.BorelTits.unitaryInvolution F0 2 1) m := by
  refine ⟨?_, ?_⟩
  · rw [det_diagHom, ← Units.coe_prod, hprod, Units.val_one]
  · rw [coe_diagHom, qTwoLMDivCoordInner_tor_conjTr_diagonal (F0 := F0),
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    have h := congrArg (fun x : F0ˣ => (x : F0)) (ht k)
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, pow_one, ← pow_succ]
    exact h

private theorem qTwoLMDivCoordInner_tor_crd_zpow {m : ℕ} (f : ↥(sumZero m 3)) (n : ℤ)
    (k : Fin m) : crd (f ^ n) k = (n : ZMod 3) * crd f k := by
  simp only [crd, Subgroup.coe_zpow]
  change toAdd (((f : Fin m → Multiplicative (ZMod 3)) k) ^ n) =
    (n : ZMod 3) * toAdd ((f : Fin m → Multiplicative (ZMod 3)) k)
  simp only [toAdd_zpow, zsmul_eq_mul]

private theorem qTwoLMDivCoordInner_tor_crd_oneVec {m : ℕ} (h3 : 3 ∣ m) (k : Fin m) :
    crd (qTwoOneVec m h3) k = 1 := by
  simp [crd, qTwoOneVec]

private theorem qTwoLMDivCoordInner_tor_zpowers_iff {m : ℕ} (h3 : 3 ∣ m)
    (f : ↥(sumZero m 3)) :
    f ∈ Subgroup.zpowers (qTwoOneVec m h3) ↔ ∀ k k' : Fin m, crd f k = crd f k' := by
  constructor
  · intro hf k k'
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hf
    rw [← hn]
    simp only [qTwoLMDivCoordInner_tor_crd_zpow, qTwoLMDivCoordInner_tor_crd_oneVec, mul_one]
  · intro hf
    rcases m with _ | m
    · refine Subgroup.mem_zpowers_iff.mpr ⟨0, ?_⟩
      rw [zpow_zero]
      exact Subsingleton.elim 1 f
    · refine Subgroup.mem_zpowers_iff.mpr ⟨(crd f 0).val, ?_⟩
      apply ext_crd
      intro k
      rw [qTwoLMDivCoordInner_tor_crd_zpow, qTwoLMDivCoordInner_tor_crd_oneVec, mul_one,
        Int.cast_natCast, ZMod.natCast_zmod_val]
      exact (hf k 0).symm

private theorem qTwoLMDivCoordInner_tor_uvec_const_iff {F0 : Type} [Field F0] {m : ℕ}
    {ω : F0ˣ} (hu : ω ^ 3 = 1) (hord : orderOf ω = 3) (f : ↥(sumZero m 3)) :
    (∀ k k' : Fin m, uvec hu f k = uvec hu f k') ↔
      ∀ k k' : Fin m, crd f k = crd f k' := by
  constructor
  · intro h k k'
    exact crd_eq_of_uvec_eq hu hord (h k k')
  · intro h k k'
    rw [uvec_apply, uvec_apply, h k k']

private theorem qTwoLMDivCoordInner_tor_diag_const_iff {F0 : Type} [Field F0] {m : ℕ}
    (t : Fin m → F0ˣ) :
    (∃ c : F0, Matrix.diagonal (fun k => (t k : F0)) = Matrix.diagonal (fun _ => c)) ↔
      ∀ k k' : Fin m, t k = t k' := by
  constructor
  · rintro ⟨c, hc⟩ k k'
    apply Units.ext
    exact (Matrix.diagonal_eq_diagonal_iff.mp hc k).trans
      (Matrix.diagonal_eq_diagonal_iff.mp hc k').symm
  · intro h
    rcases m with _ | m
    · exact ⟨1, Subsingleton.elim _ _⟩
    · refine ⟨(t 0 : F0), Matrix.diagonal_eq_diagonal_iff.mpr fun k => ?_⟩
      exact congrArg (fun x : F0ˣ => (x : F0)) (h k 0)

private theorem qTwoLMDivCoordInner_tor_scalar_aux {F0 : Type} [Field F0] {m : ℕ} {ω : F0ˣ}
    (h3 : 3 ∣ m) (hu : ω ^ 3 = 1) (hord : orderOf ω = 3) (f : ↥(sumZero m 3)) :
    (∃ c : F0,
        Matrix.diagonal (fun k => (uvec hu f k : F0)) = Matrix.diagonal (fun _ => c)) ↔
      f ∈ Subgroup.zpowers (qTwoOneVec m h3) := by
  rw [qTwoLMDivCoordInner_tor_zpowers_iff h3 f]
  exact (qTwoLMDivCoordInner_tor_diag_const_iff (uvec hu f)).trans
    (qTwoLMDivCoordInner_tor_uvec_const_iff hu hord f)

theorem qTwoLMDivCoordInner_torus {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    (hF0 : Nat.card F0 = 4) {m : ℕ} (h3 : 3 ∣ m) :
    ∃ δ : ↥(sumZero m 3) →* Su F0 2 1 m, QTwoDivTorus h3 δ := by
  classical
  obtain ⟨ω, hω⟩ := IsCyclic.exists_generator (α := F0ˣ)
  have hcard_units : Nat.card F0ˣ = 3 := by
    rw [Nat.card_units, hF0]
  have hord : orderOf ω = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hω, hcard_units]
  have hu : ω ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one ω
  have hmem : ∀ f : ↥(sumZero m 3),
      diagHom m (uvec hu f) ∈ SUid (CFSG.LieType.BorelTits.unitaryInvolution F0 2 1) m := fun f =>
    qTwoLMDivCoordInner_tor_diagHom_mem (fun k => uvec_pow_eq_one hu f k) (prod_uvec hu hord f)
  let δ : ↥(sumZero m 3) →* Su F0 2 1 m := ((diagHom m).comp (uvec hu)).codRestrict _ hmem
  have hδcoe : ∀ f, ((δ f : Su F0 2 1 m) : GL (Fin m) F0) = diagHom m (uvec hu f) := fun f => rfl
  have hδmat : ∀ f, (((δ f : Su F0 2 1 m) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) = Matrix.diagonal fun k => (uvec hu f k : F0) := fun f =>
    (congrArg (fun g : GL (Fin m) F0 => (g : Matrix (Fin m) (Fin m) F0)) (hδcoe f)).trans
      (coe_diagHom _)
  have hP : ∀ σ : Equiv.Perm (Fin m),
      ((ggPermSU (K := F0) (f := 1) σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) = permGL σ := by
    intro σ
    apply Units.ext
    rw [show (((ggPermSU (K := F0) (f := 1) σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) :
        Matrix (Fin m) (Fin m) F0) = (σ⁻¹).permMatrix F0 from rfl]
    simp only [CFSG.RankThree.Classical.permGL, MonoidHom.coe_toHomUnits,
      Matrix.permMatrixHom_apply]
  have hinj : Function.Injective δ := by
    intro f g hfg
    have h1 : diagHom m (uvec hu f) = diagHom m (uvec hu g) := by
      simpa [hδcoe] using congrArg (fun x : Su F0 2 1 m => (x : GL (Fin m) F0)) hfg
    exact uvec_injective hu hord (diagHom_injective m h1)
  have hdiag : ∀ f, ggIsDiagMat (δ f : GL (Fin m) F0) :=
    fun f => ⟨fun k => (uvec hu f k : F0), hδmat f⟩
  have hsurj : ∀ s : Su F0 2 1 m, ggIsDiagMat (s : GL (Fin m) F0) → ∃ f, δ f = s := by
    intro s hs
    obtain ⟨d, hd⟩ := hs
    have hdet : (Matrix.diagonal d).det = 1 := by
      rw [← hd]
      exact s.2.1
    have hdk : ∀ k, d k ≠ 0 := by
      intro k hk
      rw [Matrix.det_diagonal] at hdet
      rw [Finset.prod_eq_zero (Finset.mem_univ k) hk] at hdet
      exact one_ne_zero hdet.symm
    let t : Fin m → F0ˣ := fun k => Units.mk0 (d k) (hdk k)
    have ht : ∀ k, t k ^ 3 = 1 := by
      intro k
      have h := pow_card_eq_one' (x := t k)
      rwa [hcard_units] at h
    have hprod : ∏ k, t k = 1 := by
      apply Units.ext
      rw [Units.coe_prod, Units.val_one]
      have h1 : ∏ k, (t k : F0) = ∏ k, d k :=
        Finset.prod_congr rfl fun k _ => rfl
      rw [h1, ← Matrix.det_diagonal, ← hd]
      exact s.2.1
    obtain ⟨f, hf⟩ := exists_uvec_eq hu hord ht hprod
    refine ⟨f, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [hδmat f, hf, hd, Matrix.diagonal_eq_diagonal_iff]
    intro k
    exact Units.val_mk0 (hdk k)
  have hperm : ∀ (σ : Equiv.Perm (Fin m)) f,
      ggPermSU σ⁻¹ * δ f * (ggPermSU σ⁻¹)⁻¹ = δ (permAutV σ f) := by
    intro σ f
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hP σ, hδcoe f, hδcoe (permAutV σ f),
      permGL_mul_diagHom_mul_inv, uvec_permAutV]
  have hscalar : ∀ f, (∃ c : F0, ((δ f : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) = Matrix.diagonal fun _ => c) ↔
      f ∈ Subgroup.zpowers (qTwoOneVec m h3) := by
    intro f
    rw [hδmat f]
    exact qTwoLMDivCoordInner_tor_scalar_aux h3 hu hord f
  have hsep : ∀ i j : Fin m, i ≠ j → ∃ f : ↥(sumZero m 3),
      (((δ f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i i ≠
        (((δ f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) j j)) := by
    intro i j hij
    refine ⟨rootV i j, ?_⟩
    have hne : ω ≠ 1 := by
      intro h
      rw [h] at hord
      norm_num at hord
    have hne2 : ω ≠ ω ^ 2 := by
      intro h
      have h' : ω = 1 := by
        have h2 := congrArg (fun x : F0ˣ => x * ω⁻¹) h
        rw [mul_inv_cancel, pow_two, mul_assoc, mul_inv_cancel, mul_one] at h2
        exact h2.symm
      exact hne h'
    rw [hδmat, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, uvec_apply, uvec_apply,
      crd_rootV_left hij, crd_rootV_right hij]
    simp only [ZMod.val_one, ZMod.val_neg_one, pow_one]
    intro h
    exact hne2 (Units.ext h)
  have hmono : ∀ u : GL (Fin m) F0, (∀ f, ∃ f', ∃ z : F0, z ≠ 0 ∧
      (u : Matrix (Fin m) (Fin m) F0) * ((δ f : GL (Fin m) F0) :
        Matrix (Fin m) (Fin m) F0) =
        z • ((δ f' : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          (u : Matrix (Fin m) (Fin m) F0)) →
      ∃ ρ : Equiv.Perm (Fin m), ∀ f, u * (δ f : GL (Fin m) F0) =
        (δ (permAutV ρ f) : GL (Fin m) F0) * u :=
    fun u hcen => qTwoLMDivCoordInner_tormono hdiag hperm hsep u hcen
  exact ⟨δ, hinj, hdiag, hsurj, hperm, hscalar, hmono⟩

end CFSG.StandardType.QTwo

end
