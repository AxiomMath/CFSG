module

public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactURoot
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUAut
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelUFixSemi
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

private lemma spUFix_suTv_val (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} {e : Fin m → F}
    (he : herm (unitaryInvolution F 2 n) e e = 0) {s : F}
    (hs : s + unitaryInvolution F 2 n s = 0) :
    (((suTv (isUnitaryInvolution_unitaryInvolution hF) e s :
        ↥(SUid (unitaryInvolution F 2 n) m)) : GL (Fin m) F) :
      Matrix (Fin m) (Fin m) F) =
      1 + s • vecMulVec e (unitaryInvolution F 2 n ∘ e) := by
  rw [suTv, dif_pos ⟨he, hs⟩]
  rfl

private lemma spUFix_herm_comp {σ τ : F ≃+* F} (h : ∀ c, σ (τ c) = τ (σ c)) {m : ℕ}
    (v w : Fin m → F) : herm τ (σ ∘ v) (σ ∘ w) = σ (herm τ v w) := by
  simp only [herm]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Function.comp_apply, Function.comp_apply, map_mul, h]

private lemma spUFix_herm_mulVec (h : UnitaryFieldData 2 n F) {m : ℕ} {A : GL (Fin m) F}
    (hA : ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ * (A : Matrix (Fin m) (Fin m) F) = 1)
    (x y : Fin m → F) :
    herm (unitaryInvolution F 2 n) ((A : Matrix (Fin m) (Fin m) F) *ᵥ x)
        ((A : Matrix (Fin m) (Fin m) F) *ᵥ y) = herm (unitaryInvolution F 2 n) x y := by
  have hbar : ∀ c : F, h.bar c = unitaryInvolution F 2 n c := by
    intro c; rw [h.bar_apply, unitaryInvolution_apply]
  have hmap : (A : Matrix (Fin m) (Fin m) F).map (unitaryInvolution F 2 n) =
      (A : Matrix (Fin m) (Fin m) F).map h.bar := by
    ext i j; exact (hbar _).symm
  have hA' : conjTr (unitaryInvolution F 2 n) (A : Matrix (Fin m) (Fin m) F) *
      (A : Matrix (Fin m) (Fin m) F) = 1 := by
    rw [conjTr, hmap]; exact hA
  rw [herm_mulVec, hA', Matrix.one_mulVec]

private theorem spUFix_ud_conj_val (h : UnitaryFieldData 2 n F) {σ : F ≃+* F} {m : ℕ}
    {A : GL (Fin m) F}
    (hA : ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ * (A : Matrix (Fin m) (Fin m) F) = 1)
    {u : Fin m → F} {b : F} {N : StatedSU m (2 ^ n) F}
    (hN : (N : GL (Fin m) F).val = 1 + b • vecMulVec u (h.bar ∘ u)) :
    (A * glAut σ (N : GL (Fin m) F) * A⁻¹ : GL (Fin m) F).val =
      1 + σ b • vecMulVec ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u))
        (h.bar ∘ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u))) := by
  have hAinv : (A⁻¹ : GL (Fin m) F).val =
      ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ := by
    calc (A⁻¹ : GL (Fin m) F).val
        = ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ *
            (A : GL (Fin m) F).val * (A⁻¹ : GL (Fin m) F).val := by rw [hA, one_mul]
      _ = ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ *
            ((A : GL (Fin m) F).val * (A⁻¹ : GL (Fin m) F).val) := by rw [mul_assoc]
      _ = ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hAmulT : (A : Matrix (Fin m) (Fin m) F) *
      ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ = 1 := by
    rw [← hAinv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hWmap : (vecMulVec u (h.bar ∘ u)).map σ =
      vecMulVec (σ ∘ u) (σ ∘ (h.bar ∘ u)) := by
    ext i j
    simp [Matrix.map_apply, vecMulVec_apply]
  have hσbar : σ ∘ (h.bar ∘ u) = h.bar ∘ (σ ∘ u) := by
    funext i
    simp only [Function.comp_apply]
    rw [h.bar_apply, map_pow, h.bar_apply]
  have hmapN : ((N : GL (Fin m) F).val.map σ) =
      1 + σ b • vecMulVec (σ ∘ u) (σ ∘ (h.bar ∘ u)) := by
    rw [hN, Matrix.map_add σ (fun a b => map_add σ a b),
      Matrix.map_one σ (map_zero σ) (map_one σ),
      Matrix.map_smul' σ b (vecMulVec u (h.bar ∘ u)) (fun a b => map_mul σ a b), hWmap]
  have hmapmul : (A : Matrix (Fin m) (Fin m) F).map h.bar *ᵥ (h.bar ∘ (σ ∘ u)) =
      h.bar ∘ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u)) := by
    funext i
    exact (RingHom.map_mulVec h.bar (A : Matrix (Fin m) (Fin m) F) (σ ∘ u) i).symm
  have key : (A : Matrix (Fin m) (Fin m) F) * vecMulVec (σ ∘ u) (σ ∘ (h.bar ∘ u)) *
      ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ =
      vecMulVec ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u))
        (h.bar ∘ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u))) := by
    rw [hσbar, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hmapmul]
  have hcoe : (A * glAut σ (N : GL (Fin m) F) * A⁻¹ : GL (Fin m) F).val =
      (A : Matrix (Fin m) (Fin m) F) * ((N : GL (Fin m) F).val.map σ) *
        ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ := by
    rw [Units.val_mul, Units.val_mul,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut, hAinv]
  rw [hcoe, hmapN, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul,
    Matrix.smul_mul, hAmulT, key]

private lemma spUFix_semilinear_map_suProjTv (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    (h : UnitaryFieldData 2 n F) {σ : F ≃+* F} {A : GL (Fin m) F}
    (hA : ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ * (A : Matrix (Fin m) (Fin m) F) = 1)
    {α : MulAut (StatedProj (StatedSU m (2 ^ n) F))}
    (hAg : ∀ g : StatedSU m (2 ^ n) F,
      ∃ hg : A * glAut σ (g : GL (Fin m) F) * A⁻¹ ∈ StatedSU m (2 ^ n) F,
        α (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩)
    {e : Fin m → F} (he : herm (unitaryInvolution F 2 n) e e = 0) {s : F}
    (hs : s + unitaryInvolution F 2 n s = 0) :
    α (kFactsSuProjTv hF m e s) =
      kFactsSuProjTv hF m ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ e)) (σ s) := by
  set σ₀ := unitaryInvolution F 2 n
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have hbar : ∀ c : F, h.bar c = σ₀ c := by
    intro c; rw [h.bar_apply, unitaryInvolution_apply]
  have hvec : (σ₀ ∘ e) = (h.bar ∘ e) := by funext i; exact (hbar (e i)).symm
  have hcomm : ∀ c : F, σ (σ₀ c) = σ₀ (σ c) := by
    intro c
    rw [show σ₀ c = c ^ 2 ^ n by rw [unitaryInvolution_apply], map_pow, unitaryInvolution_apply]
  let E : ↥(SUid σ₀ m) ≃* StatedSU m (2 ^ n) F :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hF m)
  let N : ↥(SUid σ₀ m) := suTv hσ e s
  let N' : StatedSU m (2 ^ n) F := E N
  have hNval : (N : GL (Fin m) F).val = 1 + s • vecMulVec e (h.bar ∘ e) := by
    have h1 : ((N : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        1 + s • vecMulVec e (σ₀ ∘ e) := spUFix_suTv_val hF he hs
    rw [h1, hvec]
  have hN'val : (N' : GL (Fin m) F).val = 1 + s • vecMulVec e (h.bar ∘ e) := by
    change ((E N : StatedSU m (2 ^ n) F) : GL (Fin m) F).val = _
    rw [show ((E N : StatedSU m (2 ^ n) F) : GL (Fin m) F) = (N : GL (Fin m) F) from
      MulEquiv.subgroupCongr_apply (SUid_eq_statedSU hF m) N]
    exact hNval
  have hkFacts : kFactsSuProjTv hF m e s = QuotientGroup.mk N' := rfl
  obtain ⟨hg, hge⟩ := hAg N'
  rw [hkFacts, hge]
  have hψe_iso : herm σ₀ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ e))
      ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ e)) = 0 := by
    rw [spUFix_herm_mulVec h hA, spUFix_herm_comp hcomm, he, map_zero]
  have hσs : σ s + σ₀ (σ s) = 0 := by
    rw [← hcomm s, ← map_add, hs, map_zero]
  have hcomp_eq : (h.bar ∘ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ e))) =
      (σ₀ ∘ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ e))) := by
    funext i; exact hbar _
  have hmat1 : (A * glAut σ (N' : GL (Fin m) F) * A⁻¹ : GL (Fin m) F).val =
      1 + σ s • vecMulVec ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ e))
        (h.bar ∘ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ e))) :=
    spUFix_ud_conj_val h hA hN'val
  have hmat2 : (((suTv hσ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ e)) (σ s) :
        ↥(SUid σ₀ m)) : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      1 + σ s • vecMulVec ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ e))
        (σ₀ ∘ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ e))) :=
    spUFix_suTv_val hF hψe_iso hσs
  have hEeq : (⟨A * glAut σ (N' : GL (Fin m) F) * A⁻¹, hg⟩ : StatedSU m (2 ^ n) F) =
      E (suTv hσ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ e)) (σ s)) := by
    apply Subtype.ext
    apply Units.ext
    change (A * glAut σ (N' : GL (Fin m) F) * A⁻¹ : GL (Fin m) F).val =
      (((suTv hσ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ e)) (σ s) :
        ↥(SUid σ₀ m)) : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)
    rw [hmat1, hmat2, hcomp_eq]
  rw [hEeq]
  rfl

theorem spUFix_exists_semilinear_statedProjSU (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    (hm : 4 ≤ m) (α : MulAut (StatedProj (StatedSU m (2 ^ n) F))) (hα2 : α * α = 1)
    (hout : α ∉ (MulAut.conj : StatedProj (StatedSU m (2 ^ n) F) →*
      MulAut (StatedProj (StatedSU m (2 ^ n) F))).range) :
    ∃ (σ : F ≃+* F) (ψ : (Fin m → F) →+ (Fin m → F)), σ ≠ 1 ∧
      (∀ (c : F) (v : Fin m → F), ψ (c • v) = σ c • ψ v) ∧ Function.Injective ψ ∧
      (∀ v w, herm (unitaryInvolution F 2 n) v w = 0 →
        herm (unitaryInvolution F 2 n) (ψ v) (ψ w) = 0) ∧
      ∀ e, herm (unitaryInvolution F 2 n) e e = 0 →
        (spUFixRootU hF m e).map α.toMonoidHom = spUFixRootU hF m (ψ e) := by
  have h : UnitaryFieldData 2 n F :=
    { prime := Nat.prime_two
      one_le := by
        by_contra hn
        have hn0 : n = 0 := by omega
        subst hn0
        rw [pow_zero, one_pow] at hF
        have h2 : 1 < Nat.card F := Finite.one_lt_card
        omega
      card := by
        have h1 : (2 : ℕ) ^ (2 * n) = (2 ^ n) ^ 2 := by
          rw [Nat.mul_comm 2 n]
          exact pow_mul 2 n 2
        rw [hF, h1] }
  have hq : ¬(m = 3 ∧ 2 ^ n = 2) := by rintro ⟨h3, -⟩; omega
  obtain ⟨σ, A, hA, hAg⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.exists_unitary_semilinear_statedProj h
      (by omega : 3 ≤ m) hq α
  have hcomm : ∀ c : F, σ (unitaryInvolution F 2 n c) = unitaryInvolution F 2 n (σ c) := by
    intro c
    rw [unitaryInvolution_apply, map_pow, unitaryInvolution_apply]
  have hσ_ne : σ ≠ 1 := by
    intro hσeq
    apply hout
    have hgl : glAut (ι := Fin m) σ = glAut (ι := Fin m) (RingEquiv.refl F) := by
      rw [hσeq]; rfl
    have hα' : ∀ g : StatedSU m (2 ^ n) F,
        ∃ hg : A * glAut (RingEquiv.refl F) (g : GL (Fin m) F) * A⁻¹ ∈ StatedSU m (2 ^ n) F,
          α (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩ := by
      intro g
      obtain ⟨hg, hge⟩ := hAg g
      rw [← hgl]
      exact ⟨hg, hge⟩
    exact borel86_ufs_mem_range_conj_of_refl h hA hα' hα2
  let ψ : (Fin m → F) →+ (Fin m → F) :=
    { toFun := fun v => (A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ v)
      map_zero' := by
        have h : σ ∘ (0 : Fin m → F) = 0 := by funext i; simp
        rw [h, Matrix.mulVec_zero]
      map_add' := by
        intro v w
        have h : σ ∘ (v + w) = σ ∘ v + σ ∘ w := by
          funext i; simp [Pi.add_apply, map_add]
        rw [h, Matrix.mulVec_add] }
  refine ⟨σ, ψ, hσ_ne, ?_, ?_, ?_, ?_⟩
  · intro c v
    change (A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ (c • v)) =
      σ c • ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ v))
    have h : σ ∘ (c • v) = σ c • (σ ∘ v) := by
      funext i; simp [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [h, Matrix.mulVec_smul]
  · intro v w hvw
    have h1 : (A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ v) =
        (A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ w) := hvw
    have h2 : σ ∘ v = σ ∘ w :=
      Matrix.mulVec_injective_of_isUnit (A.isUnit) h1
    funext i
    exact σ.injective (congrFun h2 i)
  · intro v w hvw
    change herm (unitaryInvolution F 2 n)
      ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ v))
      ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ w)) = 0
    rw [spUFix_herm_mulVec h hA, spUFix_herm_comp hcomm, hvw, map_zero]
  · intro e he
    rw [spUFixRootU, spUFixRootU, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨σ s, by rw [← hcomm s, ← map_add, hs, map_zero],
        spUFix_semilinear_map_suProjTv hF h hA hAg he hs⟩
    · rintro ⟨s', hs', rfl⟩
      have hs'' : σ.symm s' + unitaryInvolution F 2 n (σ.symm s') = 0 := by
        apply σ.injective
        rw [map_add, hcomm, RingEquiv.apply_symm_apply, hs', map_zero]
      refine ⟨kFactsSuProjTv hF m e (σ.symm s'), ⟨σ.symm s', hs'', rfl⟩, ?_⟩
      change α (kFactsSuProjTv hF m e (σ.symm s')) = kFactsSuProjTv hF m (ψ e) s'
      rw [spUFix_semilinear_map_suProjTv hF h hA hAg he hs'', RingEquiv.apply_symm_apply]
      rfl

end CFSG.LocalAnalysis.WeakClosure81

end
