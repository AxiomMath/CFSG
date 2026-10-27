module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeAIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndDvd
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality

public section

namespace CFSG.StandardType.TypeANbrDvd

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.Assembly TypeA

variable {d p : ℕ} {K : Type} [Field K]

theorem slConjugation_toGL_eq (g h : SpecialLinearGroup (Fin d) K) :
    CatalogueBHigherLinearAction.slConjugation d K (SpecialLinearGroup.toGL g) h = g * h * g⁻¹ := by
  apply Subtype.ext
  rw [coe_slConjugation, ← map_inv]
  rfl

theorem permMatrix_mul_diagonal_mul_inv (σ : Equiv.Perm (Fin d)) (t : Fin d → K) :
    σ.permMatrix K * diagonal t * σ⁻¹.permMatrix K = diagonal (t ∘ σ) := by
  rw [permMatrix_mul_diagonal, Matrix.mul_assoc, ← permMatrix_mul, inv_mul_cancel, permMatrix_one,
    Matrix.mul_one]

theorem mul_conj_eq_conj_apply_mul {G : Type*} [Group G] (f : MulAut G) (g : G) :
    f * MulAut.conj g = MulAut.conj (f g) * f := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

section Acts

variable {L' : Type} [Group L'] (φ' : SpecialLinearGroup (Fin d) K →* L')

@[expose] def ActsDiag (a : MulAut L') (t : Fin d → K) : Prop :=
  ∃ D : GL (Fin d) K, (D : Matrix (Fin d) (Fin d) K) = diagonal t ∧
    ∀ s, a (φ' s) = φ' (CatalogueBHigherLinearAction.slConjugation d K D s)

variable {φ'}

theorem ActsDiag.ne_zero {a : MulAut L'} {t : Fin d → K} (ha : ActsDiag φ' a t) (k : Fin d) :
    t k ≠ 0 := by
  obtain ⟨D, hD, -⟩ := ha
  exact diag_ne_zero hD k

theorem actsDiag_one : ActsDiag φ' 1 (fun _ => (1 : K)) :=
  ⟨1, by rw [Units.val_one, diagonal_one], fun s => by
    rw [map_one, MulAut.one_apply, MulAut.one_apply]⟩

theorem ActsDiag.mul {a b : MulAut L'} {t u : Fin d → K} (ha : ActsDiag φ' a t)
    (hb : ActsDiag φ' b u) : ActsDiag φ' (a * b) (fun k => t k * u k) := by
  obtain ⟨D, hD, haD⟩ := ha
  obtain ⟨E, hE, hbE⟩ := hb
  refine ⟨D * E, ?_, act_mul haD hbE⟩
  rw [Units.val_mul, hD, hE, diagonal_mul_diagonal]

theorem ActsDiag.inv {a : MulAut L'} {t : Fin d → K} (ha : ActsDiag φ' a t) :
    ActsDiag φ' a⁻¹ (fun k => (t k)⁻¹) := by
  obtain ⟨D, hD, haD⟩ := ha
  refine ⟨D⁻¹, coe_inv_of_diagonal hD, fun s => ?_⟩
  have h := haD (CatalogueBHigherLinearAction.slConjugation d K D⁻¹ s)
  have e : CatalogueBHigherLinearAction.slConjugation d K D
      (CatalogueBHigherLinearAction.slConjugation d K D⁻¹ s) = s := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  rw [e] at h
  rw [← h, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem ActsDiag.pow {a : MulAut L'} {t : Fin d → K} (ha : ActsDiag φ' a t) (n : ℕ) :
    ActsDiag φ' (a ^ n) (fun k => t k ^ n) := by
  obtain ⟨D, hD, haD⟩ := ha
  refine ⟨D ^ n, ?_, act_pow haD n⟩
  rw [Units.val_pow_eq_pow_val, hD, diagonal_pow]
  rfl

theorem ActsDiag.unique (hφ's : Function.Surjective φ') {a b : MulAut L'} {t : Fin d → K}
    (ha : ActsDiag φ' a t) (hb : ActsDiag φ' b t) : a = b := by
  obtain ⟨D, hD, haD⟩ := ha
  obtain ⟨E, hE, hbE⟩ := hb
  have hDE : D = E := Units.ext (hD.trans hE.symm)
  subst hDE
  ext l
  obtain ⟨s, rfl⟩ := hφ's l
  rw [haD, hbE]

theorem ActsDiag.ratio (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {a : MulAut L'}
    {t t' : Fin d → K} (ha : ActsDiag φ' a t) (ha' : ActsDiag φ' a t') {k l : Fin d}
    (hkl : k ≠ l) : t k * (t l)⁻¹ = t' k * (t' l)⁻¹ := by
  obtain ⟨D, hD, haD⟩ := ha
  obtain ⟨E, hE, haE⟩ := ha'
  exact ratio_eq_of_act hφker hD hE (fun s => (haD s).symm.trans (haE s)) hkl

theorem ActsDiag.ratio_pow (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {a : MulAut L'}
    {t : Fin d → K} (ha : ActsDiag φ' a t) (hap : a ^ p = 1) (k l : Fin d) :
    (t k * (t l)⁻¹) ^ p = 1 := by
  by_cases hkl : k = l
  · rw [hkl, mul_inv_cancel₀ (ha.ne_zero l), one_pow]
  have h1 : ActsDiag φ' (a ^ p) (fun _ => (1 : K)) := by rw [hap]; exact actsDiag_one
  have h2 := (ha.pow p).ratio hφker h1 hkl
  simp only [inv_one, mul_one] at h2
  rw [mul_pow, inv_pow, h2]

theorem ActsDiag.eq_one (hd : 0 < d) (hφ's : Function.Surjective φ') {a : MulAut L'}
    {t : Fin d → K} (ha : ActsDiag φ' a t) (hc : ∀ k l, t k = t l) : a = 1 := by
  obtain ⟨D, hD, haD⟩ := ha
  ext l
  obtain ⟨s, rfl⟩ := hφ's l
  rw [haD, slConjugation_eq_self_of_const hD (fun k => hc k ⟨0, hd⟩) (diag_ne_zero hD ⟨0, hd⟩),
    MulAut.one_apply]

theorem ActsDiag.apply_of_isDiag {a : MulAut L'} {t : Fin d → K} (ha : ActsDiag φ' a t)
    {s : SpecialLinearGroup (Fin d) K} (hs : (s : Matrix (Fin d) (Fin d) K).IsDiag) :
    a (φ' s) = φ' s := by
  obtain ⟨E, hE, haE⟩ := ha
  rw [haE]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_inv_of_diagonal hE, hE, ← (isDiag_iff_diagonal_diag _).mp hs,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext k
  rw [mul_comm (t k), mul_assoc, mul_inv_cancel₀ (diag_ne_zero hE k), mul_one]

theorem ActsDiag.mul_conj_comm {a : MulAut L'} {t : Fin d → K} (ha : ActsDiag φ' a t)
    {s : SpecialLinearGroup (Fin d) K} (hs : (s : Matrix (Fin d) (Fin d) K).IsDiag) :
    a * MulAut.conj (φ' s) = MulAut.conj (φ' s) * a := by
  rw [mul_conj_eq_conj_apply_mul, ha.apply_of_isDiag hs]

theorem actsDiag_conj {D : SpecialLinearGroup (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) :
    ActsDiag φ' (MulAut.conj (φ' D)) t :=
  ⟨SpecialLinearGroup.toGL D, hD, fun s => by
    rw [MulAut.conj_apply, slConjugation_toGL_eq, map_mul, map_mul, map_inv]⟩

theorem ggActsBy_of_actsDiag {a : MulAut L'} {D : SpecialLinearGroup (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) (ha : ActsDiag φ' a t) :
    GGActsBy φ' a D := by
  obtain ⟨E, hE, haE⟩ := ha
  have hED : E = SpecialLinearGroup.toGL D := Units.ext (hE.trans hD.symm)
  intro s
  rw [haE, hED, slConjugation_toGL_eq]

theorem pow_eq_one_of_diagonal {D : SpecialLinearGroup (Fin d) K} {u : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal u) (hu : ∀ i, u i ^ p = 1) : D ^ p = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hD, diagonal_pow, Matrix.SpecialLinearGroup.coe_one]
  have e : u ^ p = fun _ => (1 : K) := by
    funext i
    exact hu i
  rw [e, diagonal_one]

variable [CharP K 2]

theorem ActsDiag.conj_perm {a : MulAut L'} {t : Fin d → K} (ha : ActsDiag φ' a t)
    (σ : Equiv.Perm (Fin d)) :
    ActsDiag φ' (MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹) (t ∘ σ) := by
  obtain ⟨D, hD, haD⟩ := ha
  refine ⟨SpecialLinearGroup.toGL (permSL σ) * D * SpecialLinearGroup.toGL ((permSL σ)⁻¹), ?_,
    fun s => ?_⟩
  · rw [Units.val_mul, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
      SpecialLinearGroup.coe_GL_coe_matrix, permSL_inv, coe_permSL, coe_permSL, hD,
      permMatrix_mul_diagonal_mul_inv]
  · have e : CatalogueBHigherLinearAction.slConjugation d K
        (SpecialLinearGroup.toGL (permSL σ) * D * SpecialLinearGroup.toGL ((permSL σ)⁻¹)) s =
        permSL σ * CatalogueBHigherLinearAction.slConjugation d K D ((permSL σ)⁻¹ * s * permSL σ) *
          (permSL σ)⁻¹ := by
      rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, slConjugation_toGL_eq,
        slConjugation_toGL_eq, inv_inv]
    rw [e, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, ← map_inv, ← map_mul,
      ← map_mul, haD, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]

end Acts

theorem exists_actsDiag_model (hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤)
    (hsec : SLHasSections d K) {L' : Type} [Group L'] {ψ : L' →* projectiveSL d K}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')}
    (hAI : ∀ a ∈ A, ∃ φa ∈ Set.range (conjAut d K), ∀ l, φa (ψ l) = ψ (a l))
    {A₀ : GL (Fin d) K}
    (hA₀ : ∀ B : GL (Fin d) K, conjAut d K B ∈ inducedSub ψ A → ∀ i j, i ≠ j →
      ((A₀ : Matrix (Fin d) (Fin d) K) * (B : Matrix (Fin d) (Fin d) K) *
        ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i j = 0) :
    ∃ φ' : SpecialLinearGroup (Fin d) K →* L', Function.Surjective φ' ∧
      (∀ g, φ' g = 1 → g ∈ scalars d K) ∧ ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t := by
  obtain ⟨φ, hφs, hφ⟩ := exists_sl_cover hsec ψ hψ hker hperf
  set c₀ := CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹ with hc₀
  set φ' := φ.comp c₀.toMonoidHom with hφ'
  refine ⟨φ', hφs.comp c₀.surjective, ?_, ?_⟩
  · intro g hg
    have h1 : proj d K (c₀ g) = 1 := by
      rw [← hφ]
      change ψ (φ' g) = 1
      rw [hg, map_one]
    exact mem_scalars_of_slConjugation_mem A₀⁻¹ (proj_eq_one_iff.mp h1)
  · intro a ha
    obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a ha
    have hBX : conjAut d K B ∈ inducedSub ψ A := ⟨a, ha, hφa⟩
    set D := A₀ * B * A₀⁻¹ with hD
    refine ⟨fun i => (D : Matrix (Fin d) (Fin d) K) i i, D,
      CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag fun i j hij => by
        rw [hD, Units.val_mul, Units.val_mul]
        exact hA₀ B hBX i j hij, fun s => ?_⟩
    have h1 := act_of_lift_GL hperfSL hker hφ hφa (c₀ s)
    change a (φ (c₀ s)) = φ (c₀ (CatalogueBHigherLinearAction.slConjugation d K D s))
    rw [h1, hc₀, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, hD]
    congr 2
    group

end CFSG.StandardType.TypeANbrDvd

end
