module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkInE
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBPosition
public import CFSG.LocalAnalysis.StandardType.GGSuDvdRootGenWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial

private lemma permSU_inv_rowA {K : Type} [Field K] {n d : ℕ} (hK : UnitaryFieldData 2 n K)
    (σ : Equiv.Perm (Fin d)) :
    (permSU hK σ)⁻¹ = permSU hK σ⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_inv]
  exact (map_inv (CFSG.RankThree.Classical.permGL (K := K)) σ).symm

private lemma exists_diag_commutator_rowA
    {d n p : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 n K) (hd : 3 ≤ d)
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t) (hap : a ^ p = 1)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal fun _ => c)
    (σ : Equiv.Perm (Fin d)) :
    ∃ s : ↥(unitarySU 2 n K d),
      (∃ v : Fin d → K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
      s ^ p = 1 ∧ φ s = φ (permSU hK σ) * (a (φ (permSU hK σ)))⁻¹ := by
  have ha0 : ActsDiagU φ a t := ha
  obtain ⟨D, hD, hDt, hact⟩ := ha
  set P : ↥(unitarySU 2 n K d) := permSU hK σ with hP
  set s : ↥(unitarySU 2 n K d) := P * (conjN D hD P)⁻¹ with hs
  have hmat : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (fun k => t (σ⁻¹ k) * (t k)⁻¹) := by
    have hcoe : (s : GL (Fin d) K) = CFSG.RankThree.Classical.permGL σ *
        (D * CFSG.RankThree.Classical.permGL σ * D⁻¹)⁻¹ := by
      simp only [hs, hP, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjN, coe_permSU]
    have hs_eq : (s : GL (Fin d) K) = (CFSG.RankThree.Classical.permGL σ * D *
        (CFSG.RankThree.Classical.permGL σ)⁻¹) * D⁻¹ := by
      rw [hcoe]; group
    rw [hs_eq]
    simp only [Units.val_mul, coe_permGL_matrix, coe_permGL_inv_matrix, hDt, coe_inv_diag hDt]
    rw [permMatrix_conj_diag σ t, diagonal_mul_diagonal]
  refine ⟨s, ⟨fun k => t (σ⁻¹ k) * (t k)⁻¹, hmat⟩, ?_, ?_⟩
  · have hratio : ∀ k, (t (σ⁻¹ k) * (t k)⁻¹) ^ p = 1 := fun k =>
      ActsDiagU.ratio_pow hK hd hφker ha0 hap (σ⁻¹ k) k
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hmat, diagonal_pow]
    have hv : (fun k => t (σ⁻¹ k) * (t k)⁻¹) ^ p = fun _ => (1 : K) := by
      funext k
      exact hratio k
    rw [hv, diagonal_one, Units.val_one]
  · rw [hs, map_mul, map_inv, ← hact P]

theorem permSU_lift_mem_normalizer_rowA
    {d n p : ℕ} {K : Type} [Field K] (hd : 3 ≤ d)
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} (hpos : GGTableBPosition p L' E I θ hE)
    {φ : ↥(unitarySU 2 n K d) →* L'} (hφ : UnitTB.Model φ)
    (hdiag : ∀ e : E, ∃ t : Fin d → K, ActsDiagU φ (L'.normalizerMonoidHom ⟨e, hE e.2⟩) t)
    (σ : Equiv.Perm (Fin d)) :
    ((φ (permSU hφ.field σ) : L') : M) ∈ Subgroup.normalizer (E : Set M) := by
  classical
  have key : ∀ (τ : Equiv.Perm (Fin d)) (e : E),
      ((φ (permSU hφ.field τ) : L') : M) * (e : M) *
        (((φ (permSU hφ.field τ) : L') : M))⁻¹ ∈ E := by
    intro τ e
    obtain ⟨t, ht⟩ := hdiag e
    have hEp : (e : M) ^ p = 1 := hpos.2.1.2 (e : M) e.2
    have hxp : (⟨e, hE e.2⟩ : ↥(Subgroup.normalizer (L' : Set M))) ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hEp, Subgroup.coe_one]
    have hap : (L'.normalizerMonoidHom ⟨e, hE e.2⟩) ^ p = 1 := by
      rw [← map_pow (L'.normalizerMonoidHom) ⟨e, hE e.2⟩ p, hxp, map_one]
    obtain ⟨s, ⟨v, hv⟩, hsp, hφs⟩ :=
      exists_diag_commutator_rowA hφ.field hd ht hap hφ.ker τ
    have hmem : ((φ s : L') : M) ∈ E := map_diag_pTorsion_mem_E hpos hdiag s ⟨v, hv⟩ hsp
    set n : M := ((φ (permSU hφ.field τ) : L') : M) with hn
    have hcoe : (((L'.normalizerMonoidHom ⟨e, hE e.2⟩) (φ (permSU hφ.field τ)) : L') : M) =
        (e : M) * n * (e : M)⁻¹ := by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, ← hn]
    have hcomm : ((φ s : L') : M) = n * (e : M) * n⁻¹ * (e : M)⁻¹ := by
      rw [hφs, Subgroup.coe_mul, Subgroup.coe_inv, hcoe, ← hn]
      group
    rw [show n * (e : M) * n⁻¹ = ((φ s : L') : M) * (e : M) by rw [hcomm]; group]
    exact E.mul_mem hmem e.2
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key σ ⟨x, hx⟩
  · intro hx
    have hnin : ((φ (permSU hφ.field σ⁻¹) : L') : M) =
        (((φ (permSU hφ.field σ) : L') : M))⁻¹ := by
      rw [← permSU_inv_rowA hφ.field σ, map_inv, Subgroup.coe_inv]
    have h2 := key σ⁻¹ ⟨((φ (permSU hφ.field σ) : L') : M) * x *
      (((φ (permSU hφ.field σ) : L') : M))⁻¹, hx⟩
    rw [hnin] at h2
    convert h2 using 1
    group

end CFSG.StandardType
