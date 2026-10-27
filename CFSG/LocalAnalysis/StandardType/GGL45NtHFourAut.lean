module

public import CFSG.LocalAnalysis.StandardType.GGL45NtNonab

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggL45NtHFourAut_eq_inducedAut_of_largeEvenInduces
    {K : Type*} [Group K] {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R)
    (ψ : MulAut K) (φ : MulAut R)
    (h : LargeEvenInduces θ (fun k k' => k' = ψ k) φ) : φ = ggInducedAut θ ψ := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l => rw [ggInducedAut_apply]; exact h l (ψ l) rfl

theorem ggL45H4Raw_of_aut {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} {R : Type} [Group R]
    {I F : Set (MulAut R)} (hsimp : GGL45NtSimp R I F) (h : GGL45NtAut p R I F) :
    GGL45H4Raw p lab R I F := by
  intro K _ _ θ hK ψ E hyp
  have hnab := ggL45Nt_nonabelian_of_kghyp hp θ hK hyp
  obtain ⟨⟨J, hJn, hJI⟩, hAut⟩ := h (hsimp hnab) hnab
  obtain ⟨f, hf, u, hu, hord, hind⟩ := hyp.2.1
  have heq : ggInducedAut θ ψ = u * f * u⁻¹ :=
    (ggL45NtHFourAut_eq_inducedAut_of_largeEvenInduces θ ψ (u * f * u⁻¹) hind).symm
  intro α hαp _hαE hαI hαpI
  obtain ⟨j, hj, hjI⟩ := hAut α hαp hαI hαpI f hf hord
  refine ⟨j, hj, ?_⟩
  rw [heq, ← hJI]
  have huJ : u ∈ J := by
    change u ∈ (J : Set (MulAut R))
    rw [hJI]
    exact hu
  have hgJ : α * (f ^ j)⁻¹ ∈ J := by
    change α * (f ^ j)⁻¹ ∈ (J : Set (MulAut R))
    rw [hJI]
    exact hjI
  have hconjJ : f ^ j * u * (f ^ j)⁻¹ ∈ J := hJn.conj_mem u huJ (f ^ j)
  have huinvJ : u⁻¹ ∈ J := J.inv_mem huJ
  have hsplit : α * ((u * f * u⁻¹) ^ j)⁻¹ =
      (α * (f ^ j)⁻¹) * (f ^ j * u * (f ^ j)⁻¹) * u⁻¹ := by
    rw [conj_pow]
    group
  rw [hsplit]
  exact J.mul_mem (J.mul_mem hgJ hconjJ) huinvJ

end CFSG.StandardType
