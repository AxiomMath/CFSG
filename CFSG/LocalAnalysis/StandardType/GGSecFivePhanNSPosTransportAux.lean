module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LieType.Universal.Unitary.Hermitian
public import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

lemma ggNSPosPD_conj_fix_center {H : Type*} [Group H] {c z : H}
    (hz : z ∈ Subgroup.center H) : MulAut.conj c z = z := by
  rw [MulAut.conj_apply]
  have h : c * z = z * c := Subgroup.mem_center_iff.mp hz c
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

lemma ggNSPosPD_ker_comp_conj {G : Type} [Group G] [Finite G]
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) (c : Su K 2 f n) :
    (ψ.comp (MulAut.conj c).toMonoidHom).ker ≤ Subgroup.center (Su K 2 f n) := by
  intro x hx
  have hx' : MulAut.conj c x ∈ ψ.ker := hx
  have hc : MulAut.conj c x ∈ Subgroup.center (Su K 2 f n) := hker hx'
  have h2 : MulAut.conj c⁻¹ (MulAut.conj c x) = MulAut.conj c x :=
    ggNSPosPD_conj_fix_center hc
  have h3 : MulAut.conj c⁻¹ (MulAut.conj c x) = x := by
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  have hx_eq : x = MulAut.conj c x := h3.symm.trans h2
  rwa [hx_eq]

lemma ggNSPosPD_range_comp_conj {G : Type} [Group G] [Finite G]
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (c : Su K 2 f n) :
    (ψ.comp (MulAut.conj c).toMonoidHom).range = ψ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective, Subgroup.map_top]

lemma ggNSPosPD_unitary_mul {K : Type} [Field K] [Finite K] {f n : ℕ} [CharP K 2]
    {A B : GL (Fin n) K}
    (hA : ggIsUnitaryMat (p := 2) (f := f) A) (hB : ggIsUnitaryMat (p := 2) (f := f) B) :
    ggIsUnitaryMat (p := 2) (f := f) (A * B) := by
  show conjTr (unitaryInvolution K 2 f) ((A * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
  rw [Units.val_mul]
  set Am : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K)
  set Bm : Matrix (Fin n) (Fin n) K := (B : Matrix (Fin n) (Fin n) K)
  have hAm : conjTr (unitaryInvolution K 2 f) Am * Am = 1 := hA
  have hBm : conjTr (unitaryInvolution K 2 f) Bm * Bm = 1 := hB
  change conjTr (unitaryInvolution K 2 f) (Am * Bm) * (Am * Bm) = 1
  rw [conjTr_mul]
  have h1 : (conjTr (unitaryInvolution K 2 f) Bm * conjTr (unitaryInvolution K 2 f) Am) *
        (Am * Bm) =
      conjTr (unitaryInvolution K 2 f) Bm * (conjTr (unitaryInvolution K 2 f) Am * Am) * Bm := by
    noncomm_ring
  rw [h1, hAm, Matrix.mul_one, hBm]

lemma ggNSPosPD_unitary_inv {K : Type} [Field K] [Finite K] {f n : ℕ} [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) {A : GL (Fin n) K}
    (hA : ggIsUnitaryMat (p := 2) (f := f) A) :
    ggIsUnitaryMat (p := 2) (f := f) A⁻¹ := by
  have hAinv : conjTr (unitaryInvolution K 2 f) ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.coe_units_inv]
    exact (Matrix.inv_eq_left_inv hA).symm
  have hconj : conjTr (unitaryInvolution K 2 f)
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← hAinv]
    exact conjTr_conjTr (unitaryInvolution_involutive hK)
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  show conjTr (unitaryInvolution K 2 f) ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
  rw [hconj, ← Units.val_mul, mul_inv_cancel, Units.val_one]

lemma ggNSPosPD_unitary_conj {K : Type} [Field K] [Finite K] {f n : ℕ} [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (c : Su K 2 f n) {g : GL (Fin n) K}
    (hg : ggIsUnitaryMat (p := 2) (f := f) g) :
    ggIsUnitaryMat (p := 2) (f := f)
      (((c : GL (Fin n) K)⁻¹) * g * ((c : GL (Fin n) K))) := by
  have hc : ggIsUnitaryMat (p := 2) (f := f) ((c : Su K 2 f n) : GL (Fin n) K) := c.2.2
  have hci : ggIsUnitaryMat (p := 2) (f := f) (((c : Su K 2 f n) : GL (Fin n) K)⁻¹) :=
    ggNSPosPD_unitary_inv hK hc
  exact ggNSPosPD_unitary_mul (ggNSPosPD_unitary_mul hci hg) hc

lemma ggNSPosPD_acts_conj {G : Type} [Group G] [Finite G]
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    {Bs : Subgroup G} (hK : Nat.card K = (2 ^ f) ^ 2) (c : Su K 2 f n)
    (hacts : GGActsUnitarily (p := 2) (f := f) ψ Bs) :
    GGActsUnitarily (p := 2) (f := f) (ψ.comp (MulAut.conj c).toMonoidHom) Bs := by
  intro b hb
  obtain ⟨g, hgu, hgi⟩ := hacts b hb
  refine ⟨((c : GL (Fin n) K)⁻¹ * g * (c : GL (Fin n) K)), ?_⟩
  refine ⟨ggNSPosPD_unitary_conj hK c hgu, ?_⟩
  intro x
  obtain ⟨y₀, hy₀_mat, hy₀_eq⟩ := hgi (MulAut.conj c x)
  refine ⟨MulAut.conj c⁻¹ y₀, ?_, ?_⟩
  · have hφy_mat : ((MulAut.conj c⁻¹ y₀ : Su K 2 f n) : GL (Fin n) K) =
        ((c : GL (Fin n) K))⁻¹ * (y₀ : GL (Fin n) K) * (c : GL (Fin n) K) := by
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    have hφx : ((MulAut.conj c x : Su K 2 f n) : GL (Fin n) K) =
        (c : GL (Fin n) K) * (x : GL (Fin n) K) * ((c : GL (Fin n) K))⁻¹ := by
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [hφy_mat, hy₀_mat, hφx]
    group
  · have hφy : MulAut.conj c (MulAut.conj c⁻¹ y₀) = y₀ := by
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    have hψy : ψ (MulAut.conj c (MulAut.conj c⁻¹ y₀)) = ψ y₀ := congrArg ψ hφy
    show b * ψ (MulAut.conj c x) * b⁻¹ = ψ (MulAut.conj c (MulAut.conj c⁻¹ y₀))
    rw [hψy]
    exact hy₀_eq

end CFSG.StandardType

end
