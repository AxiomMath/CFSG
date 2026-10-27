module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDvdFrame
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDvdMono

public section

namespace CFSG.StandardType

namespace TableBUD

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher InndiagSU TableBUI
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)

variable {K : Type} [Field K] {d n : ℕ} (h : UnitaryFieldData 2 n K)

theorem glAut_scalar (φ : K ≃+* K) (c : Kˣ) :
    glAut φ (Matrix.GeneralLinearGroup.scalar (Fin d) c) =
      Matrix.GeneralLinearGroup.scalar (Fin d) (Units.map (φ : K →* K) c) := by
  apply Units.ext
  rw [coe_glAut, Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero φ)]
  rfl

theorem IsSemilin.inv {R : Type*} [Group R] {θ : ↥(unitarySU 2 n K d) →* R} {α : MulAut R}
    {B : GL (Fin d) K} {φ : K ≃+* K} (hα : IsSemilin θ α B φ) :
    IsSemilin θ α⁻¹ (glAut φ⁻¹ B⁻¹) φ⁻¹ := by
  intro u v huv
  have hv : (v : GL (Fin d) K) = glAut φ⁻¹ (B⁻¹ * (u : GL (Fin d) K) * B) := by
    rw [huv, map_mul, map_mul, map_inv, inv_inv]
  have h1 := hα v u (by
    rw [hv, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    group)
  rw [← h1, MulAut.inv_apply, MulEquiv.symm_apply_apply]

variable [Finite K]

theorem IsSemilin.eq_smul (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {Q : GL (Fin d) K} (hQ : Q ∈ primeFormUnitary h (idGram K d))
    {α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))} {M₁ M₂ : GL (Fin d) K}
    (hM₁ : M₁ ∈ primeFormUnitary h (idGram K d)) (hM₂ : M₂ ∈ primeFormUnitary h (idGram K d))
    {φ : K ≃+* K} (h1 : IsSemilin (frameMk h Q hQ) α M₁ φ)
    (h2 : IsSemilin (frameMk h Q hQ) α M₂ φ) :
    ∃ c : Kˣ, M₁ = Matrix.GeneralLinearGroup.scalar (Fin d) c * M₂ := by
  have hC := isPrimeFormGram_one (K := K) (n := d)
  have h3 := (TableBUD.IsSemilin.inv h2).mul h h1 hM₁
  rw [inv_mul_cancel, inv_mul_cancel, ← map_mul] at h3
  have hNu : glAut φ⁻¹ (M₂⁻¹ * M₁) ∈ primeFormUnitary h (idGram K d) :=
    glAut_mem_primeFormUnitary h hC _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hM₂) hM₁)
  obtain ⟨c, hc⟩ := mem_scalars_of_isSemilin_one h hK hd hdq hp hpq Q hQ hNu h3
  refine ⟨Units.map (φ : K →* K) c, ?_⟩
  have e1 : M₂⁻¹ * M₁ = glAut φ (Matrix.GeneralLinearGroup.scalar (Fin d) c) := by
    rw [hc, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  rw [glAut_scalar] at e1
  have hcc := TypeA.PGLTor.scalar_mul_comm (ι := Fin d) (Units.map (φ : K →* K) c) M₂
  calc M₁ = M₂ * (M₂⁻¹ * M₁) := by group
    _ = M₂ * Matrix.GeneralLinearGroup.scalar (Fin d) (Units.map (φ : K →* K) c) := by rw [e1]
    _ = _ := hcc.symm

theorem exists_conj_eq_smul_of_commute (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {Q : GL (Fin d) K} (hQ : Q ∈ primeFormUnitary h (idGram K d))
    {f e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))} {B : GL (Fin d) K}
    (hB : B ∈ primeFormUnitary h (idGram K d)) {φ : K ≃+* K} (hφp : φ ^ p = 1)
    (hf : IsSemilin (frameMk h Q hQ) f B φ) {σ : Fin d → Kˣ} (hσp : ∀ k, σ k ^ p = 1)
    (hσn : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1) (he : FrameAct h Q hQ e σ)
    (hfe : f * e = e * f) :
    ∃ c : Kˣ, B * diagHom d σ = Matrix.GeneralLinearGroup.scalar (Fin d) c * diagHom d σ * B := by
  have hσu := diagHom_mem_primeFormUnitary h hσn
  have h1 := hf.mul h he hσu
  rw [glAut_diagHom_of_pow hp hφp hσp, mul_one] at h1
  have h2 := IsSemilin.mul h he hf hB
  rw [map_one, MulAut.one_apply, one_mul, ← hfe] at h2
  obtain ⟨c, hc⟩ := IsSemilin.eq_smul h hK hd hdq hp hpq hQ (Subgroup.mul_mem _ hB hσu)
    (Subgroup.mul_mem _ hσu hB) h1 h2
  exact ⟨c, by rw [hc, mul_assoc]⟩

theorem exists_bstar_of_field (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hq : ¬(d = 3 ∧ 2 ^ n = 2)) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) {Q : GL (Fin d) K} (hQ : Q ∈ primeFormUnitary h (idGram K d))
    {Eb Eh : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hle : Eb ≤ Eh) (hEbD : Eb ≤ inndiagU h (by omega)) {i j : Fin d} (hij : i ≠ j)
    (hEbact : ∀ e ∈ Eb, ∃ σ : Fin d → Kˣ, σ i = σ j ∧ FrameAct h Q hQ e σ)
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))} (hfEh : f ∈ Eh)
    (hfD : f ∉ inndiagU h (by omega)) (hfp : f ^ p = 1) {β : Fin d → Kˣ}
    (hβu : diagHom d β ∈ primeFormUnitary h (idGram K d))
    (hsl : IsSemilin (frameMk h Q hQ) f (diagHom d β) (fieldFactorU h hd hq f)) :
    ∃ E' : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))),
      Eb < E' ∧ E' ≤ Eh ∧ ∃ V : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))),
        V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ φ ∈ E', ∀ v ∈ V, φ v ∈ V := by
  classical
  have := Fact.mk hp
  set φ := fieldFactorU h hd hq f with hφ
  have hφp : φ ^ p = 1 := by rw [hφ, ← map_pow, hfp, map_one]
  have hφ1 : φ ≠ 1 := by
    intro h1
    apply hfD
    rw [← ker_fieldFactorU h hd hq]
    exact h1
  have hN := prod_eq_of_semilin hK hn hd hdq hp hpq hQ hβu hφp hfp hsl i j
  set γ : K := ((β j : Kˣ) : K) * ((β i : Kˣ) : K)⁻¹ with hγ
  have hγq : γ ^ (2 ^ n + 1) = 1 := by
    rw [hγ, mul_pow, inv_pow, norm_eq_one_of_diagHom_mem h hβu j,
      norm_eq_one_of_diagHom_mem h hβu i, inv_one, one_mul]
  have hγN : TableBUF.partNorm φ γ p = 1 := by
    have e1 : ∀ k, ∏ l ∈ Finset.range p, (φ ^ l) ((β k : Kˣ) : K) =
        ((∏ l ∈ Finset.range p, Units.map ((φ ^ l : K ≃+* K) : K →* K) (β k) : Kˣ) : K) := by
      intro k
      rw [Units.coe_prod]
      rfl
    rw [TableBUF.partNorm, hγ]
    simp only [map_mul, map_inv₀, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    rw [e1 j, e1 i, hN]
    exact mul_inv_cancel₀ (Units.ne_zero _)
  obtain ⟨c₀, hc₀q, hc₀φ⟩ := TableBUF.exists_hilbert90_unitary (q := 2 ^ n) hK
    ((Nat.even_pow' (by omega)).mpr even_two) Nat.one_le_two_pow hp hφp hφ1 hγq hγN
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hc₀q
    exact zero_ne_one hc₀q
  set c : Kˣ := Units.mk0 c₀ hc₀0 with hc
  have hcq : c ^ (2 ^ n + 1) = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hc₀q, Units.val_one])
  have hcφ : Units.map (φ : K →* K) c = β j * (β i)⁻¹ * c := by
    apply Units.ext
    rw [Units.coe_map, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    exact hc₀φ
  set M : ↥(unitarySU 2 n K d) := ⟨TableBUM.monoSwap i j c, TableBUM.monoSwap_mem h hij hcq⟩
    with hM
  set m := frameMk h Q hQ M with hm
  have hEbm : ∀ e ∈ Eb, e m = m := by
    intro e he
    obtain ⟨σ, hσij, hfr⟩ := hEbact e he
    refine hfr.apply M M ?_
    change TableBUM.monoSwap i j c = diagHom d σ * TableBUM.monoSwap i j c * (diagHom d σ)⁻¹
    rw [TableBUM.commute_monoSwap hσij c, mul_inv_cancel_right]
  have hfm : f m = m := by
    refine hsl M M ?_
    change TableBUM.monoSwap i j c =
      diagHom d β * glAut φ (TableBUM.monoSwap i j c) * (diagHom d β)⁻¹
    rw [TableBUM.diagHom_conj_glAut_monoSwap hij φ β hcφ]
  have hE'F : Eb ⊔ Subgroup.zpowers f ≤ fixerSub m :=
    sup_le (fun e he => hEbm e he) ((Subgroup.zpowers_le).mpr hfm)
  obtain ⟨V, hV1, hV2, hV⟩ := exists_two_subgroup_of_fix
    (frameMk_monoSwap_ne_one (h := h) (Q := Q) (hQ := hQ) hij hcq)
    (frameMk_monoSwap_sq (h := h) (Q := Q) (hQ := hQ) hij hcq) (fun α hα => hE'F hα)
  refine ⟨Eb ⊔ Subgroup.zpowers f, lt_of_le_of_ne le_sup_left fun he => ?_,
    sup_le hle ((Subgroup.zpowers_le).mpr hfEh), V, hV1, hV2, hV⟩
  have h1 : f ∈ Eb ⊔ Subgroup.zpowers f := Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  rw [← he] at h1
  exact hfD (hEbD h1)

end TableBUD

end CFSG.StandardType
