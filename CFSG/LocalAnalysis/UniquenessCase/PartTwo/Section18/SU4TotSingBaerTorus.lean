module

public import CFSG.ClassicalGroups.Unitary.Form
import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Unitary CFSG.Open
open CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.RankThreeUC
open scoped Matrix

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F} {n p : ℕ}

private def baerVec_T1J5 (a b : Fˣ) : Fin 4 → F :=
  ![(a : F), ((a⁻¹ : Fˣ) : F), (b : F), ((b⁻¹ : Fˣ) : F)]

private theorem baerVec_det_T1J5 (a b : Fˣ) : ∏ i, baerVec_T1J5 a b i = 1 := by
  rw [Fin.prod_univ_four]
  simp [baerVec_T1J5]

private theorem baerVec_norm_T1J5 {Z : Subgroup Fˣ} (hZ : ∀ a ∈ Z, σ (a : F) * a = 1)
    {a b : Fˣ} (ha : a ∈ Z) (hb : b ∈ Z) (i : Fin 4) :
    σ (baerVec_T1J5 a b i) * baerVec_T1J5 a b i = 1 := by
  fin_cases i
  · exact hZ a ha
  · exact hZ a⁻¹ (Z.inv_mem ha)
  · exact hZ b hb
  · exact hZ b⁻¹ (Z.inv_mem hb)

private theorem baerVec_mul_T1J5 (a a' b b' : Fˣ) (i : Fin 4) :
    baerVec_T1J5 (a * a') (b * b') i = baerVec_T1J5 a b i * baerVec_T1J5 a' b' i := by
  fin_cases i <;> simp [baerVec_T1J5, Units.val_mul, mul_inv, mul_comm]

private noncomputable def baerTorusSU_T1J5 (Z : Subgroup Fˣ)
    (hZ : ∀ a ∈ Z, σ (a : F) * a = 1) : ↥Z × ↥Z →* ↥(SUid σ 4) where
  toFun x := diagSU σ (baerVec_T1J5 (x.1 : Fˣ) (x.2 : Fˣ))
    (baerVec_norm_T1J5 hZ x.1.2 x.2.2) (baerVec_det_T1J5 _ _)
  map_one' := by
    apply ext_smul
    intro v
    rw [diagSU_smul, one_smul]
    funext i
    fin_cases i <;> simp [baerVec_T1J5]
  map_mul' x y := by
    apply ext_smul
    intro v
    rw [mul_smul, diagSU_smul, diagSU_smul, diagSU_smul]
    funext i
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    rw [baerVec_mul_T1J5, mul_assoc]

private theorem baerTorusSU_smul_T1J5 (Z : Subgroup Fˣ)
    (hZ : ∀ a ∈ Z, σ (a : F) * a = 1) (x : ↥Z × ↥Z) (v : Fin 4 → F) :
    baerTorusSU_T1J5 Z hZ x • v =
      fun i => baerVec_T1J5 (x.1 : Fˣ) (x.2 : Fˣ) i * v i :=
  diagSU_smul σ _ (baerVec_norm_T1J5 hZ x.1.2 x.2.2) (baerVec_det_T1J5 _ _) v

private theorem baerTorusSU_injective_T1J5 (Z : Subgroup Fˣ)
    (hZ : ∀ a ∈ Z, σ (a : F) * a = 1) : Function.Injective (baerTorusSU_T1J5 Z hZ) := by
  intro x y h
  have h1 := congrArg (fun g => g • (Pi.single 0 1 : Fin 4 → F)) h
  have h2 := congrArg (fun g => g • (Pi.single 2 1 : Fin 4 → F)) h
  simp only [baerTorusSU_smul_T1J5] at h1 h2
  have e1 := congrFun h1 0
  have e2 := congrFun h2 2
  simp [baerVec_T1J5] at e1 e2
  exact Prod.ext (Subtype.ext (Units.ext e1)) (Subtype.ext (Units.ext e2))

private theorem baerTorusSU_smul_e0_T1J5 (Z : Subgroup Fˣ)
    (hZ : ∀ a ∈ Z, σ (a : F) * a = 1) (x : ↥Z × ↥Z) :
    baerTorusSU_T1J5 Z hZ x • (Pi.single 0 1 : Fin 4 → F) =
      ((x.1 : Fˣ) : F) • (Pi.single 0 1 : Fin 4 → F) := by
  rw [baerTorusSU_smul_T1J5]
  funext i
  fin_cases i <;> simp [baerVec_T1J5]

private theorem baerTorusSU_smul_e1_T1J5 (Z : Subgroup Fˣ)
    (hZ : ∀ a ∈ Z, σ (a : F) * a = 1) (x : ↥Z × ↥Z) :
    baerTorusSU_T1J5 Z hZ x • (Pi.single 1 1 : Fin 4 → F) =
      (((x.1 : Fˣ) : F))⁻¹ • (Pi.single 1 1 : Fin 4 → F) := by
  rw [baerTorusSU_smul_T1J5]
  funext i
  fin_cases i <;> simp [baerVec_T1J5, Units.val_inv_eq_inv_val]

private def baerAdd_T1J5 (σ : F ≃+* F) (z : Fin 4 → Fin 4 → F) : F →+ (Fin 4 → F) where
  toFun α := α • z 0 + σ α • z 1
  map_zero' := by simp
  map_add' α β := by
    simp only [map_add, add_smul]
    abel

private theorem baerAdd_mem_T1J5 (σ : F ≃+* F) (z : Fin 4 → Fin 4 → F) (x : Fin 4 → F) :
    x ∈ (baerAdd_T1J5 σ z).range ↔ ∃ α : F, x = α • z 0 + σ α • z 1 := by
  rw [AddMonoidHom.mem_range]
  exact exists_congr fun α => eq_comm

private theorem baerBasisMat_T1J5 (z : Fin 4 → Fin 4 → F)
    (hz : ∀ i j, herm σ (z i) (z j) = if i = j then 1 else 0) :
    ∃ T : Matrix (Fin 4) (Fin 4) F,
      conjTr σ T * T = 1 ∧ (∀ i, T *ᵥ (Pi.single i 1 : Fin 4 → F) = z i) ∧
      σ T.det * T.det = 1 := by
  let T : Matrix (Fin 4) (Fin 4) F := Matrix.of fun r i => z i r
  have hTsmul : ∀ i : Fin 4, T *ᵥ (Pi.single i 1 : Fin 4 → F) = z i := by
    intro i
    rw [Matrix.mulVec_single_one]
    funext r
    simp [T, Matrix.col_apply]
  have hTiso : conjTr σ T * T = 1 := by
    ext i k
    rw [Matrix.mul_apply, Matrix.one_apply,
      show (∑ r, conjTr σ T i r * T r k) = herm σ (z i) (z k) by simp [herm, conjTr, T],
      hz i k]
  have hδ : σ T.det * T.det = 1 := by
    have h := congrArg Matrix.det hTiso
    rw [Matrix.det_mul, Matrix.det_one] at h
    have h2 : (conjTr σ T).det = σ T.det := by
      rw [conjTr, Matrix.det_transpose]
      exact (RingHom.map_det σ.toRingHom T).symm
    rwa [h2] at h
  exact ⟨T, hTiso, hTsmul, hδ⟩

private theorem baerDiagMat_T1J5 (δ : F) (hδ : σ δ * δ = 1) :
    ∃ D : Matrix (Fin 4) (Fin 4) F,
      D.det = δ⁻¹ ∧ conjTr σ D * D = 1 ∧
      D *ᵥ (Pi.single 0 1 : Fin 4 → F) = Pi.single 0 1 ∧
      D *ᵥ (Pi.single 1 1 : Fin 4 → F) = Pi.single 1 1 := by
  let D : Matrix (Fin 4) (Fin 4) F := Matrix.diagonal (![1, 1, 1, δ⁻¹] : Fin 4 → F)
  have hDnormδ : (σ δ)⁻¹ * δ⁻¹ = 1 := by
    rw [(mul_inv_rev δ (σ δ)).symm, mul_comm δ (σ δ), hδ, inv_one]
  have hDnorm : ∀ i, σ (![1, 1, 1, δ⁻¹] i) * ![1, 1, 1, δ⁻¹] i = 1 := by
    intro i
    fin_cases i <;> simp [hDnormδ]
  have hDiso : conjTr σ D * D = 1 := by
    apply conjTr_mul_self_of_isometry
    intro x y
    simp only [D, herm, Matrix.mulVec_diagonal, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (σ (x i) * y i) * hDnorm i
  have hDdet : D.det = δ⁻¹ := by
    simp only [D, Matrix.det_diagonal, Fin.prod_univ_four]
    simp
  have hD0 : D *ᵥ (Pi.single 0 1 : Fin 4 → F) = Pi.single 0 1 := by
    simp only [D, Matrix.diagonal_mulVec_single]
    simp
  have hD1 : D *ᵥ (Pi.single 1 1 : Fin 4 → F) = Pi.single 1 1 := by
    simp only [D, Matrix.diagonal_mulVec_single]
    simp
  exact ⟨D, hDdet, hDiso, hD0, hD1⟩

private theorem baerFrameMat_T1J5 (z : Fin 4 → Fin 4 → F)
    (hz : ∀ i j, herm σ (z i) (z j) = if i = j then 1 else 0) :
    ∃ T' : Matrix (Fin 4) (Fin 4) F,
      T'.det = 1 ∧ conjTr σ T' * T' = 1 ∧
      T' *ᵥ (Pi.single 0 1 : Fin 4 → F) = z 0 ∧
      T' *ᵥ (Pi.single 1 1 : Fin 4 → F) = z 1 := by
  obtain ⟨T, hTiso, hTsmul, hδ⟩ := baerBasisMat_T1J5 z hz
  have hδ0 : T.det ≠ 0 := by
    intro h
    rw [h, mul_zero] at hδ
    exact zero_ne_one hδ
  obtain ⟨D, hDdet, hDiso, hD0, hD1⟩ := baerDiagMat_T1J5 T.det hδ
  refine ⟨T * D, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, hDdet]
    exact mul_inv_cancel₀ hδ0
  · rw [conjTr_mul]
    calc (conjTr σ D * conjTr σ T) * (T * D)
        = conjTr σ D * (conjTr σ T * T) * D := by noncomm_ring
      _ = conjTr σ D * 1 * D := by rw [hTiso]
      _ = conjTr σ D * D := by rw [Matrix.mul_one]
      _ = 1 := hDiso
  · rw [← Matrix.mulVec_mulVec (Pi.single 0 1 : Fin 4 → F) T D, hD0, hTsmul 0]
  · rw [← Matrix.mulVec_mulVec (Pi.single 1 1 : Fin 4 → F) T D, hD1, hTsmul 1]

private theorem baerFrame_T1J5 (z : Fin 4 → Fin 4 → F)
    (hz : ∀ i j, herm σ (z i) (z j) = if i = j then 1 else 0) :
    ∃ t : ↥(SUid σ 4),
      t • (Pi.single 0 1 : Fin 4 → F) = z 0 ∧
      t • (Pi.single 1 1 : Fin 4 → F) = z 1 := by
  obtain ⟨T', hdet, hiso', h0, h1⟩ := baerFrameMat_T1J5 z hz
  have hiso : ∀ x y, herm σ (T' *ᵥ x) (T' *ᵥ y) = herm σ x y := by
    intro x y
    rw [herm_mulVec, hiso', Matrix.one_mulVec]
  exact ⟨mkSU σ T' hdet hiso, by rw [mkSU_smul]; exact h0, by rw [mkSU_smul]; exact h1⟩

private theorem baerStab_T1J5 {Z : Subgroup Fˣ} (hZ : ∀ a ∈ Z, σ (a : F) * a = 1)
    (t : ↥(SUid σ 4)) (z : Fin 4 → Fin 4 → F)
    (ht0 : t • (Pi.single 0 1 : Fin 4 → F) = z 0)
    (ht1 : t • (Pi.single 1 1 : Fin 4 → F) = z 1) :
    ∀ (ab : ↥Z × ↥Z) (x : Fin 4 → F), x ∈ (baerAdd_T1J5 σ z).range →
      (((t * baerTorusSU_T1J5 Z hZ ab * t⁻¹ : ↥(SUid σ 4)) : GL (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F) *ᵥ x ∈ (baerAdd_T1J5 σ z).range := by
  intro ab x hx
  obtain ⟨α, rfl⟩ := (baerAdd_mem_T1J5 σ z x).mp hx
  set a : F := ((ab.1 : Fˣ) : F) with ha
  have ha_inv : σ a = a⁻¹ := by
    rw [ha]
    exact eq_inv_of_mul_eq_one_left (hZ _ ab.1.2)
  have htinv0 : t⁻¹ • z 0 = (Pi.single 0 1 : Fin 4 → F) := by rw [← ht0, inv_smul_smul]
  have htinv1 : t⁻¹ • z 1 = (Pi.single 1 1 : Fin 4 → F) := by rw [← ht1, inv_smul_smul]
  have hΘ0 : baerTorusSU_T1J5 Z hZ ab • (Pi.single 0 1 : Fin 4 → F) =
      a • (Pi.single 0 1 : Fin 4 → F) := by rw [baerTorusSU_smul_e0_T1J5, ha]
  have hΘ1 : baerTorusSU_T1J5 Z hZ ab • (Pi.single 1 1 : Fin 4 → F) =
      a⁻¹ • (Pi.single 1 1 : Fin 4 → F) := by rw [baerTorusSU_smul_e1_T1J5, ha]
  have hgz0 : (t * baerTorusSU_T1J5 Z hZ ab * t⁻¹ : ↥(SUid σ 4)) • z 0 = a • z 0 := by
    rw [mul_smul, mul_smul, htinv0, hΘ0, (smul_comm a t (Pi.single 0 1)).symm, ht0]
  have hgz1 : (t * baerTorusSU_T1J5 Z hZ ab * t⁻¹ : ↥(SUid σ 4)) • z 1 = a⁻¹ • z 1 := by
    rw [mul_smul, mul_smul, htinv1, hΘ1, (smul_comm a⁻¹ t (Pi.single 1 1)).symm, ht1]
  have hgz : (t * baerTorusSU_T1J5 Z hZ ab * t⁻¹ : ↥(SUid σ 4)) •
        (α • z 0 + σ α • z 1) = (α * a) • z 0 + σ (α * a) • z 1 := by
    rw [smul_add, (smul_comm α _ (z 0)).symm, (smul_comm (σ α) _ (z 1)).symm, hgz0, hgz1,
      smul_smul α a (z 0), smul_smul (σ α) a⁻¹ (z 1),
      show σ α * a⁻¹ = σ (α * a) by rw [map_mul, ha_inv]]
  rw [← smul_def, hgz]
  exact (baerAdd_mem_T1J5 σ z _).mpr ⟨α * a, rfl⟩

private theorem baerStab_iff_T1J5 {Z : Subgroup Fˣ} (hZ : ∀ a ∈ Z, σ (a : F) * a = 1)
    (t : ↥(SUid σ 4)) (z : Fin 4 → Fin 4 → F)
    (ht0 : t • (Pi.single 0 1 : Fin 4 → F) = z 0)
    (ht1 : t • (Pi.single 1 1 : Fin 4 → F) = z 1) (ab : ↥Z × ↥Z) (x : Fin 4 → F) :
    ((((t * baerTorusSU_T1J5 Z hZ ab * t⁻¹ : ↥(SUid σ 4)) : GL (Fin 4) F)) :
        Matrix (Fin 4) (Fin 4) F) *ᵥ x ∈ (baerAdd_T1J5 σ z).range ↔
      x ∈ (baerAdd_T1J5 σ z).range := by
  set g : ↥(SUid σ 4) := t * baerTorusSU_T1J5 Z hZ ab * t⁻¹ with hg
  set ginv : ↥(SUid σ 4) := t * baerTorusSU_T1J5 Z hZ ab⁻¹ * t⁻¹ with hginv
  have hginv_eq : ginv = g⁻¹ := by
    rw [hginv, hg, map_inv]
    group
  have hx_eq : ginv • (g • x) = x := by rw [hginv_eq]; exact inv_smul_smul g x
  constructor
  · intro h
    set y : Fin 4 → F := (((g : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) *ᵥ x with hy
    have hmem := baerStab_T1J5 hZ t z ht0 ht1 ab⁻¹ y h
    rw [← hginv] at hmem
    have hyx : (((ginv : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) *ᵥ y = x := by
      rw [← smul_def, hy, ← smul_def, hx_eq]
    rwa [hyx] at hmem
  · intro h
    simpa only [hg] using baerStab_T1J5 hZ t z ht0 ht1 ab x h

theorem exists_stab_baerLine (hσ : IsUnitaryInvolution σ) (hσpow : ∀ c, σ c = c ^ 2 ^ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (z : Fin 4 → Fin 4 → F) (hz : ∀ i j, herm σ (z i) (z j) = if i = j then 1 else 0) :
    ∃ (X : AddSubgroup (Fin 4 → F)) (P : Subgroup (GL (Fin 4) F)),
      (∀ x, x ∈ X ↔ ∃ α : F, x = α • z 0 + σ α • z 1) ∧ P ≤ SUid σ 4 ∧ IsElemAbelian p P ∧
        Nat.card P = p ^ 2 ∧
        ∀ g ∈ P, ∀ x : Fin 4 → F,
          ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x ∈ X ↔ x ∈ X := by
  have hnorm : ∀ c : F, σ c * c = c ^ (2 ^ n + 1) := fun c => by rw [hσpow c, pow_succ]
  obtain ⟨Z, hZp, hZcard, hZ⟩ := exists_torus_data hp hpq hF hnorm
  obtain ⟨t, ht0, ht1⟩ := baerFrame_T1J5 z hz
  let Θ : ↥Z × ↥Z →* ↥(SUid σ 4) := baerTorusSU_T1J5 Z hZ
  have hΘinj : Function.Injective Θ := baerTorusSU_injective_T1J5 Z hZ
  let Ψ : ↥Z × ↥Z →* GL (Fin 4) F :=
    (SUid σ 4).subtype.comp ((MulAut.conj t).toMonoidHom.comp Θ)
  have hΨa : ∀ a, Ψ a = ((t * Θ a * t⁻¹ : ↥(SUid σ 4)) : GL (Fin 4) F) := fun a => rfl
  have hinj : Function.Injective Ψ :=
    (SUid σ 4).subtype_injective.comp ((MulAut.conj t).injective.comp hΘinj)
  have hA : ∀ x : ↥Z × ↥Z, x ^ p = 1 := fun x => by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simpa using hZp _ x.1.2
    · simpa using hZp _ x.2.2
  have hcard : Nat.card (↥Z × ↥Z) = p ^ 2 := by rw [Nat.card_prod, hZcard, sq]
  have hPcard : Nat.card Ψ.range = p ^ 2 := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hPle : Ψ.range ≤ SUid σ 4 := by
    rintro _ ⟨a, rfl⟩
    rw [hΨa]
    exact (t * Θ a * t⁻¹).2
  refine ⟨(baerAdd_T1J5 σ z).range, Ψ.range, baerAdd_mem_T1J5 σ z, hPle,
    isElemAbelian_range Ψ hA, hPcard, ?_⟩
  rintro g ⟨ab, rfl⟩ x
  rw [hΨa ab]
  exact baerStab_iff_T1J5 hZ t z ht0 ht1 ab x

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
