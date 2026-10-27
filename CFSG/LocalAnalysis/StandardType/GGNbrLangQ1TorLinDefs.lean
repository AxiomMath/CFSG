module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
public import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTypeDet
public import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalSubfield

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)

private noncomputable def l02qt2_pslRingCongr
    (d : ℕ) (hd0 : 0 < d) {F₀ E : Type} [Field F₀] [Field E] (τ : F₀ ≃+* E) :
    LinearFlag.projectiveSL d F₀ ≃* LinearFlag.projectiveSL d E :=
  MulEquiv.ofBijective
    (CFSG.SeitzReduction.LinearPilot.projMap d (τ : F₀ →+* E))
    ⟨CFSG.SeitzReduction.LinearPilot.projMap_injective hd0 _,
      fun x => by
        rw [← MonoidHom.mem_range]
        refine (CFSG.SeitzReduction.LinearPilot.mem_range_projMap (τ : F₀ →+* E)).mpr ?_
        obtain ⟨a, rfl⟩ := LinearFlag.proj_surjective d E x
        exact ⟨a, fun i j => τ.surjective _, rfl⟩⟩

private theorem l02qt2_pslRingCongr_conjAut
    {d : ℕ} {F₀ E : Type} [Field F₀] [Field E] (hd0 : 0 < d) (τ : F₀ ≃+* E)
    (X : GL (Fin d) F₀) (x : LinearFlag.projectiveSL d F₀) :
    l02qt2_pslRingCongr d hd0 τ (LinearFlag.conjAut d F₀ X x) =
      LinearFlag.conjAut d E (Matrix.GeneralLinearGroup.map (τ : F₀ →+* E) X)
        (l02qt2_pslRingCongr d hd0 τ x) := by
  have h := CFSG.SeitzReduction.LinearPilot.projMap_std_apply (n := d) (K := F₀) (F := E)
    (τ : F₀ →+* E) X (ρ := 1) (ρ' := 1) (by intro c; rfl) (ε := 0) (by norm_num) x
  change CFSG.SeitzReduction.LinearPilot.projMap d (τ : F₀ →+* E)
      (LinearFlag.conjAut d F₀ X x) =
    LinearFlag.conjAut d E (Matrix.GeneralLinearGroup.map (τ : F₀ →+* E) X)
      (CFSG.SeitzReduction.LinearPilot.projMap d (τ : F₀ →+* E) x)
  simpa only [map_one, pow_zero, mul_one] using h.symm

private theorem l02qt2_conjAut_mul_inv_eq
    {d : ℕ} {K : Type} [Field K] (A B : GL (Fin d) K) :
    LinearFlag.conjAut d K A * LinearFlag.conjAut d K B * (LinearFlag.conjAut d K A)⁻¹ =
      LinearFlag.conjAut d K (A * B * A⁻¹) := by
  rw [← map_inv, ← map_mul, ← map_mul]

private theorem l02qt2_conj_std
    {d : ℕ} {K : Type} [Field K] (A : GL (Fin d) K) (σ : K ≃+* K) (ε : ℕ) (hε : ε ≤ 1)
    (X : GL (Fin d) K) :
    (LinearFlag.conjAut d K A * LinearFlag.fieldAut d K σ * LinearFlag.dualAut d K ^ ε) *
        LinearFlag.conjAut d K X *
        (LinearFlag.conjAut d K A * LinearFlag.fieldAut d K σ * LinearFlag.dualAut d K ^ ε)⁻¹ =
      LinearFlag.conjAut d K (A *
        (if ε = 0 then Matrix.GeneralLinearGroup.map (σ : K →+* K) X
         else Matrix.GeneralLinearGroup.inverseTranspose
           (Matrix.GeneralLinearGroup.map (σ : K →+* K) X)) *
        A⁻¹) := by
  obtain ⟨hcc, hff, hfc, hδδ, hδc, hδf, -, -, -⟩ :=
    LinearFlag.standard_automorphism_transport (K := K) (n := d)
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · simp only [pow_zero, mul_one, if_pos rfl]
    calc (LinearFlag.conjAut d K A * LinearFlag.fieldAut d K σ) * LinearFlag.conjAut d K X *
          (LinearFlag.conjAut d K A * LinearFlag.fieldAut d K σ)⁻¹
        = LinearFlag.conjAut d K A *
            (LinearFlag.fieldAut d K σ * LinearFlag.conjAut d K X *
              (LinearFlag.fieldAut d K σ)⁻¹) * (LinearFlag.conjAut d K A)⁻¹ := by group
      _ = LinearFlag.conjAut d K A *
            LinearFlag.conjAut d K (Matrix.GeneralLinearGroup.map (σ : K →+* K) X) *
            (LinearFlag.conjAut d K A)⁻¹ := by rw [hfc]
      _ = LinearFlag.conjAut d K
            (A * Matrix.GeneralLinearGroup.map (σ : K →+* K) X * A⁻¹) :=
            l02qt2_conjAut_mul_inv_eq A _
  · simp only [pow_one, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    have hδinv : (LinearFlag.dualAut d K)⁻¹ = LinearFlag.dualAut d K :=
      inv_eq_of_mul_eq_one_right hδδ
    have hinv : (LinearFlag.conjAut d K A * LinearFlag.fieldAut d K σ *
        LinearFlag.dualAut d K)⁻¹ =
        LinearFlag.dualAut d K * (LinearFlag.fieldAut d K σ)⁻¹ *
          (LinearFlag.conjAut d K A)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, hδinv]; group
    calc (LinearFlag.conjAut d K A * LinearFlag.fieldAut d K σ * LinearFlag.dualAut d K) *
          LinearFlag.conjAut d K X *
          (LinearFlag.conjAut d K A * LinearFlag.fieldAut d K σ * LinearFlag.dualAut d K)⁻¹
        = LinearFlag.conjAut d K A *
            (LinearFlag.fieldAut d K σ *
              (LinearFlag.dualAut d K * LinearFlag.conjAut d K X * LinearFlag.dualAut d K) *
              (LinearFlag.fieldAut d K σ)⁻¹) * (LinearFlag.conjAut d K A)⁻¹ := by
            rw [hinv]; group
      _ = LinearFlag.conjAut d K A *
            (LinearFlag.fieldAut d K σ *
              LinearFlag.conjAut d K (Matrix.GeneralLinearGroup.inverseTranspose X) *
              (LinearFlag.fieldAut d K σ)⁻¹) * (LinearFlag.conjAut d K A)⁻¹ := by rw [hδc]
      _ = LinearFlag.conjAut d K A *
            LinearFlag.conjAut d K
              (Matrix.GeneralLinearGroup.map (σ : K →+* K)
                (Matrix.GeneralLinearGroup.inverseTranspose X)) *
            (LinearFlag.conjAut d K A)⁻¹ := by rw [hfc]
      _ = LinearFlag.conjAut d K
            (A * Matrix.GeneralLinearGroup.map (σ : K →+* K)
                (Matrix.GeneralLinearGroup.inverseTranspose X) * A⁻¹) :=
            l02qt2_conjAut_mul_inv_eq A _
      _ = LinearFlag.conjAut d K
            (A * Matrix.GeneralLinearGroup.inverseTranspose
                (Matrix.GeneralLinearGroup.map (σ : K →+* K) X) * A⁻¹) := by
            rw [Matrix.GeneralLinearGroup.map_inverseTranspose]

private theorem l02qt2_slKerEquiv_conjNormal {d : ℕ} {K : Type} [Field K]
    (A : GL (Fin d) K) (h : LargeEvenSLGroup (Fin d) K) :
    TypeA.slKerEquiv d K (MulAut.conjNormal A h) =
      slConjugation d K A (TypeA.slKerEquiv d K h) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hc : ∀ h : LargeEvenSLGroup (Fin d) K,
      Matrix.SpecialLinearGroup.toGL (TypeA.slKerEquiv d K h) = (h : GL (Fin d) K) :=
    fun h => Units.ext (TypeA.coe_slKerEquiv h)
  rw [toGL_slConjugation, hc, hc, MulAut.conjNormal_apply]

private theorem l02qt2_recipeEquiv_linConjAut {d : ℕ} {K : Type} [Field K]
    (A : GL (Fin d) K) (x : LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    TypeA.recipeEquiv d K (TableB.linConjAut (Fin d) K A x) =
      LinearFlag.conjAut d K A (TypeA.recipeEquiv d K x) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  rw [TableB.linConjAut_mk]
  rw [show (TypeA.recipeEquiv d K) (↑(MulAut.conjNormal A h)) =
      LinearFlag.proj d K (TypeA.slKerEquiv d K (MulAut.conjNormal A h))
    from TypeA.recipeEquiv_mk (MulAut.conjNormal A h)]
  rw [show (TypeA.recipeEquiv d K) (↑h) = LinearFlag.proj d K (TypeA.slKerEquiv d K h)
    from TypeA.recipeEquiv_mk h]
  rw [LinearFlag.conjAut_proj, l02qt2_slKerEquiv_conjNormal]

private theorem l02qt2_exists_conjAut {d : ℕ} (hd : 3 ≤ d)
    {K K' : Type} [Field K] [Finite K] [Field K'] [Finite K']
    (hcard : Nat.card K = Nat.card K')
    (ψ : LinearFlag.projectiveSL d K ≃* LinearFlag.projectiveSL d K')
    (M : GL (Fin d) K) :
    ∃ g : GL (Fin d) K', ∀ x,
      ψ (LinearFlag.conjAut d K M x) = LinearFlag.conjAut d K' g (ψ x) := by
  classical
  have hd0 : 0 < d := by omega
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite K'
  have hcard' : Fintype.card K = Fintype.card K' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard
  let τ : K ≃+* K' := FiniteField.ringEquivOfCardEq hcard'
  let gτ : LinearFlag.projectiveSL d K ≃* LinearFlag.projectiveSL d K' :=
    l02qt2_pslRingCongr d hd0 τ
  let β : MulAut (LinearFlag.projectiveSL d K') := ψ.symm.trans gτ
  obtain ⟨A', σ', ε', hε', hβ'⟩ :=
    (LinearFlag.automorphism_generation (K := K') (n := d) hd).2 β⁻¹
  let X : GL (Fin d) K' := Matrix.GeneralLinearGroup.map (τ : K →+* K') M
  let gval : GL (Fin d) K' := A' *
    (if ε' = 0 then Matrix.GeneralLinearGroup.map (σ' : K' →+* K') X
     else Matrix.GeneralLinearGroup.inverseTranspose
       (Matrix.GeneralLinearGroup.map (σ' : K' →+* K') X)) * A'⁻¹
  refine ⟨gval, fun x => ?_⟩
  have hβinv : β⁻¹ * LinearFlag.conjAut d K' X * (β⁻¹)⁻¹ =
      LinearFlag.conjAut d K' gval := by
    rw [hβ']
    exact l02qt2_conj_std A' σ' ε' hε' X
  have key : β⁻¹ (LinearFlag.conjAut d K' X (β (ψ x))) =
      LinearFlag.conjAut d K' gval (ψ x) := by
    have h := congrArg (fun e : MulAut (LinearFlag.projectiveSL d K') => e (ψ x)) hβinv
    simpa [MulAut.mul_apply, inv_inv] using h
  have hb : β (ψ x) = gτ x := by
    simp [β, MulEquiv.trans_apply]
  have hc : LinearFlag.conjAut d K' X (gτ x) = gτ (LinearFlag.conjAut d K M x) :=
    (l02qt2_pslRingCongr_conjAut hd0 τ M x).symm
  have hb' : β⁻¹ (gτ (LinearFlag.conjAut d K M x)) = ψ (LinearFlag.conjAut d K M x) := by
    have h1 : β (ψ (LinearFlag.conjAut d K M x)) = gτ (LinearFlag.conjAut d K M x) := by
      simp [β, MulEquiv.trans_apply]
    have h2 : β (β⁻¹ (gτ (LinearFlag.conjAut d K M x))) = gτ (LinearFlag.conjAut d K M x) := by
      change β (β.symm (gτ (LinearFlag.conjAut d K M x))) = gτ (LinearFlag.conjAut d K M x)
      rw [MulEquiv.apply_symm_apply]
    exact β.injective (h2.trans h1.symm)
  rw [hb, hc, hb'] at key
  exact key

private theorem l02qt2_exists_conj {d : ℕ} (hd : 3 ≤ d)
    {K K' : Type} [Field K] [Finite K] [Field K'] [Finite K']
    (hcard : Nat.card K = Nat.card K')
    (θ' : LargeEvenProj (LargeEvenSLGroup (Fin d) K) ≃*
          LargeEvenProj (LargeEvenSLGroup (Fin d) K'))
    (M : GL (Fin d) K) :
    ∃ g : GL (Fin d) K', ∀ x,
      θ' (TableB.linConjAut (Fin d) K M x) = TableB.linConjAut (Fin d) K' g (θ' x) := by
  let ψ' : LinearFlag.projectiveSL d K ≃* LinearFlag.projectiveSL d K' :=
    (TypeA.recipeEquiv d K).symm.trans (θ'.trans (TypeA.recipeEquiv d K'))
  obtain ⟨g, hg⟩ := l02qt2_exists_conjAut hd hcard ψ' M
  refine ⟨g, fun x => ?_⟩
  apply (TypeA.recipeEquiv d K').injective
  rw [l02qt2_recipeEquiv_linConjAut]
  have h := hg (TypeA.recipeEquiv d K x)
  rw [← l02qt2_recipeEquiv_linConjAut] at h
  simpa [ψ', MulEquiv.trans_apply] using h

private theorem l02qt2_commute_transfer {d : ℕ} {F₀ E : Type} [Field F₀] [Finite F₀] [Field E]
    [Finite E] (hd : 3 ≤ d) (hcard : Nat.card E = Nat.card F₀)
    (ψ : LargeEvenProj (LargeEvenSLGroup (Fin d) F₀) ≃*
         LargeEvenProj (LargeEvenSLGroup (Fin d) E))
    {M N : GL (Fin d) F₀} {g h : GL (Fin d) E}
    (hM : ∀ x, ψ (TableB.linConjAut (Fin d) F₀ M x) = TableB.linConjAut (Fin d) E g (ψ x))
    (hN : ∀ x, ψ (TableB.linConjAut (Fin d) F₀ N x) = TableB.linConjAut (Fin d) E h (ψ x))
    (hgh : g * h = h * g) : M * N = N * M := by
  let τF : LargeEvenProj (LargeEvenSLGroup (Fin d) F₀) ≃* LinearFlag.projectiveSL d F₀ :=
    TypeA.recipeEquiv d F₀
  let τE : LargeEvenProj (LargeEvenSLGroup (Fin d) E) ≃* LinearFlag.projectiveSL d E :=
    TypeA.recipeEquiv d E
  let ψ' : LinearFlag.projectiveSL d F₀ ≃* LinearFlag.projectiveSL d E :=
    τF.symm.trans (ψ.trans τE)
  have hM' : ∀ x, ψ' (LinearFlag.conjAut d F₀ M x) = LinearFlag.conjAut d E g (ψ' x) := by
    intro x
    have h1 : τF.symm (LinearFlag.conjAut d F₀ M x) =
        TableB.linConjAut (Fin d) F₀ M (τF.symm x) := by
      apply τF.injective
      rw [MulEquiv.apply_symm_apply, l02qt2_recipeEquiv_linConjAut, MulEquiv.apply_symm_apply]
    change τE (ψ (τF.symm (LinearFlag.conjAut d F₀ M x))) =
      LinearFlag.conjAut d E g (τE (ψ (τF.symm x)))
    rw [h1, hM, l02qt2_recipeEquiv_linConjAut]
  have hN' : ∀ x, ψ' (LinearFlag.conjAut d F₀ N x) = LinearFlag.conjAut d E h (ψ' x) := by
    intro x
    have h1 : τF.symm (LinearFlag.conjAut d F₀ N x) =
        TableB.linConjAut (Fin d) F₀ N (τF.symm x) := by
      apply τF.injective
      rw [MulEquiv.apply_symm_apply, l02qt2_recipeEquiv_linConjAut, MulEquiv.apply_symm_apply]
    change τE (ψ (τF.symm (LinearFlag.conjAut d F₀ N x))) =
      LinearFlag.conjAut d E h (τE (ψ (τF.symm x)))
    rw [h1, hN, l02qt2_recipeEquiv_linConjAut]
  exact kgLangS1A_commute_transfer (d := d) hd hcard ψ' hM' hN' hgh

@[expose] def ToralLin (R : Type) [Group R] (E : Subgroup (MulAut R)) : Prop :=
  ∃ (d : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
    (θ : R ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
    IsMulCommutative ((E.map (MulAut.congr θ).toMonoidHom).comap (TableB.linConjAut (Fin d) K))

theorem toralLin_commute_datum {d m : ℕ} (hd : 3 ≤ d) (hm : 2 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ m)
    {E : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))} (h : ToralLin _ E) :
    IsMulCommutative (E.comap (TableB.linConjAut (Fin d) K)) := by
  classical
  obtain ⟨d', K', hfieldK', hfinK', θ', hcomm⟩ := h
  letI : Field K' := hfieldK'
  letI : Finite K' := hfinK'
  have hdet := kgLangS1A_psl_typeDet (d := d) (d₁ := d') (m := m) (F₀ := K) (E := K')
    hd hm hK ((TypeA.recipeEquiv d K).symm.trans θ')
  obtain ⟨hdd, hcard⟩ := hdet
  subst d'
  rw [isMulCommutative_iff]
  intro M N
  apply Subtype.ext
  let mM : GL (Fin d) K := (M : GL (Fin d) K)
  let mN : GL (Fin d) K := (N : GL (Fin d) K)
  have hcM : TableB.linConjAut (Fin d) K mM ∈ E := Subgroup.mem_comap.mp M.2
  have hcN : TableB.linConjAut (Fin d) K mN ∈ E := Subgroup.mem_comap.mp N.2
  obtain ⟨g, hg⟩ := l02qt2_exists_conj hd hcard.symm θ' mM
  obtain ⟨h', hh'⟩ := l02qt2_exists_conj hd hcard.symm θ' mN
  have hcg : MulAut.congr θ' (TableB.linConjAut (Fin d) K mM) =
      TableB.linConjAut (Fin d) K' g := by
    ext y
    rw [MulAut.congr_apply]
    simpa using hg (θ'.symm y)
  have hch : MulAut.congr θ' (TableB.linConjAut (Fin d) K mN) =
      TableB.linConjAut (Fin d) K' h' := by
    ext y
    rw [MulAut.congr_apply]
    simpa using hh' (θ'.symm y)
  have hgmem : g ∈ (E.map (MulAut.congr θ').toMonoidHom).comap (TableB.linConjAut (Fin d) K') := by
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_map.mpr ⟨TableB.linConjAut (Fin d) K mM, hcM, hcg⟩
  have hhmem : h' ∈ (E.map (MulAut.congr θ').toMonoidHom).comap (TableB.linConjAut (Fin d) K') := by
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_map.mpr ⟨TableB.linConjAut (Fin d) K mN, hcN, hch⟩
  have hgh : g * h' = h' * g := by
    have hcomm' := (isMulCommutative_iff.mp hcomm) ⟨g, hgmem⟩ ⟨h', hhmem⟩
    exact congrArg Subtype.val hcomm'
  have htransfer := l02qt2_commute_transfer hd hcard θ' hg hh' hgh
  simpa [mM, mN] using htransfer

end CFSG.StandardType
