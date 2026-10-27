module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraph
public import CFSG.LocalAnalysis.StandardType.GGRootDetectSU

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank Matrix
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr rootDatum rootGroup rootHom longRootHom
  heisenbergSubgroup rootMatrix longRootMatrix heisenbergMatrix traceZero weight toStd)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

namespace OrdPGraph

section Field

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem map_rootMatrix (φ : F ≃+* F) (hφ : ∀ x, φ (σ x) = σ (φ x)) (i j : Fin n) (c : F) :
    (rootMatrix σ i j c).map φ = rootMatrix σ i j (φ c) := by
  rw [rootMatrix, rootMatrix, Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ),
    Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_single, Matrix.map_single, hφ]

theorem map_longRootMatrix (φ : F ≃+* F) (i : Fin n) (c : F) :
    (longRootMatrix i c).map φ = longRootMatrix i (φ c) := by
  rw [longRootMatrix, longRootMatrix, Matrix.map_add _ (map_add φ),
    Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_single]

theorem map_heisenbergMatrix (φ : F ≃+* F) (hφ : ∀ x, φ (σ x) = σ (φ x)) (i k : Fin n)
    (a b : F) :
    (heisenbergMatrix σ i k a b).map φ = heisenbergMatrix σ i k (φ a) (φ b) := by
  rw [heisenbergMatrix, heisenbergMatrix, Matrix.map_add _ (map_add φ),
    Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ),
    Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_single, Matrix.map_single,
    Matrix.map_single, hφ]

variable (hσ : ∀ c, σ (σ c) = c)

@[expose] noncomputable def fieldPre (φ : F ≃+* F) (γ : Fin (n / 2) → ℤ) : Subgroup (SU σ n) where
  carrier := {z | ∃ z' ∈ rootGroup σ hσ n γ, (z' : GL (Fin n) F) = glAut φ (z : GL (Fin n) F)}
  mul_mem' := by
    rintro a b ⟨a', ha', ea⟩ ⟨b', hb', eb⟩
    refine ⟨a' * b', mul_mem ha' hb', ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ea, eb, map_mul]
  one_mem' := ⟨1, one_mem _, by simp⟩
  inv_mem' := by
    rintro a ⟨a', ha', ea⟩
    refine ⟨a'⁻¹, inv_mem ha', ?_⟩
    rw [Subgroup.coe_inv, Subgroup.coe_inv, ea, map_inv]

theorem exists_glAut_mem_rootGroup (φ : F ≃+* F) (hφ : ∀ x, φ (σ x) = σ (φ x))
    (γ : Fin (n / 2) → ℤ) {z : SU σ n} (hz : z ∈ rootGroup σ hσ n γ) :
    ∃ z' ∈ rootGroup σ hσ n γ, (z' : GL (Fin n) F) = glAut φ (z : GL (Fin n) F) := by
  suffices h : rootGroup σ hσ n γ ≤ fieldPre hσ φ γ from h hz
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
      iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
    rintro _ ⟨c, rfl⟩
    refine ⟨rootHom σ hσ hij hi hj (Multiplicative.ofAdd (φ c.toAdd)), ?_, Units.ext ?_⟩
    · have hle : (rootHom σ hσ hij hi hj).range ≤ rootGroup σ hσ n γ :=
        le_sup_of_le_left (le_sup_of_le_left (le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le hij
          (le_iSup_of_le hi (le_iSup_of_le hj (le_iSup_of_le hji (le_iSup_of_le hw le_rfl))))))))
      exact hle ⟨_, rfl⟩
    · rw [coe_glAut, CFSG.LieType.Universal.Unitary.coe_rootHom,
        CFSG.LieType.Universal.Unitary.coe_rootHom, map_rootMatrix φ hφ]
      rfl
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    rintro _ ⟨c, rfl⟩
    have hc : φ (c.toAdd : F) ∈ traceZero σ := by
      rw [CFSG.LieType.Universal.Unitary.mem_traceZero, ← hφ, ← map_add,
        (CFSG.LieType.Universal.Unitary.mem_traceZero σ).mp c.toAdd.2, map_zero]
    refine ⟨longRootHom σ hi (Multiplicative.ofAdd ⟨φ (c.toAdd : F), hc⟩), ?_, Units.ext ?_⟩
    · have hle : (longRootHom σ hi).range ≤ rootGroup σ hσ n γ :=
        le_sup_of_le_left (le_sup_of_le_right (le_iSup_of_le i (le_iSup_of_le hi
          (le_iSup_of_le hw le_rfl))))
      exact hle ⟨_, rfl⟩
    · rw [coe_glAut, CFSG.LieType.Universal.Unitary.coe_longRootHom,
        CFSG.LieType.Universal.Unitary.coe_longRootHom, map_longRootMatrix]
      rfl
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun hw => ?_
    rintro x ⟨a, b, hab, hx⟩
    have hmem : ∃ y : SU σ n, ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        heisenbergMatrix σ i k (φ a) (φ b) := by
      refine ⟨⟨glAut φ (x : GL (Fin n) F), ?_⟩, ?_⟩
      · rw [CFSG.LieType.Universal.Unitary.mem_SU, coe_glAut]
        obtain ⟨hdet, hiso⟩ := CFSG.LieType.Universal.Unitary.mem_SU.mp x.2
        refine ⟨?_, ?_⟩
        · rw [show ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map φ =
            (φ : F →+* F).mapMatrix ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) from rfl,
            ← RingHom.map_det, hdet, map_one]
        · have e := congrArg (fun M : Matrix (Fin n) (Fin n) F => M.map φ) hiso
          simp only [conjTr, Matrix.map_mul, transpose_map] at e ⊢
          rw [CFSG.LieType.Universal.Unitary.antidiag] at e ⊢
          convert e using 3
          · ext u v
            simp [hφ]
          · ext u v
            simp only [map_apply, of_apply]
            split_ifs <;> simp
          · ext u v
            simp only [map_apply, of_apply]
            split_ifs <;> simp
      · change ((glAut φ (x : GL (Fin n) F) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = _
        rw [coe_glAut, hx, map_heisenbergMatrix φ hφ]
    obtain ⟨y, hy⟩ := hmem
    refine ⟨y, ?_, Units.ext ?_⟩
    · have hle : heisenbergSubgroup σ hσ hi hik hk ≤ rootGroup σ hσ n γ :=
        le_sup_of_le_right (le_iSup_of_le i (le_iSup_of_le k (le_iSup_of_le hi
          (le_iSup_of_le hik (le_iSup_of_le hk (le_iSup_of_le hw le_rfl))))))
      refine hle ⟨φ a, φ b, ?_, hy⟩
      rw [← hφ, ← hφ, ← map_mul, ← map_add, ← map_add, hab, map_zero]
    · rw [hy, coe_glAut, hx, map_heisenbergMatrix φ hφ]

end Field

section Diag

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem prod_mul_map_prod_eq_one {t : Fin n → F} (ht : ∀ a, σ (t a) * t (Fin.rev a) = 1) :
    (∏ a, t a) * σ (∏ a, t a) = 1 := by
  have h1 : ∏ a, (σ (t a) * t (Fin.rev a)) = 1 := Finset.prod_eq_one fun a _ => ht a
  rw [Finset.prod_mul_distrib, ← map_prod] at h1
  have h2 : ∏ a, t (Fin.rev a) = ∏ a, t a :=
    Fintype.prod_equiv Fin.revPerm _ _ (fun a => rfl)
  rw [h2, mul_comm] at h1
  exact h1

variable [CharP F 2] (hσ : ∀ c, σ (σ c) = c)

theorem exists_diag_conj_mem_rootGroup (hsq : ∀ x : F, ∃ y, y * y = x)
    (h90 : ∀ u : F, u * σ u = 1 → ∃ ρ : F, ρ ≠ 0 ∧ ρ / σ ρ = u) (hn : 4 ≤ n)
    {t : Fin n → F} (ht : ∀ a, σ (t a) * t (Fin.rev a) = 1) {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (CFSG.LieType.Universal.Unitary.isFiniteType_cartan n)
      (CFSG.LieType.Universal.Unitary.divisible n))
    {z : SU σ n} (hz : z ∈ rootGroup σ hσ n γ) :
    ∃ z'' ∈ rootGroup σ hσ n γ, (z'' : GL (Fin n) F) =
      RootDetectSU.diagGL t (CFSG.LieType.Universal.Unitary.ne_zero_of_unitary ht) *
        (z : GL (Fin n) F) *
          (RootDetectSU.diagGL t (CFSG.LieType.Universal.Unitary.ne_zero_of_unitary ht))⁻¹ := by
  have hD := prod_mul_map_prod_eq_one ht
  have hD0 : (∏ a, t a) ≠ 0 := left_ne_zero_of_mul_eq_one hD
  have hνi : (∏ a, t a)⁻¹ * σ (∏ a, t a)⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hD, inv_one]
  obtain ⟨r, hru, hrprod, hrconst⟩ :=
    RootDetectSU.exists_unitaryDiag_of_mem_roots hσ hsq h90 hn hγ hνi
  have htu := RootDetectSU.unitary_mul ht hru
  have htdet : ∏ a, (t * r) a = 1 := by
    simp only [Pi.mul_apply]
    rw [Finset.prod_mul_distrib, hrprod, mul_inv_cancel₀ hD0]
  set hel := RootDetectSU.diagSU σ (t * r) htu htdet with hheldef
  have hmem := RootDetectSU.mem_normalizer_rootGroup_of_mem_diagSubgroup hσ
    (RootDetectSU.diagSU_mem_diagSubgroup _ htu htdet) γ
  refine ⟨hel * z * hel⁻¹, (Subgroup.mem_normalizer_iff.mp hmem z).mp hz, ?_⟩
  set rGL : GL (Fin n) F :=
    RootDetectSU.diagGL r (CFSG.LieType.Universal.Unitary.ne_zero_of_unitary hru) with hrGL
  have hcommr : rGL * (z : GL (Fin n) F) = (z : GL (Fin n) F) * rGL := Units.ext (by
    rw [Units.val_mul, Units.val_mul, hrGL, RootDetectSU.coe_diagGL]
    exact RootDetectSU.diagonal_mul_comm_of_mem_rootGroup hσ hrconst hz)
  have hhel : ((hel : SU σ n) : GL (Fin n) F) =
      RootDetectSU.diagGL t (CFSG.LieType.Universal.Unitary.ne_zero_of_unitary ht) * rGL :=
    Units.ext (by
      rw [Units.val_mul, hheldef, RootDetectSU.coe_diagSU, RootDetectSU.coe_diagGL, hrGL,
        RootDetectSU.coe_diagGL, RootDetectSU.coe_diagGL, diagonal_mul_diagonal]
      rfl)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hhel, mul_assoc _ rGL, hcommr]
  group

end Diag

section Model

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}

theorem modelDiagField_su (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 4 ≤ n) :
    ∃ (C : Type) (_ : Group C) (π : SU (unitaryInvolution F 2 f) n →* C),
      Function.Surjective π ∧ π.ker = Subgroup.center (SU (unitaryInvolution F 2 f) n) ∧
        ∀ β : MulAut C, ModelDiagField (rootDatum hF n) π β := by
  classical
  have hσ : ∀ x, unitaryInvolution F 2 f (unitaryInvolution F 2 f x) = x :=
    unitaryInvolution_involutive hF
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h' => by omega
  have h : UnitaryFieldData 2 f F := RootDetectSU.unitaryFieldData_two hF hf
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : GL (Fin n) F, (C₀ : Matrix (Fin n) (Fin n) F) = antidiag n :=
    ⟨⟨antidiag n, antidiag n, CFSG.LieType.Universal.Unitary.antidiag_mul_self n,
      CFSG.LieType.Universal.Unitary.antidiag_mul_self n⟩, rfl⟩
  have hC : IsPrimeFormGram C₀ := RootDetectSU.isPrimeFormGram_of_eq_antidiag hC₀
  set C : Matrix (Fin n) (Fin n) F := (C₀ : Matrix (Fin n) (Fin n) F) with hCdef
  have hE : SU (unitaryInvolution F 2 f) n = gramSU h C := by
    rw [hC₀]
    exact RootDetectSU.SU_eq_gramSU_antidiag h
  set E : SU (unitaryInvolution F 2 f) n ≃* gramSU h C := MulEquiv.subgroupCongr hE with hEdef
  have hEval : ∀ z, ((E z : gramSU h C) : GL (Fin n) F) = z := fun z => rfl
  have hN : normOneScalars h (gramSU h C) n = Subgroup.center (gramSU h C) :=
    (CFSG.SeitzReduction.F4Pilot.center_gramSU_eq_normOneScalars h hC hn3 hq).symm
  set π : SU (unitaryInvolution F 2 f) n →* primeFormP h C :=
    (QuotientGroup.mk' (normOneScalars h (gramSU h C) n)).comp E.toMonoidHom with hπdef
  refine ⟨primeFormP h C, inferInstance, π, ?_, ?_, fun β => ?_⟩
  · exact (QuotientGroup.mk'_surjective _).comp E.surjective
  · ext z
    rw [MonoidHom.mem_ker, hπdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hN, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro hz g
      apply E.injective
      simpa only [MulEquiv.coe_toMonoidHom, map_mul] using hz (E g)
    · intro hz g
      have e := congrArg E (hz (E.symm g))
      simpa only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply] using e
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn3 hq β
  rw [primeFormPsi_apply] at hAφ
  have hsqrt : ∀ x : F, ∃ y, y * y = x := fun x => by
    obtain ⟨y, hy⟩ := isSquare_of_charTwo' x
    exact ⟨y, hy.symm⟩
  have h90 : ∀ w : F, w * unitaryInvolution F 2 f w = 1 →
      ∃ ρ : F, ρ ≠ 0 ∧ ρ / unitaryInvolution F 2 f ρ = w := fun w hw =>
    RootDetectSU.exists_div_eq h hw
  have hcomm : ∀ x, φ (unitaryInvolution F 2 f x) = unitaryInvolution F 2 f (φ x) := fun x => by
    rw [unitaryInvolution_apply, unitaryInvolution_apply, map_pow]
  set ν₀ : F := ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det with hν₀
  have hν : ν₀ * unitaryInvolution F 2 f ν₀ = 1 := by
    have e := norm_det_eq_one h C₀ A.2
    rwa [UnitaryFieldData.norm, RootDetectSU.bar_eq h] at e
  have hν0 : ν₀ ≠ 0 := left_ne_zero_of_mul_eq_one hν
  obtain ⟨δ, hδ0, hδ⟩ := h90 ν₀ hν
  set b : Fin n := ⟨0, by omega⟩ with hbdef
  have hb : b ≠ Fin.rev b := Fin.ne_of_val_ne (by simp [b]; omega)
  have hdu := RootDetectSU.pairDiag_unitary hσ hb hδ0
  set dGL : GL (Fin n) F :=
    RootDetectSU.diagGL (RootDetectSU.pairDiag (unitaryInvolution F 2 f) b δ)
      (CFSG.LieType.Universal.Unitary.ne_zero_of_unitary hdu) with hdGL
  have hdU : dGL ∈ primeFormUnitary h C := by
    rw [hC₀]
    exact RootDetectSU.diagGL_mem_primeFormUnitary h hdu
  have hddet : ((dGL : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = ν₀ := by
    rw [hdGL, RootDetectSU.coe_diagGL, det_diagonal, RootDetectSU.prod_pairDiag hb,
      ← div_eq_mul_inv, hδ]
  set a : GL (Fin n) F := (A : GL (Fin n) F) * dGL⁻¹ with hadef
  have ha : a ∈ gramSU h C := by
    refine (mem_gramSU_iff_unitary h).mpr ⟨mul_mem A.2 (inv_mem hdU), ?_⟩
    have e : ((a * dGL : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = ν₀ := by
      rw [hadef, inv_mul_cancel_right]
    rw [Units.val_mul, det_mul, hddet] at e
    exact mul_right_cancel₀ hν0 (e.trans (one_mul ν₀).symm)
  refine ⟨((⟨a, ha⟩ : gramSU h C) : primeFormP h C), fun γ hγ z hz => ?_⟩
  obtain ⟨z', hz', hz'e⟩ := exists_glAut_mem_rootGroup hσ φ hcomm γ hz
  obtain ⟨z'', hz'', hz''e⟩ := exists_diag_conj_mem_rootGroup hσ hsqrt h90 hn hdu hγ hz'
  rw [← hdGL] at hz''e
  refine ⟨z'', hz'', ?_⟩
  have hβz : β (π z) = ((⟨A * glAut φ (z : GL (Fin n) F) * (A : GL (Fin n) F)⁻¹,
      conj_mem_gramSU h C A.2 (glAut_mem_gramSU h hC φ (E z).2)⟩ : gramSU h C) :
        primeFormP h C) := by
    rw [← hAφ, MulAut.mul_apply]
    change primeFormConjHom h C A (primeFormFieldAut h hC φ ((E z : gramSU h C) :
      primeFormP h C)) = _
    rw [primeFormFieldAut_mk, primeFormConjHom_mk]
    rfl
  rw [hβz]
  change _ = ((E z'' : gramSU h C) : primeFormP h C)
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hEval, hz''e, hz'e]
  change a⁻¹ * ((A : GL (Fin n) F) * glAut φ (z : GL (Fin n) F) * (A : GL (Fin n) F)⁻¹) * a = _
  rw [hadef]
  group

end Model

end OrdPGraph

section Family

theorem ggOrdPGraphModelAt_PSU : GGOrdPGraphModelAt .PSU := by
  intro n f hadm
  have hf : 1 ≤ f := hadm.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : ggU .PSU n f =
      ⟨SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
        rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  rw [e]
  intro hrk
  have hrk' : 2 ≤ n / 2 := hrk
  obtain ⟨C, _, π, hπ, hker, hM⟩ :=
    OrdPGraph.modelDiagField_su (n := n) (card_galoisField_two_mul 2 f hf) hf (by omega)
  exact ⟨C, _, π, hπ, hker, fun _ _ _ _ β _ => hM β⟩

theorem ggOrdPGraphAt_PSU : GGOrdPGraphAt .PSU :=
  ggOrdPGraphAt_of_model ggOrdPGraphModelAt_PSU

end Family

end CFSG.StandardType
