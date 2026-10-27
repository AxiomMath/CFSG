module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  InndiagSU

namespace RecipeFieldSU

variable {K : Type} [Field K] {d n : ℕ} (h : UnitaryFieldData 2 n K)

theorem congr_field_eq (hd : 1 ≤ d)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hφ : φ ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :
    ∃ σ : K ≃+* K, MulAut.congr (projEquiv h hd) φ =
      primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := d)) σ := by
  obtain ⟨σ, hσ⟩ := hφ
  refine ⟨σ, MulEquiv.ext fun y => QuotientGroup.induction_on y fun s => ?_⟩
  set s' : gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    primeFormFieldSU h (isPrimeFormGram_one (K := K) (n := d)) σ s with hs'
  have e1 := hσ ⟨s, (largeEvenSUGroup_eq_gramSU (d := d) h).symm ▸ s.2⟩
    ⟨s', (largeEvenSUGroup_eq_gramSU (d := d) h).symm ▸ s'.2⟩ (by
      change ((glAut σ (s : GL (Fin d) K) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = _
      rw [coe_glAut])
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, projEquiv_symm_mk]
  change projEquiv h hd (φ (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))
    ⟨s, (largeEvenSUGroup_eq_gramSU (d := d) h).symm ▸ s.2⟩)) = _
  rw [e1]
  change projEquiv h hd ((⟨s', (largeEvenSUGroup_eq_gramSU (d := d) h).symm ▸ s'.2⟩ :
    LargeEvenSUGroup (Fin d) K (2 ^ n)) : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = _
  rw [projEquiv_mk]
  change _ = primeFormFieldAut h (isPrimeFormGram_one (K := K) (n := d)) σ
    (s : primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
  rw [primeFormFieldAut_mk]

variable (d) in
@[expose] noncomputable def recIU (hd : 1 ≤ d) :
    Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :=
  (primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).comap
    (MulAut.congr (projEquiv h hd)).toMonoidHom

theorem mem_recIU_iff (hd : 1 ≤ d)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))} :
    φ ∈ recIU d h hd ↔ MulAut.congr (projEquiv h hd) φ ∈
      primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
  Iff.rfl

theorem coe_recIU [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 1 ≤ d) :
    (recIU d h hd : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) =
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
  ext φ
  rw [SetLike.mem_coe, mem_recIU_iff]
  constructor
  · rintro ⟨B, hB⟩
    have hmem := congr_symm_mem h hd B
    rwa [hB, MulEquiv.symm_apply_apply] at hmem
  · exact congr_mem_primeFormD h hd hK

theorem conj_mem_recIU (hd : 1 ≤ d) (r : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :
    MulAut.conj r ∈ recIU d h hd := by
  rw [mem_recIU_iff, mulAut_congr_conj]
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (projEquiv h hd r)
  rw [← hs]
  exact ⟨⟨s, s.2.1⟩, primeFormConjHom_eq_conj h _ s⟩

variable [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2))
include h hK hd hq

omit [Finite K] hK in
theorem exists_fieldFactor :
    ∃ Θ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) →* (K ≃+* K),
      Function.Surjective Θ ∧ (∀ φ, Θ φ = 1 ↔ φ ∈ recIU d h (by omega)) ∧
      ∀ σ, Θ ((MulAut.congr (projEquiv h (by omega))).symm
        (primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := d)) σ)) = σ := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨-, -, -, -, -, happ, hsurj, hker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_one (K := K) (n := d)) hd hq
  refine ⟨(primeFormFieldFactor h (isPrimeFormGram_one (K := K) (n := d)) hd hq).comp
      (MulAut.congr (projEquiv h hd1)).toMonoidHom,
    fun σ => ?_, fun φ => ?_, fun σ => ?_⟩
  · obtain ⟨α, hα⟩ := hsurj σ
    refine ⟨(MulAut.congr (projEquiv h hd1)).symm α, ?_⟩
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hα]
  · rw [MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker]
    rfl
  · rw [MonoidHom.comp_apply]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    have := happ 1 σ
    rwa [map_one, one_mul] at this

theorem ggRawInnField_unitary {p : ℕ} (hp : p ≠ 1) :
    GGRawInnField p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Θ, -, hker, hfield⟩ := exists_fieldFactor h hd hq
  refine ggRawInnField_of_subgroup hp (recIU d h hd1) (coe_recIU h hK hd1) (conj_mem_recIU h hd1) ?_
  intro f hf hfI
  obtain ⟨σ, hσ⟩ := congr_field_eq h hd1 hf
  have hfI' : f ∈ recIU d h hd1 := by
    rw [← SetLike.mem_coe, coe_recIU h hK hd1]
    exact hfI
  have hf' : f = (MulAut.congr (projEquiv h hd1)).symm
      (primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := d)) σ) := by
    rw [← hσ, MulEquiv.symm_apply_apply]
  have h1 : Θ f = 1 := (hker f).mpr hfI'
  rw [hf', hfield σ] at h1
  rw [hf', h1, map_one, map_one]

theorem ggRawFieldCentral_unitary :
    GGRawFieldCentral (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Θ, -, hker, -⟩ := exists_fieldFactor h hd hq
  rw [← coe_recIU h hK hd1]
  refine ggRawFieldCentral_of_commutator_mem fun α β => (hker _).mp ?_
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ringEquiv_mul_comm_of_finite (Θ α)]
  group

theorem ggRawPCyclic_unitary {p : ℕ} :
    GGRawPCyclic p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
  intro _ _
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Θ, hsurj, hker, -⟩ := exists_fieldFactor h hd hq
  obtain ⟨-, -, -, -, -, -, -, -, hDn, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_one (K := K) (n := d)) hd hq
  have hJn : (recIU d h hd1).Normal := hDn.comap _
  have h2n : 1 ≤ 2 * n := by have := h.one_le; omega
  obtain ⟨Fr, -, -, hzp, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_two h2n
    (by rw [hK, ← pow_mul, mul_comm])
  obtain ⟨g, hg⟩ := hsurj Fr
  refine ⟨recIU d h hd1, ⊤, coe_recIU h hK hd1, le_top, inferInstance,
    ⟨g, Subgroup.mem_top _, fun s _ => ?_⟩, fun α _ => Subgroup.mem_top α⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hzp ▸ Subgroup.mem_top (Θ s))
  refine ⟨-k, (hker _).mp ?_⟩
  rw [map_mul, map_zpow, hg, ← hk, ← _root_.zpow_add, neg_add_cancel, zpow_zero]

end RecipeFieldSU

open RecipeFieldSU

theorem recipeUnitary_and {d q : ℕ} {Q P : LargeEvenRawCont}
    (hA : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q ^ 2 →
      P (LargeEvenProj (LargeEvenSUGroup (Fin d) K q))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K q))
          (LargeEvenGUSet (Fin d) K q))
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K q))))
    (h : LargeEvenRecipeUnitary d q Q) :
    LargeEvenRecipeUnitary d q fun R _ I F => Q R I F ∧ P R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, hA K hK⟩

theorem largeEvenLabelAll_unitary {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hS : GGInndiagUnitaryLabel lab) {P : LargeEvenRawCont}
    (hP : ∀ (d n : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ n → 3 ≤ d → ¬(d = 3 ∧ 2 ^ n = 2) →
      Nat.card K = (2 ^ n) ^ 2 →
      P (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n)))
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))))) :
    LargeEvenLabelAll lab P := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  intro Q hQ
  rcases hS with ht | ⟨ht, hl3⟩
  · dsimp only at ht
    subst ht
    obtain ⟨hl2, hl2n⟩ := hl
    change 1 ≤ n at hn
    change 2 ≤ l at hl2
    change l = 2 → 2 ≤ n at hl2n
    refine recipeUnitary_and (fun K _ _ hK => hP (l + 1) n K hn (by omega) (fun ⟨h3, h2⟩ => ?_) hK) hQ
    have hn2 : 2 ≤ n := hl2n (by omega)
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  · dsimp only at ht hl3
    subst ht hl3
    have h32 : (3 : ℕ) ≠ 2 := by decide
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [h32, ↓reduceIte] at hQ ⊢
    exact recipeUnitary_and (fun K _ _ hK => hP 4 n K hn (by norm_num) (by omega) hK) hQ

theorem unitaryFieldData_of_card {n : ℕ} {K : Type} [Field K] (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) : UnitaryFieldData 2 n K :=
  ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩

theorem ggRawInnFieldOn_unitary : GGRawInnFieldOn GGInndiagUnitaryLabel :=
  fun _ hp _ _ hlab hS => largeEvenLabelAll_unitary hlab hS fun _ _ _ _ _ hn hd hq hK =>
    ggRawInnField_unitary (unitaryFieldData_of_card hn hK) hK hd hq hp.one_lt.ne'

theorem ggRawFieldCentralOn_unitary : GGRawFieldCentralOn GGInndiagUnitaryLabel :=
  fun _ hlab hS => largeEvenLabelAll_unitary hlab hS fun _ _ _ _ _ hn hd hq hK =>
    ggRawFieldCentral_unitary (unitaryFieldData_of_card hn hK) hK hd hq

theorem ggRawPCyclicOn_unitary : GGRawPCyclicOn fun _ => GGInndiagUnitaryLabel :=
  fun _ _ _ _ hlab hS => largeEvenLabelAll_unitary hlab hS fun _ _ _ _ _ hn hd hq hK =>
    ggRawPCyclic_unitary (unitaryFieldData_of_card hn hK) hK hd hq

end CFSG.StandardType

end
