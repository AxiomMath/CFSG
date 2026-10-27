module

public import CFSG.RankThree.PartOne.TAIL.KSideAbs
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear

public section

namespace CFSG.RankThree.PartOne.TAIL

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (fieldAut_isCyclic)

section Inner

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem slConjugation_scalar (n : ℕ) (c : Fˣ) :
    slConjugation n F (GeneralLinearGroup.scalar (Fin n) c) = 1 := by
  ext g : 1
  apply SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
    GeneralLinearGroup.scalar_commute, mul_assoc, mul_inv_cancel, mul_one]
  rfl

omit [Finite F] in
theorem slConjugation_toGL (n : ℕ) (g h : SpecialLinearGroup (Fin n) F) :
    slConjugation n F (SpecialLinearGroup.toGL g) h = g * h * g⁻¹ := by
  apply SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul,
    map_mul, map_inv]

theorem slConjugation_mem_inn {n : ℕ} (hg : Nat.gcd n (Nat.card F - 1) = 1)
    (A : GeneralLinearGroup (Fin n) F) :
    slConjugation n F A ∈ innK (SpecialLinearGroup (Fin n) F) := by
  classical
  have := Fintype.ofFinite F
  have hcop : (Nat.card Fˣ).Coprime n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card]
    exact (Nat.coprime_comm.1 hg)
  set d : Fˣ := GeneralLinearGroup.det A with hd
  obtain ⟨l, hl⟩ := (powCoprime hcop).surjective d
  rw [powCoprime_apply] at hl
  set B : GeneralLinearGroup (Fin n) F := GeneralLinearGroup.scalar (Fin n) l⁻¹ * A with hB
  have hBdet : GeneralLinearGroup.det B = 1 := by
    rw [hB, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, hl, ← hd,
      inv_mul_cancel]
  have hBdet' : (B : Matrix (Fin n) (Fin n) F).det = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hBdet
    simpa using this
  let g : SpecialLinearGroup (Fin n) F := ⟨(B : Matrix (Fin n) (Fin n) F), hBdet'⟩
  have hgB : SpecialLinearGroup.toGL g = B := Units.ext rfl
  refine ⟨g, ?_⟩
  ext y : 1
  have h1 : slConjugation n F A = slConjugation n F B := by
    rw [hB, map_mul, slConjugation_scalar, one_mul]
  rw [h1, ← hgB]
  have := slConjugation_toGL n g y
  rw [this]
  rfl

theorem outData_sl {n : ℕ} (hn : 3 ≤ n) (hg : Nat.gcd n (Nat.card F - 1) = 1)
    (hAut : Nat.card (F ≃+* F) ∣ 21) : OutData (SpecialLinearGroup (Fin n) F) := by
  classical
  set δ : MulAut (SpecialLinearGroup (Fin n) F) := slGraphAut n F with hδ
  have hδ2 : δ * δ = 1 := slGraph_mul_slGraph
  have hδinv : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδ2
  have hfδ : ∀ σ : F ≃+* F, slFieldAut (Fin n) F σ * δ = δ * slFieldAut (Fin n) F σ := by
    intro σ
    have h := slGraph_mul_slField_mul_slGraph (n := n) (K := F) σ
    have h2 : δ * slFieldAut (Fin n) F σ = slFieldAut (Fin n) F σ * δ⁻¹ :=
      eq_mul_inv_of_mul_eq h
    rw [h2, hδinv]
  have hcomm : ∀ (σ : F ≃+* F) (k : ↥(Subgroup.zpowers δ)),
      Commute (slFieldAut (Fin n) F σ) (k : MulAut (SpecialLinearGroup (Fin n) F)) := by
    intro σ k
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 k.2
    rw [← hj]
    have hc : Commute (slFieldAut (Fin n) F σ) δ := hfδ σ
    exact hc.zpow_right j
  let Ψ : (F ≃+* F) × ↥(Subgroup.zpowers δ) →* MulAut (SpecialLinearGroup (Fin n) F) :=
    (slFieldAut (Fin n) F).noncommCoprod (Subgroup.zpowers δ).subtype hcomm
  have hΨ : ∀ (σ : F ≃+* F) (k : ↥(Subgroup.zpowers δ)),
      Ψ (σ, k) = slFieldAut (Fin n) F σ * (k : MulAut (SpecialLinearGroup (Fin n) F)) :=
    fun σ k => rfl
  refine OutData.of_complement Ψ.range ?_ ?_ ?_
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have := fieldAut_isCyclic F
    let _ : CommGroup (F ≃+* F) := IsCyclic.commGroup
    refine Prod.ext (mul_comm x.1 y.1) ?_
    apply Subtype.ext
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 x.2.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 y.2.2
    show (x.2 : MulAut (SpecialLinearGroup (Fin n) F)) * y.2 = y.2 * x.2
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self δ i j).eq
  · refine (Subgroup.card_range_dvd Ψ).trans ?_
    rw [Nat.card_prod, Nat.card_zpowers]
    have h2 : orderOf δ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hδ2)
    exact (Nat.mul_dvd_mul hAut h2).trans (by norm_num)
  · intro β
    obtain ⟨A, σ, ε, hε, hβ⟩ := CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl hn β
    refine ⟨slConjugation n F A, slConjugation_mem_inn hg A,
      slFieldAut (Fin n) F σ * δ ^ ε, ⟨(σ, ⟨δ ^ ε, Subgroup.pow_mem _ (Subgroup.mem_zpowers δ) ε⟩),
        by rw [hΨ]⟩, ?_⟩
    rw [hβ, mul_assoc]

end Inner

end CFSG.RankThree.PartOne.TAIL
