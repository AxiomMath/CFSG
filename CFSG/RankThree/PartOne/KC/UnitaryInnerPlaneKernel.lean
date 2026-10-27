module

public import CFSG.RankThree.PartOne.KC.UnitaryPlaneLineDim
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneDimension
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.RankThree.PartOne.KCUnitaryPlane

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

@[expose] noncomputable def toUnitary (n : ℕ) :
    gramSU h (idGram K n) →* primeFormUnitary h (idGram K n) :=
  Subgroup.inclusion fun _ hg => hg.1

@[expose] noncomputable def planeRep (n : ℕ) (Ahat : Subgroup (gramSU h (idGram K n))) :
    ↥Ahat →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
  ((toLinU h n).comp (toUnitary h n)).comp Ahat.subtype

variable {h}

theorem toUnitary_apply (x : gramSU h (idGram K n)) :
    ((toUnitary h n x : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
      ((x : gramSU h (idGram K n)) : GL (Fin n) K) := rfl

theorem toUnitary_injective : Function.Injective (toUnitary h n) := fun _ _ hxy =>
  Subtype.ext (by
    have h1 := congrArg Subtype.val hxy
    exact h1)

theorem planeRep_mem (Ahat : Subgroup (gramSU h (idGram K n))) (x : ↥Ahat) :
    planeRep h n Ahat x ∈ sesqUnitaryGroup (idForm h n) :=
  toLinU_mem (toUnitary h n x)

theorem planeRep_injective (Ahat : Subgroup (gramSU h (idGram K n))) :
    Function.Injective (planeRep h n Ahat) :=
  (toLinU_injective.comp toUnitary_injective).comp Ahat.subtype_injective

theorem isPlane_of_elementaryAbelian (hp : p.Prime) {Ahat : Subgroup (gramSU h (idGram K n))}
    (hAel : IsElementaryAbelian p Ahat) (hAcard : Nat.card Ahat = p ^ 2) : IsPlane p ↥Ahat :=
  ⟨hp, hAcard, fun x => by
    have := hAel
    have h1 : (x : gramSU h (idGram K n)) ^ p = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (x : gramSU h (idGram K n)) x.2
    exact Subtype.ext (by simpa using h1)⟩

variable (h) in
structure PlaneKernelDecomposition (n p : ℕ) (Ahat : Subgroup (gramSU h (idGram K n))) : Prop where
  nondegenerate_fixed :
    ((idForm h n).domRestrict₁₂ (fixedSpace (planeRep h n Ahat) ⊤)
      (fixedSpace (planeRep h n Ahat) ⊤)).SeparatingLeft
  nondegenerate_line : ∀ L : Subgroup ↥Ahat, Nat.card L = p →
    ((idForm h n).domRestrict₁₂ (lineSpace (planeRep h n Ahat) (idForm h n) L)
      (lineSpace (planeRep h n Ahat) (idForm h n) L)).SeparatingLeft
  orthogonal_fixed_line : ∀ L : Subgroup ↥Ahat, Nat.card L = p →
    ∀ u ∈ fixedSpace (planeRep h n Ahat) ⊤, ∀ w ∈ lineSpace (planeRep h n Ahat) (idForm h n) L,
      idForm h n u w = 0
  orthogonal_line_line : ∀ L M : Subgroup ↥Ahat, Nat.card L = p → Nat.card M = p → L ≠ M →
    ∀ u ∈ lineSpace (planeRep h n Ahat) (idForm h n) L,
      ∀ w ∈ lineSpace (planeRep h n Ahat) (idForm h n) M, idForm h n u w = 0
  independent : iSupIndep (decompFamily (planeRep h n Ahat) (idForm h n) p)
  sup_eq_top : ⨆ i, decompFamily (planeRep h n Ahat) (idForm h n) p i = ⊤
  dvd_finrank : ∀ L : Subgroup ↥Ahat, Nat.card L = p →
    ordNegQ ℓ f p ∣ Module.finrank K (lineSpace (planeRep h n Ahat) (idForm h n) L)
  exists_two_active : ∃ L M : Subgroup ↥Ahat, Nat.card L = p ∧ Nat.card M = p ∧ L ≠ M ∧
    lineSpace (planeRep h n Ahat) (idForm h n) L ≠ ⊥ ∧
      lineSpace (planeRep h n Ahat) (idForm h n) M ≠ ⊥
  ker_eq : ∀ L : Subgroup ↥Ahat, Nat.card L = p → ∀ x ∈ L, x ≠ 1 →
    LinearMap.ker (act (planeRep h n Ahat) x - 1) =
      fixedSpace (planeRep h n Ahat) ⊤ ⊔ lineSpace (planeRep h n Ahat) (idForm h n) L

theorem planeKernelDecomposition (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {Ahat : Subgroup (gramSU h (idGram K n))} (hAel : IsElementaryAbelian p Ahat)
    (hAcard : Nat.card Ahat = p ^ 2) : PlaneKernelDecomposition h n p Ahat := by
  classical
  have := h.finite
  have : Finite ↥Ahat := inferInstance
  have : Fintype ↥Ahat := Fintype.ofFinite _
  have hP : IsPlane p ↥Ahat := isPlane_of_elementaryAbelian hp hAel hAcard
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h1 := (CharP.cast_eq_zero_iff K ℓ p).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp).mp h1).symm
  set ρ := planeRep h n Ahat with hρdef
  have hρ : ∀ x : ↥Ahat, ρ x ∈ sesqUnitaryGroup (idForm h n) := planeRep_mem Ahat
  have hB := idForm_isSymm h n
  have hBl := idForm_separatingLeft h n
  have hint := isInternal_decompFamily ρ hP hpK hρ hB hBl
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint
  have hdim : ∀ x : ↥Ahat, x ≠ 1 → ordNegQ ℓ f p ∣ Module.finrank K (Fin n → K) -
      Module.finrank K (LinearMap.ker (act ρ x - 1)) := by
    intro x _
    refine ordNegQ_dvd_finrank_sub h hp hpℓ hB hBl (hρ x) ?_
    have : (x ^ p : ↥Ahat) = 1 := hP.pow x
    have h2 := congrArg (fun y : ↥Ahat => ((ρ y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) this
    simpa [map_pow] using h2
  refine ⟨separatingLeft_fixedTop ρ hP hpK hρ hB hBl,
    fun L hL => separatingLeft_lineSpace ρ hP hpK hρ hB hBl hL,
    fun L hL u hu w hw => (orth_top_line ρ hB hu hw).1,
    fun L M hL hM hne u hu w hw => orth_line_line ρ hP hpK hρ hB hBl hL hM hne hu hw,
    hint.1, hint.2,
    fun L hL => dvd_finrank_lineSpace ρ hP hpK hρ hB hBl (coprime_ordNegQ hp hpℓ h.prime)
      hdim (mem_lines.mpr hL),
    ?_, fun L hL x hxL hx1 => ker_act_sub_one_eq ρ hP hpK hρ hB hBl hL hxL hx1⟩
  obtain ⟨L, hL, M, hM, hne, h1, h2⟩ :=
    exists_two_active ρ hP hpK hρ hB hBl (planeRep_injective Ahat)
  exact ⟨L, M, mem_lines.mp hL, mem_lines.mp hM, hne, h1, h2⟩

end CFSG.RankThree.PartOne.KCUnitaryPlane
