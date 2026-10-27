module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryPairing
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartOne.FOC

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm

section Setup

variable {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

@[expose] noncomputable def phiS :
    ↥(gramSU h (idGram K n)) →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
  (Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃* LinearMap.GeneralLinearGroup K (Fin n → K)
    ).toMonoidHom.comp (gramSU h (idGram K n)).subtype

variable {h}

theorem phiS_injective : Function.Injective (phiS h (n := n)) := fun _ _ e =>
  Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective e)

theorem phiS_mem_sesqSpecial (g : ↥(gramSU h (idGram K n))) :
    phiS h g ∈ sesqSpecialUnitaryGroup (idForm h n) :=
  (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) (g : GL (Fin n) K)).mpr g.2

theorem phiS_mem_unitary (g : ↥(gramSU h (idGram K n))) : phiS h g ∈ sesqUnitaryGroup (idForm h n) :=
  sesqSpecialUnitaryGroup_le _ (phiS_mem_sesqSpecial g)

theorem mem_range_phiS {g' : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hg' : g' ∈ sesqSpecialUnitaryGroup (idForm h n)) : g' ∈ (phiS h (n := n)).range := by
  have hmem : Matrix.GeneralLinearGroup.toLin.symm g' ∈ gramSU h (idGram K n) := by
    rw [← toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n), MulEquiv.apply_symm_apply]
    exact hg'
  exact ⟨⟨Matrix.GeneralLinearGroup.toLin.symm g', hmem⟩, by
    show Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm g') = g'
    exact MulEquiv.apply_symm_apply _ _⟩

theorem phiS_apply_of_mem_normOneScalars {g : ↥(gramSU h (idGram K n))}
    (hg : g ∈ normOneScalars h (gramSU h (idGram K n)) n) :
    ∃ c : K, ∀ v : Fin n → K, ((phiS h g : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = c • v := by
  obtain ⟨c, -, -, hc⟩ := hg
  refine ⟨(c : K), fun v => ?_⟩
  change (Matrix.toLin' ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) v = _
  rw [hc, GeneralLinearGroup.coe_scalar, Matrix.toLin'_apply, Matrix.scalar_apply]
  ext i
  simp [Matrix.mulVec_diagonal]

theorem primaryData_phiS {p : ℕ} (hpℓ : p ≠ ℓ) (hp : p.Prime) {x : ↥(gramSU h (idGram K n))}
    (hxp : x ^ p = 1) :
    UnitaryPrimaryData h.bar (idForm h n) (phiS h x) := by
  have : Finite K := h.finite
  have : CharP K ℓ := h.charP
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ p).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp).mp this).symm
  set a : GL (Fin n) K := ((x : ↥(gramSU h (idGram K n))) : GL (Fin n) K) with ha
  have hap : a ^ p = GeneralLinearGroup.scalar (Fin n) 1 := by
    rw [map_one, ha, ← Subgroup.coe_pow, hxp]
    rfl
  have hsq := squarefree_minpoly_toLin'_of_pow_scalar hpK hap
  have hX : ((phiS h x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) :=
    (Matrix.toLin'_apply' _).symm
  refine ⟨h.bar_bar, idForm_isSymm h n, idForm_separatingLeft h n, phiS_mem_unitary x, ?_⟩
  rw [hX]
  exact hsq

end Setup

end CFSG.RankThree.PartOne.FOC
