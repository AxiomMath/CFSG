module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical
public import CFSG.RankThree.PartOne.KC.UnitaryRegularUnipotentCyclic

public section

namespace CFSG.RankThree.PartOne.KCUnitaryDefining

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

theorem gramForm_mulVec_of_mem_gramSU {G : Matrix (Fin n) (Fin n) K} {g : GL (Fin n) K}
    (hg : g ∈ gramSU h G) (x y : Fin n → K) :
    gramForm h G ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) ((g : Matrix (Fin n) (Fin n) K) *ᵥ y) =
      gramForm h G x y :=
  (gramForm_isometry_iff h G _).mpr (mem_gramSU.mp hg).1 x y

theorem conj_mem_isotropicRadical {G : Matrix (Fin n) (Fin n) K}
    {W : Submodule K (Fin n → K)} {g : gramSU h G}
    (hgW : ∀ w ∈ W, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    (hgW' : ∀ w ∈ W, (((g⁻¹ : gramSU h G) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    {r : gramSU h G} (hr : r ∈ isotropicRadical h G W) :
    g * r * g⁻¹ ∈ isotropicRadical h G W := by
  set gm : Matrix (Fin n) (Fin n) K := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hgm
  set gi : Matrix (Fin n) (Fin n) K :=
    (((g⁻¹ : gramSU h G) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hgi
  set rm : Matrix (Fin n) (Fin n) K := ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hrm
  have hgi' : ((g⁻¹ : gramSU h G) : GL (Fin n) K) = (g : GL (Fin n) K)⁻¹ := rfl
  have hgg : gm * gi = 1 := by rw [hgm, hgi, hgi', Units.mul_inv]
  have hgg' : gi * gm = 1 := by rw [hgm, hgi, hgi', Units.inv_mul]
  have hI : ∀ x y, gramForm h G (gm *ᵥ x) (gm *ᵥ y) = gramForm h G x y :=
    gramForm_mulVec_of_mem_gramSU h g.2
  obtain ⟨hr1, hr2, hr3⟩ := mem_isotropicRadical.mp hr
  have hgv : ∀ v, gm *ᵥ (gi *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hgg, one_mulVec]
  have hgmperp : ∀ u ∈ W.orthogonalBilin (gramForm h G),
      gm *ᵥ u ∈ W.orthogonalBilin (gramForm h G) := by
    intro u hu
    rw [Submodule.mem_orthogonalBilin] at hu ⊢
    intro w hw
    have h1 := hI (gi *ᵥ w) u
    rw [hgv] at h1
    rw [h1]
    exact hu _ (hgW' w hw)
  have hgiperp : ∀ u ∈ W.orthogonalBilin (gramForm h G),
      gi *ᵥ u ∈ W.orthogonalBilin (gramForm h G) := by
    intro u hu
    rw [Submodule.mem_orthogonalBilin] at hu ⊢
    intro w hw
    have h1 := hI w (gi *ᵥ u)
    rw [hgv] at h1
    rw [← h1]
    exact hu _ (hgW w hw)
  have hcoe : (((g * r * g⁻¹ : gramSU h G) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      gm * rm * gi := by
    simp [hgm, hgi, hrm, Subgroup.coe_mul]
  refine mem_isotropicRadical.mpr ⟨fun w hw => ?_, fun v hv => ?_, fun v => ?_⟩
  · rw [hcoe, ← mulVec_mulVec, ← mulVec_mulVec, hr1 _ (hgW' w hw), hgv]
  · have hv' := hgiperp v hv
    have h1 := hr2 (gi *ᵥ v) hv'
    have h2 : (gm * rm * gi) *ᵥ v - v = gm *ᵥ (rm *ᵥ (gi *ᵥ v) - gi *ᵥ v) := by
      rw [mulVec_sub, hgv, ← mulVec_mulVec, ← mulVec_mulVec]
    rw [hcoe, h2]
    exact hgW _ h1
  · have h1 := hr3 (gi *ᵥ v)
    have h2 : (gm * rm * gi) *ᵥ v - v = gm *ᵥ (rm *ᵥ (gi *ᵥ v) - gi *ᵥ v) := by
      rw [mulVec_sub, hgv, ← mulVec_mulVec, ← mulVec_mulVec]
    rw [hcoe, h2]
    exact hgmperp _ h1

theorem pow_eq_one_of_mem_isotropicRadical (hp3 : 3 ≤ p) (hn : 1 ≤ n)
    {G : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)} {g : gramSU h G}
    (hg : g ∈ isotropicRadical h G W) : g ^ p = 1 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have : NeZero n := ⟨by omega⟩
  have h3 := sub_one_pow_three_of_mem_radical hg
  set M : Matrix (Fin n) (Fin n) K := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1
    with hM
  have hMp : M ^ p = 0 := by rw [← Nat.sub_add_cancel hp3, pow_add, h3, mul_zero]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one,
    show ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + M by rw [hM]; abel,
    add_pow_char_of_commute p (Commute.one_left M), one_pow, hMp, add_zero]

theorem primeFormConjHom_mul_fieldHom_eq_conj {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    {A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)} {z : Kˣ}
    {r : gramSU h (C : Matrix (Fin n) (Fin n) K)}
    (hAr : (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) z * (r : GL (Fin n) K))
    {σ : K ≃+* K} (hσ : ∀ t, σ t = t) :
    primeFormConjHom h _ A * primeFormFieldHom h hC σ =
      MulAut.conj (r : primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
  have hσ' : σ = 1 := RingEquiv.ext hσ
  have hAconj : primeFormConjHom h _ A =
      primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨(r : GL (Fin n) K), r.2.1⟩ := by
    refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
    rw [primeFormConjHom_mk, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change (A : GL (Fin n) K) * (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ =
      (r : GL (Fin n) K) * (g : GL (Fin n) K) * (r : GL (Fin n) K)⁻¹
    rw [hAr]
    calc GeneralLinearGroup.scalar (Fin n) z * (r : GL (Fin n) K) * (g : GL (Fin n) K) *
          (GeneralLinearGroup.scalar (Fin n) z * (r : GL (Fin n) K))⁻¹ =
        GeneralLinearGroup.scalar (Fin n) z * ((r : GL (Fin n) K) * (g : GL (Fin n) K) *
          (r : GL (Fin n) K)⁻¹) * (GeneralLinearGroup.scalar (Fin n) z)⁻¹ := by group
      _ = (r : GL (Fin n) K) * (g : GL (Fin n) K) * (r : GL (Fin n) K)⁻¹ := by
          rw [← (commute_scalar z ((r : GL (Fin n) K) * (g : GL (Fin n) K) *
            (r : GL (Fin n) K)⁻¹)).eq]
          group
  rw [hσ', map_one, mul_one, hAconj]
  exact primeFormConjHom_eq_conj h _ r

end CFSG.RankThree.PartOne.KCUnitaryDefining
