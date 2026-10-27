module

public import CFSG.RankThree.PartOne.KC.UnitaryPlaneLineDim
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneDimension
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.RankThree.PartOne.CTP

open Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCUnitaryPlane

variable {ℓ f n p : ℕ} {K : Type} [Field K]

@[expose] noncomputable def unitaryRep (E : Subgroup (unitarySU ℓ f K n)) :
    E →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
  ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃* LinearMap.GeneralLinearGroup K
      (Fin n → K)) : GL (Fin n) K →* LinearMap.GeneralLinearGroup K (Fin n → K)).comp
    ((unitarySU ℓ f K n).subtype.comp E.subtype)

theorem unitaryRep_apply (E : Subgroup (unitarySU ℓ f K n)) (x : E) (v : Fin n → K) :
    ((unitaryRep E x : LinearMap.GeneralLinearGroup K (Fin n → K)) : (Fin n → K) →ₗ[K]
      (Fin n → K)) v = ((x : unitarySU ℓ f K n) : GL (Fin n) K).1.mulVec v := rfl

theorem unitaryRep_injective (E : Subgroup (unitarySU ℓ f K n)) :
    Function.Injective (unitaryRep E) := by
  intro x y hxy
  exact Subtype.ext (Subtype.ext (Units.ext (by
    have := Matrix.GeneralLinearGroup.toLin.injective hxy
    exact congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) this)))

variable (h : UnitaryFieldData ℓ f K)

theorem unitaryRep_mem (E : Subgroup (unitarySU ℓ f K n)) (x : E) :
    unitaryRep E x ∈ sesqUnitaryGroup (gramForm h (1 : Matrix (Fin n) (Fin n) K)) := by
  have hx : ((x : unitarySU ℓ f K n) : GL (Fin n) K) ∈ gramSU h (1 : Matrix (Fin n) (Fin n) K) := by
    rw [← unitarySU_eq_gramSU h n]
    exact (x : unitarySU ℓ f K n).2
  have := (toLin_mem_sesqSpecialUnitaryGroup_iff h (1 : Matrix (Fin n) (Fin n) K)
    ((x : unitarySU ℓ f K n) : GL (Fin n) K)).mpr hx
  exact sesqSpecialUnitaryGroup_le _ this

include h in
theorem two_mul_ordNegQ_le (hp : p.Prime) (hpℓ : p ≠ ℓ) (E : Subgroup (unitarySU ℓ f K n))
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2) :
    2 * ordNegQ ℓ f p ≤ n := by
  classical
  have hfin := h.finite
  have : Fintype E := Fintype.ofFinite E
  have hℓ := h.prime
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := h.charP
  have hpK : (p : K) ≠ 0 := by
    intro h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp ((CharP.cast_eq_zero_iff K ℓ p).mp h0)).symm
  set ρ := unitaryRep (ℓ := ℓ) (f := f) (n := n) (K := K) E with hρdef
  set B := gramForm h (1 : Matrix (Fin n) (Fin n) K) with hBdef
  have hB : B.IsSymm := gramForm_isSymm h (by simp)
  have hBl : B.SeparatingLeft := gramForm_separatingLeft h (by simp)
  have hP : IsPlane p E := ⟨hp, hcard, fun x => Subtype.ext (hexp x x.2)⟩
  have hρ : ∀ x : E, ρ x ∈ sesqUnitaryGroup B := unitaryRep_mem h E
  obtain ⟨L, hL, M, hM, hLM, hLne, hMne⟩ :=
    exists_two_active ρ hP hpK hρ hB hBl (unitaryRep_injective E)
  have hcop := coprime_ordNegQ (f := f) hp hpℓ hℓ
  have hdim : ∀ x : E, x ≠ 1 → ordNegQ ℓ f p ∣ Module.finrank K (Fin n → K) -
      Module.finrank K (LinearMap.ker (act ρ x - 1)) := by
    intro x _
    have hxp : ((ρ x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) ^ p = 1 := by
      have h1 : (ρ x) ^ p = 1 := by
        rw [← map_pow]
        have : x ^ p = 1 := Subtype.ext (hexp x x.2)
        rw [this, map_one]
      have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
        (g : Module.End K (Fin n → K))) h1
      simpa [Units.val_pow_eq_pow_val] using h2
    exact ordNegQ_dvd_finrank_sub h hp hpℓ hB hBl (hρ x) hxp
  have hdL := dvd_finrank_lineSpace ρ hP hpK hρ hB hBl hcop hdim hL
  have hdM := dvd_finrank_lineSpace ρ hP hpK hρ hB hBl hcop hdim hM
  have hposL : 0 < Module.finrank K (lineSpace ρ B L) :=
    Submodule.one_le_finrank_iff.mpr hLne
  have hposM : 0 < Module.finrank K (lineSpace ρ B M) :=
    Submodule.one_le_finrank_iff.mpr hMne
  have hL1 := Nat.le_of_dvd hposL hdL
  have hM1 := Nat.le_of_dvd hposM hdM
  have hsum := finrank_eq_sum ρ hP hpK hρ hB hBl
  have hsub : ({L, M} : Finset (Subgroup E)) ⊆ lines p E := by
    intro N hN
    rcases Finset.mem_insert.mp hN with rfl | hN
    · exact hL
    · exact (Finset.mem_singleton.mp hN) ▸ hM
  have hge : Module.finrank K (lineSpace ρ B L) + Module.finrank K (lineSpace ρ B M) ≤
      ∑ N ∈ lines p E, Module.finrank K (lineSpace ρ B N) := by
    calc Module.finrank K (lineSpace ρ B L) + Module.finrank K (lineSpace ρ B M)
        = ∑ N ∈ ({L, M} : Finset (Subgroup E)), Module.finrank K (lineSpace ρ B N) :=
          (Finset.sum_pair (f := fun N : Subgroup E => Module.finrank K (lineSpace ρ B N))
            hLM).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset hsub
  rw [Module.finrank_fin_fun] at hsum
  omega

end CFSG.RankThree.PartOne.CTP
