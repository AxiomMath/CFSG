module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.Sylow
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Lines

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L84

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem exists_isSr_of_sylow (h : Counterexample p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) :
    ∃ R S' : Subgroup G, R ≤ thetaOf θ F ∧ IsPGroup r ↥R ∧
      Nat.Coprime (R.relIndex (thetaOf θ F)) r ∧ R ≤ S' ∧ IsSr p A θ r S' := by
  have hF0 := h.ne_bot_of_mem_E1 hF
  have hAU := h.isFunctor.normalizes_thetaOf hF.1
  have hU := h.isFunctor.coprime_thetaOf hF.1 hF0
  have hbot : A ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have hbot' : A ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) ∧ IsPGroup r ↥(⊥ : Subgroup G) ∧
      (⊥ : Subgroup G) ≤ thetaOf θ F := ⟨hbot, IsPGroup.of_bot, bot_le⟩
  obtain ⟨R, -, hR⟩ := Finite.exists_le_maximal
    (p := fun Q : Subgroup G => A ≤ Subgroup.normalizer (Q : Set G) ∧ IsPGroup r ↥Q ∧
      Q ≤ thetaOf θ F) hbot'
  have hR' : IsSrSubgroupOf A r (thetaOf θ F) R := hR
  obtain ⟨hRU, hRp, hidx⟩ := isSylow_of_isSrSubgroupOf h.prime hr hrp h.elemAbelian hAU hU hR'
  have hRmem : R ∈ MsigR p A θ r :=
    ⟨mem_signalizers_of_le (h.thetaOf_mem_msig hF.1 hF0) hRU hR.1.1
      (fun hP => hypB_mono hRU hP), hRp⟩
  obtain ⟨S', hRS', hS'⟩ :=
    Finite.exists_le_maximal (p := fun Q : Subgroup G => Q ∈ MsigR p A θ r) hRmem
  exact ⟨R, S', hRU, hRp, hidx, hRS', hS'⟩

end L84

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
