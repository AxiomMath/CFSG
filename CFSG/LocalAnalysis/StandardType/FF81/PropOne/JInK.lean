module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.KFixData

import CFSG.GroupTheory.PCore.PrimeSetCore

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

theorem le_oppE {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J B₂ A R : Subgroup G}
    (hJ : JData n L z J) (hR : RData b z J B₂ A R) : J ≤ ktil R := by
  intro y hyJ
  obtain ⟨β, u, O, J', hF, _hβ, hJ', _hclass⟩ := exists_kfixData h hJ hR
  have hO : CFSG.pPrimeCore 3 (Xq R) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hlayer : J' ≤ CFSG.layer (Xq R) :=
    (CFSG.LayerFixed.le_layer_of_fixData hO (abelian_sylow_xq h hR) hF).1
  have hyH : y ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact hR.cenJ r hr y hyJ
  simp only [ktil, CFSG.RankThree.PartTwo.Sec21.FF79.OppE, Subgroup.mem_map,
    Subgroup.mem_comap, QuotientGroup.mk'_apply, Subgroup.subtype_apply]
  exact ⟨⟨y, hyH⟩, hlayer (hJ' ⟨y, hyH⟩ hyJ), rfl⟩

end CFSG.StandardType.FF81.PropOne

end
