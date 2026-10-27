
module

public import CFSG.Sporadic.J4.QT2LocCntProofBase

@[expose] public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.Th Matrix
open scoped Classical

@[expose] noncomputable def ZE' (ℓ : ℕ) : Finset J :=
  Zl.filter fun x => uElt ℓ * x * (uElt ℓ)⁻¹ ∈ Eg uJ 11

theorem ZE'_card_le (hM : MatFacts) {ℓ : ℕ} (hℓ : ℓ < 7) {n : ℕ}
    (hinv : eqRows (mulRows (pathRows (repPaths.getD ℓ []))
      (invRows (pathRows (repPaths.getD ℓ [])))) idRows = true)
    (hn : (candZ (locMats ()) (locInvs ()) ℓ).length ≤ n) : (ZE' ℓ).card ≤ n := by
  have hsub : ZE' ℓ ⊆ ((candZ (locMats ()) (locInvs ()) ℓ).map (eta uJ 11)).toFinset := by
    intro x hx
    rw [ZE', Finset.mem_filter] at hx
    obtain ⟨hxZ, hxE⟩ := hx
    obtain ⟨c, hc, rfl⟩ := mem_Zl.1 hxZ
    rw [List.mem_toFinset, List.mem_map]
    refine ⟨c, ?_, rfl⟩
    unfold candZ
    rw [List.mem_filter]
    exact ⟨hc, memEVec_of_mem hM hℓ hinv hxE⟩
  exact (Finset.card_le_card hsub).trans (List.toFinset_card_le _ |>.trans (by simpa using hn))

end CFSG.Sporadic.J4.QT2
