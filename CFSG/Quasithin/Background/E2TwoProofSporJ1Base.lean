
module

public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.Quasithin.Background.E2TwoProofSporJ1Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatPt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatO2
public import CFSG.Sporadic.J1.Simple
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore
public import CFSG.Sporadic.J1.Setup
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

namespace E2P

namespace SporB

section List

variable {Γ : Type} [Group Γ] {S : Subgroup Γ} {Y : ℕ → Subgroup Γ} {L : Array ℕ} {N k : ℕ}

theorem list_sup_eq_top (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ L.size, Z = memberOrTop L.size Y j)
    (hSY : ∀ j < L.size, S ≤ Y j) (hcard : ∀ j < L.size, Nat.card (Y j) = L[j]! * 2 ^ k)
    (hΓ : Nat.card Γ = N * 2 ^ k) {a b : ℕ}
    (hno : ∀ j < L.size, latSz L N a ∣ latSz L N j → ¬ latSz L N b ∣ latSz L N j) :
    memberOrTop L.size Y a ⊔ memberOrTop L.size Y b = ⊤ := by
  obtain ⟨j, hj, hjZ⟩ := hall _ (le_sup_of_le_left (list_S_le hSY a) :
    S ≤ memberOrTop L.size Y a ⊔ memberOrTop L.size Y b)
  rw [hjZ]
  by_cases hjL : j < L.size
  · exfalso
    exact hno j hjL (list_dvd_of_le hcard hΓ (le_sup_left.trans hjZ.le))
      (list_dvd_of_le hcard hΓ (le_sup_right.trans hjZ.le))
  · unfold memberOrTop
    rw [ite_eq_right hjL]

theorem list_ne_top' (hcard : ∀ j < L.size, Nat.card (Y j) = L[j]! * 2 ^ k)
    (hΓ : Nat.card Γ = N * 2 ^ k) {a : ℕ} (hN : latSz L N a ≠ N) :
    memberOrTop L.size Y a ≠ ⊤ := by
  intro h
  have h1 := congrArg (fun Z : Subgroup Γ => Nat.card Z) h
  rw [list_card hcard hΓ, Subgroup.card_top, hΓ] at h1
  exact hN (Nat.eq_of_mul_eq_mul_right (by positivity) h1)

end List

section J1

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB.J1Lat CFSG.Sporadic.J1

theorem j1_tab_a : (tab 1540 (a : J)).toArray = j1ta.toArray := by
  rw [tab_eq_of_rep _ _ rep_alpha]
  rfl

theorem j1_tab_b : (tab 1540 (b : J)).toArray = j1tb.toArray := by
  rw [tab_eq_of_rep _ _ rep_beta]
  rfl

theorem j1_delta_valid : PtValid 1540 j1Delta := by decide

@[expose] noncomputable def j1S : Subgroup ↥J :=
  Subgroup.closure {x | x ∈ j1Words.map (wordElt (a : J) (b : J))}

theorem j1_S_eq : Subgroup.closure {x | x ∈ j1Words.map (wordElt (a : J) (b : J))} = j1S := rfl

theorem j1_card_J : Nat.card ↥J = 21945 * 2 ^ 3 := by
  rw [card_J]
  norm_num

theorem j1_inner :
    ∀ α : MulAut ↥J, ∃ g : ↥J, α = MulAut.conj g := by
  intro α
  obtain ⟨g, hg⟩ := (CFSG.Sporadic.Schreier.at_j1_schreier).2.1
    (nativeEquiv.trans (α.trans nativeEquiv.symm))
  refine ⟨nativeEquiv g, ?_⟩
  ext x
  have h := congrArg (fun φ : MulAut CFSG.Blueprint.NativeSporadic.J1 => φ (nativeEquiv.symm x))
    hg
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulAut.conj_apply] at h
  have h2 := congrArg nativeEquiv h
  rw [MulEquiv.apply_symm_apply] at h2
  rw [h2, MulAut.conj_apply]
  simp [map_mul, map_inv]

end J1

end SporB

end E2P

end CFSG.Quasithin
