
module

public import CFSG.Sporadic.Co1.Module.OddCentCardBase

public import CFSG.Sporadic.Co1.Module.OddFactsBase1
public import Certificates.Data.CFSGNative.Co1.OddCent
public import CFSG.Sporadic.Co1.Module.OddCentCardInputs
public import Certificates.Certificate10072
public meta import CFSG.Sporadic.Co1.Module.OddChecks
public meta import Certificates.Data.CFSGNative.Co1.OddCent
public import CFSG.Sporadic.Suz.Setup
public import Certificates.Certificate10072Base
public meta import Certificates.Certificate10073Base
public import Certificates.Certificate10073Base

public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative CFSG.Sporadic.Co1.OddCentNative Matrix

attribute [local instance] vecAct vecSMul

attribute [local irreducible] rr regsRows

section Counting

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]

end Counting

theorem centOK_true : ∃ T : VTree, centOK T = true :=
  Certificates.certificate10072

theorem centOK_facts :
    (∀ i ∈ genIdx3, mulRows 24 (rr3 i) (rr 27) = mulRows 24 (rr 27) (rr3 i)) ∧
      ∃ T : VTree, vtreeOK genRows3 code4 T = true ∧ T.pts.size = 32400 := by
  obtain ⟨T, h⟩ := centOK_true
  simp only [centOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, T, h2, h3⟩

theorem card_Hcent_ge :
    2752512 ≤ Nat.card ↥(Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1)) :=
  card_Hcent_ge_lit

theorem card_cent_orbit :
    32400 * Nat.card ↥(Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1)) ≤
      Nat.card ↥(Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1)) := by
  have := finite_co1
  obtain ⟨hcomm, T, hok, hsz⟩ := centOK_facts
  have hlen : genRows3.size = genIdx3.length := by simp [genRows3]
  have hy : ∀ l < genRows3.size,
      mat (reg3 (genIdx3[l]!)) = rowsMatrix 24 genRows3[l]! := by
    intro l hl
    rw [mat_reg3, show genRows3[l]! = rr3 (genIdx3[l]!) from
      map_toArray_get3 rr3 genIdx3 (hlen ▸ hl)]
  have hK : ∀ l < genRows3.size,
      reg3 (genIdx3[l]!) ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) := by
    intro l hl
    have hl' : l < genIdx3.length := hlen ▸ hl
    have hmem : genIdx3[l]! ∈ genIdx3 := by
      rw [getElem!_pos genIdx3 l hl']
      exact List.getElem_mem hl'
    exact reg3_mem_centralizer (hcomm _ hmem)
  obtain ⟨t, ht, hdist⟩ := vtreeOK_sound hok (fun l => reg3 (genIdx3[l]!)) hy
    (Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1)) hK
  rw [hsz] at ht hdist
  have h1 := card_mul_card_stab_le (G := NativeSporadic.Co1) (Ω := Vec24)
    (Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1)) omega0 32400 t
    (fun i hi => (ht i hi).1) (fun i hi j hj e => hdist i hi j hj (by
      have e1 : co1Act (t i) (toVecD 24 code4) = co1Act (t j) (toVecD 24 code4) := e
      rw [(ht i hi).2, (ht j hj).2] at e1
      exact e1))
  exact h1

theorem card_cent_rho3_ge :
    89181388800 ≤ Nat.card ↥(Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1)) := by
  have h1 := card_cent_orbit
  have h2 := card_Hcent_ge
  calc 89181388800 = 32400 * 2752512 := by norm_num
    _ ≤ 32400 * Nat.card ↥(Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1)) :=
        Nat.mul_le_mul_left _ h2
    _ ≤ _ := h1

end CFSG.Sporadic.Co1.Module.Odd
