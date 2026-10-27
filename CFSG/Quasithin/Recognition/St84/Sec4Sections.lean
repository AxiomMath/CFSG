module

public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
public import CFSG.GH74.QTGen4.DSGen4.Defs

import CFSG.Quasithin.Background.B19Setup
import CFSG.Quasithin.Recognition.St84.Gen.NatSecIndex
public import CFSG.GH74.QTGen4.DSGen4.Statements

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement

variable {G : Type} [Group G]

theorem comm_le_of_relIndex_le_eight {L E N : Subgroup G} [Finite ↥L]
    (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hNE : N ≤ E)
    (hEN : E ≤ Subgroup.normalizer (N : Set G))
    (hLE : L ≤ Subgroup.normalizer (E : Set G))
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) (hE : IsPGroup 2 E)
    (hcore : ⁅E, pCoreOf 2 L⁆ ≤ N) (h0 : N.relIndex E ≠ 0) (h8 : N.relIndex E ≤ 8) :
    ⁅E, L⁆ ≤ N :=
  comm_le_of_relIndex_lt_two_pow (n := 2) (by norm_num) hq hNE hEN hLE hLN hE hcore h0
    (lt_of_le_of_lt h8 (by norm_num : (8 : ℕ) < 2 ^ (2 * 2)))

theorem relCent_L_eq {L Q E : Subgroup G} (hEQ : E ≤ Q)
    (hQE : Q ≤ Subgroup.centralizer (E : Set G)) (hL : L = ⁅L, L⁆ ⊔ Q) :
    relCent E (centerOf L ⊓ E) L = centerOf L ⊓ E := by
  let Z : Subgroup G := centerOf L ⊓ E
  have hZL : Z ≤ Subgroup.centralizer (L : Set G) :=
    (inf_le_left.trans inf_le_right : centerOf L ⊓ E ≤ Subgroup.centralizer (L : Set G))
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨hgE, hgN, hgcomm⟩ := hg
    have hgL : g ∈ L := by
      rw [hL]
      exact Subgroup.mem_sup_right (hEQ hgE)
    have hLgZ : ⁅L, Subgroup.zpowers g⁆ ≤ Z := by
      have hg : g ∈ CFSG.Quasithin.B19.commTo L Z := CFSG.Quasithin.B19.mem_commTo.mpr
        ⟨hgN, fun a ha => by rw [← commutatorElement_inv]; exact Z.inv_mem (hgcomm a ha)⟩
      exact Subgroup.commutator_le.mpr fun a ha k hk =>
        (CFSG.Quasithin.B19.mem_commTo.mp (Subgroup.zpowers_le.mpr hg hk)).2 a ha
    have h1 : ⁅⁅L, Subgroup.zpowers g⁆, L⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hLgZ.trans hZL)
    have h2 : ⁅⁅Subgroup.zpowers g, L⁆, L⁆ = ⊥ := by
      simpa [Subgroup.commutator_comm (Subgroup.zpowers g) L] using h1
    have hLLcent : ⁅L, L⁆ ≤ Subgroup.centralizer (Subgroup.zpowers g : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp
        (Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2)
    have hLcent : L ≤ Subgroup.centralizer (Subgroup.zpowers g : Set G) := by
      rw [hL]
      exact sup_le hLLcent (hQE.trans (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hgE)))
    refine ⟨⟨hgL, ?_⟩, hgE⟩
    exact Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (hLcent ha) g (Subgroup.mem_zpowers g)).symm
  · intro g hg
    refine ⟨(Subgroup.mem_inf.mp hg).2, Subgroup.le_normalizer hg, fun a ha => ?_⟩
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).1.2 a ha).symm ▸ Z.one_mem

theorem isElemSec_of_natQuot_center {L E Z N : Subgroup G} [Finite ↥L]
    (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hE2 : IsPGroup 2 E) (hnat : NatQuot L E Z 2)
    (hsec : IsElemSec Z E) (hZN : IsElemSec N Z) (hcent : ⁅Z, L⁆ ≤ N) : IsElemSec N E :=
  isElemSec_of_natQuot_of_comm_le (n := 2) (by norm_num) hq hE2 hnat hsec hZN hcent

end CFSG.Quasithin.St84
