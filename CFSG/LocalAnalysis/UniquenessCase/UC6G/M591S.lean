module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.M591R
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C622
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C636a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem EL_le_normalizer_K_inf : m.EL ≤ normalizer ((m.K ⊓ normalizer (m.L : Set G) : Subgroup G) : Set G) := by
  intro e he
  have heM : e ∈ m.M := m.R_le_M (m.EL_le_R he)
  have heN : e ∈ normalizer (m.L : Set G) := Subgroup.le_normalizer (m.EL_le_L he)
  exact mem_normalizer_of_forward_uc6 fun w hw =>
    ⟨m.conj_mem_K heM hw.1, (normalizer (m.L : Set G)).mul_mem
      ((normalizer (m.L : Set G)).mul_mem heN hw.2) ((normalizer (m.L : Set G)).inv_mem heN)⟩

theorem r_dvd_card_L (h620 : m.C620) : m.r ∣ Nat.card ↥m.L := by
  have hd := Subgroup.card_dvd_of_le (inf_le_right : m.A ⊓ m.L ≤ m.L)
  rw [m.card_A_inf_L h620] at hd
  exact (dvd_pow_self m.r two_ne_zero).trans hd

theorem c636_of_r_gt_3 (hr : 3 < m.r) (h63 : R6_3 Dat)
    (h69 : R6_9 Dat) (h619 : m.C619) (h620 : m.C620) (h621 : m.C621)
    (h622 : m.C622) (h625 : m.C625) (h632 : m.C632) (hKC : m.KC633) (hKN : m.KN633) : m.C636 := by
  have hq : CFSG.Open.IsQuasisimple ↥m.L := h622.quasisimple_of_ne_three (by omega)
  have hR3 := m.rElt_trivial_on_Lbar h69 h619 h620 h621 h625 h632 hKC
  have hYc : ⁅m.K ⊓ normalizer (m.L : Set G), m.L⁆ ≤ m.OL := by
    rcases (hKN (m.K ⊓ normalizer (m.L : Set G)) inf_le_right m.EL_le_normalizer_K_inf hR3).2 with h | h
    · exact h
    · omega
  have hYcent : m.K ⊓ normalizer (m.L : Set G) ≤ centralizer (m.L : Set G) :=
    m.le_centralizer_of_comm_le_OL hq (m.r_dvd_card_L h620) hYc
  refine ⟨?_, hYcent⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(m.K ⊓ normalizer (m.L : Set G)) := by
    rcases Nat.even_or_odd (Nat.card ↥(m.K ⊓ normalizer (m.L : Set G))) with h | h
    · exact even_iff_two_dvd.1 h
    · exact absurd h hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hu1 : (u : G) ≠ 1 := by
    intro h
    have : u = 1 := Subtype.ext h
    rw [this, orderOf_one] at hu
    omega
  have hord : orderOf (u : G) = 2 ^ 1 := by
    rw [Subgroup.orderOf_coe, hu]
    norm_num
  have hcomm : ⁅zpowers (u : G), m.L⁆ ≤ m.OL := by
    have : ⁅zpowers (u : G), m.L⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (Subgroup.zpowers_le.2 (hYcent u.2))
    rw [this]
    exact bot_le
  exact m.gl h63 h619 h620 h632 u.2.2 ⟨1, hord⟩ hu1 hcomm

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
