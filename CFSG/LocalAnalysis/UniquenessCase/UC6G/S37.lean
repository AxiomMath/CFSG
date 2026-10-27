module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.K
public import CFSG.LocalAnalysis.UniquenessCase.UC6S37

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem L_le_H : m.L ≤ m.H := by
  refine (closure_le _).2 ?_
  rintro x ⟨hx, -⟩
  have : inftyOf m.H ≤ m.H := Subgroup.map_subtype_le _
  exact this hx

theorem Z_comm_L {z l : G} (hz : z ∈ m.Z) (hl : l ∈ m.L) : z * l = l * z :=
  mem_centralizer_iff.1 (m.L_le_H hl) z hz

theorem Z_le_A : m.Z ≤ m.A := le_sup_left

theorem E_le_A : m.E ≤ m.A := le_sup_right

theorem A_le_R : m.A ≤ m.R := sup_le m.hZ.le m.E_le_R

theorem Z_comm_E {z e : G} (hz : z ∈ m.Z) (he : e ∈ m.E) : z * e = e * z :=
  mem_centralizer_iff.1 (m.d.E_le he).2 z (m.hZ.le hz)

theorem Z_inf_E : m.Z ⊓ m.E = ⊥ :=
  inf_eq_bot_of_not_le_of_card_prime m.hr m.card_Z m.hZ.not_le_E

theorem card_A : Nat.card ↥m.A = m.r ^ 3 := by
  rw [A, card_sup_of_commute_of_disjoint (fun z hz e he => m.Z_comm_E hz he) m.Z_inf_E, m.card_Z,
    m.d.E_card]
  ring

theorem isElemAbelian_A : IsElemAbelian m.r m.A :=
  IsElemAbelian.sup_of_commute (isElemAbelian_of_card_prime m.hr m.card_Z) m.d.E_el
    (fun z hz e he => m.Z_comm_E hz he)

theorem card_A_inf_L (h620 : m.C620) : Nat.card ↥(m.A ⊓ m.L) = m.r ^ 2 := by
  have hZL : m.Z ⊓ m.L = ⊥ :=
    inf_eq_bot_of_not_le_of_card_prime m.hr m.card_Z h620.2
  have hZE0 : m.Z ⊓ (m.A ⊓ m.L) = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hZL]
    exact inf_le_inf_left _ inf_le_right
  have hcomm' : ∀ z ∈ m.Z, ∀ e ∈ m.A ⊓ m.L, z * e = e * z := fun z hz e he => m.Z_comm_L hz he.2
  have hsup : m.A = m.Z ⊔ (m.A ⊓ m.L) := by
    refine le_antisymm ?_ (sup_le m.Z_le_A inf_le_left)
    intro a ha
    obtain ⟨z, hz, l, hl, rfl⟩ :=
      exists_mul_of_mem_sup_of_commute (fun z hz l hl => m.Z_comm_L hz hl) (h620.1 ha)
    have hlA : l ∈ m.A := by
      have := m.A.mul_mem (m.A.inv_mem (m.Z_le_A hz)) ha
      simpa using this
    exact (m.Z ⊔ (m.A ⊓ m.L)).mul_mem (mem_sup_left hz) (mem_sup_right ⟨hlA, hl⟩)
  have hcard := card_sup_of_commute_of_disjoint hcomm' hZE0
  rw [← hsup, m.card_A, m.card_Z] at hcard
  have hr0 : 0 < m.r := m.hr.pos
  have h2 : m.r * Nat.card ↥(m.A ⊓ m.L) = m.r * m.r ^ 2 := by
    rw [← hcard]; ring
  exact Nat.eq_of_mul_eq_mul_left hr0 h2

theorem semiregular (h67 : R6_7 Dat) (h619 : m.C619) (h620 : m.C620)
    (h632 : m.C632) (h635 : m.C635) (h636 : m.C636) :
    ∀ x ∈ m.K ⊓ normalizer (m.L : Set G), x ≠ 1 → ∀ v ∈ m.V, x * v * x⁻¹ = v → v = 1 := by
  intro x hx hx1 v hv hxv
  by_contra hv1
  have hxL : x ∈ centralizer (m.L : Set G) := h636.2 hx
  have hxC : ∀ l ∈ m.L, x * l = l * x := fun l hl => (mem_centralizer_iff.1 hxL l hl).symm
  have hsub : Dat.sig ⊆ Dat.sig1 :=
    m.hσ1
  have hE₀M : m.A ⊓ m.L ≤ m.M := fun a ha => m.R_le_M (m.A_le_R ha.1)
  have hE₀H : m.A ⊓ m.L ≤ centralizer ({x} : Set G) := fun e he =>
    mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]; exact hxC e he.2
  have hvH : v ∈ centralizer ({x} : Set G) := mem_centralizer_iff.2 fun y hy => by
    rw [Set.mem_singleton_iff.1 hy]
    calc x * v = (x * v * x⁻¹) * x := by group
      _ = v * x := by rw [hxv]
  have hvM : v ∈ m.M := CFSG.LieType.BorelTits.pCoreOf_le 2 m.M hv
  have hpcore : pCoreOf 2 (centralizer ({x} : Set G) ⊓ m.M) ≠ ⊥ := by
    set N : Subgroup G := m.V ⊓ centralizer ({x} : Set G) with hN
    have hNle : N ≤ pCoreOf 2 (centralizer ({x} : Set G) ⊓ m.M) := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
      · exact fun y hy => ⟨hy.2, CFSG.LieType.BorelTits.pCoreOf_le 2 m.M hy.1⟩
      · intro g hg
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨le_normalizer_pCoreOf 2 m.M hg.2, Subgroup.le_normalizer hg.1⟩
      · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 m.M).to_le inf_le_left
    intro hb
    have := hNle ⟨hv, hvH⟩
    rw [hb] at this
    exact hv1 (Subgroup.mem_bot.1 this)
  have hnotM : ¬ centralizer ({x} : Set G) ≤ m.M := by
    intro h
    apply m.hZ.not_le
    have hLM : m.L ≤ m.M := fun l hl => h (mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]; exact hxC l hl)
    have : m.H ≤ m.M := by
      rw [h619]
      exact sup_le hLM inf_le_right
    exact this
  have key := h67 hsub m.r m.hr m.d.odd (m.A ⊓ m.L) hE₀M
    ((m.isElemAbelian_A).mono inf_le_left) (m.card_A_inf_L h620) h632 (centralizer ({x} : Set G))
    hE₀H (centralizer_singleton_ne_top Dat.standing.simple Dat.standing.nonab hx1) hpcore hnotM
  have h3 : m.r = 3 := key.1
  have : 3 < m.r := h635
  omega

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
