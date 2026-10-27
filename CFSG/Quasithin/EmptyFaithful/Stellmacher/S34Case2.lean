module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Case1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
variable {δ δ' : Geo H M}

theorem comm_A0_eq_Zv (hG : Glob H M S) (hp : PD δ δ')
    (h : ⁅Vn δ ⊓ Qv δ', Vn δ'⁆ ≠ ⊥) : ⁅Vn δ ⊓ Qv δ', Vn δ'⁆ = Zv δ' := by
  rw [Subgroup.commutator_comm] at h ⊢
  have hle : ⁅Vn δ', Vn δ ⊓ Qv δ'⁆ ≤ Zv δ' :=
    (Subgroup.commutator_mono le_rfl inf_le_right).trans (comm_Vn_Qv_le hG hp.vδ')
  by_contra hne
  apply h
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro b hb a ha
  rcases aon_Vn hG hp.vδ' ha.2 with h0 | h1
  · have hm := Subgroup.commutator_mem_commutator hb (Subgroup.mem_zpowers a)
    rw [h0] at hm
    exact hm
  · exfalso
    apply hne
    refine le_antisymm hle ?_
    rw [← h1]
    exact Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr ha)

theorem case3_data (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ') :
    ⁅Vn δ ⊓ Qv δ', Vn δ'⁆ ≠ ⊥ ∧ ¬ Vn δ' ≤ Qv δ ∧ ⁅Vn δ' ⊓ Qv δ, Vn δ⁆ ≠ ⊥ := by
  have h1 : ⁅Vn δ ⊓ Qv δ', Vn δ'⁆ ≠ ⊥ := fun h => case1_false hG hirr h15 hng hp h
  have h2 : ¬ Vn δ' ≤ Qv δ := by
    intro hB
    have hZ := comm_A0_eq_Zv hG hp h1
    have hAB : ⁅Vn δ, Vn δ'⁆ ≤ Zv δ :=
      (Subgroup.commutator_mono le_rfl hB).trans (comm_Vn_Qv_le hG hp.vδ)
    have hle : Zv δ' ≤ Zv δ := by
      rw [← hZ]
      exact (Subgroup.commutator_mono inf_le_left le_rfl).trans hAB
    have heq : Zv δ' = Zv δ :=
      Subgroup.eq_of_le_of_card_ge hle
        (le_of_eq (card_Zv_eq_of_vtype hG hp.vδ hp.vδ'))
    exact pd_not_comm_le hG hp (heq ▸ hAB)
  refine ⟨h1, h2, ?_⟩
  exact fun h => case1_false hG hirr h15 hng (hp.symm' h2) h

end S34

end F53.Stellmacher

end CFSG.Quasithin
