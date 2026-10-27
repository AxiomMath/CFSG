module

public import CFSG.RankThree.PartOne.CTP.SeitzExc
public import CFSG.RankThree.PartOne.K133.ParA
public import CFSG.RankThree.PartOne.Q1327T.Item7Basic

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
open CFSG.RankThree.PartOne.Census3 (IsoLie)


theorem row8U3Item_two : Row8U3Item 2 := by
  intro Q _ _ p g Ē hX h
  exfalso
  have hp := h.prime
  have h5 := h.five_le
  obtain ⟨A, hAel, hAcard⟩ := h.exists_image
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := h.quasisimple.2.1
  have hZ : Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥ :=
    center_eq_bot_of_simple_nonabelian h.quasisimple.2.2
  obtain ⟨k, hk⟩ := CTP.card_mulAut_dvd_smallRee (ℓ := 3) rfl (CTP.reeTitsModel_reeG2 1 hX)
  have hinj : Function.Injective (MulAut.conj : (Q ⧸ Subgroup.center Q) →* _) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.center (Q ⧸ Subgroup.center Q) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := DFunLike.congr_fun hx z
      rw [MulAut.conj_apply, MulAut.one_apply] at h1
      calc z * x = x * z * x⁻¹ * x * 1 := by rw [h1]; group
        _ = x * z := by group
    rwa [hZ, Subgroup.mem_bot] at hxc
  have h1 : Nat.card (Q ⧸ Subgroup.center Q) ∣ Nat.card (MulAut (Q ⧸ Subgroup.center Q)) :=
    Subgroup.card_dvd_of_injective _ hinj
  have h2 : p ^ 2 ∣ Nat.card (Q ⧸ Subgroup.center Q) := hAcard ▸ Subgroup.card_subgroup_dvd_card A
  exact CTP.not_sq_dvd_smallRee_aut hp h5 (h2.trans (h1.trans hk))

end CFSG.RankThree.PartOne.Q1327T
