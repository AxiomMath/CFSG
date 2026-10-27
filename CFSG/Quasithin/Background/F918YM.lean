module

public import CFSG.Quasithin.EmptyFaithful.A38c11D36
public import CFSG.Quasithin.Background.F918D7
public import CFSG.Quasithin.Background.F918YB
public import CFSG.Quasithin.Background.F918YD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem d36B48qN_proved (h35 : D35)
    (hA38 : D36A38) (hL38 : D3L38) : D36B48qN := by
  intro W _ _ M Mp T L V t std hlt ht htn hMp hc hq hpsl hs
  have n : D36Norm M Mp T L V t := ⟨std, hlt, ht, htn, hMp, hc.1⟩
  by_contra hZne
  obtain ⟨s, hsT, hsN, hsV⟩ := hs
  have hUeq := d36_U_eq hL38 n
  rcases hc.2.2.2 with hUV | ⟨-, -, hall, -⟩
  · apply hsV
    have hsU : s ∈ stabSub (commSub (orbSup T V) L) := by
      rw [hUeq]
      exact le_stabSub_orbSup _ _ ⟨hsT, hsN⟩
    rw [hUV] at hsU
    exact hsU
  · obtain ⟨hU, hsum⟩ := hall s hsT hsN hsV
    obtain ⟨D, -, hDne, hDel, hDq, hDr, hDnorm⟩ := d36_quad_offender_restrict hL38 n hq
    obtain ⟨σ, hbase⟩ := d36_n4_base h35 hA38 hL38 n hc.2.2.1 hsT hsN hsV hU hsum hZne
    refine N4Core.core (A := autSub D (commSub (orbSup T V) L))
      ⟨hbase.hexp, hbase.hinv, hbase.hcomm, hbase.hnat, hbase.hZ, hbase.hσL, hbase.hne,
        hbase.hdyn, hbase.hsum, hbase.hint, ?_, hDel, ?_, ?_, hDr, hDne⟩
    · intro a ha x
      exact Subgroup.mem_normalizer_iff.mp (hDnorm ha) x
    · intro a ha b hb w
      have h3 : a w * w⁻¹ ∈ commSub (⊤ : Subgroup ↥(commSub (orbSup T V) L))
          (autSub D (commSub (orbSup T V) L)) :=
        Subgroup.subset_closure ⟨a, ha, w, Subgroup.mem_top w, rfl⟩
      have h4 : b (a w * w⁻¹) * (a w * w⁻¹)⁻¹ ∈ commSub (commSub
          (⊤ : Subgroup ↥(commSub (orbSup T V) L)) (autSub D (commSub (orbSup T V) L)))
          (autSub D (commSub (orbSup T V) L)) :=
        Subgroup.subset_closure ⟨b, hb, _, h3, rfl⟩
      have h5 : commSub (commSub (⊤ : Subgroup ↥(commSub (orbSup T V) L))
          (autSub D (commSub (orbSup T V) L))) (autSub D (commSub (orbSup T V) L)) = ⊥ := hDq
      rw [h5, Subgroup.mem_bot] at h4
      exact mul_inv_eq_one.1 h4
    · intro a _ hcomm
      exact hbase.centralizer_eq_one hcomm

end CFSG.Quasithin
