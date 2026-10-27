module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreA

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec93Omega_Z0_le_LB (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec9Hyp hc n t) (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    Z0 ≤ LB M Q B := by
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  obtain ⟨hprod, hcomm, -⟩ := sec9_N51 h34 h311a hNC hs hr
  rw [HS9.isCentrePre_eq_inf91 hs hr hprod hcomm hZ0]
  exact inf_le_left

theorem sec93Omega_of_centre_le {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {h : G} (hZH : Z0 ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B)) :
    Z0 ⊓ (LB M Q B ⊓ conjSubgroup h (LB M Q B)) ≠ Q := by
  intro hQ
  have htZ : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) hs.mem hZ0
  have ht : t ∈ Z0 ⊓ (LB M Q B ⊓ conjSubgroup h (LB M Q B)) :=
    ⟨htZ, hZH htZ⟩
  rw [hQ] at ht
  exact hs.notQ ht

end CFSG.RankThree.GF2n.Stroth80
