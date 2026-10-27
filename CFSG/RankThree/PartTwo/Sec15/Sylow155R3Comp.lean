module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3CompA
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3CompB
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3T28Q
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Rank5
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Datum

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

variable {Q : Type} [Group Q] [Finite Q] {c d g : Q} {A B₀ K V₀ U : Subgroup Q}

theorem Res3QBase.res3QCompFacts (h : Res3QBase c d A B₀ K) : Res3QCompFacts c d A B₀ K where
  le_centralizer _ hJ hJK := h.le_centralizer hJ hJK
  unique _ _ h₁ h₂ h₁K h₂K := h.eq_of_isComponent h₁ h₂ h₁K h₂K
  d_mem _ hJ hJK := h.d_mem_of_isComponent (fun _ hJ hJK => h.le_centralizer hJ hJK)
    (fun _ _ h₁ h₂ h₁K h₂K => h.eq_of_isComponent h₁ h₂ h₁K h₂K)
    (fun _ hJ hJK _ hz hz3 => h.mem_zpowers_of_mem_center hJ hJK hz hz3) h.inf_centralizer
    (fun _ hxK hxc hx3 => h.mem_of_pow_three hxK hxc hx3) (fun _ hx => h.mem_normalizer hx)
    (fun _ hJ => h.three_dvd_card hJ) hJ hJK
  center_pGroup _ hJ _ := h.isPGroup_center hJ
  normalizes _ hJ _ hx := h.mem_normalizer_of_isComponent
    (fun _ _ h₁ h₂ h₁K h₂K => h.eq_of_isComponent h₁ h₂ h₁K h₂K)
    (fun _ hx => h.mem_normalizer hx) hJ hx
  inf_centralizer := h.inf_centralizer

theorem Res3Q.false_of_noDatum (hND : Res3NoDatum) (h : Res3Q c d g A B₀ K V₀ U) : False :=
  have hC := h.toRes3QBase.res3QCompFacts
  h.false_of_res3NoDatum hND hC (h.exists_isComponent hC) fun _ hJ hJK => h.rank5 hC hJ hJK

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
