module

public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5SpConsumers
public import CFSG.RankThree.GF2n.Stroth80.Sec51Sp
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix


theorem sec8CommN_of_311 (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h311b : Stroth311bCommStatement) : Sec8CommNStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0
  obtain ⟨K, fK, finK, hK, m, hm, φ, hφ, hker, hact⟩ := hs.spNat
  obtain ⟨u, -, hL, hr'⟩ := hc.sp_points h34 hRoot hs.toSec5 hK hm φ hφ hker hact
  obtain ⟨r, hr, hplane, -⟩ := hc.exists_hypPlane_sp h34 hRoot hs.toSec5 hs.spNat
  have hnotSL : ¬ SLNat hc t := not_slNat_of_spNat hc hs.spNat
  have hRne : Rt M (LB M Q B) t ≠ LB M Q B := by
    intro heq
    have hne := (hr' ⟨r, hr⟩).1.mp hplane
    have hrL : r ∈ LB M Q B := heq ▸ hr
    have hmem : φ ⟨r, hr⟩ ∈ LspGL m K u := by
      rw [← hL]
      exact ⟨⟨r, hr⟩, Subgroup.mem_subgroupOf.mpr hrL, rfl⟩
    exact hne (by rw [LspGL_mulVec_self hmem, spForm_self])
  obtain ⟨T, hT⟩ := exists_centLB hc t
  have hNNT := h311b G M Q Z B hc n hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2
    hs.toSec5.gen t hs.toSec5.mem hs.toSec5.notQ hRne hnotSL T hT
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (LB M Q B) hs.toSec5.mem
  have hTZ0 : T ≤ Z0 := fun x hx => by
    refine hZ0.mem_iff.mpr ⟨hLR ((hT x).mp hx).1, fun r' hr' => ?_⟩
    have h1 := ((hT x).mp hx).2 r' hr'
    rw [← commutatorElement_inv]
    exact Q.inv_mem h1
  exact hNNT.trans hTZ0

end CFSG.RankThree.GF2n.Stroth80
