module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec8.Hering611RSp62Inner

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

theorem kf_sp62Out : KF_Sp62Out := by
  intro G _ _ L hL g hg
  have hmap : L.map (MulAut.conj g).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  let α : MulAut L := (L.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hmap)
  obtain ⟨γ, hγ⟩ := CFSG.RankThree.PartTwo.Sec8.Hering611.exists_conj_eq_of_sp62 hL α
  refine ⟨γ, γ.2, fun x hx => ?_⟩
  have h := congrArg (fun β : MulAut L => ((β ⟨x, hx⟩ : L) : G)) hγ
  have h1 : ((α ⟨x, hx⟩ : L) : G) = g * x * g⁻¹ := rfl
  simpa [h1] using h

end CFSG.RankThree.PartTwo.Sec21.FF81
