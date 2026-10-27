module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfOmega
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
public import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofConjPt

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {A L : Subgroup G} {c d : G}

theorem map_conj_x₀
    (h134 : Item134) (h48 : Sec4.Item4_8) (h : Ctx A c L d)
    {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G)) :
    (x₀ L d).map (MulAut.conj w).toMonoidHom = x₀ L d := by
  obtain ⟨hWd, -, -, -⟩ := omega_case2 h134 h48 h
  have hD := h.sec13Data
  have hwd : w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := hWd hw
  have hcwΩ : (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom ∈ omegaA A :=
    (map_conj_mem_omegaA_iff hw).mpr hD.zpowers_mem_omegaA
  have hwcB : w * c * w⁻¹ ∈ Subgroup.closure {c, d} :=
    omega_le_closure h134 h48 h _ hcwΩ ⟨c, Subgroup.mem_zpowers c, rfl⟩
  have hCz : Subgroup.centralizer (Subgroup.zpowers d : Set G) =
      Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCd' : Subgroup.centralizer ({w * d * w⁻¹} : Set G) =
      Subgroup.centralizer ({d} : Set G) :=
    centralizer_singleton_eq_of_zpowers_eq (zpowers_conj_eq_of_mem_normalizer hwd)
  have hCdmap : (Subgroup.centralizer ({d} : Set G)).map (MulAut.conj w).toMonoidHom =
      Subgroup.centralizer ({d} : Set G) := by
    rw [← hCz, Sec14.map_conj_centralizer, MonoidHom.map_zpowers,
      show (MulEquiv.toMonoidHom (MulAut.conj w)) d = w * d * w⁻¹ by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]]
    rw [zpowers_conj_eq_of_mem_normalizer hwd, hCz]
  calc (x₀ L d).map (MulAut.conj w).toMonoidHom
      = inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer ({d} : Set G)).map
          (MulAut.conj w).toMonoidHom) :=
        CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective
          _ (MulAut.conj w).injective _
    _ = inSubgroup perfectResidual (L.map (MulAut.conj w).toMonoidHom ⊓
          Subgroup.centralizer ({w * d * w⁻¹} : Set G)) := by
        rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj w).injective, hCdmap, ← hCd']
    _ = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
        h.conf.residual_eq_conj h.mem_d h.ne_d h.zCentral hw hwd hwcB
    _ = x₀ L d := rfl

end Ctx

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
