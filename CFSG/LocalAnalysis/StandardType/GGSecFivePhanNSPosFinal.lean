module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTransport
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiag
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPerm
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {f n : ℕ} {ψ : Su K 2 f n →* G}

theorem ggNSDiag_position (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) :
    GGTableBPosSU p Bs ψ.range K f n ψ := by
  obtain ⟨ε, hε, hrefl⟩ := ggNSDiag_automizer_perm h hd
  refine ⟨ε, hrefl, fun a b hab => ggNSDiag_rankOne_block h hd a b hab _ (fun s => ?_)⟩
  have := hε (Equiv.swap a b) s
  rwa [Equiv.swap_inv] at this

theorem ggNSLocal_position (hC : GGSecFiveNSCornerInput) (h : GGNSLocalHyp p B Bs K f n ψ) :
    ∃ c : Su K 2 f n, GGTableBPosSU p Bs ψ.range K f n (ψ.comp (MulAut.conj c).toMonoidHom) := by
  obtain ⟨c, hc⟩ := ggNSLocal_exists_diag hC h
  have hr : (ψ.comp (MulAut.conj c).toMonoidHom).range = ψ.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective, Subgroup.map_top]
  refine ⟨c, ?_⟩
  have := ggNSDiag_position (h.comp_conj c) hc
  rwa [hr] at this

end CFSG.StandardType

end
