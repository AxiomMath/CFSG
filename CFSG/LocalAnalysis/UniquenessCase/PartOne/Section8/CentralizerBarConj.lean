module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_inv_conj_centralizerBar_iff (t : G) (P L : Subgroup G) {x : G} :
    t⁻¹ * x * t ∈ centralizerBar P L ↔
      x ∈ centralizerBar (P.map (MulAut.conj t).toMonoidHom)
        (L.map (MulAut.conj t).toMonoidHom) := by
  constructor
  · intro hx
    obtain ⟨hxP, hxcomm⟩ := mem_centralizerBar_iff.mp hx
    have hxP' : x ∈ P.map (MulAut.conj t).toMonoidHom := by
      have hfx : (MulAut.conj t).toMonoidHom (t⁻¹ * x * t) = x := by
        change (MulAut.conj t) (t⁻¹ * x * t) = x
        rw [MulAut.conj_apply]
        group
      rw [← hfx]
      exact Subgroup.mem_map_of_mem _ hxP
    refine mem_centralizerBar_iff.mpr ⟨hxP', ?_⟩
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
    rw [CFSG.QuasithinUnique.pCoreOf_map_equiv 2 (MulAut.conj t) L]
    refine Subgroup.mem_map.mpr ⟨⁅t⁻¹ * x * t, l⁆, hxcomm l hl, ?_⟩
    rw [map_commutatorElement]
    have hfx : (MulAut.conj t).toMonoidHom (t⁻¹ * x * t) = x := by
      change (MulAut.conj t) (t⁻¹ * x * t) = x
      rw [MulAut.conj_apply]
      group
    rw [hfx]
  · intro hx
    obtain ⟨hxP', hxcomm'⟩ := mem_centralizerBar_iff.mp hx
    have hxP : (MulAut.conj t).symm x ∈ P :=
      (Subgroup.mem_map_equiv (f := MulAut.conj t)).mp hxP'
    refine mem_centralizerBar_iff.mpr ⟨?_, ?_⟩
    · simpa only [MulAut.conj_symm_apply] using hxP
    · intro l hl
      have h1 : ⁅x, (MulAut.conj t).toMonoidHom l⁆ ∈
          CFSG.Open.pCoreOf 2 (L.map (MulAut.conj t).toMonoidHom) :=
        hxcomm' _ (Subgroup.mem_map_of_mem _ hl)
      rw [CFSG.QuasithinUnique.pCoreOf_map_equiv 2 (MulAut.conj t) L] at h1
      have h2 : (MulAut.conj t).symm ⁅x, (MulAut.conj t).toMonoidHom l⁆ ∈
          CFSG.Open.pCoreOf 2 L :=
        (Subgroup.mem_map_equiv (f := MulAut.conj t)).mp h1
      have hval : (MulAut.conj t).symm ⁅x, (MulAut.conj t).toMonoidHom l⁆ =
          ⁅t⁻¹ * x * t, l⁆ := by
        rw [map_commutatorElement]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply,
          MulEquiv.symm_apply_apply]
      rwa [hval] at h2

theorem map_conj_centralizerBar (t : G) (P L : Subgroup G) :
    (centralizerBar P L).map (MulAut.conj t).toMonoidHom =
      centralizerBar (P.map (MulAut.conj t).toMonoidHom)
        (L.map (MulAut.conj t).toMonoidHom) := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simpa only [MulAut.conj_symm_apply] using mem_inv_conj_centralizerBar_iff t P L (x := x)

theorem conj_mem_centralizerBar (t : G) (P L : Subgroup G)
    (hP : P.map (MulAut.conj t).toMonoidHom = P)
    (hL : L.map (MulAut.conj t).toMonoidHom = L)
    {x : G} (hx : x ∈ centralizerBar P L) :
    t * x * t⁻¹ ∈ centralizerBar P L := by
  have hx' : (MulAut.conj t).toMonoidHom x ∈
      (centralizerBar P L).map (MulAut.conj t).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rw [map_conj_centralizerBar, hP, hL] at hx'
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hx'

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
