module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1Defs
import CFSG.RankThree.PartTwo.Sec11.SimsR1OddAutL2
import CFSG.RankThree.PartTwo.Sec11.SimsR1OddAutL2Inv
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo OddAut
open CFSG.Assembly.RankThreeEven (projSL)

theorem l2CubeTwoLocal_holds : SimsR1L2CubeTwoLocal := by
  intro p _ hp5 X _ _ hX P hP hP1 S hS
  obtain ⟨e⟩ := hX
  set F := GaloisField p (3 * 1) with hFdef
  let ε : X ≃* PSL2 F := e.trans (Sec4.projSLEquivPSL F)
  have hle : P ≤ (pglToAut ε).range :=
    le_range_pglToAut_of_isPGroup_two (Fact.out : p.Prime) (card_galoisField_cube p)
      (by decide) ε hP
  have hQ : IsPGroup 2 (P.comap (pglToAut ε)) := hP.comap_of_injective _ (pglToAut_injective ε)
  have hQ1 : P.comap (pglToAut ε) ≠ ⊥ := comap_ne_bot ε hle hP1
  set ι : PSL2 F →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL with hι
  set j : X →* PGL2 F := ι.comp ε.toMonoidHom with hj
  have hjinj : Function.Injective j :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp ε.injective
  have hS'N : ∀ s ∈ S.map j, ∀ q : PGL2 F, q ∈ P.comap (pglToAut ε) ↔
      s * q * s⁻¹ ∈ P.comap (pglToAut ε) := by
    rintro _ ⟨s, hs, rfl⟩ q
    have h1 : pglToAut ε (j s) = MulAut.conj s := pglToAut_toPGL ε s
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv, h1]
    exact Subgroup.mem_normalizer_iff.mp (hS s hs) _
  have hsolv := isSolvable_of_normalizes_isPGroup_two (two_ne_zero_galoisField p hp5 _) hQ hQ1 hS'N
  let f : S →* S.map j := (j.comp S.subtype).codRestrict (S.map j) (fun s => ⟨s, s.2, rfl⟩)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hjinj
    exact congrArg Subtype.val hab
  exact Group.isSolvable_of_isSolvable_injective hf

end CFSG.RankThree.PartTwo.Sec11.SimsR1
