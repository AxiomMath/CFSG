module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2CharacteristicSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.SymmetricFourCommutator
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.example_1_3
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace CFSG
end CFSG
open CFSG

/-!
# The derived subgroup of odd projective general linear groups

The canonical map `PSL₂(K) → PGL₂(K)` contains the derived subgroup for every
field.  When `|K| > 3`, Huppert--Blackburn XI.1.3 supplies simplicity of
`PSL₂(K)`, so the nontrivial derived subgroup pulls back to all of `PSL₂(K)`.
Consequently the derived subgroup of `PGL₂(K)` is exactly the canonical
embedded `PSL₂(K)`.

The small field `|K| = 3` is deliberately excluded here: `PSL₂(3) ≃ A₄` is
not simple and needs its own explicit argument.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- The derived subgroup of `PGL₂(K)` lies in the canonical embedded
`PSL₂(K)`. -/
public theorem pgl2_commutator_le_psl2_range
    (K : Type u) [Field K] [Finite K] :
    commutator (PGL2 K) ≤
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := K)).range := by
  let mkPGL : Matrix.GeneralLinearGroup (Fin 2) K →* PGL2 K :=
    Matrix.ProjGenLinGroup.mk
  let toPGL : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hmkRange : mkPGL.range = ⊤ :=
    MonoidHom.range_eq_top.mpr Matrix.ProjGenLinGroup.mk_surjective
  have hmapComm :
      (commutator (Matrix.GeneralLinearGroup (Fin 2) K)).map mkPGL =
        commutator (PGL2 K) := by
    rw [map_commutator_eq, hmkRange]
    rfl
  rw [← hmapComm]
  rintro _ ⟨g, hg, rfl⟩
  have hgdetUnit : Matrix.GeneralLinearGroup.det g = 1 :=
    MonoidHom.mem_ker.mp
      (Abelianization.commutator_subset_ker Matrix.GeneralLinearGroup.det hg)
  have hgdet : Matrix.det g.1 = 1 := by
    simpa using congrArg Units.val hgdetUnit
  let s : Matrix.SpecialLinearGroup (Fin 2) K := ⟨g.1, hgdet⟩
  have hsGL : Matrix.SpecialLinearGroup.toGL s = g := by
    ext i j
    rfl
  refine ⟨QuotientGroup.mk s, ?_⟩
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, hsGL]

/-- For `|K| > 3`, the derived subgroup of `PGL₂(K)` is precisely the
canonical image of `PSL₂(K)`. -/
public theorem pgl2_commutator_eq_psl2_range_of_card_gt_three
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    commutator (PGL2 K) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := K)).range := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let toPGL : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hle : commutator (PGL2 K) ≤ toPGL.range := by
    simpa [toPGL] using pgl2_commutator_le_psl2_range K
  have hcomm_ne : commutator (PGL2 K) ≠ ⊥ :=
    (pgl2_commutator_ne_bot_ne_top K hK).1
  rcases BenderSuzuki.External.huppert_blackburn_XI_example_1_3_a K with
    ⟨_hOmegaCard, _rho, _iota, _hrho, _hiota, _hiota_apply, _hrho_apply,
      _hiota_normal, _hiota_index, _hsharp, hlarge,
      _hsmall_two, _hsmall_three⟩
  have hsimple : IsSimpleGroup (PSL2 K) := (hlarge hcard).1
  let Cpre : Subgroup (PSL2 K) := (commutator (PGL2 K)).comap toPGL
  have hCpre_normal : Cpre.Normal := by
    dsimp [Cpre]
    exact Subgroup.Normal.comap (inferInstance : (commutator (PGL2 K)).Normal) toPGL
  have hCpre_ne : Cpre ≠ ⊥ := by
    intro hbot
    apply hcomm_ne
    apply le_antisymm
    · intro x hx
      rcases hle hx with ⟨y, rfl⟩
      have hy : y ∈ Cpre := hx
      have hybot : y ∈ (⊥ : Subgroup (PSL2 K)) := by
        simpa [hbot] using hy
      simpa using congrArg toPGL (show y = 1 from hybot)
    · exact bot_le
  have hCpre_top : Cpre = ⊤ :=
    ((haveI := hCpre_normal; hsimple.eq_bot_or_eq_top_of_normal Cpre)).resolve_left hCpre_ne
  apply le_antisymm hle
  intro x hx
  rcases hx with ⟨y, rfl⟩
  have hy : y ∈ Cpre := by
    rw [hCpre_top]
    trivial
  exact hy

/-- A group isomorphic to `PGL₂(K)`, for `|K| > 3`, has derived subgroup
isomorphic to `PSL₂(K)`. -/
public theorem commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
    {Q : Type u} [Group Q] [Finite Q]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : Q ≃* PGL2 K) :
    Nonempty (commutator Q ≃* PSL2 K) := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let toPGL : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hmap : (commutator Q).map e.toMonoidHom = commutator (PGL2 K) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  have hcommRange : commutator (PGL2 K) = toPGL.range := by
    simpa [toPGL] using
      pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard
  let eQmap : commutator Q ≃* (commutator Q).map e.toMonoidHom :=
    Subgroup.equivMapOfInjective (commutator Q) e.toMonoidHom e.injective
  have htopMap : (⊤ : Subgroup (PSL2 K)).map toPGL = toPGL.range := by
    exact (MonoidHom.range_eq_map toPGL).symm
  let eTopRange : (⊤ : Subgroup (PSL2 K)) ≃* toPGL.range :=
    (Subgroup.equivMapOfInjective (⊤ : Subgroup (PSL2 K)) toPGL
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).trans
        (MulEquiv.subgroupCongr htopMap)
  exact ⟨eQmap.trans (MulEquiv.subgroupCongr hmap) |>.trans
    (MulEquiv.subgroupCongr hcommRange) |>.trans
    eTopRange.symm |>.trans Subgroup.topEquiv⟩

/-- A normal subgroup modeled by large-field `PGL₂(K)` contains a
characteristic-derived normal subgroup modeled by `PSL₂(K)`. -/
public theorem exists_normal_psl2_core_of_normal_mulEquiv_pgl2_card_gt_three
    {R : Type u} [Group R] [Finite R]
    (N : Subgroup R) (hNnormal : N.Normal)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : N ≃* PGL2 K) :
    ∃ L : Subgroup R, L.Normal ∧ L ≤ N ∧ Nonempty (L ≃* PSL2 K) := by
  let C : Subgroup N := commutator N
  let L : Subgroup R := C.map N.subtype
  let : C.Characteristic := by
    dsimp [C]
    infer_instance
  let : N.Normal := hNnormal
  have hLnormal : L.Normal := by
    dsimp [L]
    exact ConjAct.normal_of_characteristic_of_normal
  have hLle : L ≤ N := by
    dsimp [L]
    exact Subgroup.map_subtype_le C
  have eC : Nonempty (C ≃* PSL2 K) := by
    simpa [C] using
      commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three K hK hcard e
  let eCL : C ≃* L :=
    Subgroup.equivMapOfInjective C N.subtype N.subtype_injective
  exact ⟨L, hLnormal, hLle, ⟨eCL.symm.trans eC.some⟩⟩

/-- A group isomorphic to `S₄` has derived subgroup isomorphic to `A₄`. -/
public theorem commutator_mulEquiv_alternatingGroup_of_mulEquiv_perm_four
    {Q : Type u} [Group Q] [Finite Q]
    (e : Q ≃* Equiv.Perm (Fin 4)) :
    Nonempty (commutator Q ≃* alternatingGroup (Fin 4)) := by
  have hmap : (commutator Q).map e.toMonoidHom =
      commutator (Equiv.Perm (Fin 4)) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  let eQmap : commutator Q ≃* (commutator Q).map e.toMonoidHom :=
    Subgroup.equivMapOfInjective (commutator Q) e.toMonoidHom e.injective
  exact ⟨(eQmap.trans (MulEquiv.subgroupCongr hmap)).trans
    (MulEquiv.subgroupCongr commutator_perm_fin_four_eq_alternatingGroup)⟩

/-- A normal subgroup modeled by `PGL₂(3) ≃ S₄` contains its
characteristic derived subgroup, modeled by `PSL₂(3) ≃ A₄`. -/
public theorem exists_normal_psl2_three_core_of_normal_mulEquiv_pgl2_three
    {R : Type u} [Group R] [Finite R]
    (N : Subgroup R) (hNnormal : N.Normal)
    (e : N ≃* PGL2 (ZMod 3)) :
    ∃ L : Subgroup R, L.Normal ∧ L ≤ N ∧
      Nonempty (L ≃* PSL2 (ZMod 3)) := by
  let C : Subgroup N := commutator N
  let L : Subgroup R := C.map N.subtype
  let : C.Characteristic := by
    dsimp [C]
    infer_instance
  let : N.Normal := hNnormal
  have hLnormal : L.Normal := by
    dsimp [L]
    exact ConjAct.normal_of_characteristic_of_normal
  have hLle : L ≤ N := by
    dsimp [L]
    exact Subgroup.map_subtype_le C
  have eC : Nonempty (C ≃* alternatingGroup (Fin 4)) := by
    simpa [C] using
      commutator_mulEquiv_alternatingGroup_of_mulEquiv_perm_four
        (e.trans pgl2_three_equiv_perm)
  let eCL : C ≃* L :=
    Subgroup.equivMapOfInjective C N.subtype N.subtype_injective
  exact ⟨L, hLnormal, hLle,
    ⟨(eCL.symm.trans eC.some).trans psl2_three_equiv_alternatingGroup.symm⟩⟩

end CFSG.GorensteinWalter
