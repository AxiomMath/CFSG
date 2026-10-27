module

public import CFSG.Quasithin.Vol2.KGFactC31EBasis
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.KGC31.E8

open Matrix CFSG.Assembly.LowTwoRank

theorem eq_one_of_cube : ∀ r : ZMod 2, r ^ 3 = 1 → r = 1 := by decide

theorem center_sl3 : Subgroup.center (SpecialLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
  refine eq_bot_iff.mpr fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  rw [eq_one_of_cube r hr] at hrA
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA]
  simp

@[expose] noncomputable def slEquivPSL3 :
    SpecialLinearGroup (Fin 3) (ZMod 2) ≃* ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  ((QuotientGroup.quotientMulEquivOfEq center_sl3).trans QuotientGroup.quotientBot).symm

theorem isSimpleGroup_statedSL3 : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) := by
  obtain ⟨-, hs, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3)
    (by norm_num) (Or.inl le_rfl)
  have := hs
  exact ((specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm.trans slEquivPSL3).isSimpleGroup

theorem card_statedSL3 : Nat.card ↥(StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

@[expose] noncomputable def statedSLEquivProj3 :
    ↥(StatedSL 3 (ZMod 2)) ≃* StatedProj (StatedSL 3 (ZMod 2)) :=
  ((specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm.trans slEquivPSL3).trans
    (projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 2))

theorem isPSL_of_equiv3 {X : Type} [Group X] (e : X ≃* ↥(StatedSL 3 (ZMod 2))) :
    CFSG.Quasithin.IsPSL 3 2 1 X :=
  ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2, inferInstance,
    inferInstance, by rw [Nat.card_zmod]; norm_num, ⟨e.trans statedSLEquivProj3⟩⟩

theorem mem_statedSL3 (g : GL (Fin 3) (ZMod 2)) : g ∈ StatedSL 3 (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSL_zmod_two g

variable {Γ : Type*} [Group Γ] {v : Fin 3 → Γ} (hv : EBasis v)

@[expose] noncomputable def e3Hom {X : Subgroup Γ} (hX : X ≤ eNorm hv) :
    ↥X →* ↥(StatedSL 3 (ZMod 2)) :=
  ((eGL hv).comp (Subgroup.inclusion hX)).codRestrict _ fun _ => mem_statedSL3 _

theorem e3Hom_coe {X : Subgroup Γ} (hX : X ≤ eNorm hv) (x : ↥X) :
    (((e3Hom hv hX x : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = eMat hv ⟨x, hX x.2⟩ := rfl

theorem e3Hom_eq_one_iff {X : Subgroup Γ} (hX : X ≤ eNorm hv) (x : ↥X) :
    e3Hom hv hX x = 1 ↔ (x : Γ) ∈ Subgroup.centralizer (eSub hv : Set Γ) := by
  rw [← eMat_eq_one_iff hv ⟨x, hX x.2⟩]
  constructor
  · intro h
    have := congrArg (fun y : ↥(StatedSL 3 (ZMod 2)) =>
      ((y : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
    simpa [e3Hom_coe] using this
  · intro h
    apply Subtype.ext
    apply Units.ext
    rw [e3Hom_coe, h]
    rfl

end CFSG.Quasithin.KGC31.E8

end
