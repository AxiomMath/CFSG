module

public import CFSG.Quasithin.Vol2.KGFactC31EBasis
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.KGC31.E16

open Matrix CFSG.Assembly.LowTwoRank

theorem mem_statedSL {n : ℕ} (g : GL (Fin n) (ZMod 2)) : g ∈ StatedSL n (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSL_zmod_two g

variable {Γ : Type*} [Group Γ] {n : ℕ} {v : Fin n → Γ} (hv : EBasis v)

@[expose] noncomputable def eNHom {X : Subgroup Γ} (hX : X ≤ eNorm hv) :
    ↥X →* ↥(StatedSL n (ZMod 2)) :=
  ((eGL hv).comp (Subgroup.inclusion hX)).codRestrict _ fun _ => mem_statedSL _

theorem eNHom_coe {X : Subgroup Γ} (hX : X ≤ eNorm hv) (x : ↥X) :
    (((eNHom hv hX x : ↥(StatedSL n (ZMod 2))) : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = eMat hv ⟨x, hX x.2⟩ := rfl

theorem eNHom_eq_one_iff {X : Subgroup Γ} (hX : X ≤ eNorm hv) (x : ↥X) :
    eNHom hv hX x = 1 ↔ (x : Γ) ∈ Subgroup.centralizer (eSub hv : Set Γ) := by
  rw [← eMat_eq_one_iff hv ⟨x, hX x.2⟩]
  constructor
  · intro h
    have := congrArg (fun y : ↥(StatedSL n (ZMod 2)) =>
      ((y : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) h
    simpa [eNHom_coe] using this
  · intro h
    apply Subtype.ext
    apply Units.ext
    rw [eNHom_coe, h]
    rfl

theorem eq_one_of_pow_four : ∀ r : ZMod 2, r ^ 4 = 1 → r = 1 := by decide

theorem center_sl4 : Subgroup.center (SpecialLinearGroup (Fin 4) (ZMod 2)) = ⊥ := by
  refine eq_bot_iff.mpr fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  rw [eq_one_of_pow_four r hr] at hrA
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA]
  simp

@[expose] noncomputable def slEquivPSL4 :
    SpecialLinearGroup (Fin 4) (ZMod 2) ≃* ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2) :=
  ((QuotientGroup.quotientMulEquivOfEq center_sl4).trans QuotientGroup.quotientBot).symm

theorem isSimpleGroup_statedSL4 : IsSimpleGroup ↥(StatedSL 4 (ZMod 2)) := by
  obtain ⟨-, hs, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 4)
    (by norm_num) (Or.inl (by norm_num))
  have := hs
  exact ((specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm.trans slEquivPSL4).isSimpleGroup

theorem card_statedSL4 : Nat.card ↥(StatedSL 4 (ZMod 2)) = 20160 :=
  CFSG.Open.StatedAPI.card_statedSL_four_zmod_two

@[expose] noncomputable def statedSLEquivProj4 :
    ↥(StatedSL 4 (ZMod 2)) ≃* StatedProj (StatedSL 4 (ZMod 2)) :=
  ((specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm.trans slEquivPSL4).trans
    (projectiveSpecialLinearGroupEquivStatedProj 4 (ZMod 2))

theorem isPSL_of_equiv4 {X : Type} [Group X] (e : X ≃* ↥(StatedSL 4 (ZMod 2))) :
    CFSG.Quasithin.IsPSL 4 2 1 X :=
  ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, ZMod 2, inferInstance,
    inferInstance, by rw [Nat.card_zmod]; norm_num, ⟨e.trans statedSLEquivProj4⟩⟩

end CFSG.Quasithin.KGC31.E16

end
