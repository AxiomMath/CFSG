module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47eOmega
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.SylowOpposition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47

theorem exists_mulEquiv_adjointGroup_map_eq_sylow_g2
    {Y : Type} [Group Y] [Finite Y] {p n : ℕ} (hp : p.Prime)
    (hmodel : UntwistedChevalleyModel Y .G2 (p ^ n)) (P : Sylow p Y) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : ↥(adjointGroup .G2 F) ≃* Y),
      Nat.card F = p ^ n ∧
        (P : Subgroup Y) =
          ((posUnipotent .G2 F).subgroupOf (adjointGroup .G2 F)).map φ.toMonoidHom := by
  obtain ⟨F, hFfield, hFfin, hFcard, ⟨e⟩⟩ := hmodel
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP F p := charP_of_natCard_eq_pow hp hFcard
  have hZ : Subgroup.center ↥(adjointGroup .G2 F) = ⊥ := center_adjointGroup_eq_bot
  let θ : Y ≃* ↥(adjointGroup .G2 F) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  have hUC : posUnipotent .G2 F ≤ adjointGroup .G2 F := posUnipotent_le_adjointGroup' .G2 F
  have hcardU : Nat.card (posUnipotent .G2 F) = Nat.card F ^ 6 := by
    rw [card_posUnipotent, ncard_posRoots_G2]
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index p hUC (by rw [hcardU, ncard_posRoots_G2])
  let PU : Sylow p ↥(adjointGroup .G2 F) := hUp.toSylow hUi
  have hPU : (PU : Subgroup ↥(adjointGroup .G2 F)) =
      (posUnipotent .G2 F).subgroupOf (adjointGroup .G2 F) := IsPGroup.toSylow_coe hUp hUi
  let Q : Sylow p Y := Sylow.mapSurjective (f := θ.symm.toMonoidHom) θ.symm.surjective PU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q P
  have hP : (P : Subgroup Y) =
      ((posUnipotent .G2 F).subgroupOf (adjointGroup .G2 F)).map
        (θ.symm.trans (MulAut.conj g)).toMonoidHom := by
    have h1 : (P : Subgroup Y) =
        ((PU : Subgroup ↥(adjointGroup .G2 F)).map θ.symm.toMonoidHom).map
          (MulAut.conj g).toMonoidHom := by
      rw [← hg]
      rfl
    rw [h1, hPU, Subgroup.map_map]
    rfl
  exact ⟨F, hFfield, hFfin, θ.symm.trans (MulAut.conj g), hFcard, hP⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

