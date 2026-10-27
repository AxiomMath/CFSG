module

public import CFSG.RankThree.PartOne.S11d.FixedFactsRee
public import CFSG.Sporadic.Schreier.TitsIso

public section

namespace CFSG.RankThree.PartOne.TCF

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix CFSG.Sporadic.Schreier.Tits
open CFSG.LieType.Simplicity (titsData)



theorem tits_of_fixed {C : Type} [Group C] [Finite C] {α : MulAut C} {k : Type} [Field k]
    [Finite k] [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2)
    (e : ↥(fixSub α) ≃* ReeTag.F4.reeGamma k 0) :
    ∃ _ : ↥(commutator ↥(fixSub α)) ≃* ↥titsD,
      (∀ (y : ↥(fixSub α)) (m : ℕ), Odd m → y ^ m = 1 → y ∈ commutator ↥(fixSub α)) ∧
      (∀ y : ↥(commutator ↥(fixSub α)), (((y : ↥(fixSub α)) : C)) ∈ fixRes α) := by
  classical
  have : Fact (Nat.card k = 2) := ⟨hk⟩
  have : Finite (ModGL ReeTag.F4.tag k) := finite_modGL
  have : Finite ↥(adjointGroup ReeTag.F4.tag k) := Subtype.finite
  set W₂ : Subgroup ↥(adjointGroup ReeTag.F4.tag k) := reeFixed ReeTag.F4 k 0 with hW₂
  have : Finite ↥W₂ := Subtype.finite
  let eW : ↥(fixSub α) ≃* ↥W₂ := e.trans (reeFixedEquivReeGamma k 0).symm
  have hT := titsData k hk
  have hsup := hT.commutator_sup_zpowers_eq_top hk
  have hg2 := hT.g₁_sq_mem
  have : (commutator ↥W₂).Normal := Subgroup.commutator_normal ⊤ ⊤
  have hperfW : Group.IsPerfect ↥(commutator ↥W₂) := hT.isPerfect hk
  have hcomm : (commutator ↥(fixSub α)).map eW.toMonoidHom = commutator ↥W₂ := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ eW.surjective]
  let e' : ↥(commutator ↥(fixSub α)) ≃* ↥(commutator ↥W₂) :=
    (Subgroup.equivMapOfInjective _ eW.toMonoidHom eW.injective).trans
      (MulEquiv.subgroupCongr hcomm)
  refine ⟨e'.trans titsDerivedIso, ?_, ?_⟩
  · intro y m hm hy
    have hw : (eW y) ^ m = 1 := by rw [← map_pow, hy, map_one]
    have hmem : eW y ∈ commutator ↥W₂ := mem_of_odd_pow_of_sup_zpowers hsup hg2 hm hw
    rw [← hcomm] at hmem
    obtain ⟨z, hz, hzy⟩ := hmem
    exact (eW.injective hzy) ▸ hz
  · have hperf : Group.IsPerfect ↥(commutator ↥(fixSub α)) :=
      Group.IsPerfect.ofSurjective (f := e'.symm.toMonoidHom) e'.symm.surjective
    have hsub : commutator ↥(fixSub α) ≤ perfectResidual ↥(fixSub α) :=
      (perfect_residual_transport (MonoidHom.id ↥(fixSub α))).2.2 _ hperf
    intro y
    exact ⟨(y : ↥(fixSub α)), hsub y.2, rfl⟩

end CFSG.RankThree.PartOne.TCF
