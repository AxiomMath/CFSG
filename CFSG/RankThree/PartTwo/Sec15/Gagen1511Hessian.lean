module

public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofHessConj
import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofSub
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1511Point

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open Matrix CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Assembly.RankThreeEven (projImage)

theorem isSolvable_centralizer_of_hessian {X : Type} [Group X] [Finite X] {p e : ℕ}
    [Fact p.Prime] (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e) {E : Subgroup X}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    {y : X} (hyE : y ∈ E) (hy1 : y ≠ 1) :
    Group.IsSolvable ↥(Subgroup.centralizer ({y} : Set X)) := by
  obtain ⟨π, K, _, hK, hq, τ, hτ, hτ1, dM, cM, hdM, hcM, -, hdo, -, -, Φ, hΦE⟩ :=
    Res8Hess.exists_hessian_equiv he hiso hEe hE9 htr
  let M := projImage (slPi π 3 (p ^ e) K)
  have hy0E : Φ dM ∈ E := by
    rw [← hΦE]
    exact Subgroup.mem_map.mpr ⟨dM, Subgroup.mem_sup_left (Subgroup.mem_zpowers dM), rfl⟩
  have hdM1 : dM ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hdo
    exact absurd hdo (by norm_num)
  have hy01 : Φ dM ≠ 1 := by
    intro h
    exact hdM1 (Φ.injective (by rw [h, map_one]))
  have hπ : π = false → UnitaryFieldData p e K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ e) := fun h => by subst h; exact hq
  have hdS : diagTau hτ ∈ slPi π 3 (p ^ e) K := diagTau_mem_slPi hπ hq' hτ
  have hd3 : diagTau hτ ^ 3 = 1 := diagTau_pow_three hτ
  have hd1 : ProjGenLinGroup.mk (diagTau hτ) ≠ 1 := by
    intro h
    apply hdM1
    apply Subtype.ext
    rw [hdM, h]
    rfl
  have hsolInf : Group.IsSolvable ↥(M ⊓ Subgroup.centralizer
      ({ProjGenLinGroup.mk (diagTau hτ)} : Set (ProjGenLinGroup (Fin 3) K))) :=
    KSL3Two.isSolvable_inf_centralizer_of_lift hK hq hdS hd3 hd1
  have hCeq : Subgroup.centralizer ({dM} : Set M) =
      (M ⊓ Subgroup.centralizer ({ProjGenLinGroup.mk (diagTau hτ)} :
        Set (ProjGenLinGroup (Fin 3) K))).subgroupOf M := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have h := congrArg (fun z : M => (z : ProjGenLinGroup (Fin 3) K)) hx
      simpa only [Subgroup.coe_mul, hdM] using h
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, hdM] using hx
  have hsolCM : Group.IsSolvable ↥(Subgroup.centralizer ({dM} : Set M)) := by
    haveI : Group.IsSolvable ↥(M ⊓ Subgroup.centralizer
        ({ProjGenLinGroup.mk (diagTau hτ)} : Set (ProjGenLinGroup (Fin 3) K))) := hsolInf
    let eCM : ↥(Subgroup.centralizer ({dM} : Set M)) ≃*
        ↥(M ⊓ Subgroup.centralizer ({ProjGenLinGroup.mk (diagTau hτ)} :
          Set (ProjGenLinGroup (Fin 3) K))) :=
      (MulEquiv.subgroupCongr hCeq).trans (Subgroup.subgroupOfEquivOfLe inf_le_left)
    exact Group.isSolvable_of_surjective (f := eCM.symm.toMonoidHom) eCM.symm.surjective
  have hsolX0 : Group.IsSolvable ↥(Subgroup.centralizer ({Φ dM} : Set X)) := by
    haveI : Group.IsSolvable ↥(Subgroup.centralizer ({dM} : Set M)) := hsolCM
    let eX : ↥(Subgroup.centralizer ({dM} : Set M)) ≃*
        ↥(Subgroup.centralizer ({Φ dM} : Set X)) :=
      ((Subgroup.centralizer ({dM} : Set M)).equivMapOfInjective Φ.toMonoidHom Φ.injective).trans
        (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.map_centralizer_singleton Φ dM))
    exact Group.isSolvable_of_surjective (f := eX.toMonoidHom) eX.surjective
  obtain ⟨w, -, hwy⟩ := htr (Φ dM) hy0E hy01 y hyE hy1
  have hcenw : (Subgroup.centralizer ({Φ dM} : Set X)).map (MulAut.conj w).toMonoidHom =
      Subgroup.centralizer ({y} : Set X) := by
    rw [CFSG.RankThree.PartTwo.map_centralizer_singleton (MulAut.conj w) (Φ dM),
      MulAut.conj_apply, hwy]
  haveI : Group.IsSolvable ↥(Subgroup.centralizer ({Φ dM} : Set X)) := hsolX0
  let eY : ↥(Subgroup.centralizer ({Φ dM} : Set X)) ≃*
      ↥(Subgroup.centralizer ({y} : Set X)) :=
    ((Subgroup.centralizer ({Φ dM} : Set X)).equivMapOfInjective (MulAut.conj w).toMonoidHom
      (MulAut.conj w).injective).trans (MulEquiv.subgroupCongr hcenw)
  exact Group.isSolvable_of_surjective (f := eY.toMonoidHom) eY.surjective

end CFSG.RankThree.PartTwo.Sec15.Proof1511Point
