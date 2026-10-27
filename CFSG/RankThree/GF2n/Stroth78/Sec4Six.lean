module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusNotCentral
public import CFSG.Timmesfeld.Transvection.QTwoSp
public import CFSG.GroupTheory.ThreeTranspositions.FischerResidual
public import CFSG.RankThree.GF2n.Stroth78.Sec2Six
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module Matrix
open CFSG.GroupTheory.ThreeTranspositions

namespace Sec4Six

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem exists_mulEquiv_statedSp_of_fischerLinearModel
    {H : Type} [Group H] {D : Set H} {m : ℕ}
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hsp : fischerLinearModel D
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    Nonempty (H ≃* StatedSp m (ZMod 2)) := by
  obtain ⟨φ, hφ⟩ := hsp
  obtain ⟨ψ, -⟩ := CFSG.Timmesfeld.Transvection.QTwo.exists_sympEquiv_of_isometry
    b halt hnd φ hφ
  let e : StatedSp m (ZMod 2) ≃* TauCeti.GLSymplectic (Fin m) (ZMod 2) :=
    MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic
  exact ⟨ψ.trans e.symm⟩

theorem stroth78_46_of_structure (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hsp : fischerLinearModel
      (threeResidualClass
        (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    (hw : w = 2 * m)
    (hprod : Nonempty (Hbar z ≃*
      ↥(threeResidualQuot
        (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a))) ×
        Equiv.Perm (Fin 3)))
    (hHZ : ∀ x ∈ ⁅⁅H z, H z⁆, ⁅H z, H z⁆⁆, ∀ y ∈ ZQ z, Commute x y) :
    CFSG.RankThree.GF2n.Tim79a.StrothCaseVIII z w := by
  obtain ⟨ψ⟩ := exists_mulEquiv_statedSp_of_fischerLinearModel halt hnd hsp
  obtain ⟨e⟩ := hprod
  let e' : Hbar z ≃*
      ↥(StatedSp m (ZMod 2)) × Equiv.Perm (Fin 3) :=
    e.trans (MulEquiv.prodCongr ψ (MulEquiv.refl (Equiv.Perm (Fin 3))))
  exact ⟨m, hw, by omega, ⟨inferInstance, ⟨e'⟩⟩, hHZ, not_zq_le_centerIn_H S h⟩

end Sec4Six

end CFSG.RankThree.GF2n.Stroth78

end
