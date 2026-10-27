module

public import CFSG.RankThree.GF2n.Stroth78.Sec4SixWLbar
public import CFSG.RankThree.GF2n.Stroth78.Sec4SixWidth

import CFSG.RankThree.GF2n.Stroth78.Sec4Six

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification Matrix

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

theorem Sec4SixW.stroth78_46_of_center (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
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
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    (hZX : Subgroup.center ↥(Xsub S a) = ⊥) :
    StrothCaseVIII z w := by
  obtain ⟨α₀, hα₀, hα₀1, hO₀⟩ := Sec4Five.exists_mem_Rbar_fischerLinearModel S h h217 h3 hα hsp
  obtain ⟨β, hβL, hβ1, hβC, hLW⟩ :=
    Sec4SixW.exists_mem_Lbar_centralizer S h h217 h3 hα₀ hα₀1 hm halt hnd hO₀ hZX
  have hZ := Sec4SixW.rhoZ_Xsub_eq_one S h h217 h3 (h.mem_Tset_of_mem_Rbar hα₀ hα₀1) hm halt
    hnd hO₀
  have hβX : ∀ x ∈ threeResidualJoin (alphaInX S h hα₀),
      β * ((x : ↥(Xsub S a)) : Hbar z) = ((x : ↥(Xsub S a)) : Hbar z) * β := fun x _ =>
    (Subgroup.mem_centralizer_iff.mp hβC _ (x : ↥(Xsub S a)).2).symm
  have hw1 := Sec4SixW.two_mul_le_of_mem_centralizer S h h217 h3 hα₀ hα₀1 hm halt hnd hO₀ hZ
    hβL hβ1 hβX hLW
  have hw2 := Sec4SixW.le_two_mul S h h217 h3 hα₀ hα₀1 hm halt hnd hO₀ hZX
  have heven := Sec4SixW.even_card_centralizer_Xsub S h h217 h3 hα₀ hα₀1 hm halt hnd hO₀ hZX
  have hprod := Sec4SixW.nonempty_mulEquiv_prod_of_even S h h217 h3 (Tset_subset_Eset S a hα) hm
    halt hnd hsp hZX heven
  have hHZ := Sec4SixW.commute_of_mem_derived_two S h h217 h3 hα hm halt hnd hsp hZX
  exact Sec4Six.stroth78_46_of_structure S h h217 h3 hα hm halt hnd hsp (by omega) hprod hHZ

theorem stroth78_46
    (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
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
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    StrothCaseVIII z w :=
  Sec4SixW.stroth78_46_of_center S h h217 h3 hα hm halt hnd hsp
    (Sec4SixW.center_Xsub_eq_bot S h h217 h3 (Tset_subset_Eset S a hα) hm halt hnd hsp)

end CFSG.RankThree.GF2n.Stroth78
