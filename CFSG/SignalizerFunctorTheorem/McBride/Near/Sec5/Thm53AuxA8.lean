module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.Thm41
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm52
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA4

public section

open CFSG.Open
open scoped Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53A

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

structure Setting (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (W : Subgroup G) : Prop where
  mem_mtil : W ∈ mtil p A θ
  not_isSolvable : ¬ Group.IsSolvable ↥W
  sol_mul : ∀ Z ∈ mhat p A θ, ∀ U ∈ mhat p A θ, (Z : Set G) * (sol W : Set G) = (kOf W : Set G) →
    Z ≤ U → (Z : Set G) * (sol U : Set G) = (kOf U : Set G)
  le_of_kOf_le : ∀ U ∈ mhat p A θ, kOf W ≤ U → U ≤ W
  isGreatest : ∀ Z ∈ mhat p A θ, ∀ T ∈ mhat p A θ,
    (Z : Set G) * (sol W : Set G) = (kOf W : Set G) → Group.IsSolvable ↥T → sol W ≤ T →
      IsGreatest {M | M ≤ T ∧ Admits Z M} (sol W)

theorem exists_setting
    (h : Counterexample p A θ) : ∃ W : Subgroup G, Setting p A θ W := by
  obtain ⟨W, hW, hns, hc, hd, he⟩ :=
    thm41 h.hyp.nearFunctor h.isLocallyComplete h.exists_not_solvable
  exact ⟨W, hW, hns, hc, hd, he⟩

omit [Finite G] in
theorem admits_thetaMG (Y : Subgroup G) : Admits (dsub A θ) (thetaMG p A θ Y) :=
  Admits.iSup fun _ => Admits.iSup fun _ => Admits.iSup fun _ => Admits.iSup fun hP =>
    hP.1.1.1.2

omit [Finite G] in
theorem thetaMG_mem_mhat {Y : Subgroup G}
    (hI : ∀ Y ∈ dset p A θ, thetaMG p A θ Y ∈ assoc p A θ) (hY : Y ∈ dset p A θ) :
    thetaMG p A θ Y ∈ mhat p A θ :=
  ⟨hI Y hY, admits_thetaMG Y⟩

omit [Finite G] in
theorem thetaM_le_thetaMG {Y X : Subgroup G} (hX : X ∈ cset p A θ Y) :
    thetaM p A θ Y X ≤ thetaMG p A θ Y :=
  le_iSup₂ (f := fun X (_ : X ∈ cset p A θ Y) => thetaM p A θ Y X) X hX

omit [Finite G] in
theorem dsub_sup_le_centralizer (hθ : NearFunctor p A θ) {b : G} (hb : b ∈ A) :
    dsub A θ ⊔ A ≤ Subgroup.centralizer {b} :=
  sup_le ((dsub_le_centralizer hθ).trans (Subgroup.centralizer_le
    (Set.singleton_subset_iff.mpr hb)))
    (fun _ hg => Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_of_mem hθ.elemAbelian.1 hg hb))

theorem kOf_apply_le
    (h : Counterexample p A θ) {W : Subgroup G} (hW : Setting p A θ W)
    (hI : ∀ Y ∈ dset p A θ, thetaMG p A θ Y ∈ assoc p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hns : ¬ Group.IsSolvable ↥(θ a ⊓ W)) : kOf (θ a) ≤ W := by
  have hθ := h.hyp.nearFunctor
  have hHa : θ a ∈ mtil p A θ := apply_mem_mtil hθ ha ha1
  have hX : θ a ⊓ W ∈ mtil p A θ :=
    ⟨mem_assoc_of_le hθ.prime hW.mem_mtil.1 inf_le_right (Admits.inf hHa.1.1 hW.mem_mtil.1.1),
      le_inf hHa.2 hW.mem_mtil.2⟩
  obtain ⟨P, hP, hPle⟩ := exists_pair_le hθ hX hns
  have hY : dsub A θ ⊓ P.2 ∈ dset p A θ := ⟨P, hP, rfl⟩
  have hPY : P ∈ pairsY p A θ (dsub A θ ⊓ P.2) := ⟨hP, inf_comm _ _⟩
  have hWc : W ∈ cset p A θ (dsub A θ ⊓ P.2) := ⟨hW.mem_mtil, P, hPY, hPle.trans inf_le_right⟩
  have hHc : θ a ∈ cset p A θ (dsub A θ ⊓ P.2) := ⟨hHa, P, hPY, hPle.trans inf_le_left⟩
  have hV : thetaMG p A θ (dsub A θ ⊓ P.2) ∈ mhat p A θ := thetaMG_mem_mhat hI hY
  have hkW : kOf W ≤ thetaMG p A θ (dsub A θ ⊓ P.2) :=
    (kOf_le_thetaM hθ hY hWc).trans (thetaM_le_thetaMG hWc)
  have hkH : kOf (θ a) ≤ thetaMG p A θ (dsub A θ ⊓ P.2) :=
    (kOf_le_thetaM hθ hY hHc).trans (thetaM_le_thetaMG hHc)
  exact hkH.trans (hW.le_of_kOf_le _ hV hkW)

theorem exists_apply_isSolvable
    (h : Counterexample p A θ) {W : Subgroup G}
    (hW : Setting p A θ W) (hI : ∀ Y ∈ dset p A θ, thetaMG p A θ Y ∈ assoc p A θ) :
    ∃ a ∈ A, a ≠ 1 ∧ Group.IsSolvable ↥(θ a ⊓ W) := by
  obtain ⟨a, ha, ha1, hnot⟩ := h.exists_not_kOf_le hW.mem_mtil.1
  refine ⟨a, ha, ha1, ?_⟩
  by_contra hns
  exact hnot (kOf_apply_le h hW hI ha ha1 hns)

theorem perfRes_le_kOf
    (h : Counterexample p A θ) {W : Subgroup G} (hW : Setting p A θ W)
    (hI : ∀ Y ∈ dset p A θ, thetaMG p A θ Y ∈ assoc p A θ) (hin : CompInput p W) :
    perfRes W ≤ kOf W := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨a, ha, ha1, hsolv⟩ := exists_apply_isSolvable h hW hI
  have hWa := hW.mem_mtil.1
  have hle : W ⊓ Subgroup.centralizer {a} ≤ θ a ⊓ W :=
    le_inf (hWa.2.2.1 a ha ha1) inf_le_left
  have hcen : Group.IsSolvable ↥(W ⊓ Subgroup.centralizer {a}) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  exact perfRes_le_kOf_of_isSolvable_cen' hθ.prime hWa.2.2.2.1 hin (hWa.1 ha)
    (hθ.elemAbelian.2 a ha) hcen

end Thm53A

end CFSG.SignalizerFunctorTheorem.McBride.Near
