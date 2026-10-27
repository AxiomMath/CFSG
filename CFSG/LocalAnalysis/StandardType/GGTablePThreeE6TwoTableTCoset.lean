module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoTableTBridge

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Certificates.Data.E6TableT

private lemma e6tCoset_threeVarpiOne_eq :
    Certificates.Data.E6TableTTwo.threeVarpiOne = List.ofFn e6ThreeVarpiOne := rfl

private lemma e6tCoset_int_emod (x : ℤ) : (x % 3 == 0) = true ↔ ((x : ZMod 3) = 0) := by
  rw [beq_iff_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
  exact Iff.rfl

private lemma e6tCoset_threeVarpiOne_getD (k : ℕ) (hk : k < Tag.E6.rank) :
    Certificates.Data.E6TableTTwo.threeVarpiOne.getD k 0 = e6ThreeVarpiOne ⟨k, hk⟩ := by
  rw [e6tCoset_threeVarpiOne_eq,
    List.getD_eq_getElem (l := List.ofFn e6ThreeVarpiOne) (d := 0) (n := k) (by simpa using hk),
    List.getElem_ofFn]

private lemma e6tCoset_ofFn_getD (f : Fin Tag.E6.rank → ℤ) (k : ℕ) (hk : k < Tag.E6.rank) :
    (List.ofFn f).getD k 0 = f ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem (l := List.ofFn f) (d := 0) (n := k) (by simpa using hk),
    List.getElem_ofFn]

private lemma e6tCoset_all_iff (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) :
    (List.range 6).all (fun k =>
        ((List.ofFn (ρ e6ThreeVarpiOne)).getD k 0 -
          Certificates.Data.E6TableTTwo.threeVarpiOne.getD k 0) % 3 == 0) = true ↔
      E6CosetW ρ := by
  rw [List.all_eq_true]
  constructor
  · intro H k
    have hk : k.val < Tag.E6.rank := k.isLt
    have hmem : k.val ∈ List.range 6 := List.mem_range.mpr (show k.val < 6 from hk)
    have hb := H k.val hmem
    have h1 : (List.ofFn (ρ e6ThreeVarpiOne)).getD k.val 0 = ρ e6ThreeVarpiOne k := by
      rw [e6tCoset_ofFn_getD _ _ hk]
    have h2 : Certificates.Data.E6TableTTwo.threeVarpiOne.getD k.val 0 = e6ThreeVarpiOne k := by
      rw [e6tCoset_threeVarpiOne_getD _ hk]
    rw [h1, h2] at hb
    exact (e6tCoset_int_emod _).mp hb
  · intro H k hk
    have hk' : k < Tag.E6.rank := List.mem_range.mp hk
    have h1 : (List.ofFn (ρ e6ThreeVarpiOne)).getD k 0 = ρ e6ThreeVarpiOne ⟨k, hk'⟩ :=
      e6tCoset_ofFn_getD _ _ hk'
    have h2 : Certificates.Data.E6TableTTwo.threeVarpiOne.getD k 0 =
        e6ThreeVarpiOne ⟨k, hk'⟩ := e6tCoset_threeVarpiOne_getD _ hk'
    rw [h1, h2]
    exact (e6tCoset_int_emod _).mpr (H ⟨k, hk'⟩)

theorem e6CosetW_iff_cosetW (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y) :
    E6CosetW ρ ↔ Certificates.Data.E6TableTTwo.cosetW (bList fun i => ρ (Pi.single i 1)) = true := by
  have hact : act (bList fun i => ρ (Pi.single i 1)) Certificates.Data.E6TableTTwo.threeVarpiOne =
      List.ofFn (ρ e6ThreeVarpiOne) := by
    rw [e6tCoset_threeVarpiOne_eq]
    exact act_bList_ofFn ρ hadd e6ThreeVarpiOne
  rw [E6CosetW, Certificates.Data.E6TableTTwo.cosetW, hact]
  exact (e6tCoset_all_iff ρ).symm

end CFSG.StandardType.TablePThreeKG

end
