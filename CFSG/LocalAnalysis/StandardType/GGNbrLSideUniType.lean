module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.Open.StatedDefs
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpTypeGU
import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpTypeGL
import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitComm
import CFSG.Open.StatedAPI
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Open.StatedAPI
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU)

theorem ggNbrLSideUni_typeSU {n a : ℕ} {E : Type} [Field E] [Finite E] {τ : E ≃+* E}
    {hτ : ∀ y, τ (τ y) = y} {M : Type} [Group M] (hn : 1 ≤ n)
    (hEc : Nat.card E = (2 ^ n) ^ 2) (hτQ : ∀ y, τ y = y ^ 2 ^ n)
    (φ : M ≃* ↥(heldSU a E τ hτ)) (hq : CFSG.IsQuasisimple M) :
    ∃ (t : StatedLieTag) (m : ℕ), ((t = .PSU ∧ m = a) ∨ (t = .PSL ∧ m = 2)) ∧
      CFSG.Blueprint.LieModel (M ⧸ Subgroup.center M) t m 2 n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqSU : CFSG.IsQuasisimple ↥(heldSU a E τ hτ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv φ hq
  have hperfSU : Group.IsPerfect ↥(heldSU a E τ hτ) := hqSU.1
  have hcomm_eq : ⁅(heldGU a E τ hτ : Subgroup (GL (Fin a) E)), heldGU a E τ hτ⁆ =
      heldSU a E τ hτ :=
    GGNbrLSideKit.commutator_heldGU_eq_heldSU_of_isPerfect (r := a) (E := E)
      (τ := τ) (hτ := hτ) hperfSU
  have e1 : ↥(commutator (heldGU a E τ hτ)) ≃* ↥(heldSU a E τ hτ) :=
    ((Subgroup.equivMapOfInjective (commutator ↥(heldGU a E τ hτ)) (heldGU a E τ hτ).subtype
        Subtype.val_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator (heldGU a E τ hτ)))).trans
      (MulEquiv.subgroupCongr hcomm_eq)
  have e : M ≃* ↥(commutator (heldGU a E τ hτ)) := φ.trans e1.symm
  have hqB : CFSG.IsQuasisimple ↥(commutator (heldGU a E τ hτ)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  have hn0 : n ≠ 0 := by omega
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  obtain ⟨t, m, htm, hmodel⟩ :=
    GGNbrLSideKit.lieModel_commutator_heldGU (n := n) (r := a) (K := GaloisField 2 n)
      (E := E) (τ := τ) (hτ := hτ) hK hn (by rw [hK]; exact hEc)
      (fun y => by rw [hK]; exact hτQ y) hqB
  exact ⟨t, m, htm, CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv e.symm hmodel⟩

theorem ggNbrLSideUni_typeSL {f b : ℕ} {E : Type} [Field E] [Finite E] {M : Type} [Group M]
    (hf : 1 ≤ f) (hE : Nat.card E = 2 ^ f) (φ : M ≃* ↥(StatedSL b E))
    (hq : CFSG.IsQuasisimple M) :
    CFSG.Blueprint.LieModel (M ⧸ Subgroup.center M) .PSL b 2 f := by
  classical
  have eSL : ↥(StatedSL b E) ≃* Matrix.SpecialLinearGroup (Fin b) E :=
    ((MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (statedSL_eq_range_toGL b E).symm)).symm
  have e : M ≃* Matrix.SpecialLinearGroup (Fin b) E := φ.trans eSL
  have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin b) E) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  have hnotsolv : ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin b) E) := by
    haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin b) E) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hqSL
    haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin b) E) := hqSL.1
    exact Group.IsPerfect.not_isSolvable (Matrix.SpecialLinearGroup (Fin b) E)
  have hb2 : 2 ≤ b := by
    by_contra hlt
    haveI : Subsingleton (Fin b) := Fin.subsingleton_iff_le_one.mpr (by omega)
    haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin b) E) :=
      Matrix.SpecialLinearGroup.subsingleton_of_subsingleton
    exact hnotsolv inferInstance
  have hbad1 : (b, 2 ^ f) ≠ (2, 2) := by
    intro h
    obtain ⟨hb, h2⟩ := Prod.mk.inj h
    rw [hb] at hnotsolv
    have hcard : Nat.card E = 2 ∨ Nat.card E = 3 := by
      left; rw [hE, h2]
    haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) E) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable E hcard
    haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) E) :=
      Group.isSolvable_of_isSolvable_injective
        (f := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective
    exact hnotsolv inferInstance
  have hbad2 : (b, 2 ^ f) ≠ (2, 3) := by
    intro h
    obtain ⟨-, h3⟩ := Prod.mk.inj h
    have hdvd : 2 ∣ 3 := by
      rw [← h3]
      exact dvd_pow_self 2 (by omega)
    norm_num at hdvd
  have hadm : StatedLieAdmissible .PSL b 2 f :=
    ⟨Nat.prime_two, hf, hb2, hbad1, hbad2⟩
  obtain ⟨eZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl b e
  exact Or.inl ⟨by decide, ⟨hadm, E, inferInstance, inferInstance, hE, ⟨eZ⟩⟩⟩

end CFSG.StandardType
