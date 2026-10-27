module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUHyp
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUBridge
import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactURootEq
import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ClassicalGroups.Unitary
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.BorelTits CFSG.LinearGroups

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem uCited_exists_rootParabolic_statedProjSU (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    (hm : 4 ≤ m) (R : Subgroup (StatedProj (StatedSU m (2 ^ n) F))) (hR : Nat.card R = 2 ^ n)
    (hRt : ∀ x ∈ R, x ≠ 1 → IsUnitaryTransvectionIn m n x)
    {Sy : Subgroup (StatedProj (StatedSU m (2 ^ n) F))}
    (hSy : ∃ P : Sylow 2 (StatedProj (StatedSU m (2 ^ n) F)),
      (P : Subgroup (StatedProj (StatedSU m (2 ^ n) F))) = Sy) (hRSy : R ≤ Sy)
    (hSyR : Sy ≤ Subgroup.normalizer (R : Set (StatedProj (StatedSU m (2 ^ n) F)))) :
    ∃ X₂ Pα : Subgroup (StatedProj (StatedSU m (2 ^ n) F)), RootParabolic R Sy X₂ Pα 2 := by
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ m = 2 * r + ε :=
    ⟨m / 2, m % 2, by omega, by omega⟩
  have hr : 2 ≤ r := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 :=
    CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hF
  have h : UnitaryFieldData 2 n F := unitaryFieldDataOfCard hF
  have hbar : ∀ c : F, h.bar c = unitaryInvolution F 2 n c := by
    intro c
    rw [UnitaryFieldData.bar_apply]
    exact (unitaryInvolution_apply F 2 n c).symm
  obtain ⟨e, he0, he, rfl⟩ := exists_eq_spUFixRootU hF hm R hR hRt
  obtain ⟨Rm, hR'⟩ := exists_isHypTransport (r := r) (ε := ε) h
  have hn : 1 ≤ 2 * r + ε := by omega
  let τ := hypPSUEquivStatedProj h hR' hn
  let x := transportInv h Rm *ᵥ e
  have hx_def : x = transportInv h Rm *ᵥ e := rfl
  have hRm_x : Rm *ᵥ x = e := by
    rw [hx_def, mulVec_mulVec, mul_transportInv hR', one_mulVec]
  have hx0 : x ≠ 0 := by
    intro hx
    apply he0
    rw [← hRm_x, hx, Matrix.mulVec_zero]
  have hstd : stdHermForm h (2 * r + ε) e e = herm (unitaryInvolution F 2 n) e e := by
    rw [stdHermForm_apply, herm]
    exact Finset.sum_congr rfl fun i _ => by rw [hbar]
  have hx : hypForm h r ε x x = 0 := by
    rw [hx_def, hypForm_transportInv hR' e e, hstd, he]
  have hmap := uCited_map_root_transport h hR' hn hF hx
  rw [hRm_x] at hmap
  have hRmap : (spUFixRootU hF (2 * r + ε) e).map τ.symm.toMonoidHom
      = (uCitedRoot h r ε x).map (hypProj h r ε) := by
    rw [← hmap, Subgroup.map_map]
    have h1 : τ.symm.toMonoidHom.comp τ.toMonoidHom = MonoidHom.id (hypPSU h r ε) := by
      ext y
      simp
    rw [h1, Subgroup.map_id]
  obtain ⟨P, hPsy⟩ := hSy
  have hsurj : Function.Surjective τ.symm.toMonoidHom := fun y => ⟨τ y, by simp⟩
  let P' := Sylow.mapSurjective (f := τ.symm.toMonoidHom) hsurj P
  have hP' : (P' : Subgroup (hypPSU h r ε)) = Sy.map τ.symm.toMonoidHom := by
    dsimp only [P']
    rw [Sylow.coe_mapSurjective (f := τ.symm.toMonoidHom), hPsy]
  have hRSy' : (uCitedRoot h r ε x).map (hypProj h r ε) ≤ Sy.map τ.symm.toMonoidHom := by
    rw [← hRmap]
    exact Subgroup.map_mono hRSy
  have hSyR' : Sy.map τ.symm.toMonoidHom ≤
      Subgroup.normalizer ((uCitedRoot h r ε x).map (hypProj h r ε) :
        Set (hypPSU h r ε)) := by
    rw [← hRmap]
    exact (Subgroup.map_mono hSyR).trans (Subgroup.le_normalizer_map τ.symm.toMonoidHom)
  obtain ⟨X₂', Pα', hP⟩ :=
    uCited_exists_rootParabolic_hypPSU h hr hε hx0 hx ⟨P', hP'⟩ hRSy' hSyR'
  exact rootParabolic_exists_of_mulEquiv τ.symm ⟨X₂', Pα', by rwa [hRmap]⟩

end CFSG.LocalAnalysis.WeakClosure81

end
