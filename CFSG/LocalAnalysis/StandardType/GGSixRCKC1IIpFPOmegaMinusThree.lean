module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAt
import CFSG.RankThree.PartOne.CTP.SU4EvenBridge

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.RCKRP

theorem rckClassicalModelIDAt_PSU_of_POmegaMinus_three
    {X : Type} [Group X] {g : ℕ} (hg : 1 ≤ g) {K B : Subgroup X}
    (φ : (ggU .POmegaMinus 3 g).K →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaMinus 3 g).K)
    (hlift : ∀ b ∈ B, ∃ x ∈ φ.range, b * x ∈ Subgroup.centralizer (φ.range : Set X)) :
    RCKClassicalModelIDAt .PSU K B := by
  classical
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  let F := GaloisField 2 (g + 1)
  let L := GaloisField 2 (2 * (g + 1))
  have hcardF : Nat.card F = 2 ^ (g + 1) :=
    GaloisField.card (p := 2) (n := g + 1) (by omega)
  have hcardL : Nat.card L = (2 ^ (g + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (g + 1) (by omega)
  obtain ⟨_, e, -⟩ :=
    CFSG.RankThree.PartOne.CTP.SU4Even.exists_equiv_su_four_even
      (F := F) (K := L) (f := g + 1)
      (b := (minusCoeffs 2 (g + 1)).1) (c := (minusCoeffs 2 (g + 1)).2)
      hcardF hcardL (minusCoeffs_irr 2 (g + 1))
  let e' : (ggU .POmegaMinus 3 (g + 1)).K ≃* (ggU .PSU 4 (g + 1)).K := e
  let φ' : (ggU .PSU 4 (g + 1)).K →* X := φ.comp e'.symm.toMonoidHom
  have hrange : φ'.range = φ.range := by
    change (φ.comp e'.symm.toMonoidHom).range = φ.range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e'.symm.surjective, Subgroup.map_top]
  have hker : φ'.ker ≤ Subgroup.center (ggU .PSU 4 (g + 1)).K := by
    have h1 : φ'.ker = φ.ker.map e'.toMonoidHom :=
      MonoidHom.ker_comp_mulEquiv φ e'.symm
    rw [h1]
    exact (Subgroup.map_mono hφk).trans (le_of_eq (Subgroup.map_center_eq e'))
  refine ⟨4, g + 1, φ', hg, hrange.trans hφr, hker, fun b hb => ?_⟩
  obtain ⟨x, hx, hbx⟩ := hlift b hb
  refine ⟨x, hrange ▸ hx, fun γ _ => ⟨1, Subgroup.one_mem _, fun z _ => ?_⟩⟩
  have hz : φ' z ∈ φ.range := hrange ▸ MonoidHom.mem_range.mpr ⟨z, rfl⟩
  have hcomm : φ' z * (b * x) = (b * x) * φ' z :=
    Subgroup.mem_centralizer_iff.mp hbx (φ' z) hz
  rw [one_mul, inv_one, mul_one, mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]

end CFSG.StandardType.RCKC1
