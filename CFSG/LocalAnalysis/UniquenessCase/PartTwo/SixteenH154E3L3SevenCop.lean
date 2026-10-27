module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_seven_inf_le (hW : ∀ w : W, w ^ 2 = 1) {g : MulAut W} (hg7 : g ^ 7 = 1)
    {Z : Subgroup W} (hgZ : ∀ z ∈ Z, g z = z) {u : W}
    (hu : u ∈ commSub ⊤ (Subgroup.zpowers g) ⊔ Z) (hgu : g u * u⁻¹ ∈ Z) : u ∈ Z := by
  have hdiv : Nat.card (Subgroup.zpowers g) ∣ 7 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hg7
  have hPodd : Odd (Nat.card (Subgroup.zpowers g)) :=
    Odd.of_dvd_nat (by decide) hdiv
  have hZfix : Z ≤ fixV (Subgroup.zpowers g) := by
    intro z hz
    rw [mem_fixV_zpowers_iff]
    exact hgZ z hz
  have hdec := coprime_decomp (P := Subgroup.zpowers g) hPodd hW (W := ⊤)
    (fun _ _ _ _ => Subgroup.mem_top _)
  rw [top_inf_eq] at hdec
  obtain ⟨w, hwC, z, hzZ, hwz⟩ := Subgroup.mem_sup.mp hu
  have hcZ : g w * w⁻¹ ∈ Z := by
    have h1 : g w * w⁻¹ = g u * u⁻¹ := by
      rw [← hwz, map_mul, hgZ z hzZ, mul_inv_rev]
      group
    rw [h1]
    exact hgu
  have hcC : g w * w⁻¹ ∈ commSub ⊤ (Subgroup.zpowers g) :=
    Subgroup.subset_closure ⟨g, Subgroup.mem_zpowers g, w, Subgroup.mem_top w, rfl⟩
  have hcFix : g w * w⁻¹ ∈ fixV (Subgroup.zpowers g) := hZfix hcZ
  have hc1 : g w * w⁻¹ = 1 := by
    have hmem : g w * w⁻¹ ∈ (⊥ : Subgroup W) := by
      rw [← hdec.2]
      exact ⟨hcC, hcFix⟩
    exact Subgroup.mem_bot.mp hmem
  have hgw : g w = w := mul_inv_eq_one.mp hc1
  have hwFix : w ∈ fixV (Subgroup.zpowers g) := mem_fixV_zpowers_iff.mpr hgw
  have hw1 : w = 1 := by
    have hmem : w ∈ (⊥ : Subgroup W) := by
      rw [← hdec.2]
      exact ⟨hwC, hwFix⟩
    exact Subgroup.mem_bot.mp hmem
  rw [← hwz, hw1, one_mul]
  exact hzZ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
