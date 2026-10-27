module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeAut
public import Certificates.Certificate725005
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowConjInvSound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Sporadic.HeldB CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.RuSchreier

private theorem e25_products_of_check {n : ℕ} {x y m1 m2 m3 m4 m5 : PArr}
    {gx gy gm1 gm2 gm3 gm4 gm5 : Equiv.Perm (Fin n)}
    (hx : PRep n x gx) (hy : PRep n y gy) (hm1 : PRep n m1 gm1) (hm2 : PRep n m2 gm2)
    (hm3 : PRep n m3 gm3) (hm4 : PRep n m4 gm4) (hm5 : PRep n m5 gm5)
    (hc : e25PackCheck n x y m1 m2 m3 m4 m5 = true) :
    gx ^ 5 = 1 ∧ gy ^ 5 = 1 ∧ gx ≠ 1 ∧ gx * gy = gy * gx ∧ (∀ j < 5, gy ≠ gx ^ j) ∧
      gm1 * gx * gm1⁻¹ = gy ∧ gm2 * gx * gm2⁻¹ = gx * gy ∧
      gm3 * gx * gm3⁻¹ = gx * gy ^ 2 ∧ gm4 * gx * gm4⁻¹ = gx * gy ^ 3 ∧
      gm5 * gx * gm5⁻¹ = gx * gy ^ 4 := by
  simp only [e25PackCheck, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hx5, hy5⟩, hxne⟩, hcomm⟩, hnotmem⟩, hm1e⟩, hm2e⟩, hm3e⟩, hm4e⟩, hm5e⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (eqA_iff (rep_powA hx.1 5) (rep_idA (n := n))).1 hx5
  · exact (eqA_iff (rep_powA hy.1 5) (rep_idA (n := n))).1 hy5
  · exact ne_of_eqA_eq_false hx.1 (rep_idA (n := n)) hxne
  · exact (eqA_iff (rep_compA hx.1 hy.1) (rep_compA hy.1 hx.1)).1 hcomm
  · intro j hj
    exact ne_of_eqA_eq_false hy.1 (rep_powA hx.1 j)
      (by simpa only [Bool.not_eq_true'] using allLt_iff.1 hnotmem j hj)
  · exact (eqA_iff (rep_compA (rep_compA hm1.1 hx.1) hm1.2) hy.1).1 hm1e
  · exact (eqA_iff (rep_compA (rep_compA hm2.1 hx.1) hm2.2) (rep_compA hx.1 hy.1)).1 hm2e
  · exact (eqA_iff (rep_compA (rep_compA hm3.1 hx.1) hm3.2)
      (rep_compA hx.1 (rep_powA hy.1 2))).1 hm3e
  · exact (eqA_iff (rep_compA (rep_compA hm4.1 hx.1) hm4.2)
      (rep_compA hx.1 (rep_powA hy.1 3))).1 hm4e
  · exact (eqA_iff (rep_compA (rep_compA hm5.1 hx.1) hm5.2)
      (rep_compA hx.1 (rep_powA hy.1 4))).1 hm5e

private theorem pRep_he_involutions :
    PRep 8330 heT0P (heGenPerm 0) ∧ PRep 8330 heT1ArrP heT1P ∧ PRep 8330 heUP heAutU := by
  refine ⟨PRep.of_sq (rep_heGen (k := 0) (by norm_num)) (by rw [← sq]; exact heGen0_sq),
    PRep.of_sq rep_heT1 ?_, PRep.of_sq rep_heU (by rw [← sq]; exact heAutU_sq)⟩
  rw [← sq]
  have := pow_orderOf_eq_one heT1P
  rwa [orderOf_heT1P] at this

theorem he_e25_package :
    ∃ x₁ ∈ heP, ∃ x₂ ∈ heP, x₁ ^ 5 = 1 ∧ x₂ ^ 5 = 1 ∧ x₁ ≠ 1 ∧ x₁ * x₂ = x₂ * x₁ ∧
      (∀ j < 5, x₂ ≠ x₁ ^ j) ∧ (∃ m ∈ heP, m * x₁ * m⁻¹ = x₂) ∧
      (∀ i, 0 < i → i < 5 → ∃ m ∈ heP, m * x₁ * m⁻¹ = x₁ * x₂ ^ i) ∧
      ∀ t ∈ [heGenPerm 0, heT1P, heAutU], ∃ h ∈ heP,
        t * (h * x₁ * h⁻¹) * t⁻¹ = (h * x₁ * h⁻¹)⁻¹ := by
  obtain ⟨x, hxP, hx⟩ := regIn_heP.word heE25WX
  obtain ⟨y, hyP, hy⟩ := regIn_heP.word heE25WY
  obtain ⟨m1, hm1P, hm1⟩ := regIn_heP.word heE25WM1
  obtain ⟨m2, hm2P, hm2⟩ := regIn_heP.word heE25WM2
  obtain ⟨m3, hm3P, hm3⟩ := regIn_heP.word heE25WM3
  obtain ⟨m4, hm4P, hm4⟩ := regIn_heP.word heE25WM4
  obtain ⟨m5, hm5P, hm5⟩ := regIn_heP.word heE25WM5
  obtain ⟨h0, h0P, h0r⟩ := regIn_heP.word heE25WH0
  obtain ⟨h1, h1P, h1r⟩ := regIn_heP.word heE25WH1
  obtain ⟨hu, huP, hur⟩ := regIn_heP.word heE25WHU
  have hc := Certificates.certificate725005
  simp only [heE25Check, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨he25, hc0⟩, hc1⟩, hcu⟩ := hc
  obtain ⟨hx5, hy5, hxne, hcomm, hnotmem, hm1e, hm2e, hm3e, hm4e, hm5e⟩ :=
    e25_products_of_check hx hy hm1 hm2 hm3 hm4 hm5 he25
  obtain ⟨hT0, hT1, hTU⟩ := pRep_he_involutions
  refine ⟨x, hxP, y, hyP, hx5, hy5, hxne, hcomm, hnotmem, ⟨m1, hm1P, hm1e⟩, ?_, ?_⟩
  · intro i hi0 hi5
    interval_cases i
    · exact ⟨m2, hm2P, by rw [pow_one]; exact hm2e⟩
    · exact ⟨m3, hm3P, hm3e⟩
    · exact ⟨m4, hm4P, hm4e⟩
    · exact ⟨m5, hm5P, hm5e⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨h0, h0P, inv_of_conjInvCheck hT0 h0r hx hc0⟩
    · exact ⟨h1, h1P, inv_of_conjInvCheck hT1 h1r hx hc1⟩
    · exact ⟨hu, huP, inv_of_conjInvCheck hTU hur hx hcu⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
