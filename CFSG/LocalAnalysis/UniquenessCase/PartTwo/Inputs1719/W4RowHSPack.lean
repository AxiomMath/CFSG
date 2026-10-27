module

public import CFSG.Quasithin.Background.SmithB45ExcHSClass
public import Certificates.Certificate725004
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowConjInvSound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Sporadic.Schreier CFSG.Quasithin.B45Exc.HS CFSG.QuasithinUnique.Bridge.HSExcl
  CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.RuSchreier

private theorem e9_products_of_check {n : ℕ} {x y m1 m2 m3 k : PArr}
    {gx gy gm1 gm2 gm3 gk : Equiv.Perm (Fin n)}
    (hx : PRep n x gx) (hy : PRep n y gy) (hm1 : PRep n m1 gm1) (hm2 : PRep n m2 gm2)
    (hm3 : PRep n m3 gm3) (hk : PRep n k gk)
    (hc : e9PackCheck n x y m1 m2 m3 k = true) :
    gx ^ 3 = 1 ∧ gy ^ 3 = 1 ∧ gx ≠ 1 ∧ gx * gy = gy * gx ∧ (∀ j < 3, gy ≠ gx ^ j) ∧
      gm1 * gx * gm1⁻¹ = gy ∧ gm2 * gx * gm2⁻¹ = gx * gy ∧
      gm3 * gx * gm3⁻¹ = gx * gy ^ 2 ∧
      (gx * (gk * gx * gk⁻¹)) ^ 5 = 1 ∧ gx * (gk * gx * gk⁻¹) ≠ 1 := by
  simp only [e9PackCheck, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hx3, hy3⟩, hxne⟩, hcomm⟩, hnotmem⟩, hm1e⟩, hm2e⟩, hm3e⟩, hb5⟩, hbne⟩ := hc
  have hb : Rep n (compA n x.1 (compA n (compA n k.1 x.1) k.2))
      (gx * (gk * gx * gk⁻¹)) :=
    rep_compA hx.1 (rep_compA (rep_compA hk.1 hx.1) hk.2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (eqA_iff (rep_powA hx.1 3) (rep_idA (n := n))).1 hx3
  · exact (eqA_iff (rep_powA hy.1 3) (rep_idA (n := n))).1 hy3
  · exact ne_of_eqA_eq_false hx.1 (rep_idA (n := n)) hxne
  · exact (eqA_iff (rep_compA hx.1 hy.1) (rep_compA hy.1 hx.1)).1 hcomm
  · intro j hj
    exact ne_of_eqA_eq_false hy.1 (rep_powA hx.1 j)
      (by simpa only [Bool.not_eq_true'] using allLt_iff.1 hnotmem j hj)
  · exact (eqA_iff (rep_compA (rep_compA hm1.1 hx.1) hm1.2) hy.1).1 hm1e
  · exact (eqA_iff (rep_compA (rep_compA hm2.1 hx.1) hm2.2)
      (rep_compA hx.1 hy.1)).1 hm2e
  · exact (eqA_iff (rep_compA (rep_compA hm3.1 hx.1) hm3.2)
      (rep_compA hx.1 (rep_powA hy.1 2))).1 hm3e
  · exact (eqA_iff (rep_powA hb 5) (rep_idA (n := n))).1 hb5
  · exact ne_of_eqA_eq_false hb (rep_idA (n := n)) hbne

theorem hs_e9_package :
    ∃ x₁ ∈ hsP, ∃ x₂ ∈ hsP, x₁ ^ 3 = 1 ∧ x₂ ^ 3 = 1 ∧ x₁ ≠ 1 ∧ x₁ * x₂ = x₂ * x₁ ∧
      (∀ j < 3, x₂ ≠ x₁ ^ j) ∧
      (∃ m ∈ hsP, m * x₁ * m⁻¹ = x₂) ∧ (∃ m ∈ hsP, m * x₁ * m⁻¹ = x₁ * x₂) ∧
      (∃ m ∈ hsP, m * x₁ * m⁻¹ = x₁ * x₂ ^ 2) ∧
      (∃ k ∈ hsP, (x₁ * (k * x₁ * k⁻¹)) ^ 5 = 1 ∧ x₁ * (k * x₁ * k⁻¹) ≠ 1) ∧
      ∀ i ∈ [5, 12, 21, 34], ∃ h ∈ hsP,
        hsT i * (h * x₁ * h⁻¹) * (hsT i)⁻¹ = (h * x₁ * h⁻¹)⁻¹ := by
  obtain ⟨x, hxP, hx⟩ := regIn_hsP.word hsE9WX
  obtain ⟨y, hyP, hy⟩ := regIn_hsP.word hsE9WY
  obtain ⟨m1, hm1P, hm1⟩ := regIn_hsP.word hsE9WM1
  obtain ⟨m2, hm2P, hm2⟩ := regIn_hsP.word hsE9WM2
  obtain ⟨m3, hm3P, hm3⟩ := regIn_hsP.word hsE9WM3
  obtain ⟨k, hkP, hk⟩ := regIn_hsP.word hsE9WK
  obtain ⟨h5, h5P, h5r⟩ := regIn_hsP.word hsE9WH5
  obtain ⟨h12, h12P, h12r⟩ := regIn_hsP.word hsE9WH12
  obtain ⟨h21, h21P, h21r⟩ := regIn_hsP.word hsE9WH21
  obtain ⟨h34, h34P, h34r⟩ := regIn_hsP.word hsE9WH34
  have hc := Certificates.certificate725004
  simp only [hsE9Check, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨he9, hc5⟩, hc12⟩, hc21⟩, hc34⟩ := hc
  obtain ⟨hx3, hy3, hxne, hcomm, hnotmem, hm1e, hm2e, hm3e, hb5, hbne⟩ :=
    e9_products_of_check hx hy hm1 hm2 hm3 hk he9
  refine ⟨x, hxP, y, hyP, hx3, hy3, hxne, hcomm, hnotmem, ⟨m1, hm1P, hm1e⟩,
    ⟨m2, hm2P, hm2e⟩, ⟨m3, hm3P, hm3e⟩, ⟨k, hkP, hb5, hbne⟩, ?_⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact ⟨h5, h5P, inv_of_conjInvCheck (pRep_hsT (k := 5) (by simp)) h5r hx hc5⟩
  · exact ⟨h12, h12P, inv_of_conjInvCheck (pRep_hsT (k := 12) (by simp)) h12r hx hc12⟩
  · exact ⟨h21, h21P, inv_of_conjInvCheck (pRep_hsT (k := 21) (by simp)) h21r hx hc21⟩
  · exact ⟨h34, h34P, inv_of_conjInvCheck (pRep_hsT (k := 34) (by simp)) h34r hx hc34⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
