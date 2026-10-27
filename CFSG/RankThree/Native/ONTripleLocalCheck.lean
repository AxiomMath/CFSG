module

public import Certificates.Certificate8142

public section

namespace CFSG.RankThree.Native.ONTriple


theorem p0_facts : (∀ r ∈ rX, eM r ^ 3 = 1) ∧ ∀ i < 4, ∀ j < 4, i ≠ j →
    eM (rX.getD i 0) * (eM (rX.getD j 0) * ((eM (rX.getD i 0))⁻¹ * (eM (rX.getD j 0))⁻¹)) =
      eM 7 ^ omegaN i j :=
  Certificates.certificate8142.1

theorem conj_facts : ∀ d ∈ conjData, (eM d.1)⁻¹ * (eM (rX.getD d.2.1 0) * eM d.1) =
    eM (rX.getD 3 0) ^ d.2.2.2.getD 3 0 * (eM (rX.getD 2 0) ^ d.2.2.2.getD 2 0 *
      (eM (rX.getD 1 0) ^ d.2.2.2.getD 1 0 * (eM (rX.getD 0 0) ^ d.2.2.2.getD 0 0 *
        eM 7 ^ d.2.2.1))) :=
  Certificates.certificate8142.2.1

theorem k0_facts : (eM rK1 * eM (rX.getD 0 0) = eM (rX.getD 0 0) * eM rK1 ∧
    eM rK2 * eM (rX.getD 0 0) = eM (rX.getD 0 0) * eM rK2) ∧
    eM rY1 = eM (rX.getD 1 0) ∧ eM rY3 = eM rX12 :=
  Certificates.certificate8142.2.2.1

theorem blocks_facts :
    (MapsB (eM rK1) sigK1 ∧ MapsB (eM rK2) sigK2 ∧ MapsB (eM 7) [0, 1, 2, 3, 4, 5]) ∧
      ∀ t < 60, ptAct (eM (rX.getD 0 0)) (pt 0) ≠ pt t :=
  Certificates.certificate8142.2.2.2.1

theorem v_facts {j m : ℕ} (hj : j < 2) (hm : m < 3) :
    let v := fun i => eM (vRegI j m i)
    let y := eM (if j = 0 then rX.getD 1 0 else rX12)
    v 0 * v 1 = v 2 ∧ v 1 * v 0 = v 2 ∧ (∀ i < 3, v i * v i = 1 ∧ v i ≠ 1) ∧
      (∀ i < 3, ∃ i' < 3, y⁻¹ * (v i * y) = v i') ∧
      ∀ i < 3, MapsB (v i) (((sigV.getD j []).getD m []).getD i []) :=
  Certificates.certificate8142.2.2.2.2.1 j hj m hm

theorem wit_facts : ∀ d ∈ witData,
    let n₁ := eM ((rL.getD d.1 []).getD d.2.1 0)
    let n₂ := eM ((rL.getD d.1 []).getD d.2.2.1 0)
    let t₀ := n₁⁻¹ * (eM (vRegI d.1 d.2.2.2.1 0) * n₁)
    let s₀ := n₂⁻¹ * (eM (vRegI d.1 d.2.2.2.2 0) * n₂)
    let s₁ := n₂⁻¹ * (eM (vRegI d.1 d.2.2.2.2 1) * n₂)
    (s₁ * (t₀ * (s₀ * t₀))) ^ 3 = 1 ∧ s₁ * (t₀ * (s₀ * t₀)) ≠ 1 :=
  Certificates.certificate8142.2.2.2.2.2.1

theorem pts_ne : ∀ s < 60, ∀ t < 60, s ≠ t → pt s ≠ pt t :=
  Certificates.certificate8142.2.2.2.2.2.2

end CFSG.RankThree.Native.ONTriple
