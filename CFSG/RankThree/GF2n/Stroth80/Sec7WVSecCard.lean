module

public import CFSG.RankThree.GF2n.Stroth80.Sec7WVSplit

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix


@[expose] def Sec7WVSecCardStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ P : Subgroup G, Vt M (LB M Q B) B Z t ≤ P →
    P ≤ Wt Q (Vt M (LB M Q B) B Z t) → (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r P = P) →
    ∀ m : ℕ, 2 ≤ m →
    (OmegaMinusNat hc t m →
      ∃ k : ℕ, Nat.card P = Nat.card (Vt M (LB M Q B) B Z t) * Nat.card Z ^ (2 ^ m * k)) ∧
    (OmegaPlusNat hc t m → 3 ≤ m →
      ∃ k : ℕ, Nat.card P = Nat.card (Vt M (LB M Q B) B Z t) * Nat.card Z ^ (2 ^ (m - 1) * k))

theorem sec7WVSecCard_of (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) : Sec7WVSecCardStatement := by
  intro G _ _ M Q Z B hc n t hs P hVP hPW hPR m hm2
  classical
  obtain ⟨r, hr, hd⟩ := sec7WVSplit_of hA hPts h52a h52b G M Q Z B hc n t hs P hVP hPW hPR
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq : 1 < Nat.card Z := by omega
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) :=
    hc.LB_conj (hc.Rt_le_M t hr.mem)
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  have hPn : ∀ x ∈ Rt M (LB M Q B) t, ∀ y ∈ P, x * y * x⁻¹ ∈ P := by
    intro x hx y hy
    have h1 : x * y * x⁻¹ ∈ conjSubgroup x P := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hy
    rwa [hPR x hx] at h1
  have hVn : ∀ x ∈ Rt M (LB M Q B) t, ∀ y ∈ Vt M (LB M Q B) B Z t,
      x * y * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hx) y).mp hy
  obtain ⟨-, hWN⟩ := h52a G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (hc.CN t) (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t))
    rfl rfl rfl rfl
  have hPN : ∀ s ∈ hc.CN t, ∀ y ∈ P, ⁅s, y⁆ ∈ Vt M (LB M Q B) B Z t :=
    fun s hs' y hy => hWN s hs' y (hPW hy)
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
  refine ⟨fun hMinus => ?_, fun hPlus hm3 => ?_⟩
  · have hV := n12N_card_V hc t m hm2 (Or.inr hMinus)
    rcases hcases with
      ⟨m', hm', φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩ |
      ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩
    · exfalso
      have hnat : NaturalRep (ι := Fin m' ⊕ Fin m') K (StatedOmega (StatedQuadPlus m' K))
          (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      have hmm : m' = m := sec7_pin_dim hq (hcard.symm.trans hV)
      have hPlusM : OmegaPlusNat hc t m := by
        rw [← hmm]
        exact ⟨K, hKf, hKfin, hKZ, hnat⟩
      exact omegaSignStatement_holds G M Q Z B hc t m hm2 hPlusM hMinus
    · have hnat : NaturalRep (ι := Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) K
          (StatedOmega (StatedQuadMinus m' K b c)) (Rt M (LB M Q B) t)
          (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      have hmm : m' = m := sec7_pin_dim hq (hcard.symm.trans hV)
      obtain ⟨k, hk⟩ := stroth_2_1_ii_secOmegaMinus (ElemMatrixIso.minus hm' hirr) hm'
        (isMinus_quadMinus (by omega) hirr) φ hrange hker hPn hVn hPN hd hLR hL2R hu hu' huu'
        (by rw [ElemMatrixIso.LomGL_minus hm' hirr]; exact hLu)
        (by rw [hLA, ElemMatrixIso.LomGL_minus hm' hirr]; exact hLu')
      rw [hKZ, hmm] at hk
      exact ⟨k, hk⟩
  · have hV := n12N_card_V hc t m hm2 (Or.inl hPlus)
    rcases hcases with
      ⟨m', hm', φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩ |
      ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩
    · have hnat : NaturalRep (ι := Fin m' ⊕ Fin m') K (StatedOmega (StatedQuadPlus m' K))
          (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      have hmm : m' = m := sec7_pin_dim hq (hcard.symm.trans hV)
      obtain ⟨k, hk⟩ := stroth_2_1_ii_secOmegaPlus (ElemMatrixIso.plus hm') hm'
        (isPlus_quadPlus m') φ hrange hker hPn hVn hPN hd hLR hL2R hu hu' huu'
        (by rw [ElemMatrixIso.LomGL_plus hm']; exact hLu)
        (by rw [hLA, ElemMatrixIso.LomGL_plus hm']; exact hLu')
      rw [hKZ, hmm] at hk
      exact ⟨k, hk⟩
    · exfalso
      have hnat : NaturalRep (ι := Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) K
          (StatedOmega (StatedQuadMinus m' K b c)) (Rt M (LB M Q B) t)
          (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      have hmm : m' = m := sec7_pin_dim hq (hcard.symm.trans hV)
      have hMinusM : OmegaMinusNat hc t m := by
        rw [← hmm]
        exact ⟨K, hKf, hKfin, hKZ, b, c, hirr, hnat⟩
      exact omegaSignStatement_holds G M Q Z B hc t m hm2 hPlus hMinusM

end CFSG.RankThree.GF2n.Stroth80
