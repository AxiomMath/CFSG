module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatBridge
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec83Card
public import CFSG.RankThree.GF2n.Stroth80.Sec7Transport
public import CFSG.RankThree.GF2n.Stroth80.Sec7OmegaSign

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix

theorem sec7_secOrder_ge {G : Type} [Group G] [Finite G] {V P : Subgroup G} (hVP : V < P)
    {q e k : ℕ} (hq : 1 < q) (he : 1 ≤ e) (h : Nat.card P = Nat.card V * q ^ (e * k)) :
    Nat.card V * q ^ e ≤ Nat.card P := by
  have hk : 1 ≤ k := by
    by_contra h0
    have h0' : k = 0 := by omega
    subst h0'
    have hle : Nat.card P ≤ Nat.card V := by
      rw [h]
      simp
    exact absurd (Subgroup.eq_of_le_of_card_ge hVP.le hle) (ne_of_lt hVP)
  rw [h]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right e hk))

theorem sec7_pin_dim {q a b : ℕ} (hq : 1 < q) (h : q * q ^ (2 * a) = q * q ^ (2 * b)) : a = b := by
  have h1 : q ^ (2 * a) = q ^ (2 * b) := Nat.eq_of_mul_eq_mul_left (by omega) h
  have h2 := Nat.pow_right_injective hq h1
  omega


theorem sec7WVSecOrder_of_points (hPts : Sec5NatPointsOmegaStatement) :
    Sec7WVSecOrderStatement := by
  intro G _ _ M Q Z B hc n t hs P hVP hPW hPR hPN ⟨r, hr, A₁, A₂, hd⟩ m hm2
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hq : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
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
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
  refine ⟨fun hMinus => ?_, fun hPlus hm3 => ?_⟩
  · have hMinus' := hMinus
    obtain ⟨K₀, _, _, hK₀, b₀, c₀, hirr₀, hrep₀⟩ := hMinus
    have hcard₀ := card_of_naturalRep hrep₀ sec39_Z_le_Vt hK₀
    have hι₀ : Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) = 2 * m := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι₀] at hcard₀
    rcases hcases with
      ⟨m', hm', φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩ |
      ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩
    · exfalso
      have hnat : NaturalRep (ι := Fin m' ⊕ Fin m') K (StatedOmega (StatedQuadPlus m' K))
          (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      obtain rfl : m' = m := sec7_pin_dim hq (by rw [← hcard, ← hcard₀])
      exact omegaSignStatement_holds G M Q Z B hc t m' hm2 ⟨K, hKf, hKfin, hKZ, hnat⟩ hMinus'
    · have hnat : NaturalRep (ι := Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) K
          (StatedOmega (StatedQuadMinus m' K b c)) (Rt M (LB M Q B) t)
          (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      obtain rfl : m' = m := sec7_pin_dim hq (by rw [← hcard, ← hcard₀])
      obtain ⟨k, hk⟩ := stroth_2_1_ii_secOmegaMinus (ElemMatrixIso.minus hm' hirr) hm'
        (isMinus_quadMinus (by omega) hirr) φ hrange hker hPn hVn hPN hd hLR hL2R hu hu' huu'
        (by rw [ElemMatrixIso.LomGL_minus hm' hirr]; exact hLu)
        (by rw [hLA, ElemMatrixIso.LomGL_minus hm' hirr]; exact hLu')
      rw [hKZ] at hk
      exact sec7_secOrder_ge hVP hq (Nat.one_le_two_pow) hk
  · have hPlus' := hPlus
    obtain ⟨K₀, _, _, hK₀, hrep₀⟩ := hPlus
    have hcard₀ := card_of_naturalRep hrep₀ sec39_Z_le_Vt hK₀
    have hι₀ : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι₀] at hcard₀
    rcases hcases with
      ⟨m', hm', φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩ |
      ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩
    · have hnat : NaturalRep (ι := Fin m' ⊕ Fin m') K (StatedOmega (StatedQuadPlus m' K))
          (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      obtain rfl : m' = m := sec7_pin_dim hq (by rw [← hcard, ← hcard₀])
      obtain ⟨k, hk⟩ := stroth_2_1_ii_secOmegaPlus (ElemMatrixIso.plus hm') hm'
        (isPlus_quadPlus m') φ hrange hker hPn hVn hPN hd hLR hL2R hu hu' huu'
        (by rw [ElemMatrixIso.LomGL_plus hm']; exact hLu)
        (by rw [hLA, ElemMatrixIso.LomGL_plus hm']; exact hLu')
      rw [hKZ] at hk
      exact sec7_secOrder_ge hVP hq (Nat.one_le_two_pow) hk
    · exfalso
      have hnat : NaturalRep (ι := Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) K
          (StatedOmega (StatedQuadMinus m' K b c)) (Rt M (LB M Q B) t)
          (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      obtain rfl : m' = m := sec7_pin_dim hq (by rw [← hcard, ← hcard₀])
      exact omegaSignStatement_holds G M Q Z B hc t m' hm2 hPlus'
        ⟨K, hKf, hKfin, hKZ, b, c, hirr, hnat⟩

end CFSG.RankThree.GF2n.Stroth80
