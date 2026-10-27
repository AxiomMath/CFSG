module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenDegen
public import CFSG.RankThree.PartTwo.Sec16.KL3SubProofEnd
import CFSG.RankThree.PartTwo.Sec16.KL3SubProofMain
import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YD8
import CFSG.LocalAnalysis.OddStandard.ONanB2D8
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Small
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutOmega

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree Matrix Module
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj)
open CFSG.RankThree.PartTwo.Sec16.KL3SubProof (IsElat exists_isElat_of_mul_self
  exists_eq_smul_of_vecMulVec_eq exists_eq_smul_of_vecMulVec_eq' exists_eq_smul_of_dotProduct_eq_zero
  sq_mul_of_dotProduct_eq_zero IsUT IsZUT utm utm_mul utm_inj utm_eq_one_iff utm_zero utm_mul_self
  isUT_utm isZUT_utm utm_comm utm_apply_zero_one utm_apply_one_two)
open scoped MatrixGroups

section Elations

variable {F : Type} [Field F]

theorem special_of_even [Finite F] [CharP F 2] {s t : GL (Fin 3) F} {a φ b ψ : Fin 3 → F}
    (hs : IsElat s a φ) (ht : IsElat t b ψ) (hst : s * t ≠ t * s)
    (hev : Even (orderOf (s * t))) : φ ⬝ᵥ b = 0 ∨ ψ ⬝ᵥ a = 0 := by
  have hss : s * s = 1 := hs.mul_self
  have htt : t * t = 1 := ht.mul_self
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hm0 : 0 < orderOf (s * t) := orderOf_pos (s * t)
  obtain ⟨k, hk⟩ := hev
  set w := (s * t) ^ k with hw
  have hww : w * w = 1 := by
    rw [hw, ← pow_add, ← hk, pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hstinv : (s * t)⁻¹ = t * s := by rw [_root_.mul_inv_rev, hsi, hti]
  have hsw : s * w = w * s := by
    have h1 : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
      rw [hstinv, hsi, ← mul_assoc, hss, one_mul]
    have h2 : s * w * s⁻¹ = w⁻¹ := by
      rw [hw, ← conj_pow, h1, inv_pow]
    rw [hwi] at h2
    calc s * w = s * w * s⁻¹ * s := by group
      _ = w * s := by rw [h2]
  have htw : t * w = w * t := by
    have h1 : t * (s * t) * t⁻¹ = (s * t)⁻¹ := by
      rw [hstinv, hti, mul_assoc, mul_assoc, htt, mul_one]
    have h2 : t * w * t⁻¹ = w⁻¹ := by
      rw [hw, ← conj_pow, h1, inv_pow]
    rw [hwi] at h2
    calc t * w = t * w * t⁻¹ * t := by group
      _ = w * t := by rw [h2]
  obtain ⟨c, δ, hwE⟩ := exists_isElat_of_mul_self hww hw1
  obtain ⟨hc0, hδ0, hδc, -⟩ := id hwE
  have hsφa := hs.2.2.1
  have htψb := ht.2.2.1
  rcases hs.center_or_axis_of_commute hwE hsw with ⟨k₁, hk₁⟩ | ⟨k₁, hk₁⟩ <;>
    rcases ht.center_or_axis_of_commute hwE htw with ⟨k₂, hk₂⟩ | ⟨k₂, hk₂⟩
  ·
    left
    have hk₂0 : k₂ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hk₂
      exact hc0 hk₂
    have e : k₂ • b = k₁ • a := hk₂.symm.trans hk₁
    have hb : b = (k₁ / k₂) • a := by
      calc b = k₂⁻¹ • (k₂ • b) := by rw [smul_smul, inv_mul_cancel₀ hk₂0, one_smul]
        _ = (k₁ / k₂) • a := by rw [e, smul_smul, div_eq_inv_mul]
    rw [hb, dotProduct_smul, hsφa, smul_zero]
  ·
    right
    have hk₁0 : k₁ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hk₁
      exact hc0 hk₁
    have hk₂0 : k₂ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hk₂
      exact hδ0 hk₂
    rw [hk₁, hk₂, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hδc
    rcases mul_eq_zero.mp hδc with h | h
    · exact absurd h hk₂0
    · exact (mul_eq_zero.mp h).resolve_left hk₁0
  ·
    left
    have hk₁0 : k₁ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hk₁
      exact hδ0 hk₁
    have hk₂0 : k₂ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hk₂
      exact hc0 hk₂
    rw [hk₁, hk₂, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hδc
    rcases mul_eq_zero.mp hδc with h | h
    · exact absurd h hk₁0
    · exact (mul_eq_zero.mp h).resolve_left hk₂0
  ·
    right
    have hk₂0 : k₂ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hk₂
      exact hδ0 hk₂
    have e : k₂ • ψ = k₁ • φ := hk₂.symm.trans hk₁
    have hψ : ψ = (k₁ / k₂) • φ := by
      calc ψ = k₂⁻¹ • (k₂ • ψ) := by rw [smul_smul, inv_mul_cancel₀ hk₂0, one_smul]
        _ = (k₁ / k₂) • φ := by rw [e, smul_smul, div_eq_inv_mul]
    rw [hψ, smul_dotProduct, hsφa, smul_zero]

theorem eigen_of_commute {x y : GL (Fin 3) F} {a φ : Fin 3 → F} (hx : IsElat x a φ)
    (hxy : y * x = x * y) :
    ∃ κ : F, (y : Matrix (Fin 3) (Fin 3) F) *ᵥ a = κ • a ∧
      φ ᵥ* (y : Matrix (Fin 3) (Fin 3) F) = κ • φ := by
  obtain ⟨ha, hφ, -, hxm⟩ := hx
  set Y := (y : Matrix (Fin 3) (Fin 3) F) with hY
  have hYi : ((y⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Y = 1 := by
    rw [hY, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hm : vecMulVec (Y *ᵥ a) φ = vecMulVec a (φ ᵥ* Y) := by
    have h1 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hxy
    simp only [Units.val_mul, hxm] at h1
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h1
    rw [← mul_vecMulVec, ← vecMulVec_mul]
    exact add_left_cancel h1
  have hφY : φ ᵥ* Y ≠ 0 := by
    intro h0
    apply hφ
    have := congrArg (fun v => v ᵥ* ((y⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h0
    simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at this
    rwa [show Y * ((y⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 by
      rw [hY, ← Units.val_mul, mul_inv_cancel, Units.val_one], Matrix.vecMul_one] at this
  obtain ⟨κ, hκ⟩ := exists_eq_smul_of_vecMulVec_eq ha hφY hm.symm
  refine ⟨κ, hκ, ?_⟩
  rw [hκ, smul_vecMulVec, ← vecMulVec_smul] at hm
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  funext j
  have := congrFun (congrFun hm i) j
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this hi ⊢
  exact (mul_left_cancel₀ hi this).symm

theorem eq_scalar_of_commute_special [CharP F 2] {s t y : GL (Fin 3) F} {a φ b ψ : Fin 3 → F}
    (hs : IsElat s a φ) (ht : IsElat t b ψ) (hφb : φ ⬝ᵥ b = 0) (hψa : ψ ⬝ᵥ a ≠ 0)
    (hys : y * s = s * y) (hyt : y * t = t * y)
    (hyz : y * (s * t * (s * t)) = s * t * (s * t) * y) (hodd : Odd (orderOf y)) :
    ∃ κ : F, (y : Matrix (Fin 3) (Fin 3) F) = κ • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨ha, hφ, hφa, hsm⟩ := hs
  obtain ⟨hb, hψ, hψb, htm⟩ := ht
  have hzE : IsElat (s * t * (s * t)) b ((ψ ⬝ᵥ a) • φ) := by
    refine ⟨hb, smul_ne_zero hψa hφ, by rw [smul_dotProduct, hφb, smul_zero], ?_⟩
    rw [Units.val_mul, Units.val_mul, hsm, htm]
    exact sq_mul_of_dotProduct_eq_zero hφa hψb hφb
  obtain ⟨κ₁, ha1, hφ1⟩ := eigen_of_commute ⟨ha, hφ, hφa, hsm⟩ hys
  obtain ⟨κ₂, hb2, hψ2⟩ := eigen_of_commute ⟨hb, hψ, hψb, htm⟩ hyt
  obtain ⟨κ₃, hb3, hφ3⟩ := eigen_of_commute hzE hyz
  set Y := (y : Matrix (Fin 3) (Fin 3) F) with hY
  have h13 : κ₃ = κ₁ := by
    have e : ((ψ ⬝ᵥ a) * κ₁) • φ = (κ₃ * (ψ ⬝ᵥ a)) • φ := by
      rw [mul_smul, mul_smul, ← hφ1, ← Matrix.smul_vecMul, hφ3]
    have e2 := smul_left_injective F hφ e
    exact (mul_right_cancel₀ hψa (by rw [← e2, mul_comm])).symm
  have h23 : κ₂ = κ₃ := smul_left_injective F hb (hb2.symm.trans hb3)
  set N := Y - κ₁ • (1 : Matrix (Fin 3) (Fin 3) F) with hN
  have hNb : N *ᵥ b = 0 := by
    rw [hN, Matrix.sub_mulVec, hb3, h13, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  have hφN : φ ᵥ* N = 0 := by
    rw [hN, Matrix.vecMul_sub, hφ1, Matrix.vecMul_smul, Matrix.vecMul_one, sub_self]
  have hψN : ψ ᵥ* N = 0 := by
    rw [hN, Matrix.vecMul_sub, hψ2, h23, h13, Matrix.vecMul_smul, Matrix.vecMul_one, sub_self]
  have hli : LinearIndependent F ![φ, ψ] := by
    refine (LinearIndependent.pair_iff' hφ).mpr fun c hc => hψa ?_
    rw [← hc, smul_dotProduct, hφa, smul_zero]
  have hNN : N * N = 0 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      map_zero, LinearMap.zero_apply]
    obtain ⟨c, hc⟩ := exists_eq_smul_of_dotProduct_eq_zero (y := N *ᵥ v) hli hφb hψb
      (by rw [Matrix.dotProduct_mulVec, hφN, zero_dotProduct])
      (by rw [Matrix.dotProduct_mulVec, hψN, zero_dotProduct]) hb
    rw [hc, Matrix.mulVec_smul, hNb, smul_zero]
  have hYN : Y = N + κ₁ • (1 : Matrix (Fin 3) (Fin 3) F) := by rw [hN, sub_add_cancel]
  have hYY : Y * Y = (κ₁ ^ 2) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    calc Y * Y = N * N + (κ₁ • N + κ₁ • N) + (κ₁ * κ₁) • (1 : Matrix (Fin 3) (Fin 3) F) := by
          rw [hYN]
          simp only [add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
            Matrix.one_mul, smul_smul]
          abel
      _ = (κ₁ ^ 2) • (1 : Matrix (Fin 3) (Fin 3) F) := by
          rw [hNN, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, zero_add, zero_add, pow_two]
  obtain ⟨j, hj⟩ := hodd
  refine ⟨(κ₁ ^ 2) ^ (j + 1), ?_⟩
  have hpow : y ^ (2 * (j + 1)) = y := by
    rw [show 2 * (j + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  have h3 : Y ^ (2 * (j + 1)) = Y := by
    have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hpow
    simpa [Units.val_pow_eq_pow_val] using this
  calc Y = Y ^ (2 * (j + 1)) := h3.symm
    _ = (Y * Y) ^ (j + 1) := by rw [pow_mul, pow_two]
    _ = ((κ₁ ^ 2) ^ (j + 1)) • (1 : Matrix (Fin 3) (Fin 3) F) := by rw [hYY, smul_pow, one_pow]

end Elations


section Sylow

variable {F : Type} [Field F] [CharP F 2]

open CFSG.RankThree.PartTwo.Sec16.KL3SubProof (IsUT.coe_inv IsUT.eq_utm utm_zero_zero_mul_self)

theorem card_le_eight_of_unitriangular {X : Type*} [Group X] [Finite X]
    (ρ : X →* GL (Fin 3) F) (hρ : Function.Injective ρ) (P : Subgroup X)
    (hUT : ∀ p ∈ P, IsUT ((ρ p : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (hZ : ∀ u v : X, IsZUT ((ρ u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) →
      IsZUT ((ρ v : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) → u ≠ 1 → v ≠ 1 → u = v)
    {x0 : X} (hx0P : x0 ∈ P) (hx0sq : x0 ^ 2 ≠ 1) : Nat.card P ≤ 8 := by
  classical
  have h2K : (2 : F) = 0 := CharTwo.two_eq_zero
  set m : X → Matrix (Fin 3) (Fin 3) F := fun x => ((ρ x : GL (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) with hmdef
  have hm_mul : ∀ x y, m (x * y) = m x * m y := fun x y => by
    simp only [hmdef, map_mul, Units.val_mul]
  have hm_one : m 1 = 1 := by simp only [hmdef, map_one, Units.val_one]
  have hm_inj : ∀ x y, m x = m y → x = y := fun x y h => hρ (Units.ext h)
  have hm_eq_one : ∀ x, m x = 1 → x = 1 := fun x h => hm_inj x 1 (by rw [h, hm_one])
  have hm_inv : ∀ x, IsUT (m x) →
      m x⁻¹ = utm (m x 0 1) (m x 1 2) (m x 0 2 + m x 0 1 * m x 1 2) := by
    intro x hx
    simp only [hmdef, map_inv]
    exact IsUT.coe_inv hx
  have hPUT : ∀ y ∈ P, IsUT (m y) := hUT
  have hx0U := hPUT x0 hx0P
  set a := m x0 0 1 with ha
  set b := m x0 1 2 with hb
  set c := m x0 0 2 with hc
  have hmx0 : m x0 = utm a b c := hx0U.eq_utm
  have hmx0i : m x0⁻¹ = utm a b (c + a * b) := hm_inv x0 hx0U
  set z := x0 ^ 2 with hzdef
  have hmz : m z = utm 0 0 (a * b) := by rw [hzdef, pow_two, hm_mul, hmx0, utm_mul_self]
  have hab : a * b ≠ 0 := by
    intro h0
    apply hx0sq
    apply hm_eq_one
    rw [hmz, h0, utm_zero]
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hab
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hab
  have hz1 : z ≠ 1 := hx0sq
  have hzZ : IsZUT (m z) := hmz ▸ isZUT_utm _
  have hZz : ∀ y, IsZUT (m y) → y = 1 ∨ y = z := by
    intro y hy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · exact Or.inr (hZ y z hy hzZ hy1 hz1)
  set val : X → F := fun y => m y 0 1 * b + a * m y 1 2 with hval
  have hcomm_m : ∀ y, IsUT (m y) → m (y * x0 * y⁻¹ * x0⁻¹) = utm 0 0 (val y) := by
    intro y hy
    obtain ⟨a', b', c', hy'⟩ : ∃ a' b' c' : F, m y = utm a' b' c' := ⟨_, _, _, hy.eq_utm⟩
    have hyi : m y⁻¹ = utm a' b' (c' + a' * b') := by
      rw [hm_inv y hy, hy']
      simp
    rw [hm_mul, hm_mul, hm_mul, hy', hmx0, hyi, hmx0i, utm_comm, hval]
    simp [hy']
  have hval_cases : ∀ y, IsUT (m y) → val y = 0 ∨ val y = a * b := by
    intro y hy
    rcases hZz _ (hcomm_m y hy ▸ isZUT_utm _) with h | h
    · left
      have := congrArg m h
      rw [hcomm_m y hy, hm_one, utm_eq_one_iff] at this
      exact this.2.2
    · right
      have := congrArg m h
      rw [hcomm_m y hy, hmz] at this
      exact (utm_inj this).2.2
  have hcomm_iff : ∀ y, IsUT (m y) → (x0 * y = y * x0 ↔ val y = 0) := by
    intro y hy
    constructor
    · intro h
      have h1 : y * x0 * y⁻¹ * x0⁻¹ = 1 := by
        rw [← h]
        group
      have := congrArg m h1
      rw [hcomm_m y hy, hm_one, utm_eq_one_iff] at this
      exact this.2.2
    · intro h
      have h1 : m (y * x0 * y⁻¹ * x0⁻¹) = m 1 := by
        rw [hcomm_m y hy, h, utm_zero, hm_one]
      have h2 := hm_inj _ _ h1
      have h3 : y * x0 = x0 * y := by
        calc y * x0 = (y * x0 * y⁻¹ * x0⁻¹) * (x0 * y) := by group
          _ = x0 * y := by rw [h2, one_mul]
      exact h3.symm
  have hval_mul : ∀ y y', IsUT (m y) → IsUT (m y') → val (y * y') = val y + val y' := by
    intro y y' hy hy'
    simp only [hval, hm_mul]
    rw [hy.eq_utm, hy'.eq_utm, utm_mul]
    simp
    ring
  set Q : Subgroup X := Subgroup.centralizer ({x0} : Set X) ⊓ P with hQdef
  have hmemQ : ∀ y, y ∈ Q ↔ y ∈ P ∧ val y = 0 := by
    intro y
    rw [hQdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (hcomm_iff y (hPUT y h2)).mp (h1 x0 rfl)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1⟩
      rintro _ rfl
      exact (hcomm_iff y (hPUT y h1)).mpr h2
  have hQP : Q ≤ P := inf_le_right
  have hQelts : ∀ y ∈ Q, y = 1 ∨ y = z ∨ y = x0 ∨ y = z * x0 := by
    intro y hyQ
    obtain ⟨hyP, hyv⟩ := (hmemQ y).mp hyQ
    have hy := hPUT y hyP
    obtain ⟨a', b', c', hy'⟩ : ∃ a' b' c' : F, m y = utm a' b' c' := ⟨_, _, _, hy.eq_utm⟩
    have hv : a' * b + a * b' = 0 := by
      have : val y = a' * b + a * b' := by simp [hval, hy']
      rw [← this, hyv]
    by_cases ha' : a' = 0
    · have hb' : b' = 0 := by
        subst ha'
        have : a * b' = 0 := by linear_combination hv
        exact (mul_eq_zero.mp this).resolve_left ha0
      rcases hZz y ⟨hy, by simp [hy', ha'], by simp [hy', hb']⟩ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hy2 : m (y * y) = utm 0 0 (a' * b') := by rw [hm_mul, hy', utm_mul_self]
      have hE1 : a' * b = a * b' := by linear_combination hv - a * b' * h2K
      rcases hZz (y * y) (hy2 ▸ isZUT_utm _) with h | h
      · exfalso
        have h0 : a' * b' = 0 := by
          have := congrArg m h
          rw [hy2, hm_one, utm_eq_one_iff] at this
          exact this.2.2
        have : a' * a' * b = 0 := by linear_combination a' * hE1 + a * h0
        rcases mul_eq_zero.mp this with h' | h'
        · exact ha' (mul_self_eq_zero.mp h')
        · exact hb0 h'
      · have h0 : a' * b' = a * b := by
          have := congrArg m h
          rw [hy2, hmz] at this
          exact (utm_inj this).2.2
        have hsq : (a' + a) * (a' + a) * b = 0 := by
          linear_combination a' * hE1 + a * h0 + (a * a' * b + a * a * b) * h2K
        have haa : a' + a = 0 := by
          rcases mul_eq_zero.mp hsq with h' | h'
          · exact mul_self_eq_zero.mp h'
          · exact absurd h' hb0
        have ha'a : a' = a := by linear_combination haa - a * h2K
        have hb'b : b' = b := by
          rw [ha'a] at hE1
          have : a * (b' - b) = 0 := by linear_combination -hE1
          exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha0)
        have hyx : IsZUT (m (y * x0⁻¹)) := by
          rw [hm_mul, hy', hmx0i, utm_mul, ha'a, hb'b]
          refine ⟨isUT_utm _ _ _, ?_, ?_⟩
          · simp only [utm_apply_zero_one]
            linear_combination a * h2K
          · simp only [utm_apply_one_two]
            linear_combination b * h2K
        rcases hZz (y * x0⁻¹) hyx with h' | h'
        · right; right; left
          calc y = y * x0⁻¹ * x0 := by group
            _ = x0 := by rw [h', one_mul]
        · right; right; right
          calc y = y * x0⁻¹ * x0 := by group
            _ = z * x0 := by rw [h']
  have hQcard : Nat.card Q ≤ 4 := by
    have hsub : (Q : Set X) ⊆ ↑({1, z, x0, z * x0} : Finset X) := by
      intro y hy
      rcases hQelts y hy with h | h | h | h <;> simp [h]
    calc Nat.card Q = (Q : Set X).ncard := (Nat.card_coe_set_eq _)
      _ ≤ (↑({1, z, x0, z * x0} : Finset X) : Set X).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ({1, z, x0, z * x0} : Finset X).card := Set.ncard_coe_finset _
      _ ≤ 4 := Finset.card_le_four
  by_cases hex : ∃ y0 ∈ P, y0 ∉ Q
  · obtain ⟨y0, hy0P, hy0Q⟩ := hex
    have hvy0 : val y0 = a * b := by
      rcases hval_cases y0 (hPUT y0 hy0P) with h | h
      · exact absurd ((hmemQ y0).mpr ⟨hy0P, h⟩) hy0Q
      · exact h
    have hindex : (Q.subgroupOf P).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨y0, hy0P⟩, fun w => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      have hwU := hPUT w w.2
      have hwy : (w : X) * y0 ∈ P := P.mul_mem w.2 hy0P
      rw [hmemQ, hmemQ, hval_mul _ _ hwU (hPUT y0 hy0P), hvy0]
      simp only [hwy, w.2, true_and]
      rcases hval_cases w hwU with h | h
      · rw [h, zero_add]
        exact Or.inr ⟨rfl, hab⟩
      · rw [h]
        exact Or.inl ⟨by linear_combination (a * b) * h2K, hab⟩
    have hcard := Subgroup.card_mul_index (Q.subgroupOf P)
    rw [hindex, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv] at hcard
    omega
  · push Not at hex
    calc Nat.card P ≤ Nat.card Q := Subgroup.card_le_of_le hex
      _ ≤ 4 := hQcard
      _ ≤ 8 := by norm_num

end Sylow


section Tools

theorem nonempty_centralizer_equiv_of_conj {G : Type*} [Group G] {u v g : G}
    (h : g⁻¹ * u * g = v) :
    Nonempty (Subgroup.centralizer ({u} : Set G) ≃* Subgroup.centralizer ({v} : Set G)) := by
  have hmap : (Subgroup.centralizer ({u} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
      Subgroup.centralizer ({v} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← h]
      calc g⁻¹ * y * g * (g⁻¹ * u * g) = g⁻¹ * (y * u) * g := by group
        _ = g⁻¹ * (u * y) * g := by rw [hy]
        _ = g⁻¹ * u * g * (g⁻¹ * y * g) := by group
    · intro hx
      refine ⟨g * x * g⁻¹, ?_, by group⟩
      rw [← h] at hx
      calc g * x * g⁻¹ * u = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by rw [hx]
        _ = u * (g * x * g⁻¹) := by group
  exact ⟨((MulAut.conj g⁻¹).subgroupMap _).trans (MulEquiv.subgroupCongr hmap)⟩

theorem mem_of_card_le_four {G : Type*} [Group G] {E : Subgroup G} [Finite E]
    (hE : Nat.card E ≤ 4) {a b c d : G} (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E) (hd : d ∈ E)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∀ x ∈ E, x = a ∨ x = b ∨ x = c ∨ x = d := by
  classical
  intro x hx
  by_contra h
  push Not at h
  obtain ⟨hxa, hxb, hxc, hxd⟩ := h
  have := Fintype.ofFinite E
  set S : Finset E := {⟨x, hx⟩, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩} with hS
  have hcard : S.card = 5 := by
    rw [hS, Finset.card_insert_of_notMem (by simp [hxa, hxb, hxc, hxd]),
      Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair (by simp [hcd])]
  have h1 := Finset.card_le_univ S
  rw [hcard, ← Nat.card_eq_fintype_card] at h1
  omega

end Tools

section ElationGroups

variable {F : Type} [Field F] [CharP F 2]

theorem elat_mul_elat_axis {c c' φ : Fin 3 → F} (h : φ ⬝ᵥ c' = 0) :
    (1 + vecMulVec c φ : Matrix (Fin 3) (Fin 3) F) * (1 + vecMulVec c' φ) =
      1 + vecMulVec (c + c') φ := by
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, vecMulVec_mul_vecMulVec, h, zero_smul,
    vecMulVec_zero, add_zero, add_vecMulVec, add_assoc]

theorem elat_mul_elat_center {b δ δ' : Fin 3 → F} (h : δ ⬝ᵥ b = 0) :
    (1 + vecMulVec b δ : Matrix (Fin 3) (Fin 3) F) * (1 + vecMulVec b δ') =
      1 + vecMulVec b (δ + δ') := by
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, vecMulVec_mul_vecMulVec, h, zero_smul,
    vecMulVec_zero, add_zero, vecMulVec_add, add_assoc]

theorem vec_add_self (c : Fin 3 → F) : c + c = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (c i)

noncomputable def axisElatGroup (D : Subgroup (GL (Fin 3) F)) (φ : Fin 3 → F) : Subgroup D where
  carrier := {x | ∃ c : Fin 3 → F, φ ⬝ᵥ c = 0 ∧
    ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec c φ}
  mul_mem' := by
    rintro x y ⟨c, hc, hx⟩ ⟨c', hc', hy⟩
    refine ⟨c + c', by rw [dotProduct_add, hc, hc', add_zero], ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hx, hy, elat_mul_elat_axis hc']
  one_mem' := ⟨0, by simp, by simp⟩
  inv_mem' := by
    rintro x ⟨c, hc, hx⟩
    refine ⟨c, hc, ?_⟩
    have hxx : x * x = 1 := Subtype.ext (Units.ext (by
      rw [Subgroup.coe_mul, Units.val_mul, hx, elat_mul_elat_axis hc, vec_add_self,
        zero_vecMulVec, add_zero]
      rfl))
    rw [inv_eq_of_mul_eq_one_right hxx, hx]

noncomputable def centerElatGroup (D : Subgroup (GL (Fin 3) F)) (b : Fin 3 → F) : Subgroup D where
  carrier := {x | ∃ δ : Fin 3 → F, δ ⬝ᵥ b = 0 ∧
    ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec b δ}
  mul_mem' := by
    rintro x y ⟨δ, hδ, hx⟩ ⟨δ', hδ', hy⟩
    refine ⟨δ + δ', by rw [add_dotProduct, hδ, hδ', add_zero], ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hx, hy, elat_mul_elat_center hδ]
  one_mem' := ⟨0, by simp, by simp⟩
  inv_mem' := by
    rintro x ⟨δ, hδ, hx⟩
    refine ⟨δ, hδ, ?_⟩
    have hxx : x * x = 1 := Subtype.ext (Units.ext (by
      rw [Subgroup.coe_mul, Units.val_mul, hx, elat_mul_elat_center hδ, vec_add_self,
        vecMulVec_zero, add_zero]
      rfl))
    rw [inv_eq_of_mul_eq_one_right hxx, hx]

theorem axisElatGroup_comm {D : Subgroup (GL (Fin 3) F)} {φ : Fin 3 → F} {x y : D}
    (hx : x ∈ axisElatGroup D φ) (hy : y ∈ axisElatGroup D φ) : x * y = y * x := by
  obtain ⟨c, hc, hxm⟩ := hx
  obtain ⟨c', hc', hym⟩ := hy
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hxm, hym,
    elat_mul_elat_axis hc', elat_mul_elat_axis hc, add_comm c c']

theorem axisElatGroup_mul_self {D : Subgroup (GL (Fin 3) F)} {φ : Fin 3 → F} {x : D}
    (hx : x ∈ axisElatGroup D φ) : x * x = 1 := by
  obtain ⟨c, hc, hxm⟩ := hx
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, hxm, elat_mul_elat_axis hc, vec_add_self, zero_vecMulVec,
    add_zero]
  rfl

theorem centerElatGroup_comm {D : Subgroup (GL (Fin 3) F)} {b : Fin 3 → F} {x y : D}
    (hx : x ∈ centerElatGroup D b) (hy : y ∈ centerElatGroup D b) : x * y = y * x := by
  obtain ⟨δ, hδ, hxm⟩ := hx
  obtain ⟨δ', hδ', hym⟩ := hy
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hxm, hym,
    elat_mul_elat_center hδ, elat_mul_elat_center hδ', add_comm δ δ']

theorem centerElatGroup_mul_self {D : Subgroup (GL (Fin 3) F)} {b : Fin 3 → F} {x : D}
    (hx : x ∈ centerElatGroup D b) : x * x = 1 := by
  obtain ⟨δ, hδ, hxm⟩ := hx
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, hxm, elat_mul_elat_center hδ, vec_add_self, vecMulVec_zero,
    add_zero]
  rfl

theorem conj_elat_matrix (y : GL (Fin 3) F) (c φ : Fin 3 → F) :
    (y : Matrix (Fin 3) (Fin 3) F) * (1 + vecMulVec c φ) * ((y⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) =
      1 + vecMulVec ((y : Matrix (Fin 3) (Fin 3) F) *ᵥ c)
        (φ ᵥ* ((y⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
  have hyy : (y : Matrix (Fin 3) (Fin 3) F) * ((y⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [mul_add, add_mul, mul_one, hyy, mul_vecMulVec, vecMulVec_mul]

theorem conj_mem_axisElatGroup {D : Subgroup (GL (Fin 3) F)} {φ : Fin 3 → F} {x y : D} {κ : F}
    (hκ : κ ≠ 0) (hy : φ ᵥ* ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = κ • φ)
    (hx : x ∈ axisElatGroup D φ) : y * x * y⁻¹ ∈ axisElatGroup D φ := by
  obtain ⟨c, hc, hxm⟩ := hx
  set Y := ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hY
  set Yi := (((y : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hYi
  have hYYi : Y * Yi = 1 := by rw [hY, hYi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hφYi : φ ᵥ* Yi = κ⁻¹ • φ := by
    have h1 : φ ᵥ* Y ᵥ* Yi = φ := by rw [Matrix.vecMul_vecMul, hYYi, Matrix.vecMul_one]
    rw [hy, Matrix.smul_vecMul] at h1
    calc φ ᵥ* Yi = κ⁻¹ • (κ • φ ᵥ* Yi) := by rw [smul_smul, inv_mul_cancel₀ hκ, one_smul]
      _ = κ⁻¹ • φ := by rw [h1]
  refine ⟨κ⁻¹ • (Y *ᵥ c), ?_, ?_⟩
  · rw [dotProduct_smul, Matrix.dotProduct_mulVec, hy, smul_dotProduct, hc, smul_zero, smul_zero]
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul, hxm,
      ← hY, ← hYi, conj_elat_matrix, ← hY, ← hYi, hφYi, vecMulVec_smul, smul_vecMulVec]

theorem conj_mem_centerElatGroup {D : Subgroup (GL (Fin 3) F)} {b : Fin 3 → F} {x y : D} {κ : F}
    (hκ : κ ≠ 0) (hy : ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ b = κ • b)
    (hx : x ∈ centerElatGroup D b) : y * x * y⁻¹ ∈ centerElatGroup D b := by
  obtain ⟨δ, hδ, hxm⟩ := hx
  set Y := ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hY
  set Yi := (((y : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hYi
  have hYiY : Yi * Y = 1 := by rw [hY, hYi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hYib : Yi *ᵥ b = κ⁻¹ • b := by
    have h1 : Yi *ᵥ (Y *ᵥ b) = b := by rw [Matrix.mulVec_mulVec, hYiY, Matrix.one_mulVec]
    rw [hy, Matrix.mulVec_smul] at h1
    calc Yi *ᵥ b = κ⁻¹ • (κ • Yi *ᵥ b) := by rw [smul_smul, inv_mul_cancel₀ hκ, one_smul]
      _ = κ⁻¹ • b := by rw [h1]
  refine ⟨κ • (δ ᵥ* Yi), ?_, ?_⟩
  · rw [smul_dotProduct, ← Matrix.dotProduct_mulVec, hYib, dotProduct_smul, hδ, smul_zero,
      smul_zero]
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul, hxm,
      ← hY, ← hYi, conj_elat_matrix, ← hY, ← hYi, hy, smul_vecMulVec, vecMulVec_smul]

end ElationGroups

section Groups

theorem card_le_four_of_sylow {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (hT8 : Nat.card (T : Subgroup G) = 8) {s t : G} (hsT : s ∈ (T : Subgroup G))
    (htT : t ∈ (T : Subgroup G)) (hst : s * t ≠ t * s) (E : Subgroup G)
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, pow_two]
    exact hE2 x x.2)⟩
  obtain ⟨T', hET'⟩ := hEp.exists_le_sylow
  have hT'8 : Nat.card (T' : Subgroup G) = 8 := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity T, hT8]
  have hdvd : Nat.card E ∣ 8 := hT'8 ▸ Subgroup.card_dvd_of_le hET'
  have hne : Nat.card E ≠ 8 := by
    intro h8
    have hEq : E = T' := Subgroup.eq_of_le_of_card_ge hET' (by rw [hT'8, h8])
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T T'
    apply hst
    have hs' : g * s * g⁻¹ ∈ E := by
      rw [hEq, ← hg, CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_conj_smul_iff]
      have e : g⁻¹ * (g * s * g⁻¹) * g = s := by group
      rw [e]
      exact hsT
    have ht' : g * t * g⁻¹ ∈ E := by
      rw [hEq, ← hg, CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_conj_smul_iff]
      have e : g⁻¹ * (g * t * g⁻¹) * g = t := by group
      rw [e]
      exact htT
    have h1 := hEc _ hs' _ ht'
    have h2 : g * (s * t) * g⁻¹ = g * (t * s) * g⁻¹ := by
      calc g * (s * t) * g⁻¹ = g * s * g⁻¹ * (g * t * g⁻¹) := by group
        _ = g * t * g⁻¹ * (g * s * g⁻¹) := h1
        _ = g * (t * s) * g⁻¹ := by group
    simpa using h2
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num] at hdvd hne
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk3 : k ≠ 3 := fun h => hne (by rw [hk', h])
  calc Nat.card E = 2 ^ k := hk'
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 4 := by norm_num

theorem conj_sq_of_sylow_eight {X : Type*} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) (P : Sylow 2 X) (hP8 : Nat.card (P : Subgroup X) = 8)
    {x : X} (hxP : x ∈ (P : Subgroup X)) (hx4 : orderOf x = 4) :
    ∀ u : X, orderOf u = 2 → ∃ g, g⁻¹ * u * g = x ^ 2 := by
  classical
  set Q : Subgroup X := Subgroup.zpowers x with hQ
  have hQP : Q ≤ (P : Subgroup X) := by rw [hQ, Subgroup.zpowers_le]; exact hxP
  have hQ4 : Nat.card Q = 4 := by rw [hQ, Nat.card_zpowers, hx4]
  have hindex : Q.relIndex (P : Subgroup X) = 2 := by
    have hcard := Subgroup.card_mul_index (Q.subgroupOf (P : Subgroup X))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hQ4, hP8] at hcard
    rw [Subgroup.relIndex]
    omega
  have hx2 : x ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have hx44 : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have hinvQ : ∀ w ∈ Q, w ^ 2 = 1 → w ≠ 1 → w = x ^ 2 := by
    intro w hw hw2 hw1
    rw [hQ, mem_zpowers_iff_mem_range_orderOf, hx4] at hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
    rw [Finset.mem_range] at hk
    interval_cases k
    · exact absurd (pow_zero _) hw1
    · exact absurd (by rwa [pow_one] at hw2) hx2
    · rfl
    · exfalso
      apply hx2
      rw [← pow_mul] at hw2
      calc x ^ 2 = x ^ (3 * 2) * (x ^ 4)⁻¹ := by rw [← pow_sub x (by norm_num : 4 ≤ 3 * 2)]
        _ = 1 := by rw [hw2, hx44, inv_one, mul_one]
  intro u hu
  by_contra hno
  push Not at hno
  have hnoQ : ∀ g, g⁻¹ * u * g ∉ Q := by
    intro g hg
    apply hno g
    refine hinvQ _ hg ?_ ?_
    · have e : (g⁻¹ * u * g) ^ 2 = g⁻¹ * u ^ 2 * g := by rw [pow_two, pow_two]; group
      rw [e, ← hu, pow_orderOf_eq_one]
      group
    · intro h1
      have : u = 1 := by
        calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
          _ = 1 := by rw [h1]; group
      rw [this, orderOf_one] at hu
      norm_num at hu
  obtain ⟨N, hN, hNsq, huN⟩ := CFSG.Quasithin.thompson_transfer_exists_normal P hQP hindex hu hnoQ
  haveI := hN
  rcases hs.eq_bot_or_eq_top_of_normal N with h | h
  · obtain ⟨a', b', hab'⟩ := hnab
    apply hab'
    refine CFSG.RankThree.PartTwo.Sec16.KL3SubProof.mul_comm_of_forall_sq_eq_one (fun y => ?_) a' b'
    have := hNsq y
    rwa [h, Subgroup.mem_bot] at this
  · exact huN (h ▸ Subgroup.mem_top u)

theorem isPGroup_centralizer_mk {D : Type*} [Group D] [Finite D]
    (hZ3 : ∀ z ∈ Subgroup.center D, z ^ 3 = 1) {z : D} (hzz : z * z = 1)
    (hcen : ∀ y : D, y * z = z * y → Odd (orderOf y) → y ∈ Subgroup.center D) :
    IsPGroup 2 (Subgroup.centralizer
      ({QuotientGroup.mk' (Subgroup.center D) z} : Set (D ⧸ Subgroup.center D))) := by
  set mk : D →* D ⧸ Subgroup.center D := QuotientGroup.mk' (Subgroup.center D) with hmk
  have hmk_eq_one : ∀ g : D, mk g = 1 ↔ g ∈ Subgroup.center D := fun g =>
    QuotientGroup.eq_one_iff g
  have huniq : ∀ {q : ℕ}, q.Prime →
      q ∣ Nat.card (Subgroup.centralizer ({mk z} : Set (D ⧸ Subgroup.center D))) → q = 2 := by
    intro q hq hqd
    by_contra hq2
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨yb, hyb⟩ := exists_prime_orderOf_dvd_card' q hqd
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center D) (yb : D ⧸ Subgroup.center D)
    have hybz : (yb : D ⧸ Subgroup.center D) * mk z = mk z * yb :=
      Subgroup.mem_centralizer_singleton_iff.mp yb.2
    have hyz : y * z = z * y := by
      set ζ := y * z * y⁻¹ * z⁻¹ with hζ
      have hζZ : ζ ∈ Subgroup.center D := by
        rw [← hmk_eq_one, hζ, map_mul, map_mul, map_mul, map_inv, map_inv]
        change (QuotientGroup.mk' (Subgroup.center D)) y * mk z * _ * _ = 1
        rw [hy, hybz]
        group
      have h1 : y * z * y⁻¹ = ζ * z := by rw [hζ]; group
      have h2 : (y * z * y⁻¹) * (y * z * y⁻¹) = 1 := by
        calc (y * z * y⁻¹) * (y * z * y⁻¹) = y * (z * z) * y⁻¹ := by group
          _ = 1 := by rw [hzz]; group
      have hζz : z * ζ = ζ * z := Subgroup.mem_center_iff.mp hζZ z
      have h3 : ζ * ζ = 1 := by
        calc ζ * ζ = ζ * ζ * (z * z) := by rw [hzz, mul_one]
          _ = ζ * (z * ζ) * z := by rw [hζz]; group
          _ = ζ * z * (ζ * z) := by group
          _ = 1 := by rw [← h1]; exact h2
      have h4 := hZ3 ζ hζZ
      have hζ1 : ζ = 1 := by
        calc ζ = ζ ^ 3 * (ζ * ζ)⁻¹ := by group
          _ = 1 := by rw [h4, h3, inv_one, mul_one]
      rw [hζ1, one_mul] at h1
      calc y * z = y * z * y⁻¹ * y := by group
        _ = z * y := by rw [h1]
    have hyq : y ^ q ∈ Subgroup.center D := by
      rw [← hmk_eq_one, map_pow]
      change (QuotientGroup.mk' (Subgroup.center D)) y ^ q = 1
      rw [hy, ← Subgroup.coe_pow, ← hyb, pow_orderOf_eq_one, Subgroup.coe_one]
    have hyodd : Odd (orderOf y) := by
      have h3 := hZ3 _ hyq
      rw [← pow_mul] at h3
      exact Odd.of_dvd_nat ((hq.odd_of_ne_two hq2).mul (by decide)) (orderOf_dvd_of_pow_eq_one h3)
    have hyZ := hcen y hyz hyodd
    apply hq.one_lt.ne'
    rw [← hyb, orderOf_eq_one_iff]
    apply Subtype.ext
    rw [Subgroup.coe_one, ← hy]
    exact (hmk_eq_one y).mpr hyZ
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' huniq)

end Groups

section Small

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem card_le_eight_of_small {D : Subgroup (GL (Fin 3) F)}
    (hsmall : ∀ x ∈ D, ∀ y ∈ D, ∀ (a φ : Fin 3 → F) (c : F),
      IsElat x a φ → IsElat y a (c • φ) → x = y)
    {T : Subgroup D} (hT2 : IsPGroup 2 T) {x0 : D} (hx0T : x0 ∈ T) (hx0sq : x0 ^ 2 ≠ 1) :
    Nat.card T ≤ 8 := by
  obtain ⟨B, hB⟩ := CFSG.RankThree.PartTwo.Sec16.KL3SubProof.exists_conj_mem_utSub
    (T.map D.subtype) (hT2.map D.subtype)
  set ρ : D →* GL (Fin 3) F := (MulAut.conj B⁻¹).toMonoidHom.comp D.subtype with hρdef
  have hρ : ∀ j : D, ρ j = B⁻¹ * (j : GL (Fin 3) F) * B := fun j => by simp [hρdef]
  have hρinj : Function.Injective ρ := (MulAut.conj B⁻¹).injective.comp D.subtype_injective
  refine card_le_eight_of_unitriangular ρ hρinj T (fun p hp => ?_)
    (fun u v hu hv hu1 hv1 => ?_) hx0T hx0sq
  · rw [hρ]
    exact hB _ ⟨p, hp, rfl⟩
  · rw [hρ] at hu hv
    have hu1' : (u : GL (Fin 3) F) ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hv1' : (v : GL (Fin 3) F) ≠ 1 := fun h => hv1 (Subtype.ext h)
    obtain ⟨c₁, hc₁, -, huE⟩ :=
      CFSG.RankThree.PartTwo.Sec16.KL3SubProof.exists_isElat_of_isZUT hu hu1'
    obtain ⟨c₂, -, -, hvE⟩ :=
      CFSG.RankThree.PartTwo.Sec16.KL3SubProof.exists_isElat_of_isZUT hv hv1'
    have hφ' : (![0, 0, c₂] : Fin 3 → F) ᵥ* ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (c₂ / c₁) • ((![0, 0, c₁] : Fin 3 → F) ᵥ*
          ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
      rw [← Matrix.smul_vecMul]
      congr 1
      ext i
      fin_cases i <;> simp [div_mul_cancel₀ _ hc₁]
    rw [hφ'] at hvE
    exact Subtype.ext (hsmall _ u.2 _ v.2 _ _ _ huE hvE)

end Small

section SpecialPair

variable {F : Type} [Field F] [CharP F 2]

theorem special_pair_facts {D : Subgroup (GL (Fin 3) F)} {s t : D} {a φ b ψ : Fin 3 → F}
    (hs : IsElat (s : GL (Fin 3) F) a φ) (ht : IsElat (t : GL (Fin 3) F) b ψ)
    (hφb : φ ⬝ᵥ b = 0) (hψa : ψ ⬝ᵥ a ≠ 0) :
    IsElat ((s * t * (s * t) : D) : GL (Fin 3) F) b ((ψ ⬝ᵥ a) • φ) ∧
      s * s = 1 ∧ t * t = 1 ∧ s ≠ 1 ∧ t ≠ 1 ∧ s * t * (s * t) ≠ 1 ∧
      s * t * (s * t) * (s * t * (s * t)) = 1 ∧
      s ≠ s * t * (s * t) ∧ t ≠ s * t * (s * t) ∧
      s * (s * t * (s * t)) = s * t * (s * t) * s ∧
      t * (s * t * (s * t)) = s * t * (s * t) * t := by
  obtain ⟨ha, hφ, hφa, hsm⟩ := id hs
  obtain ⟨hb, hψ, hψb, htm⟩ := id ht
  set z : D := s * t * (s * t) with hz
  have hzE : IsElat ((z : D) : GL (Fin 3) F) b ((ψ ⬝ᵥ a) • φ) := by
    refine ⟨hb, smul_ne_zero hψa hφ, by rw [smul_dotProduct, hφb, smul_zero], ?_⟩
    simp only [hz, Subgroup.coe_mul, Units.val_mul, hsm, htm]
    exact sq_mul_of_dotProduct_eq_zero hφa hψb hφb
  have hss : s * s = 1 := Subtype.ext (by simpa using hs.mul_self)
  have htt : t * t = 1 := Subtype.ext (by simpa using ht.mul_self)
  have hzz : z * z = 1 := Subtype.ext (by simpa using hzE.mul_self)
  have hz1 : z ≠ 1 := fun h => hzE.ne_one (by rw [h]; rfl)
  have hs1 : s ≠ 1 := fun h => hs.ne_one (by rw [h]; rfl)
  have ht1 : t ≠ 1 := fun h => ht.ne_one (by rw [h]; rfl)
  have hsz_ne : s ≠ z := by
    intro h
    have h1 := congrArg (fun g : D => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
    simp only [hsm, hzE.2.2.2] at h1
    obtain ⟨c, hc⟩ := exists_eq_smul_of_vecMulVec_eq ha hφ (add_left_cancel h1)
    apply hψa
    have h2 : ψ ⬝ᵥ b = c * (ψ ⬝ᵥ a) := by rw [hc, dotProduct_smul, smul_eq_mul]
    rw [hψb] at h2
    rcases mul_eq_zero.mp h2.symm with h0 | h0
    · exact absurd (by rw [hc, h0, zero_smul]) hb
    · exact h0
  have htz_ne : t ≠ z := by
    intro h
    have h1 := congrArg (fun g : D => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
    simp only [htm, hzE.2.2.2] at h1
    obtain ⟨c, hc⟩ := exists_eq_smul_of_vecMulVec_eq' hb hψ (add_left_cancel h1)
    apply hψa
    have h2 : ((ψ ⬝ᵥ a) • φ) ⬝ᵥ a = c * (ψ ⬝ᵥ a) := by rw [hc, smul_dotProduct, smul_eq_mul]
    rw [smul_dotProduct, hφa, smul_zero] at h2
    rcases mul_eq_zero.mp h2.symm with h0 | h0
    · exfalso
      apply smul_ne_zero hψa hφ
      rw [hc, h0, zero_smul]
    · exact h0
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hx0i : (s * t)⁻¹ = t * s := by rw [_root_.mul_inv_rev, hsi, hti]
  have hsz : s * z = z * s := by
    have h1 : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by rw [hx0i, hsi, ← mul_assoc, hss, one_mul]
    have h2 : s * z * s⁻¹ = z := by
      rw [hz, ← pow_two, ← conj_pow, h1, inv_pow, pow_two, ← hz, hzi]
    calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [h2]
  have htz : t * z = z * t := by
    have h1 : t * (s * t) * t⁻¹ = (s * t)⁻¹ := by
      rw [hx0i, hti, mul_assoc, mul_assoc, htt, mul_one]
    have h2 : t * z * t⁻¹ = z := by
      rw [hz, ← pow_two, ← conj_pow, h1, inv_pow, pow_two, ← hz, hzi]
    calc t * z = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [h2]
  exact ⟨hzE, hss, htt, hs1, ht1, hz1, hzz, hsz_ne, htz_ne, hsz, htz⟩

theorem mem_center_of_odd_commute [Finite F] {D : Subgroup (GL (Fin 3) F)}
    (hE4 : ∀ E : Subgroup D, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
      Nat.card E ≤ 4)
    {s t : D} {a φ b ψ : Fin 3 → F} (hs : IsElat (s : GL (Fin 3) F) a φ)
    (ht : IsElat (t : GL (Fin 3) F) b ψ) (hφb : φ ⬝ᵥ b = 0) (hψa : ψ ⬝ᵥ a ≠ 0)
    {y : D} (hyz : y * (s * t * (s * t)) = s * t * (s * t) * y) (hyodd : Odd (orderOf y)) :
    y ∈ Subgroup.center D := by
  obtain ⟨hzE, hss, htt, hs1, ht1, hz1, hzz, hsz_ne, htz_ne, -, -⟩ :=
    special_pair_facts hs ht hφb hψa
  obtain ⟨ha, hφ, hφa, hsm⟩ := id hs
  obtain ⟨hb, hψ, hψb, htm⟩ := id ht
  set z : D := s * t * (s * t) with hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  set Z0 := axisElatGroup D φ with hZ0
  set Z1 := centerElatGroup D b with hZ1
  have hsZ0 : s ∈ Z0 := ⟨a, hφa, hsm⟩
  have hzZ0 : z ∈ Z0 := ⟨(ψ ⬝ᵥ a) • b, by rw [dotProduct_smul, hφb, smul_zero], by
    rw [hzE.2.2.2, vecMulVec_smul, smul_vecMulVec]⟩
  have htZ1 : t ∈ Z1 := ⟨ψ, hψb, htm⟩
  have hzZ1 : z ∈ Z1 := ⟨(ψ ⬝ᵥ a) • φ, by rw [smul_dotProduct, hφb, smul_zero], hzE.2.2.2⟩
  have hsz1 : s * z ≠ 1 := by
    intro h
    apply hsz_ne
    calc s = s * z * z⁻¹ := by group
      _ = z := by rw [h, one_mul, hzi]
  have htz1 : t * z ≠ 1 := by
    intro h
    apply htz_ne
    calc t = t * z * z⁻¹ := by group
      _ = z := by rw [h, one_mul, hzi]
  have hZ0elts : ∀ x ∈ Z0, x = 1 ∨ x = s ∨ x = z ∨ x = s * z :=
    mem_of_card_le_four (hE4 Z0 (fun x hx y hy => axisElatGroup_comm hx hy)
      (fun x hx => axisElatGroup_mul_self hx)) Z0.one_mem hsZ0 hzZ0 (Z0.mul_mem hsZ0 hzZ0)
      hs1.symm hz1.symm hsz1.symm hsz_ne
      (fun h => hz1 (mul_left_cancel (h.symm.trans (mul_one s).symm)))
      (fun h => hs1 (mul_right_cancel ((one_mul z).trans h)).symm)
  have hZ1elts : ∀ x ∈ Z1, x = 1 ∨ x = t ∨ x = z ∨ x = t * z :=
    mem_of_card_le_four (hE4 Z1 (fun x hx y hy => centerElatGroup_comm hx hy)
      (fun x hx => centerElatGroup_mul_self hx)) Z1.one_mem htZ1 hzZ1 (Z1.mul_mem htZ1 hzZ1)
      ht1.symm hz1.symm htz1.symm htz_ne
      (fun h => hz1 (mul_left_cancel (h.symm.trans (mul_one t).symm)))
      (fun h => ht1 (mul_right_cancel ((one_mul z).trans h)).symm)
  have hyzGL : (y : GL (Fin 3) F) * (z : GL (Fin 3) F) = (z : GL (Fin 3) F) * y := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hyz]
  obtain ⟨κ, hκb, hκφ⟩ := eigen_of_commute hzE hyzGL
  have hφY : φ ᵥ* ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = κ • φ := by
    rw [Matrix.smul_vecMul, smul_comm κ (ψ ⬝ᵥ a) φ] at hκφ
    exact smul_right_injective _ hψa hκφ
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    apply hb
    have h1 : (((y : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ b) = b := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [hκb, zero_smul, Matrix.mulVec_zero] at h1
    exact h1.symm
  obtain ⟨j, hj⟩ := hyodd
  have hcent_of_sq : ∀ w : D, y * y * w = w * (y * y) → y * w = w * y := by
    intro w hw
    have hpow : (y * y) ^ (j + 1) = y := by
      rw [← pow_two, ← pow_mul, show 2 * (j + 1) = orderOf y + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    have hmem : y * y ∈ Subgroup.centralizer ({w} : Set D) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hw
    have hmem' := Subgroup.pow_mem _ hmem (j + 1)
    rw [hpow] at hmem'
    exact Subgroup.mem_centralizer_singleton_iff.mp hmem'
  have hyzy : y * z * y⁻¹ = z := by rw [hyz, mul_assoc, mul_inv_cancel, mul_one]
  have key : ∀ w : D, w ≠ 1 → w ≠ z → (w * z) * (w * z) = 1 → w * z = z * w →
      (y * w * y⁻¹ = 1 ∨ y * w * y⁻¹ = w ∨ y * w * y⁻¹ = z ∨ y * w * y⁻¹ = w * z) →
      y * w = w * y := by
    intro w hw1 hwz _ hwzc h
    apply hcent_of_sq
    rcases h with h | h | h | h
    · exfalso
      apply hw1
      calc w = y⁻¹ * (y * w * y⁻¹) * y := by group
        _ = 1 := by rw [h]; group
    · have h' : y * w = w * y := by
        calc y * w = y * w * y⁻¹ * y := by group
          _ = w * y := by rw [h]
      rw [mul_assoc, h', ← mul_assoc, h', mul_assoc]
    · exfalso
      apply hwz
      calc w = y⁻¹ * (y * w * y⁻¹) * y := by group
        _ = y⁻¹ * (y * z * y⁻¹) * y := by rw [h, hyzy]
        _ = z := by group
    · have e1 : y * w = w * z * y := by
        calc y * w = y * w * y⁻¹ * y := by group
          _ = w * z * y := by rw [h]
      have e2 : y * z = z * y := hyz
      calc y * y * w = y * (y * w) := mul_assoc _ _ _
        _ = y * (w * z * y) := by rw [e1]
        _ = (y * w) * (z * y) := by simp only [mul_assoc]
        _ = (w * z * y) * (z * y) := by rw [e1]
        _ = w * z * (y * z) * y := by simp only [mul_assoc]
        _ = w * z * (z * y) * y := by rw [e2]
        _ = w * (z * z) * (y * y) := by simp only [mul_assoc]
        _ = w * (y * y) := by rw [hzz, mul_one]
  have hszz : s * z * (s * z) = 1 := axisElatGroup_mul_self (Z0.mul_mem hsZ0 hzZ0)
  have htzz : t * z * (t * z) = 1 := centerElatGroup_mul_self (Z1.mul_mem htZ1 hzZ1)
  have hys : y * s = s * y := key s hs1 hsz_ne hszz (axisElatGroup_comm hsZ0 hzZ0)
    (hZ0elts _ (conj_mem_axisElatGroup hκ0 hφY hsZ0))
  have hyt : y * t = t * y := key t ht1 htz_ne htzz (centerElatGroup_comm htZ1 hzZ1)
    (hZ1elts _ (conj_mem_centerElatGroup hκ0 hκb htZ1))
  have hysGL : (y : GL (Fin 3) F) * s = s * y := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hys]
  have hytGL : (y : GL (Fin 3) F) * t = t * y := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hyt]
  have hyoddGL : Odd (orderOf (y : GL (Fin 3) F)) := by
    rw [Subgroup.orderOf_coe]
    exact ⟨j, hj⟩
  obtain ⟨κ', hκ'⟩ := eq_scalar_of_commute_special hs ht hφb hψa hysGL hytGL hyzGL hyoddGL
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hκ', Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]

end SpecialPair

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem psl2_of_small
    {D : Subgroup (GL (Fin 3) F)} (hDq : IsQuasisimple D)
    (hZ3 : ∀ z ∈ Subgroup.center D, z ^ 3 = 1)
    (hsmall : ∀ x ∈ D, ∀ y ∈ D, ∀ (a φ : Fin 3 → F) (c : F),
      IsElat x a φ → IsElat y a (c • φ) → x = y)
    {s t : D} {a φ b ψ : Fin 3 → F} (hs : IsElat (s : GL (Fin 3) F) a φ)
    (ht : IsElat (t : GL (Fin 3) F) b ψ) (hφb : φ ⬝ᵥ b = 0) (hψa : ψ ⬝ᵥ a ≠ 0) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K'), (Nat.card K' = 7 ∨ Nat.card K' = 9) ∧
      Nonempty (D ⧸ Subgroup.center D ≃* CFSG.GorensteinWalter.PSL2 K') := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hKs : IsSimpleGroup (D ⧸ Subgroup.center D) := hDq.2.1
  have hnabK := hDq.2.2
  set mk : D →* D ⧸ Subgroup.center D := QuotientGroup.mk' (Subgroup.center D) with hmk
  have hmk_surj : Function.Surjective mk := QuotientGroup.mk'_surjective _
  have hmk_eq_one : ∀ g : D, mk g = 1 ↔ g ∈ Subgroup.center D := fun g =>
    QuotientGroup.eq_one_iff g
  obtain ⟨hzE, hss, htt, hs1, ht1, hz1, hzz, hsz_ne, htz_ne, hsz, htz⟩ :=
    special_pair_facts hs ht hφb hψa
  set x0 : D := s * t with hx0
  set z : D := x0 * x0 with hz
  have hx0sq : x0 ^ 2 ≠ 1 := by rw [pow_two]; exact hz1
  have hx04 : orderOf x0 = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x0) (by norm_num; exact hx0sq)
      (by
        rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two]
        exact hzz)
    simpa using h
  have hso : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hss) hs1
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hst : s * t ≠ t * s := by
    intro h
    apply hz1
    rw [hz, hx0]
    calc s * t * (s * t) = s * (t * s) * t := by simp only [mul_assoc]
      _ = s * (s * t) * t := by rw [h]
      _ = 1 := by rw [← mul_assoc, hss, one_mul, htt]
  set C : Subgroup D := Subgroup.closure ({t, s} : Set D) with hCdef
  obtain ⟨eC⟩ := CFSG.OddStandard.HigherRank.YamadaG23.dihedral_of_involutions' (C := C) rfl hto
    hso hx04
  have hC8 : Nat.card C = 8 := by rw [Nat.card_congr eC.toEquiv, DihedralGroup.nat_card]
  have hsC : s ∈ C := Subgroup.subset_closure (by simp)
  have htC : t ∈ C := Subgroup.subset_closure (by simp)
  have hx0C : x0 ∈ C := C.mul_mem hsC htC
  have hC2 : IsPGroup 2 C := IsPGroup.of_card (n := 3) (by rw [hC8]; norm_num)
  obtain ⟨T, hCT⟩ := hC2.exists_le_sylow
  have hT8 : Nat.card (T : Subgroup D) = 8 := by
    apply le_antisymm (card_le_eight_of_small hsmall T.isPGroup' (hCT hx0C) hx0sq)
    have h := Subgroup.card_dvd_of_le hCT
    rw [hC8] at h
    exact Nat.le_of_dvd Nat.card_pos h
  have hTC : (T : Subgroup D) = C := (Subgroup.eq_of_le_of_card_ge hCT (by rw [hT8, hC8])).symm
  have hsT : s ∈ (T : Subgroup D) := hCT hsC
  have htT : t ∈ (T : Subgroup D) := hCT htC
  have hx0T : x0 ∈ (T : Subgroup D) := hCT hx0C
  have hzT : z ∈ (T : Subgroup D) := (T : Subgroup D).mul_mem hx0T hx0T
  have hTZ : ∀ g ∈ (T : Subgroup D), g ∈ Subgroup.center D → g = 1 := by
    intro g hgT hgZ
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨g, hgT⟩
    have h1 : g ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have h2 := orderOf_dvd_of_pow_eq_one h1
    have h3 := orderOf_dvd_of_pow_eq_one (hZ3 g hgZ)
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have h4 : orderOf g ∣ 1 := by
      have := Nat.dvd_gcd h2 h3
      rwa [Nat.Coprime.gcd_eq_one hcop] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
  have hmk_ne_one : ∀ g ∈ (T : Subgroup D), g ≠ 1 → mk g ≠ 1 := fun g hg hg1 h =>
    hg1 (hTZ g hg ((hmk_eq_one g).mp h))
  set Tb : Sylow 2 (D ⧸ Subgroup.center D) := T.mapSurjective hmk_surj with hTb
  have hTbmap : (Tb : Subgroup (D ⧸ Subgroup.center D)) = (T : Subgroup D).map mk :=
    Sylow.coe_mapSurjective hmk_surj T
  have hTb8 : Nat.card (Tb : Subgroup (D ⧸ Subgroup.center D)) = 8 := by
    have hinj : Function.Injective (mk.comp (T : Subgroup D).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro g hg
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hmk_eq_one] at hg
      exact Subtype.ext (hTZ _ g.2 hg)
    rw [hTbmap, ← hT8, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      MonoidHom.range_comp, Subgroup.range_subtype]
  have hmz1 : mk z ≠ 1 := hmk_ne_one z hzT hz1
  have hmx04 : orderOf (mk x0) = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := mk x0)
      (by norm_num; rw [pow_two, ← map_mul]; exact hmz1)
      (by
        rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two, ← map_mul, ← hz, ← map_mul,
          hzz, map_one])
    simpa using h
  have hmz : mk x0 ^ 2 = mk z := by rw [pow_two, ← map_mul]
  have hconj : ∀ u : D ⧸ Subgroup.center D, orderOf u = 2 → ∃ g, g⁻¹ * u * g = mk z := by
    intro u hu
    obtain ⟨g, hg⟩ := conj_sq_of_sylow_eight hKs hnabK Tb hTb8
      (by rw [hTbmap]; exact ⟨x0, hx0T, rfl⟩) hmx04 u hu
    exact ⟨g, by rw [hg, hmz]⟩
  have hE4 : ∀ E : Subgroup D, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
      Nat.card E ≤ 4 := fun E hEc hE2 => card_le_four_of_sylow T hT8 hsT htT hst E hEc hE2
  have hcent2 := isPGroup_centralizer_mk hZ3 hzz (fun y hyz hyodd =>
    mem_center_of_odd_commute hE4 hs ht hφb hψa hyz hyodd)
  have hTbcent : (Tb : Subgroup (D ⧸ Subgroup.center D)) ≤
      Subgroup.centralizer ({mk z} : Set (D ⧸ Subgroup.center D)) := by
    rw [hTbmap, hTC, Subgroup.map_le_iff_le_comap, hCdef, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← map_mul,
      ← map_mul]
    rcases hg with rfl | rfl
    · exact congrArg mk htz
    · exact congrArg mk hsz
  have hcentEq : Subgroup.centralizer ({mk z} : Set (D ⧸ Subgroup.center D)) =
      (Tb : Subgroup (D ⧸ Subgroup.center D)) := Tb.is_maximal' hcent2 hTbcent
  have hTbcl : (Tb : Subgroup (D ⧸ Subgroup.center D)) = Subgroup.closure {mk t, mk s} := by
    rw [hTbmap, hTC, hCdef, MonoidHom.map_closure, Set.image_pair]
  have hmso : orderOf (mk s) = 2 :=
    orderOf_eq_prime (by rw [pow_two, ← map_mul, hss, map_one]) (hmk_ne_one s hsT hs1)
  have hmto : orderOf (mk t) = 2 :=
    orderOf_eq_prime (by rw [pow_two, ← map_mul, htt, map_one]) (hmk_ne_one t htT ht1)
  have hmst : orderOf (mk s * mk t) = 4 := by rw [← map_mul]; exact hmx04
  obtain ⟨eT⟩ := CFSG.OddStandard.HigherRank.YamadaG23.dihedral_of_involutions' hTbcl hmto hmso
    hmst
  have hcentD8 : CFSG.OddStandard.ONanRec.B2.CentD8 (D ⧸ Subgroup.center D) := by
    intro u hu
    obtain ⟨g, hg⟩ := hconj u hu
    obtain ⟨e1⟩ := nonempty_centralizer_equiv_of_conj hg
    exact ⟨(e1.trans (MulEquiv.subgroupCongr hcentEq)).trans eT⟩
  have hmzo : orderOf (mk z) = 2 :=
    orderOf_eq_prime (by rw [pow_two, ← map_mul, hzz, map_one]) hmz1
  exact CFSG.OddStandard.ONanRec.B2.exists_psl2_of_centD8 hcentD8 ⟨mk z, hmzo⟩

end Main

theorem evenSL3IrredNondeg_small
    {F : Type} [Field F] [Finite F] {e : ℕ} (hF : Nat.card F = 2 ^ e)
    {D : Subgroup (GL (Fin 3) F)} (hDq : IsQuasisimple D)
    (hZ3 : ∀ z ∈ Subgroup.center D, z ^ 3 = 1)
    (hnd : ∃ s t : D, s ^ 2 = 1 ∧ t ^ 2 = 1 ∧ s * t ≠ t * s ∧ Even (orderOf (s * t)))
    (hsmall : ∀ x ∈ D, ∀ y ∈ D, ∀ (a φ : Fin 3 → F) (c : F),
      IsElat x a φ → IsElat y a (c • φ) → x = y) :
    StatedClassicalModel (D ⧸ Subgroup.center D) .PSL 2 3 2 ∨
      ∃ f : ℕ, 1 ≤ f ∧ f ∣ e ∧ (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩;
        IsLThreeEpsAt (D ⧸ Subgroup.center D) 2 f) := by
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨s, t, hs2, ht2, hst, hev⟩ := hnd
  have hss : (s : GL (Fin 3) F) * s = 1 := by
    rw [← Subgroup.coe_mul, ← pow_two, hs2, Subgroup.coe_one]
  have htt : (t : GL (Fin 3) F) * t = 1 := by
    rw [← Subgroup.coe_mul, ← pow_two, ht2, Subgroup.coe_one]
  have hs1 : (s : GL (Fin 3) F) ≠ 1 := by
    intro h
    apply hst
    rw [show s = 1 from Subtype.ext h, one_mul, mul_one]
  have ht1 : (t : GL (Fin 3) F) ≠ 1 := by
    intro h
    apply hst
    rw [show t = 1 from Subtype.ext h, one_mul, mul_one]
  obtain ⟨a, φ, hsE⟩ := CFSG.RankThree.PartTwo.Sec16.KL3SubProof.exists_isElat_of_mul_self hss hs1
  obtain ⟨b, ψ, htE⟩ := CFSG.RankThree.PartTwo.Sec16.KL3SubProof.exists_isElat_of_mul_self htt ht1
  have hstGL : (s : GL (Fin 3) F) * t ≠ t * s := fun h => hst (Subtype.ext (by simpa using h))
  have hevGL : Even (orderOf ((s : GL (Fin 3) F) * t)) := by
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
    exact hev
  have key : ∃ (K' : Type) (_ : Field K') (_ : Finite K'), (Nat.card K' = 7 ∨ Nat.card K' = 9) ∧
      Nonempty (D ⧸ Subgroup.center D ≃* CFSG.GorensteinWalter.PSL2 K') := by
    have hss' : s * s = 1 := by rw [← pow_two]; exact hs2
    have htt' : t * t = 1 := by rw [← pow_two]; exact ht2
    have hcomm2 : ∀ u v : D, u * u = 1 → v * v = 1 → u * v * (u * v) = 1 → u * v = v * u := by
      intro u v hu hv h
      calc u * v = (u * v)⁻¹ := (inv_eq_of_mul_eq_one_right h).symm
        _ = v⁻¹ * u⁻¹ := _root_.mul_inv_rev _ _
        _ = v * u := by rw [inv_eq_of_mul_eq_one_right hv, inv_eq_of_mul_eq_one_right hu]
    rcases special_of_even hsE htE hstGL hevGL with h | h
    · have hψa : ψ ⬝ᵥ a ≠ 0 := by
        intro h'
        apply hst
        refine hcomm2 s t hss' htt' (Subtype.ext ?_)
        simp only [Subgroup.coe_mul, Subgroup.coe_one]
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, Units.val_one, hsE.2.2.2, htE.2.2.2,
          sq_mul_of_dotProduct_eq_zero hsE.2.2.1 htE.2.2.1 h, h', zero_smul, vecMulVec_zero,
          add_zero]
      exact psl2_of_small hDq hZ3 hsmall hsE htE h hψa
    · have hφb : φ ⬝ᵥ b ≠ 0 := by
        intro h'
        apply hst
        refine (hcomm2 t s htt' hss' (Subtype.ext ?_)).symm
        simp only [Subgroup.coe_mul, Subgroup.coe_one]
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, Units.val_one, hsE.2.2.2, htE.2.2.2,
          sq_mul_of_dotProduct_eq_zero htE.2.2.1 hsE.2.2.1 h, h', zero_smul, vecMulVec_zero,
          add_zero]
      exact psl2_of_small hDq hZ3 hsmall htE hsE h hφb
  obtain ⟨K', _, _, hK', ⟨χ⟩⟩ := key
  rcases hK' with h7 | h9
  · right
    refine ⟨1, le_rfl, one_dvd e, Or.inl ?_⟩
    exact CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.nonempty_projSL_three_two_of_psl_two_seven
      ⟨⟨by norm_num, le_rfl, le_rfl, by decide, by decide⟩, K', inferInstance, inferInstance,
        by rw [h7]; norm_num,
        ⟨χ.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K')⟩⟩
  · left
    exact ⟨⟨Nat.prime_three, by norm_num, le_rfl, by decide, by decide⟩, K', inferInstance,
      inferInstance, by rw [h9]; norm_num,
      ⟨χ.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K')⟩⟩

@[expose] def EvenSL3IrredLarge : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (e : ℕ), 1 ≤ e → Nat.card F = 2 ^ e → 2 ^ e % 3 = 1 →
    ∀ D : Subgroup (GL (Fin 3) F), (∀ x ∈ D, (x : Matrix (Fin 3) (Fin 3) F).det = 1) →
      IsQuasisimple D → (∀ z ∈ Subgroup.center D, z ^ 3 = 1) →
      SubgroupLists.IsIrreducibleOn D →
      (∀ M : Matrix (Fin 3) (Fin 3) F, (∀ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) * M = M * g) →
        ∃ c : F, M = Matrix.scalar (Fin 3) c) →
      ¬ SubgroupLists.IsTransitiveMonomial D →
      (∃ s t : D, s ^ 2 = 1 ∧ t ^ 2 = 1 ∧ s * t ≠ t * s ∧ Even (orderOf (s * t))) →
      (∃ x ∈ D, ∃ y ∈ D, ∃ (a φ : Fin 3 → F) (c : F),
        IsElat x a φ ∧ IsElat y a (c • φ) ∧ x ≠ y) →
      StatedClassicalModel (D ⧸ Subgroup.center D) .PSL 2 3 2 ∨
        ∃ f : ℕ, 1 ≤ f ∧ f ∣ e ∧ (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩;
          IsLThreeEpsAt (D ⧸ Subgroup.center D) 2 f)

theorem evenSL3IrredNondeg_of_large
    (hL : EvenSL3IrredLarge) : EvenSL3IrredNondeg := by
  intro F _ _ e he hF hq D hdet hDq hZ3 hirr hcomm hprim hnd
  by_cases hsmall : ∀ x ∈ D, ∀ y ∈ D, ∀ (a φ : Fin 3 → F) (c : F),
      IsElat x a φ → IsElat y a (c • φ) → x = y
  · exact evenSL3IrredNondeg_small hF hDq hZ3 hnd hsmall
  · push Not at hsmall
    obtain ⟨x, hx, y, hy, a, φ, c, hxE, hyE, hxy⟩ := hsmall
    exact hL F e he hF hq D hdet hDq hZ3 hirr hcomm hprim hnd ⟨x, hx, y, hy, a, φ, c, hxE, hyE, hxy⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
