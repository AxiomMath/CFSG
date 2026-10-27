module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSUCore

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.SeitzReduction.F4Pilot (gramSUToSL coe_gramSUToSL gramSUToSL_injective)
open AutPSL (fixVec midIdx)

namespace AutPSU

section Odd

variable {m : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem eq_bot_of_even_form (hm : Even m) (hm2 : 2 ≤ m)
    {S : Subgroup (SpecialLinearGroup (Fin (m + 1)) K)} (hS2 : IsPGroup 2 S)
    (hF1 : ∀ (a : Fin (m + 1)) (ha : a ≠ Fin.rev a), ∀ w ∈ fixVec S,
      ((SpecialLinearGroup.transvection ha (1 : K) : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ w ∈ fixVec S)
    (hF2 : ∀ (a b : Fin (m + 1)) (hba : b ≠ a) (hrab : Fin.rev a ≠ Fin.rev b), a ≠ Fin.rev a →
      b ≠ Fin.rev b → ∀ w ∈ fixVec S, ((SpecialLinearGroup.transvection hba (1 : K) *
        SpecialLinearGroup.transvection hrab (1 : K) : SpecialLinearGroup (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ w ∈ fixVec S)
    (τ : K →+* K)
    (hent : ∀ s ∈ S, ∀ i j, ((s : SpecialLinearGroup (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j =
      τ (((s⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
        (Fin.rev j) (Fin.rev i))) : S = ⊥ := by
  have hrevmid : Fin.rev (midIdx m) = midIdx m := AutPSL.rev_midIdx hm
  have hrev_ne : ∀ i : Fin (m + 1), i ≠ midIdx m → Fin.rev i ≠ midIdx m := fun i hi h =>
    hi (by rw [← Fin.rev_rev i, h, hrevmid])
  obtain ⟨w, -, hw0, hwW⟩ := AutPSL.exists_ne_zero_mem_fixVec hS2 ⊤
    (fun _ _ _ _ => Submodule.mem_top) Submodule.mem_top AutPSL.single_zero_ne_zero
  by_cases h : ∃ w' ∈ fixVec S, ∃ k, k ≠ midIdx m ∧ w' k ≠ 0
  · obtain ⟨w', hw', k, hk, hwk⟩ := h
    have hall : ∀ b, b ≠ midIdx m → Pi.single b (1 : K) ∈ fixVec S := fun b hb =>
      AutPSL.single_mem_of_rev hF1 hF2 hw' (AutPSL.ne_rev_of_ne_mid hm hk) hwk b
        (AutPSL.ne_rev_of_ne_mid hm hb)
    apply AutPSL.eq_bot_of_forall_single_mem
    intro b
    by_cases hb : b = midIdx m
    · subst hb
      intro s hs
      have hoff : ∀ i, i ≠ midIdx m → ((s : SpecialLinearGroup (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) i (midIdx m) = 0 := by
        intro i hi
        rw [hent s hs i (midIdx m), hrevmid, AutPSL.col_eq_of_mulVec_single
          (hall (Fin.rev i) (hrev_ne i hi) _ (S.inv_mem hs)) (midIdx m)]
        simp [Ne.symm (hrev_ne i hi)]
      have hsv : ((s : SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
          *ᵥ Pi.single (midIdx m) 1 = ((s : SpecialLinearGroup (Fin (m + 1)) K) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) K) (midIdx m) (midIdx m) •
              Pi.single (midIdx m) 1 := by
        funext i
        rw [Matrix.mulVec_single_one, Matrix.col_apply]
        by_cases hi : i = midIdx m
        · subst hi
          simp
        · simp [hoff i hi, hi]
      obtain ⟨a, ha⟩ := hS2 ⟨s, hs⟩
      have ha' : s ^ 2 ^ a = 1 := congrArg Subtype.val ha
      have hne : (Pi.single (midIdx m) (1 : K) : Fin (m + 1) → K) ≠ 0 := by
        intro h0
        have := congrFun h0 (midIdx m)
        simp at this
      rw [hsv, AutPSL.eigen_eq_one ha' hne hsv, one_smul]
    · exact hall b hb
  · push Not at h
    exfalso
    have hwm : w (midIdx m) ≠ 0 := by
      intro h0
      apply hw0
      funext l
      by_cases hl : l = midIdx m
      · rw [hl, h0]
        rfl
      · exact h w hwW l hl
    have hemid : Pi.single (midIdx m) (1 : K) ∈ fixVec S := by
      have e : Pi.single (midIdx m) (1 : K) = (w (midIdx m))⁻¹ • w := by
        funext l
        by_cases hl : l = midIdx m
        · subst hl
          simp [inv_mul_cancel₀ hwm]
        · simp [hl, h w hwW l hl]
      rw [e]
      exact Submodule.smul_mem _ _ hwW
    have hrow : ∀ s ∈ S, ∀ j, ((s : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) (midIdx m) j = if j = midIdx m then 1 else 0 := by
      intro s hs j
      rw [hent s hs (midIdx m) j, hrevmid,
        AutPSL.col_eq_of_mulVec_single (hemid _ (S.inv_mem hs))]
      by_cases hj : j = midIdx m
      · simp [hj, hrevmid]
      · simp [hrev_ne j hj, hj]
    set U : Submodule K (Fin (m + 1) → K) := LinearMap.ker (LinearMap.proj (midIdx m))
    have hU : ∀ s ∈ S, ∀ u ∈ U, ((s : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ u ∈ U := by
      intro s hs u hu
      simp only [U, LinearMap.mem_ker, LinearMap.proj_apply] at hu ⊢
      rw [Matrix.mulVec, dotProduct]
      simp [hrow s hs, hu]
    have he0U : Pi.single 0 (1 : K) ∈ U := by
      simp only [U, LinearMap.mem_ker, LinearMap.proj_apply]
      exact Pi.single_eq_of_ne (AutPSL.zero_ne_midIdx hm2).symm 1
    obtain ⟨u, huU, hu0, huW⟩ := AutPSL.exists_ne_zero_mem_fixVec hS2 U hU he0U
      AutPSL.single_zero_ne_zero
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hu0
    have hkm : k ≠ midIdx m := by
      intro hkm
      subst hkm
      apply hk
      simpa [U] using huU
    exact hk (h u huW k hkm)

end Odd

section Main

variable {f m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

theorem o2_eq_bot (hm : 3 ≤ m) {c : MulAut (PJ h (m + 1))} (hc : c ∈ compl h)
    (Q : Subgroup (PJ h (m + 1))) (hQ2 : IsPGroup 2 Q)
    (hnorm : ∀ y : PJ h (m + 1), c y = y → ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) : Q = ⊥ := by
  obtain ⟨S, hS2, hSQ, -, hS⟩ := exists_lift_of_odd
    (normOneScalars_le_center h (XJ h (m + 1)) (m + 1))
    (odd_card_normOneScalars h (XJ h (m + 1))) Q hQ2
  set T := gramSUToSL h ((gramJ (m + 1) : GL (Fin (m + 1)) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K) with hTdef
  set S' := S.map T with hS'def
  have hS'2 : IsPGroup 2 S' := hS2.map T
  have hinv : ∀ y : XJ h (m + 1), c (y : PJ h (m + 1)) = y → ∀ w ∈ fixVec S',
      ((T y : SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ w ∈
        fixVec S' := by
    intro y hy w hw
    refine AutPSL.mulVec_mem_fixVec (fun s' hs' => ?_) hw
    obtain ⟨s, hs, rfl⟩ := hs'
    have hy' : c ((y⁻¹ : XJ h (m + 1)) : PJ h (m + 1)) = ((y⁻¹ : XJ h (m + 1)) : PJ h (m + 1)) := by
      rw [QuotientGroup.mk_inv, map_inv, hy]
    have hconj := conj_mem_lift_of hS2 hSQ hS (y := y⁻¹) (fun q hq => hnorm _ hy' q hq) hs
    rw [inv_inv] at hconj
    exact ⟨_, hconj, by rw [map_mul, map_mul, map_inv]⟩
  have hF1 : ∀ (a : Fin (m + 1)) (ha : a ≠ Fin.rev a), ∀ w ∈ fixVec S',
      ((SpecialLinearGroup.transvection ha (1 : K) : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ w ∈ fixVec S' := by
    intro a ha
    rw [← gramSUToSL_lroot h ha]
    exact hinv _ (compl_fixes_lroot h hc ha)
  have hF2 : ∀ (a b : Fin (m + 1)) (hba : b ≠ a) (hrab : Fin.rev a ≠ Fin.rev b),
      a ≠ Fin.rev a → b ≠ Fin.rev b → ∀ w ∈ fixVec S',
        ((SpecialLinearGroup.transvection hba (1 : K) * SpecialLinearGroup.transvection hrab
          (1 : K) : SpecialLinearGroup (Fin (m + 1)) K) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ w ∈ fixVec S' := by
    intro a b hba hrab ha hb
    rw [← gramSUToSL_sroot h hba hrab ha hb]
    exact hinv _ (compl_fixes_sroot h hc hba hb ha)
  have hent : ∀ s' ∈ S', ∀ i j, ((s' : SpecialLinearGroup (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j =
      h.bar (((s'⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.rev j) (Fin.rev i)) := by
    rintro _ ⟨s, -, rfl⟩ i j
    rw [← map_inv]
    exact entry_eq_bar_inv h s.2 i j
  have hS'bot : S' = ⊥ := by
    rcases Nat.even_or_odd m with hme | hmo
    · exact eq_bot_of_even_form hme (by omega) hS'2 hF1 hF2 h.bar hent
    · exact AutPSL.eq_bot_of_odd hmo hS'2 hF1 hF2
  have hSbot : S = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    have hTs : T s ∈ S' := ⟨s, hs, rfl⟩
    rw [hS'bot, Subgroup.mem_bot] at hTs
    rw [Subgroup.mem_bot]
    exact gramSUToSL_injective h _ (by rw [← hTdef, hTs, map_one])
  rw [← hSQ, hSbot, Subgroup.map_bot]

theorem goodAut_compl (hm : 3 ≤ m) {c : MulAut (PJ h (m + 1))} (hc : c ∈ compl h)
    {e : MulAut (PJ h (m + 1))} (he : e ∈ inndiag h) :
    GGGoodAut (projU h (rootU m)) (e * c * e⁻¹) :=
  goodAut_of_core h hm hc (fun Q _ hQ2 hnorm => o2_eq_bot h hm hc Q hQ2 hnorm) he

end Main

end AutPSU

end CFSG.StandardType
