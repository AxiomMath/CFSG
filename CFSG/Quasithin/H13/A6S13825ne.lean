module

public import CFSG.Quasithin.H13.A6S13825nd
public import CFSG.Quasithin.H13.A6S13825f

public section

namespace CFSG.Quasithin.H13.A6.L4Tw

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open L4Ind

section Orbit

variable {M : Type*} [CommGroup M] {Φ : MulAut SL4 →* MulAut M} {m₀ : M}

theorem mu_mul_of_mem (hU : ∀ u ∈ unitriangular 4 (ZMod 2), Φ (MulAut.conj u) m₀ = m₀)
    (g u : SL4) (hu : u ∈ unitriangular 4 (ZMod 2)) :
    Φ (MulAut.conj (g * u)) m₀ = Φ (MulAut.conj g) m₀ := by
  rw [map_mul, map_mul, MulAut.mul_apply, hU u hu]

theorem mu_Q13 (hU : ∀ u ∈ unitriangular 4 (ZMod 2), Φ (MulAut.conj u) m₀ = m₀) {g : SL4}
    (hg : g ∈ Q13) :
    Φ (MulAut.conj g) m₀ = m₀ ∨ Φ (MulAut.conj g) m₀ = Φ (MulAut.conj q1) m₀ ∨
      Φ (MulAut.conj g) m₀ = Φ (MulAut.conj q2) m₀ := by
  rcases tri hg with h | h | h
  · exact Or.inl (hU g h)
  · refine Or.inr (Or.inl ?_)
    rw [show g = q1 * (q1⁻¹ * g) by group]
    exact mu_mul_of_mem hU _ _ h
  · refine Or.inr (Or.inr ?_)
    rw [show g = q2 * (q2⁻¹ * g) by group]
    exact mu_mul_of_mem hU _ _ h

theorem rel_of (hsq : ∀ x : M, x * x = 1)
    (hU : ∀ u ∈ unitriangular 4 (ZMod 2), Φ (MulAut.conj u) m₀ = m₀) {c : SL4} (hc : c ∈ Q13)
    (h1 : Φ (MulAut.conj c) m₀ ≠ m₀) (h2 : Φ (MulAut.conj (c * c)) m₀ ≠ m₀)
    (h12 : Φ (MulAut.conj c) m₀ ≠ Φ (MulAut.conj (c * c)) m₀)
    (hcc : m₀ * Φ (MulAut.conj c) m₀ = Φ (MulAut.conj (c * c)) m₀) :
    m₀ * Φ (MulAut.conj q1) m₀ * Φ (MulAut.conj q2) m₀ = 1 ∧ Φ (MulAut.conj q1) m₀ ≠ m₀ := by
  have hrel : m₀ * Φ (MulAut.conj c) m₀ * Φ (MulAut.conj (c * c)) m₀ = 1 := by
    rw [hcc, hsq]
  have hcc2 := Q13.mul_mem hc hc
  rcases mu_Q13 hU hc with ha | ha | ha
  · exact absurd ha h1
  · rcases mu_Q13 hU hcc2 with hb | hb | hb
    · exact absurd hb h2
    · exact absurd (ha.trans hb.symm) h12
    · refine ⟨?_, ha ▸ h1⟩
      rw [← ha, ← hb, hrel]
  · rcases mu_Q13 hU hcc2 with hb | hb | hb
    · exact absurd hb h2
    · refine ⟨?_, hb ▸ h2⟩
      rw [← ha, ← hb, mul_assoc, mul_comm (Φ (MulAut.conj (c * c)) m₀), ← mul_assoc, hrel]
    · exact absurd (ha.trans hb.symm) h12

end Orbit

theorem tauW_eq_revGraph : tauW = L13825.revGraph 4 := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  ext i j
  rw [tauW_matrix, w0_entry, L13825.revGraph_apply]

section Fix

variable {M : Type*} [CommGroup M] {Φ : MulAut SL4 →* MulAut M} {m₀ : M}

theorem Q2_fix (hU : ∀ u ∈ unitriangular 4 (ZMod 2), Φ (MulAut.conj u) m₀ = m₀)
    (hτ : Φ tauW m₀ = m₀) {A : SL4} (hA : A ∉ unitriangular 4 (ZMod 2))
    (hAf : Φ (MulAut.conj A) m₀ = m₀) (hq1 : Φ (MulAut.conj q1) m₀ ≠ m₀) {g : SL4}
    (hg : InQ2 (g : M4)) : Φ (MulAut.conj g) m₀ = m₀ := by
  set F : Subgroup SL4 := (IndQuad.fixer Φ m₀).comap MulAut.conj with hF
  have hmemF : ∀ x : SL4, x ∈ F ↔ Φ (MulAut.conj x) m₀ = m₀ := fun x => Iff.rfl
  have hUF : upperTriangular 4 (ZMod 2) ≤ F := by
    rw [CFSG.Quasithin.SBd8.Flag.upperTriangular_eq_unitriangular (Nat.card_zmod 2)]
    exact fun u hu => (hmemF u).2 (hU u hu)
  obtain ⟨hFC, hC⟩ := CFSG.Quasithin.SBd8.Flag.eq_flagStabilizer_borelOvergroupCuts hUF
  set C := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.borelOvergroupCuts F with hCdef
  have hτF : ∀ x ∈ F, tauW x ∈ F := by
    intro x hx
    rw [hmemF] at hx ⊢
    have e : MulAut.conj (tauW x) = tauW * MulAut.conj x * tauW := by
      rw [tauW_mul_conj, mul_assoc, tauW_mul_self, mul_one]
    rw [e, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hτ, hx, hτ]
  have hmap : F.map tauW.toMonoidHom = F := by
    refine le_antisymm ?_ fun x hx => ⟨tauW x, hτF x hx, tauW_tauW x⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hτF x hx
  have hrev : L13825.revCuts 4 C = C := by
    have h := hmap
    rw [hFC, tauW_eq_revGraph, L13825.map_revGraph_flagStabilizer hC] at h
    exact CFSG.Quasithin.SBd8.Flag.flagStabilizer_injOn (L13825.isCuts_revCuts hC) hC h
  have hfull : ¬ L13825.fullCuts 4 ⊆ C := by
    intro h
    apply hA
    rw [← L13825.flagStabilizer_fullCuts]
    have hle : flagStabilizer 4 (ZMod 2) C ≤ flagStabilizer 4 (ZMod 2) (L13825.fullCuts 4) :=
      (CFSG.Quasithin.SBd8.Flag.flagStabilizer_le_iff hC fun i hi => ⟨hi.1, hi.2⟩).2 h
    exact hle (hFC ▸ (hmemF A).2 hAf)
  have hmin : ¬ C ⊆ L13825.minPar 4 2 := by
    intro h
    apply hq1
    have hle : Q13 ≤ flagStabilizer 4 (ZMod 2) C :=
      (CFSG.Quasithin.SBd8.Flag.flagStabilizer_le_iff (fun i hi => ⟨hi.1, hi.2.1⟩) hC).2 h
    have := hle q1_mem
    rw [← hFC] at this
    exact this
  have h2 : 2 ∈ C := by
    by_contra h2
    apply hmin
    intro i hi
    obtain ⟨hi1, hi4⟩ := hC i hi
    refine ⟨hi1, hi4, fun h => h2 (h ▸ hi)⟩
  have hiff : ∀ i, i ∈ C ↔ i ≤ 4 ∧ 4 - i ∈ C := fun i => by
    conv_lhs => rw [← hrev]
    rfl
  have h1 : 1 ∉ C := by
    intro h1
    have h3 : 3 ∈ C := (hiff 3).2 ⟨by norm_num, h1⟩
    apply hfull
    intro i hi
    obtain ⟨hi1, hi4⟩ := hi
    interval_cases i
    · exact h1
    · exact h2
    · exact h3
  have h3 : 3 ∉ C := fun h3 => h1 ((hiff 1).2 ⟨by norm_num, h3⟩)
  have hC2 : C = {2} := by
    ext i
    rw [Set.mem_singleton_iff]
    constructor
    · intro hi
      obtain ⟨hi1, hi4⟩ := hC i hi
      interval_cases i
      · exact absurd hi h1
      · rfl
      · exact absurd hi h3
    · rintro rfl
      exact h2
  have hgF : g ∈ F := by
    rw [hFC, hC2]
    exact (mem_flag_iff g).2 hg
  exact hgF

end Fix

abbrev midB (m : M4) : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![m 1 1, m 1 2; m 2 1, m 2 2]

abbrev liftM (C : Matrix (Fin 2) (Fin 2) (ZMod 2)) : M4 :=
  !![1, 0, 0, 0; 0, C 0 0, C 0 1, 0; 0, C 1 0, C 1 1, 0; 0, 0, 0, 1]

theorem liftM_mul : ∀ C C' : Matrix (Fin 2) (Fin 2) (ZMod 2),
    liftM C * liftM C' = liftM (C * C') := by
  decide

theorem liftM_one : liftM 1 = 1 := by
  decide

theorem midB_liftM (C : Matrix (Fin 2) (Fin 2) (ZMod 2)) : midB (liftM C) = C := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem midB_one : midB (1 : M4) = 1 := by
  decide

theorem midB_mul {m m' : M4} (h10 : m 1 0 = 0) (h20 : m 2 0 = 0) (h31 : m' 3 1 = 0)
    (h32 : m' 3 2 = 0) : midB (m * m') = midB m * midB m' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, h10, h20, h31, h32]

theorem midB_mul_Q13 {g g' : SL4} (hg : g ∈ Q13) (hg' : g' ∈ Q13) :
    midB ((g * g' : SL4) : M4) = midB (g : M4) * midB (g' : M4) := by
  obtain ⟨a, b, -, -, -⟩ := entries_of_mem_Q13 hg
  obtain ⟨-, -, -, c, d⟩ := entries_of_mem_Q13 hg'
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact midB_mul a b c d

theorem midB_pow {g : SL4} (hg : g ∈ Q13) :
    ∀ n : ℕ, midB ((g ^ n : SL4) : M4) = midB (g : M4) ^ n
  | 0 => by rw [pow_zero, pow_zero, Matrix.SpecialLinearGroup.coe_one, midB_one]
  | n + 1 => by
    rw [pow_succ, midB_mul_Q13 (Q13.pow_mem hg n) hg, midB_pow hg n, pow_succ]

theorem midB_inv {g : SL4} (hg : g ∈ Q13) :
    midB (g : M4) * midB ((g⁻¹ : SL4) : M4) = 1 := by
  rw [← midB_mul_Q13 hg (Q13.inv_mem hg), mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    midB_one]

theorem gl2_tau : ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 2), A * B = 1 →
    !![B 1 1, B 0 1; B 1 0, B 0 0] = A := by
  decide

theorem tauW_mem_Q13 {g : SL4} (hg : g ∈ Q13) : tauW g ∈ Q13 := by
  have h := L13825.map_revGraph_flagStabilizer (L13825.isCuts_minPar 4 2)
  rw [L13825.revCuts_minPar (by norm_num : 2 < 4), ← tauW_eq_revGraph] at h
  rw [Q13, ← h]
  exact ⟨g, hg, rfl⟩

theorem midB_w0 (m : M4) : midB (w0M * mᵀ * w0M) = !![m 2 2, m 1 2; m 2 1, m 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact w0_entry m 1 1
  · exact w0_entry m 1 2
  · exact w0_entry m 2 1
  · exact w0_entry m 2 2

theorem midB_tauW {g : SL4} (hg : g ∈ Q13) : midB ((tauW g : SL4) : M4) = midB (g : M4) := by
  rw [tauW_matrix, midB_w0]
  exact gl2_tau _ _ (midB_inv hg)

theorem midB_cond {g : SL4} (hg : g ∈ Q13) (ε : Bool) :
    cond ε (tauW g) g ∈ Q13 ∧ midB ((cond ε (tauW g) g : SL4) : M4) = midB (g : M4) := by
  cases ε
  · exact ⟨hg, rfl⟩
  · exact ⟨tauW_mem_Q13 hg, midB_tauW hg⟩

theorem eq_uSL_of_midB {g : SL4} (hg : g ∈ Q13) (hm : midB (g : M4) = 1) :
    g = uSL ((g : M4) 0 1) ((g : M4) 0 2) ((g : M4) 0 3) ((g : M4) 1 3) ((g : M4) 2 3) := by
  obtain ⟨h10, h20, h30, h31, h32⟩ := entries_of_mem_Q13 hg
  obtain ⟨i10, i20, i30, i31, i32⟩ := entries_of_mem_Q13 (Q13.inv_mem hg)
  have h11 : (g : M4) 1 1 = 1 := congrFun (congrFun hm 0) 0
  have h12 : (g : M4) 1 2 = 0 := congrFun (congrFun hm 0) 1
  have h21 : (g : M4) 2 1 = 0 := congrFun (congrFun hm 1) 0
  have h22 : (g : M4) 2 2 = 1 := congrFun (congrFun hm 1) 1
  have h00 : (g : M4) 0 0 = 1 := by
    have e := congrFun (congrFun (congrArg Subtype.val (mul_inv_cancel g)) 0) 0
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Matrix.mul_apply, Fin.sum_univ_four, i10, i20, i30, mul_zero, add_zero] at e
    exact L4Ind.zmod2_eq_one_of_mul _ _ e
  have h33 : (g : M4) 3 3 = 1 := by
    have e := congrFun (congrFun (congrArg Subtype.val (inv_mul_cancel g)) 3) 3
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Matrix.mul_apply, Fin.sum_univ_four, i30, i31, i32, zero_mul, zero_add] at e
    exact L4Ind.zmod2_eq_one_of_mul _ _ (by rw [mul_comm]; exact e)
  apply Subtype.ext
  rw [coe_uSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h20, h30, h31, h32, h11, h12, h21, h22, h00, h33]

theorem U_le_Q13 : unitriangular 4 (ZMod 2) ≤ Q13 := flag_inf_Q13 ▸ inf_le_right

@[expose] def Ptau : Subgroup (MulAut SL4) where
  carrier := {x | ∃ q ∈ Q13, ∃ ε, x = nf q ε}
  mul_mem' := by
    rintro _ _ ⟨q, hq, ε, rfl⟩ ⟨q', hq', ε', rfl⟩
    exact ⟨_, Q13.mul_mem hq (midB_cond hq' ε).1, _, nf_mul q q' ε ε'⟩
  one_mem' := ⟨1, Q13.one_mem, false, by rw [nf_false, map_one]⟩
  inv_mem' := by
    rintro _ ⟨q, hq, ε, rfl⟩
    refine ⟨cond ε (tauW q⁻¹) q⁻¹, (midB_cond (Q13.inv_mem hq) ε).1, ε, ?_⟩
    refine inv_eq_of_mul_eq_one_right ?_
    rw [nf_mul, Bool.xor_self, nf_false]
    cases ε
    · rw [Bool.cond_false, Bool.cond_false, mul_inv_cancel, map_one]
    · rw [Bool.cond_true, Bool.cond_true, tauW_tauW, mul_inv_cancel, map_one]

theorem mem_enc_of_normal {N : Subgroup (MulAut SL4)}
    (hNP : ∀ x ∈ N, ∃ q ∈ Q13, ∃ ε, x = nf q ε)
    (hnorm : ∀ q ∈ Q13, ∀ x ∈ N, MulAut.conj q * x * (MulAut.conj q)⁻¹ ∈ N)
    (h2 : IsPGroup 2 ↥N) {x : MulAut SL4} (hx : x ∈ N) : ∃ o, x = enc o := by
  have hinner : ∀ p ∈ Q13, MulAut.conj p ∈ N → ∃ k : ℕ, midB (p : M4) ^ 2 ^ k = 1 := by
    intro p hp hpN
    obtain ⟨k, hk⟩ := h2 ⟨_, hpN⟩
    have hk' : MulAut.conj p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    have : p ^ 2 ^ k = 1 := conj_injective (by rw [map_pow, hk', map_one])
    rw [← midB_pow hp, this, Matrix.SpecialLinearGroup.coe_one, midB_one]
  obtain ⟨q, hq, ε, rfl⟩ := hNP _ hx
  obtain ⟨hq', hmq'⟩ := midB_cond hq ε
  have hmid : midB (q : M4) = 1 := by
    by_contra hne
    have hx2 : nf q ε * nf q ε = MulAut.conj (q * cond ε (tauW q) q) := by
      rw [nf_mul, Bool.xor_self, nf_false]
    obtain ⟨k, hk⟩ := hinner _ (Q13.mul_mem hq hq') (hx2 ▸ N.mul_mem hx hx)
    rw [midB_mul_Q13 hq hq', hmq', ← pow_two, ← pow_mul, ← pow_succ'] at hk
    have hA2 := L4Ind.sq_eq_one_of (L4Ind.exp6 (midB_inv hq)) hk
    obtain ⟨pr, -, hpr, hZ3, hZ1⟩ := L4Ind.condC_of (midB_inv hq) hne hA2
    set q₀ : SL4 := L4Ind.mkSL (liftM pr.1) (liftM pr.2) (by rw [liftM_mul, hpr, liftM_one])
      with hq₀def
    have hq₀ : q₀ ∈ Q13 := by
      refine CFSG.QuasithinUnique.Vol2Native.A312L.mem_flagStabilizer_of_entries ?_
      intro k l c hc hl hk
      obtain ⟨hc1, hc4, hc2⟩ := hc
      rw [hq₀def, L4Ind.coe_mkSL]
      fin_cases k <;> fin_cases l <;> simp at hl hk ⊢ <;> omega
    have hq₀i : ((q₀⁻¹ : SL4) : M4) = liftM pr.2 := L4Ind.coe_mkSL_inv _ _ _
    obtain ⟨hc₀, hmc₀⟩ := midB_cond (Q13.inv_mem hq₀) ε
    set p := q₀ * q * cond ε (tauW q₀⁻¹) q₀⁻¹ * cond ε (tauW q) q with hp
    have hz : MulAut.conj q₀ * nf q ε * (MulAut.conj q₀)⁻¹ * nf q ε = MulAut.conj p := by
      rw [conj_nf, nf_mul, Bool.xor_self, nf_false]
    have hpQ : p ∈ Q13 := Q13.mul_mem (Q13.mul_mem (Q13.mul_mem hq₀ hq) hc₀) hq'
    obtain ⟨j, hj⟩ := hinner p hpQ (hz ▸ N.mul_mem (hnorm q₀ hq₀ _ hx) hx)
    have hmp : midB (p : M4) = pr.1 * midB (q : M4) * pr.2 * midB (q : M4) := by
      rw [hp, midB_mul_Q13 (Q13.mul_mem (Q13.mul_mem hq₀ hq) hc₀) hq',
        midB_mul_Q13 (Q13.mul_mem hq₀ hq) hc₀, midB_mul_Q13 hq₀ hq, hmc₀, hmq', hq₀i,
        L4Ind.coe_mkSL, midB_liftM, midB_liftM]
    rw [hmp] at hj
    exact hZ1 (L4Ind.eq_one_of_three hZ3 hj)
  exact ⟨⟨_, _, _, _, _, ε⟩, by rw [enc, ← eq_uSL_of_midB hq hmid]⟩

end CFSG.Quasithin.H13.A6.L4Tw
