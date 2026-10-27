module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmN
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4K
public import CFSG.Quasithin.Vol2.Ch11SecQ9aShB
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4E

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.ClassicalInvolution.ModelFacts.OddCover
  CFSG.QuasithinUnique.Setup.X6
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.Quasithin.Vol2.KGNat (qSp_mem_Usp nSp_mem_Usp)
open CFSG.Open (pCoreOf)
open scoped commutatorElement

variable {K : Type} [Field K]

theorem blkQ_qSp (x y z : K) (h : qSp x y z ∈ Q2 K 1) : blkQ 1 ⟨qSp x y z, h⟩ = 1 := by
  rw [blkQ_apply]
  change blkIdx (sigma2 1) (mat 2 K (qSp x y z)) = 1
  rw [mat_qSp]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2, qMat]

theorem blkQ_nSp (r : K) (h : nSp r ∈ Q2 K 0) : blkQ 0 ⟨nSp r, h⟩ = 1 := by
  rw [blkQ_apply]
  change blkIdx (sigma2 0) (mat 2 K (lSp K (uGL r))) = 1
  rw [mat_lSp]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2, uGL]

theorem nSp_inj {r r' : K} (h : nSp r = nSp r') : r = r' := by
  have h1 := congrArg (fun g : StatedSp 2 K => mat 2 K g (Sum.inl 0) (Sum.inl 1)) h
  simpa [nSp, mat_lSp, uGL] using h1

theorem eq_zero_of_mul_eq {b c : K} (hb : b ≠ 1) (h : b * c = c) : c = 0 := by
  have h' : (b - 1) * c = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hb
  · exact h1

variable [Finite K] [CharP K 2]

theorem sp4_commutator_ne_bot (hK : Nat.card K = 4) (j : Fin 2) :
    ⁅pCoreOf 2 (perfectCore (Q2 K j)), perfectCore (Q2 K j)⁆ ≠ ⊥ := by
  have hK4 : ∃ s : Finset K, s.card = 4 := exists_finset_card_four hK.ge
  obtain ⟨a, ha⟩ := C11P9A.exists_units_ne_one hK
  have ha3 : a ^ 3 = 1 := C11P9A.pow_three_units hK a
  have ha1 : (a : K) ≠ 1 := fun h => ha (Units.ext h)
  have ha2 : (a : K) ^ 2 ≠ 1 := by
    intro h
    apply ha1
    have h3 : (a : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ha3, Units.val_one]
    calc (a : K) = (a : K) ^ 3 / (a : K) ^ 2 := by field_simp
      _ = 1 := by rw [h3, h, div_one]
  have hai1 : ((a⁻¹ : Kˣ) : K) ≠ 1 := fun h => ha (inv_eq_one.mp (Units.ext h))
  intro h0
  fin_cases j
  ·
    change ⁅pCoreOf 2 (perfectCore (Q2 K 0)), perfectCore (Q2 K 0)⁆ = ⊥ at h0
    have hd : (torusHom ![1, a] : StatedSp 2 K) ∈ perfectCore (Q2 K 0) :=
      (C11P9A.torusHom_mem_N0_iff hK4 _).mpr rfl
    set r : K := ((a⁻¹ : Kˣ) : K) - 1 with hr
    have hv : nSp r ∈ perfectCore (Q2 K 0) := C11P9A.usp_le_perfectCore hK4 (nSp_mem_Usp r)
    have hvO : nSp r ∈ pCoreOf 2 (perfectCore (Q2 K 0)) :=
      (C11P9A.mem_pCoreOf_N_iff hK4 0 hv).mpr (blkQ_nSp r _)
    have hc := Subgroup.commutator_mem_commutator hvO hd
    rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    have hconj : (torusHom ![1, a] : StatedSp 2 K) * nSp r * (torusHom ![1, a])⁻¹ =
        nSp (((a⁻¹ : Kˣ) : K) * r) := by
      rw [← C11P9A.lSp_dGL_one_eq a, lSp_dGL_conj_nSp]
      simp
    have hfix : (torusHom ![1, a] : StatedSp 2 K) * nSp r * (torusHom ![1, a])⁻¹ = nSp r := by
      rw [← hc, mul_inv_cancel_right]
    rw [hconj] at hfix
    have hr0 := eq_zero_of_mul_eq hai1 (nSp_inj hfix)
    exact hai1 (sub_eq_zero.mp hr0)
  ·
    change ⁅pCoreOf 2 (perfectCore (Q2 K 1)), perfectCore (Q2 K 1)⁆ = ⊥ at h0
    have hd : (torusHom ![a, a⁻¹] : StatedSp 2 K) ∈ perfectCore (Q2 K 1) :=
      (C11P9A.torusHom_mem_N1_iff hK4 _).mpr (by simp)
    have hdl : (torusHom ![a, a⁻¹] : StatedSp 2 K) = lSp K (dGL (a, a⁻¹)) :=
      (C11P9A.lSp_dGL_eq (a, a⁻¹)).symm
    have hconj : ∀ x : K, (torusHom ![a, a⁻¹] : StatedSp 2 K) * qSp x 0 0 *
        (torusHom ![a, a⁻¹])⁻¹ = qSp ((a : K) ^ 2 * x) 0 0 := fun x => by
      rw [hdl, lSp_dGL_conj_qSp]
      simp
    have hu : qSp (1 : K) 0 0 ∈ Q2 K 1 := C11P9A.mem_Q2_of_mem_Usp 1 (qSp_mem_Usp 1 0 0)
    set x : K := (a : K) ^ 2 - 1 with hx
    have hve : (torusHom ![a, a⁻¹] : StatedSp 2 K) *
        (qSp (1 : K) 0 0 * (torusHom ![a, a⁻¹])⁻¹ * (qSp (1 : K) 0 0)⁻¹) = qSp x 0 0 := by
      rw [← mul_assoc, ← mul_assoc, hconj, qSp_inv, qSp_mul, mul_one, hx]
      simp [sub_eq_add_neg]
    have hv : qSp x 0 0 ∈ perfectCore (Q2 K 1) := by
      rw [← hve]
      exact mul_mem hd ((Subgroup.mem_normalizer_iff.mp (C11P9A.mem_normalizer_N 1 hu) _).mp
        (inv_mem hd))
    have hvO : qSp x 0 0 ∈ pCoreOf 2 (perfectCore (Q2 K 1)) :=
      (C11P9A.mem_pCoreOf_N_iff hK4 1 hv).mpr (blkQ_qSp x 0 0 _)
    have hc := Subgroup.commutator_mem_commutator hvO hd
    rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    have hfix : (torusHom ![a, a⁻¹] : StatedSp 2 K) * qSp x 0 0 * (torusHom ![a, a⁻¹])⁻¹ =
        qSp x 0 0 := by
      rw [← hc, mul_inv_cancel_right]
    rw [hconj] at hfix
    have hx0 := eq_zero_of_mul_eq ha2 (qSp_injective hfix).1
    exact ha2 (sub_eq_zero.mp hx0)

omit [Field K] [Finite K] [CharP K 2] in
theorem map_map_symm {G H : Type} [Group G] [Group H] (e : G ≃* H) (N : Subgroup G) :
    (N.map e.toMonoidHom).map e.symm.toMonoidHom = N := by
  ext x
  simp

omit [Field K] [Finite K] [CharP K 2] in
theorem parabRadical_sp4 {Q : Type} [Group Q] [Finite Q]
    (hQ : StatedClassicalModel Q .PSp 2 2 2) {S B : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (hB : IsL24Sub S B) : ⁅pCoreOf 2 B, B⁆ ≠ ⊥ := by
  have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp Q 2 2 2 hQ
  obtain ⟨K, _, _, _, φ, hK, -, hres, -⟩ := even_rank_two_residual_symplectic hQ hS
  have hK4' : Nat.card K = 4 := by rw [hK]; norm_num
  have hK4 : ∃ s : Finset K, s.card = 4 := exists_finset_card_four hK4'.ge
  have hpp := C11P9A.parabPair_of_residual hS hres fun j =>
    C11P9A.dInf_projStabilizer_ne_bot hK4 φ j
  have hker : (proj 2 K).ker = ⊥ := by
    rw [ker_proj, CFSG.QuasithinUnique.Vol2Native.A312L.spScalars_eq_bot]
  set ψ : StatedSp 2 K →* Q := φ.symm.toMonoidHom.comp (proj 2 K) with hψ
  have hψi : Function.Injective ψ :=
    φ.symm.injective.comp ((MonoidHom.ker_eq_bot_iff _).mp hker)
  have hψs : Function.Surjective ψ :=
    φ.symm.surjective.comp (proj_surjective (r := 2) (K := K))
  set e : StatedSp 2 K ≃* Q := MulEquiv.ofBijective ψ ⟨hψi, hψs⟩ with he
  have key : ∀ j : Fin 2, ⁅pCoreOf 2 (dInf ((projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map
      φ.symm.toMonoidHom)), dInf ((projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map
        φ.symm.toMonoidHom)⁆ ≠ ⊥ := by
    intro j h0
    have hBe : dInf ((projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map φ.symm.toMonoidHom) =
        (perfectCore (Q2 K j)).map e.toMonoidHom := by
      rw [dInf_eq_perfectCore, projStabilizer, Subgroup.map_map, map_perfectCore]
      rfl
    rw [hBe] at h0
    have h1 := commutator_pCoreOf_map_eq_bot e.symm.toMonoidHom
      (by rw [(MonoidHom.ker_eq_bot_iff _).mpr e.symm.injective, inf_bot_eq]) h0
    rw [map_map_symm] at h1
    exact sp4_commutator_ne_bot hK4' j h1
  rcases hpp.eq_or_eq_of_isL24Sub hB with hj | hj | hj
  · rw [hj]
    exact key 0
  · rw [hj]
    exact key 1
  · exfalso
    have hQc : Nat.card Q = 979200 := by
      rw [← Nat.card_congr e.toEquiv, card_statedSp, hK4']
      decide
    obtain ⟨a, ha⟩ := exists_card_eq_of_SL2 (hj ▸ hB).2.2.2
    rw [Subgroup.card_top, hQc] at ha
    have h2 : 2 ^ a = 16320 := by omega
    have ha' : a < 15 := by
      by_contra hc
      have : 2 ^ 15 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hc)
      omega
    interval_cases a <;> norm_num at h2

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS
