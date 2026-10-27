module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadFix
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadTrans
import CFSG.LinearAlgebra.RootGroupSL.NormalizerYWAux

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LinearGroups (stdHermForm)
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f ε : ℕ}
  {b : StatedSU (2 * 2 + ε) (2 ^ f) K} {ω : K}

omit [Finite K] in
theorem RadSetup.stabSU_ne_top (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K) :
    stabSU (2 ^ f) (eigSU b ω) ≠ ⊤ := by
  have hne : eigSU b ω⁻¹ ≠ ⊥ := by
    intro hbot
    have h2 := hS.finrank_eig_inv
    rw [hbot, finrank_bot] at h2
    omega
  obtain ⟨a, haW', ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have haa : stdHermForm h (2 * 2 + ε) a a = 0 := hS.symm.isotropic h a haW' a haW'
  have hex : ∃ w ∈ eigSU b ω, stdHermForm h (2 * 2 + ε) w a ≠ 0 := by
    by_contra hcon
    have hzero : ∀ w ∈ eigSU b ω, stdHermForm h (2 * 2 + ε) w a = 0 := by
      intro w hw
      by_contra hne'
      exact hcon ⟨w, hw, hne'⟩
    exact ha0 (hS.eq_zero_of_orth h haW' hzero)
  obtain ⟨w, hwW, hwa⟩ := hex
  have haw : stdHermForm h (2 * 2 + ε) a w ≠ 0 := fun h0 =>
    hwa (by
      have hbar := (CFSG.LinearGroups.stdHermForm_isSymm h (2 * 2 + ε)).eq a w
      simpa [h0] using hbar.symm)
  obtain ⟨t, ht⟩ := exists_transvection (n := 2 * 2 + ε) h haa
  have hnot : t ∉ stabSU (2 ^ f) (eigSU b ω) := by
    intro htmem
    have htw : ((t : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ w ∈ eigSU b ω :=
      (mem_stabSU.mp htmem) w hwW
    have hmemW : stdHermForm h (2 * 2 + ε) a w • a ∈ eigSU b ω := by
      have hsub := Submodule.sub_mem _ htw hwW
      rwa [ht w, add_sub_cancel_left] at hsub
    have hmemW' : stdHermForm h (2 * 2 + ε) a w • a ∈ eigSU b ω⁻¹ :=
      Submodule.smul_mem _ _ haW'
    have hbot : stdHermForm h (2 * 2 + ε) a w • a = 0 := by
      have hinf := Submodule.mem_inf.mpr ⟨hmemW, hmemW'⟩
      rw [hS.inf_eq_bot] at hinf
      simpa using hinf
    exact haw ((smul_eq_zero.mp hbot).resolve_right ha0)
  intro htop
  exact hnot (by rw [htop]; exact Subgroup.mem_top t)

omit [Finite K] [CharP K 2] in
theorem RadSetup.pCoreOf_ne_bot (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K) :
    pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω)) ≠ ⊥ := by
  have hne : eigSU b ω ≠ ⊥ := by
    intro hbot
    have h2 := hS.finrank_eig
    rw [hbot, finrank_bot] at h2
    omega
  obtain ⟨a, haW, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have haa : stdHermForm h (2 * 2 + ε) a a = 0 := hS.isotropic h a haW a haW
  obtain ⟨t, htP, ht⟩ :=
    exists_transvection_mem_pCoreOf (n := 2 * 2 + ε) h (hS.isotropic h) haW
  have ht_ne : t ≠ 1 := by
    intro ht1
    have hzero : ∀ x : Fin (2 * 2 + ε) → K, stdHermForm h (2 * 2 + ε) a x = 0 := by
      intro x
      have hx : x = x + stdHermForm h (2 * 2 + ε) a x • a := by
        have h := ht x
        simpa [ht1] using h
      have hxa : stdHermForm h (2 * 2 + ε) a x • a = 0 :=
        add_left_cancel (hx.symm.trans (add_zero x).symm)
      exact (smul_eq_zero.mp hxa).resolve_right ha0
    exact ha0 (CFSG.LinearGroups.stdHermForm_separatingLeft h (2 * 2 + ε) a hzero)
  intro hbot
  apply ht_ne
  have htbot : t ∈ (⊥ : Subgroup (StatedSU (2 * 2 + ε) (2 ^ f) K)) := by
    rwa [hbot] at htP
  simpa using htbot

private theorem pCoreOf_inf_stabSU_fixes_eig_inv (hS : RadSetup ε b ω)
    (h : UnitaryFieldData 2 f K) (hK₀ : F08.KOf8103 ⊤ (zpowers b) ≠ ⊥)
    {y : StatedSU (2 * 2 + ε) (2 ^ f) K}
    (hy : y ∈ pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω)) ⊓
      stabSU (2 ^ f) (eigSU b ω⁻¹)) :
    ∀ w' ∈ eigSU b ω⁻¹,
      ((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ w' = w' := by
  intro w' hw'
  have hfixW : ∀ w ∈ eigSU b ω,
      ((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ w = w :=
    fun w hw => hS.pCoreOf_fix h hK₀ hy.1 hw
  have hyw' : ((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ w' ∈ eigSU b ω⁻¹ :=
    (mem_stabSU.mp hy.2) w' hw'
  have hu : ((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ w' - w' ∈
      eigSU b ω⁻¹ :=
    Submodule.sub_mem _ hyw' hw'
  have horth : ∀ w ∈ eigSU b ω,
      stdHermForm h (2 * 2 + ε) w
        (((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ w' - w') = 0 := by
    intro w hw
    rw [map_sub]
    have h1 : stdHermForm h (2 * 2 + ε) w
        (((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ w') =
        stdHermForm h (2 * 2 + ε) w w' := by
      calc
        stdHermForm h (2 * 2 + ε) w
            (((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ w') =
            stdHermForm h (2 * 2 + ε)
              (((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ w)
              (((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ w') := by
          rw [hfixW w hw]
        _ = stdHermForm h (2 * 2 + ε) w w' :=
          ((CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff_isometry h).mp y.2).2 w w'
    rw [h1, sub_self]
  exact sub_eq_zero.mp (hS.eq_zero_of_orth h hu horth)

private theorem pCoreOf_inf_stabSU_maps_eig_one (hS : RadSetup ε b ω)
    (h : UnitaryFieldData 2 f K) (hK₀ : F08.KOf8103 ⊤ (zpowers b) ≠ ⊥)
    {y : StatedSU (2 * 2 + ε) (2 ^ f) K}
    (hy : y ∈ pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω)) ⊓
      stabSU (2 ^ f) (eigSU b ω⁻¹)) :
    ∀ v ∈ eigSU b 1,
      ((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ v ∈ eigSU b 1 := by
  intro v hv
  have hfixW : ∀ w ∈ eigSU b ω,
      ((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ w = w :=
    fun w hw => hS.pCoreOf_fix h hK₀ hy.1 hw
  have hfixW' := pCoreOf_inf_stabSU_fixes_eig_inv hS h hK₀ hy
  have hiso : ∀ x z : Fin (2 * 2 + ε) → K,
      stdHermForm h (2 * 2 + ε)
        (((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ x)
        (((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ z) =
        stdHermForm h (2 * 2 + ε) x z :=
    ((CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff_isometry h).mp y.2).2
  refine hS.mem_one_of_orth h ?_ ?_
  · intro w hw
    have h1 : stdHermForm h (2 * 2 + ε) w
        (((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ v) =
        stdHermForm h (2 * 2 + ε)
          (((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ w)
          (((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ v) := by
      rw [hfixW w hw]
    rw [h1, hiso w v]
    exact (hS.orth_one h v hv w hw).2
  · intro w hw
    have h1 : stdHermForm h (2 * 2 + ε) w
        (((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ v) =
        stdHermForm h (2 * 2 + ε)
          (((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ w)
          (((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ v) := by
      rw [hfixW' w hw]
    rw [h1, hiso w v]
    exact (hS.symm.orth_one h v hv w hw).2

private theorem pCoreOf_inf_stabSU_fixes_generator (hS : RadSetup ε b ω)
    (h : UnitaryFieldData 2 f K) (hK₀ : F08.KOf8103 ⊤ (zpowers b) ≠ ⊥)
    {y : StatedSU (2 * 2 + ε) (2 ^ f) K}
    (hy : y ∈ pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω)) ⊓
      stabSU (2 ^ f) (eigSU b ω⁻¹))
    {v₀ : Fin (2 * 2 + ε) → K} (hv₀mem : v₀ ∈ eigSU b 1) (hv₀ne : v₀ ≠ 0)
    (hgen : ∀ w ∈ eigSU b 1, ∃ c : K, c • v₀ = w) :
    ((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ v₀ = v₀ := by
  have hmapv₀ := pCoreOf_inf_stabSU_maps_eig_one hS h hK₀ hy v₀ hv₀mem
  obtain ⟨lam, hlam⟩ := hgen (((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ v₀) hmapv₀
  have hgroup : IsPGroup 2 ↥(pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω))) :=
    (CFSG.pCore_isPGroup (p := 2)
      (G := ↥(stabSU (2 ^ f) (eigSU b ω)))).map
      (stabSU (2 ^ f) (eigSU b ω)).subtype
  obtain ⟨k, hk⟩ := hgroup ⟨y, hy.1⟩
  have hk' : y ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have hpow : ∀ m : ℕ,
      (((y ^ m : StatedSU (2 * 2 + ε) (2 ^ f) K) :
          GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ v₀ = lam ^ m • v₀ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← hlam,
        Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  have hpowk := hpow (2 ^ k)
  rw [hk', Subgroup.coe_one, Units.val_one, Matrix.one_mulVec] at hpowk
  have h1 : lam ^ 2 ^ k = 1 := by
    have h3 : (lam ^ 2 ^ k - 1) • v₀ = 0 := by
      calc
        (lam ^ 2 ^ k - 1) • v₀ = lam ^ 2 ^ k • v₀ - 1 • v₀ := sub_smul ..
        _ = v₀ - v₀ := by rw [← hpowk, one_smul]
        _ = 0 := sub_self v₀
    exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hv₀ne)
  have hlam1 : lam = 1 :=
    CFSG.LinearAlgebra.RootGroupSL.NormalizerYWAux.eq_one_of_pow_two_pow_eq_one h1
  rw [← hlam, hlam1, one_smul]

private theorem pCoreOf_inf_stabSU_fixes_eig_one (hS : RadSetup ε b ω)
    (h : UnitaryFieldData 2 f K) (hK₀ : F08.KOf8103 ⊤ (zpowers b) ≠ ⊥)
    {y : StatedSU (2 * 2 + ε) (2 ^ f) K}
    (hy : y ∈ pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω)) ⊓
      stabSU (2 ^ f) (eigSU b ω⁻¹)) :
    ∀ v ∈ eigSU b 1,
      ((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ v = v := by
  obtain ⟨v₀, hgen₀⟩ :=
    (finrank_le_one_iff (K := K) (V := eigSU b 1)).1 hS.finrank_eig_one_le
  by_cases hv₀ : v₀ = 0
  · intro v hv
    obtain ⟨c, hc⟩ := hgen₀ ⟨v, hv⟩
    have hv0 : v = 0 := by
      have h := congrArg Subtype.val hc
      simpa [hv₀] using h.symm
    subst v
    simp
  · have hv₀mem : (v₀ : Fin (2 * 2 + ε) → K) ∈ eigSU b 1 := v₀.2
    have hv₀ne : (v₀ : Fin (2 * 2 + ε) → K) ≠ 0 := fun h => hv₀ (Subtype.ext h)
    have hgen : ∀ w ∈ eigSU b 1, ∃ c : K, c • (v₀ : Fin (2 * 2 + ε) → K) = w := by
      intro w hw
      obtain ⟨c, hc⟩ := hgen₀ ⟨w, hw⟩
      exact ⟨c, by simpa using congrArg Subtype.val hc⟩
    have hfix₀ :=
      pCoreOf_inf_stabSU_fixes_generator hS h hK₀ hy hv₀mem hv₀ne hgen
    intro v hv
    obtain ⟨c, hc⟩ := hgen v hv
    rw [← hc, Matrix.mulVec_smul, hfix₀]

theorem RadSetup.pCoreOf_inf_stabSU_eq_bot (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K)
    (hK₀ : F08.KOf8103 ⊤ (zpowers b) ≠ ⊥) :
    pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω)) ⊓ stabSU (2 ^ f) (eigSU b ω⁻¹) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hfixW : ∀ w ∈ eigSU b ω,
      ((y : GL (Fin (2 * 2 + ε)) K) : Matrix _ _ K) *ᵥ w = w :=
    fun w hw => hS.pCoreOf_fix h hK₀ hy.1 hw
  have hfixW' := pCoreOf_inf_stabSU_fixes_eig_inv hS h hK₀ hy
  have hfixV := pCoreOf_inf_stabSU_fixes_eig_one hS h hK₀ hy
  have hfixall : ∀ x : Fin (2 * 2 + ε) → K,
      ((y : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ x = x := by
    intro x
    obtain ⟨v₁, hv₁, w, hw, w', hw', hx⟩ :=
      hS.decomp (U := ⊤) (by intro u hu; exact Submodule.mem_top) x (Submodule.mem_top)
    rw [hx, Matrix.mulVec_add, Matrix.mulVec_add, hfixV v₁ hv₁.1, hfixW w hw.1,
      hfixW' w' hw'.1]
  have hy1 : y = 1 := by
    refine Subtype.ext (Units.ext (Matrix.ext_iff_mulVec.2 fun x => ?_))
    simpa using hfixall x
  simpa using hy1

theorem RadSetup.kOf_inf_pCoreOf_eq_bot (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K)
    (hK₀ : F08.KOf8103 ⊤ (zpowers b) ≠ ⊥) :
    F08.KOf8103 ⊤ (zpowers b) ⊓ pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω)) = ⊥ := by
  have hle : F08.KOf8103 ⊤ (zpowers b) ⊓ pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω)) ≤
      pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω)) ⊓ stabSU (2 ^ f) (eigSU b ω⁻¹) := by
    rw [inf_comm (F08.KOf8103 ⊤ (zpowers b)) (pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω)))]
    exact inf_le_inf le_rfl (kOf_le_stabSU_eigSU b ω⁻¹)
  exact le_bot_iff.mp (hle.trans (le_of_eq (hS.pCoreOf_inf_stabSU_eq_bot h hK₀)))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
