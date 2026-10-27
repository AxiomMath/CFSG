module

public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
import CFSG.RankThree.GF2n.Tim81.Sec7.LinePairFrame
import CFSG.Timmesfeld.Transvection.ModelSUAutLine
import CFSG.Timmesfeld.Transvection.ModelSUAutField
import CFSG.Timmesfeld.Transvection.ModelSUBlock
public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen

public section

namespace CFSG.RankThree.GF2n.Tim81

open Matrix CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree
open scoped MatrixGroups commutatorElement

theorem unitaryAutCentralizer : UnitaryAutCentralizer := by
  intro K _ _ X₀ Δ f n hf hn hf2 hN hX _hodd A hA B hB hAB h hh hord y hy hy2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨Ψ, hker, hrange, hΔ, T₀, T₁, hT₀, hT₁, hAΨ, hBΨ⟩ :=
    hX.exists_frame (m := m) hA hB hAB.commutator_ne_bot
  let F := GaloisField 2 (2 * f)
  let σ : F ≃+* F := unitaryInvolution F 2 f
  have hF : Nat.card F = (2 ^ f) ^ 2 := CFSG.Timmesfeld.Transvection.card_galoisField_two_mul hf
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  have htr : ∀ a, σ a = a → ∃ c, c + σ c = a := fun a ha => exists_add_unitaryInvolution_eq hF ha
  have hnorm : ∀ d, σ d = d → ∃ l, σ l * l = d := fun d hd => exists_sigma_mul_self_eq hF hd
  have hΔ' : ∀ U : Subgroup K, U ∈ Δ ↔ ∃ x : SU σ (m + 2), U = (conjSub
      (Unitary.rootGroup σ hσ (m + 2) (unitaryLongRoot (m + 2) (by omega))) x).map Ψ := hΔ
  have hy' : y ∈ Subgroup.centralizer
      ((perpRoots Δ (T₀.map Ψ ⊔ T₁.map Ψ) : Subgroup K) : Set K) := by
    rw [← hAΨ, ← hBΨ]
    exact (Subgroup.mem_inf.1 hy).1
  have hP := SUTrans.commute_of_mem_centralizer_perpRoots hσ htr (by omega) hΔ' hT₀ hT₁ hy'
  obtain ⟨s, hs, hΦs⟩ :=
    SUTrans.exists_mem_lineSL_of_mem_sup hσ Ψ hT₀ hT₁ (by rw [← hAΨ, ← hBΨ]; exact hh)
  have haa : uForm σ (Pi.single (0 : Fin (m + 2)) 1) (Pi.single 0 1) = 0 :=
    uForm_single_self (by rw [Fin.rev_zero]; exact zero_ne_last)
  have hdd : uForm σ (Pi.single (Fin.last (m + 1)) 1) (Pi.single (Fin.last (m + 1)) 1) = 0 :=
    uForm_single_self (by rw [Fin.rev_last]; exact zero_ne_last.symm)
  have had : uForm σ (Pi.single (0 : Fin (m + 2)) 1) (Pi.single (Fin.last (m + 1)) 1) = 1 :=
    uForm_single_zero_last
  have hq : ¬(m + 2 = 3 ∧ 2 ^ f = 2) := by
    rintro ⟨-, h⟩
    have h4 : (2 : ℕ) ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    rw [h] at h4
    norm_num at h4
  obtain ⟨A, φ, α, hL⟩ :=
    exists_isSemilinearLift (F := F) (n := m + 2) hF hf (by omega) hq hker (hrange ▸ hN) y
  have hinj : ∀ v, (A : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ v = 0 → v = 0 :=
    fun v hv => Matrix.mulVec_injective_of_isUnit A.isUnit (by rw [hv, Matrix.mulVec_zero])
  have hφ : ∀ c, φ c = c := by
    have h := ringEquiv_eq_refl_of_isotropic_eigen hσ htr hnorm (by omega) haa hdd had
      (A : Matrix (Fin (m + 2)) (Fin (m + 2)) F) hinj φ (fun u hu huu => by
        obtain ⟨t, ht⟩ := exists_suMat_eq_uTrans hσ huu (c := 1)
          (by rw [map_one]; exact CharTwo.add_self_eq_zero 1)
        exact hL.exists_smul hker huu ht (hP u hu huu t ht))
    intro c
    rw [h]
    rfl
  rw [← hrange]
  refine hL.mem_centralizer_range hF hf2 (by omega) hφ hker haa hdd had hs ?_ hy2 ?_ hP
  · rw [hΦs]
    exact hord
  · rw [hΦs]
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.1 hy).2

end CFSG.RankThree.GF2n.Tim81
