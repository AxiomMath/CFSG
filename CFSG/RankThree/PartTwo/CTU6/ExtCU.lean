module

public import CFSG.RankThree.PartOne.CTP.ExtB
public import CFSG.RankThree.PartTwo.CTU6.WeakCT

public section

namespace CFSG.RankThree.PartTwo.CTU6

open CFSG.RankThree.PartOne (ExtCurtisTitsCThreeU)
open CFSG.RankThree.PartOne.CTP
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Unitary (SUid conjEquiv)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open scoped MatrixGroups

theorem dvd_two_pow_two_mul_sub_one {p f : ℕ} (h : p ∣ 2 ^ f - 1) : p ∣ 2 ^ (2 * f) - 1 := by
  refine h.trans ?_
  have := Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 2
  rwa [one_pow, ← pow_mul, mul_comm] at this

theorem extCurtisTitsCThreeU :
    ExtCurtisTitsCThreeU := by
  intro G _ _ f p K₁ K₂ K₃ E hf hp hpq hE hgen h₁ h₂ h₃ hcomm₁₃ hL3 hSU htor hz
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hSU
  have : CharP K 2 := charP_two_of_card_eq_two_pow (f := 2 * f) (by rw [hK]; ring)
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hfd : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, by rw [hK]; ring⟩
  have hσ := unitaryInvolution_involutive hK
  obtain ⟨ψ⟩ := nonempty_suid_four_equiv_of_psu_model hfd hq4 e
  let θ : SUid (unitaryInvolution K 2 f) 4 →* G := (K₂ ⊔ K₃).subtype.comp ψ.toMonoidHom
  have hθinj : Function.Injective θ := (Subgroup.subtype_injective _).comp ψ.injective
  have hθrange : θ.range = K₂ ⊔ K₃ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hθker : θ.ker ≤ Subgroup.center (SUid (unitaryInvolution K 2 f) 4) := by
    rw [(MonoidHom.ker_eq_bot_iff θ).mpr hθinj]
    exact bot_le
  have hE₃₂ : EdgeTorus p E K₃ K₂ :=
    ⟨(htor.1 2).1, (htor.1 2).2, (htor.1 1).1, (htor.1 1).2, htor.2 2 1 (by decide)⟩
  have hE₁₂ : EdgeTorus p E K₁ K₂ :=
    ⟨(htor.1 0).1, (htor.1 0).2, (htor.1 1).1, (htor.1 1).2, htor.2 0 1 (by decide)⟩
  obtain ⟨L₂, _, _, _, hL₂, ⟨ρ₂⟩⟩ := exists_sl2_equiv_of_model h₂
  obtain ⟨L₃, _, _, _, hL₃, ⟨ρ₃⟩⟩ := exists_sl2_equiv_of_model h₃
  have hL₂' : Nat.card L₂ = (2 ^ f) ^ 2 := by rw [hL₂]; ring
  obtain ⟨Q, hQ, hA, hB⟩ := su_edge_pair hfd hf θ hθker hp hpq hE₃₂
    (by rw [hθrange, sup_comm]) hL₃ hL₂' ρ₃ ρ₂ hz
  have hK₂le : K₂ ≤ θ.range := by rw [hθrange]; exact le_sup_left
  have hK₃le : K₃ ≤ θ.range := by rw [hθrange]; exact le_sup_right
  let Θ : CFSG.LieType.Universal.Unitary.SU (unitaryInvolution K 2 f) 4 →* G :=
    θ.comp (conjEquiv Q hQ).toMonoidHom
  have hΘinj : Function.Injective Θ := hθinj.comp (conjEquiv Q hQ).injective
  have hΘl : (lbEmb (unitaryInvolution K 2 f)).range.map Θ = K₃ := by
    calc (lbEmb (unitaryInvolution K 2 f)).range.map Θ
        = ((lbEmb (unitaryInvolution K 2 f)).range.map (conjEquiv Q hQ).toMonoidHom).map θ := by
          rw [Subgroup.map_map]
      _ = (K₃.comap θ).map θ := by rw [hA]
      _ = K₃ := by rw [Subgroup.map_comap_eq, inf_of_le_right hK₃le]
  have hΘs : (sbEmb (unitaryInvolution K 2 f) hσ).range.map Θ = K₂ := by
    calc (sbEmb (unitaryInvolution K 2 f) hσ).range.map Θ
        = ((sbEmb (unitaryInvolution K 2 f) hσ).range.map
            (conjEquiv Q hQ).toMonoidHom).map θ := by
          rw [Subgroup.map_map]
      _ = (K₂.comap θ).map θ := by rw [hB]
      _ = K₂ := by rw [Subgroup.map_comap_eq, inf_of_le_right hK₂le]
  have htw : ∃ W, (su4Model hK).StandardPair W K₃ K₂ := by
    refine ⟨Θ.range, Θ, rfl, ?_, hΘinj.comp lbSU4_injective,
      hΘinj.comp (sbEmb_injective _ hσ), ?_, hΘs⟩
    · rw [(MonoidHom.ker_eq_bot_iff Θ).mpr hΘinj]
      exact bot_le
    · change (lbSU4 K f).range.map Θ = K₃
      rw [range_lbSU4]
      exact hΘl
  have hpair : ∃ W, LinearBlockStandardPair K W K₁ K₂ :=
    exists_linearBlockStandardPair (f := 2 * f) (by omega) hp (dvd_two_pow_two_mul_sub_one hpq)
      hE₁₂ h₁ h₂ hL3 (by rw [hK]; ring)
  have hgen' : (⨆ k : Fin 3, (![K₁, K₂, K₃] : Fin 3 → Subgroup G) k) = ⊤ := by
    rw [← hgen]
    refine le_antisymm (iSup_le fun k => ?_) ?_
    · fin_cases k
      · exact le_sup_of_le_left le_sup_left
      · exact le_sup_of_le_left le_sup_right
      · exact le_sup_right
    · exact sup_le (sup_le (le_iSup (fun k : Fin 3 => (![K₁, K₂, K₃] : Fin 3 → Subgroup G) k) 0)
        (le_iSup (fun k : Fin 3 => (![K₁, K₂, K₃] : Fin 3 → Subgroup G) k) 1))
        (le_iSup (fun k : Fin 3 => (![K₁, K₂, K₃] : Fin 3 → Subgroup G) k) 2)
  obtain ⟨-, -, -, -, -, hmodel, -⟩ := weakCT_unitary_six_even hK hf ![K₁, K₂, K₃] hgen'
    (fun u hu v hv => (Subgroup.mem_centralizer_iff.mp (hcomm₁₃.1 hu) v hv).symm) hpair htw
  exact CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel
    (by decide : CFSG.Assembly.LowTwoRank.StatedLieTag.PSU ∈ CFSG.Blueprint.classicalTags) hmodel

end CFSG.RankThree.PartTwo.CTU6
