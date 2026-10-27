module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinIrredDef
public import CFSG.LocalAnalysis.StandardType.GGTableBLinIrredEnd
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLRound11

public section

namespace CFSG.StandardType.LinIrred

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.Assembly TypeA TypeANbrDvd CFSG.StandardType.LinUnitL
open CFSG.StandardType

variable {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggTableBActionSCr_PSL (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d) {r : ℕ}
    (hrd : d - 2 ≤ r) :
    GGTableBActionSCr p r (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  have := Fact.mk hp
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_card_sub_one hpK
  refine ⟨hp2, fun L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc => ?_⟩
  obtain ⟨φ', hφ's, hφker, hdiag⟩ := exists_model hp hpK hd hψ hker hperf hA hAI
    ((Nat.pow_le_pow_right hp.pos hrd).trans hr) h3
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  set H := Subgroup.closure (heartSet φ' p) with hH
  have hVA : heartSet φ' p ⊆ A := by
    rintro _ ⟨D, u, hD, hu, rfl⟩
    exact conj_mem_of_selfCent hsc hdiag hD hu
  have hHA : H ≤ A := (Subgroup.closure_le A).mpr hVA
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  refine ⟨H, Set.range fun σ : Equiv.Perm (Fin d) => φ' (permSL σ), hHA, ?_, ?_,
    weyl_spec hφker hAp hdiag, ?_, eq_one_of_perm_fixed (by omega) hφ's hφker hdiag, ?_, ?_, ?_, ?_⟩
  · intro hbot
    set i0 : Fin d := ⟨0, by omega⟩
    set i1 : Fin d := ⟨1, by omega⟩
    set i2 : Fin d := ⟨2, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have hi02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
    set D₁ := diagSLOf (rootT ζ i0 i1) (prod_rootT hζ0 h01)
    have he₁ : MulAut.conj (φ' D₁) ∈ H :=
      Subgroup.subset_closure ⟨D₁, _, coe_diagSLOf _ _, rootT_pow hζ.pow_eq_one i0 i1, rfl⟩
    rw [hbot, Subgroup.mem_bot] at he₁
    have h2 : ActsDiag φ' (MulAut.conj (φ' D₁)) (fun _ => (1 : K)) := by
      rw [he₁]
      exact actsDiag_one
    have h3' := (actsDiag_conj (φ' := φ') (coe_diagSLOf _ (prod_rootT hζ0 h01))).ratio hφker h2 hi02
    rw [rootT_left, rootT_other ζ (Ne.symm hi02) (by simp [i2, i1, Fin.ext_iff])] at h3'
    simp only [inv_one, mul_one] at h3'
    exact hζ1 h3'
  · intro n hn h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      exact Subgroup.subset_closure
        (conj_mem_heart_of_normalizes hp hp2 hpK hd hφ's hφker hA hsc hdiag hn hx)
    | one => simp
    | mul x y _ _ hx hy =>
      have e : MulAut.conj n * (x * y) * (MulAut.conj n)⁻¹ =
          (MulAut.conj n * x * (MulAut.conj n)⁻¹) * (MulAut.conj n * y * (MulAut.conj n)⁻¹) := by
        group
      rw [e]
      exact H.mul_mem hx hy
    | inv x _ hx =>
      have e : MulAut.conj n * x⁻¹ * (MulAut.conj n)⁻¹ =
          (MulAut.conj n * x * (MulAut.conj n)⁻¹)⁻¹ := by group
      rw [e]
      exact H.inv_mem hx
  · intro A' hA'A hA'ne hinv
    obtain ⟨⟨a₀, ha₀⟩, ha₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA'ne
    have ha₀1' : a₀ ≠ 1 := fun h => ha₀1 (Subtype.ext h)
    refine (Subgroup.closure_le A').mpr ?_
    rintro _ ⟨D, u, hD, hu, rfl⟩
    exact conj_mem_of_invariant hp (by omega) hφ's hφker hA'A hsc hdiag hAp
      (fun σ a ha => hinv _ ⟨σ, rfl⟩ a ha) ha₀ ha₀1' hD hu
  · rintro n ⟨σ, rfl⟩ a ha
    exact conj_mul_inv_mem_heart hφker hφ's hAp hdiag σ ha
  · intro n hn
    exact exists_weyl_fix hp hp2 hpK hd hφ's hφker hA hsc hdiag hn
  · rintro n ⟨σ, rfl⟩
    exact perm_image_mem_closure φ' σ
  · intro f hfH hfmul hfW
    exact heart_end_pow hp hp2 hpK hd hφ's hφker hA hsc hdiag f hfH hfmul hfW

end CFSG.StandardType.LinIrred

namespace CFSG.StandardType

open CFSG.Assembly LocalAnalysis.ComponentInitial.LinearFlag

theorem largeEvenLabelAll_linDvd_action {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGLinDvdLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTableBActionSCr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpn, hpd⟩ := h
  dsimp only at ht hl hpn hpd
  subst ht
  have hp2 : p ≠ 2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hlab.1 hpn
  have hd5 : 5 ≤ l + 1 := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    rcases hpd with ⟨k, hk⟩
    rcases k with _ | _ | k
    · omega
    · have : p ≠ 4 := by
        intro h4
        rw [h4] at hp
        exact absurd hp (by decide)
      omega
    · nlinarith
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', l + 1 - 2,
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TypeA.ggTorusLift_sub_two hp hpK (by omega) (TypeA.slHasSections_of_five_le hd5)),
    ggTableBActionSCr_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
      (LinIrred.ggTableBActionSCr_PSL hp hpK hd5 le_rfl)⟩

theorem ggTableBActionInputOn_linDvd_holds : GGTableBActionInputOn GGLinDvdLabel :=
  ggTableBActionInputOn_of_labelsSCr ggBstarInnerDiagLInputOn_linDvd
    fun _ _ hp hlab h => largeEvenLabelAll_linDvd_action hp hlab h

end CFSG.StandardType

end
