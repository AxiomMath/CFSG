module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4Outer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallField
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Rank
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.HardMathSupport.U4FF (NaturalSU4 NaturalOmega6 disp)
open scoped commutatorElement Pointwise Matrix

theorem le_disp_of_linear_coords {I : Type} [CommGroup I] [Finite I]
    [Fact (∀ s : I, s * s = 1)] {L : Subgroup (MulAut I)} (hirr : IsIrrOn L ⊤ ⊥)
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F] {k : ℕ}
    (hF : Nat.card F = 2 ^ k) (hι : 2 ≤ Fintype.card ι)
    {Γ : Subgroup (GL ι F)} (ε : ↥L ≃* ↥Γ) (ψ : I ≃* Multiplicative (ι → F))
    (hψ : ∀ (l : ↥L) (s : I), ψ ((l : MulAut I) s) = Multiplicative.ofAdd
      (((ε l : GL ι F) : Matrix ι ι F) *ᵥ Multiplicative.toAdd (ψ s)))
    {t : MulAut I} (ht : t * t = 1) (ht1 : t ≠ 1)
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut I))) : k ≤ disp t := by
  classical
  let ρ : Representation (ZMod 2) ↥L (Additive I) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (binaryLin.comp L.subtype)
  haveI hirrρ : Fact ρ.IsIrreducible := by
    refine ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mpr ⟨?_, fun U hU => ?_⟩⟩
    · obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt hirr.1
      refine ⟨⟨Additive.ofMul x, 0, fun h0 => hx ?_⟩⟩
      have hx1 : x = 1 := congrArg Additive.toMul h0
      rw [hx1]
      exact Subgroup.one_mem _
    · let U' : Subgroup I :=
        { carrier := {x | Additive.ofMul x ∈ U}
          mul_mem' := fun ha hb => U.add_mem ha hb
          one_mem' := U.zero_mem
          inv_mem' := fun ha => U.neg_mem ha }
      have hU' : StableUnder L U' := fun l hl u hu => hU ⟨l, hl⟩ (Additive.ofMul u) hu
      rcases hirr.2.2.2 U' hU' bot_le le_top with h0 | h1
      · left
        rw [eq_bot_iff]
        intro w hw
        have hw' : Additive.toMul w ∈ U' := hw
        rw [h0, Subgroup.mem_bot] at hw'
        rw [Submodule.mem_bot]
        exact congrArg Additive.ofMul hw'
      · right
        rw [eq_top_iff]
        intro w _
        have hw' : Additive.toMul w ∈ U' := h1 ▸ Subgroup.mem_top _
        exact hw'
  let β : Additive I ≃+ (ι → F) :=
    { toFun := fun w => Multiplicative.toAdd (ψ (Additive.toMul w))
      invFun := fun v => Additive.ofMul (ψ.symm (Multiplicative.ofAdd v))
      left_inv := fun w => by simp
      right_inv := fun v => by simp
      map_add' := fun a b => by
        show Multiplicative.toAdd (ψ (Additive.toMul a * Additive.toMul b)) = _
        rw [map_mul, toAdd_mul] }
  have hβ : ∀ (l : ↥L) (w : Additive I), β (ρ l w) =
      ((ε l : GL ι F) : Matrix ι ι F) *ᵥ β w := fun l w => by
    show Multiplicative.toAdd (ψ ((l : MulAut I) (Additive.toMul w))) = _
    rw [hψ, toAdd_ofAdd]
    rfl
  let μ : F → Module.End (ZMod 2) (Additive I) := fun c =>
    AddMonoidHom.toZModLinearMap 2 ((β.symm.toAddMonoidHom.comp
      { toFun := fun v : ι → F => c • v
        map_zero' := smul_zero c
        map_add' := smul_add c }).comp β.toAddMonoidHom)
  have hμ : ∀ c w, μ c w = β.symm (c • β w) := fun _ _ => rfl
  have hμρ : ∀ c (l : ↥L) w, μ c (ρ l w) = ρ l (μ c w) := by
    intro c l w
    apply β.injective
    rw [hμ, hβ, AddEquiv.apply_symm_apply, hμ, hβ, AddEquiv.apply_symm_apply,
      Matrix.mulVec_smul]
  let s : Additive I ≃ₗ[ZMod 2] Additive I := binaryLin t
  have hs : ∀ w, s (s w) = w := fun w => by
    show binaryLin t (binaryLin t w) = w
    rw [← LinearEquiv.mul_apply, ← map_mul, ht, map_one]
    rfl
  have hN : ∀ l : ↥L, ∃ l' : ↥L, ∀ w, s (ρ l (s w)) = ρ l' w := by
    intro l
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
    have hmem : t * (l : MulAut I) * t ∈ L := by
      have h1 := (Subgroup.mem_normalizer_iff.mp htN (l : MulAut I)).mp l.2
      rwa [htinv] at h1
    refine ⟨⟨_, hmem⟩, fun w => ?_⟩
    show binaryLin t (binaryLin (l : MulAut I) (binaryLin t w)) =
      binaryLin (t * (l : MulAut I) * t) w
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hcardW : Nat.card (Additive I) = 2 ^ (k * Fintype.card ι) := by
    rw [Nat.card_congr β.toEquiv, Nat.card_fun, hF, Nat.card_eq_fintype_card, ← pow_mul]
  have hdimW : Module.finrank (ZMod 2) (Additive I) = k * Fintype.card ι :=
    Nat.pow_right_injective le_rfl
      ((CFSG.QuasithinUnique.Setup.X7.natCard_eq_two_pow_finrank (Additive I)).symm.trans hcardW)
  have hdisp : disp t = Module.finrank (ZMod 2)
      (LinearMap.range ((s : Additive I →ₗ[ZMod 2] Additive I) - 1)) := rfl
  have hrn := LinearMap.finrank_range_add_finrank_ker
    ((s : Additive I →ₗ[ZMod 2] Additive I) - 1)
  by_cases hcomm : ∀ c w, s (μ c (s w)) = μ c w
  ·
    have hcomm' : ∀ c w, μ c (s w) = s (μ c w) := fun c w => by
      have h1 := hcomm c (s w)
      rw [hs] at h1
      exact h1.symm
    set R := LinearMap.range ((s : Additive I →ₗ[ZMod 2] Additive I) - 1) with hR
    have hRμ : ∀ c, ∀ r ∈ R, μ c r ∈ R := by
      rintro c _ ⟨x, rfl⟩
      refine ⟨μ c x, ?_⟩
      simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, map_sub, hcomm']
    let N : Submodule F (ι → F) :=
      { carrier := β '' R
        add_mem' := by
          rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
          exact ⟨a + b, R.add_mem ha hb, map_add β a b⟩
        zero_mem' := ⟨0, R.zero_mem, map_zero β⟩
        smul_mem' := by
          rintro c _ ⟨a, ha, rfl⟩
          exact ⟨μ c a, hRμ c a ha, by rw [hμ, AddEquiv.apply_symm_apply]⟩ }
    have hcardNR : Nat.card N = Nat.card R := by
      refine Nat.card_congr
        { toFun := fun v => ⟨β.symm v, ?_⟩
          invFun := fun r => ⟨β r, ⟨r, r.2, rfl⟩⟩
          left_inv := fun v => Subtype.ext (β.apply_symm_apply v)
          right_inv := fun r => Subtype.ext (β.symm_apply_apply r) }
      obtain ⟨r, hr, hrv⟩ := v.2
      rw [← hrv, AddEquiv.symm_apply_apply]
      exact hr
    have h1 : Nat.card R = 2 ^ disp t := by
      rw [hdisp]
      exact CFSG.QuasithinUnique.Setup.X7.natCard_eq_two_pow_finrank R
    have h2 : Nat.card N = 2 ^ (k * Module.finrank F N) := by
      rw [Module.natCard_eq_pow_finrank (K := F), hF, ← pow_mul]
    have hdeq : disp t = k * Module.finrank F N :=
      Nat.pow_right_injective le_rfl (h1.symm.trans (hcardNR.symm.trans h2))
    rw [hdeq]
    have hpos : 0 < Module.finrank F N := by
      rcases Nat.eq_zero_or_pos (Module.finrank F N) with h0 | h0
      · exfalso
        have hN0 : N = ⊥ := Submodule.finrank_eq_zero.mp h0
        refine ht1 (MulEquiv.ext fun x => ?_)
        have hmem : (s : Additive I →ₗ[ZMod 2] Additive I) (Additive.ofMul x) -
            Additive.ofMul x ∈ R := ⟨Additive.ofMul x, rfl⟩
        have hβ0 : β ((s : Additive I →ₗ[ZMod 2] Additive I) (Additive.ofMul x) -
            Additive.ofMul x) ∈ N := ⟨_, hmem, rfl⟩
        rw [hN0, Submodule.mem_bot, map_eq_zero_iff β β.injective, sub_eq_zero] at hβ0
        exact congrArg Additive.toMul hβ0
      · exact h0
    calc k = k * 1 := (Nat.mul_one k).symm
      _ ≤ k * Module.finrank F N := Nat.mul_le_mul_left k hpos
  ·
    push Not at hcomm
    obtain ⟨c, w, hw⟩ := hcomm
    obtain ⟨d, hd⟩ := (mem_endRing_iff ρ (μ c)).mpr fun l v => hμρ c l v
    have hD : ∃ d : EndRing ρ, ∃ w, s (d (s w)) ≠ d w :=
      ⟨d, w, by
        have h1 : ∀ v, d v = μ c v := fun v => congrFun hd v
        rw [h1, h1]
        exact hw⟩
    have hsq := Thm14_5.card_fix_sq_of_not_commute_endRing ρ s hs hN hD
    have hfix : Nat.card {w : Additive I // s w = w} =
        Nat.card (LinearMap.ker ((s : Additive I →ₗ[ZMod 2] Additive I) - 1)) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
        rfl)
    rw [hfix, CFSG.QuasithinUnique.Setup.X7.natCard_eq_two_pow_finrank, hcardW,
      ← pow_mul] at hsq
    have hker := Nat.pow_right_injective le_rfl hsq
    have hk2 : 2 * k ≤ k * Fintype.card ι := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left k hι
    omega

theorem le_disp_of_naturalOmega6 {I : Type} [CommGroup I] [Finite I]
    [Fact (∀ s : I, s * s = 1)] {L : Subgroup (MulAut I)} {e : ℕ} (hirr : IsIrrOn L ⊤ ⊥)
    (h : NaturalOmega6 e L) {t : MulAut I} (ht : t * t = 1) (ht1 : t ≠ 1)
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut I))) : e ≤ disp t := by
  obtain ⟨F, _, _, b, c, hF, -, ε, ψ, hψ⟩ := h
  exact le_disp_of_linear_coords hirr hF (by decide) ε ψ hψ ht ht1 htN

private theorem k146ModU4Omega6_pointwise :
    ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
      ∀ (N S : Subgroup (MulAut U)) (n : ℕ), S ≤ N → (S.subgroupOf N).Normal →
        IsU4 ↥S n → 1 < n → IsIrrOn S ⊤ ⊥ → NaturalOmega6 n S → n ≤ E3.mParam N := by
  intro U _ _ hU2 N S n hSN hSnormal hU4 _ hirr hnat
  classical
  haveI : Fact (∀ s : U, s * s = 1) := ⟨fun s => by rw [← pow_two]; exact hU2 s⟩
  have hevS : Even (Nat.card ↥S) := Thm14_5.even_card_of_isU4 hU4
  have hevN : Even (Nat.card N) := by
    rw [even_iff_two_dvd] at hevS ⊢
    exact hevS.trans (Subgroup.card_dvd_of_le hSN)
  obtain ⟨t₀, ht₀N, ht₀o, -⟩ := CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam N hevN
  refine le_mParam_of_forall_involutions N n hevN ⟨t₀, ht₀N, ht₀o⟩ ?_
  intro t htN hto
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by rintro rfl; rw [orderOf_one] at hto; omega
  have hnorm : t ∈ Subgroup.normalizer (S : Set (MulAut U)) :=
    (CFSG.Quasithin.BlueprintB2.normal_subgroupOf_iff_le_normalizer hSN).mp hSnormal htN
  have hdisp : n ≤ disp t := le_disp_of_naturalOmega6 hirr hnat ht2 ht1 hnorm
  simpa only [← Thm14_5.rkIdx_fixV_zpowers_eq_disp] using hdisp

theorem k146ModU4Omega6_holds : K146ModU4Omega6 := by
  unfold K146ModU4Omega6
  exact k146ModU4Omega6_pointwise

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
