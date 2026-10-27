module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Walter.ReeOrder.JT.Defs
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallRee
import CFSG.Walter.Ree.Model.JTHyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open scoped MatrixGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.ComponentClassification.OuterAutomorphisms

section


private theorem exists_involution_psl2_of_field_descent
    {F : Type} [Field F] [Finite F] [CharP F ReeTag.G2.prime]
    {a b : ℕ} (hb : 1 ≤ b)
    (α : MulAut (ReeTag.G2.reeGamma F a))
    (σ : F ≃+* F)
    (hkk : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 3 ^ (2 * b + 1))
    (δ : MulAut (ReeTag.G2.reeGamma F a))
    (hδ : δ * α * δ⁻¹ = ReeTag.G2.reeGammaFieldAut F a σ)
    (hfix : ((ReeTag.G2.reeGammaFieldAut F a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.G2.reeGamma F a).subtype =
        (ReeTag.G2.reeGamma (CFSG.LieType.Chevalley.fixSubfield σ) b).map
          (baseChangeGL (τ := ReeTag.G2.tag) (CFSG.LieType.Chevalley.fixSubfield σ).subtype)) :
    ∃ v ∈ fixedSubgroup α, orderOf v = 2 ∧
      ∃ F' : Subgroup (ReeTag.G2.reeGamma F a),
        F' ≤ fixedSubgroup α ∧
        F' ≤ centralizer ({v} : Set (ReeTag.G2.reeGamma F a)) ∧
        Nonempty (F' ≃* PSL(2, GaloisField 3 (2 * b + 1))) := by
  classical
  set kk : Subfield F := CFSG.LieType.Chevalley.fixSubfield σ
  have : Finite kk :=
    Nat.finite_of_card_ne_zero (by rw [hkk]; exact (pow_pos (by norm_num) _).ne')
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP kk ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_three (by omega) hkk
  let J : CFSG.Walter.JT.JTHyp (ReeTag.G2.reeGamma kk b) :=
    CFSG.Walter.Ree.Model.smallReeJTHyp (a := b) hb (K := kk) hkk
  let ι₀ : ↥(ReeTag.G2.reeGamma kk b) →* ModGL ReeTag.G2.tag F :=
    (baseChangeGL (τ := ReeTag.G2.tag) kk.subtype).comp (ReeTag.G2.reeGamma kk b).subtype
  have hsub : ∀ x : ↥(ReeTag.G2.reeGamma kk b), ι₀ x ∈ ReeTag.G2.reeGamma F a := by
    intro x
    have hx : ι₀ x ∈ (ReeTag.G2.reeGamma kk b).map
        (baseChangeGL (τ := ReeTag.G2.tag) kk.subtype) :=
      Subgroup.mem_map_of_mem _ x.2
    rw [← hfix] at hx
    obtain ⟨y, -, hyval⟩ := Subgroup.mem_map.mp hx
    rw [← hyval]
    exact y.2
  let ι : ↥(ReeTag.G2.reeGamma kk b) →* ↥(ReeTag.G2.reeGamma F a) :=
    ι₀.codRestrict (ReeTag.G2.reeGamma F a) hsub
  have hι_apply : ∀ x, ((ι x : ↥(ReeTag.G2.reeGamma F a)) : ModGL ReeTag.G2.tag F) = ι₀ x :=
    fun x => rfl
  have hι_fix : ∀ x, ReeTag.G2.reeGammaFieldAut F a σ (ι x) = ι x := by
    intro x
    have hx : ι₀ x ∈ ((ReeTag.G2.reeGammaFieldAut F a σ).toMonoidHom.eqLocus
        (MonoidHom.id _)).map (ReeTag.G2.reeGamma F a).subtype := by
      rw [hfix]
      exact Subgroup.mem_map_of_mem _ x.2
    obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp hx
    have hy_eq : y = ι x := Subtype.ext (hyval.trans (hι_apply x).symm)
    rwa [hy_eq] at hy
  have hι₀_inj : Function.Injective ι₀ :=
    (baseChangeGL_injective (τ := ReeTag.G2.tag) kk.subtype).comp
      (Subgroup.subtype_injective (ReeTag.G2.reeGamma kk b))
  have hι_inj : Function.Injective ι := by
    intro x y h
    exact hι₀_inj (by rw [← hι_apply x, ← hι_apply y, h])
  have hkey : ∀ y : ↥(ReeTag.G2.reeGamma F a),
      α (δ.symm y) = δ.symm (ReeTag.G2.reeGammaFieldAut F a σ y) := by
    intro y
    apply δ.injective
    calc δ (α (δ.symm y)) = (δ * α * δ⁻¹) y := rfl
      _ = ReeTag.G2.reeGammaFieldAut F a σ y := by rw [hδ]
      _ = δ (δ.symm (ReeTag.G2.reeGammaFieldAut F a σ y)) := by
          rw [MulEquiv.apply_symm_apply]
  let ψ : ↥(ReeTag.G2.reeGamma kk b) →* ↥(ReeTag.G2.reeGamma F a) :=
    δ.symm.toMonoidHom.comp ι
  have hψ_apply : ∀ x, ψ x = δ.symm (ι x) := fun x => rfl
  have hψ_fix : ∀ x, ψ x ∈ fixedSubgroup α := by
    intro x
    show α (δ.symm (ι x)) = δ.symm (ι x)
    rw [hkey (ι x), hι_fix x]
  have hψ_inj : Function.Injective ψ := by
    intro x y h
    apply hι_inj
    have h2 : δ (δ.symm (ι x)) = δ (δ.symm (ι y)) := by
      rw [← hψ_apply x, ← hψ_apply y]
      exact congrArg δ h
    simpa using h2
  refine ⟨ψ J.t, hψ_fix J.t, ?_, J.F.map ψ, ?_, ?_, ?_⟩
  · exact (orderOf_injective ψ hψ_inj J.t).trans J.orderOf_t
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact hψ_fix y
  · rw [Subgroup.map_le_iff_le_comap]
    intro y hy
    change ψ y ∈ centralizer ({ψ J.t} : Set (ReeTag.G2.reeGamma F a))
    have hyc : y ∈ centralizer ({J.t} : Set ↥(ReeTag.G2.reeGamma kk b)) := J.le_centralizer hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
    rw [← map_mul, ← map_mul, hyc]
  · exact ⟨(Subgroup.equivMapOfInjective J.F ψ hψ_inj).symm.trans J.iso⟩

private theorem card_fixedSubgroup_reeGamma_seven (a : ℕ) (ha : 1 ≤ a) (F : Type) [Field F]
    [Finite F] [CharP F ReeTag.G2.prime] (hF : Nat.card F = 3 ^ (2 * a + 1))
    (α : MulAut (ReeTag.G2.reeGamma F a)) (hα : α ^ 7 = 1)
    (hαout : α ∉ inner (ReeTag.G2.reeGamma F a)) :
    ∃ b : ℕ, 2 * a + 1 = 7 * (2 * b + 1) ∧ Nat.card (fixedSubgroup α) =
      (3 ^ (2 * b + 1)) ^ 3 * ((3 ^ (2 * b + 1)) ^ 3 + 1) * (3 ^ (2 * b + 1) - 1) := by
  obtain ⟨⟨d, hd⟩, δ, σ, -, hδ, hk, hfix⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent a ha F hF
      Nat.prime_seven (by norm_num) α hα hαout
  have hd' : (2 * a + 1) / 7 = d := by
    rw [hd, Nat.mul_div_cancel_left _ (by norm_num : 0 < 7)]
  have hdodd : Odd d := by
    have h1 : Odd (7 * d) := hd ▸ odd_two_mul_add_one a
    exact (Nat.odd_mul.1 h1).2
  obtain ⟨b, hb⟩ := hdodd
  have hbd : (d - 1) / 2 = b := by omega
  rw [hd'] at hk hfix
  rw [hbd] at hfix
  have hkb : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 3 ^ (2 * b + 1) := by
    rw [hk, hb]
  have : Finite (CFSG.LieType.Chevalley.fixSubfield σ) :=
    Nat.finite_of_card_ne_zero (by rw [hkb]; exact (pow_pos (by norm_num) _).ne')
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP (CFSG.LieType.Chevalley.fixSubfield σ) ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_three (by omega) hkb
  have hcard1 : Nat.card (fixedSubgroup α) = Nat.card (fixedSubgroup
      (ReeTag.G2.reeGammaFieldAut F a σ)) :=
    CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_eq_of_intertwine δ α _ fun x => by
      rw [← hδ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have hcard2 : Nat.card (fixedSubgroup (ReeTag.G2.reeGammaFieldAut F a σ)) =
      Nat.card (ReeTag.G2.reeGamma (CFSG.LieType.Chevalley.fixSubfield σ) b) := by
    have h1 := Subgroup.card_map_of_injective
      (K := (ReeTag.G2.reeGammaFieldAut F a σ).toMonoidHom.eqLocus (MonoidHom.id _))
      (Subgroup.subtype_injective (ReeTag.G2.reeGamma F a))
    have h2 := Subgroup.card_map_of_injective (K := ReeTag.G2.reeGamma
      (CFSG.LieType.Chevalley.fixSubfield σ) b)
      (baseChangeGL_injective (τ := ReeTag.G2.tag)
        (CFSG.LieType.Chevalley.fixSubfield σ).subtype)
    rw [hfix, h2] at h1
    exact h1.symm
  exact ⟨b, by rw [hd, hb], by
    rw [hcard1, hcard2, CFSG.HardMathSupport.Lang.Coordinator.card_reeGamma_G2_eq hkb]⟩

private theorem reeGamma_outer_seven_fixed (a : ℕ) (ha : 1 ≤ a) (F : Type) [Field F]
    [Finite F] [CharP F ReeTag.G2.prime] (hF : Nat.card F = 3 ^ (2 * a + 1))
    (α : MulAut (ReeTag.G2.reeGamma F a)) (hα : α ^ 7 = 1)
    (hαout : α ∉ inner (ReeTag.G2.reeGamma F a)) :
    ∃ d : ℕ, 2 * a + 1 = 7 * d ∧ Odd d ∧
      Nat.card (fixedSubgroup α) =
        (3 ^ d) ^ 3 * ((3 ^ d) ^ 3 + 1) * (3 ^ d - 1) ∧
      (3 ≤ d → ∃ v ∈ fixedSubgroup α, orderOf v = 2 ∧
        ∃ F' : Subgroup (ReeTag.G2.reeGamma F a),
          F' ≤ fixedSubgroup α ∧
          F' ≤ centralizer ({v} : Set (ReeTag.G2.reeGamma F a)) ∧
          Nonempty (F' ≃* PSL(2, GaloisField 3 d))) := by
  obtain ⟨b, hdb, hcard⟩ :=
    card_fixedSubgroup_reeGamma_seven a ha F hF α hα hαout
  obtain ⟨⟨d, hd⟩, δ, σ, -, hδ, hk, hfix⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent a ha F hF
      Nat.prime_seven (by norm_num) α hα hαout
  have hd' : (2 * a + 1) / 7 = d := by
    rw [hd, Nat.mul_div_cancel_left _ (by norm_num : 0 < 7)]
  have hdodd : Odd d := by
    have h1 : Odd (7 * d) := hd ▸ odd_two_mul_add_one a
    exact (Nat.odd_mul.1 h1).2
  have hb' : d = 2 * b + 1 := by omega
  have hbd : (d - 1) / 2 = b := by omega
  rw [hd'] at hk hfix
  rw [hbd] at hfix
  have hkb : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 3 ^ (2 * b + 1) := by
    rw [hk, hb']
  refine ⟨2 * b + 1, ?_, ?_, ?_, ?_⟩
  · rw [← hb']
    exact hd
  · rw [← hb']
    exact hdodd
  · exact hcard
  · intro hd3
    have hb1 : 1 ≤ b := by omega
    exact exists_involution_psl2_of_field_descent hb1 α σ hkb δ hδ hfix

end

theorem ree_outer_seven_fixed
    {G : Type} [Group G] [Finite G] {f : ℕ} (hmod : CFSG.Blueprint.LieModel G .twistedG2 0 3 f)
    (α : MulAut G) (hα : α ^ 7 = 1)
    (hαout : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner G) :
    ∃ d : ℕ, f = 7 * d ∧ Odd d ∧
      Nat.card (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α) =
        (3 ^ d) ^ 3 * ((3 ^ d) ^ 3 + 1) * (3 ^ d - 1) ∧
      (3 ≤ d → ∃ v ∈ CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α,
        orderOf v = 2 ∧ ∃ F : Subgroup G,
          F ≤ CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α ∧
          F ≤ centralizer ({v} : Set G) ∧ Nonempty (F ≃* PSL(2, GaloisField 3 d))) := by
  classical
  obtain ⟨-, -, -, -, ⟨k, rfl⟩, hf3⟩ := CFSG.Blueprint.LieModel.admissible hmod
  have hree : CFSG.Blueprint.ReeTitsModel G .twistedG2 3 (2 * k + 1) :=
    (hmod.reeTitsModel (by simp [CFSG.Blueprint.reeTitsTags])).2
  obtain ⟨-, a, hfa, hrel⟩ := hree
  obtain ⟨F, _, _, _, hF, ⟨e₁⟩⟩ :=
    (CFSG.LieType.Ree.reeTitsRelationModel_iff .G2 G (2 * k + 1) a).1 hrel
  have ha : 1 ≤ a := by omega
  have hF' : Nat.card F = 3 ^ (2 * a + 1) := hfa ▸ hF
  obtain ⟨e₂⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.nonempty_derivedCentralQuotient_reeGamma_G2
      (K := F) ha hF'
  let e : G ≃* ReeTag.G2.reeGamma F a := e₁.trans e₂
  let β : MulAut (ReeTag.G2.reeGamma F a) := MulAut.congr e α
  have hβ : β ^ 7 = 1 := by
    show (MulAut.congr e α) ^ 7 = 1
    rw [← map_pow, hα, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (ReeTag.G2.reeGamma F a) := by
    show MulAut.congr e α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner _
    exact fun hin => hαout
      ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e α).mp hin)
  obtain ⟨d, hd, hdodd, hcard, hpart⟩ :=
    reeGamma_outer_seven_fixed a ha F hF' β hβ hβout
  refine ⟨d, hfa.trans hd, hdodd, ?_, ?_⟩
  · rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr e α]
    exact hcard
  · intro hd3
    obtain ⟨v, hv, hvord, F', hF'1, hF'2, ⟨iso⟩⟩ := hpart hd3
    refine ⟨e.symm v, ?_, ?_, Subgroup.map e.symm.toMonoidHom F', ?_, ?_, ?_⟩
    · show α (e.symm v) = e.symm v
      have h := congrArg e.symm hv
      simpa [β, MulAut.congr_apply] using h
    · exact (orderOf_injective e.symm.toMonoidHom e.symm.injective v).trans hvord
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      show α (e.symm y) = e.symm y
      have h := congrArg e.symm (hF'1 hy)
      simpa [β, MulAut.congr_apply] using h
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hyc : y ∈ Subgroup.centralizer ({v} : Set _) := hF'2 hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
      show e.symm y * e.symm v = e.symm v * e.symm y
      rw [← map_mul, ← map_mul, hyc]
    · exact ⟨(Subgroup.equivMapOfInjective F' e.symm.toMonoidHom e.symm.injective).symm.trans iso⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
