module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallD4Perp
public import CFSG.LieType.Universal.Spin.Twisted.RankOne
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisSpinMinus
public import CFSG.LieType.Steinberg.Classical.Symplectic.RankOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted

theorem range_le_perpSub_of_sl2 {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {k : ℕ} (hF : Nat.card F = 2 ^ k)
    (hk : 2 ≤ k) {y : MulAut V} (φ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut V)
    (hφy : ∀ x, φ x * y = y * φ x) (hlt : (fixV (Subgroup.zpowers y)).index < 2 ^ (2 * k)) :
    φ.range ≤ perpSub y := by
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have := CFSG.LocalAnalysis.EvenBN.Common.sl2_isSimpleGroup_of_charTwo (k := F) h4
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · refine le_perpSub_of_sl2 hV hF hk
      (MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff φ).1 h)).symm ?_ hlt
    rintro _ ⟨x, rfl⟩
    exact hφy x
  · rintro _ ⟨x, rfl⟩
    rw [show φ x = 1 from MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x)]
    exact one_mem _

section Transport

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private noncomputable def mulAutOfRep {H : Type*} [Group H] (σ : Representation (ZMod 2) H W) :
    H →* MulAut (Multiplicative W) where
  toFun h := AddEquiv.toMultiplicative
    { toFun := σ h
      invFun := σ h⁻¹
      left_inv := fun w => by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      right_inv := fun w => by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      map_add' := map_add (σ h) }
  map_one' := by
    ext v
    simp [AddEquiv.toMultiplicative_apply_apply]
  map_mul' g h := by
    ext v
    simp [AddEquiv.toMultiplicative_apply_apply, MulAut.mul_apply]

private theorem index_fixV_toMultiplicative [Finite W] (a : W ≃ₗ[ZMod 2] W) :
    (fixV (Subgroup.zpowers (AddEquiv.toMultiplicative a.toAddEquiv))).index =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  set y := AddEquiv.toMultiplicative a.toAddEquiv
  have hy : ∀ v, commHom y v = Multiplicative.ofAdd ((a.toLinearMap - 1) v.toAdd) := by
    intro v
    rw [commHom_apply, AddEquiv.toMultiplicative_apply_apply]
    apply Multiplicative.toAdd.injective
    simp [sub_eq_add_neg]
  have e : Nat.card (commHom y).range = Nat.card (LinearMap.range (a.toLinearMap - 1)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative W), ?_⟩
        invFun := fun w => ⟨Multiplicative.ofAdd (w : W), ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · obtain ⟨v, hv⟩ := x.2
      exact ⟨v.toAdd, by rw [← hv, hy]; rfl⟩
    · obtain ⟨w', hw'⟩ := w.2
      exact ⟨Multiplicative.ofAdd w', by rw [hy]; exact congrArg Multiplicative.ofAdd hw'⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← ker_commHom, Subgroup.index_ker, e, FiniteField.pow_finrank_eq_natCard]

end Transport

theorem shortSL2_perp_of_finrank_lt {n : ℕ} {K W : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) {b c : K} (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (i : Fin (n - 1)) (ρ : Representation (ZMod 2) (spinGroup (quadMinus n K b c)) W)
    (a : W ≃ₗ[ZMod 2] W)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) < 4 * e)
    (hcomm : ∀ g ∈ (shortPosHom n hirrQ i).range ⊔ (shortNegHom n hirrQ i).range,
      ∀ w, a (ρ g w) = ρ g (a w)) :
    ∀ g ∈ (shortPosHom n hirrQ i).range ⊔ (shortNegHom n hirrQ i).range,
      (ρ g - 1) * (a.toLinearMap - 1) = 0 ∧ (a.toLinearMap - 1) * (ρ g - 1) = 0 := by
  have := fact_shortField hirrQ
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap K (ShortField b c)).injective 2
  have hE : Nat.card (ShortField b c) = 2 ^ (2 * e) := by
    rw [CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.card_shortField, hK, ← pow_mul,
      mul_comm]
  set R := shortRels n hirrQ i with hR
  obtain ⟨Θ, hU, hL⟩ := CFSG.AGLEmbeddingD2.HeisSpinMinus.exists_hom_of_rankOneRels' R
  have hΘS : ∀ x, Θ x ∈ (shortPosHom n hirrQ i).range ⊔ (shortNegHom n hirrQ i).range := by
    intro x
    rw [← shortRels_sub n hirrQ i, ← hR]
    have hle : (Subgroup.closure (Set.range (sl2Upper (k := ShortField b c)) ∪
        Set.range sl2Lower)).map Θ ≤ R.sub := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨z, ⟨t, rfl⟩ | ⟨t, rfl⟩, rfl⟩
      · rw [hU]
        exact R.x_mem_sub t
      · rw [hL]
        exact R.y_mem_sub t
    exact hle ⟨x, CFSG.LieType.Steinberg.Sp.mem_closure_sl2 x, rfl⟩
  have hSΘ : ∀ g ∈ (shortPosHom n hirrQ i).range ⊔ (shortNegHom n hirrQ i).range,
      ∃ x, Θ x = g := by
    intro g hg
    rw [← shortRels_sub n hirrQ i, ← hR] at hg
    have hle : R.sub ≤ Θ.range := by
      rw [RankOneRels.sub, Subgroup.closure_le]
      rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · exact ⟨sl2Upper t, hU t⟩
      · exact ⟨sl2Lower t, hL t⟩
    exact hle hg
  set φ := mulAutOfRep (ρ.comp Θ) with hφ
  set y : MulAut (Multiplicative W) := AddEquiv.toMultiplicative a.toAddEquiv with hy
  have hV : ∀ v : Multiplicative W, v ^ 2 = 1 := fun v =>
    congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero (n := 2) v.toAdd)
  have hφy : ∀ x, φ x * y = y * φ x := by
    intro x
    ext v
    exact congrArg Multiplicative.ofAdd (hcomm _ (hΘS x) v.toAdd).symm
  have hlt : (fixV (Subgroup.zpowers y)).index < 2 ^ (2 * (2 * e)) := by
    rw [hy, index_fixV_toMultiplicative]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hperp := range_le_perpSub_of_sl2 hV hE (by omega) φ hφy hlt
  intro g hg
  obtain ⟨x, rfl⟩ := hSΘ g hg
  have hx := mem_perpSub.1 (hperp ⟨x, rfl⟩)
  have hφw : ∀ u, φ x (Multiplicative.ofAdd u) = Multiplicative.ofAdd (ρ (Θ x) u) := fun _ => rfl
  have hyw : ∀ u, y (Multiplicative.ofAdd u) = Multiplicative.ofAdd (a u) := fun _ => rfl
  have hdiv : ∀ u u' : W,
      Multiplicative.ofAdd u * (Multiplicative.ofAdd u')⁻¹ = Multiplicative.ofAdd (u - u') :=
    fun u u' => by rw [sub_eq_add_neg, ofAdd_add, ofAdd_neg]
  refine ⟨LinearMap.ext fun w => ?_, LinearMap.ext fun w => ?_⟩
  · have h1 := (hx (Multiplicative.ofAdd w)).2
    rw [hyw, hdiv, hφw] at h1
    have h : ρ (Θ x) (a w - w) = a w - w := Multiplicative.ofAdd.injective h1
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearEquiv.coe_coe, LinearMap.zero_apply]
    rw [h, sub_self]
  · have h1 := (hx (Multiplicative.ofAdd w)).1
    rw [hφw, hdiv, hyw] at h1
    have h : a (ρ (Θ x) w - w) = ρ (Θ x) w - w := Multiplicative.ofAdd.injective h1
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearEquiv.coe_coe, LinearMap.zero_apply]
    rw [h, sub_self]

theorem shortSL2_perp_of_finrank_le {n : ℕ} {K W : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) {b c : K} (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (i : Fin (n - 1)) (ρ : Representation (ZMod 2) (spinGroup (quadMinus n K b c)) W)
    (a : W ≃ₗ[ZMod 2] W)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) ≤ 2 * e + 1)
    (hcomm : ∀ g ∈ (shortPosHom n hirrQ i).range ⊔ (shortNegHom n hirrQ i).range,
      ∀ w, a (ρ g w) = ρ g (a w)) :
    ∀ g ∈ (shortPosHom n hirrQ i).range ⊔ (shortNegHom n hirrQ i).range,
      (ρ g - 1) * (a.toLinearMap - 1) = 0 ∧ (a.toLinearMap - 1) * (ρ g - 1) = 0 :=
  shortSL2_perp_of_finrank_lt he hK hirrQ i ρ a (by omega) hcomm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
