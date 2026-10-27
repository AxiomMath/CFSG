module

public import CFSG.Quasithin.Background.SmithB42SL3Aut
public import CFSG.Quasithin.Background.SmithB45SL3Label
public import CFSG.Quasithin.Background.SmithB45SL3Herm
public import CFSG.Quasithin.Background.HL3NineM

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X7
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups Matrix

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {e : ℕ}
  {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

theorem rank_up3_le_two_mul (hF : Fintype.card F = 2 ^ e) (he : 2 ≤ e)
    (ρ : Representation (ZMod 2) SL(3, F) U) (hirr : ρ.IsIrreducible)
    (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ LinearFlag.scalars 3 F)
    (a : U ≃ₗ[ZMod 2] U) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haN : ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ (up3 0 0 1) - 1)) ≤
      2 * Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  classical
  set A : Subgroup (U ≃ₗ[ZMod 2] U) := Subgroup.zpowers a with hAdef
  have hmemA : ∀ b ∈ A, b = 1 ∨ b = a := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hsq : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha2]
    obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
    · left
      rw [hj, zpow_mul, hsq, one_zpow]
    · right
      rw [hj, zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]
  have hA : ∀ b ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ b x y := by
    intro b hb x
    rcases hmemA b hb with rfl | rfl
    · exact ⟨x, fun u => rfl⟩
    · exact haN x
  have : CFSG.IsElementaryAbelian 2 ↥A := by
    refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
    · apply Subtype.ext
      rcases hmemA _ x.2 with hx | hx <;> rcases hmemA _ y.2 with hy | hy <;>
        simp only [Subgroup.coe_mul, hx, hy, one_mul, mul_one]
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      apply Subtype.ext
      rcases hmemA _ x.2 with hx | hx
      · simp [hx]
      · simp [hx, pow_two, ha2]
  have hNat : Nat.card F = 2 ^ e := by rw [Nat.card_eq_fintype_card, hF]
  have haA : a ∈ A := Subgroup.mem_zpowers a
  by_cases hin : (⟨a, haA⟩ : ↥A) ∈ B42SL3.innerPart ρ hker A hA
  · obtain ⟨t, ht2, hta⟩ := B42SL3.exists_lift_of_inner ρ hker A hA (by omega) hNat hirr _ hin
    have ht1 : t ≠ 1 := by
      rintro rfl
      apply ha1
      refine LinearEquiv.ext fun u => ?_
      rw [hta u, map_one]
      rfl
    have heq : (ρ t - 1) = a.toLinearMap - 1 := LinearMap.ext fun u => by
      simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe]
      rw [← hta u]
    rw [← B42SL3.finrank_range_involution ρ ht1 ht2, heq]
    omega
  · obtain ⟨t, ht, hrk⟩ := B42SL3.exists_transvection_of_outer ρ hker A hA he hNat _ hin
    rw [← B42SL3.finrank_range_involution ρ (ne_one_of_isTransvection ht) (isTransvection_sq ht)]
    exact hrk

theorem three_mul_le_finrank_range_of_herm {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card F = (2 ^ m) ^ 2)
    (ρ : Representation (ZMod 2) SL(3, F) U) (ψ : SL(3, F) →* SL(3, F)) (hψ : ∀ g, ψ (ψ g) = g)
    (E : Multiplicative U ≃* H.L3Nine.HMod m F)
    (hE : ∀ g u, E (Multiplicative.ofAdd (ρ g u)) =
      H.L3Nine.rho hK (ψ g) (E (Multiplicative.ofAdd u)))
    (a : U ≃ₗ[ZMod 2] U) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haN : ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y) :
    3 * m ≤ Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  classical
  have hfin : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  let aM : Multiplicative U ≃* Multiplicative U := AddEquiv.toMultiplicative a.toAddEquiv
  let T : MulAut (H.L3Nine.HMod m F) := (E.symm.trans aM).trans E
  have hT : ∀ X, T X = E (aM (E.symm X)) := fun X => rfl
  have haa : ∀ u, a (a u) = u := fun u => by
    have := LinearEquiv.congr_fun ha2 u
    simpa using this
  have hT2 : T * T = 1 := MulEquiv.ext fun X => by
    show E (aM (E.symm (E (aM (E.symm X))))) = X
    rw [MulEquiv.symm_apply_apply]
    have h1 : aM (aM (E.symm X)) = E.symm X := by
      show Multiplicative.ofAdd (a (a (Multiplicative.toAdd (E.symm X)))) = E.symm X
      rw [haa]
      rfl
    rw [h1, MulEquiv.apply_symm_apply]
  have hT1 : T ≠ 1 := by
    intro h1
    apply ha1
    refine LinearEquiv.ext fun u => ?_
    have h := congrArg (fun f : MulAut (H.L3Nine.HMod m F) => E.symm (f (E (Multiplicative.ofAdd u))))
      h1
    simp only [hT, MulEquiv.symm_apply_apply, MulAut.one_apply] at h
    exact congrArg Multiplicative.toAdd h
  have hconj : ∀ x : SL(3, F), ∀ X, E (Multiplicative.ofAdd (ρ x (Multiplicative.toAdd
      (E.symm X)))) = H.L3Nine.rho hK (ψ x) X := fun x X => by
    rw [hE, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have hfwd : ∀ g : SL(3, F), T * H.L3Nine.rho hK g * T⁻¹ ∈ H.L3Nine.img hK := by
    intro g
    obtain ⟨y, hy⟩ := haN (ψ g)
    refine ⟨ψ y, MulEquiv.ext fun X => ?_⟩
    have hTinv : T⁻¹ = T := by
      rw [inv_eq_iff_mul_eq_one]
      exact hT2
    rw [hTinv]
    show H.L3Nine.rho hK (ψ y) X = T (H.L3Nine.rho hK g (T X))
    rw [hT, hT, ← hconj y X]
    congr 1
    rw [← hψ g, ← hconj (ψ g)]
    simp only [MulEquiv.symm_apply_apply]
    show Multiplicative.ofAdd (ρ y (Multiplicative.toAdd (E.symm X))) =
      Multiplicative.ofAdd (a (Multiplicative.toAdd (Multiplicative.ofAdd
        (ρ (ψ g) (Multiplicative.toAdd (Multiplicative.ofAdd (a (Multiplicative.toAdd
          (E.symm X)))))))))
    rw [toAdd_ofAdd, toAdd_ofAdd, hy, haa]
  have hfwd' : ∀ k ∈ H.L3Nine.img hK, T * k * T⁻¹ ∈ H.L3Nine.img hK := by
    rintro _ ⟨g, rfl⟩
    exact hfwd g
  have hTN : T ∈ H.L3Nine.norm hK := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hfwd' h, fun hh => ?_⟩
    have h2 := hfwd' _ hh
    have hid : T * (T * h * T⁻¹) * T⁻¹ = h := by
      calc T * (T * h * T⁻¹) * T⁻¹ = (T * T) * h * (T * T)⁻¹ := by group
        _ = h := by rw [hT2]; group
    rwa [hid] at h2
  have hcard := H.L3Nine.card_fixV_le_of_involution hm hK hTN hT2 hT1
  have hfixeq : Nat.card ↥(fixV (Subgroup.zpowers T)) =
      Nat.card ↥(LinearMap.ker (a.toLinearMap - 1)) := by
    refine Nat.card_congr
      { toFun := fun X => ⟨Multiplicative.toAdd (E.symm X), ?_⟩
        invFun := fun u => ⟨E (Multiplicative.ofAdd u), ?_⟩
        left_inv := fun X => Subtype.ext (by simp)
        right_inv := fun u => Subtype.ext (by simp) }
    · have hX := (mem_fixV_zpowers_iff_apply).1 X.2
      rw [hT] at hX
      have h1 := congrArg (fun Y => Multiplicative.toAdd (E.symm Y)) hX
      simp only [MulEquiv.symm_apply_apply] at h1
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact h1
    · rw [mem_fixV_zpowers_iff_apply, hT, MulEquiv.symm_apply_apply]
      congr 1
      have hu := u.2
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hu
      show Multiplicative.ofAdd (a (Multiplicative.toAdd (Multiplicative.ofAdd (u : U)))) =
        Multiplicative.ofAdd (u : U)
      rw [toAdd_ofAdd]
      exact congrArg Multiplicative.ofAdd hu
  have hpow : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V],
      Nat.card V = 2 ^ Module.finrank (ZMod 2) V := fun V _ _ _ => by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]
  have hU : Nat.card U = 2 ^ (9 * m) := by
    rw [← H.L3Nine.card_HMod hm hK]
    exact (Nat.card_congr (Multiplicative.toAdd : Multiplicative U ≃ U).symm).trans
      (Nat.card_congr E.toEquiv)
  have hdimU : Module.finrank (ZMod 2) U = 9 * m := by
    rw [hpow U] at hU
    exact Nat.pow_right_injective le_rfl hU
  have hdimK : Module.finrank (ZMod 2) (LinearMap.ker (a.toLinearMap - 1)) ≤ 6 * m := by
    have h := hcard
    rw [hfixeq, hpow] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  have hrn := LinearMap.finrank_range_add_finrank_ker (a.toLinearMap - 1)
  omega

theorem natural_of_rank_le (hF : Fintype.card F = 2 ^ e) (he : 3 ≤ e)
    (ρ : Representation (ZMod 2) SL(3, F) U) (hirr : ρ.IsIrreducible) (hnt : ∃ x, ρ x ≠ 1)
    (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ LinearFlag.scalars 3 F)
    (a : U ≃ₗ[ZMod 2] U) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haN : ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y)
    (hrk : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) ≤ e + 1) :
    ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧ ∃ E : U ≃+ (Fin 3 → F), ∀ g u,
      E (ρ g u) = ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E u := by
  classical
  have hfin : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  let bas := Module.finBasis (ZMod 2) U
  obtain ⟨a', b', hne, hsum, W₀, ⟨e₀⟩⟩ := B42SL3.exists_label hF (by omega) ρ bas hirr hnt
  have hdim' : ∀ c : (Fin e → Bool) × (Fin e → Bool),
      3 ^ cntS c.1 c.2 * 8 ^ cntH c.1 c.2 ≤
        2 * (tensorRep (F := F) F c.1 c.2 (up3 0 0 1) - 1).rank + 1 :=
    fun c => dim_le_two_mul_rank_tensorRep c.1 c.2
  have hR := rank_up3_le_two_mul hF (by omega) ρ hirr hker a ha2 ha1 haN
  rcases B45SL3.label_cases' (by omega) a' b' hne _ hdim' (hsum.trans hR) with
    ⟨hS, hH⟩ | ⟨hS, hH, ho4, hoe⟩ | ⟨-, -, -, h4⟩ | h4
  · exact B42SL3.exists_natural_of_single hF ρ bas hirr hS hH W₀ e₀
  ·
    exfalso
    have hlt : (pairOrbit e (a', b')).card < e := by omega
    obtain ⟨m, hm, hem, hK, ψ, hψ, E, hE⟩ :=
      B45SL3.exists_herm_of_row hF ρ bas hirr hS hH hlt W₀ e₀
    have h3 := three_mul_le_finrank_range_of_herm hm hK ρ ψ hψ E hE a ha2 ha1 haN
    omega
  · omega
  · omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
