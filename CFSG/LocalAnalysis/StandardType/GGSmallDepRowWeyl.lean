module

public import CFSG.LocalAnalysis.StandardType.GGSmallDepRowMisc
public import CFSG.LocalAnalysis.StandardType.GGNineDepRowSymSuccHolds
import CFSG.LocalAnalysis.StandardType.ZS.Adapter
import CFSG.LocalAnalysis.StandardType.GGSmallDepE7Seven
import CFSG.LocalAnalysis.StandardType.ZS.TableCommon
import CFSG.LocalAnalysis.StandardType.GGNineDepRowOrthHolds
import CFSG.LocalAnalysis.StandardType.ZS.TableWeyl
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
  {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}

theorem ggSmallE7Input_holds :
    ∀ (U : Type) [AddCommGroup U] [Module (ZMod 7) U] [Module.Finite (ZMod 7) U]
      (A : Subgroup (U ≃ₗ[ZMod 7] U)) (h : Fin 6 → U) (α : Fin 6 → Module.Dual (ZMod 7) U)
      (r : Fin 6 → (U ≃ₗ[ZMod 7] U)),
      ZS.IsCartanModel 7 (CartanMatrix.E 7) A →
      (∀ i, r i ∈ A) → (∀ i v, r i v = v - α i v • h i) →
      (∀ i j, α i (h j) = (CartanMatrix.A 6 i j : ZMod 7)) →
      LinearIndependent (ZMod 7) h := by
  intro U _ _ _ A h α r hA hr hrpair hpair
  obtain ⟨u, φ, hφ, hK, hspan, hker, hAeq⟩ := hA
  haveI : Finite U := Module.finite_of_finite (ZMod 7)
  exact ggE7Seven_A6_linearIndependent u φ hK (fun i => Module.reflection (hφ i))
    (fun i v => Module.reflection_apply v (hφ i)) h α hpair r hrpair
    (fun j => hAeq ▸ hr j)

namespace GGNineDepCtx

theorem false_of_linWeyl
    (X : GGNineDepCtx h α r s x)
    (hcell : (p = 5 ∧ N = 5) ∨ (p = 3 ∧ N = 6) ∨ (p = 7 ∧ N = 7) ∨ (p = 5 ∧ N = 10))
    (hw : ZS.LinWeyl p (ggNineQ X)) : False := by
  haveI : Module.Finite (ZMod p) V := X.finite
  haveI : Module.Finite (ZMod p) ↥(ggFixLineT r s) :=
    FiniteDimensional.finiteDimensional_submodule (ggFixLineT r s)
  have hirr : ∀ W : Submodule (ZMod p) ↥(ggFixLineT r s),
      (∀ a ∈ ggNineQ X, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤ := X.restr.2.1.1
  have hdle : Module.finrank (ZMod p) ↥(ggFixLineT r s) ≤ N := X.d_le
  have hdge : N - 2 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) := X.d_ge
  have hN5 : 5 ≤ N := by
    rcases hcell with ⟨-, hN5⟩ | ⟨-, hN6⟩ | ⟨-, hN7⟩ | ⟨-, hN10⟩ <;> omega
  have h3 : 3 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) := by omega
  rcases ZS.isCartanModel_cases_typed_of_linWeyl X.case.lin.p_ne_two h3 hirr hw with
      ⟨ℓ, hA, T, hT⟩ | ⟨ℓ, hℓ2, hA⟩ | ⟨ℓ, hℓ4, hA⟩ | ⟨hE6, hE6ne⟩ | ⟨hE7, _⟩ |
      ⟨hE8, hE8ne⟩ | ⟨hF4, _⟩
  ·
    obtain ⟨-, e, he⟩ | ⟨hdvd, e, -⟩ :=
      ZS.symmetric_row_of_isCartanModel_A X.case.lin.p_ne_two rfl hA T hT
    · refine X.false_of_symSucc X.factorial_dvd X.natCard_ne_factorial e ?_
      intro q hq
      exact he q ((ZS.isRefl_iff_ggLinRefl (q : ↥(ggFixLineT r s) ≃ₗ[ZMod p]
        ↥(ggFixLineT r s))).mpr hq)
    · exact X.false_of_symSuccTwo hdvd e
  ·
    exact X.not_isImprimitiveOnV
      (ZS.isImprimitiveOnV_of_isCartanModel_B X.case.lin.p_ne_two hℓ2 hA)
  ·
    exact X.not_isImprimitiveOnV
      (ZS.isImprimitiveOnV_of_isCartanModel_D X.case.lin.p_ne_two hℓ4 hA)
  ·
    by_cases hp3 : p = 3
    · subst hp3
      obtain ⟨hd, Q, hQ, hcl⟩ := ZS.isCartanModel_E6_three_classRefl hE6
      have hN6 : N = 6 := by
        rcases hcell with ⟨hp5, -⟩ | ⟨-, hN6⟩ | ⟨hp7, -⟩ | ⟨hp5, -⟩ <;> omega
      have h2 : (2 : ZMod 3) ≠ 0 := by
        intro h
        have hdvd : 3 ∣ 2 :=
          Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) 3).mp h)
        have hle : 3 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
        omega
      exact X.false_of_heart rfl hN6 hd hQ (c := 2) h2 hcl
    · have hdet6 : (((CartanMatrix.E 6).det : ℤ) : ZMod p) ≠ 0 := by
        rw [CartanMatrix.E₆_det]
        intro h
        have hdvd3 : p ∣ 3 :=
          Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd (3 : ℤ) p).mp h)
        exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp hdvd3)
      have hd6 : Module.finrank (ZMod p) ↥(ggFixLineT r s) = 6 :=
        ZS.IsCartanModel.finrank_eq_card_of_det hE6 hdet6
      have hN7 : N = 7 := by
        rcases hcell with ⟨hp5, hN5⟩ | ⟨hp3', hN6⟩ | ⟨hp7, hN7⟩ | ⟨hp5', hN10⟩
        · omega
        · exact (hp3 hp3').elim
        · exact hN7
        · omega
      subst hN7
      let e : CoxeterMatrix.E₆.Group ≃* ↥(ggNineQ X) := Classical.choice hE6ne
      have hcardE6 : Nat.card (CoxeterMatrix.E₆.Group) = 51840 := by
        have hC : GGIntCartan CoxeterMatrix.E₆ (CFSG.Blueprint.Chevalley.Tag.cartan .E6) := by
          refine ⟨by decide, fun i j hij => ?_⟩
          fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
        have hM : CFSG.LieType.RootSystem.coxeterMatrix
            (CFSG.LieType.Chevalley.isFiniteType_cartan .E6) = CoxeterMatrix.E₆ :=
          coxeterMatrix_eq_of_ggIntCartan (CFSG.LieType.Chevalley.isFiniteType_cartan .E6) hC
        have h : Nat.card (CFSG.LieType.Chevalley.WeylGroup .E6) = 51840 :=
          NoOffExc.card_weyl_E6
        change Nat.card ((CFSG.LieType.RootSystem.coxeterMatrix
          (CFSG.LieType.Chevalley.isFiniteType_cartan .E6)).Group) = 51840 at h
        rw [hM] at h
        exact h
      have hcard : Nat.card ↥(ggNineQ X) = 51840 :=
        (Nat.card_congr e.toEquiv).symm.trans hcardE6
      have hdvd := X.factorial_dvd
      rw [hcard] at hdvd
      exact absurd hdvd (by decide : ¬ (Nat.factorial 7 ∣ 51840))
  ·
    have hdet7 : (((CartanMatrix.E 7).det : ℤ) : ZMod p) ≠ 0 := by
      rw [CartanMatrix.E₇_det]
      intro h
      have hdvd2 : p ∣ 2 :=
        Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).mp h)
      exact X.case.lin.p_ne_two ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd2)
    have hd7 : Module.finrank (ZMod p) ↥(ggFixLineT r s) = 7 :=
      ZS.IsCartanModel.finrank_eq_card_of_det hE7 hdet7
    have hN7 : N = 7 := by
      rcases hcell with ⟨hp5, hN5⟩ | ⟨hp3, hN6⟩ | ⟨hp7, hN7⟩ | ⟨hp5, hN10⟩
      · omega
      · omega
      · exact hN7
      · omega
    have hp7 : p = 7 := by
      rcases hcell with ⟨hp5, hN5⟩ | ⟨hp3, hN6⟩ | ⟨hp7, hN7⟩ | ⟨hp5, hN10⟩
      · omega
      · omega
      · exact hp7
      · omega
    subst hp7
    subst hN7
    obtain ⟨h', α', r', hmem, hrfl, hpair, hdep⟩ := X.exists_restrict_frame
    exact hdep (ggSmallE7Input_holds (U := ↥(ggFixLineT r s)) (A := ggNineQ X)
      (h := h') (α := α') (r := r') hE7 hmem hrfl hpair)
  ·
    have hdet8 : (((CartanMatrix.E 8).det : ℤ) : ZMod p) ≠ 0 := by
      rw [CartanMatrix.E₈_det]
      intro h
      have h1 : p ∣ 1 :=
        Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd (1 : ℤ) p).mp h)
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) h1
      omega
    have hd8 : Module.finrank (ZMod p) ↥(ggFixLineT r s) = 8 :=
      ZS.IsCartanModel.finrank_eq_card_of_det hE8 hdet8
    have hN10 : N = 10 := by
      rcases hcell with ⟨hp5, hN5⟩ | ⟨hp3, hN6⟩ | ⟨hp7, hN7⟩ | ⟨hp5, hN10⟩
      · omega
      · omega
      · omega
      · exact hN10
    let e : CoxeterMatrix.E₈.Group ≃* ↥(ggNineQ X) := Classical.choice hE8ne
    have hcentral : ∃ z : CoxeterMatrix.E₈.Group,
        z ≠ 1 ∧ z * z = 1 ∧ ∀ w, z * w = w * z := by
      have key : ∀ M : CoxeterMatrix (Fin 8),
          CFSG.LieType.RootSystem.coxeterMatrix
            (CFSG.LieType.Chevalley.isFiniteType_cartan .E8) = M →
          ∃ z : M.Group, z ≠ 1 ∧ z * z = 1 ∧ ∀ w, z * w = w * z := by
        rintro M rfl
        exact NineDepOrth.exists_central_involution_weylE8
      exact key _ NineDepOrth.coxeterMatrix_E8_eq
    obtain ⟨z, hz1, hzz, hzc⟩ :=
      NineDepOrth.exists_central_involution_of_mulEquiv e hcentral
    have hz_center : z ∈ Subgroup.center ↥(ggNineQ X) :=
      Subgroup.mem_center_iff.mpr (fun w => (hzc w).symm)
    obtain ⟨c, hc⟩ := ZS.AbsIrred.exists_eq_smul_of_mem_center X.restr.2.1 hz_center
    have hpos : 0 < Module.finrank (ZMod p) ↥(ggFixLineT r s) := by rw [hd8]; norm_num
    obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    have hc_sq : c * c = 1 := by
      have h1 : (z : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) *
          (z : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) = 1 := by
        have h := congrArg (fun e : ↥(ggNineQ X) => (e : ↥(ggFixLineT r s) ≃ₗ[ZMod p]
          ↥(ggFixLineT r s))) hzz
        simpa [Subgroup.coe_mul] using h
      have h2 : ((z : ↥(ggFixLineT r s) →ₗ[ZMod p] ↥(ggFixLineT r s)) *
          (z : ↥(ggFixLineT r s) →ₗ[ZMod p] ↥(ggFixLineT r s))) = LinearMap.id := by
        simpa [LinearEquiv.coe_toLinearMap_mul] using congrArg
          (fun e : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s) =>
            (e : ↥(ggFixLineT r s) →ₗ[ZMod p] ↥(ggFixLineT r s))) h1
      rw [hc] at h2
      have h3 : ((c * c) • LinearMap.id :
          ↥(ggFixLineT r s) →ₗ[ZMod p] ↥(ggFixLineT r s)) = LinearMap.id := by
        simpa [Module.End.mul_eq_comp, LinearMap.smul_comp, LinearMap.comp_smul,
          smul_smul] using h2
      have hv' := congrArg (fun f : ↥(ggFixLineT r s) →ₗ[ZMod p] ↥(ggFixLineT r s) => f v) h3
      have h4 : (c * c - 1) • v = 0 := by
        rw [sub_smul, one_smul]
        exact sub_eq_zero.mpr hv'
      have h5 : c * c - 1 = 0 := (smul_eq_zero.mp h4).resolve_right hv
      exact sub_eq_zero.mp h5
    have hc_eq : c = 1 ∨ c = -1 := by
      have h : (c - 1) * (c + 1) = 0 := by
        calc (c - 1) * (c + 1) = c * c - 1 := by ring
          _ = 0 := by rw [hc_sq, sub_self]
      rcases mul_eq_zero.mp h with h1 | h1
      · left; linear_combination h1
      · right; linear_combination h1
    have hc_ne_one : c ≠ 1 := by
      intro hc1
      have hz_one : z = 1 := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro w
        have h := congrArg (fun f : ↥(ggFixLineT r s) →ₗ[ZMod p] ↥(ggFixLineT r s) => f w) hc
        rw [hc1, one_smul] at h
        simpa [LinearMap.id_apply] using h
      exact hz1 hz_one
    have hc_neg : c = -1 := hc_eq.resolve_left hc_ne_one
    have hneg : (LinearEquiv.neg (ZMod p) : ↥(ggFixLineT r s) ≃ₗ[ZMod p]
        ↥(ggFixLineT r s)) ∈ ggNineQ X := by
      have h : (z : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) =
          LinearEquiv.neg (ZMod p) := by
        apply LinearEquiv.ext
        intro w
        have h := congrArg (fun f : ↥(ggFixLineT r s) →ₗ[ZMod p] ↥(ggFixLineT r s) => f w) hc
        rw [hc_neg] at h
        simpa [LinearMap.smul_apply, LinearMap.id_apply] using h
      rw [← h]
      exact z.2
    have hdN : Module.finrank (ZMod p) ↥(ggFixLineT r s) = N :=
      X.finrank_eq_of_neg_mem hneg
    rw [hd8, hN10] at hdN
    omega
  ·
    have hdet4 : (((CartanMatrix.F₄).det : ℤ) : ZMod p) ≠ 0 := by
      rw [CartanMatrix.F₄_det]
      intro h
      have h1 : p ∣ 1 :=
        Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd (1 : ℤ) p).mp h)
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) h1
      omega
    have hd4 : Module.finrank (ZMod p) ↥(ggFixLineT r s) = 4 :=
      ZS.IsCartanModel.finrank_eq_card_of_det hF4 hdet4
    have hneg : (LinearEquiv.neg (ZMod p) : ↥(ggFixLineT r s) ≃ₗ[ZMod p]
        ↥(ggFixLineT r s)) ∈ ggNineQ X :=
      ZS.neg_mem_of_isCartanModel_F4 hF4
    have hdN : Module.finrank (ZMod p) ↥(ggFixLineT r s) = N :=
      X.finrank_eq_of_neg_mem hneg
    rw [hd4] at hdN
    omega

end GGNineDepCtx

end CFSG.StandardType

end
