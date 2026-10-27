module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.ZS

open Subgroup

theorem witCR_of_dMax {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ} (hd : 4 < d)
    (hD : DMax p A d) (hone : OneClass p A) :
    ∀ r ∈ A, IsRefl p r → WitCR p A r := by
  intro r hrA hr
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hD.2
  obtain ⟨g, hgA, hg⟩ := hone x hx r hrA hxr hr
  obtain ⟨h, hhA, hh⟩ := hone r hrA y hy hr hyr
  refine ⟨g * h, A.mul_mem hgA hhA, ?_⟩
  have ht' : (g * h) * r * (g * h)⁻¹ = g * y * g⁻¹ := by
    rw [hh]
    group
  have hrt : r * ((g * h) * r * (g * h)⁻¹) = g * (x * y) * g⁻¹ := by
    rw [ht', hg]
    group
  rw [hrt]
  have hord : orderOf (g * (x * y) * g⁻¹) = orderOf (x * y) := by
    simpa [MulAut.conj_apply] using
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (x * y)
  rw [hord, hxy]
  exact hd

theorem wit_exc_abstract {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} (hai : AbsIrred p A) (k : ExcRow) (hk : ¬ k.needsModel)
    (hadm : k.admissible p) (hdeg : Module.finrank (ZMod p) U = k.deg) (hcard : Nat.card A = k.ord)
    (hcen : Nat.card (center A) = k.cen) (hD : DMax p A k.dmax) (hone : OneClass p A) :
    WitNEG3 p A ∨ ∀ r ∈ A, IsRefl p r → WitCR p A r := by
  cases k with
  | N4 => exact absurd trivial hk
  | EN4 => exact absurd trivial hk
  | K5 => exact absurd trivial hk
  | K6 => exact absurd trivial hk
  | H4 => exact Or.inr (witCR_of_dMax (by decide) hD hone)
  | H3 => exact Or.inr (witCR_of_dMax (by decide) hD hone)
  | J35 => exact Or.inr (witCR_of_dMax (by decide) hD hone)
  | EJ35 => exact Or.inr (witCR_of_dMax (by decide) hD hone)
  | J34 =>
    left
    have : NeZero p := ⟨hp.ne_zero⟩
    have : Fact (1 < p) := ⟨hp.one_lt⟩
    have : Nontrivial U :=
      Module.nontrivial_of_finrank_eq_succ (R := ZMod p) (M := U) (n := 2)
        (by simpa [ExcRow.deg] using hdeg)
    let : Field (ZMod p) := @ZMod.instField p ⟨hp⟩
    have hcen_ne : Nat.card (center A) ≠ 0 := by rw [hcen]; norm_num [ExcRow.cen]
    have : Finite (center A) := by
      by_contra hfin
      exact hcen_ne (by rw [Nat.card_eq]; exact dif_neg hfin)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2dvd : 2 ∣ Nat.card (center A) := by rw [hcen]; norm_num [ExcRow.cen]
    obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := center A) 2 h2dvd
    have hz2A : (z : A) * (z : A) = 1 := by
      have hz2 : z * z = 1 := by
        have h : z ^ 2 = 1 := by
          have h' := pow_orderOf_eq_one z
          rwa [hzord] at h'
        simpa [pow_two] using h
      simpa [Subgroup.coe_mul] using congrArg Subtype.val hz2
    have hz2U : (z : U ≃ₗ[ZMod p] U) * (z : U ≃ₗ[ZMod p] U) = 1 := by
      simpa [Subgroup.coe_mul] using congrArg Subtype.val hz2A
    let T : Module.End (ZMod p) U := ((z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)
    have hcommT : ∀ a ∈ A, T ∘ₗ (a : U →ₗ[ZMod p] U) = (a : U →ₗ[ZMod p] U) ∘ₗ T := by
      intro a ha
      have hc := Subgroup.mem_center_iff.mp z.property (⟨a, ha⟩ : A)
      have hc' : (a : U ≃ₗ[ZMod p] U) * (z : U ≃ₗ[ZMod p] U)
          = (z : U ≃ₗ[ZMod p] U) * (a : U ≃ₗ[ZMod p] U) := by
        simpa [Subgroup.coe_mul] using congrArg Subtype.val hc
      ext v
      have hv := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hc'
      simp only [LinearEquiv.mul_apply] at hv
      simpa [T, LinearMap.comp_apply] using hv.symm
    obtain ⟨c, hcT⟩ := hai.2 T hcommT
    have hT2 : T ∘ₗ T = LinearMap.id := by
      ext v
      have h := congrArg (fun e : U ≃ₗ[ZMod p] U => (e : U →ₗ[ZMod p] U)) hz2U
      have hv := congrArg (fun f : U →ₗ[ZMod p] U => f v) h
      simpa [T, LinearEquiv.coe_toLinearMap_mul, LinearMap.comp_apply] using hv
    have hcc : c * c = 1 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : U)
      have hv' : T (T v) = v := by
        have h := congrArg (fun f : Module.End (ZMod p) U => f v) hT2
        simpa using h
      have hcv : (c * c) • v = (1 : ZMod p) • v := by
        rw [hcT] at hv'
        simpa [smul_smul] using hv'
      exact (smul_left_inj hv).mp hcv
    have hc1 : c = 1 ∨ c = -1 := by
      have h : c ^ 2 = 1 := by simpa [pow_two] using hcc
      exact sq_eq_one_iff.mp h
    have hz_ne_one : z ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hzord
      exact absurd hzord (by norm_num)
    have hc_eq_neg : c = -1 := by
      rcases hc1 with h1 | h1
      · exfalso
        apply hz_ne_one
        apply Subtype.ext
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        have hTv : T v = v := by rw [hcT, h1]; simp
        simpa [T] using hTv
      · exact h1
    have hz_neg : (z : U ≃ₗ[ZMod p] U) = LinearEquiv.neg (ZMod p) := by
      apply LinearEquiv.ext
      intro v
      have hTv : T v = c • v := by rw [hcT]; simp
      rw [hc_eq_neg] at hTv
      simpa [T, LinearEquiv.neg_apply] using hTv
    have hmemA : (z : U ≃ₗ[ZMod p] U) ∈ A := (z : A).property
    refine ⟨by simpa [ExcRow.deg] using hdeg, ?_⟩
    rw [← hz_neg]
    exact hmemA
  | J44 =>
    exfalso
    have hp3 : p = 3 := hadm
    subst hp3
    have : NeZero 3 := ⟨by norm_num⟩
    let : Field (ZMod 3) := @ZMod.instField 3 ⟨hp⟩
    let b : Module.Basis (Fin 4) (ZMod 3) U :=
      Module.finBasisOfFinrankEq (ZMod 3) U (by simpa [ExcRow.deg] using hdeg)
    let eGL : GL (Fin 4) (ZMod 3) ≃* (U ≃ₗ[ZMod 3] U) :=
      (Matrix.GeneralLinearGroup.toLin' (R := ZMod 3) (V := U) b).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) U)
    have hq : Fintype.card (ZMod 3) = 3 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_zmod]
    have hcardGL : Nat.card (U ≃ₗ[ZMod 3] U) = 24261120 := by
      have h1 : Nat.card (U ≃ₗ[ZMod 3] U) = Nat.card (GL (Fin 4) (ZMod 3)) :=
        (Nat.card_congr eGL.toEquiv).symm
      rw [h1, Matrix.card_GL_field (𝔽 := ZMod 3) 4, hq]
      norm_num [Fin.prod_univ_succ]
    have hval : Nat.card A = 161280 := by
      rw [hcard]
      norm_num [ExcRow.ord]
    have hdvd : 161280 ∣ 24261120 := by
      rw [← hval, ← hcardGL]
      exact Subgroup.card_subgroup_dvd_card A
    exact (by norm_num : ¬ (161280 ∣ 24261120)) hdvd

end CFSG.StandardType.ZS

end
