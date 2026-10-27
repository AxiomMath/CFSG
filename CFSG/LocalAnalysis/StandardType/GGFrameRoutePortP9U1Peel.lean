module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStructEig
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U1PeelGrp
import CFSG.LargeExtraspecial.S4Restrict
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U1Heis
public import Mathlib

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct
open scoped commutatorElement

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private lemma p9uPeel_restrict_mem_scalars {H : Type*} [Group H]
    (φ : H →* (V ≃ₗ[K] V)) (U : Submodule K V) (hU : ∀ x u, u ∈ U → φ x u ∈ U) {z : H}
    (hz : φ z ∈ scalars K V) :
    CFSG.LargeExtraspecial.S4.restrictHom φ U hU z ∈ scalars K U := by
  obtain ⟨c, hc⟩ := mem_scalars_iff.1 hz
  refine mem_scalars_iff.2 ⟨c, fun u => Subtype.ext ?_⟩
  simpa using hc (u : V)

theorem exists_peel_of_not_abelian [Finite K] (hK : Nat.card K = 4) [FiniteDimensional K V]
    {Q : Subgroup (V ≃ₗ[K] V)} (hQ : IsGoodIn (scalars K V) Q)
    (hnab : ¬ ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) :
    ∃ (U : Submodule K V) (Q' : Subgroup (U ≃ₗ[K] U)),
      Module.finrank K V = 3 * Module.finrank K U ∧ IsGoodIn (scalars K U) Q' ∧
      Nat.card Q = 9 * Nat.card Q' ∧
      Nat.card (Subgroup.center Q') = Nat.card (Subgroup.center Q) := by
  classical
  haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv
  have hZ : ScalarLike (scalars K V) := scalarLike_scalars (V := V) hK
  obtain ⟨g, hg, h, hh, hg3, hgh⟩ := exists_pow_three_eq_one_noncomm hZ hQ hnab
  obtain ⟨ω, hω3, hω1, hconj⟩ := exists_omega hK (hQ.1 g hg h hh) hgh
  have hωprim : IsPrimitiveRoot ω 3 := isPrimitiveRoot_of_pow_three hω3 hω1
  have hg3lin : (g : V →ₗ[K] V) ^ 3 = 1 := by
    ext v
    have h := congrArg (fun e : V ≃ₗ[K] V => e v) hg3
    simpa [LinearEquiv.pow_apply, Module.End.pow_apply] using h
  have hxy : (g : V →ₗ[K] V) * (h : V →ₗ[K] V) =
      ω • ((h : V →ₗ[K] V) * (g : V →ₗ[K] V)) := by
    ext v
    simp only [Module.End.mul_apply, LinearMap.smul_apply]
    exact hconj v
  have hker : (⊤ : Submodule K V) ⊓ LinearMap.ker ((g : V →ₗ[K] V) - 1) = eig g 1 := by
    rw [top_inf_eq]
    ext v
    simp only [LinearMap.mem_ker, mem_eig_iff, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero, one_smul]
    exact Iff.rfl
  have hdim : Module.finrank K V = 3 * Module.finrank K (eig g 1) := by
    have h := finrank_eq_three_mul_finrank_inf_ker_sub_one hωprim
      (x := (g : V →ₗ[K] V)) (y := (h : V →ₗ[K] V)) (P := ⊤)
      (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top)
      hg3lin h.injective hxy
    rwa [finrank_top, hker] at h
  let Q₁ : Subgroup (V ≃ₗ[K] V) := Q ⊓ Subgroup.centralizer ({g, h} : Set (V ≃ₗ[K] V))
  have hCU : ∀ x ∈ Q₁, ∀ u ∈ eig g 1, x u ∈ eig g 1 := by
    intro x hx u hu
    have hxcent : x ∈ Subgroup.centralizer ({g, h} : Set (V ≃ₗ[K] V)) :=
      (Subgroup.mem_inf.mp hx).2
    have hgx : g * x = x * g := Subgroup.mem_centralizer_iff.1 hxcent g (by simp)
    rw [mem_eig_iff] at hu ⊢
    have h1 : g (x u) = x (g u) := by
      have h := congrArg (fun e : V ≃ₗ[K] V => e u) hgx
      simpa using h
    rw [h1, hu, one_smul, one_smul]
  let ρ : Q₁ →* (eig g 1 ≃ₗ[K] eig g 1) :=
    CFSG.LargeExtraspecial.S4.restrictHom Q₁.subtype (eig g 1)
      (fun x u hu => hCU x x.2 u hu)
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxcent : (x : V ≃ₗ[K] V) ∈ Subgroup.centralizer ({g, h} : Set (V ≃ₗ[K] V)) :=
      (Subgroup.mem_inf.mp x.2).2
    have hcx : (x : V ≃ₗ[K] V) * h = h * (x : V ≃ₗ[K] V) :=
      (Subgroup.mem_centralizer_iff.1 hxcent h (by simp)).symm
    have hfix : ∀ u ∈ eig g 1, (x : V ≃ₗ[K] V) u = u :=
      (CFSG.LargeExtraspecial.S4.restrictHom_eq_one_iff Q₁.subtype (eig g 1)
        (fun y u hu => hCU y y.2 u hu) x).1 hx
    exact Subtype.ext (eq_one_of_fix_eig hg3 hconj hω3 hω1 hcx hfix)
  have hρgood : IsGoodIn (scalars K (eig g 1)) ρ.range := by
    constructor
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [← map_commutatorElement]
      exact p9uPeel_restrict_mem_scalars Q₁.subtype (eig g 1)
        (fun y u hu => hCU y y.2 u hu)
        (by
          rw [map_commutatorElement]
          exact hQ.1 (x : V ≃ₗ[K] V) (Subgroup.mem_inf.mp x.2).1
            (y : V ≃ₗ[K] V) (Subgroup.mem_inf.mp y.2).1)
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      refine p9uPeel_restrict_mem_scalars Q₁.subtype (eig g 1)
        (fun y u hu => hCU y y.2 u hu) ?_
      rw [map_pow]
      exact hQ.2 (x : V ≃ₗ[K] V) (Subgroup.mem_inf.mp x.2).1
  refine ⟨eig g 1, ρ.range, hdim, hρgood, ?_, ?_⟩
  · have h9 : Nat.card Q = 9 * Nat.card Q₁ :=
      card_eq_nine_mul_card_inf_centralizer_pair hZ hQ hg hh hgh
    have hrange : Nat.card ρ.range = Nat.card Q₁ :=
      (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
    rwa [← hrange] at h9
  · have e : Q₁ ≃* ρ.range := MonoidHom.ofInjective hρinj
    calc Nat.card (Subgroup.center ρ.range)
        = Nat.card (Subgroup.center Q₁) :=
          (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
      _ = Nat.card (Subgroup.center Q) := card_center_inf_centralizer_pair hZ hQ hg hh hgh

end CFSG.StandardType.FrameRoute

end
