module

public import CFSG.Quasithin.Background.F918X1
public import CFSG.Quasithin.Background.F918X4
public import CFSG.Quasithin.Background.HSp4Rel
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
import CFSG.LieType.Universal.Symplectic
public import CFSG.Quasithin.Background.B4ModelsIso

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjSp fieldSp coe_conjSp
  coe_fieldSp conjAut_proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.QuasithinUnique.Lin2.Five (tauSp tauEquiv tauSp_bijective)

section Sp4Aut

variable {K : Type} [Field K]

theorem coe_conj_fieldSp (s : StatedSp 2 K) (σ : K ≃+* K) (g : StatedSp 2 K) :
    ((((MulAut.conj s * fieldSp 2 K σ) g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((s : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ *
        (((s : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  rw [MulAut.mul_apply, MulAut.conj_apply]
  have h : ((s * fieldSp 2 K σ g * s⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
      (s : GL (Fin 2 ⊕ Fin 2) K) * (fieldSp 2 K σ g : GL (Fin 2 ⊕ Fin 2) K) *
        (s : GL (Fin 2 ⊕ Fin 2) K)⁻¹ := rfl
  rw [h, Units.val_mul, Units.val_mul, coe_fieldSp]

theorem coe_conjSp_fieldSp (A : gsp 2 K) (σ : K ≃+* K) (g : StatedSp 2 K) :
    (((conjSp 2 K A (fieldSp 2 K σ g) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ *
        (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  rw [coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp]

variable [CharP K 2] [Finite K]

theorem exists_conjSp_eq_conj (A : gsp 2 K) :
    ∃ s : StatedSp 2 K, ∀ x : StatedSp 2 K, conjSp 2 K A x = s * x * s⁻¹ := by
  obtain ⟨s, hs⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_conjAut_eq_statedSp A
  refine ⟨s, fun x => ?_⟩
  have hπ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
    (r := 2) (K := K)
  apply hπ.1
  have h1 := congrArg (fun α : MulAut (StatedProj (StatedSp 2 K)) => α (proj 2 K x)) hs
  simp only [conjAut_proj] at h1
  rw [h1]
  rfl

theorem exists_cover_of_natural_sp4 {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
    {π : ↥(StatedSp 2 K) →* ↥H} (hπ : (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ ⊥ π)
    (hbij : Function.Bijective π) :
    ∃ γ : MulAut ↥H, ∀ α : MulAut ↥H, α ∈ realized H ∨ γ⁻¹ * α ∈ realized H := by
  set e : ↥(StatedSp 2 K) ≃* ↥H := MulEquiv.ofBijective π hbij
  set γ : MulAut ↥H := e.symm.trans (tauEquiv.trans e)
  have hγ : ∀ g, γ (π g) = π (tauSp g) := by
    intro g
    have h1 : e.symm (π g) = g := e.symm_apply_apply g
    show e (tauEquiv (e.symm (π g))) = π (tauSp g)
    rw [h1]
    rfl
  refine ⟨γ, fun α => ?_⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : MulAut ↥(StatedSp 2 K), ∀ g : ↥(StatedSp 2 K), α (π g) = π (θ g) :=
    exists_theta_of_bijective (D := FFModel.nat (StatedSp 2 K)) hbij α
  obtain ⟨A, σ, h1 | h2⟩ := CFSG.Quasithin.H.Sp4.exists_aut_eq θ
  · left
    refine mem_realized_of_semilinear hπ α θ hθ (A : GL (Fin 2 ⊕ Fin 2) K) σ fun g => ?_
    rw [h1 g, coe_conjSp_fieldSp]
  · right
    obtain ⟨s, hs⟩ := exists_conjSp_eq_conj A
    obtain ⟨s', hs'⟩ := tauSp_bijective.2 s
    set θ₂ : MulAut ↥(StatedSp 2 K) := MulAut.conj s' * fieldSp 2 K σ with hθ₂def
    have hθ₂ : ∀ g, tauSp (θ₂ g) = θ g := by
      intro g
      rw [h2 g, hs, hθ₂def, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hs',
        CFSG.RankThree.PartTwo.KFacts.tauSp_fieldSp]
    have hα₂ : ∀ g, (γ⁻¹ * α) (π g) = π (θ₂ g) := by
      intro g
      rw [MulAut.mul_apply, hθ g, ← hθ₂ g, ← hγ, MulAut.inv_apply_self]
    refine mem_realized_of_semilinear hπ (γ⁻¹ * α) θ₂ hα₂ (s' : GL (Fin 2 ⊕ Fin 2) K) σ fun g => ?_
    exact coe_conj_fieldSp s' σ g

end Sp4Aut

theorem charP_two_of_card_two_pow {K : Type} [Field K] [Finite K] {n : ℕ}
    (h : Nat.card K = 2 ^ n) : CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, h])

theorem center_eq_bot_of_equiv_sp4 {K : Type} [Field K] [CharP K 2] {H : Type*} [Group H]
    (e : StatedSp 2 K ≃* H) : Subgroup.center H = ⊥ := by
  have hZ : Subgroup.center (StatedSp 2 K) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq]
    exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.spScalars_eq_bot_of_charTwo
  rw [← Subgroup.map_center_eq e, hZ, Subgroup.map_bot]

theorem twoClassMod_centralData_of_binaryNaturalSp4 {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n : ℕ} (h : BinaryNaturalSp4 H ⊤ ⊥ n) :
    TwoClassMod H ∧ CentralData H := by
  obtain ⟨K, hK, hfin, hc, π, hπ⟩ := h
  have : CharP K 2 := charP_two_of_card_two_pow hc
  have hbij : Function.Bijective π :=
    ⟨hπ.injective_of_faithful (FFModel.nat_faithful _), hπ.1⟩
  obtain ⟨γ, hγ⟩ := exists_cover_of_natural_sp4 hπ hbij
  exact ⟨twoClassMod_of_cover γ hγ,
    Or.inl (center_eq_bot_of_equiv_sp4 (MulEquiv.ofBijective π hbij))⟩

theorem case3TwistBig_holds : Case3TwistBig := by
  intro V _ _ _ G L n _ _ hnat hL
  subst hL
  exact twoClassMod_centralData_of_binaryNaturalSp4 hnat

end CFSG.Quasithin.F918X
