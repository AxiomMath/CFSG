module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitStruct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LargeExtraspecial.O62

theorem s16c15t_noTrans_of_natOmegaMinus {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {J : Subgroup W} (h : NatOmegaMinus H J ⊥ 6 1)
    {e : MulAut W} (he : e ∈ H) {c : W} (hc : c ≠ 1)
    (htr : ∀ x ∈ J, e x = x ∨ e x = x * c) : ∀ x ∈ J, e x = x := by
  classical
  obtain ⟨-, K, hK, hKf, b, c', hK2, hpoly, hReal⟩ := h
  letI := hK
  haveI : Finite K := hKf
  have hdiv : (6 : ℕ) / 2 = 3 := by norm_num
  rw [hdiv] at hReal
  obtain ⟨π, hπ⟩ := hReal
  let π' : ↥(StatedOmega (StatedQuadMinus 3 K b c')) →* ↥H := π
  have hπ' : (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b c'))).RealizesVia H J ⊥ π' := hπ
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ'
  obtain ⟨β, hβsurj, hβker, hβe⟩ := R.exists_β
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥J) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  let βe : ↥J ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :=
    MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩
  obtain ⟨θ, ψ, hψθ, hψΩ⟩ := s16c1_statedOmega_minus_model (K := K) (b := b) (c := c')
    (by simpa using hK2) hpoly
  let Φ : ↥J ≃* Multiplicative V₀ := βe.trans (AddEquiv.toMultiplicative θ)
  have hΦγ : ∀ (γ : ↥(StatedOmega (StatedQuadMinus 3 K b c'))) (u : ↥J),
      Φ ⟨((π' γ : ↥H) : MulAut W) u.1, R.U_inv (π' γ) u u.2⟩ =
        Multiplicative.ofAdd ((ψ (γ : GL _ K)) (Multiplicative.toAdd (Φ u))) := by
    intro γ u
    have h := hβe γ u (R.U_inv (π' γ) u u.2)
    have h1 : Multiplicative.toAdd (β ⟨((π' γ : ↥H) : MulAut W) u.1,
          R.U_inv (π' γ) u u.2⟩) =
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K (γ : GL _ K)
          (Multiplicative.toAdd (β u)) := by
      rw [h, CFSG.Quasithin.natAct, toAdd_ofAdd,
        ← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
    have hΦapp : Φ ⟨((π' γ : ↥H) : MulAut W) u.1, R.U_inv (π' γ) u u.2⟩ =
        Multiplicative.ofAdd (θ (Multiplicative.toAdd (β ⟨((π' γ : ↥H) : MulAut W) u.1,
          R.U_inv (π' γ) u u.2⟩))) := rfl
    have hΦu : Multiplicative.toAdd (Φ u) = θ (Multiplicative.toAdd (β u)) := rfl
    rw [hΦapp, h1, hψθ (γ : GL _ K), ← hΦu]
  by_cases htriv : ∀ x ∈ J, e x = x
  · exact htriv
  · obtain ⟨x₀, hx₀⟩ := not_forall.mp htriv
    obtain ⟨hx₀J, hx₀ne⟩ := not_imp.mp hx₀
    have hx₀c : e x₀ = x₀ * c := by
      rcases htr x₀ hx₀J with h' | h'
      · exact absurd h' hx₀ne
      · exact h'
    have hc_eq : c = x₀⁻¹ * e x₀ := by rw [hx₀c, inv_mul_cancel_left]
    have hcJ : c ∈ J := by
      rw [hc_eq]
      exact J.mul_mem (J.inv_mem hx₀J) (R.U_inv ⟨e, he⟩ x₀ hx₀J)
    obtain ⟨γ, hγe⟩ := R.surj ⟨e, he⟩
    let g : V₀ ≃ₗ[ZMod 2] V₀ := ψ (γ : GL _ K)
    have hgΩ : g ∈ Ω₀ true := (hψΩ g).2 ⟨(γ : GL _ K), γ.2, rfl⟩
    let w : V₀ := θ (Multiplicative.toAdd (β ⟨c, hcJ⟩))
    have hΦc : Φ ⟨c, hcJ⟩ = Multiplicative.ofAdd w := rfl
    have hcJne : (⟨c, hcJ⟩ : ↥J) ≠ 1 :=
      fun hh => hc (by simpa using congrArg Subtype.val hh)
    have hw : w ≠ 0 := by
      intro hw0
      apply hcJne
      apply Φ.injective
      simp [hΦc, hw0]
    have hΦe : ∀ y : ↥J,
        Φ ⟨e y.1, R.U_inv ⟨e, he⟩ y.1 y.2⟩ =
          Multiplicative.ofAdd (g (Multiplicative.toAdd (Φ y))) := by
      intro y
      have h := hΦγ γ y
      rw [hγe] at h
      exact h
    have hgtrans : ∀ v : V₀, g v = v ∨ g v = v + w := by
      intro v
      obtain ⟨y, hy⟩ := Φ.surjective (Multiplicative.ofAdd v)
      have hv : v = Multiplicative.toAdd (Φ y) := by rw [hy, toAdd_ofAdd]
      rcases htr y.1 y.2 with hy1 | hy1
      · left
        have h1 : (⟨e y.1, R.U_inv ⟨e, he⟩ y.1 y.2⟩ : ↥J) = y := Subtype.ext hy1
        have key : Multiplicative.ofAdd (g v) = Multiplicative.ofAdd v := by
          rw [hv, ← hΦe y, h1, hy]
          simp
        exact Multiplicative.ofAdd.injective key
      · right
        have h1 : (⟨e y.1, R.U_inv ⟨e, he⟩ y.1 y.2⟩ : ↥J) = y * ⟨c, hcJ⟩ := by
          apply Subtype.ext
          show e y.1 = y.1 * c
          rw [hy1]
        have key : Multiplicative.ofAdd (g v) = Multiplicative.ofAdd (v + w) := by
          rw [hv, ← hΦe y, h1, map_mul, hΦc, hy, toAdd_ofAdd, ← ofAdd_add]
        exact Multiplicative.ofAdd.injective key
    have hg1 : g = 1 := s16c1_omega0_noTrans hgΩ hw hgtrans
    intro x hxJ
    have h1 : Φ ⟨e x, R.U_inv ⟨e, he⟩ x hxJ⟩ = Φ ⟨x, hxJ⟩ := by
      have h := hΦe ⟨x, hxJ⟩
      rw [hg1] at h
      simpa using h
    exact congrArg Subtype.val (Φ.injective h1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
