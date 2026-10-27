module

public import CFSG.RankThree.GF2n.Smith81.S81QCoreFix

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


section Char

variable {K : Type} [Field K] [CharP K 2] [Finite K] {X : Type} [AddCommGroup X] [Module K X]

theorem scalar_mul0 (B : ↥(EAut0 K) →* (X ≃ₗ[K] X)) {v₀ : X} (hne : v₀ ≠ 0)
    {g₁ g₂ : ↥(EAut0 K)} {c₁ c₂ c : K} (h₁ : B g₁ v₀ = c₁ • v₀) (h₂ : B g₂ v₀ = c₂ • v₀)
    (h : B (g₁ * g₂) v₀ = c • v₀) : c = c₁ * c₂ := by
  rw [map_mul, LinearEquiv.mul_apply, h₂, map_smul, h₁, smul_smul] at h
  exact smul_left_injective K hne (h.symm.trans (by rw [mul_comm]))

variable (B : ↥(EAut0 K) →* (X ≃ₗ[K] X)) (hline : Module.finrank K (fix0 B) = 1) {v₀ : X}
  (hv₀ : v₀ ∈ fix0 B) (hne : v₀ ≠ 0)

include hline hv₀ hne

theorem exists_scalar_of_stab {g : ↥(EAut0 K)} (hg : g ∈ StabP0 K) :
    ∃ c : K, c ≠ 0 ∧ B g v₀ = c • v₀ := by
  have hmem : B g v₀ ∈ fix0 B := fix0_map_le_of_mem_StabP0 B hg (Submodule.mem_map_of_mem hv₀)
  have hnz : (⟨v₀, hv₀⟩ : ↥(fix0 B)) ≠ 0 := fun h => hne (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hline hnz ⟨B g v₀, hmem⟩
  have hc' : c • v₀ = B g v₀ := congrArg Subtype.val hc
  refine ⟨c, ?_, hc'.symm⟩
  rintro rfl
  rw [zero_smul] at hc'
  exact hne ((B g).injective (by rw [← hc', map_zero]))

noncomputable def charOf0 : ↥(StabP0 K) →* Kˣ :=
  MonoidHom.mk'
    (fun h => Units.mk0 (Classical.choose (exists_scalar_of_stab B hline hv₀ hne h.2))
      (Classical.choose_spec (exists_scalar_of_stab B hline hv₀ hne h.2)).1)
    (fun h h' => by
      apply Units.ext
      set c := Classical.choose (exists_scalar_of_stab B hline hv₀ hne (h * h').2) with hc
      set c₁ := Classical.choose (exists_scalar_of_stab B hline hv₀ hne h.2) with hc₁
      set c₂ := Classical.choose (exists_scalar_of_stab B hline hv₀ hne h'.2) with hc₂
      have e := (Classical.choose_spec (exists_scalar_of_stab B hline hv₀ hne (h * h').2)).2
      have e1 := (Classical.choose_spec (exists_scalar_of_stab B hline hv₀ hne h.2)).2
      have e2 := (Classical.choose_spec (exists_scalar_of_stab B hline hv₀ hne h'.2)).2
      exact scalar_mul0 B hne e1 e2 e)

theorem charOf0_spec (h : ↥(StabP0 K)) :
    B (h : ↥(EAut0 K)) v₀ = ((charOf0 B hline hv₀ hne h : Kˣ) : K) • v₀ :=
  (Classical.choose_spec (exists_scalar_of_stab B hline hv₀ hne h.2)).2

omit hline hv₀ hne

theorem hhom_E4 (hChar : E4StabChar K) (B : ↥(EAut0 K) →* (X ≃ₗ[K] X))
    (hline : Module.finrank K (fix0 B) = 1) {v₀ : X} (hv₀ : v₀ ∈ fix0 B) (hne : v₀ ≠ 0)
    (hd : ∀ c : Kˣ, B (d0Hom K c) v₀ = (c : K) • v₀)
    {g g' : ↥(EAut0 K)} {c : K} (hc : c ≠ 0)
    (h : (g : W K ≃ₗ[K] W K) (p0 K) = c • (g' : W K ≃ₗ[K] W K) (p0 K)) :
    B g v₀ = c • B g' v₀ := by
  set p : ↥(EAut0 K) := g'⁻¹ * g with hp
  have hpw : (p : W K ≃ₗ[K] W K) (p0 K) = c • p0 K := by
    show ((g' : W K ≃ₗ[K] W K)⁻¹ * (g : W K ≃ₗ[K] W K)) (p0 K) = _
    rw [LinearEquiv.mul_apply, h, map_smul]
    congr 1
    exact LinearEquiv.symm_apply_apply _ _
  let χ := charOf0 B hline hv₀ hne
  have hχd : ∀ c : Kˣ, χ (d0 K c) = c := by
    intro c
    apply Units.ext
    have h1 := charOf0_spec B hline hv₀ hne (d0 K c)
    have h2 : B ((d0 K c : ↥(StabP0 K)) : ↥(EAut0 K)) v₀ = (c : K) • v₀ := hd c
    rw [h2] at h1
    exact (smul_left_injective K hne h1).symm
  let q : ↥(StabP0 K) := ⟨p, c, hc, hpw⟩
  have hC := hChar χ hχd q
  have hχq : ((χ q : Kˣ) : K) = c := by
    have h1 : ((q : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K) = c • p0 K := hpw
    rw [h1] at hC
    exact (smul_left_injective K p0_ne_zero hC).symm
  have hBp : B p v₀ = c • v₀ := by
    have := charOf0_spec B hline hv₀ hne q
    rw [hχq] at this
    exact this
  calc B g v₀ = B (g' * p) v₀ := by rw [hp, mul_inv_cancel_left]
    _ = B g' (B p v₀) := by rw [map_mul, LinearEquiv.mul_apply]
    _ = c • B g' v₀ := by rw [hBp, map_smul]

end Char

end CFSG.RankThree.GF2n.Smith81.D6Spin
