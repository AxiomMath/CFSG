module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Data
public import CFSG.Quasithin.Background.GoldschmidtE23SymFin
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique G6 Equiv

namespace GE23

section Spec

variable {V : Type} [CommGroup V]

structure SymSpec (H D : Subgroup (MulAut V)) (ψ : Perm (Fin 5) →* MulAut V)
    (β : ↥(coreMod 5) →* V) : Prop where
  ψ_inj : Function.Injective ψ
  ψ_range : ψ.range = H
  β_inj : Function.Injective β
  β_range : β.range = commV H
  equiv : ∀ (σ : Perm (Fin 5)) (u : ↥(coreMod 5)), β (coreAct 5 σ u) = ψ σ (β u)
  syl : D = d8.map ψ

theorem eq_one_of_coreAct_trivial (ρ : Perm (Fin 5)) (h : ∀ u : ↥(coreMod 5), coreAct 5 ρ u = u) :
    ρ = 1 := by
  refine eq_one_of_fixed_all ρ fun y hy i => ?_
  have := (coreAct_eq_iff).1 (h (ofVec y hy)) i
  exact this

theorem eq_one_of_coreAct_fixed (u : ↥(coreMod 5)) (h : ∀ σ : Perm (Fin 5), coreAct 5 σ u = u) :
    u = 1 := by
  have hu0 : vecOf u = 0 :=
    fixed_by_all (vecOf u) (sum_vecOf u) fun σ i => (coreAct_eq_iff).1 (h σ) i
  apply vecOf_injective
  rw [hu0]
  rfl

namespace SymSpec

variable {H D : Subgroup (MulAut V)} {ψ : Perm (Fin 5) →* MulAut V} {β : ↥(coreMod 5) →* V}
  (h : SymSpec H D ψ β)

include h

theorem ψ_mem (σ : Perm (Fin 5)) : ψ σ ∈ H := h.ψ_range ▸ MonoidHom.mem_range.2 ⟨σ, rfl⟩

theorem exists_ψ {x : MulAut V} (hx : x ∈ H) : ∃ σ, ψ σ = x := by
  have : x ∈ ψ.range := h.ψ_range ▸ hx
  exact MonoidHom.mem_range.1 this

theorem β_mem (u : ↥(coreMod 5)) : β u ∈ commV H := h.β_range ▸ MonoidHom.mem_range.2 ⟨u, rfl⟩

theorem exists_β {v : V} (hv : v ∈ commV H) : ∃ u, β u = v := by
  have : v ∈ β.range := h.β_range ▸ hv
  exact MonoidHom.mem_range.1 this

theorem stab {x : MulAut V} (hx : x ∈ H) {v : V} (hv : v ∈ commV H) : x v ∈ commV H :=
  CFSG.Quasithin.commV_apply_mem_of_mem hx hv

theorem faithful {σ τ : Perm (Fin 5)} (hst : ∀ u : ↥(coreMod 5), ψ σ (β u) = ψ τ (β u)) :
    σ = τ := by
  have h1 : ∀ u : ↥(coreMod 5), coreAct 5 σ u = coreAct 5 τ u := fun u =>
    h.β_inj (by rw [h.equiv, h.equiv]; exact hst u)
  have h2 : τ⁻¹ * σ = 1 := by
    refine eq_one_of_coreAct_trivial _ fun u => ?_
    rw [map_mul, MulAut.mul_apply, h1 u, map_inv]
    exact MulAut.inv_apply_self _ _ _
  exact (inv_mul_eq_one.1 h2).symm

theorem eq_of_act {x y : MulAut V} (hx : x ∈ H) (hy : y ∈ H)
    (hxy : ∀ v ∈ commV H, x v = y v) : x = y := by
  obtain ⟨σ, rfl⟩ := h.exists_ψ hx
  obtain ⟨τ, rfl⟩ := h.exists_ψ hy
  rw [h.faithful (fun u => hxy _ (h.β_mem u))]

theorem fixed_trivial {v : V} (hv : v ∈ commV H) (hfix : ∀ x ∈ H, x v = v) : v = 1 := by
  obtain ⟨u, rfl⟩ := h.exists_β hv
  have : u = 1 := by
    refine eq_one_of_coreAct_fixed u fun σ => h.β_inj ?_
    rw [h.equiv]
    exact hfix _ (h.ψ_mem σ)
  rw [this, map_one]

theorem card_commV : Nat.card ↥(commV H) = 16 := by
  have e : ↥(coreMod 5) ≃* ↥β.range := MonoidHom.ofInjective h.β_inj
  have : Nat.card ↥β.range = 16 := by rw [← Nat.card_congr e.toEquiv]; exact card_coreMod
  rwa [h.β_range] at this

theorem D_le : D ≤ H := by
  rw [h.syl]
  rintro x ⟨σ, -, rfl⟩
  exact h.ψ_mem σ

theorem fix_map {R : Subgroup (Perm (Fin 5))} {u : ↥(coreMod 5)} :
    β u ∈ fixV (R.map ψ) ↔ u ∈ fixΔ R := by
  constructor
  · intro hu σ hσ
    apply h.β_inj
    rw [h.equiv]
    exact hu _ (Subgroup.mem_map_of_mem ψ hσ)
  · intro hu x hx
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← h.equiv, hu σ hσ]

theorem inf_fixV_map {R : Subgroup (Perm (Fin 5))} :
    commV H ⊓ fixV (R.map ψ) = (fixΔ R).map β := by
  ext v
  constructor
  · rintro ⟨hv, hf⟩
    obtain ⟨u, rfl⟩ := h.exists_β hv
    exact ⟨u, (h.fix_map).1 hf, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨h.β_mem u, (h.fix_map).2 hu⟩

theorem card_fix_map [Finite V] {R : Subgroup (Perm (Fin 5))} :
    Nat.card ↥(commV H ⊓ fixV (R.map ψ)) = Nat.card ↥(fixΔ R) := by
  rw [h.inf_fixV_map]
  exact Subgroup.card_map_of_injective h.β_inj

end SymSpec

end Spec

end GE23

end CFSG.Quasithin
