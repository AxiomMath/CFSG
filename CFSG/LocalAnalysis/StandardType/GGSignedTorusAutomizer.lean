module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpAutomizer

public noncomputable section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly SpCoord Multiplicative

private theorem signed_automizer_coordinates {p : ℕ} {R : Type} [Group R] [Finite R]
    (E : Subgroup R) (τ : (Fin 3 → Multiplicative (ZMod p)) →* R)
    (κ : (Fin 3 → Multiplicative (ZMod p)) ≃* ↥E) (hκ : ∀ f, (κ f : R) = τ f)
    (hnorm : ∀ g : R, (∀ a ∈ E, g * a * g⁻¹ ∈ E) →
      ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i))
    {u : MulAut (Fin 3 → Multiplicative (ZMod p))}
    (hu : u ∈ (ggAutomizer (⊤ : Subgroup R) E).map (MulAut.congr κ.symm).toMonoidHom) :
    IsSignedPerm ⇑u := by
  obtain ⟨g, -, hgu⟩ := (mem_map_congr_ggAutomizer_iff E ⊤ κ u).mp hu
  obtain ⟨π, ε, hε, hact⟩ := hnorm g (by
    intro a ha
    obtain ⟨f, hf⟩ := κ.surjective ⟨a, ha⟩
    have hfa : (κ f : R) = a := congrArg Subtype.val hf
    rw [← hfa, hgu f]
    exact (κ (u f)).2)
  exact ⟨π, ε, hε, fun f i => hact f (u f) (by simpa only [hκ] using hgu f) i⟩

private theorem signed_simple_isReflection {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Type} [Group R] {E : Subgroup R}
    (κ : (Fin 3 → Multiplicative (ZMod p)) ≃* ↥E) (i : Fin 3) :
    GGIsReflection p (MulAut.congr κ (ggSpSigned_spReflAut p 3 i)) := by
  by_cases hi : i.val + 1 < 3
  · rw [ggSpSigned_spReflAut, dif_pos hi]
    have hne : i ≠ (⟨i.val + 1, hi⟩ : Fin 3) := by
      intro h
      have : i.val = i.val + 1 := congrArg Fin.val h
      omega
    exact ggSpSigned_ggIsReflection_congr hp hp2 κ
      (permAut_swap_sq i ⟨i.val + 1, hi⟩) (card_fix_permAut_swap hp hp2 hne)
  · rw [ggSpSigned_spReflAut, dif_neg hi]
    exact ggSpSigned_ggIsReflection_congr hp hp2 κ (sgnAut_sq i)
      (card_fix_sgnAut hp hp2 i)

theorem exists_coxeterB_three_automizer_of_torus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Type} [Group R] [Finite R] (E : Subgroup R)
    (τ : (Fin 3 → Multiplicative (ZMod p)) →* R)
    (hτinj : Function.Injective τ) (hτrange : τ.range = E)
    (hsgn : ∀ i : Fin 3, ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f))
    (hperm : ∀ σ : Equiv.Perm (Fin 3), ∃ w : R,
      ∀ f, w * τ f * w⁻¹ = τ (permAut σ f))
    (hnorm : ∀ g : R, (∀ a ∈ E, g * a * g⁻¹ ∈ E) →
      ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) :
    ∃ e : (CoxeterMatrix.B 3).Group ≃* ↥(ggAutomizer (⊤ : Subgroup R) E),
      ∀ i, GGIsReflection p (e ((CoxeterMatrix.B 3).simple i) : MulAut ↥E) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let κ : (Fin 3 → Multiplicative (ZMod p)) ≃* ↥E :=
    (MonoidHom.ofInjective hτinj).trans (MulEquiv.subgroupCongr hτrange)
  have hκ : ∀ f, (κ f : R) = τ f := fun _ => rfl
  let H : Subgroup (MulAut (Fin 3 → Multiplicative (ZMod p))) :=
    (ggAutomizer (⊤ : Subgroup R) E).map (MulAut.congr κ.symm).toMonoidHom
  have hsgnH : ∀ i, sgnAut i ∈ H := by
    intro i
    obtain ⟨w, hw⟩ := hsgn i
    refine (mem_map_congr_ggAutomizer_iff E ⊤ κ (sgnAut i)).mpr
      ⟨w, Subgroup.mem_top _, ?_⟩
    intro f
    simpa only [hκ] using hw f
  have hpermH : ∀ σ, permAut σ ∈ H := by
    intro σ
    obtain ⟨w, hw⟩ := hperm σ
    refine (mem_map_congr_ggAutomizer_iff E ⊤ κ (permAut σ)).mpr
      ⟨w, Subgroup.mem_top _, ?_⟩
    intro f
    simpa only [hκ] using hw f
  have hsigned : ∀ u ∈ H, IsSignedPerm ⇑u := by
    intro u hu
    exact signed_automizer_coordinates E τ κ hκ hnorm hu
  let φ : Fin 3 → MulAut (Fin 3 → Multiplicative (ZMod p)) :=
    ggSpSigned_spReflAut p 3
  let gen : Fin 3 → ↥(SpJoin.spSignedGroup 3 p) := fun i =>
    ⟨SpJoin.spReflPerm 3 p i, SpJoin.spReflPerm_mem_spSignedGroup 3 p i⟩
  have htop : Subgroup.closure (Set.range gen) = ⊤ :=
    ggSpSigned_closure_range_subtype (SpJoin.spReflPerm 3 p)
      (fun i => SpJoin.spReflPerm_mem_spSignedGroup 3 p i) rfl
  have hrange : (ggSpSigned_rho p 3).range = Subgroup.closure (Set.range φ) := by
    rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
    congr 1
    ext u
    constructor
    · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (ggSpSigned_rho_spReflPerm p 3 i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨gen i, ⟨i, rfl⟩, ggSpSigned_rho_spReflPerm p 3 i⟩
  have hFull : H = (ggSpSigned_rho p 3).range := by
    apply le_antisymm
    · intro u hu
      exact ggSpSigned_isSignedPerm_mem_range (by decide : 1 ≤ 3) (hsigned u hu)
    · rw [hrange, Subgroup.closure_le]
      rintro u ⟨i, rfl⟩
      change φ i ∈ H
      by_cases hi : i.val + 1 < 3
      · simpa only [φ, ggSpSigned_spReflAut, dif_pos hi] using
          hpermH (Equiv.swap i ⟨i.val + 1, hi⟩)
      · simpa only [φ, ggSpSigned_spReflAut, dif_neg hi] using hsgnH i
  obtain ⟨e, he⟩ := ggTBJ_sp_coxeter_of_coordinates hp hp2 κ hFull
  refine ⟨e, fun i => ?_⟩
  rw [he i]
  exact signed_simple_isReflection hp hp2 κ i

end CFSG.StandardType

end
