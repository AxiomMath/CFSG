module

public import CFSG.Quasithin.Background.GoldschmidtD35CoreFrame
public import CFSG.Quasithin.Background.GoldschmidtD35CoreGeom

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 Equiv
open scoped LinearAlgebra.Projectivization

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {L : Subgroup (V ≃ₗ[F] V)} {pt : Fin 6 → ℙ F V}

theorem IsSixOrbit.scalar_of_fixes (hV : Module.finrank F V = 3) (hO : IsSixOrbit L pt)
    (hirr : ∀ W : Submodule F V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    {g : V ≃ₗ[F] V} {a b c d : Fin 6} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (ha : lineAction F V g (pt a) = pt a)
    (hb : lineAction F V g (pt b) = pt b) (hc : lineAction F V g (pt c) = pt c)
    (hd : lineAction F V g (pt d) = pt d) : ∃ c₀ : F, ∀ v, g v = c₀ • v := by
  obtain ⟨ca, -, ea⟩ := exists_smul_rep ha
  obtain ⟨cb, -, eb⟩ := exists_smul_rep hb
  obtain ⟨cc, -, ec⟩ := exists_smul_rep hc
  obtain ⟨cd, -, ed⟩ := exists_smul_rep hd
  have h3 : ∀ {i j k : Fin 6}, i ≠ j → i ≠ k → j ≠ k →
      LinearIndependent F ![(pt i).rep, (pt j).rep, (pt k).rep] :=
    fun hij hik hjk => hO.linearIndependent_three hV hirr hij hik hjk
  have := eq_smul_of_frame hV (h3 hab hac hbc) (h3 hab had hbd) (h3 hac had hcd) (h3 hbc hbd hcd)
    (g : V →ₗ[F] V) ea eb ec ed
  exact ⟨cd, fun v => by simpa using LinearMap.congr_fun this v⟩

omit [FiniteDimensional F V] in
theorem lineAction_of_smul {g : V ≃ₗ[F] V} {c : F} (hc : ∀ v, g v = c • v) (p : ℙ F V) :
    lineAction F V g p = p := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply p.rep_nonzero
    apply g.injective
    rw [hc, zero_smul, map_zero]
  have : g = scalarHom F V (Units.mk0 c hc0) := LinearEquiv.ext fun v => by
    rw [hc, scalarHom_apply]
    rfl
  rw [this]
  exact lineAction_scalar _ p

omit [FiniteDimensional F V] in
theorem IsSixOrbit.exists_perm (hO : IsSixOrbit L pt) {g : V ≃ₗ[F] V}
    (hg : ∀ i, ∃ j, lineAction F V g (pt i) = pt j) :
    ∃ π : Perm (Fin 6), ∀ i, lineAction F V g (pt i) = pt (π i) := by
  choose f hf using hg
  have hinj : Function.Injective f := fun i i' h => by
    apply hO.inj
    apply (lineAction F V g).injective
    rw [hf, hf, h]
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

theorem IsSixOrbit.even_of_preserves (hV : Module.finrank F V = 3) (hO : IsSixOrbit L pt)
    (hirr : ∀ W : Submodule F V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    {g : V ≃ₗ[F] V} {π : Perm (Fin 6)} (hg : ∀ i, lineAction F V g (pt i) = pt (π i)) :
    π ∈ alternatingGroup (Fin 6) := by
  by_contra hodd
  have h1 : Perm.sign π = -1 := by
    rcases Int.units_eq_one_or (Perm.sign π) with h | h
    · exact absurd (Perm.mem_alternatingGroup.2 h) hodd
    · exact h
  have hρ : π⁻¹ * swap 0 1 ∈ alternatingGroup (Fin 6) := by
    rw [Perm.mem_alternatingGroup, map_mul, map_inv, h1, Perm.sign_swap (by decide)]
    decide
  obtain ⟨l, hl, hlρ⟩ := (hO.alt _).1 hρ
  have hgl : ∀ i, lineAction F V (g * l) (pt i) = pt (swap 0 1 i) := by
    intro i
    rw [map_mul, Perm.mul_apply, hlρ, hg]
    simp
  obtain ⟨c, hc⟩ := hO.scalar_of_fixes hV hirr (g := g * l) (a := 2) (b := 3) (c := 4) (d := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hgl, swap_apply_of_ne_of_ne (by decide) (by decide)])
    (by rw [hgl, swap_apply_of_ne_of_ne (by decide) (by decide)])
    (by rw [hgl, swap_apply_of_ne_of_ne (by decide) (by decide)])
    (by rw [hgl, swap_apply_of_ne_of_ne (by decide) (by decide)])
  have h0 := lineAction_of_smul hc (pt 0)
  rw [hgl] at h0
  have := hO.inj h0
  revert this
  decide

theorem IsSixOrbit.mem_of_preserves (hV : Module.finrank F V = 3) (hO : IsSixOrbit L pt)
    (hirr : ∀ W : Submodule F V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hscal : ∀ c : Fˣ, scalarHom F V c ∈ L) {g : V ≃ₗ[F] V}
    (hg : ∀ i, ∃ j, lineAction F V g (pt i) = pt j) : g ∈ L := by
  obtain ⟨π, hπ⟩ := hO.exists_perm hg
  obtain ⟨l, hl, hlπ⟩ := (hO.alt π).1 (hO.even_of_preserves hV hirr hπ)
  have hfix : ∀ i, lineAction F V (l⁻¹ * g) (pt i) = pt i := by
    intro i
    rw [map_mul, Perm.mul_apply, hπ, ← hlπ, ← Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  obtain ⟨c, hc⟩ := hO.scalar_of_fixes hV hirr (g := l⁻¹ * g) (a := 0) (b := 1) (c := 2) (d := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hfix 0) (hfix 1)
    (hfix 2) (hfix 3)
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank F V)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    apply (l⁻¹ * g).injective
    rw [hc, zero_smul, map_zero]
  have hmem : l⁻¹ * g ∈ L := by
    have : l⁻¹ * g = scalarHom F V (Units.mk0 c hc0) := LinearEquiv.ext fun v => by
      rw [hc, scalarHom_apply]
      rfl
    rw [this]
    exact hscal _
  simpa using L.mul_mem hl hmem

end CFSG.Quasithin.D35Core
