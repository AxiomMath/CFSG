module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3SixPointC

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 Equiv
open scoped LinearAlgebra.Projectivization

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

structure IsSixOrbit (L : Subgroup (V ≃ₗ[F] V)) (pt : Fin 6 → ℙ F V) : Prop where
  inj : Function.Injective pt
  mem : ∀ g ∈ L, ∀ i, ∃ j, lineAction F V g (pt i) = pt j
  alt : ∀ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) ↔
    ∃ g ∈ L, ∀ i, lineAction F V g (pt i) = pt (σ i)

open scoped Classical in
theorem exists_isSixOrbit [Finite F] [Module.Finite F V] {L : Subgroup (V ≃ₗ[F] V)}
    (hD : ThreeQuaternaryData F V L) : ∃ pt : Fin 6 → ℙ F V, IsSixOrbit L pt := by
  have hP : Nat.card (ℙ F V) = 21 := card_points hD.card_field hD.finrank_eq
  have : Finite (ℙ F V) := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype (ℙ F V) := Fintype.ofFinite _
  obtain ⟨x, y, hx, hy, hcov, θ, hθ, hker, himg, -⟩ := three_quaternary_normalizer_six_point hD
  have hLN : ∀ g ∈ L, toGamma F V g ∈ semilinearNormalizer L := fun g hg =>
    Subgroup.le_normalizer (Subgroup.mem_map_of_mem _ hg)
  have hcard : Nat.card (lineOrbit L x) = 6 := by rw [Nat.card_coe_set_eq]; exact hx
  let e : Fin 6 ≃ lineOrbit L x := (Finite.equivFinOfCardEq hcard).symm
  have hmem : ∀ g ∈ L, ∀ p ∈ lineOrbit L x, lineAction F V g p ∈ lineOrbit L x := by
    intro g hg p hp
    obtain ⟨h, hh, rfl⟩ := (mem_lineOrbit_iff x p).1 hp
    exact (mem_lineOrbit_iff x _).2 ⟨g * h, L.mul_mem hg hh, by simp⟩
  refine ⟨fun i => (e i : ℙ F V), fun i j hij => e.injective (Subtype.ext hij),
    fun g hg i => ⟨e.symm ⟨_, hmem g hg _ (e i).2⟩, by simp⟩, fun σ => ?_⟩
  have hsign : σ ∈ alternatingGroup (Fin 6) ↔ e.permCongr σ ∈ alternatingGroup (lineOrbit L x) := by
    simp [Equiv.Perm.mem_alternatingGroup]
  rw [hsign, ← himg]
  constructor
  · rintro ⟨n, hn, hnσ⟩
    obtain ⟨g, hg, hgn⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
    refine ⟨g, hg, fun i => ?_⟩
    have := congrArg (fun τ : Perm (lineOrbit L x) => (τ (e i) : ℙ F V)) hnσ
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply] at this
    rw [hθ, ← hgn] at this
    exact this
  · rintro ⟨g, hg, hgσ⟩
    refine ⟨⟨toGamma F V g, hLN g hg⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ hg),
      ?_⟩
    refine Equiv.ext fun p => Subtype.ext ?_
    obtain ⟨i, rfl⟩ := e.surjective p
    rw [hθ]
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    exact hgσ i

end CFSG.Quasithin.D35Core
