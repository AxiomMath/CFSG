module

public import CFSG.Monster.B.Dyadic.Beta

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Dyadic

open Module CFSG.Monster.B.Dyadic.Native CFSG.Monster.B.Binary.Native
open scoped Matrix

theorem mem_span_singleton_zmod2 {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x y : M) :
    x ∈ Submodule.span (ZMod 2) {y} ↔ x = 0 ∨ x = y := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℚ V]
  (R : Basis (Fin 4371) ℚ V) (ρ : G →* (V ≃ₗ[ℚ] V))

theorem fbar_ne_zero :
    fbar R ≠ 0 := by
  intro h
  apply fvec_ne_zero
  have := congrArg (bb R).equivFun h
  rwa [fbar, LinearEquiv.apply_symm_apply, map_zero] at this

theorem ker_Phi_eq_span :
    LinearMap.ker (Phi R) = Submodule.span (ZMod 2) {fbar R} := by
  ext x
  rw [mem_ker_Phi_iff, mem_span_singleton_zmod2 x (fbar R)]

theorem coordQ_mk_bb (k : Fin 4370) :
    coordQ R (Submodule.Quotient.mk (bb R (pIdx.succAbove k))) = Pi.single k 1 := by
  rw [← coordQ_symm_single, LinearEquiv.apply_symm_apply]

variable (hΛ : ∀ s, ∀ x ∈ Lam R, ρ s x ∈ Lam R)

theorem modRep_gens_bb
    (gens : Fin 26 → G)
    (hact : ∀ g t, (ρ (gens g) : V →ₗ[ℚ] V) (R t) =
      ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u) (g : Fin 26) (k : Fin 4371) :
    modRep R ρ hΛ (gens g) (bb R k) = ∑ l, Cmat g k l • bb R l :=
  modRep_gen_basis R ρ hΛ gens hact g k

theorem coords_modRep_gens
    (gens : Fin 26 → G)
    (hact : ∀ g t, (ρ (gens g) : V →ₗ[ℚ] V) (R t) =
      ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u) (g : Fin 26) (x : ModN (Lam R) 2) :
    (bb R).equivFun (modRep R ρ hΛ (gens g) x) = (bb R).equivFun x ᵥ* Cmat g := by
  have key : ∀ y : Fin 4371 → ZMod 2,
      modRep R ρ hΛ (gens g) (∑ k, y k • bb R k) = ∑ l, (y ᵥ* Cmat g) l • bb R l := by
    intro y
    rw [map_sum]
    simp_rw [map_smul, modRep_gens_bb R ρ hΛ gens hact, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul]
    rfl
  conv_lhs => rw [← (bb R).sum_equivFun x]
  rw [key, equivFun_sum]

theorem modRep_fixed_iff
    (gens : Fin 26 → G) (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (hact : ∀ g t, (ρ (gens g) : V →ₗ[ℚ] V) (R t) =
      ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u) (x : ModN (Lam R) 2) :
    (∀ s, modRep R ρ hΛ s x = x) ↔ x ∈ Submodule.span (ZMod 2) {fbar R} := by
  rw [mem_span_singleton_zmod2 x (fbar R)]
  constructor
  · intro hx
    have hy : ∀ g : Fin 26, (bb R).equivFun x ᵥ* Cmat g = (bb R).equivFun x := by
      intro g
      rw [← coords_modRep_gens R ρ hΛ gens hact, hx]
    rcases (fixed_vectors _).1 hy with h | h
    · left
      exact (bb R).equivFun.injective (by rw [h, map_zero])
    · right
      rw [fbar, ← h, LinearEquiv.symm_apply_apply]
  · rintro (rfl | rfl) s
    · exact map_zero _
    · exact fbar_fixed R ρ hΛ gens hgen hact s

theorem modRep_cofixed_iff
    (gens : Fin 26 → G)
    (hact : ∀ g t, (ρ (gens g) : V →ₗ[ℚ] V) (R t) =
      ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u)
    (φ : Module.Dual (ZMod 2) (ModN (Lam R) 2)) :
    (∀ s, φ ∘ₗ modRep R ρ hΛ s = φ) ↔ φ = 0 := by
  constructor
  · intro hφ
    have hx : ∀ g : Fin 26, Cmat g *ᵥ (fun k => φ (bb R k)) = fun k => φ (bb R k) := by
      intro g
      funext k
      have h := LinearMap.congr_fun (hφ (gens g)) (bb R k)
      rw [LinearMap.comp_apply, modRep_gens_bb R ρ hΛ gens hact, map_sum] at h
      rw [← h]
      simp only [map_smul, smul_eq_mul, Matrix.mulVec, dotProduct]
    have h0 := (fixed_covectors _).1 hx
    refine (bb R).ext fun k => ?_
    rw [LinearMap.zero_apply]
    exact congrFun h0 k
  · rintro rfl s
    exact LinearMap.zero_comp _

theorem quotRep_gens_basis
    (gens : Fin 26 → G)
    (hact : ∀ g t, (ρ (gens g) : V →ₗ[ℚ] V) (R t) =
      ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u)
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) (g : Fin 26) (j : Fin 4370) :
    coordQ R (quotRep R ρ hΛ hf (gens g) (Submodule.Quotient.mk (bb R (pIdx.succAbove j)))) =
      Qmat g j := by
  change coordQ R (quotEnd R ρ hΛ hf (gens g) (Submodule.Quotient.mk (bb R (pIdx.succAbove j)))) = _
  have he : (bb R).equivFun (bb R (pIdx.succAbove j)) = Pi.single (pIdx.succAbove j) 1 := by
    funext k
    rw [Basis.equivFun_self, Pi.single_apply]
    by_cases h : k = pIdx.succAbove j
    · subst h
      simp
    · simp [h, Ne.symm h]
  rw [quotEnd_mk, coordQ_mk, Phi_apply, coords_modRep_gens R ρ hΛ gens hact, quotient_action, he,
    Pmap_single, Matrix.single_one_vecMul]
  rfl

theorem coe_beta_eq
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) (s : G) :
    ((beta R ρ hΛ hf s : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) =
      LinearMap.toMatrix' ((coordQ R).toLinearMap ∘ₗ quotRep R ρ hΛ hf s ∘ₗ
        (coordQ R).symm.toLinearMap) := rfl

theorem beta_range_eq
    (gens : Fin 26 → G) (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (hact : ∀ g t, (ρ (gens g) : V →ₗ[ℚ] V) (R t) =
      ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u)
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) :
    (beta R ρ hΛ hf).range = Subgroup.closure {u : GL (Fin 4370) (ZMod 2) |
      ∃ g : Fin 26, (u : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = (Qmat g).transpose} := by
  rw [beta_range R ρ hΛ gens hgen hf]
  refine congrArg Subgroup.closure (Set.ext fun u => ?_)
  rw [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, beta_gen R ρ hΛ gens hact hf g⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Units.ext ((beta_gen R ρ hΛ gens hact hf g).trans hg.symm)⟩

end CFSG.Monster.B.Dyadic
