module

public import CFSG.Quasithin.EmptyFaithful.SBd17I

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.exists_outer_action (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (ρ : ↥L →* projectiveSL 3 K)
      (φ : ↥I →* MulAut ↥L) (Φ : ↥I →* MulAut (projectiveSL 3 K)),
      Nat.card K = 4 ∧ SBd9.IsBorelModel L (Sgp153 T V₁ ⊓ L) ρ ∧ ρ.ker = Subgroup.center ↥L ∧
        (∀ (h : ↥I) (x : ↥L), ((φ h x : ↥L) : G) = (h : G) * (x : G) * (h : G)⁻¹) ∧
        (∀ (h : ↥I) (x : ↥L), Φ h (ρ x) = ρ (φ h x)) ∧
        ∀ g : ↥I, Φ g ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ↔
          (g : G) ∈ L := by
  classical
  obtain ⟨K, _, _, _, ρ, hK4, hmod⟩ := exists_borelModel r.ctx.c33.center_eq r.sylow r.hn2
  have hperf : Group.IsPerfect ↥L := r.ctx.c33.quasisimple.1
  have hLI : L ≤ I := r.L_le_I
  have hC : I ⊓ Subgroup.centralizer (L : Set G) ≤ L := by
    rw [r.centralizer_I_L h113]
    exact r.V₁_le_L h113
  obtain ⟨φ, Φ, hφ, hΦ⟩ := exists_induced_action hmod.surj hmod.ker_eq r.hNL
  refine ⟨K, inferInstance, inferInstance, inferInstance, ρ, φ, Φ, hK4, hmod, hmod.ker_eq, hφ, hΦ,
    fun g => ?_⟩
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨x₀, hx₀⟩ := exists_conj_of_induced_inner hmod.surj hmod.ker_eq hperf (φ g) (Φ g) (hΦ g)
      ⟨p, hp⟩
    have hcL : (x₀ : G)⁻¹ * (g : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 : (g : G) * y * (g : G)⁻¹ = (x₀ : G) * y * (x₀ : G)⁻¹ :=
        (hφ g ⟨y, hy⟩).symm.trans (congrArg (fun z : ↥L => (z : G)) (hx₀ ⟨y, hy⟩))
      calc y * ((x₀ : G)⁻¹ * (g : G)) = (x₀ : G)⁻¹ * ((x₀ : G) * y * (x₀ : G)⁻¹) * (g : G) := by
            group
        _ = (x₀ : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * (g : G) := by rw [← h1]
        _ = ((x₀ : G)⁻¹ * (g : G)) * y := by group
    have hcI : (x₀ : G)⁻¹ * (g : G) ∈ I := I.mul_mem (I.inv_mem (hLI x₀.2)) g.2
    have hcL' : (x₀ : G)⁻¹ * (g : G) ∈ L := hC ⟨hcI, hcL⟩
    have : (g : G) = (x₀ : G) * ((x₀ : G)⁻¹ * (g : G)) := by group
    rw [this]
    exact L.mul_mem x₀.2 hcL'
  · intro hg
    refine ⟨ρ ⟨(g : G), hg⟩, ?_⟩
    ext p
    obtain ⟨y, rfl⟩ := hmod.surj p
    have e : φ g y = ⟨(g : G), hg⟩ * y * ⟨(g : G), hg⟩⁻¹ := Subtype.ext (by rw [hφ]; rfl)
    rw [hΦ, e, MulAut.conj_apply, map_mul, map_mul, map_inv]

end CFSG.Quasithin.SBd14
