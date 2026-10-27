module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.TightEmbedding
public import CFSG.Quasithin.EmptyFaithful.S143IE
public import CFSG.Quasithin.EmptyFaithful.S143NM

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Tight
  CFSG.QuasithinUnique.BenderBranch CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Quasithin.S152O4

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c in
theorem exists_gam_model_idx :
    ∃ (cm : UT T M ≃* Vec) (ρ : Gam →* MulAut (UT T M)),
      Function.Injective ρ ∧ (∀ γ v, cm (ρ γ v) = act γ (cm v)) ∧
      (∀ (u : G) (hu : u ∈ uOfL22 T M), detQ (cm (tclsE c.hUN hu)) = 0 ↔ u * u = 1) ∧
      (∀ (n : G) (hn : n ∈ mcOf T), n ∈ oTwoUpper (mcOf T) →
        ∃ γ : Gam, γ ^ 3 = 1 ∧ c.actK ⟨n, hn⟩ = ρ γ) ∧
      ρ.range ≤ c.actK.range ∧ ρ.range.relIndex c.actK.range = 2 := by
  have h := c.h1281
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ := c.c15.orth
  let _ : CommGroup (UT T M) :=
    { (inferInstance : Group (UT T M)) with
      mul_comm := fun a b => (tilde_isMulCommutative h).is_comm.comm a b }
  have hrange : c.actK.range = orthogonalGroupOf q := c.actK_range.trans hq6
  have hexp : ∀ w : UT T M, w * w = 1 := tilde_mul_self h
  obtain ⟨U₁, U₂, hinf, hsup, φ₁, φ₂, hqe⟩ :=
    S153.exists_decomposition_of_plusType hexp hq4 hq1 hq2 hq3
  let cm : UT T M ≃* Vec := (S1417.coordEquiv hinf hsup φ₁ φ₂).trans kappa
  have hqc : ∀ v, q v = detQ (cm v) := by
    intro v
    rw [hqe v, quadOf_eq_qFloc hinf hsup φ₁ φ₂ v]
    exact qFloc_eq_detQ _
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType hexp hq4 hq1 hq2 hq3
  have hO72 : Nat.card (orthogonalGroupOf q) = 72 := hS.card_X
  have hOq : ∀ γ : Gam, rhoV cm γ ∈ orthogonalGroupOf q := by
    intro γ v
    rw [hqc, hqc, rhoV_apply, detQ_act]
  have hle : (rhoV cm).range ≤ orthogonalGroupOf q := by
    rintro _ ⟨γ, rfl⟩
    exact hOq γ
  have hR36 : Nat.card (rhoV cm).range = 36 := by
    rw [← card_Gam]
    exact (Nat.card_congr (MonoidHom.ofInjective (rhoV_injective cm)).toEquiv).symm
  have hrel : (rhoV cm).range.relIndex (orthogonalGroupOf q) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (rhoV cm).range (orthogonalGroupOf q)
    rw [inf_eq_left.mpr hle, hR36, hO72] at h1
    omega
  have hle' : (rhoV cm).range ≤ c.actK.range := by rw [hrange]; exact hle
  have hrel' : (rhoV cm).range.relIndex c.actK.range = 2 := by rw [hrange]; exact hrel
  refine ⟨cm, rhoV cm, rhoV_injective cm, fun γ v => rhoV_apply cm γ v, ?_, ?_, hle', hrel'⟩
  · intro u hu
    have := hq5 _ (tclsE c.hUN hu).2 ⟨u, c.hUN hu⟩ hu rfl
    rw [← hqc (tclsE c.hUN hu), pow_two] at *
    exact this
  · intro n hn hnN
    have h3 := c.actK_cube_of_mem_oTwoUpper (x := ⟨n, hn⟩) hnN
    have hmem : c.actK ⟨n, hn⟩ ∈ (rhoV cm).range :=
      mem_of_cube_of_relIndex_two hrel' ⟨⟨n, hn⟩, rfl⟩ h3
    obtain ⟨γ, hγ⟩ := hmem
    refine ⟨γ, ?_, hγ.symm⟩
    apply rhoV_injective cm
    rw [map_pow, hγ, h3, map_one]

end InspW2

end S143

end CFSG.Quasithin
