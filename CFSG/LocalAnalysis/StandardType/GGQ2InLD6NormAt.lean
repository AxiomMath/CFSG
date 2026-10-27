module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLD6Mon
public import CFSG.LocalAnalysis.StandardType.GGQTwoD6Group
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace QTwoD6

private lemma qd6n_lin_coroot {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {y : G}
    {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {hy : y ∈ Bs} (Fr : GGQ2D6Frame N b hy)
    (φ : MulAut ↥Bs) (i : Fin 6) :
    ggLin (p := 3) N.model φ (N.coroot (Fr.e i)) = Fr.F.symm (ggCoord N Fr.F φ (hvec i)) := by
  rw [ggQ2_d6_coord_apply, Fr.F.symm_apply_apply]
  congr 1
  apply Fr.F.injective
  rw [Fr.F_coroot, LinearEquiv.apply_symm_apply]

private lemma qd6n_cartanD6_swap (a b : Fin 6) :
    cartanD6 (swapD6 a) (swapD6 b) = cartanD6 a b := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem ggQ2_normAt_of_d6Datum (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) (hAJ : ggAutomizer J Bs ≠ ⊥)
    {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K) (hy : y ∈ Bs)
    (N : GGQ2NbrDatum 3 Bs K) (b : N.Λ) (hb : N.IsD6Fork b) : N.NormAt y := by
  intro u hu hfix hyV φ hφ hstep
  have _ := hfix
  have _ := hyV
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hS.1 hI1
  have hu' : u = (⟨y, hy⟩ : ↥Bs) := Subtype.ext hu
  subst u
  obtain ⟨Fr⟩ := ggQ2_d6_frame hnb N b hb hK1 hy
  have hmap : (ggAutomizer K Bs).map (ggCoord N Fr.F) = W6 := by
    have himg : (ggCoord N Fr.F) '' Set.range N.simple = Set.range simpleD6 := by
      ext t
      constructor
      · rintro ⟨s, ⟨i, rfl⟩, rfl⟩
        refine ⟨Fr.e.symm i, ?_⟩
        have h := ggQ2_d6_coord_simple Fr (Fr.e.symm i)
        rw [Fr.e.apply_symm_apply i] at h
        exact h.symm
      · rintro ⟨j, rfl⟩
        exact ⟨N.simple (Fr.e j), ⟨Fr.e j, rfl⟩, ggQ2_d6_coord_simple Fr j⟩
    rw [N.automizer_K, MonoidHom.map_closure, himg]
    rfl
  have hφy : φ ⟨y, hy⟩ ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) :=
    (ggQ2d6_model_span_iff (p := 3) N.model hy (φ ⟨y, hy⟩)).mp
      (by simpa only [ggLin_apply_ofMul] using hstep)
  have hφnorm : φ ∈ Subgroup.normalizer (ggAutomizer K Bs : Set (MulAut ↥Bs)) :=
    ggQ2_nbrLineStab_normalizes hLB hP hS.1 hAJ hK1 hnb hy hφ hφy
  have hT : ∀ g : V7 ≃ₗ[ZMod 3] V7,
      g ∈ W6 ↔ ggCoord N Fr.F φ * g * (ggCoord N Fr.F φ)⁻¹ ∈ W6 := by
    intro g
    constructor
    · intro hg
      rw [← hmap] at hg
      obtain ⟨ψ, hψ, hψeq⟩ := Subgroup.mem_map.mp hg
      have h1 : φ * ψ * φ⁻¹ ∈ ggAutomizer K Bs :=
        (Subgroup.mem_normalizer_iff.mp hφnorm ψ).mp hψ
      rw [← hmap]
      refine Subgroup.mem_map.mpr ⟨φ * ψ * φ⁻¹, h1, ?_⟩
      rw [map_mul, map_mul, map_inv, hψeq]
    · intro hg
      rw [← hmap] at hg
      obtain ⟨ρ, hρ, hρeq⟩ := Subgroup.mem_map.mp hg
      have h2 : φ⁻¹ * ρ * φ ∈ ggAutomizer K Bs := by
        refine (Subgroup.mem_normalizer_iff.mp hφnorm (φ⁻¹ * ρ * φ)).mpr ?_
        have hρ' : φ * (φ⁻¹ * ρ * φ) * φ⁻¹ = ρ := by group
        rwa [hρ']
      rw [← hmap]
      refine Subgroup.mem_map.mpr ⟨φ⁻¹ * ρ * φ, h2, ?_⟩
      rw [map_mul, map_mul, map_inv, hρeq]
      group
  have hT0 : ggCoord N Fr.F φ e0 ∈ Submodule.span (ZMod 3) {e0} := by
    obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp hstep
    have h1 : ggCoord N Fr.F φ e0 = c₀ • e0 := by
      rw [ggQ2_d6_coord_apply,
        show Fr.F.symm e0 = N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) from by
          rw [← Fr.F_y, LinearEquiv.symm_apply_apply],
        ← hc₀, map_smul, Fr.F_y]
    rw [h1]
    exact Submodule.smul_mem _ c₀ (Submodule.mem_span_singleton_self e0)
  obtain ⟨w, hw, π, hπ, hTapply⟩ :=
    w6_normalizer_normal_form (ggCoord N Fr.F φ) hT hT0
  rw [← hmap] at hw
  obtain ⟨ψ, hψ, hψeq⟩ := Subgroup.mem_map.mp hw
  let π' : N.Λ ≃ N.Λ := Fr.e.symm.trans (π.trans Fr.e)
  have hπ'e : ∀ a : Fin 6, π' (Fr.e a) = Fr.e (π a) := by
    intro a
    change (Fr.e.symm.trans (π.trans Fr.e)) (Fr.e a) = Fr.e (π a)
    rw [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.trans_apply]
  have hcartFr : ∀ i j : Fin 6, N.cartan (Fr.e i) (Fr.e j) = cartanD6 i j :=
    ggQ2d6_cartan_reindex N Fr.e Fr.coxeter_eq
  have hcartπ : ∀ a b : Fin 6, cartanD6 (π a) (π b) = cartanD6 a b := by
    rcases hπ with rfl | rfl
    · intro a b; rfl
    · exact qd6n_cartanD6_swap
  refine ⟨π', (fun _ : N.Λ => 1), 1, one_ne_zero, (fun _ => one_ne_zero), ?_, ?_⟩
  · intro i j
    have hZ : N.cartan i j = N.cartan (π' i) (π' j) := by
      obtain ⟨a, rfl⟩ := Fr.e.surjective i
      obtain ⟨b, rfl⟩ := Fr.e.surjective j
      rw [hπ'e a, hπ'e b, hcartFr (π a) (π b), hcartFr a b, hcartπ a b]
    have := congrArg (fun z : ℤ => (z : ZMod 3)) hZ
    simpa only [one_mul] using this
  · refine ⟨ggLin (p := 3) N.model ψ, Subgroup.mem_map.mpr ⟨ψ, hψ, rfl⟩, ?_⟩
    intro i
    simp only [one_smul]
    obtain ⟨a, rfl⟩ := Fr.e.surjective i
    rw [hπ'e a]
    calc ggLin (p := 3) N.model φ (N.coroot (Fr.e a))
        = Fr.F.symm (ggCoord N Fr.F φ (hvec a)) := qd6n_lin_coroot Fr φ a
      _ = Fr.F.symm (w (hvec (π a))) := by rw [hTapply a]
      _ = Fr.F.symm (ggCoord N Fr.F ψ (hvec (π a))) := by rw [hψeq]
      _ = ggLin (p := 3) N.model ψ (N.coroot (Fr.e (π a))) :=
            (qd6n_lin_coroot Fr ψ (π a)).symm

end QTwoD6

end CFSG.StandardType

end
