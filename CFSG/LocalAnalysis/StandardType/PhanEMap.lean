module

public import CFSG.LocalAnalysis.StandardType.PhanEBridgeDefs

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

section Map

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {n : ℕ} {M : CoxeterMatrix (Fin n)} {G G' G'' : Type} [Group G] [Group G'] [Group G'']

@[expose] noncomputable def PhanFamilyE.map (S : PhanFamilyE K p f M G) (φ : G →* G') :
    PhanFamilyE K p f M G' where
  ι i := φ.comp (S.ι i)
  θ i j := φ.comp (S.θ i j)
  left i j hij hM := by
    rw [MonoidHom.comp_assoc, S.left i j hij hM]
  right i j hij hM := by
    rw [MonoidHom.comp_assoc, S.right i j hij hM]
  comm i j hM a b := by
    show φ ((S.ι i) a) * φ ((S.ι j) b) = φ ((S.ι j) b) * φ ((S.ι i) a)
    rw [← map_mul, ← map_mul, S.comm i j hM a b]

@[simp] theorem PhanFamilyE.map_ι (S : PhanFamilyE K p f M G) (φ : G →* G') (i : Fin n) :
    (S.map φ).ι i = φ.comp (S.ι i) := rfl

@[simp] theorem PhanFamilyE.map_θ (S : PhanFamilyE K p f M G) (φ : G →* G') (i j : Fin n) :
    (S.map φ).θ i j = φ.comp (S.θ i j) := rfl

@[simp] theorem PhanFamilyE.map_id (S : PhanFamilyE K p f M G) :
    S.map (MonoidHom.id G) = S := by
  cases S
  rfl

@[simp] theorem PhanFamilyE.map_map (S : PhanFamilyE K p f M G) (φ : G →* G')
    (ψ : G' →* G'') : (S.map φ).map ψ = S.map (ψ.comp φ) := by
  cases S
  rfl

theorem PhanFamilyE.IsUniversal.map {S : PhanFamilyE K p f M G} (e : G ≃* G')
    (h : S.IsUniversal) : (S.map e.toMonoidHom).IsUniversal := by
  intro Y _ F
  obtain ⟨ψ, hψι, hψθ⟩ := h Y F
  refine ⟨ψ.comp e.symm.toMonoidHom, ?_, ?_⟩
  · intro i
    ext x
    simpa using DFunLike.congr_fun (hψι i) x
  · intro i j hij hM
    ext x
    simpa using DFunLike.congr_fun (hψθ i j hij hM) x

end Map

section Good

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ}
  {M : CoxeterMatrix (Fin n)} {G G' : Type} [Group G] [Group G']

theorem PhanFamilyE.nodeTor_map (S : PhanFamilyE K 2 f M G) (φ : G →* G') (i : Fin n) :
    (S.map φ).nodeTor i = φ.comp (S.nodeTor i) := rfl

theorem PhanFamilyE.torus_map (S : PhanFamilyE K 2 f M G) (φ : G →* G') :
    (S.map φ).torus = S.torus.map φ := by
  simp only [PhanFamilyE.torus, PhanFamilyE.nodeTor_map, MonoidHom.range_comp,
    Subgroup.map_iSup]

theorem PhanFamilyE.Good.of_map {S : PhanFamilyE K 2 f M G} {φ : G →* G'}
    (hφ : Function.Injective φ) (h : (S.map φ).Good) : S.Good where
  simplyLaced := h.simplyLaced
  inj i := by
    exact Function.Injective.of_comp (f := φ) (h.inj i)
  disj i j hij := by
    refine Subgroup.map_injective hφ ?_
    rw [Subgroup.map_bot, Subgroup.map_inf _ _ φ hφ,
      ← MonoidHom.range_comp φ (S.ι i), ← MonoidHom.range_comp φ (S.ι j)]
    simpa only [PhanFamilyE.map_ι] using h.disj i j hij
  θ_inj i j hij hM := by
    exact Function.Injective.of_comp (f := φ) (h.θ_inj i j hij hM)
  indep := by
    have h' : iSupIndep (fun i => ((S.nodeTor i).range).map φ) := by
      simpa only [PhanFamilyE.nodeTor_map, MonoidHom.range_comp] using h.indep
    rw [iSupIndep_def] at h' ⊢
    intro i
    have hi := h' i
    rw [disjoint_iff] at hi ⊢
    have h1 : (⨆ j, ⨆ (_ : j ≠ i), (S.nodeTor j).range).map φ =
        ⨆ j, ⨆ (_ : j ≠ i), ((S.nodeTor j).range).map φ := by
      rw [Subgroup.map_iSup]
      congr 1
      funext j
      rw [Subgroup.map_iSup]
    rw [← h1, ← Subgroup.map_inf _ _ φ hφ] at hi
    exact (Subgroup.map_eq_bot_iff_of_injective _ hφ).mp hi
  torus_inf J hJ := by
    refine Subgroup.map_injective hφ ?_
    have hL : (⨆ j ∈ J, (S.ι j).range).map φ = ⨆ j ∈ J, ((S.map φ).ι j).range := by
      simp only [PhanFamilyE.map_ι, MonoidHom.range_comp, Subgroup.map_iSup]
    have hR : (⨆ j ∈ J, (S.nodeTor j).range).map φ =
        ⨆ j ∈ J, ((S.map φ).nodeTor j).range := by
      simp only [PhanFamilyE.nodeTor_map, MonoidHom.range_comp, Subgroup.map_iSup]
    rw [Subgroup.map_inf _ _ φ hφ, hL, ← PhanFamilyE.torus_map, hR]
    exact h.torus_inf J hJ

end Good

section Equiv

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ}
  {M : CoxeterMatrix (Fin n)} {G G' : Type} [Group G] [Group G']

@[expose] noncomputable def PhanFamilyE.torusEquiv (S : PhanFamilyE K 2 f M G) (e : G ≃* G') :
    G ⧸ S.torus ≃ G' ⧸ (S.map e.toMonoidHom).torus where
  toFun := Quotient.map' (e : G → G') (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [PhanFamilyE.torus_map]
    change (e.toMonoidHom a)⁻¹ * e.toMonoidHom b ∈ S.torus.map e.toMonoidHom
    simpa only [map_inv, map_mul] using Subgroup.mem_map_of_mem e.toMonoidHom hab)
  invFun := Quotient.map' (e.symm : G' → G) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [PhanFamilyE.torus_map] at hab
    have hmem : e.symm.toMonoidHom (a⁻¹ * b) ∈ S.torus := by
      refine (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp ?_
      simpa using hab
    change (e.symm.toMonoidHom a)⁻¹ * e.symm.toMonoidHom b ∈ S.torus
    simpa only [map_inv, map_mul] using hmem)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn' with
    | h a =>
      rw [Quotient.map'_mk'', Quotient.map'_mk'', e.symm_apply_apply]
  right_inv := by
    intro x
    induction x using Quotient.inductionOn' with
    | h a =>
      rw [Quotient.map'_mk'', Quotient.map'_mk'', e.apply_symm_apply]

@[simp] theorem PhanFamilyE.torusEquiv_mk (S : PhanFamilyE K 2 f M G) (e : G ≃* G') (a : G) :
    PhanFamilyE.torusEquiv S e (a : G ⧸ S.torus) =
      ((e a : G') : G' ⧸ (S.map e.toMonoidHom).torus) :=
  rfl

end Equiv

end CFSG.ClassicalInvolution.Phan.PhanE

end
