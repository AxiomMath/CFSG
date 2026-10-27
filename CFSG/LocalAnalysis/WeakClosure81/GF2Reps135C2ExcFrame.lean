module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcMonomial
import CFSG.LieType.Chevalley.E6GraphInvolutionForms
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.TopRank
public import CFSG.LieType.Chevalley.KernelComponentLength

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
open CFSG.LieType.Steinberg.Adjoint (iform)

variable {τ : Tag} {K : Type} [Field K]

private theorem vSL_inv_mul_uSL_mul_vSL {c : Kˣ} (h2 : (2 : K) = 0) :
    vSL (((c⁻¹ : Kˣ) : K)) * uSL (c : K) * (vSL (((c⁻¹ : Kˣ) : K)))⁻¹ = nSL c := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  fin_cases i <;> fin_cases j <;>
    simp [nSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  · ring
  · rw [one_add_one_eq_two]
    exact h2

private theorem mul_conj_mul_conj {G : Type*} [Group G] {gβ g' x z' : G}
    (h1 : g' * x = x * g')
    (hK : gβ * (g' * z' * g'⁻¹) = (g' * z' * g'⁻¹) * gβ) :
    (gβ * g') * (x * z') * (gβ * g')⁻¹ = (gβ * x * gβ⁻¹) * (g' * z' * g'⁻¹) := by
  have hK' : (g' * z' * g'⁻¹) * gβ⁻¹ = gβ⁻¹ * (g' * z' * g'⁻¹) := by
    calc (g' * z' * g'⁻¹) * gβ⁻¹
        = gβ⁻¹ * (gβ * (g' * z' * g'⁻¹)) * gβ⁻¹ := by group
      _ = gβ⁻¹ * ((g' * z' * g'⁻¹) * gβ) * gβ⁻¹ := by rw [hK]
      _ = gβ⁻¹ * (g' * z' * g'⁻¹) := by group
  calc (gβ * g') * (x * z') * (gβ * g')⁻¹
      = gβ * (g' * x) * z' * (g'⁻¹ * gβ⁻¹) := by group
    _ = gβ * (x * g') * z' * (g'⁻¹ * gβ⁻¹) := by rw [h1]
    _ = gβ * x * ((g' * z' * g'⁻¹) * gβ⁻¹) := by group
    _ = gβ * x * (gβ⁻¹ * (g' * z' * g'⁻¹)) := by rw [hK']
    _ = (gβ * x * gβ⁻¹) * (g' * z' * g'⁻¹) := by group


variable [Finite K] [CharP K 2] {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

private noncomputable def frameProd (F : List (Fin τ.rank → ℤ))
    (c : (Fin τ.rank → ℤ) → Kˣ) : adjointGroup τ K :=
  ⟨(F.map fun β => pinnedX τ K β (c β)).prod,
    Subgroup.list_prod_mem (adjointGroup τ K) fun g hg => by
      obtain ⟨β, -, rfl⟩ := List.mem_map.1 hg
      exact pinnedX_mem_adjointGroup β _⟩

section RankOne

omit
  [Finite K]

private theorem pinnedX_conj_eq_rootWeyl {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (c : Kˣ) :
    pinnedX τ K (-β) (((c⁻¹ : Kˣ) : K)) * pinnedX τ K β ((c : Kˣ) : K) *
      (pinnedX τ K (-β) (((c⁻¹ : Kˣ) : K)))⁻¹ = rootWeylSL2 τ K β c := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [← E6GraphInvolution.rootSL2_uSL_of_two (E := K) h2 β ((c : Kˣ) : K),
    ← E6GraphInvolution.rootSL2_vSL_of_two (E := K) h2 hβ (((c⁻¹ : Kˣ) : K))]
  rw [← map_mul, ← map_inv, ← map_mul, vSL_inv_mul_uSL_mul_vSL (c := c) h2]
  rfl

section Closure

omit [CharP K 2]

private noncomputable def frameClosure (F : List (Fin τ.rank → ℤ)) : Subgroup (ModGL τ K) :=
  Subgroup.closure (⋃ γ ∈ F, (rootRankOneGroup τ K γ : Set (ModGL τ K)))

private theorem le_frameClosure_cons_self (β : Fin τ.rank → ℤ)
    (F : List (Fin τ.rank → ℤ)) :
    rootRankOneGroup τ K β ≤ frameClosure (β :: F) := fun _ hy =>
  Subgroup.subset_closure
    (Set.mem_iUnion.2 ⟨β, Set.mem_iUnion.2 ⟨List.mem_cons_self (a := β) (l := F), hy⟩⟩)

private theorem frameClosure_cons_le (β : Fin τ.rank → ℤ) (F : List (Fin τ.rank → ℤ)) :
    frameClosure (K := K) F ≤ frameClosure (K := K) (β :: F) := by
  rw [frameClosure, frameClosure]
  refine Subgroup.closure_mono ?_
  intro y hy
  obtain ⟨γ, hy⟩ := Set.mem_iUnion.1 hy
  obtain ⟨hγ, hy⟩ := Set.mem_iUnion.1 hy
  exact Set.mem_iUnion.2 ⟨γ, Set.mem_iUnion.2 ⟨List.mem_cons_of_mem β hγ, hy⟩⟩

private theorem commute_frameClosure {β : Fin τ.rank → ℤ} {F : List (Fin τ.rank → ℤ)}
    (hcomm : ∀ γ ∈ F,
      ∀ x ∈ rootRankOneGroup τ K β, ∀ y ∈ rootRankOneGroup τ K γ, x * y = y * x) :
    ∀ x ∈ rootRankOneGroup τ K β, ∀ y ∈ frameClosure F, x * y = y * x := by
  have hgen : ∀ x ∈ (rootRankOneGroup τ K β : Set (ModGL τ K)),
      ∀ y ∈ (⋃ γ ∈ F, (rootRankOneGroup τ K γ : Set (ModGL τ K))), x * y = y * x := by
    intro x hx y hy
    obtain ⟨γ, hy⟩ := Set.mem_iUnion.1 hy
    obtain ⟨hγ, hy⟩ := Set.mem_iUnion.1 hy
    exact hcomm γ hγ x hx y hy
  have h := closure_commute hgen
  rw [Subgroup.closure_eq] at h
  exact h

end Closure

private theorem exists_conj_frame_prod {F : List (Fin τ.rank → ℤ)}
    (hF : ∀ β ∈ F, IsRoot τ β)
    (hcomm : F.Pairwise fun β γ =>
      ∀ x ∈ rootRankOneGroup τ K β, ∀ y ∈ rootRankOneGroup τ K γ, x * y = y * x)
    (c : (Fin τ.rank → ℤ) → Kˣ) :
    ∃ (g : adjointGroup τ K) (hm : ((g * frameProd F c * g⁻¹ : adjointGroup τ K) : ModGL τ K) ∈
        monomialSubgroup τ K),
      weylQuotientHom τ K ⟨_, hm⟩ = reflectionWordProd F ∧
      (g : ModGL τ K) ∈ frameClosure F ∧
      ((g * frameProd F c * g⁻¹ : adjointGroup τ K) : ModGL τ K) ∈ frameClosure F := by
  induction F with
  | nil =>
      have hone : ((1 : adjointGroup τ K) * frameProd ([] : List (Fin τ.rank → ℤ)) c * 1⁻¹ :
          adjointGroup τ K) = 1 := by
        rw [show frameProd ([] : List (Fin τ.rank → ℤ)) c = 1 from rfl]
        simp
      have hm : (((1 : adjointGroup τ K) * frameProd ([] : List (Fin τ.rank → ℤ)) c * 1⁻¹ :
          adjointGroup τ K) : ModGL τ K) ∈ monomialSubgroup τ K := by
        rw [hone]
        exact Subgroup.one_mem _
      have hweyl : weylQuotientHom τ K
          ⟨((1 : adjointGroup τ K) * frameProd ([] : List (Fin τ.rank → ℤ)) c * 1⁻¹ :
            adjointGroup τ K), hm⟩ = reflectionWordProd ([] : List (Fin τ.rank → ℤ)) := by
        simp only [hone]
        exact map_one (weylQuotientHom τ K)
      have hgcl : (((1 : adjointGroup τ K) * frameProd ([] : List (Fin τ.rank → ℤ)) c * 1⁻¹ :
          adjointGroup τ K) : ModGL τ K) ∈ frameClosure ([] : List (Fin τ.rank → ℤ)) := by
        rw [hone, frameClosure]
        simp
      exact ⟨1, hm, hweyl, hgcl, hgcl⟩
  | cons β F' ih =>
      obtain ⟨hβroot, hF'⟩ := List.forall_mem_cons.1 hF
      obtain ⟨hcommβ, hcomm'⟩ := List.pairwise_cons.1 hcomm
      obtain ⟨g', hm', hweyl', hg'cl, hconj'cl⟩ := ih hF' hcomm'
      have hLβ : rootRankOneGroup τ K β = rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) :=
        (exceptional_Lang_root_rank_one_torus_transport τ K hβroot).1
      obtain ⟨hmβ, hweylβ⟩ :=
        (exceptional_Lang_root_rank_one_torus_transport τ K hβroot).2.2.1 (c β)
      let xA : adjointGroup τ K :=
        ⟨pinnedX τ K β ((c β : Kˣ) : K), pinnedX_mem_adjointGroup _ _⟩
      let gβ : adjointGroup τ K :=
        ⟨pinnedX τ K (-β) (((c β)⁻¹ : Kˣ) : K), pinnedX_mem_adjointGroup _ _⟩
      let z' : adjointGroup τ K := frameProd F' c
      let g : adjointGroup τ K := gβ * g'
      have hxA : (xA : ModGL τ K) ∈ rootRankOneGroup τ K β := by
        rw [hLβ]
        exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
      have hgβ : (gβ : ModGL τ K) ∈ rootRankOneGroup τ K β := by
        rw [hLβ]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
      have hcomm := commute_frameClosure (K := K) hcommβ
      have h1M : (g' : ModGL τ K) * (xA : ModGL τ K) = (xA : ModGL τ K) * (g' : ModGL τ K) :=
        (hcomm _ hxA _ hg'cl).symm
      have hKM : (gβ : ModGL τ K) *
            ((g' : ModGL τ K) * (z' : ModGL τ K) * (g' : ModGL τ K)⁻¹) =
          ((g' : ModGL τ K) * (z' : ModGL τ K) * (g' : ModGL τ K)⁻¹) * (gβ : ModGL τ K) :=
        hcomm _ hgβ _ hconj'cl
      have hzE : ((g' * z' * g'⁻¹ : adjointGroup τ K) : ModGL τ K) =
          (g' : ModGL τ K) * (z' : ModGL τ K) * (g' : ModGL τ K)⁻¹ := rfl
      have hcons : frameProd (β :: F') c = xA * z' := by
        refine Subtype.ext ?_
        simp [frameProd, xA, z']
      have hcoe : ((g * frameProd (β :: F') c * g⁻¹ : adjointGroup τ K) : ModGL τ K) =
          ((gβ : ModGL τ K) * (g' : ModGL τ K)) *
            ((xA : ModGL τ K) * (z' : ModGL τ K)) *
              ((gβ : ModGL τ K) * (g' : ModGL τ K))⁻¹ := by
        rw [show g = gβ * g' from rfl, hcons]
        rfl
      have hkey : ((g * frameProd (β :: F') c * g⁻¹ : adjointGroup τ K) : ModGL τ K) =
          rootWeylSL2 τ K β (c β) *
            ((g' * z' * g'⁻¹ : adjointGroup τ K) : ModGL τ K) := by
        rw [hcoe, mul_conj_mul_conj h1M hKM, hzE]
        rw [show (gβ : ModGL τ K) * (xA : ModGL τ K) * (gβ : ModGL τ K)⁻¹ =
            rootWeylSL2 τ K β (c β) from by
          simpa [gβ, xA] using pinnedX_conj_eq_rootWeyl hβroot (c β)]
      have hm : ((g * frameProd (β :: F') c * g⁻¹ : adjointGroup τ K) : ModGL τ K) ∈
          monomialSubgroup τ K := by
        rw [hkey]
        exact mul_mem hmβ hm'
      have hweyl : weylQuotientHom τ K
          ⟨((g * frameProd (β :: F') c * g⁻¹ : adjointGroup τ K) : ModGL τ K), hm⟩ =
          reflectionWordProd (β :: F') := by
        have hXY : rootWeylSL2 τ K β (c β) *
            ((g' * z' * g'⁻¹ : adjointGroup τ K) : ModGL τ K) ∈ monomialSubgroup τ K :=
          mul_mem hmβ hm'
        have hsub : (⟨((g * frameProd (β :: F') c * g⁻¹ : adjointGroup τ K) : ModGL τ K),
            hm⟩ : monomialSubgroup τ K) =
            ⟨rootWeylSL2 τ K β (c β), hmβ⟩ *
              ⟨((g' * z' * g'⁻¹ : adjointGroup τ K) : ModGL τ K), hm'⟩ := by
          rw [show (⟨((g * frameProd (β :: F') c * g⁻¹ : adjointGroup τ K) : ModGL τ K),
              hm⟩ : monomialSubgroup τ K) =
              ⟨rootWeylSL2 τ K β (c β) *
                ((g' * z' * g'⁻¹ : adjointGroup τ K) : ModGL τ K), hXY⟩ from
            Subtype.ext hkey]
          rfl
        rw [hsub, map_mul, hweylβ, hweyl', reflectionWordProd_cons]
      have hrootWeyl : rootWeylSL2 τ K β (c β) ∈ rootRankOneGroup τ K β :=
        MonoidHom.mem_range.2 ⟨nSL (c β), rfl⟩
      have hgcl : (g : ModGL τ K) ∈ frameClosure (β :: F') := by
        rw [show g = gβ * g' from rfl]
        exact mul_mem (le_frameClosure_cons_self β F' hgβ) (frameClosure_cons_le β F' hg'cl)
      have hconjcl : ((g * frameProd (β :: F') c * g⁻¹ : adjointGroup τ K) : ModGL τ K) ∈
          frameClosure (β :: F') := by
        rw [hkey]
        exact mul_mem (le_frameClosure_cons_self β F' hrootWeyl)
          (frameClosure_cons_le β F' hconj'cl)
      exact ⟨g, hm, hweyl, hgcl, hconjcl⟩

theorem exists_conj_frame_mem_monomialSubgroup_of_commute {F : List (Fin τ.rank → ℤ)}
    (hF : ∀ β ∈ F, IsRoot τ β)
    (hcomm : F.Pairwise fun β γ =>
      ∀ x ∈ rootRankOneGroup τ K β, ∀ y ∈ rootRankOneGroup τ K γ, x * y = y * x)
    (c : (Fin τ.rank → ℤ) → Kˣ) (z : adjointGroup τ K)
    (hz : (z : ModGL τ K) = (F.map fun β => pinnedX τ K β (c β)).prod) :
    ∃ (g : adjointGroup τ K) (hm : ((g * z * g⁻¹ : adjointGroup τ K) : ModGL τ K) ∈
        monomialSubgroup τ K),
      weylQuotientHom τ K ⟨_, hm⟩ = reflectionWordProd F := by
  obtain ⟨g, hm, hweyl, -, -⟩ := exists_conj_frame_prod hF hcomm c
  have hz' : z = frameProd F c := Subtype.ext hz
  rw [hz']
  exact ⟨g, hm, hweyl⟩

end RankOne

omit [Finite K] [CharP K 2] in
private theorem pairwise_commute_of_strongOrth {F : List (Fin τ.rank → ℤ)}
    (hF : ∀ β ∈ F, IsRoot τ β)
    (horth : F.Pairwise fun β γ => iform β γ = 0 ∧ ¬ IsRoot τ (β + γ) ∧ ¬ IsRoot τ (β - γ)) :
    F.Pairwise fun β γ =>
      ∀ x ∈ rootRankOneGroup τ K β, ∀ y ∈ rootRankOneGroup τ K γ, x * y = y * x :=
  horth.imp_of_mem fun hβ hγ h =>
    exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K (hF _ hβ) (hF _ hγ) h.1
      h.2.1 h.2.2

omit [Finite K] in
theorem exists_conj_frame_mem_monomialSubgroup {F : List (Fin τ.rank → ℤ)}
    (hF : ∀ β ∈ F, IsRoot τ β)
    (horth : F.Pairwise fun β γ => iform β γ = 0 ∧ ¬ IsRoot τ (β + γ) ∧ ¬ IsRoot τ (β - γ))
    (c : (Fin τ.rank → ℤ) → Kˣ) (z : adjointGroup τ K)
    (hz : (z : ModGL τ K) = (F.map fun β => pinnedX τ K β (c β)).prod) :
    ∃ (g : adjointGroup τ K) (hm : ((g * z * g⁻¹ : adjointGroup τ K) : ModGL τ K) ∈
        monomialSubgroup τ K),
      weylQuotientHom τ K ⟨_, hm⟩ = reflectionWordProd F :=
  exists_conj_frame_mem_monomialSubgroup_of_commute hF (pairwise_commute_of_strongOrth hF horth)
    c z hz

theorem le_finrank_range_frame_sub_one_of_commute [Module.Finite k V]
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)} (ht : IsChevType τ K 2 hw ρ y χ J)
    {v₀ : Fin τ.rank → ℤ} (hv : ∀ j ∈ J, reflect τ j v₀ = v₀) {F : List (Fin τ.rank → ℤ)}
    (hF : ∀ β ∈ F, IsRoot τ β)
    (hcomm : F.Pairwise fun β γ =>
      ∀ x ∈ rootRankOneGroup τ K β, ∀ y ∈ rootRankOneGroup τ K γ, x * y = y * x)
    (c : (Fin τ.rank → ℤ) → Kˣ) (z : adjointGroup τ K)
    (hz : (z : ModGL τ K) = (F.map fun β => pinnedX τ K β (c β)).prod) {R : ℕ}
    (w : Fin R → WeylGroup τ)
    (hinj : Function.Injective (Sum.elim (fun i => w i • v₀)
      (fun i => (reflectionWordProd F * w i) • v₀))) :
    R ≤ Module.finrank k (LinearMap.range (ρ z - 1)) := by
  obtain ⟨g, hm, hσ⟩ := exists_conj_frame_mem_monomialSubgroup_of_commute hF hcomm c z hz
  have hinj' : Function.Injective (Sum.elim (fun i => w i • v₀)
      (fun i => (weylQuotientHom τ K ⟨((g * z * g⁻¹ : adjointGroup τ K) : ModGL τ K), hm⟩ *
        w i) • v₀)) := by
    simpa only [hσ] using hinj
  have h := le_finrank_range_sub_one_of_monomial hρ ht hv (g * z * g⁻¹) hm w hinj'
  rwa [CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.finrank_range_rep_conj_sub_one
    ρ g z] at h

theorem le_finrank_range_frame_sub_one [Module.Finite k V]
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)} (ht : IsChevType τ K 2 hw ρ y χ J)
    {v₀ : Fin τ.rank → ℤ} (hv : ∀ j ∈ J, reflect τ j v₀ = v₀) {F : List (Fin τ.rank → ℤ)}
    (hF : ∀ β ∈ F, IsRoot τ β)
    (horth : F.Pairwise fun β γ => iform β γ = 0 ∧ ¬ IsRoot τ (β + γ) ∧ ¬ IsRoot τ (β - γ))
    (c : (Fin τ.rank → ℤ) → Kˣ) (z : adjointGroup τ K)
    (hz : (z : ModGL τ K) = (F.map fun β => pinnedX τ K β (c β)).prod) {R : ℕ}
    (w : Fin R → WeylGroup τ)
    (hinj : Function.Injective (Sum.elim (fun i => w i • v₀)
      (fun i => (reflectionWordProd F * w i) • v₀))) :
    R ≤ Module.finrank k (LinearMap.range (ρ z - 1)) :=
  le_finrank_range_frame_sub_one_of_commute hρ ht hv hF (pairwise_commute_of_strongOrth hF horth)
    c z hz w hinj

end CFSG.LocalAnalysis.WeakClosure81
