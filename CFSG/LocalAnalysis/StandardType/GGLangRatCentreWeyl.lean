module

public import CFSG.LocalAnalysis.StandardType.GGLangRatCentreStmts

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
open scoped TensorProduct

private theorem langRatCW_iform_self
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    iform β β = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hβ
  have hsym : τ.symmetrizer j j = 1 := by
    rcases hτ with rfl | rfl <;> simp [Tag.symmetrizer]
  rw [hj, hsym, mul_one]

private theorem langRatCW_corootPair_eq_iform
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {β v : Fin τ.rank → ℤ} (hβ : IsRoot τ β) : corootPair β v = iform β v := by
  have h := corootPair_mul hβ v
  rw [langRatCW_iform_self hτ hβ] at h
  omega

private theorem langRatCW_reflection_sub
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {γ x : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    rootReflection γ • x - x = iform x γ • (-γ) := by
  rw [rootReflection_smul hγ, langRatCW_corootPair_eq_iform hτ hγ, iform_comm γ x, smul_neg]
  abel

private theorem langRatCW_rootReflection_mem
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hγΨ : γ ∈ Ψ)
    {x : Fin τ.rank → ℤ} (hx : x ∈ Submodule.span ℤ Ψ) :
    rootReflection γ • x ∈ Submodule.span ℤ Ψ := by
  rw [rootReflection_smul hγ, langRatCW_corootPair_eq_iform hτ hγ]
  exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (Submodule.subset_span hγΨ))

private theorem langRatCW_smul_sum {τ : Tag} (a : WeylGroup τ) (x : Fin τ.rank → ℤ)
    (l : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))) :
    a • (l.map (fun p => iform x p.1 • p.2)).sum =
      (l.map (fun p => iform x p.1 • (a • p.2))).sum := by
  induction l with
  | nil => simp
  | cons p t ih =>
      simp only [List.map_cons, List.sum_cons, smul_add, ih,
        smul_comm a (iform x p.1) p.2]

private theorem langRatCW_neg_smul_sum {τ : Tag} (a : WeylGroup τ) (x : Fin τ.rank → ℤ)
    (l : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))) :
    -(a • (l.map (fun p => iform x p.1 • p.2)).sum) =
      (l.map (fun p => iform x p.1 • (-(a • p.2)))).sum := by
  induction l with
  | nil => simp
  | cons p t ih =>
      simp only [List.map_cons, List.sum_cons, smul_add, neg_add, ih,
        smul_comm a (iform x p.1) p.2, smul_neg]

theorem langRatWeylFactor_holds :
    ∀ (τ : Tag), (τ = .E7 ∨ τ = .E8) → ∀ (Ψ : Set (Fin τ.rank → ℤ)), (∀ γ ∈ Ψ, IsRoot τ γ) →
      ∀ u ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ},
        LangRatRootFactor Ψ (fun x => u • x - x) := by
  intro τ hτ Ψ hroots u hu
  let P : WeylGroup τ → Prop := fun u =>
    (∀ x ∈ Submodule.span ℤ Ψ, u • x ∈ Submodule.span ℤ Ψ) ∧
    (∀ x ∈ Submodule.span ℤ Ψ, u⁻¹ • x ∈ Submodule.span ℤ Ψ) ∧
    LangRatRootFactor Ψ (fun x => u • x - x)
  have key : P u := by
    refine Subgroup.closure_induction (p := fun u _ => P u) ?mem ?one ?mul ?inv hu
    · intro s hs
      obtain ⟨γ, hγΨ, rfl⟩ := hs
      have hγ : IsRoot τ γ := hroots γ hγΨ
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        exact langRatCW_rootReflection_mem hτ hγ hγΨ hx
      · intro x hx
        rw [rootReflection_inv hγ]
        exact langRatCW_rootReflection_mem hτ hγ hγΨ hx
      · refine ⟨[(γ, -γ)], ?_, ?_⟩
        · intro p hp
          rw [List.mem_singleton] at hp
          rw [hp]
          exact ⟨hγΨ, Submodule.neg_mem _ (Submodule.subset_span hγΨ)⟩
        · intro x hx
          rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          exact langRatCW_reflection_sub hτ hγ
    · refine ⟨?_, ?_, ?_⟩
      · intro x hx; simpa using hx
      · intro x hx; simpa using hx
      · refine ⟨[], by simp, ?_⟩
        intro x hx; simp
    · intro a b _ _ Pa Pb
      obtain ⟨ha, ha', hfa⟩ := Pa
      obtain ⟨hb, hb', hfb⟩ := Pb
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rw [mul_smul]
        exact ha _ (hb x hx)
      · intro x hx
        rw [mul_inv_rev, mul_smul]
        exact hb' _ (ha' x hx)
      · obtain ⟨la, hla, hfa⟩ := hfa
        obtain ⟨lb, hlb, hfb⟩ := hfb
        refine ⟨lb.map (fun p => (p.1, a • p.2)) ++ la, ?_, ?_⟩
        · intro p hp
          rw [List.mem_append] at hp
          rcases hp with hp | hp
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
            exact ⟨(hlb q hq).1, ha q.2 (hlb q hq).2⟩
          · exact hla p hp
        · intro x hx
          rw [List.map_append, List.sum_append]
          simp only [List.map_map, Function.comp_def]
          rw [← langRatCW_smul_sum a x lb, ← hfb x hx, ← hfa x hx, mul_smul, smul_sub]
          exact (sub_add_sub_cancel _ _ _).symm
    · intro a _ Pa
      obtain ⟨ha, ha', hfa⟩ := Pa
      refine ⟨?_, ?_, ?_⟩
      · intro x hx; exact ha' x hx
      · intro x hx; rw [inv_inv]; exact ha x hx
      · obtain ⟨la, hla, hfa⟩ := hfa
        refine ⟨la.map (fun p => (p.1, -(a⁻¹ • p.2))), ?_, ?_⟩
        · intro p hp
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          exact ⟨(hla q hq).1, Submodule.neg_mem _ (ha' q.2 (hla q hq).2)⟩
        · intro x hx
          simp only [List.map_map, Function.comp_def]
          rw [← langRatCW_neg_smul_sum a⁻¹ x la, ← hfa x hx, smul_sub, inv_smul_smul]
          abel
  exact key.2.2

private theorem langRatCW_exists_coords_span
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) {x : Fin τ.rank → ℤ} (hx : x ∈ Submodule.span ℤ Ψ) :
    ∃ c : (Fin τ.rank → ℤ) → ℤ, x = ∑ β ∈ simpleRoots Ψ, c β • β := by
  refine Submodule.span_induction
    (p := fun x _ => ∃ c : (Fin τ.rank → ℤ) → ℤ, x = ∑ β ∈ simpleRoots Ψ, c β • β)
    ?mem ?zero ?add ?smul hx
  · intro y hy
    exact exists_coords hΨ hy
  · exact ⟨0, by simp⟩
  · intro y z _ _ ⟨cy, hcy⟩ ⟨cz, hcz⟩
    refine ⟨cy + cz, ?_⟩
    rw [hcy, hcz, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [Pi.add_apply, add_smul]
  · intro m y _ ⟨cy, hcy⟩
    refine ⟨m • cy, ?_⟩
    rw [hcy, Finset.smul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, smul_smul]

private theorem langRatCW_four_eq_sum {τ : Tag} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (emb : ι → (Fin τ.rank → ℤ)) (C : Matrix ι ι ℤ) (k d : ℤ)
    (x : Fin τ.rank → ℤ) (cι y : ι → ℤ)
    (hk : (4 : ℤ) = d * k)
    (hx' : x = ∑ i : ι, cι i • emb i)
    (hcoord : ∀ i : ι, d * cι i = ∑ j : ι, C.adjugate i j * y j) :
    (4 : ℤ) • x = k • (∑ i : ι, ∑ j : ι, (C.adjugate i j * y j) • emb i) := by
  calc
    (4 : ℤ) • x = k • (d • x) := by rw [hk, mul_comm, mul_smul]
    _ = k • (∑ i : ι, (d * cι i) • emb i) := by
        rw [hx', Finset.smul_sum]
        simp only [smul_smul]
    _ = k • (∑ i : ι, (∑ j : ι, C.adjugate i j * y j) • emb i) := by
        simp only [hcoord]
    _ = k • (∑ i : ι, ∑ j : ι, (C.adjugate i j * y j) • emb i) := by
        simp only [Finset.sum_smul]

private theorem langRatCW_swap {τ : Tag} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (emb : ι → (Fin τ.rank → ℤ)) (C : Matrix ι ι ℤ) (y : ι → ℤ) :
    (∑ i : ι, ∑ j : ι, (C.adjugate i j * y j) • emb i) =
      ∑ j : ι, y j • (∑ i : ι, C.adjugate i j • emb i) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm, smul_smul]

private theorem langRatCW_smul_swap {τ : Tag} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (emb : ι → (Fin τ.rank → ℤ)) (C : Matrix ι ι ℤ) (k : ℤ) (y : ι → ℤ) :
    k • (∑ j : ι, y j • (∑ i : ι, C.adjugate i j • emb i)) =
      ∑ j : ι, y j • (∑ i : ι, (k * C.adjugate i j) • emb i) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_comm k (y j)]
  congr 1
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [← smul_smul]

private theorem langRatCW_list_sum {τ : Tag} {ι : Type*} [Fintype ι]
    (emb : ι → (Fin τ.rank → ℤ)) (v : ι → (Fin τ.rank → ℤ))
    (x : Fin τ.rank → ℤ) (y : ι → ℤ)
    (hy : ∀ j : ι, y j = iform x (emb j)) :
    (List.map (fun p => iform x p.1 • p.2)
      ((Finset.univ : Finset ι).toList.map (fun j => (emb j, v j)))).sum =
      ∑ j : ι, y j • v j := by
  rw [List.map_map]
  simp only [Function.comp_def]
  rw [Finset.sum_map_toList]
  exact Finset.sum_congr rfl fun j _ => by rw [hy j]

theorem langRatFactorOfDet_holds :
    ∀ (τ : Tag), (τ = .E7 ∨ τ = .E8) → ∀ (Ψ : Set (Fin τ.rank → ℤ)), IsRootComponent Ψ →
      (Matrix.of fun α β : ↥(simpleRoots Ψ) => iform (α : Fin τ.rank → ℤ) β).det ∣ 4 →
        LangRatRootFactor Ψ (fun x => (4 : ℤ) • x) := by
  intro τ hτ Ψ hΨ hd
  classical
  let Δ := simpleRoots Ψ
  let ι := ↥Δ
  let emb : ι → (Fin τ.rank → ℤ) := fun i => (i : Fin τ.rank → ℤ)
  let C : Matrix ι ι ℤ := Matrix.of fun α β => iform (emb α) (emb β)
  let d : ℤ := C.det
  obtain ⟨k, hk⟩ := hd
  have hCtrans : C.transpose = C :=
    Matrix.ext fun i j => (iform_comm (emb i) (emb j)).symm
  let v : ι → (Fin τ.rank → ℤ) :=
    fun j => ∑ i : ι, (k * C.adjugate i j) • emb i
  let l : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ)) :=
    (Finset.univ : Finset ι).toList.map (fun j => (emb j, v j))
  refine ⟨l, ?_, ?_⟩
  · intro p hp
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp
    refine ⟨simpleRoots_subset j.2, ?_⟩
    change (∑ i : ι, (k * C.adjugate i j) • emb i) ∈ Submodule.span ℤ Ψ
    exact Submodule.sum_mem _ fun (i : ι) _ =>
      Submodule.smul_mem _ (k * C.adjugate i j)
        (Submodule.subset_span (simpleRoots_subset i.2))
  · intro x hx
    obtain ⟨c, hcx⟩ := langRatCW_exists_coords_span hΨ hx
    let cι : ι → ℤ := fun i => c (emb i)
    have hx' : x = ∑ i : ι, cι i • emb i := by
      rw [hcx, ← Finset.sum_attach, Finset.attach_eq_univ]
    let y : ι → ℤ := fun i => iform x (emb i)
    have hy : y = C.transpose.mulVec cι := by
      funext i
      show iform x (emb i) = ∑ j : ι, C.transpose i j * cι j
      rw [hx', iform_finset_sum_left]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [iform_smul_left, Matrix.transpose_apply]
      rw [show C j i = iform (emb j) (emb i) from rfl]
      ring
    have hadj : C.adjugate.mulVec y = d • cι := by
      rw [hy, Matrix.mulVec_mulVec, hCtrans, Matrix.adjugate_mul, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    have hcoord : ∀ i : ι, d * cι i = ∑ j : ι, C.adjugate i j * y j := by
      intro i
      have h := congrFun hadj i
      simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using h.symm
    have h4x : (4 : ℤ) • x = ∑ j : ι, y j • v j := by
      rw [langRatCW_four_eq_sum emb C k d x cι y hk hx' hcoord]
      rw [langRatCW_swap emb C y]
      exact langRatCW_smul_swap emb C k y
    have hlist : (l.map (fun p => iform x p.1 • p.2)).sum = ∑ j : ι, y j • v j :=
      langRatCW_list_sum emb v x y fun j => rfl
    change (4 : ℤ) • x = (l.map (fun p => iform x p.1 • p.2)).sum
    rw [h4x, hlist]

end CFSG.StandardType.LangRat
