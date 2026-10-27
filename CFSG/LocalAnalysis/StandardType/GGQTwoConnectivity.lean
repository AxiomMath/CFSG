module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInvForm

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2x_rootPair_self (D : GGQ2Lin 3) (γ : ↥D.rootPairs) :
    γ.1.1 γ.1.2 = 2 := by
  obtain ⟨k, w, _, hq2, hq1⟩ := γ.2
  rw [hq2, hq1]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_apply, D.root_coroot_self]

private lemma ggQ2x_simplePair_mem (D : GGQ2Lin 3) (k : D.ι) :
    (D.root k, D.coroot k) ∈ D.rootPairs :=
  ⟨k, 1, D.weyl.one_mem, rfl, by
    change D.root k = (D.root k).comp (LinearMap.id : D.V →ₗ[ZMod 3] D.V)
    rw [LinearMap.comp_id]⟩

private lemma ggQ2x_simpleRefl_mem_weyl (D : GGQ2Lin 3) (k : D.ι) :
    D.simpleRefl k ∈ D.weyl :=
  Subgroup.subset_closure ⟨k, trivial, rfl⟩

private lemma ggQ2x_rootPairs_weyl (D : GGQ2Lin 3) (γ : ↥D.rootPairs)
    (u : D.V ≃ₗ[ZMod 3] D.V) (hu : u ∈ D.weyl) :
    ((γ.1.1.comp (u.symm : D.V →ₗ[ZMod 3] D.V), u γ.1.2) :
      Dual (ZMod 3) D.V × D.V) ∈ D.rootPairs := by
  obtain ⟨k, w, hw, h2, h1⟩ := γ.2
  refine ⟨k, u * w, Subgroup.mul_mem _ hu hw, ?_, ?_⟩
  · rw [h2]; rfl
  · rw [h1]
    ext v
    show D.root k (w.symm (u.symm v)) = D.root k ((u * w).symm v)
    rw [show (u * w).symm v = w.symm (u.symm v) from by
      rw [LinearEquiv.symm_apply_eq]
      simp [LinearEquiv.mul_apply]]

private lemma ggQ2x_rootRefl_mem_weyl (D : GGQ2Lin 3) (γ : ↥D.rootPairs) :
    Module.reflection (ggQ2x_rootPair_self D γ) ∈ D.weyl := by
  obtain ⟨k, w, hw, hq2, hq1⟩ := γ.2
  have heq : Module.reflection (ggQ2x_rootPair_self D γ) = w * D.simpleRefl k * w.symm := by
    ext v
    rw [Module.reflection_apply v (ggQ2x_rootPair_self D γ),
      LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [show D.simpleRefl k = Module.reflection (D.root_coroot_self k) from rfl,
      Module.reflection_apply (w.symm v) (D.root_coroot_self k)]
    rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]
    rw [hq1, hq2]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw (ggQ2x_simpleRefl_mem_weyl D k))
    (Subgroup.inv_mem _ hw)

private lemma ggQ2x_root_mem_span (D : GGQ2Lin 3) (γ : ↥D.rootPairs) :
    γ.1.1 ∈ Submodule.span (ZMod 3) (Set.range D.root) := by
  obtain ⟨k, w, hw, -, h1⟩ := γ.2
  let S : Submodule (ZMod 3) (Dual (ZMod 3) D.V) :=
    Submodule.span (ZMod 3) (Set.range D.root)
  have hgen : ∀ j : D.ι, ∀ α ∈ S,
      α.comp (D.simpleRefl j : D.V →ₗ[ZMod 3] D.V) ∈ S := by
    intro j α hα
    have hsub : α.comp (D.simpleRefl j : D.V →ₗ[ZMod 3] D.V) =
        α - α (D.coroot j) • D.root j := by
      ext v
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply]
      erw [Module.reflection_apply v (D.root_coroot_self j)]
      simp only [map_sub, map_smul, smul_eq_mul]
      ring
    rw [hsub]
    exact Submodule.sub_mem _ hα (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hp : ∀ w ∈ D.weyl,
      (∀ α ∈ S, α.comp (w : D.V →ₗ[ZMod 3] D.V) ∈ S) ∧
      (∀ α ∈ S, α.comp (w.symm : D.V →ₗ[ZMod 3] D.V) ∈ S) := by
    intro w hw
    refine Subgroup.closure_induction (p := fun (w : D.V ≃ₗ[ZMod 3] D.V) _ =>
      (∀ α ∈ S, α.comp (w : D.V →ₗ[ZMod 3] D.V) ∈ S) ∧
      (∀ α ∈ S, α.comp (w.symm : D.V →ₗ[ZMod 3] D.V) ∈ S)) ?_ ?_ ?_ ?_ hw
    · intro r hr
      obtain ⟨j, -, rfl⟩ := hr
      refine ⟨hgen j, ?_⟩
      intro α hα
      have hs : (D.simpleRefl j).symm = D.simpleRefl j := by
        rw [show D.simpleRefl j = Module.reflection (D.root_coroot_self j) from rfl]
        exact Module.reflection_inv (D.root_coroot_self j)
      rw [hs]
      exact hgen j α hα
    · refine ⟨?_, ?_⟩
      · intro α hα
        change α.comp (LinearMap.id : D.V →ₗ[ZMod 3] D.V) ∈ S
        rwa [LinearMap.comp_id]
      · intro α hα
        change α.comp (LinearMap.id : D.V →ₗ[ZMod 3] D.V) ∈ S
        rwa [LinearMap.comp_id]
    · intro x y hx hy hpx hpy
      refine ⟨?_, ?_⟩
      · intro α hα
        have heq : α.comp (((x * y : D.V ≃ₗ[ZMod 3] D.V) : D.V →ₗ[ZMod 3] D.V)) =
            (α.comp (x : D.V →ₗ[ZMod 3] D.V)).comp (y : D.V →ₗ[ZMod 3] D.V) := by
          rw [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp,
            LinearMap.comp_assoc]
        rw [heq]
        exact hpy.1 _ (hpx.1 α hα)
      · intro α hα
        have heq : α.comp (((x * y).symm) : D.V →ₗ[ZMod 3] D.V) =
            (α.comp ((y.symm) : D.V →ₗ[ZMod 3] D.V)).comp
              ((x.symm) : D.V →ₗ[ZMod 3] D.V) := by
          have hsymm : (x * y).symm = y.symm * x.symm := by
            ext z
            rw [LinearEquiv.symm_apply_eq]
            simp [LinearEquiv.mul_apply]
          rw [hsymm, LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp,
            LinearMap.comp_assoc]
        rw [heq]
        exact hpx.2 _ (hpy.2 α hα)
    · intro x hx hpx
      refine ⟨?_, ?_⟩
      · intro α hα
        exact hpx.2 α hα
      · intro α hα
        change α.comp (x : D.V →ₗ[ZMod 3] D.V) ∈ S
        exact hpx.1 α hα
  rw [h1]
  exact (hp w hw).2 (D.root k) (Submodule.subset_span ⟨k, rfl⟩)

private lemma ggQ2x_zero_symm (D : GGQ2Lin 3) (hbas : D.Basis) (h4 : 4 ≤ Fintype.card D.ι)
    (γ δ : ↥D.rootPairs) : γ.1.1 δ.1.2 = 0 ↔ δ.1.1 γ.1.2 = 0 := by
  obtain ⟨β, d, hβsymm, hd, hβh⟩ := ggQ2_exists_invariantForm (p := 3) rfl D hbas h4
  have hiff : ∀ γ δ : ↥D.rootPairs, β γ.1.2 δ.1.2 = 0 ↔ γ.1.1 δ.1.2 = 0 := by
    intro γ δ
    rw [hβh γ δ.1.2]
    exact ⟨fun h => (mul_eq_zero.mp h).resolve_left (hd γ), fun h => by rw [h, mul_zero]⟩
  rw [← hiff γ δ, hβsymm.eq_iff (x := γ.1.2) (y := δ.1.2), hiff δ γ]

private def ggQ2x_graph (D : GGQ2Lin 3) : SimpleGraph D.ι := TauCeti.diagramGraph D.cartan

private lemma ggQ2x_connected (D : GGQ2Lin 3) : (ggQ2x_graph D).Connected :=
  connected_diagramGraph_of_ggIsWeylMatrix (D.isWeyl) D.isCartan

private lemma ggQ2x_cartan_cast_ne_zero (D : GGQ2Lin 3) (hbas : D.Basis)
    (h4 : 4 ≤ Fintype.card D.ι) {i j : D.ι} (hij : i ≠ j) (h : D.cartan i j ≠ 0) :
    (D.cartan i j : ZMod 3) ≠ 0 := by
  have hsome : (D.cartan i j : ZMod 3) ≠ 0 ∨ (D.cartan j i : ZMod 3) ≠ 0 := by
    rcases D.isCartan.entries hij with ⟨-, h0, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1⟩ | ⟨-, h1⟩
    · exact absurd h0 h
    · exact Or.inl (by rw [h1]; norm_num)
    · rcases h1 with h1 | h1
      · exact Or.inl (by rw [h1.1]; norm_num)
      · exact Or.inr (by rw [h1.2]; norm_num)
    · rcases h1 with h1 | h1
      · exact Or.inl (by rw [h1.1]; norm_num)
      · exact Or.inr (by rw [h1.2]; norm_num)
  rcases hsome with hcij | hcji
  · exact hcij
  · refine fun h0 => hcji ?_
    have hz := ggQ2x_zero_symm D hbas h4
      ⟨(D.root i, D.coroot i), ggQ2x_simplePair_mem D i⟩
      ⟨(D.root j, D.coroot j), ggQ2x_simplePair_mem D j⟩
    simp only [D.pairing] at hz
    exact hz.mp h0

private noncomputable def ggQ2x_prod (D : GGQ2Lin 3) (j : ℕ → D.ι) :
    ℕ → D.V ≃ₗ[ZMod 3] D.V :=
  Nat.rec 1 (fun t acc => D.simpleRefl (j (t + 1)) * acc)

private lemma ggQ2x_cartan_eq_zero_of_not_adj (D : GGQ2Lin 3) {i j : D.ι} (hij : i ≠ j)
    (h : ¬ (ggQ2x_graph D).Adj i j) : (D.cartan i j : ZMod 3) = 0 := by
  rw [ggQ2x_graph, TauCeti.diagramGraph_adj] at h
  rw [not_and_or] at h
  rcases h with h | h
  · exact absurd hij h
  rw [not_and_or] at h
  rcases h with h | h
  · rw [not_not] at h; rw [h]; norm_num
  · rw [not_not] at h
    rw [D.isCartan.eq_zero_symm hij h]; norm_num

private lemma ggQ2x_prod_kill (D : GGQ2Lin 3) (k : D.ι) (m : ℕ) (j : ℕ → D.ι)
    (hj0 : j 0 = k)
    (hdist : ∀ r ≤ m, (ggQ2x_graph D).dist k (j r) = r) :
    ∀ t, t + 2 ≤ m → D.root (j m) (ggQ2x_prod D j t (D.coroot k)) = 0 := by
  have hnochord : ∀ s t, s + 2 ≤ t → t ≤ m → ¬ (ggQ2x_graph D).Adj (j s) (j t) := by
    intro s t hst ht hadj
    have htri := (ggQ2x_connected D).dist_triangle (u := k) (v := j s) (w := j t)
    have hd : (ggQ2x_graph D).dist (j s) (j t) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    rw [hdist s (by omega), hdist t ht] at htri
    omega
  intro t
  induction t with
  | zero =>
      intro ht
      have hne : j m ≠ j 0 := by
        intro h
        have h1 := hdist m le_rfl
        rw [h] at h1
        have h0 := hdist 0 (by omega)
        omega
      have hnadj : ¬ (ggQ2x_graph D).Adj (j m) (j 0) := fun hadj =>
        hnochord 0 m (by omega) le_rfl hadj.symm
      have hzero := ggQ2x_cartan_eq_zero_of_not_adj D hne hnadj
      change D.root (j m) (D.coroot k) = 0
      rw [← hj0, D.pairing]
      exact hzero
  | succ t ih =>
      intro ht
      have ht2 : t + 2 ≤ m := by omega
      have hzero_t : D.root (j m) (ggQ2x_prod D j t (D.coroot k)) = 0 := ih ht2
      have hne : j m ≠ j (t + 1) := by
        intro h
        have h1 := hdist m le_rfl
        have h2 := hdist (t + 1) (by omega)
        rw [h] at h1
        omega
      have hnadj : ¬ (ggQ2x_graph D).Adj (j m) (j (t + 1)) := fun hadj =>
        hnochord (t + 1) m (by omega) le_rfl hadj.symm
      have hzero := ggQ2x_cartan_eq_zero_of_not_adj D hne hnadj
      rw [show ggQ2x_prod D j (t + 1) =
        D.simpleRefl (j (t + 1)) * ggQ2x_prod D j t from rfl]
      rw [LinearEquiv.mul_apply]
      erw [Module.reflection_apply (ggQ2x_prod D j t (D.coroot k))
        (D.root_coroot_self (j (t + 1)))]
      rw [map_sub, map_smul, smul_eq_mul, hzero_t, D.pairing, hzero]
      ring

private lemma ggQ2x_prod_ne_zero (D : GGQ2Lin 3) (hbas : D.Basis)
    (h4 : 4 ≤ Fintype.card D.ι) (δ : ↥D.rootPairs) (k : D.ι)
    (hk : D.root k δ.1.2 = 0) :
    ∀ (m : ℕ) (j : ℕ → D.ι), j 0 = k →
      (∀ r < m, (ggQ2x_graph D).Adj (j r) (j (r + 1))) →
      (∀ r ≤ m, (ggQ2x_graph D).dist k (j r) = r) →
      (∀ t < m, D.root (j t) δ.1.2 = 0) →
      D.root (j m) (ggQ2x_prod D j (m - 1) (D.coroot k)) ≠ 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro j hj0 hadj hdist hkill
    rcases m with _ | _ | n
    · rw [show ggQ2x_prod D j (0 - 1) (D.coroot k) = D.coroot k from rfl, hj0,
        D.root_coroot_self]
      exact two_ne_zero_of_charP_three (K := ZMod 3)
    · have h01 : (ggQ2x_graph D).Adj (j 0) (j 1) := hadj 0 (by omega)
      have hne : j 1 ≠ j 0 := h01.ne.symm
      have hc : D.cartan (j 1) (j 0) ≠ 0 := by
        rw [ggQ2x_graph, TauCeti.diagramGraph_adj] at h01
        exact h01.2.2
      have hcast := ggQ2x_cartan_cast_ne_zero D hbas h4 hne hc
      rw [show ggQ2x_prod D j (1 - 1) (D.coroot k) = D.coroot k from rfl, ← hj0,
        D.pairing]
      exact hcast
    · rw [show n + 1 + 1 = n + 2 from by omega,
        show n + 2 - 1 = n + 1 from by omega]
      have hv0 : D.root (j (n + 2)) (ggQ2x_prod D j n (D.coroot k)) = 0 :=
        ggQ2x_prod_kill D k (n + 2) j hj0 hdist n (by omega)
      have hIH : D.root (j (n + 1)) (ggQ2x_prod D j n (D.coroot k)) ≠ 0 :=
        ih (n + 1) (by omega) j hj0 (fun r hr => hadj r (by omega))
          (fun r hr => hdist r (by omega)) (fun t ht => hkill t (by omega))
      have hadj1 : (ggQ2x_graph D).Adj (j (n + 1)) (j (n + 2)) := hadj (n + 1) (by omega)
      have hne1 : j (n + 2) ≠ j (n + 1) := hadj1.ne.symm
      have hc1 : D.cartan (j (n + 2)) (j (n + 1)) ≠ 0 := by
        rw [ggQ2x_graph, TauCeti.diagramGraph_adj] at hadj1
        exact hadj1.2.2
      have hcast1 := ggQ2x_cartan_cast_ne_zero D hbas h4 hne1 hc1
      have hcomp : D.root (j (n + 2)) (D.simpleRefl (j (n + 1))
            (ggQ2x_prod D j n (D.coroot k))) =
          -(D.root (j (n + 1)) (ggQ2x_prod D j n (D.coroot k)) *
            (D.cartan (j (n + 2)) (j (n + 1)) : ZMod 3)) := by
        rw [show D.simpleRefl (j (n + 1)) (ggQ2x_prod D j n (D.coroot k)) =
            ggQ2x_prod D j n (D.coroot k) -
              D.root (j (n + 1)) (ggQ2x_prod D j n (D.coroot k)) •
                D.coroot (j (n + 1)) from
          Module.reflection_apply _ (D.root_coroot_self (j (n + 1)))]
        rw [map_sub, map_smul, smul_eq_mul, D.pairing, hv0]
        ring
      rw [show ggQ2x_prod D j (n + 1) =
          D.simpleRefl (j (n + 1)) * ggQ2x_prod D j n from rfl, LinearEquiv.mul_apply,
        hcomp]
      exact neg_ne_zero.mpr (mul_ne_zero hIH hcast1)

private lemma ggQ2x_cn_simple (D : GGQ2Lin 3) (hbas : D.Basis)
    (h4 : 4 ≤ Fintype.card D.ι) (k : D.ι) (δ : ↥D.rootPairs)
    (hk : D.root k δ.1.2 = 0) :
    ∃ ε : ↥D.rootPairs, ε.1.1 (D.coroot k) ≠ 0 ∧ ε.1.1 δ.1.2 ≠ 0 := by
  classical
  let Good : Finset D.ι := Finset.univ.filter (fun j => D.root j δ.1.2 ≠ 0)
  have hGood : Good.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hall : ∀ j, D.root j δ.1.2 = 0 := by
      intro j
      by_contra hj
      have hmem : j ∈ Good := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
      rw [h] at hmem
      exact absurd hmem (by simp)
    have hspan : δ.1.1 ∈ Submodule.span (ZMod 3) (Set.range D.root) :=
      ggQ2x_root_mem_span D δ
    have hzero : δ.1.1 δ.1.2 = 0 := by
      have hf : ∀ i, (Module.Dual.eval (ZMod 3) D.V (δ.1.2)) (D.root i) = 0 := by
        intro i; rw [Module.Dual.eval_apply]; exact hall i
      exact apply_eq_zero_of_mem_span_range hf hspan
    rw [ggQ2x_rootPair_self D δ] at hzero
    exact two_ne_zero_of_charP_three (K := ZMod 3) hzero
  obtain ⟨i, hiGood, hmin⟩ :=
    Finset.exists_min_image Good (fun j => (ggQ2x_graph D).dist k j) hGood
  have hi : D.root i δ.1.2 ≠ 0 := (Finset.mem_filter.mp hiGood).2
  have hik : i ≠ k := fun h => hi (by rw [h]; exact hk)
  obtain ⟨p, hp⟩ := (ggQ2x_connected D).exists_walk_length_eq_dist k i
  let j : ℕ → D.ι := fun r => p.getVert r
  have hj0 : j 0 = k := p.getVert_zero
  have hjm : j p.length = i := p.getVert_length
  have hpos : 1 ≤ p.length := by
    have hne : (ggQ2x_graph D).dist k i ≠ 0 := by
      rw [SimpleGraph.dist_ne_zero_iff_ne_and_reachable]
      exact ⟨hik.symm, (ggQ2x_connected D).preconnected k i⟩
    rw [← hp] at hne
    omega
  have hadj : ∀ r < p.length, (ggQ2x_graph D).Adj (j r) (j (r + 1)) := by
    intro r hr
    simpa [j] using p.adj_getVert_succ hr
  have hdist : ∀ r ≤ p.length, (ggQ2x_graph D).dist k (j r) = r := by
    intro r hr
    have h1 : (ggQ2x_graph D).dist k (j r) ≤ r := by
      have h := SimpleGraph.dist_le (p.take r)
      rw [SimpleGraph.Walk.take_length] at h
      rwa [min_eq_left hr] at h
    have h2 : r ≤ (ggQ2x_graph D).dist k (j r) := by
      have hd := SimpleGraph.dist_le (p.drop r)
      rw [SimpleGraph.Walk.drop_length] at hd
      have hd' : (ggQ2x_graph D).dist (j r) i ≤ p.length - r := by
        simpa [j] using hd
      have htri := (ggQ2x_connected D).dist_triangle (u := k) (v := j r) (w := i)
      rw [← hp] at htri
      omega
    omega
  have hkill : ∀ t < p.length, D.root (j t) δ.1.2 = 0 := by
    intro t ht
    by_contra hne
    have htGood : j t ∈ Good := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    have hle := hmin (j t) htGood
    have h1 := hdist t (le_of_lt ht)
    have h2 : (ggQ2x_graph D).dist k i = p.length := by
      simpa [hjm] using hdist p.length le_rfl
    omega
  have hmain : D.root i (ggQ2x_prod D j (p.length - 1) (D.coroot k)) ≠ 0 := by
    have h := ggQ2x_prod_ne_zero D hbas h4 δ k hk p.length j hj0 hadj hdist hkill
    rwa [hjm] at h
  have hfixδ : ∀ t, t + 1 ≤ p.length → ggQ2x_prod D j t δ.1.2 = δ.1.2 := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
        intro ht
        rw [show ggQ2x_prod D j (t + 1) =
          D.simpleRefl (j (t + 1)) * ggQ2x_prod D j t from rfl, LinearEquiv.mul_apply,
          ih (by omega)]
        rw [show D.simpleRefl (j (t + 1)) δ.1.2 =
          δ.1.2 - D.root (j (t + 1)) δ.1.2 • D.coroot (j (t + 1)) from
          Module.reflection_apply _ (D.root_coroot_self (j (t + 1)))]
        rw [hkill (t + 1) (by omega), zero_smul, sub_zero]
  have hfix : ggQ2x_prod D j (p.length - 1) δ.1.2 = δ.1.2 := hfixδ _ (by omega)
  have hu_mem : ggQ2x_prod D j (p.length - 1) ∈ D.weyl := by
    have hmem : ∀ t, ggQ2x_prod D j t ∈ D.weyl := by
      intro t
      induction t with
      | zero => exact D.weyl.one_mem
      | succ t ih =>
          rw [show ggQ2x_prod D j (t + 1) =
            D.simpleRefl (j (t + 1)) * ggQ2x_prod D j t from rfl]
          exact Subgroup.mul_mem _ (ggQ2x_simpleRefl_mem_weyl D _) ih
    exact hmem _
  let w := (ggQ2x_prod D j (p.length - 1))⁻¹
  have hw : w ∈ D.weyl := Subgroup.inv_mem _ hu_mem
  have hwsymm : w.symm = ggQ2x_prod D j (p.length - 1) := by
    change ((ggQ2x_prod D j (p.length - 1))⁻¹)⁻¹ =
      ggQ2x_prod D j (p.length - 1)
    rw [inv_inv]
  have hεmem : ((D.root i).comp (w.symm : D.V →ₗ[ZMod 3] D.V), w (D.coroot i)) ∈
      D.rootPairs :=
    ggQ2x_rootPairs_weyl D ⟨(D.root i, D.coroot i), ggQ2x_simplePair_mem D i⟩ w hw
  refine ⟨⟨((D.root i).comp (w.symm : D.V →ₗ[ZMod 3] D.V), w (D.coroot i)), hεmem⟩, ?_, ?_⟩
  · show D.root i (w.symm (D.coroot k)) ≠ 0
    rw [hwsymm]
    exact hmain
  · show D.root i (w.symm δ.1.2) ≠ 0
    rw [hwsymm, hfix]
    exact hi

private lemma ggQ2x_cn (D : GGQ2Lin 3) (hbas : D.Basis) (h4 : 4 ≤ Fintype.card D.ι)
    (γ δ : ↥D.rootPairs) (h : γ.1.1 δ.1.2 = 0) :
    ∃ ε : ↥D.rootPairs, ε.1.1 γ.1.2 ≠ 0 ∧ ε.1.1 δ.1.2 ≠ 0 := by
  obtain ⟨k, w, hw, h2, h1⟩ := γ.2
  have hw' : w.symm ∈ D.weyl := Subgroup.inv_mem _ hw
  let δ' : ↥D.rootPairs :=
    ⟨((δ.1.1).comp (w : D.V →ₗ[ZMod 3] D.V), w.symm δ.1.2),
      ggQ2x_rootPairs_weyl D δ w.symm hw'⟩
  have hδ' : D.root k δ'.1.2 = 0 := by
    change D.root k (w.symm δ.1.2) = 0
    have hh : γ.1.1 δ.1.2 = 0 := h
    rw [h1] at hh
    simpa [LinearMap.comp_apply] using hh
  obtain ⟨ε', hε'1, hε'2⟩ := ggQ2x_cn_simple D hbas h4 k δ' hδ'
  refine ⟨⟨((ε'.1.1).comp (w.symm : D.V →ₗ[ZMod 3] D.V), w ε'.1.2),
    ggQ2x_rootPairs_weyl D ε' w hw⟩, ?_, ?_⟩
  · show ε'.1.1 (w.symm γ.1.2) ≠ 0
    rw [h2, LinearEquiv.symm_apply_apply]
    exact hε'1
  · show ε'.1.1 (w.symm δ.1.2) ≠ 0
    exact hε'2

theorem ggQ2_connectivity {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) (hbas : D.Basis)
    (h4 : 4 ≤ Fintype.card D.ι) (c : D.V) :
    ∀ γ δ : ↥D.rootPairs, γ.1.1 c ≠ 0 → δ.1.1 c ≠ 0 →
      Relation.ReflTransGen
        (fun γ' δ' : ↥D.rootPairs => γ'.1.1 c ≠ 0 ∧ δ'.1.1 c ≠ 0 ∧ γ'.1.1 δ'.1.2 ≠ 0) γ δ := by
  subst hp
  intro γ δ hγc hδc
  by_cases hγδ : γ.1.1 δ.1.2 = 0
  · obtain ⟨ε, hεγ, hεδ⟩ := ggQ2x_cn D hbas h4 γ δ hγδ
    by_cases hεc : ε.1.1 c = 0
    · let sγ : D.V ≃ₗ[ZMod 3] D.V := Module.reflection (ggQ2x_rootPair_self D γ)
      have hsγ_mem : sγ ∈ D.weyl := ggQ2x_rootRefl_mem_weyl D γ
      have hsγ_inv : sγ.symm = sγ := Module.reflection_inv _
      have hsγ_apply : ∀ v, sγ v = v - γ.1.1 v • γ.1.2 := fun v =>
        Module.reflection_apply v (ggQ2x_rootPair_self D γ)
      let ε' : ↥D.rootPairs :=
        ⟨((ε.1.1).comp (sγ.symm : D.V →ₗ[ZMod 3] D.V), sγ ε.1.2),
          ggQ2x_rootPairs_weyl D ε sγ hsγ_mem⟩
      have hε'_apply : ∀ v, ε'.1.1 v = ε.1.1 v - γ.1.1 v * ε.1.1 γ.1.2 := by
        intro v
        change ε.1.1 (sγ.symm v) = ε.1.1 v - γ.1.1 v * ε.1.1 γ.1.2
        rw [hsγ_inv, hsγ_apply v, map_sub, map_smul, smul_eq_mul]
      have hε'c : ε'.1.1 c ≠ 0 := by
        rw [hε'_apply c, hεc, zero_sub]
        exact neg_ne_zero.mpr (mul_ne_zero hγc hεγ)
      have hε'γ : ε'.1.1 γ.1.2 ≠ 0 := by
        rw [hε'_apply γ.1.2, ggQ2x_rootPair_self D γ]
        have h2' : ε.1.1 γ.1.2 - 2 * ε.1.1 γ.1.2 = -ε.1.1 γ.1.2 := by ring
        rw [h2']
        exact neg_ne_zero.mpr hεγ
      have hε'δ : ε'.1.1 δ.1.2 ≠ 0 := by
        rw [hε'_apply δ.1.2, hγδ, zero_mul, sub_zero]
        exact hεδ
      have hγε' : γ.1.1 ε'.1.2 ≠ 0 := fun h0 =>
        hε'γ ((ggQ2x_zero_symm D hbas h4 γ ε').mp h0)
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.single ⟨hγc, hε'c, hγε'⟩) ⟨hε'c, hδc, hε'δ⟩
    · have hγε : γ.1.1 ε.1.2 ≠ 0 := fun h0 =>
        hεγ ((ggQ2x_zero_symm D hbas h4 γ ε).mp h0)
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.single ⟨hγc, hεc, hγε⟩) ⟨hεc, hδc, hεδ⟩
  · exact Relation.ReflTransGen.single ⟨hγc, hδc, hγδ⟩

end CFSG.StandardType

end

