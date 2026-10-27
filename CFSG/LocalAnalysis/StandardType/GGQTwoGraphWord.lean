module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphWordDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXGraphLinDefs

public section

namespace CFSG.StandardType

open Module

variable {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]

@[expose] noncomputable def ggQ2gwBasis (h : Fin n → U) (hli : LinearIndependent (ZMod 3) h)
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤) : Basis (Fin n) (ZMod 3) U :=
  Basis.mk hli hsp.ge

@[expose] noncomputable def ggQ2gwCoord (h : Fin n → U) (hli : LinearIndependent (ZMod 3) h)
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤) : U ≃ₗ[ZMod 3] (Fin n → ZMod 3) :=
  (ggQ2gwBasis h hli hsp).equivFun

theorem ggQ2gwCoord_h (h : Fin n → U) (hli : LinearIndependent (ZMod 3) h)
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤) (i : Fin n) :
    ggQ2gwCoord h hli hsp (h i) = ggQ2gwE i := by
  funext k
  have hb : ggQ2gwBasis h hli hsp i = h i := by
    rw [ggQ2gwBasis, Basis.mk_apply]
  rw [ggQ2gwCoord, ← hb, Basis.equivFun_self, ggQ2gwE]
  by_cases hik : i = k
  · subst hik
    simp
  · have hki : ¬k = i := fun h => hik h.symm
    simp [hik, hki]

private lemma ggQ2gw_sum_coord (h : Fin n → U) (hli : LinearIndependent (ZMod 3) h)
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤) (v : U) :
    ∑ k, ggQ2gwCoord h hli hsp v k • h k = v := by
  conv_rhs => rw [← (ggQ2gwBasis h hli hsp).sum_equivFun v]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show ggQ2gwBasis h hli hsp k = h k from by rw [ggQ2gwBasis, Basis.mk_apply]]
  rfl

theorem ggQ2gw_root_eq (C : Fin n → Fin n → ZMod 3) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (hα : ∀ i j, α i (h j) = C i j) (j : Fin n) (v : U) :
    α j v = ggQ2gwRoot C j (ggQ2gwCoord h hli hsp v) := by
  have hb : ∀ k, ggQ2gwBasis h hli hsp k = h k := fun k => by
    rw [ggQ2gwBasis, Basis.mk_apply]
  have hv : ∑ k, ggQ2gwCoord h hli hsp v k • h k = v := by
    conv_rhs => rw [← (ggQ2gwBasis h hli hsp).sum_equivFun v]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hb k]
    rfl
  conv_lhs => rw [← hv]
  rw [map_sum, ggQ2gwRoot]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, hα j k, smul_eq_mul, mul_comm]

@[expose] noncomputable def ggQ2gwElt (h : Fin n → U) (α : Fin n → Dual (ZMod 3) U)
    (h2 : ∀ j, α j (h j) = 2) (l : List (Fin n)) : U ≃ₗ[ZMod 3] U :=
  (l.map fun j => Module.reflection (h2 j)).prod

private lemma ggQ2gwElt_nil {h : Fin n → U} {α : Fin n → Dual (ZMod 3) U}
    {h2 : ∀ j, α j (h j) = 2} : ggQ2gwElt h α h2 ([] : List (Fin n)) = 1 := by
  simp [ggQ2gwElt]

private lemma ggQ2gwElt_append {h : Fin n → U} {α : Fin n → Dual (ZMod 3) U}
    {h2 : ∀ j, α j (h j) = 2} (l₁ l₂ : List (Fin n)) :
    ggQ2gwElt h α h2 (l₁ ++ l₂) =
      ggQ2gwElt h α h2 l₁ * ggQ2gwElt h α h2 l₂ := by
  simp [ggQ2gwElt, List.map_append, List.prod_append]

private lemma ggQ2gwElt_cons {h : Fin n → U} {α : Fin n → Dual (ZMod 3) U}
    {h2 : ∀ j, α j (h j) = 2} (j : Fin n) (l : List (Fin n)) :
    ggQ2gwElt h α h2 (j :: l) =
      Module.reflection (h2 j) * ggQ2gwElt h α h2 l := by
  simp [ggQ2gwElt]

private lemma ggQ2gwElt_singleton {h : Fin n → U} {α : Fin n → Dual (ZMod 3) U}
    {h2 : ∀ j, α j (h j) = 2} (j : Fin n) :
    ggQ2gwElt h α h2 [j] = Module.reflection (h2 j) := by
  simp [ggQ2gwElt]

theorem ggQ2gwElt_mem (h : Fin n → U) (α : Fin n → Dual (ZMod 3) U) (h2 : ∀ j, α j (h j) = 2)
    (l : List (Fin n)) : ggQ2gwElt h α h2 l ∈ ggQ2WeylOf h α := by
  induction l with
  | nil => simp [ggQ2gwElt]
  | cons j l ih =>
    rw [ggQ2gwElt, List.map_cons, List.prod_cons]
    refine Subgroup.mul_mem _ ?_ ih
    exact Subgroup.subset_closure ⟨j, fun v => Module.reflection_apply (h := h2 j) v⟩

private lemma ggQ2gw_sub_smul_e (C : Fin n → Fin n → ZMod 3) (j : Fin n)
    (y : Fin n → ZMod 3) :
    y - (∑ k, C j k * y k) • ggQ2gwE j = ggQ2gwRefl C j y := by
  funext i
  rw [Pi.sub_apply, Pi.smul_apply, ggQ2gwE, ggQ2gwRefl]
  by_cases h : i = j <;> simp [h]

theorem ggQ2gwElt_coord (C : Fin n → Fin n → ZMod 3) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (hα : ∀ i j, α i (h j) = C i j) (h2 : ∀ j, α j (h j) = 2)
    (l : List (Fin n)) (v : U) :
    ggQ2gwCoord h hli hsp (ggQ2gwElt h α h2 l v) = ggQ2gwAct C l (ggQ2gwCoord h hli hsp v) := by
  induction l with
  | nil => simp [ggQ2gwElt, ggQ2gwAct]
  | cons j l ih =>
    have hstep : ggQ2gwElt h α h2 (j :: l) =
        Module.reflection (h2 j) * ggQ2gwElt h α h2 l := ggQ2gwElt_cons j l
    have hroot : α j (ggQ2gwElt h α h2 l v) =
        ggQ2gwRoot C j (ggQ2gwAct C l (ggQ2gwCoord h hli hsp v)) := by
      rw [ggQ2gw_root_eq C h hli hsp α hα j, ih]
    rw [hstep, LinearEquiv.mul_apply, Module.reflection_apply (h := h2 j), map_sub,
      map_smul, ih, ggQ2gwCoord_h, hroot]
    change ggQ2gwAct C l (ggQ2gwCoord h hli hsp v) -
        ggQ2gwRoot C j (ggQ2gwAct C l (ggQ2gwCoord h hli hsp v)) • ggQ2gwE j =
      ggQ2gwRefl C j (ggQ2gwAct C l (ggQ2gwCoord h hli hsp v))
    rw [← ggQ2gw_sub_smul_e C j (ggQ2gwAct C l (ggQ2gwCoord h hli hsp v))]
    rfl

theorem ggQ2gwElt_reverse (h : Fin n → U) (α : Fin n → Dual (ZMod 3) U)
    (h2 : ∀ j, α j (h j) = 2) (l : List (Fin n)) :
    ggQ2gwElt h α h2 l.reverse = (ggQ2gwElt h α h2 l)⁻¹ := by
  induction l with
  | nil => simp [ggQ2gwElt]
  | cons j l ih =>
    rw [List.reverse_cons, ggQ2gwElt_append, ggQ2gwElt_singleton, ih, ggQ2gwElt_cons,
      mul_inv_rev, Module.reflection_inv]

private lemma ggQ2gw_kill_f (h : Fin 4 → U) (hli : LinearIndependent (ZMod 3) h)
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤) (φ : Fin 3 → Fin 4 → ZMod 3)
    (f : Fin 3 → Dual (ZMod 3) U) (hfh : ∀ m k, f m (h k) = φ m k) :
    ∀ m (v : U), f m v = ggQ2gwDot (φ m) (ggQ2gwCoord h hli hsp v) := by
  intro m v
  calc f m v = f m (∑ k, ggQ2gwCoord h hli hsp v k • h k) := by
        rw [ggQ2gw_sum_coord h hli hsp v]
    _ = ∑ k, ggQ2gwCoord h hli hsp v k • f m (h k) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [map_smul]
    _ = ∑ k, ggQ2gwCoord h hli hsp v k • φ m k :=
        Finset.sum_congr rfl fun k _ => by rw [hfh m k]
    _ = ggQ2gwDot (φ m) (ggQ2gwCoord h hli hsp v) := by
        rw [ggQ2gwDot]
        exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul, mul_comm]

private lemma ggQ2gw_kill_conn (φ : Fin 3 → Fin 4 → ZMod 3) (cc : Fin 3 → Fin 4 → ZMod 3)
    (f : Fin 3 → Dual (ZMod 3) U) (c : Fin 3 → U)
    (hdot : ∀ a b : Fin 3, f a (c b) = ggQ2gwDot (φ a) (cc b))
    (h4 : ggQ2gwDot (φ 0) (cc 1) ≠ 0 ∨ ggQ2gwDot (φ 1) (cc 0) ≠ 0)
    (h5 : ggQ2gwDot (φ 1) (cc 2) ≠ 0 ∨ ggQ2gwDot (φ 2) (cc 1) ≠ 0) :
    ∀ S : Set (Fin 3), S.Nonempty →
      (∀ i j, (f i (c j) ≠ 0 ∨ f j (c i) ≠ 0) → (i ∈ S ↔ j ∈ S)) → S = Set.univ := by
  intro S hne hcl
  have hj01 : f 0 (c 1) ≠ 0 ∨ f 1 (c 0) ≠ 0 := by
    rw [hdot 0 1, hdot 1 0]
    exact h4
  have hj12 : f 1 (c 2) ≠ 0 ∨ f 2 (c 1) ≠ 0 := by
    rw [hdot 1 2, hdot 2 1]
    exact h5
  have h0 : (0 : Fin 3) ∈ S → ∀ i, i ∈ S := by
    intro h0 i
    have h1 : (1 : Fin 3) ∈ S := (hcl 0 1 hj01).mp h0
    have h2 : (2 : Fin 3) ∈ S := (hcl 1 2 hj12).mp h1
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have h1 : (1 : Fin 3) ∈ S → ∀ i, i ∈ S := by
    intro h1 i
    have h0 : (0 : Fin 3) ∈ S := (hcl 0 1 hj01).mpr h1
    have h2 : (2 : Fin 3) ∈ S := (hcl 1 2 hj12).mp h1
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have h2 : (2 : Fin 3) ∈ S → ∀ i, i ∈ S := by
    intro h2v i
    have h1 : (1 : Fin 3) ∈ S := (hcl 1 2 hj12).mpr h2v
    have h0 : (0 : Fin 3) ∈ S := (hcl 0 1 hj01).mpr h1
    fin_cases i
    · exact h0
    · exact h1
    · exact h2v
  obtain ⟨i₀, hi₀⟩ := hne
  refine Set.eq_univ_of_forall ?_
  intro i
  fin_cases i₀
  · exact h0 hi₀ i
  · exact h1 hi₀ i
  · exact h2 hi₀ i

private lemma ggQ2gw_kill_ker (h : Fin 4 → U) (hli : LinearIndependent (ZMod 3) h)
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤) (E : GGQ2gwKill) (d : U)
    (hd : ggQ2gwCoord h hli hsp d = E.d) (φ : Fin 3 → Fin 4 → ZMod 3)
    (f : Fin 3 → Dual (ZMod 3) U)
    (hf : ∀ m (v : U), f m v = ggQ2gwDot (φ m) (ggQ2gwCoord h hli hsp v))
    (h6 : ∀ x : Fin 4 → ZMod 3, (∀ m, ggQ2gwDot (φ m) x = 0) → x = 0 ∨ x = E.d ∨ x = -E.d) :
    ∀ u : U, (∀ m, f m u = 0) → u ∈ Submodule.span (ZMod 3) ({d} : Set U) := by
  intro u hu
  have hu' : ∀ m, ggQ2gwDot (φ m) (ggQ2gwCoord h hli hsp u) = 0 := by
    intro m
    rw [← hf m u]
    exact hu m
  rcases h6 (ggQ2gwCoord h hli hsp u) hu' with h0 | hd' | hneg
  · have hu0 : u = 0 := by
      apply (ggQ2gwCoord h hli hsp).injective
      rw [h0, map_zero]
    rw [hu0]
    exact Submodule.zero_mem _
  · have hud : u = d := by
      apply (ggQ2gwCoord h hli hsp).injective
      rw [hd', hd]
    rw [hud]
    exact Submodule.mem_span_singleton_self d
  · have hud : u = -d := by
      apply (ggQ2gwCoord h hli hsp).injective
      rw [hneg, map_neg, hd]
    rw [hud]
    exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self d)

private lemma ggQ2gw_kill_span (h : Fin 4 → U) (hli : LinearIndependent (ZMod 3) h)
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤) (E : GGQ2gwKill)
    (h7 : ∀ k, ggQ2gwE k = E.inv k 0 • E.c 0 + E.inv k 1 • E.c 1 + E.inv k 2 • E.c 2 +
      E.inv k 3 • E.d) (d : U) (hd : ggQ2gwCoord h hli hsp d = E.d) (c : Fin 3 → U)
    (hc : ∀ m, ggQ2gwCoord h hli hsp (c m) = E.c m) :
    Submodule.span (ZMod 3) (Set.range c) ⊔ Submodule.span (ZMod 3) ({d} : Set U) = ⊤ := by
  rw [eq_top_iff, ← hsp, Submodule.span_le]
  rintro x ⟨k, rfl⟩
  have h7k := h7 k
  have hcoord : ggQ2gwCoord h hli hsp (h k) =
      ggQ2gwCoord h hli hsp (E.inv k 0 • c 0 + E.inv k 1 • c 1 + E.inv k 2 • c 2 +
        E.inv k 3 • d) := by
    rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
      hc 0, hc 1, hc 2, hd, ggQ2gwCoord_h, h7k]
  have hk : h k = E.inv k 0 • c 0 + E.inv k 1 • c 1 + E.inv k 2 • c 2 + E.inv k 3 • d :=
    (ggQ2gwCoord h hli hsp).injective hcoord
  rw [hk]
  have hc0 : c 0 ∈ Submodule.span (ZMod 3) (Set.range c) :=
    Submodule.subset_span (Set.mem_range_self 0)
  have hc1 : c 1 ∈ Submodule.span (ZMod 3) (Set.range c) :=
    Submodule.subset_span (Set.mem_range_self 1)
  have hc2 : c 2 ∈ Submodule.span (ZMod 3) (Set.range c) :=
    Submodule.subset_span (Set.mem_range_self 2)
  have hcd : d ∈ Submodule.span (ZMod 3) ({d} : Set U) := Submodule.mem_span_singleton_self d
  have hm0 : E.inv k 0 • c 0 ∈
      Submodule.span (ZMod 3) (Set.range c) ⊔ Submodule.span (ZMod 3) ({d} : Set U) :=
    Submodule.mem_sup_left (Submodule.smul_mem _ _ hc0)
  have hm1 : E.inv k 1 • c 1 ∈
      Submodule.span (ZMod 3) (Set.range c) ⊔ Submodule.span (ZMod 3) ({d} : Set U) :=
    Submodule.mem_sup_left (Submodule.smul_mem _ _ hc1)
  have hm2 : E.inv k 2 • c 2 ∈
      Submodule.span (ZMod 3) (Set.range c) ⊔ Submodule.span (ZMod 3) ({d} : Set U) :=
    Submodule.mem_sup_left (Submodule.smul_mem _ _ hc2)
  have hmd : E.inv k 3 • d ∈
      Submodule.span (ZMod 3) (Set.range c) ⊔ Submodule.span (ZMod 3) ({d} : Set U) :=
    Submodule.mem_sup_right (Submodule.smul_mem _ _ hcd)
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ hm0 hm1) hm2) hmd

theorem ggQ2gw_kill_of_entry (C : Fin 4 → Fin 4 → ZMod 3) {U : Type} [AddCommGroup U]
    [Module (ZMod 3) U] (h : Fin 4 → U) (hli : LinearIndependent (ZMod 3) h)
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤) (α : Fin 4 → Dual (ZMod 3) U)
    (hα : ∀ i j, α i (h j) = C i j) (hdiag : ∀ j, C j j = 2) (E : GGQ2gwKill) (hE : E.OK C)
    (d : U) (hd : ggQ2gwCoord h hli hsp d = E.d) : GGQ2KillFamily h α d := by
  obtain ⟨h1, h2', h3, h4, h5, h6, h7⟩ := hE
  have h2 : ∀ j, α j (h j) = 2 := fun j => (hα j j).trans (hdiag j)
  let c : Fin 3 → U := fun m => ggQ2gwElt h α h2 (E.w m) (h (E.j m))
  let f : Fin 3 → Dual (ZMod 3) U :=
    fun m => (α (E.j m)).comp (ggQ2gwElt h α h2 (E.w m).reverse).toLinearMap
  have hc : ∀ m, ggQ2gwCoord h hli hsp (c m) = E.c m := by
    intro m
    show ggQ2gwCoord h hli hsp (ggQ2gwElt h α h2 (E.w m) (h (E.j m))) = E.c m
    rw [ggQ2gwElt_coord C h hli hsp α hα h2, ggQ2gwCoord_h, h1 m]
  have hfh : ∀ m k, f m (h k) = E.φ m k := by
    intro m k
    show α (E.j m) ((ggQ2gwElt h α h2 (E.w m).reverse) (h k)) = E.φ m k
    rw [ggQ2gw_root_eq C h hli hsp α hα (E.j m), ggQ2gwElt_coord C h hli hsp α hα h2,
      ggQ2gwCoord_h]
    exact h2' m k
  have hf : ∀ m (v : U), f m v = ggQ2gwDot (E.φ m) (ggQ2gwCoord h hli hsp v) :=
    ggQ2gw_kill_f h hli hsp E.φ f hfh
  have hfc : ∀ m, f m (c m) = 2 := by
    intro m
    show α (E.j m) ((ggQ2gwElt h α h2 (E.w m).reverse)
      (ggQ2gwElt h α h2 (E.w m) (h (E.j m)))) = 2
    rw [ggQ2gwElt_reverse, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact h2 (E.j m)
  have hmem : ∀ m, Module.reflection (hfc m) ∈ ggQ2WeylOf h α := by
    intro m
    have hconj : Module.reflection (hfc m) =
        ggQ2gwElt h α h2 (E.w m) * Module.reflection (h2 (E.j m)) *
          (ggQ2gwElt h α h2 (E.w m))⁻¹ := by
      ext v
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Module.reflection_apply (h := hfc m),
        Module.reflection_apply (h := h2 (E.j m)), map_sub, map_smul, LinearEquiv.coe_inv,
        LinearEquiv.apply_symm_apply]
      simp only [f, c]
      rw [ggQ2gwElt_reverse]
      rfl
    rw [hconj]
    have hW : ggQ2gwElt h α h2 (E.w m) ∈ ggQ2WeylOf h α := ggQ2gwElt_mem h α h2 (E.w m)
    have hR : Module.reflection (h2 (E.j m)) ∈ ggQ2WeylOf h α :=
      Subgroup.subset_closure ⟨E.j m, fun v => Module.reflection_apply (h := h2 (E.j m)) v⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hW hR) (Subgroup.inv_mem _ hW)
  have hkill : ∀ m, f m d = 0 := by
    intro m
    rw [hf m d, hd, h3 m]
  have hconn := ggQ2gw_kill_conn E.φ E.c f c (fun a b => by rw [hf a (c b), hc b]) h4 h5
  have hker := ggQ2gw_kill_ker h hli hsp E d hd E.φ f hf h6
  have hspan := ggQ2gw_kill_span h hli hsp E h7 d hd c hc
  exact ⟨Fin 3, ⟨(0 : Fin 3)⟩, c, f, hfc, hmem, hkill, hconn, hker, Or.inl hspan⟩

private lemma ggQ2gw_word_sign (C : Fin n → Fin n → ZMod 3) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (hα : ∀ i j, α i (h j) = C i j) (h2 : ∀ j, α j (h j) = 2)
    (base : Fin n → ZMod 3) (word : (Fin n → ZMod 3) → List (Fin n)) (x : Fin n → ZMod 3)
    (hx : ggQ2gwAct C (word x) x = base ∨ ggQ2gwAct C (word x) x = -base) :
    ggQ2gwElt h α h2 (word x) ((ggQ2gwCoord h hli hsp).symm x) =
        (ggQ2gwCoord h hli hsp).symm base ∨
      ggQ2gwElt h α h2 (word x) ((ggQ2gwCoord h hli hsp).symm x) =
        -((ggQ2gwCoord h hli hsp).symm base) := by
  have hcoord := ggQ2gwElt_coord C h hli hsp α hα h2 (word x)
    ((ggQ2gwCoord h hli hsp).symm x)
  rcases hx with hw | hw
  · left
    refine (ggQ2gwCoord h hli hsp).injective ?_
    rw [hcoord, LinearEquiv.apply_symm_apply, hw, LinearEquiv.apply_symm_apply]
  · right
    refine (ggQ2gwCoord h hli hsp).injective ?_
    rw [hcoord, LinearEquiv.apply_symm_apply, hw, map_neg, LinearEquiv.apply_symm_apply]

theorem ggQ2gw_line_of_trans (C : Fin n → Fin n → ZMod 3) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (hα : ∀ i j, α i (h j) = C i j) (h2 : ∀ j, α j (h j) = 2)
    (S : (Fin n → ZMod 3) → Prop) (base : Fin n → ZMod 3)
    (word : (Fin n → ZMod 3) → List (Fin n))
    (hword : ∀ x, S x → ggQ2gwAct C (word x) x = base ∨ ggQ2gwAct C (word x) x = -base)
    (d : U) (hd : S (ggQ2gwCoord h hli hsp d))
    (hT : ∀ T : U ≃ₗ[ZMod 3] U, T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)) →
      S (ggQ2gwCoord h hli hsp (T.symm d))) :
    GGQ2LineCrit h α d := by
  intro T hTmem
  have hx2 : S (ggQ2gwCoord h hli hsp (T.symm d)) := hT T hTmem
  have hb1 := ggQ2gw_word_sign C h hli hsp α hα h2 base word
    (ggQ2gwCoord h hli hsp d) (hword (ggQ2gwCoord h hli hsp d) hd)
  rw [LinearEquiv.symm_apply_apply] at hb1
  have hb2 := ggQ2gw_word_sign C h hli hsp α hα h2 base word
    (ggQ2gwCoord h hli hsp (T.symm d)) (hword (ggQ2gwCoord h hli hsp (T.symm d)) hx2)
  rw [LinearEquiv.symm_apply_apply] at hb2
  have hcancel : ((ggQ2gwElt h α h2 (word (ggQ2gwCoord h hli hsp (T.symm d))))⁻¹)
      (ggQ2gwElt h α h2 (word (ggQ2gwCoord h hli hsp (T.symm d))) (T.symm d)) = T.symm d := by
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  have hneg2 : ((ggQ2gwElt h α h2 (word (ggQ2gwCoord h hli hsp (T.symm d))))⁻¹)
      (-((ggQ2gwCoord h hli hsp).symm base)) =
      -(((ggQ2gwElt h α h2 (word (ggQ2gwCoord h hli hsp (T.symm d))))⁻¹)
        ((ggQ2gwCoord h hli hsp).symm base)) := map_neg _ _
  have key : ggQ2gwElt h α h2 (word (ggQ2gwCoord h hli hsp (T.symm d))).reverse
        (ggQ2gwElt h α h2 (word (ggQ2gwCoord h hli hsp d)) d) = T.symm d ∨
      ggQ2gwElt h α h2 (word (ggQ2gwCoord h hli hsp (T.symm d))).reverse
        (ggQ2gwElt h α h2 (word (ggQ2gwCoord h hli hsp d)) d) = -T.symm d := by
    rcases hb1 with h1 | h1 <;> rcases hb2 with h2' | h2'
    · left
      have hc := congrArg (fun v : U =>
        ((ggQ2gwElt h α h2 (word (ggQ2gwCoord h hli hsp (T.symm d))))⁻¹) v) h2'
      rw [hcancel] at hc
      rw [h1, ggQ2gwElt_reverse]
      exact hc.symm
    · right
      have hc := congrArg (fun v : U =>
        ((ggQ2gwElt h α h2 (word (ggQ2gwCoord h hli hsp (T.symm d))))⁻¹) v) h2'
      rw [hcancel, hneg2] at hc
      rw [h1, ggQ2gwElt_reverse]
      exact neg_eq_iff_eq_neg.mp hc.symm
    · right
      have hc := congrArg (fun v : U =>
        ((ggQ2gwElt h α h2 (word (ggQ2gwCoord h hli hsp (T.symm d))))⁻¹) v) h2'
      rw [hcancel] at hc
      rw [h1, ggQ2gwElt_reverse, hneg2, ← hc]
    · left
      have hc := congrArg (fun v : U =>
        ((ggQ2gwElt h α h2 (word (ggQ2gwCoord h hli hsp (T.symm d))))⁻¹) v) h2'
      rw [hcancel, hneg2] at hc
      rw [h1, ggQ2gwElt_reverse, hneg2, ← hc]
  refine ⟨ggQ2gwElt h α h2 (word (ggQ2gwCoord h hli hsp (T.symm d))).reverse *
      ggQ2gwElt h α h2 (word (ggQ2gwCoord h hli hsp d)), ?_, ?_⟩
  · have hrev : ggQ2gwElt h α h2 (word (ggQ2gwCoord h hli hsp (T.symm d))).reverse ∈
        ggQ2WeylOf h α := by
      rw [ggQ2gwElt_reverse]
      exact Subgroup.inv_mem _
        (ggQ2gwElt_mem h α h2 (word (ggQ2gwCoord h hli hsp (T.symm d))))
    exact Subgroup.mul_mem _ hrev
      (ggQ2gwElt_mem h α h2 (word (ggQ2gwCoord h hli hsp d)))
  · rw [LinearEquiv.mul_apply]
    rcases key with key | key
    · rw [key, LinearEquiv.apply_symm_apply]
      exact Submodule.mem_span_singleton_self d
    · rw [key, show T (-(T.symm d)) = -(T (T.symm d)) from map_neg _ _,
        LinearEquiv.apply_symm_apply]
      exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self d)

@[expose] noncomputable def ggQ2gwForm (wt : Fin n → ZMod 3) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (u v : U) : ZMod 3 :=
  ∑ i, wt i * ggQ2gwCoord h hli hsp u i * α i v

private lemma ggQ2gwForm_add_left (wt : Fin n → ZMod 3) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (u₁ u₂ v : U) :
    ggQ2gwForm wt h hli hsp α (u₁ + u₂) v =
      ggQ2gwForm wt h hli hsp α u₁ v + ggQ2gwForm wt h hli hsp α u₂ v := by
  simp only [ggQ2gwForm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, Pi.add_apply]
  ring_nf

private lemma ggQ2gwForm_add_right (wt : Fin n → ZMod 3) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (u v₁ v₂ : U) :
    ggQ2gwForm wt h hli hsp α u (v₁ + v₂) =
      ggQ2gwForm wt h hli hsp α u v₁ + ggQ2gwForm wt h hli hsp α u v₂ := by
  simp only [ggQ2gwForm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add]
  ring_nf

private lemma ggQ2gwForm_smul_left (wt : Fin n → ZMod 3) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (a : ZMod 3) (u v : U) :
    ggQ2gwForm wt h hli hsp α (a • u) v = a * ggQ2gwForm wt h hli hsp α u v := by
  simp only [ggQ2gwForm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  ring_nf

private lemma ggQ2gwForm_smul_right (wt : Fin n → ZMod 3) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (a : ZMod 3) (u v : U) :
    ggQ2gwForm wt h hli hsp α u (a • v) = a * ggQ2gwForm wt h hli hsp α u v := by
  simp only [ggQ2gwForm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  ring_nf

private lemma ggQ2gwForm_neg_left (wt : Fin n → ZMod 3) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (u v : U) :
    ggQ2gwForm wt h hli hsp α (-u) v = -ggQ2gwForm wt h hli hsp α u v := by
  have h0 : ggQ2gwForm wt h hli hsp α (0 : U) v = 0 := by simp [ggQ2gwForm]
  have hadd := ggQ2gwForm_add_left wt h hli hsp α u (-u) v
  rw [add_neg_cancel, h0] at hadd
  exact eq_neg_of_add_eq_zero_right hadd.symm

private lemma ggQ2gwForm_neg_right (wt : Fin n → ZMod 3) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (u v : U) :
    ggQ2gwForm wt h hli hsp α u (-v) = -ggQ2gwForm wt h hli hsp α u v := by
  have h0 : ggQ2gwForm wt h hli hsp α u (0 : U) = 0 := by simp [ggQ2gwForm]
  have hadd := ggQ2gwForm_add_right wt h hli hsp α u v (-v)
  rw [add_neg_cancel, h0] at hadd
  exact eq_neg_of_add_eq_zero_right hadd.symm

private lemma ggQ2gwForm_sub_smul_left (wt : Fin n → ZMod 3) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (c : U) (a : ZMod 3) (u v : U) :
    ggQ2gwForm wt h hli hsp α (u - a • c) v =
      ggQ2gwForm wt h hli hsp α u v - a * ggQ2gwForm wt h hli hsp α c v := by
  simp only [sub_eq_add_neg]
  rw [ggQ2gwForm_add_left, ggQ2gwForm_neg_left, ggQ2gwForm_smul_left]
  rfl

private lemma ggQ2gwForm_sub_smul_right (wt : Fin n → ZMod 3) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (c : U) (a : ZMod 3) (u v : U) :
    ggQ2gwForm wt h hli hsp α u (v - a • c) =
      ggQ2gwForm wt h hli hsp α u v - a * ggQ2gwForm wt h hli hsp α u c := by
  simp only [sub_eq_add_neg]
  rw [ggQ2gwForm_add_right, ggQ2gwForm_neg_right, ggQ2gwForm_smul_right]
  rfl

theorem ggQ2gwForm_self (C : Fin n → Fin n → ZMod 3) (wt : Fin n → ZMod 3) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (hα : ∀ i j, α i (h j) = C i j) (u : U) :
    ggQ2gwForm wt h hli hsp α u u = ggQ2gwQ C wt (ggQ2gwCoord h hli hsp u) := by
  rw [ggQ2gwForm, ggQ2gwQ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ggQ2gw_root_eq C h hli hsp α hα i u]

private lemma ggQ2gwForm_h_left (wt : Fin n → ZMod 3) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (k : Fin n) (v : U) :
    ggQ2gwForm wt h hli hsp α (h k) v = wt k * α k v := by
  simp only [ggQ2gwForm]
  rw [Finset.sum_eq_single k]
  · rw [ggQ2gwCoord_h, ggQ2gwE]
    simp
  · intro i _ hik
    rw [ggQ2gwCoord_h, ggQ2gwE]
    simp [hik]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private lemma ggQ2gwForm_h_right (C : Fin n → Fin n → ZMod 3) (wt : Fin n → ZMod 3)
    (hsym : ∀ i j, wt i * C i j = wt j * C j i) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (hα : ∀ i j, α i (h j) = C i j) (u : U) (k : Fin n) :
    ggQ2gwForm wt h hli hsp α u (h k) = wt k * α k u := by
  rw [ggQ2gwForm, ggQ2gw_root_eq C h hli hsp α hα k u, ggQ2gwRoot, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hα i k]
  calc wt i * ggQ2gwCoord h hli hsp u i * C i k
      = (wt i * C i k) * ggQ2gwCoord h hli hsp u i := by ring
    _ = (wt k * C k i) * ggQ2gwCoord h hli hsp u i := by rw [hsym i k]
    _ = wt k * (C k i * ggQ2gwCoord h hli hsp u i) := by ring

private lemma ggQ2gwForm_gen (C : Fin n → Fin n → ZMod 3) (wt : Fin n → ZMod 3)
    (hsym : ∀ i j, wt i * C i j = wt j * C j i) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (hα : ∀ i j, α i (h j) = C i j) (hdiag : ∀ j, C j j = 2)
    (k : Fin n) (x : U ≃ₗ[ZMod 3] U) (hx : ∀ v, x v = v - α k v • h k) (u v : U) :
    ggQ2gwForm wt h hli hsp α (x u) (x v) = ggQ2gwForm wt h hli hsp α u v := by
  have h2k : α k (h k) = 2 := (hα k k).trans (hdiag k)
  have hBhh : ggQ2gwForm wt h hli hsp α (h k) (h k) = wt k * 2 := by
    rw [ggQ2gwForm_h_left, h2k]
  rw [hx u, hx v]
  simp only [ggQ2gwForm_sub_smul_left, ggQ2gwForm_sub_smul_right]
  rw [ggQ2gwForm_h_right C wt hsym h hli hsp α hα u k,
    ggQ2gwForm_h_left wt h hli hsp α k v, hBhh]
  ring

private lemma ggQ2gwForm_closure (C : Fin n → Fin n → ZMod 3) (wt : Fin n → ZMod 3)
    (hsym : ∀ i j, wt i * C i j = wt j * C j i) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (hα : ∀ i j, α i (h j) = C i j) (hdiag : ∀ j, C j j = 2) :
    ∀ x ∈ ggQ2WeylOf h α, ∀ u v : U,
      ggQ2gwForm wt h hli hsp α (x u) (x v) = ggQ2gwForm wt h hli hsp α u v := by
  let H : Subgroup (U ≃ₗ[ZMod 3] U) :=
    { carrier := {x | ∀ u v : U, ggQ2gwForm wt h hli hsp α (x u) (x v) =
        ggQ2gwForm wt h hli hsp α u v}
      one_mem' := by
        intro u v
        simp
      mul_mem' := by
        intro x y hx hy u v
        simp only [LinearEquiv.mul_apply]
        rw [hx, hy]
      inv_mem' := by
        intro x hx u v
        rw [LinearEquiv.coe_inv]
        have h := hx (x.symm u) (x.symm v)
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
        exact h.symm }
  have hgen : ({t : U ≃ₗ[ZMod 3] U | ∃ j, ∀ v, t v = v - α j v • h j}) ⊆ H := by
    rintro y ⟨k, hk⟩
    exact ggQ2gwForm_gen C wt hsym h hli hsp α hα hdiag k y hk
  intro x hx
  have hle : Subgroup.closure {t : U ≃ₗ[ZMod 3] U | ∃ j, ∀ v, t v = v - α j v • h j} ≤ H :=
    (Subgroup.closure_le H).mpr hgen
  exact hle hx

theorem ggQ2gwForm_mem_weyl (C : Fin n → Fin n → ZMod 3) (wt : Fin n → ZMod 3)
    (hsym : ∀ i j, wt i * C i j = wt j * C j i) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (hα : ∀ i j, α i (h j) = C i j) (hdiag : ∀ j, C j j = 2)
    {g : U ≃ₗ[ZMod 3] U} (hg : g ∈ ggQ2WeylOf h α) (u v : U) :
    ggQ2gwForm wt h hli hsp α (g u) (g v) = ggQ2gwForm wt h hli hsp α u v :=
  ggQ2gwForm_closure C wt hsym h hli hsp α hα hdiag g hg u v

private lemma zmod3_eq_two_mul_of_neg_sub {x a l : ZMod 3} (h : -(x - a * l) = x) :
    x = 2 * (a * l) := by
  have h1 : a * l - x = x := (neg_sub x (a * l)).symm.trans h
  have h2 : a * l = x + x := eq_add_of_sub_eq' h1
  have h' : a * l = 2 * x := h2.trans (two_mul x).symm
  have hchar : (2 : ZMod 3) * 2 = 1 := by decide
  calc x = (2 * 2) * x := by rw [hchar, one_mul]
    _ = 2 * (2 * x) := by ring
    _ = 2 * (a * l) := by rw [← h']

private lemma ggQ2gwForm_normalizer_weyl (C : Fin n → Fin n → ZMod 3) (wt : Fin n → ZMod 3)
    (hsym : ∀ i j, wt i * C i j = wt j * C j i) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (hα : ∀ i j, α i (h j) = C i j) (hdiag : ∀ j, C j j = 2)
    (T : U ≃ₗ[ZMod 3] U)
    (hT : T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)))
    {g : U ≃ₗ[ZMod 3] U} (hg : g ∈ ggQ2WeylOf h α) (u v : U) :
    ggQ2gwForm wt h hli hsp α (T (g u)) (T (g v)) =
      ggQ2gwForm wt h hli hsp α (T u) (T v) := by
  have hconj : T * g * T⁻¹ ∈ ggQ2WeylOf h α :=
    (Subgroup.mem_normalizer_iff.mp hT g).mp hg
  have hTu : (T * g * T⁻¹) (T u) = T (g u) := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply]
  have hTv : (T * g * T⁻¹) (T v) = T (g v) := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply]
  rw [← hTu, ← hTv]
  exact ggQ2gwForm_mem_weyl C wt hsym h hli hsp α hα hdiag hconj (T u) (T v)

private lemma ggQ2gwForm_normalizer_h_left (C : Fin n → Fin n → ZMod 3) (wt : Fin n → ZMod 3)
    (hsym : ∀ i j, wt i * C i j = wt j * C j i) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (hα : ∀ i j, α i (h j) = C i j) (hdiag : ∀ j, C j j = 2)
    (T : U ≃ₗ[ZMod 3] U)
    (hT : T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)))
    (i : Fin n) (v : U) :
    ggQ2gwForm wt h hli hsp α (T (h i)) (T v) =
      2 * (α i v * ggQ2gwForm wt h hli hsp α (T (h i)) (T (h i))) := by
  have h2 : ∀ j, α j (h j) = 2 := fun j => (hα j j).trans (hdiag j)
  have hr : Module.reflection (h2 i) ∈ ggQ2WeylOf h α :=
    Subgroup.subset_closure ⟨i, fun w => Module.reflection_apply (h := h2 i) w⟩
  have hinv := ggQ2gwForm_normalizer_weyl C wt hsym h hli hsp α hα hdiag T hT hr (h i) v
  rw [Module.reflection_apply_self (h := h2 i), Module.reflection_apply (h := h2 i),
    map_neg, map_sub, map_smul] at hinv
  rw [ggQ2gwForm_neg_left, ggQ2gwForm_sub_smul_right] at hinv
  exact zmod3_eq_two_mul_of_neg_sub hinv

private lemma ggQ2gwForm_normalizer_h_right (C : Fin n → Fin n → ZMod 3) (wt : Fin n → ZMod 3)
    (hsym : ∀ i j, wt i * C i j = wt j * C j i) (h : Fin n → U)
    (hli : LinearIndependent (ZMod 3) h) (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (hα : ∀ i j, α i (h j) = C i j) (hdiag : ∀ j, C j j = 2)
    (T : U ≃ₗ[ZMod 3] U)
    (hT : T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)))
    (i : Fin n) (v : U) :
    ggQ2gwForm wt h hli hsp α (T v) (T (h i)) =
      2 * (α i v * ggQ2gwForm wt h hli hsp α (T (h i)) (T (h i))) := by
  have h2 : ∀ j, α j (h j) = 2 := fun j => (hα j j).trans (hdiag j)
  have hr : Module.reflection (h2 i) ∈ ggQ2WeylOf h α :=
    Subgroup.subset_closure ⟨i, fun w => Module.reflection_apply (h := h2 i) w⟩
  have hinv := ggQ2gwForm_normalizer_weyl C wt hsym h hli hsp α hα hdiag T hT hr v (h i)
  rw [Module.reflection_apply_self (h := h2 i), Module.reflection_apply (h := h2 i),
    map_neg, map_sub, map_smul] at hinv
  rw [ggQ2gwForm_neg_right, ggQ2gwForm_sub_smul_left] at hinv
  exact zmod3_eq_two_mul_of_neg_sub hinv

private lemma ggQ2gwForm_normalizer_expand (wt : Fin n → ZMod 3)
    (h : Fin n → U) (hli : LinearIndependent (ZMod 3) h)
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤) (α : Fin n → Dual (ZMod 3) U)
    (T : U ≃ₗ[ZMod 3] U) (u v : U) :
    ggQ2gwForm wt h hli hsp α (T u) (T v) =
      ∑ i, ggQ2gwCoord h hli hsp u i * ggQ2gwForm wt h hli hsp α (T (h i)) (T v) := by
  have hsum : ∑ i, ggQ2gwCoord h hli hsp u i • h i = u := ggQ2gw_sum_coord h hli hsp u
  conv_lhs => rw [← hsum]
  rw [map_sum]
  simp only [map_smul]
  have hlin : ∀ f : Fin n → U,
      ggQ2gwForm wt h hli hsp α (∑ i, f i) (T v) =
        ∑ i, ggQ2gwForm wt h hli hsp α (f i) (T v) := by
    intro f
    have hgen : ∀ s : Finset (Fin n),
        ggQ2gwForm wt h hli hsp α (∑ i ∈ s, f i) (T v) =
          ∑ i ∈ s, ggQ2gwForm wt h hli hsp α (f i) (T v) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [ggQ2gwForm]
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, ggQ2gwForm_add_left, ih]
    exact hgen Finset.univ
  rw [hlin (fun i => ggQ2gwCoord h hli hsp u i • T (h i))]
  exact Finset.sum_congr rfl fun i _ => ggQ2gwForm_smul_left wt h hli hsp α _ _ _

theorem ggQ2gwForm_normalizer (C : Fin n → Fin n → ZMod 3) (wt : Fin n → ZMod 3)
    (hsym : ∀ i j, wt i * C i j = wt j * C j i)
    (hlam : ∀ lam : Fin n → ZMod 3, (∀ i j, C i j * lam i = C j i * lam j) →
      ∃ μ : ZMod 3, ∀ i, 2 * lam i = μ * wt i)
    (h : Fin n → U) (hli : LinearIndependent (ZMod 3) h)
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤) (α : Fin n → Dual (ZMod 3) U)
    (hα : ∀ i j, α i (h j) = C i j) (hdiag : ∀ j, C j j = 2) (T : U ≃ₗ[ZMod 3] U)
    (hT : T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U))) :
    ∃ μ : ZMod 3, ∀ u v : U,
      ggQ2gwForm wt h hli hsp α (T u) (T v) = μ * ggQ2gwForm wt h hli hsp α u v := by
  have hdiag_eq : ∀ i j : Fin n,
      C i j * ggQ2gwForm wt h hli hsp α (T (h i)) (T (h i)) =
        C j i * ggQ2gwForm wt h hli hsp α (T (h j)) (T (h j)) := by
    intro i j
    have h1 := ggQ2gwForm_normalizer_h_left C wt hsym h hli hsp α hα hdiag T hT i (h j)
    have h2 := ggQ2gwForm_normalizer_h_right C wt hsym h hli hsp α hα hdiag T hT j (h i)
    have hEq : (2 : ZMod 3) *
        (C i j * ggQ2gwForm wt h hli hsp α (T (h i)) (T (h i))) =
        2 * (C j i * ggQ2gwForm wt h hli hsp α (T (h j)) (T (h j))) := by
      rw [← hα i j, ← hα j i, ← h1, h2]
    exact mul_left_cancel₀ (by decide : (2 : ZMod 3) ≠ 0) hEq
  obtain ⟨μ, hμ⟩ := hlam
    (fun i => ggQ2gwForm wt h hli hsp α (T (h i)) (T (h i))) hdiag_eq
  refine ⟨μ, fun u v => ?_⟩
  have hcongr : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ggQ2gwCoord h hli hsp u i * ggQ2gwForm wt h hli hsp α (T (h i)) (T v) =
      μ * (wt i * ggQ2gwCoord h hli hsp u i * α i v) := by
    intro i _
    rw [ggQ2gwForm_normalizer_h_left C wt hsym h hli hsp α hα hdiag T hT i v]
    rw [show (2 : ZMod 3) * (α i v * ggQ2gwForm wt h hli hsp α (T (h i)) (T (h i))) =
        α i v * (2 * ggQ2gwForm wt h hli hsp α (T (h i)) (T (h i))) from by ring,
      hμ i]
    ring
  rw [ggQ2gwForm_normalizer_expand wt h hli hsp α T u v,
    Finset.sum_congr rfl hcongr, ← Finset.mul_sum, ggQ2gwForm]

end CFSG.StandardType

end
