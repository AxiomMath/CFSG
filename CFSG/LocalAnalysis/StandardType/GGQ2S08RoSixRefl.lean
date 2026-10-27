module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}

noncomputable abbrev ggQ2s08r6S (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) : M.V ≃ₗ[ZMod 3] M.V :=
  ggLin (p := 3) M.model (M.simple i)

private theorem ggQ2s08r6_mem_automizer (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    M.simple i ∈ ggAutomizer L Bs := by
  rw [M.automizer_L]
  exact Subgroup.subset_closure (Set.mem_range_self i)

private theorem ggQ2s08r6S_apply (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) (v : M.V) :
    ggQ2s08r6S M i v = v - M.root i v • M.coroot i :=
  M.simple_apply i v

private theorem ggQ2s08r6_coroot_ne_zero (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    M.coroot i ≠ 0 := by
  intro h
  have h2 : M.root i (M.coroot i) = 0 := by rw [h, map_zero]
  rw [M.pairing, M.isCartan.1 i] at h2
  have h3 : ((2 : ℤ) : ZMod 3) = (2 : ZMod 3) := by norm_num
  rw [h3] at h2
  exact (by decide : (2 : ZMod 3) ≠ 0) h2

private theorem ggQ2s08r6S_fixed_xV (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    ggQ2s08r6S M i M.xV = M.xV := by
  have hx : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [M.fixed_x]
    exact Submodule.mem_span_singleton_self M.xV
  exact (mem_ggFixedSubmodule_iff.mp hx) (M.simple i) (ggQ2s08r6_mem_automizer M i)

theorem ggQ2s08r6_root_xV (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) : M.root i M.xV = 0 := by
  have h : ggQ2s08r6S M i M.xV = M.xV - M.root i M.xV • M.coroot i :=
    ggQ2s08r6S_apply M i M.xV
  rw [ggQ2s08r6S_fixed_xV M i] at h
  have hz : M.root i M.xV • M.coroot i = 0 := sub_eq_self.mp h.symm
  exact (smul_eq_zero.mp hz).resolve_right (ggQ2s08r6_coroot_ne_zero M i)

theorem ggQ2s08r6_coroot_not_mem (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    M.coroot i ∉ Submodule.span (ZMod 3) {M.xV} := by
  intro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h2 : M.root i (M.coroot i) = 0 := by
    rw [← hc, map_smul, ggQ2s08r6_root_xV M i, smul_zero]
  rw [M.pairing, M.isCartan.1 i] at h2
  have h3 : ((2 : ℤ) : ZMod 3) = (2 : ZMod 3) := by norm_num
  rw [h3] at h2
  exact (by decide : (2 : ZMod 3) ≠ 0) h2

private theorem ggQ2s08r6_coxeter_apply (M : GGQ2LDatum 3 Bs L x) {e : Fin 5 ≃ M.Λ}
    (he : M.coxeter = (CoxeterMatrix.A 5).reindex e) (i j : Fin 5) :
    M.coxeter (e i) (e j) = (CoxeterMatrix.A 5) i j := by
  have hM : M.coxeter.M (e i) (e j) = (CoxeterMatrix.A 5).M i j := by
    rw [he, CoxeterMatrix.reindex_apply]
    simp
  exact hM

private theorem ggQ2s08r6_A_adj (k l : Fin 5) (h : (k : ℕ) + 1 = l ∨ (l : ℕ) + 1 = k) :
    (CoxeterMatrix.A 5) k l = 3 := by
  have hkl : k ≠ l := by rcases h with h | h <;> omega
  rw [show (CoxeterMatrix.A 5) k l =
    (if k = l then (1 : ℕ) else if (l : ℕ) + 1 = k ∨ (k : ℕ) + 1 = l then 3 else 2) from rfl]
  rcases h with h | h
  · rw [if_neg hkl, if_pos (Or.inr h)]
  · rw [if_neg hkl, if_pos (Or.inl h)]

private theorem ggQ2s08r6_A_nonadj (k l : Fin 5) (hkl : k ≠ l) (h1 : (k : ℕ) + 1 ≠ l)
    (h2 : (l : ℕ) + 1 ≠ k) : (CoxeterMatrix.A 5) k l = 2 := by
  rw [show (CoxeterMatrix.A 5) k l =
    (if k = l then (1 : ℕ) else if (l : ℕ) + 1 = k ∨ (k : ℕ) + 1 = l then 3 else 2) from rfl]
  rw [if_neg hkl, if_neg (fun h => h.elim h2 h1)]

private theorem ggQ2s08r6_cartan_eq_zero_of_cox_two (M : GGQ2LDatum 3 Bs L x)
    {i j : M.Λ} (hij : i ≠ j) (h : M.coxeter i j = 2) :
    M.cartan i j = 0 ∧ M.cartan j i = 0 := by
  rcases M.isCartan.2 i j hij with ⟨-, h1, h2⟩ | ⟨h3, -, -⟩ | ⟨h3, -, -⟩ | ⟨h3, -, -⟩
  · exact ⟨h1, h2⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

private theorem ggQ2s08r6_cartan_eq_neg_one_of_cox_three (M : GGQ2LDatum 3 Bs L x)
    {i j : M.Λ} (hij : i ≠ j) (h : M.coxeter i j = 3) :
    M.cartan i j = -1 ∧ M.cartan j i = -1 := by
  rcases M.isCartan.2 i j hij with ⟨h2, -, -⟩ | ⟨-, h1, h2⟩ | ⟨h2, -, -⟩ | ⟨h2, -, -⟩
  · exfalso; omega
  · exact ⟨h1, h2⟩
  · exfalso; omega
  · exfalso; omega

private theorem ggQ2s08r6S_apply_apply (M : GGQ2LDatum 3 Bs L x) (i j : M.Λ) (v : M.V) :
    ggQ2s08r6S M i (ggQ2s08r6S M j v) =
      v - (M.root j v • M.coroot j +
        (M.root i v - M.root j v * (M.cartan i j : ZMod 3)) • M.coroot i) := by
  rw [ggQ2s08r6S_apply M j v, ggQ2s08r6S_apply M i (v - M.root j v • M.coroot j)]
  rw [map_sub, map_smul, M.pairing, smul_eq_mul]
  abel

private theorem ggQ2s08r6S_involutive (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) (v : M.V) :
    ggQ2s08r6S M i (ggQ2s08r6S M i v) = v := by
  have hfx : M.root i (M.coroot i) = 2 := by
    rw [M.pairing, M.isCartan.1 i]
    norm_num
  have h : ggQ2s08r6S M i = Module.reflection hfx :=
    ggLin_eq_reflection (p := 3) M.model hfx (fun w => M.simple_apply i w)
  rw [h]
  exact Module.involutive_reflection hfx v

private theorem ggQ2s08r6S_ne_one (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    ggQ2s08r6S M i ≠ 1 := by
  intro h
  have hh : M.root i (M.coroot i) • M.coroot i = 0 := by
    have h1 : ggQ2s08r6S M i (M.coroot i) =
        M.coroot i - M.root i (M.coroot i) • M.coroot i :=
      ggQ2s08r6S_apply M i (M.coroot i)
    rw [h] at h1
    have h2 : M.coroot i - M.root i (M.coroot i) • M.coroot i = M.coroot i := by
      simpa using h1.symm
    exact sub_eq_self.mp h2
  rw [M.pairing, M.isCartan.1 i] at hh
  have h3 : ((2 : ℤ) : ZMod 3) = (2 : ZMod 3) := by norm_num
  rw [h3] at hh
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  exact ggQ2s08r6_coroot_ne_zero M i ((smul_eq_zero.mp hh).resolve_left h2)

private theorem ggQ2s08r6_exists_root_vals (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeA)
    (c : M.Λ → ZMod 3) : ∃ v : M.V, ∀ i, M.root i v = c i := by
  obtain ⟨v, hv⟩ := hShape.2.2.2.2 c
  exact ⟨v, fun i => by
    have h := congrArg (fun z : M.Λ → ZMod 3 => z i) hv
    simpa only [GGQ2LDatum.rootMap, LinearMap.pi_apply] using h⟩

theorem ggQ2s08r6_S_ne_mod (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeA) {e : Fin 5 ≃ M.Λ}
    (he : M.coxeter = (CoxeterMatrix.A 5).reindex e) {k l : Fin 5} (hkl : k ≠ l) :
    ∃ v : M.V, ggQ2s08r6S M (e k) v - ggQ2s08r6S M (e l) v ∉ Submodule.span (ZMod 3) {M.xV} := by
  obtain ⟨v, hv⟩ := ggQ2s08r6_exists_root_vals M hShape
    (fun m => if m = e k then (1 : ZMod 3) else 0)
  have hk : M.root (e k) v = 1 := by simpa using hv (e k)
  have hl : M.root (e l) v = 0 := by
    have h := hv (e l)
    rw [if_neg (fun hlk : e l = e k => hkl (e.injective hlk.symm))] at h
    exact h
  refine ⟨v, ?_⟩
  have hdiff : ggQ2s08r6S M (e k) v - ggQ2s08r6S M (e l) v = -M.coroot (e k) := by
    rw [ggQ2s08r6S_apply M (e k) v, ggQ2s08r6S_apply M (e l) v, hk, hl]
    simp
  rw [hdiff]
  intro hmem
  exact ggQ2s08r6_coroot_not_mem M (e k) ((Submodule.neg_mem_iff _).mp hmem)

theorem ggQ2s08r6_S_noncomm_mod (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeA)
    {e : Fin 5 ≃ M.Λ} (he : M.coxeter = (CoxeterMatrix.A 5).reindex e) {k l : Fin 5}
    (hkl : (k : ℕ) + 1 = l) :
    ∃ v : M.V, ggQ2s08r6S M (e k) (ggQ2s08r6S M (e l) v) -
      ggQ2s08r6S M (e l) (ggQ2s08r6S M (e k) v) ∉ Submodule.span (ZMod 3) {M.xV} := by
  have hklne : k ≠ l := by omega
  have hne : e k ≠ e l := fun h => hklne (e.injective h)
  obtain ⟨v, hv⟩ := ggQ2s08r6_exists_root_vals M hShape
    (fun m => if m = e k then (1 : ZMod 3) else 0)
  have hk : M.root (e k) v = 1 := by simpa using hv (e k)
  have hl : M.root (e l) v = 0 := by
    have h := hv (e l)
    rw [if_neg (fun hlk : e l = e k => hklne (e.injective hlk.symm))] at h
    exact h
  have hcx : M.coxeter (e k) (e l) = 3 := by
    rw [ggQ2s08r6_coxeter_apply M he k l, ggQ2s08r6_A_adj k l (Or.inl hkl)]
  have hcx2 : M.coxeter (e l) (e k) = 3 := by
    rw [ggQ2s08r6_coxeter_apply M he l k, ggQ2s08r6_A_adj l k (Or.inr hkl)]
  obtain ⟨hC, hC2⟩ := ggQ2s08r6_cartan_eq_neg_one_of_cox_three M hne hcx
  obtain ⟨hC', hC2'⟩ := ggQ2s08r6_cartan_eq_neg_one_of_cox_three M (Ne.symm hne) hcx2
  have hsc : M.root (e k) v - M.root (e l) v * (M.cartan (e k) (e l) : ZMod 3) = 1 := by
    rw [hk, hl, hC]
    norm_num
  have hsc2 : M.root (e l) v - M.root (e k) v * (M.cartan (e l) (e k) : ZMod 3) = 1 := by
    rw [hk, hl, hC']
    decide
  refine ⟨v, ?_⟩
  have hdiff : ggQ2s08r6S M (e k) (ggQ2s08r6S M (e l) v) -
      ggQ2s08r6S M (e l) (ggQ2s08r6S M (e k) v) = M.coroot (e l) := by
    rw [ggQ2s08r6S_apply_apply M (e k) (e l) v, ggQ2s08r6S_apply_apply M (e l) (e k) v,
      hsc, hsc2, hk, hl]
    simp
  rw [hdiff]
  exact ggQ2s08r6_coroot_not_mem M (e l)

theorem ggQ2s08r6_S_comm (M : GGQ2LDatum 3 Bs L x) {e : Fin 5 ≃ M.Λ}
    (he : M.coxeter = (CoxeterMatrix.A 5).reindex e) {k l : Fin 5} (hkl : k ≠ l)
    (h1 : (k : ℕ) + 1 ≠ l) (h2 : (l : ℕ) + 1 ≠ k) (v : M.V) :
    ggQ2s08r6S M (e k) (ggQ2s08r6S M (e l) v) =
      ggQ2s08r6S M (e l) (ggQ2s08r6S M (e k) v) := by
  have hne : e k ≠ e l := fun h => hkl (e.injective h)
  have hcx : M.coxeter (e k) (e l) = 2 := by
    rw [ggQ2s08r6_coxeter_apply M he k l, ggQ2s08r6_A_nonadj k l hkl h1 h2]
  have hcx2 : M.coxeter (e l) (e k) = 2 := by
    rw [ggQ2s08r6_coxeter_apply M he l k, ggQ2s08r6_A_nonadj l k (Ne.symm hkl) h2 h1]
  obtain ⟨hC, hC2⟩ := ggQ2s08r6_cartan_eq_zero_of_cox_two M hne hcx
  obtain ⟨hC', hC2'⟩ := ggQ2s08r6_cartan_eq_zero_of_cox_two M (Ne.symm hne) hcx2
  have hsc : M.root (e k) v - M.root (e l) v * (M.cartan (e k) (e l) : ZMod 3) =
      M.root (e k) v := by
    rw [hC]
    simp
  have hsc2 : M.root (e l) v - M.root (e k) v * (M.cartan (e l) (e k) : ZMod 3) =
      M.root (e l) v := by
    rw [hC']
    simp
  rw [ggQ2s08r6S_apply_apply M (e k) (e l) v, ggQ2s08r6S_apply_apply M (e l) (e k) v,
    hsc, hsc2]
  abel

theorem ggQ2s08r6_S_ne_one_mod (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeA) (i : M.Λ) :
    ∃ v : M.V, ggQ2s08r6S M i v - v ∉ Submodule.span (ZMod 3) {M.xV} := by
  obtain ⟨v, hv⟩ := ggQ2s08r6_exists_root_vals M hShape
    (fun m => if m = i then (1 : ZMod 3) else 0)
  have hi : M.root i v = 1 := by simpa using hv i
  refine ⟨v, ?_⟩
  have hdiff : ggQ2s08r6S M i v - v = -M.coroot i := by
    rw [ggQ2s08r6S_apply M i v, hi]
    simp
  rw [hdiff]
  intro hmem
  exact ggQ2s08r6_coroot_not_mem M i ((Submodule.neg_mem_iff _).mp hmem)

private theorem ggQ2s08r6_repr_coord {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin 6) (ZMod 3) V) {i si : Fin 6} (hsi : si ≠ i) {γ : ZMod 3}
    {h : V} (heq : b si = b i - γ • h) :
    (∀ j, j ≠ i → j ≠ si → b.repr h j = 0) ∧ b.repr h i ≠ 0 := by
  have hγ : γ ≠ 0 := by
    intro h0
    rw [h0] at heq
    have h1 : b si = b i := by rw [heq]; simp
    exact hsi (b.linearIndependent.injective h1)
  have hr : Finsupp.single si (1 : ZMod 3) = Finsupp.single i 1 - γ • b.repr h := by
    have h1 := congrArg b.repr heq
    simpa only [map_sub, map_smul, Module.Basis.repr_self] using h1
  have hval : ∀ m : Fin 6, (Finsupp.single si (1 : ZMod 3)) m =
      (Finsupp.single i 1) m - γ * b.repr h m := by
    intro m
    calc (Finsupp.single si (1 : ZMod 3)) m
        = ((Finsupp.single i (1 : ZMod 3)) - γ • b.repr h) m := congrArg (fun z => z m) hr
      _ = (Finsupp.single i (1 : ZMod 3)) m - (γ • b.repr h) m := Finsupp.sub_apply _ _ m
      _ = (Finsupp.single i (1 : ZMod 3)) m - γ * b.repr h m := by
          rw [Finsupp.smul_apply, smul_eq_mul]
  constructor
  · intro j hj hjs
    have h2 := hval j
    rw [Finsupp.single_eq_of_ne hjs, Finsupp.single_eq_of_ne hj] at h2
    have h3 : γ * b.repr h j = 0 := neg_eq_zero.mp h2.symm
    exact (mul_eq_zero.mp h3).resolve_left hγ
  · intro hc
    have h2 := hval i
    rw [Finsupp.single_eq_of_ne (Ne.symm hsi), Finsupp.single_eq_same] at h2
    have h4 : γ * b.repr h i = 1 := by
      have h5 : (0 : ZMod 3) = 1 - γ * b.repr h i := h2
      rw [eq_sub_iff_add_eq] at h5
      simpa using h5
    rw [hc, mul_zero] at h4
    exact zero_ne_one h4

private theorem ggQ2s08r6_eq_of_frame (M : GGQ2LDatum 3 Bs L x) (f : Fin 6 → M.V)
    (hf : GGQ2S08ROFrame M f) {T U : M.V ≃ₗ[ZMod 3] M.V}
    (h : ∀ i, T (f i) = U (f i)) : T = U := by
  have hlin : (T : M.V →ₗ[ZMod 3] M.V) = (U : M.V →ₗ[ZMod 3] M.V) :=
    LinearMap.ext_on_range hf.2.1 h
  exact LinearEquiv.ext (fun v => congrArg (fun (g : M.V →ₗ[ZMod 3] M.V) => g v) hlin)

theorem ggQ2s08r6_fswap (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeA) {e : Fin 5 ≃ M.Λ}
    (he : M.coxeter = (CoxeterMatrix.A 5).reindex e) (f : Fin 6 → M.V)
    (hf : GGQ2S08ROFrame M f) :
    ∃ σ : Fin 5 → Equiv.Perm (Fin 6),
      (∀ k i, ggQ2s08r6S M (e k) (f i) = f (σ k i)) ∧ (∀ k, (σ k).IsSwap) ∧
      (∀ k l : Fin 5, (k : ℕ) + 1 = l → σ k * σ l ≠ σ l * σ k) ∧
      (∀ k l : Fin 5, k ≠ l → (k : ℕ) + 1 ≠ l → (l : ℕ) + 1 ≠ k →
        σ k * σ l = σ l * σ k ∧ σ k ≠ σ l) := by
  classical
  have hex : ∀ k : Fin 5, ∃ τ : Equiv.Perm (Fin 6), ∀ i, ggQ2s08r6S M (e k) (f i) = f (τ i) :=
    fun k => hf.2.2.2 (M.simple (e k)) (ggQ2s08r6_mem_automizer M (e k))
  choose σ hσ using hex
  have hinv : ∀ k i, σ k (σ k i) = i := by
    intro k i
    refine hf.1.injective ?_
    rw [← hσ k (σ k i), ← hσ k i, ggQ2s08r6S_involutive]
  have hne_one : ∀ k, σ k ≠ 1 := by
    intro k h1
    apply ggQ2s08r6S_ne_one M (e k)
    have hfix : ∀ i, ggQ2s08r6S M (e k) (f i) = f i := by
      intro i
      rw [hσ k i, h1]
      rfl
    exact ggQ2s08r6_eq_of_frame M f hf hfix
  have hswap : ∀ k, (σ k).IsSwap := by
    intro k
    have hmoved : ∃ i : Fin 6, σ k i ≠ i := by
      by_contra h
      have h' : ∀ i, σ k i = i := by
        intro i
        by_contra hi
        exact h ⟨i, hi⟩
      exact hne_one k (Equiv.ext h')
    obtain ⟨i, hi⟩ := hmoved
    let b : Module.Basis (Fin 6) (ZMod 3) M.V := Module.Basis.mk hf.1 (le_of_eq hf.2.1.symm)
    have hb : ∀ m, b m = f m := fun m => Module.Basis.mk_apply hf.1 (le_of_eq hf.2.1.symm) m
    have hcoord : ∀ (j : Fin 6) (hj : σ k j ≠ j),
        (∀ m, m ≠ j → m ≠ σ k j → b.repr (M.coroot (e k)) m = 0) ∧
        b.repr (M.coroot (e k)) j ≠ 0 := by
      intro j hj
      refine ggQ2s08r6_repr_coord (γ := M.root (e k) (f j)) (h := M.coroot (e k)) b hj ?_
      have h1 : f (σ k j) = f j - M.root (e k) (f j) • M.coroot (e k) := by
        rw [← hσ k j]
        exact ggQ2s08r6S_apply M (e k) (f j)
      simpa only [hb] using h1
    have hmem : ∀ j, σ k j ≠ j → j = i ∨ j = σ k i := by
      intro j hj
      by_contra hcon
      rw [not_or] at hcon
      exact (hcoord j hj).2 ((hcoord i hi).1 j hcon.1 hcon.2)
    have heq : σ k = Equiv.swap i (σ k i) := by
      refine Equiv.ext fun j => ?_
      by_cases hji : j = i
      · subst hji
        rw [Equiv.swap_apply_left]
      · by_cases hjs : j = σ k i
        · subst hjs
          rw [Equiv.swap_apply_right, hinv k i]
        · have hfixj : σ k j = j := by
            by_contra hj
            exact (hmem j hj).elim hji hjs
          rw [hfixj, Equiv.swap_apply_of_ne_of_ne hji hjs]
    exact ⟨i, σ k i, Ne.symm hi, heq⟩
  have hcomm : ∀ k l : Fin 5, k ≠ l → (k : ℕ) + 1 ≠ l → (l : ℕ) + 1 ≠ k →
      σ k * σ l = σ l * σ k := by
    intro k l hkl h1 h2
    refine Equiv.ext fun i => hf.1.injective ?_
    have h1' : f ((σ k * σ l) i) = ggQ2s08r6S M (e k) (ggQ2s08r6S M (e l) (f i)) := by
      rw [Equiv.Perm.mul_apply, ← hσ k (σ l i), ← hσ l i]
    have h2' : f ((σ l * σ k) i) = ggQ2s08r6S M (e l) (ggQ2s08r6S M (e k) (f i)) := by
      rw [Equiv.Perm.mul_apply, ← hσ l (σ k i), ← hσ k i]
    rw [h1', h2', ggQ2s08r6_S_comm M he hkl h1 h2]
  have hnoncomm : ∀ k l : Fin 5, (k : ℕ) + 1 = l → σ k * σ l ≠ σ l * σ k := by
    intro k l hkl hcomm'
    obtain ⟨v, hv⟩ := ggQ2s08r6_S_noncomm_mod M hShape he hkl
    refine hv ?_
    have hbasis : ∀ i, ggQ2s08r6S M (e k) (ggQ2s08r6S M (e l) (f i)) =
        ggQ2s08r6S M (e l) (ggQ2s08r6S M (e k) (f i)) := by
      intro i
      rw [hσ l i, hσ k (σ l i), hσ k i, hσ l (σ k i)]
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, hcomm']
    have hT : ggQ2s08r6S M (e k) * ggQ2s08r6S M (e l) =
        ggQ2s08r6S M (e l) * ggQ2s08r6S M (e k) :=
      ggQ2s08r6_eq_of_frame M f hf (fun i => by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        exact hbasis i)
    have hpoint : ggQ2s08r6S M (e k) (ggQ2s08r6S M (e l) v) =
        ggQ2s08r6S M (e l) (ggQ2s08r6S M (e k) v) := by
      have := congrArg (fun (g : M.V ≃ₗ[ZMod 3] M.V) => g v) hT
      simpa only [LinearEquiv.mul_apply] using this
    rw [hpoint, sub_self]
    exact Submodule.zero_mem _
  have hdistinct : ∀ k l : Fin 5, k ≠ l → (k : ℕ) + 1 ≠ l → (l : ℕ) + 1 ≠ k →
      σ k ≠ σ l := by
    intro k l hkl h1 h2 hper
    obtain ⟨v, hv⟩ := ggQ2s08r6_S_ne_mod M hShape he hkl
    refine hv ?_
    have hT : ggQ2s08r6S M (e k) = ggQ2s08r6S M (e l) :=
      ggQ2s08r6_eq_of_frame M f hf (fun i => by rw [hσ k i, hσ l i, hper])
    rw [hT, sub_self]
    exact Submodule.zero_mem _
  exact ⟨σ, hσ, hswap, hnoncomm, fun k l hkl h1 h2 =>
    ⟨hcomm k l hkl h1 h2, hdistinct k l hkl h1 h2⟩⟩

end CFSG.StandardType

end
