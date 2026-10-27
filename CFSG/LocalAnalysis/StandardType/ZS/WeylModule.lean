module

public import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.GGTDAutomizer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem weylMatrix_nonempty {ι : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrix M) :
    Nonempty ι := by
  rcases h with ⟨n, e, hn, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · exact ⟨e ⟨0, by omega⟩⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩

private theorem closure_reflections_eq_of_mulEquiv {ι : Type} {M : CoxeterMatrix ι}
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (f : M.Group ≃* A)
    {u : ι → U} {φ : ι → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hfeq : ∀ i, (f (M.simple i) : U ≃ₗ[ZMod p] U) = Module.reflection (hφ i)) :
    A = Subgroup.closure (Set.range fun i => Module.reflection (hφ i)) := by
  have hgen : Subgroup.closure (Set.range M.simple) = ⊤ := by
    have hg := CoxeterSystem.subgroup_closure_range_simple M.toCoxeterSystem
    rwa [CoxeterMatrix.toCoxeterSystem_simple] at hg
  let H : Subgroup (U ≃ₗ[ZMod p] U) :=
    Subgroup.closure (Set.range fun i => Module.reflection (hφ i))
  have hle : A ≤ H := by
    intro a ha
    obtain ⟨g, hg⟩ := f.surjective ⟨a, ha⟩
    have hsub : (⊤ : Subgroup M.Group) ≤ H.comap (A.subtype.comp f.toMonoidHom) := by
      rw [← hgen]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨i, rfl⟩
      exact Subgroup.mem_comap.mpr (by
        rw [MonoidHom.comp_apply]
        change (↑(f (M.simple i)) : U ≃ₗ[ZMod p] U) ∈ H
        rw [hfeq i]
        exact Subgroup.subset_closure ⟨i, rfl⟩)
    have hmem : (↑(f g) : U ≃ₗ[ZMod p] U) ∈ H :=
      Subgroup.mem_comap.mp (hsub (Subgroup.mem_top g))
    rw [hg] at hmem
    simpa using hmem
  have hge : H ≤ A := by
    refine (Subgroup.closure_le A).mpr ?_
    rintro _ ⟨i, rfl⟩
    change Module.reflection (hφ i) ∈ A
    rw [← hfeq i]
    exact (f (M.simple i)).2
  exact le_antisymm hle hge

private theorem orderOf_reflections_eq {ι : Type} {M : CoxeterMatrix ι}
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (f : M.Group ≃* A)
    {u : ι → U} {φ : ι → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hfeq : ∀ i, (f (M.simple i) : U ≃ₗ[ZMod p] U) = Module.reflection (hφ i)) :
    ∀ i j, orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) = M i j := by
  intro i j
  have hs : orderOf (M.simple i * M.simple j) = M i j := by
    have hh := CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem i j
    rwa [CoxeterMatrix.toCoxeterSystem_simple] at hh
  have hcoe : (↑(f (M.simple i)) * ↑(f (M.simple j)) : U ≃ₗ[ZMod p] U) =
      ↑(f (M.simple i * M.simple j)) := by
    rw [map_mul, Subgroup.coe_mul]
  rw [← hfeq i, ← hfeq j, hcoe, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact hs

theorem exists_rootData_of_linWeyl [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h : LinWeyl p A) :
    ∃ (ι : Type) (M : CoxeterMatrix ι), GGIsWeylMatrix M ∧
      ∃ (u : ι → U) (φ : ι → Module.Dual (ZMod p) U) (hφ : ∀ i, φ i (u i) = 2),
        (∀ i j, orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) = M i j) ∧
        Submodule.span (ZMod p) (Set.range u) = ⊤ ∧ (⨅ i, LinearMap.ker (φ i)) = ⊥ ∧
        A = Subgroup.closure (Set.range fun i => Module.reflection (hφ i)) ∧
        ∃ f : M.Group ≃* A,
          ∀ i, (f (M.simple i) : U ≃ₗ[ZMod p] U) = Module.reflection (hφ i) := by
  classical
  obtain ⟨ι, M, hM, f, hf⟩ := h
  have : Nonempty ι := weylMatrix_nonempty hM
  choose u φ hφ hfeq using fun i =>
    (isRefl_iff hp (f (M.simple i) : U ≃ₗ[ZMod p] U)).mp (hf i)
  have hA := closure_reflections_eq_of_mulEquiv f hφ hfeq
  have hord := orderOf_reflections_eq f hφ hfeq
  rw [hA] at hirr
  exact ⟨ι, M, hM, u, φ, hφ, hord, span_range_eq_top_of_invariant hp hφ hirr,
    iInf_ker_eq_bot_of_invariant hp hφ hirr, hA, f, hfeq⟩

private theorem isCartanModel_of_reindex_data {ι : Type} {n : ℕ} (e : Fin n ≃ ι)
    {M₀ : CoxeterMatrix (Fin n)} {K₀ : Matrix (Fin n) (Fin n) ℤ}
    (hp : p ≠ 2) (hK : GGIntCartan M₀ K₀)
    (hent : ∀ i j, i ≠ j → K₀ i j = 0 ∨ K₀ i j = -1 ∨ K₀ i j = -2)
    (hT : SecFiveRootRefl.CartanTree K₀)
    {u : ι → U} {φ : ι → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hord : ∀ i j, orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) =
      (M₀.reindex e) i j)
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤)
    (hker : (⨅ i, LinearMap.ker (φ i)) = ⊥)
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = Subgroup.closure (Set.range fun i => Module.reflection (hφ i))) :
    IsCartanModel p K₀ A := by
  have hK' : GGIntCartan (M₀.reindex e) (Matrix.reindex e e K₀) :=
    GGIntCartan.reindex e hK
  have hT' : SecFiveRootRefl.CartanTree (Matrix.reindex e e K₀) :=
    SecFiveRootRefl.CartanTree.reindex e hT
  have hent' := SecFiveRootRefl.entries_reindex e hent
  have hmodel := isCartanModel_of_orderOf hp hK' hent' hT' hφ hord hspan hker
  rw [← hA] at hmodel
  exact IsCartanModel.of_reindex e hmodel

private theorem exists_perm_mulEquiv_of_linWeyl {ι : Type} {M : CoxeterMatrix ι} {n : ℕ}
    (e : Fin n ≃ ι) (hM : M = (CoxeterMatrix.A n).reindex e)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (f : M.Group ≃* A)
    (hf : ∀ i, IsRefl p (f (M.simple i) : U ≃ₗ[ZMod p] U)) :
    ∃ T : Equiv.Perm (Fin (n + 1)) ≃* A,
      ∀ k : Fin n, IsRefl p (T (Equiv.swap k.castSucc k.succ) : U ≃ₗ[ZMod p] U) := by
  subst hM
  obtain ⟨eA, heA⟩ := ggCoxeterA_mulEquivPerm n
  let Ψ : ((CoxeterMatrix.A n).reindex e).Group ≃* Equiv.Perm (Fin (n + 1)) :=
    ((CoxeterMatrix.A n).reindexGroupEquiv e).trans eA
  refine ⟨Ψ.symm.trans f, ?_⟩
  intro k
  change IsRefl p (↑(f (Ψ.symm (Equiv.swap k.castSucc k.succ))) : U ≃ₗ[ZMod p] U)
  have harg : Ψ.symm (Equiv.swap k.castSucc k.succ) =
      ((CoxeterMatrix.A n).reindex e).simple (e k) := by
    change ((CoxeterMatrix.A n).reindexGroupEquiv e).symm
        (eA.symm (Equiv.swap k.castSucc k.succ)) = _
    rw [← heA k, MulEquiv.symm_apply_apply]
    exact CoxeterMatrix.reindexGroupEquiv_symm_apply_simple
      (M := CoxeterMatrix.A n) (e := e) k
  rw [harg]
  exact hf (e k)

private theorem linWeyl_case_A [Module.Finite (ZMod p) U] (hp : p ≠ 2) {ι : Type} {n : ℕ}
    (hn : 1 ≤ n) (e : Fin n ≃ ι)
    {u : ι → U} {φ : ι → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hord : ∀ i j, orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) =
      (CoxeterMatrix.A n).reindex e i j)
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤)
    (hker : (⨅ i, LinearMap.ker (φ i)) = ⊥)
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = Subgroup.closure (Set.range fun i => Module.reflection (hφ i)))
    (f : ((CoxeterMatrix.A n).reindex e).Group ≃* A)
    (hf : ∀ i, (f (((CoxeterMatrix.A n).reindex e).simple i) : U ≃ₗ[ZMod p] U) =
      Module.reflection (hφ i)) :
    IsCartanModel p (CartanMatrix.A n) A ∧
      ∃ T : Equiv.Perm (Fin (n + 1)) ≃* A,
        ∀ k : Fin n, IsRefl p (T (Equiv.swap k.castSucc k.succ) : U ≃ₗ[ZMod p] U) := by
  refine ⟨isCartanModel_of_reindex_data e hp (ggIntCartan_A n) (SecFiveRootRefl.entries_A n)
    (SecFiveRootRefl.cartanTree_A n hn) hφ hord hspan hker hA, ?_⟩
  have hfR : ∀ i, IsRefl p (f (((CoxeterMatrix.A n).reindex e).simple i) :
      U ≃ₗ[ZMod p] U) := by
    intro i
    rw [hf i]
    exact (isRefl_iff hp (Module.reflection (hφ i))).mpr ⟨u i, φ i, hφ i, rfl⟩
  exact exists_perm_mulEquiv_of_linWeyl e rfl f hfR

private theorem linWeyl_case_B (hp : p ≠ 2) {ι : Type} {n : ℕ} (hn : 2 ≤ n) (e : Fin n ≃ ι)
    {u : ι → U} {φ : ι → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hord : ∀ i j, orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) =
      (CoxeterMatrix.B n).reindex e i j)
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤)
    (hker : (⨅ i, LinearMap.ker (φ i)) = ⊥)
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = Subgroup.closure (Set.range fun i => Module.reflection (hφ i))) :
    IsCartanModel p (CartanMatrix.B n) A :=
  isCartanModel_of_reindex_data e hp (ggIntCartan_B n) (SecFiveRootRefl.entries_B n)
    (SecFiveRootRefl.cartanTree_B n (by omega)) hφ hord hspan hker hA

private theorem linWeyl_case_D (hp : p ≠ 2) {ι : Type} {n : ℕ} (hn : 4 ≤ n) (e : Fin n ≃ ι)
    {u : ι → U} {φ : ι → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hord : ∀ i j, orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) =
      (ggCoxeterMatrixD n).reindex e i j)
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤)
    (hker : (⨅ i, LinearMap.ker (φ i)) = ⊥)
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = Subgroup.closure (Set.range fun i => Module.reflection (hφ i))) :
    IsCartanModel p (CartanMatrix.D n) A :=
  isCartanModel_of_reindex_data e hp (ggIntCartan_D n) (SecFiveRootRefl.entries_D n)
    (SecFiveRootRefl.cartanTree_D n hn) hφ hord hspan hker hA

private theorem linWeyl_case_E6 (hp : p ≠ 2) {ι : Type} (e : Fin 6 ≃ ι)
    {u : ι → U} {φ : ι → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hord : ∀ i j, orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) =
      CoxeterMatrix.E₆.reindex e i j)
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤)
    (hker : (⨅ i, LinearMap.ker (φ i)) = ⊥)
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = Subgroup.closure (Set.range fun i => Module.reflection (hφ i))) :
    IsCartanModel p (CartanMatrix.E 6) A :=
  isCartanModel_of_reindex_data e hp ggIntCartan_E₆ (SecFiveRootRefl.entries_E 6)
    (SecFiveRootRefl.cartanTree_E 6 (by norm_num)) hφ hord hspan hker hA

private theorem linWeyl_case_E7 (hp : p ≠ 2) {ι : Type} (e : Fin 7 ≃ ι)
    {u : ι → U} {φ : ι → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hord : ∀ i j, orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) =
      CoxeterMatrix.E₇.reindex e i j)
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤)
    (hker : (⨅ i, LinearMap.ker (φ i)) = ⊥)
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = Subgroup.closure (Set.range fun i => Module.reflection (hφ i))) :
    IsCartanModel p (CartanMatrix.E 7) A :=
  isCartanModel_of_reindex_data e hp ggIntCartan_E₇ (SecFiveRootRefl.entries_E 7)
    (SecFiveRootRefl.cartanTree_E 7 (by norm_num)) hφ hord hspan hker hA

private theorem linWeyl_case_E8 (hp : p ≠ 2) {ι : Type} (e : Fin 8 ≃ ι)
    {u : ι → U} {φ : ι → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hord : ∀ i j, orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) =
      CoxeterMatrix.E₈.reindex e i j)
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤)
    (hker : (⨅ i, LinearMap.ker (φ i)) = ⊥)
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = Subgroup.closure (Set.range fun i => Module.reflection (hφ i))) :
    IsCartanModel p (CartanMatrix.E 8) A :=
  isCartanModel_of_reindex_data e hp ggIntCartan_E₈ (SecFiveRootRefl.entries_E 8)
    (SecFiveRootRefl.cartanTree_E 8 (by norm_num)) hφ hord hspan hker hA

private theorem linWeyl_case_F4 (hp : p ≠ 2) {ι : Type} (e : Fin 4 ≃ ι)
    {u : ι → U} {φ : ι → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hord : ∀ i j, orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) =
      CoxeterMatrix.F₄.reindex e i j)
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤)
    (hker : (⨅ i, LinearMap.ker (φ i)) = ⊥)
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = Subgroup.closure (Set.range fun i => Module.reflection (hφ i))) :
    IsCartanModel p CartanMatrix.F₄ A :=
  isCartanModel_of_reindex_data e hp ggIntCartan_F₄ SecFiveRootRefl.entries_F₄
    SecFiveRootRefl.cartanTree_F₄ hφ hord hspan hker hA

private theorem linWeyl_case_G2 {ι : Type} (e : Fin 2 ≃ ι) {u : ι → U}
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤)
    (h3 : 3 ≤ Module.finrank (ZMod p) U) : False := by
  have : Fintype ι := Fintype.ofEquiv (Fin 2) e
  have hle : Module.finrank (ZMod p) U ≤ 2 := by
    have h1 : Module.finrank (ZMod p) U = (Set.range u).finrank (ZMod p) := by
      change Module.finrank (ZMod p) U =
        Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range u))
      rw [hspan, finrank_top]
    rw [h1]
    calc (Set.range u).finrank (ZMod p) ≤ Fintype.card ι := finrank_range_le_card u
      _ = 2 := by rw [← Fintype.card_congr e, Fintype.card_fin]
  omega

private theorem linWeyl_cases [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {ι : Type} {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) {u : ι → U} {φ : ι → Module.Dual (ZMod p) U}
    (hφ : ∀ i, φ i (u i) = 2)
    (hord : ∀ i j, orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) = M i j)
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤)
    (hker : (⨅ i, LinearMap.ker (φ i)) = ⊥)
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = Subgroup.closure (Set.range fun i => Module.reflection (hφ i)))
    (f : M.Group ≃* A)
    (hf : ∀ i, (f (M.simple i) : U ≃ₗ[ZMod p] U) = Module.reflection (hφ i)) :
    (∃ ℓ : ℕ, IsCartanModel p (CartanMatrix.A ℓ) A ∧ ∃ T : Equiv.Perm (Fin (ℓ + 1)) ≃* A,
        ∀ k : Fin ℓ, IsRefl p (T (Equiv.swap k.castSucc k.succ) : U ≃ₗ[ZMod p] U)) ∨
      (∃ ℓ : ℕ, 2 ≤ ℓ ∧ IsCartanModel p (CartanMatrix.B ℓ) A) ∨
      (∃ ℓ : ℕ, 4 ≤ ℓ ∧ IsCartanModel p (CartanMatrix.D ℓ) A) ∨
      (IsCartanModel p (CartanMatrix.E 6) A ∧ Nonempty (CoxeterMatrix.E₆.Group ≃* A)) ∨
      (IsCartanModel p (CartanMatrix.E 7) A ∧ Nonempty (CoxeterMatrix.E₇.Group ≃* A)) ∨
      (IsCartanModel p (CartanMatrix.E 8) A ∧ Nonempty (CoxeterMatrix.E₈.Group ≃* A)) ∨
      (IsCartanModel p CartanMatrix.F₄ A ∧ Nonempty (CoxeterMatrix.F₄.Group ≃* A)) := by
  rcases hM with ⟨n, e, hn, hAeq | ⟨hn2, hBeq⟩ | ⟨hn4, hDeq⟩⟩ | ⟨e, hE6⟩ |
    ⟨e, hE7⟩ | ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2⟩
  · subst hAeq
    exact Or.inl ⟨n, linWeyl_case_A hp hn e hφ hord hspan hker hA f hf⟩
  · subst hBeq
    exact Or.inr (Or.inl ⟨n, hn2, linWeyl_case_B hp hn2 e hφ hord hspan hker hA⟩)
  · subst hDeq
    exact Or.inr (Or.inr (Or.inl ⟨n, hn4, linWeyl_case_D hp hn4 e hφ hord hspan hker hA⟩))
  · subst hE6
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨linWeyl_case_E6 hp e hφ hord hspan hker hA,
      ⟨(CoxeterMatrix.E₆.reindexGroupEquiv e).symm.trans f⟩⟩)))
  · subst hE7
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨linWeyl_case_E7 hp e hφ hord hspan hker hA,
        ⟨(CoxeterMatrix.E₇.reindexGroupEquiv e).symm.trans f⟩⟩))))
  · subst hE8
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨linWeyl_case_E8 hp e hφ hord hspan hker hA,
        ⟨(CoxeterMatrix.E₈.reindexGroupEquiv e).symm.trans f⟩⟩)))))
  · subst hF4
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨linWeyl_case_F4 hp e hφ hord hspan hker hA,
        ⟨(CoxeterMatrix.F₄.reindexGroupEquiv e).symm.trans f⟩⟩)))))
  · subst hG2
    exact (linWeyl_case_G2 e hspan h3).elim

theorem isCartanModel_cases_typed_of_linWeyl [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h : LinWeyl p A) :
    (∃ ℓ : ℕ, IsCartanModel p (CartanMatrix.A ℓ) A ∧ ∃ T : Equiv.Perm (Fin (ℓ + 1)) ≃* A,
        ∀ k : Fin ℓ, IsRefl p (T (Equiv.swap k.castSucc k.succ) : U ≃ₗ[ZMod p] U)) ∨
      (∃ ℓ : ℕ, 2 ≤ ℓ ∧ IsCartanModel p (CartanMatrix.B ℓ) A) ∨
      (∃ ℓ : ℕ, 4 ≤ ℓ ∧ IsCartanModel p (CartanMatrix.D ℓ) A) ∨
      (IsCartanModel p (CartanMatrix.E 6) A ∧ Nonempty (CoxeterMatrix.E₆.Group ≃* A)) ∨
      (IsCartanModel p (CartanMatrix.E 7) A ∧ Nonempty (CoxeterMatrix.E₇.Group ≃* A)) ∨
      (IsCartanModel p (CartanMatrix.E 8) A ∧ Nonempty (CoxeterMatrix.E₈.Group ≃* A)) ∨
      (IsCartanModel p CartanMatrix.F₄ A ∧ Nonempty (CoxeterMatrix.F₄.Group ≃* A)) := by
  obtain ⟨ι, M, hM, u, φ, hφ, hord, hspan, hker, hA, f, hf⟩ :=
    exists_rootData_of_linWeyl hp hirr h
  exact linWeyl_cases hp h3 hM hφ hord hspan hker hA f hf

theorem isCartanModel_cases_of_linWeyl [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h : LinWeyl p A) :
    (∃ ℓ : ℕ, IsCartanModel p (CartanMatrix.A ℓ) A ∧ ∃ T : Equiv.Perm (Fin (ℓ + 1)) ≃* A,
        ∀ k : Fin ℓ, IsRefl p (T (Equiv.swap k.castSucc k.succ) : U ≃ₗ[ZMod p] U)) ∨
      (∃ ℓ : ℕ, 2 ≤ ℓ ∧ IsCartanModel p (CartanMatrix.B ℓ) A) ∨
      (∃ ℓ : ℕ, 4 ≤ ℓ ∧ IsCartanModel p (CartanMatrix.D ℓ) A) ∨
      IsCartanModel p (CartanMatrix.E 6) A ∨ IsCartanModel p (CartanMatrix.E 7) A ∨
      IsCartanModel p (CartanMatrix.E 8) A ∨ IsCartanModel p CartanMatrix.F₄ A := by
  rcases isCartanModel_cases_typed_of_linWeyl hp h3 hirr h with
      hA | hB | hD | ⟨hE6, -⟩ | ⟨hE7, -⟩ | ⟨hE8, -⟩ | ⟨hF4, -⟩
  · exact Or.inl hA
  · exact Or.inr (Or.inl hB)
  · exact Or.inr (Or.inr (Or.inl hD))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hE6)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE7))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE8)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hF4)))))

end CFSG.StandardType.ZS

end
