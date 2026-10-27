module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTBWNormAmbInner
public import CFSG.LocalAnalysis.StandardType.GGQTwoNoF4
import CFSG.LocalAnalysis.StandardType.GGQTwoS5Dispatch
import CFSG.LocalAnalysis.StandardType.GGQTwoWeylInnerSmall
import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylA
import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylE7
import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylE8
import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112Lin
import CFSG.LocalAnalysis.StandardType.GGWAutModelNorm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGQ2Lin.not_F4Leaf {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) :
    ¬ ∃ f : Fin 4 ≃ {k // k ≠ D.a}, (∀ i j, D.cartan (f i) (f j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, D.cartan (f i) (f j) = CartanMatrix.F₄ j i) := by
  rintro ⟨f, hf⟩
  obtain ⟨i, j, hij⟩ := ggQ2_no_F4_leaf D.coxeter D.isWeyl D.a f
  apply hij
  by_cases hij' : i = j
  · subst hij'
    exact (CoxeterMatrix.diagonal D.coxeter (f i)).trans
      (CoxeterMatrix.diagonal CoxeterMatrix.F₄ i).symm
  · have hne : (f i : D.ι) ≠ (f j : D.ι) := fun hh => hij' (f.injective (Subtype.ext hh))
    have h2 := D.isCartan.2 (f i) (f j) hne
    rcases hf with hC | hC <;>
      (fin_cases i <;> fin_cases j <;>
        (rcases h2 with ⟨hm, hcond⟩ | ⟨hm, hcond⟩ | ⟨hm, hcond⟩ | ⟨hm, hcond⟩ <;>
          first
            | (rw [hm]; decide +kernel)
            | (exfalso; simp only [hC] at hcond; revert hcond; decide +kernel)))

private lemma ggQ2rl_fixed_of_root_zero {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (v : D.V)
    (hv : ∀ j : D.ι, j ≠ D.a → D.root j v = 0) : ∀ g ∈ D.parab {k | k ≠ D.a}, g v = v := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨j, hj, rfl⟩ := ht
    rw [GGQ2Lin.simpleRefl, Module.reflection_apply, hv j hj, zero_smul, sub_zero]
  | one => rfl
  | mul g₁ g₂ _ _ h₁ h₂ => rw [LinearEquiv.mul_apply, h₂, h₁]
  | inv g₁ _ h₁ =>
    nth_rewrite 1 [← h₁]
    exact g₁.symm_apply_apply v

theorem GGQ2Lin.finrank_le_card_compl_add_one {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p)
    [Module.Finite (ZMod p) D.V] (u : D.V)
    (hfix : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod p) {u}) :
    Module.finrank (ZMod p) D.V ≤ Fintype.card {k // k ≠ D.a} + 1 := by
  classical
  let Φ : D.V →ₗ[ZMod p] ({k // k ≠ D.a} → ZMod p) := LinearMap.pi fun j => D.root j.1
  have hker : LinearMap.ker Φ ≤ Submodule.span (ZMod p) {u} := by
    intro v hv
    have hv' : ∀ j : {k // k ≠ D.a}, D.root j.1 v = 0 := fun j =>
      congrFun (LinearMap.mem_ker.mp hv) j
    exact (hfix v).mp (ggQ2rl_fixed_of_root_zero D v fun j hj => hv' ⟨j, hj⟩)
  have h1 : Module.finrank (ZMod p) (LinearMap.ker Φ) ≤ 1 :=
    (Submodule.finrank_mono hker).trans ((finrank_span_le_card ({u} : Set D.V)).trans (by simp))
  have h2 : Module.finrank (ZMod p) (LinearMap.range Φ) ≤ Fintype.card {k // k ≠ D.a} :=
    (Submodule.finrank_le _).trans (Module.finrank_fintype_fun_eq_card (ZMod p)).le
  have h3 := LinearMap.finrank_range_add_finrank_ker Φ
  omega

theorem ggQ2_three_le_card_compl_of_fix {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    [Fact p.Prime] {y : G} {H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H) (u : M.V)
    (hfix : ∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {u}) :
    3 ≤ Fintype.card {k // k ≠ M.a} := by
  classical
  have hp : p.Prime := Fact.out
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod p) M.V := Module.Finite.of_finite
  have hcard : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) M.V := by
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := rfl
      _ = Nat.card M.V := Nat.card_congr M.model.toEquiv
      _ = p ^ Module.finrank (ZMod p) M.V := (FiniteField.pow_finrank_eq_natCard p M.V).symm
  have h4 : 4 ≤ Module.finrank (ZMod p) M.V := by
    have hp4 : p ^ 4 ≤ Nat.card ↥Bs := (hS.1.1.tableB_facts).2.2.2.2
    rw [hcard] at hp4
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hp4
  have : Module.Finite (ZMod p) M.toLin.V := (inferInstance : Module.Finite (ZMod p) M.V)
  have := M.toLin.finrank_le_card_compl_add_one u hfix
  change Module.finrank (ZMod p) M.V ≤ Fintype.card {k // k ≠ M.a} + 1 at this
  omega

theorem GGQ2Lin.evenDLeaf_of_not_weylInnerLeaf (D : GGQ2Lin 3)
    (h3 : 3 ≤ Fintype.card {k // k ≠ D.a}) (hin : ¬ D.WeylInnerLeaf D.a) :
    ∃ (n : ℕ) (f : Fin n ≃ {k // k ≠ D.a}), 4 ≤ n ∧ Even n ∧
      ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D n i j := by
  have hcard : ∀ {n : ℕ} (f : Fin n ≃ {k // k ≠ D.a}), Fintype.card {k // k ≠ D.a} = n :=
    fun f => (Fintype.card_congr f).symm.trans (Fintype.card_fin _)
  rcases ggQ2s4_leaf_models D with
    ⟨n, f, hn, hA | ⟨hn2, hB | hC⟩ | ⟨hn4, hD⟩⟩ | ⟨f, hE6⟩ | ⟨f, hE7⟩ | ⟨f, hE8⟩ | ⟨f, hF⟩ |
      ⟨f, hG⟩
  · exfalso
    apply hin
    by_cases h4 : 4 ≤ n
    · exact ⟨n, CartanMatrix.A n, f, hA, ggQ2WeylInner_A h4⟩
    · obtain rfl | rfl | rfl : n = 1 ∨ n = 2 ∨ n = 3 := by omega
      · exact ⟨1, CartanMatrix.A 1, f, hA, ggQ2WeylInner_A1⟩
      · exact ⟨2, CartanMatrix.A 2, f, hA, ggQ2WeylInner_A2⟩
      · exact ⟨3, CartanMatrix.A 3, f, hA, ggQ2WeylInner_A3⟩
  · exfalso
    have hn3 : 3 ≤ n := by rw [← hcard f]; exact h3
    exact hin ⟨n, CartanMatrix.B n, f, hB, ggQ2WeylInner_B hn3⟩
  · exfalso
    have hn3 : 3 ≤ n := by rw [← hcard f]; exact h3
    exact hin ⟨n, CartanMatrix.C n, f, hC, ggQ2WeylInner_C hn3⟩
  · rcases Nat.even_or_odd n with he | ho
    · exact ⟨n, f, hn4, he, hD⟩
    · exfalso
      have h5 : 5 ≤ n := by
        obtain ⟨m, hm⟩ := ho
        omega
      exact hin ⟨n, CartanMatrix.D n, f, hD, ggQ2WeylInner_D_odd h5 ho⟩
  · exact absurd ⟨6, CartanMatrix.E 6, f, hE6, ggQ2WeylInner_E6⟩ hin
  · exact absurd ⟨7, CartanMatrix.E 7, f, hE7, ggQ2WeylInner_E7⟩ hin
  · exact absurd ⟨8, CartanMatrix.E 8, f, hE8, ggQ2WeylInner_E8⟩ hin
  · exact absurd ⟨f, hF⟩ (GGQ2Lin.not_F4Leaf D)
  · exfalso
    have := hcard f
    omega

theorem ggQ2_evenDLeaf_of_not_weylInnerLeaf {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p = 3) [Fact p.Prime] {y : G} {H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H)
    (hin : ¬ M.toLin.WeylInnerLeaf M.a) (u : M.V)
    (hfix : ∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {u}) :
    ∃ (n : ℕ) (f : Fin n ≃ {k // k ≠ M.a}), 4 ≤ n ∧ Even n ∧
      ∀ i j, M.cartan (f i) (f j) = CartanMatrix.D n i j := by
  subst hp
  exact M.toLin.evenDLeaf_of_not_weylInnerLeaf (ggQ2_three_le_card_compl_of_fix hS M u hfix) hin

end CFSG.StandardType

end
