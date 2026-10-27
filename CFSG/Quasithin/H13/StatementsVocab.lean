module

public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

abbrev FanoPoint : Type := {v : Fin 3 → ZMod 2 // v ≠ 0}

@[expose] noncomputable def fanoPointAct (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (p : FanoPoint) : FanoPoint :=
  ⟨Matrix.SpecialLinearGroup.toLin' g p.1, (LinearEquiv.map_ne_zero_iff _).2 p.2⟩

@[expose] noncomputable def fanoPermAct (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (f : Multiplicative (FanoPoint → ZMod 2)) : Multiplicative (FanoPoint → ZMod 2) :=
  Multiplicative.ofAdd fun p => Multiplicative.toAdd f (fanoPointAct g⁻¹ p)

@[expose] def fanoCore : Subgroup (Multiplicative (FanoPoint → ZMod 2)) :=
  AddSubgroup.toSubgroup
    { carrier := {f : FanoPoint → ZMod 2 | ∑ p, f p = 0}
      add_mem' := fun {f g} hf hg => by
        change ∑ p, (f + g) p = 0
        change ∑ p, f p = 0 at hf
        change ∑ p, g p = 0 at hg
        simp only [Pi.add_apply, Finset.sum_add_distrib, hf, hg, add_zero]
      zero_mem' := by
        change ∑ p, (0 : FanoPoint → ZMod 2) p = 0
        simp
      neg_mem' := fun {f} hf => by
        change ∑ p, (-f) p = 0
        change ∑ p, f p = 0 at hf
        have h : ∑ p, (-f) p = -∑ p, f p := by
          simp only [Pi.neg_apply]
          exact Finset.sum_neg_distrib (f := f)
        rw [h, hf]
        rfl }

@[expose] noncomputable def fanoCoreModel : FFModel where
  Gam := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  Amb := Multiplicative (FanoPoint → ZMod 2)
  act := fanoPermAct
  sec := fanoCore
  ker := ⊥

@[expose] def FanoCoreModule {V : Type*} [CommGroup V] (H : Subgroup (MulAut V))
    (U Z : Subgroup V) : Prop :=
  fanoCoreModel.Realizes H U Z

variable {G : Type} [Group G]

@[expose] def IsXSectionIso₂ (X J C K D : Subgroup G) : Prop :=
  ∃ (_ : (C.subgroupOf J).Normal) (_ : (D.subgroupOf K).Normal)
    (e : ↥J ⧸ C.subgroupOf J ≃* ↥K ⧸ D.subgroupOf K),
    ∀ x ∈ X, ∀ (j : ↥J) (k : ↥K) (hj : x * (j : G) * x⁻¹ ∈ J) (hk : x * (k : G) * x⁻¹ ∈ K),
      e (j : ↥J ⧸ C.subgroupOf J) = (k : ↥K ⧸ D.subgroupOf K) →
        e ((⟨x * (j : G) * x⁻¹, hj⟩ : ↥J) : ↥J ⧸ C.subgroupOf J) =
          ((⟨x * (k : G) * x⁻¹, hk⟩ : ↥K) : ↥K ⧸ D.subgroupOf K)

@[expose] def IsNaturalSumUnder (n : ℕ) (L V : Subgroup G) : Prop :=
  ∃ (k : ℕ) (W : Fin k → Subgroup G), 0 < k ∧
    (∀ i, W i ≤ V ∧ L ≤ Subgroup.normalizer (W i : Set G) ∧
      ∃ _ : IsMulCommutative ↥(W i), BinaryNaturalSL (V := ↥(W i)) (autOn L (W i)) ⊤ ⊥ n 1) ∧
    (∀ i j, IsXSectionIso₂ L (W i) ⊥ (W j) ⊥) ∧ iSupIndep W ∧ ⨆ i, W i = V

@[expose] def IsIrrPlusBase (X A I : Subgroup G) : Prop :=
  I ≤ A ∧ I ≠ ⊥ ∧ X ≤ Subgroup.normalizer (I : Set G) ∧ ⁅I, X⁆ = I ∧
    I ⊓ Subgroup.centralizer (X : Set G) < I ∧
    ∀ J : Subgroup G, I ⊓ Subgroup.centralizer (X : Set G) ≤ J → J ≤ I →
      X ≤ Subgroup.normalizer (J : Set G) →
        J = I ⊓ Subgroup.centralizer (X : Set G) ∨ J = I

end CFSG.Quasithin.H13
