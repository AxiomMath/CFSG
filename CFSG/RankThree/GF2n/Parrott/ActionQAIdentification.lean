module

public import CFSG.RankThree.GF2n.Parrott.ActionQA
public import CFSG.RankThree.GF2n.Parrott.SpinActionA

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G}

local notation "A45" => QA45.originalSubgroup
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def x45A : A45 := ⟨x45, Q45_le_A45 x45_mem_Q⟩

@[expose] def y45A : A45 := ⟨y45, Q45_le_A45 y45_mem_Q⟩

@[expose] def f45A : A45 := ⟨f45, f45_mem_A⟩

@[expose] noncomputable def toQAct : A45 ≃* QAct := QAEquiv.symm

theorem rhoA_apply (a : A45) : rhoA a = rhoAct (toQAct a) := rfl

theorem image_generators_QA45 :
    ((QA45.originalSubgroup).subtype '' ({x45A, y45A, f45A} : Set A45)) =
      ({x45, y45, f45} : Set P45) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl <;> simp [x45A, y45A, f45A]
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨x45A, by simp, rfl⟩
    · exact ⟨y45A, by simp, rfl⟩
    · exact ⟨f45A, by simp, rfl⟩

theorem closure_generators_QA45 :
    Subgroup.closure ({x45A, y45A, f45A} : Set A45) = ⊤ := by
  apply Subgroup.map_injective (f := (QA45.originalSubgroup).subtype) (QA45.originalSubgroup).subtype_injective
  rw [MonoidHom.map_closure, image_generators_QA45]
  have htop : (⊤ : Subgroup A45).map (QA45.originalSubgroup).subtype = A45 := by
    ext x
    constructor
    · rintro ⟨a, -, rfl⟩
      exact a.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  rw [htop]
  exact QA45_closure.symm

theorem hom_ext_QA45 {M : Type*} [Monoid M] {f g : A45 →* M}
    (hx : f x45A = g x45A) (hy : f y45A = g y45A) (hf : f f45A = g f45A) :
    f = g :=
  MonoidHom.eq_of_eqOn_dense closure_generators_QA45 (by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hf)

@[expose] noncomputable def GeneratorConjugacy (h : Tim79a.ParrottHyp z)
    {hN : ((J z).subgroupOf (H z)).Normal} (D : QuotientData (z := z) hN) : Prop :=
  ∃ P : GL8,
    actionQA45 (z := z) h D x45A = P * rhoAct (toQAct x45A) * P⁻¹ ∧
    actionQA45 (z := z) h D y45A = P * rhoAct (toQAct y45A) * P⁻¹ ∧
    actionQA45 (z := z) h D f45A = P * rhoAct (toQAct f45A) * P⁻¹

theorem actionQA45_eq_conj_rhoAct_of_generatorConjugacy
    (h : Tim79a.ParrottHyp z) {hN : ((J z).subgroupOf (H z)).Normal}
    (D : QuotientData (z := z) hN) (H : GeneratorConjugacy (z := z) h D) :
    ∃ P : GL8, P * P⁻¹ = 1 ∧
      ∀ a : A45,
        actionQA45 (z := z) h D a = P * rhoAct (toQAct a) * P⁻¹ := by
  obtain ⟨P, hx, hy, hf⟩ := H
  refine ⟨P, by simp, fun a => ?_⟩
  have hhom : actionQA45 (z := z) h D = (MulAut.conj P).toMonoidHom.comp rhoA := by
    refine hom_ext_QA45 ?_ ?_ ?_
    · simpa [MonoidHom.comp_apply, MulAut.conj_apply, rhoA, toQAct] using hx
    · simpa [MonoidHom.comp_apply, MulAut.conj_apply, rhoA, toQAct] using hy
    · simpa [MonoidHom.comp_apply, MulAut.conj_apply, rhoA, toQAct] using hf
  have hval := congrArg (fun f : A45 →* GL8 => f a) hhom
  rw [hval]
  simp [MonoidHom.comp_apply, MulAut.conj_apply, rhoA_apply]

theorem generatorConjugacy_of_actionQA45_eq_conj
    (h : Tim79a.ParrottHyp z) {hN : ((J z).subgroupOf (H z)).Normal}
    (D : QuotientData (z := z) hN)
    (H : ∃ P : GL8, P * P⁻¹ = 1 ∧
      ∀ a : A45,
        actionQA45 (z := z) h D a = P * rhoAct (toQAct a) * P⁻¹) :
    GeneratorConjugacy (z := z) h D := by
  obtain ⟨P, -, hP⟩ := H
  exact ⟨P, hP x45A, hP y45A, hP f45A⟩

theorem generatorConjugacy_iff_actionQA45_eq_conj_rhoAct
    (h : Tim79a.ParrottHyp z) {hN : ((J z).subgroupOf (H z)).Normal}
    (D : QuotientData (z := z) hN) :
    GeneratorConjugacy (z := z) h D ↔
      ∃ P : GL8, P * P⁻¹ = 1 ∧
        ∀ a : A45,
          actionQA45 (z := z) h D a = P * rhoAct (toQAct a) * P⁻¹ :=
  ⟨actionQA45_eq_conj_rhoAct_of_generatorConjugacy h D,
    generatorConjugacy_of_actionQA45_eq_conj h D⟩

end CFSG.RankThree.GF2n.Parrott
