module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Blueprint (LieModel OddLieType)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)

@[expose] def Psp45Shape (T : Type) [Group T] : Prop :=
  LieModel T .PSp 2 5 1

theorem Psp45Shape.finite {T : Type} [Group T] (h : Psp45Shape T) : Finite T :=
  CFSG.LieType.Simplicity.finite_of_statedClassicalModel (h.statedClassicalModel (by decide))

theorem Psp45Shape.oddLieType {T : Type} [Group T] (h : Psp45Shape T) : OddLieType T :=
  ⟨.PSp, 2, 5, 1, Nat.prime_five, by norm_num, h.admissible, h⟩

theorem Psp45Shape.card_eq (hO : LieOrderFormulasInput) {T : Type} [Group T]
    (h : Psp45Shape T) : Nat.card T = 4680000 := by
  obtain ⟨-, hM, -⟩ := hO T .PSp 2 5 1 h.admissible h
  have hd : lieOrderDivisor .PSp 2 (5 ^ 1) = 2 := by decide
  have hn : lieOrderNumerator .PSp 2 (5 ^ 1) = 9360000 := by
    simp [lieOrderNumerator, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair]
  rw [hd, hn] at hM
  omega

theorem Psp45Shape.two_dvd_card (hO : LieOrderFormulasInput) {T : Type} [Group T]
    (h : Psp45Shape T) : 2 ∣ Nat.card T := by
  rw [h.card_eq hO]
  norm_num

theorem Psp45Shape.exists_not_commute (hO : LieOrderFormulasInput) {T : Type} [Group T]
    (h : Psp45Shape T) : ∃ a b : T, a * b ≠ b * a := by
  haveI := h.finite
  haveI : IsSimpleGroup T :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp T 2 5 1
      (h.statedClassicalModel (by decide))
  by_contra hcon
  have hcomm : ∀ a b : T, a * b = b * a := fun a b => by
    by_contra hne
    exact hcon ⟨a, b, hne⟩
  letI : CommGroup T := { ‹Group T› with mul_comm := hcomm }
  have hp := IsSimpleGroup.prime_card (α := T)
  rw [h.card_eq hO] at hp
  norm_num at hp

theorem Psp45Shape.card_facts (hO : LieOrderFormulasInput) {T : Type} [Group T]
    (h : Psp45Shape T) :
    168 ≤ Nat.card T ∧ ¬ Nat.card T ∣ 720 ∧ Nat.card T ≠ 20160 ∧ Nat.card T ≠ 25920 ∧
      Nat.card T ≠ 3265920 := by
  rw [h.card_eq hO]
  refine ⟨by norm_num, by decide, by norm_num, by norm_num, by norm_num⟩

theorem Psp45Shape.crossChar (hO : LieOrderFormulasInput) {T : Type} [Group T]
    (h : Psp45Shape T) {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : Nat.card T * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f)) :
    (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ f = 1) := by
  obtain ⟨t', n', p, g, -, hp2, hadm', hY⟩ := h.oddLieType
  exact CFSG.SeitzReduction.CrossChar.eq_of_crossChar_arith
    (CFSG.SeitzReduction.CrossChar.crossChar_arith hadm hadm' hp2 hM
      (hO T t' n' p g hadm' hY).2.1)

@[expose] def NoPsp45Factor (Y : Type) [Group Y] : Prop :=
  ∀ (T : Type) [Group T], Psp45Shape T → ¬ E1.IsCompositionFactor Y T

namespace NoPsp45Factor

theorem of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : NoPsp45Factor Y) :
    NoPsp45Factor Y' :=
  fun T _ hT hcf => h T hT ((CFSG.Quasithin.H13.L829N.isCompositionFactor_congr e).2 hcf)

theorem of_surjective {X Y : Type} [Group X] [Group Y] (f : X →* Y) (hf : Function.Surjective f)
    (h : NoPsp45Factor X) : NoPsp45Factor Y :=
  fun T _ hT hcf =>
    h T hT (CFSG.Quasithin.H13.L829N.isCompositionFactor_of_surjective f hf hcf)

theorem of_normal {Y : Type} [Group Y] (A : Subgroup Y) [A.Normal] (hA : NoPsp45Factor ↥A)
    (hQ : NoPsp45Factor (Y ⧸ A)) : NoPsp45Factor Y :=
  fun T _ hT hcf => (isCompositionFactor_of_normal A hcf).elim (hA T hT) (hQ T hT)

theorem of_commute (hO : LieOrderFormulasInput) {Y : Type} [Group Y] [Finite Y]
    (h : ∀ a b : Y, a * b = b * a) : NoPsp45Factor Y := by
  intro T _ hT hcf
  haveI := isCompositionFactor_finite hcf
  obtain ⟨a, b, hab⟩ := hT.exists_not_commute hO
  exact hab (isCompositionFactor_commute h hcf a b)

theorem of_commutator (hO : LieOrderFormulasInput) {Y : Type} [Group Y] [Finite Y]
    (h : NoPsp45Factor ↥(commutator Y)) : NoPsp45Factor Y :=
  of_normal (commutator Y) h (of_commute hO fun a b => mul_comm (G := Abelianization Y) a b)

theorem of_index_two (hO : LieOrderFormulasInput) {Y : Type} [Group Y] [Finite Y]
    (A : Subgroup Y) (hidx : A.index = 2) (hA : NoPsp45Factor ↥A) : NoPsp45Factor Y := by
  haveI : A.Normal := Subgroup.normal_of_index_eq_two hidx
  refine of_normal A hA (of_commute hO ?_)
  haveI : Fact (Nat.card (Y ⧸ A)).Prime :=
    ⟨by rw [← Subgroup.index_eq_card, hidx]; exact Nat.prime_two⟩
  haveI : IsCyclic (Y ⧸ A) := isCyclic_of_prime_card rfl
  exact fun a b => (IsCyclic.commGroup (α := Y ⧸ A)).mul_comm a b

theorem of_not_dvd {Y : Type} [Group Y] [Finite Y]
    (h : ∀ (T : Type) [Group T], Psp45Shape T → ¬ Nat.card T ∣ Nat.card Y) :
    NoPsp45Factor Y :=
  fun T _ hT hcf => h T hT (isCompositionFactor_natCard_dvd hcf)

theorem of_isSimpleGroup {Y : Type} [Group Y] [IsSimpleGroup Y]
    (h : ∀ (T : Type) [Group T], Psp45Shape T → IsEmpty (Y ≃* T)) : NoPsp45Factor Y :=
  fun T _ hT hcf => (h T hT).false (isCompositionFactor_mulEquiv_of_isSimpleGroup hcf).some

end NoPsp45Factor

end CFSG.LocalAnalysis.WeakClosure81

end
