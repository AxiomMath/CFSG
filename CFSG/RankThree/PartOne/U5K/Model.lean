module

public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.PartOne.S12.PushingUp
import CFSG.Models.PGLSimple

public noncomputable section

namespace CFSG.RankThree.PartOne.U5K

open CFSG
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.Sec4

@[expose] def U5Inn (f : ℕ) : Subgroup (MulAut (projSU 5 2 f)) :=
  (MulAut.conj : projSU 5 2 f →* MulAut (projSU 5 2 f)).range

theorem u5FieldData (f : ℕ) (hf : 1 ≤ f) : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
  unitaryFieldData_galoisField 2 f hf

@[expose] def u5Equiv (f : ℕ) (hf : 1 ≤ f) :
    projSU 5 2 f ≃* primeFormP (u5FieldData f hf)
      ((1 : GL (Fin 5) (GaloisField 2 (2 * f))) :
        Matrix (Fin 5) (Fin 5) (GaloisField 2 (2 * f))) :=
  (projSUEquivStatedProj 5 2 f).trans
    ((unitaryPSUEquiv (u5FieldData f hf) (by norm_num)).symm.trans
      (Classical.choice (unitary_prime_form_full_semilinear_realization (u5FieldData f hf)
        (isPrimeFormGram_one_GL (n := 5) (K := GaloisField 2 (2 * f))) (by norm_num)
        (by omega)).1).symm)

theorem u5_finite (f : ℕ) (hf : 1 ≤ f) : Finite (projSU 5 2 f) := by
  have : NeZero (2 * f) := ⟨by omega⟩
  have : Finite (GaloisField 2 (2 * f)) := inferInstance
  have : Finite (GL (Fin 5) (GaloisField 2 (2 * f))) := inferInstance
  have : Finite (Matrix.ProjGenLinGroup (Fin 5) (GaloisField 2 (2 * f))) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  infer_instance

theorem u5_isPerfect (f : ℕ) (hf : 1 ≤ f) : Group.IsPerfect (projSU 5 2 f) := by
  have hP : Group.IsPerfect (primeFormP (u5FieldData f hf)
      ((1 : GL (Fin 5) (GaloisField 2 (2 * f))) :
        Matrix (Fin 5) (Fin 5) (GaloisField 2 (2 * f)))) := by
    have := CFSG.RankThree.Classical.isPerfect_gramSU_one (u5FieldData f hf) (n := 5)
      (by norm_num) (by omega)
    exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.ofSurjective (f := (u5Equiv f hf).symm.toMonoidHom)
    (u5Equiv f hf).symm.surjective

theorem u5_isSimpleGroup (f : ℕ) (hf : 1 ≤ f) : IsSimpleGroup (projSU 5 2 f) :=
  CFSG.PGLModel.isSimpleGroup_projSU_of_admissible ⟨Nat.prime_two, hf, by norm_num, fun h => by have := (Prod.mk.inj h).1; omega⟩

theorem u5_normal_two_eq_bot (f : ℕ) (hf : 1 ≤ f) (K : Subgroup (projSU 5 2 f)) [K.Normal]
    (hK : IsPGroup 2 K) : K = ⊥ := by
  have hs := u5_isSimpleGroup f hf
  have hp := u5_isPerfect f hf
  rcases hs.eq_bot_or_eq_top_of_normal K with h | h
  · exact h
  · exfalso
    subst h
    have h2 : IsPGroup 2 (projSU 5 2 f) :=
      (show IsPGroup 2 (⊤ : Subgroup (projSU 5 2 f)) from hK).of_equiv Subgroup.topEquiv
    have := u5_finite f hf
    have h3 : Group.IsNilpotent (projSU 5 2 f) := h2.isNilpotent
    exact (Group.IsPerfect.not_isNilpotent (G := projSU 5 2 f)) h3

@[expose] def u5FieldFactor (f : ℕ) (hf : 1 ≤ f) :
    MulAut (projSU 5 2 f) →* (GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f)) :=
  (primeFormFieldFactor (u5FieldData f hf)
    (isPrimeFormGram_one_GL (n := 5) (K := GaloisField 2 (2 * f))) (by norm_num)
    (by omega)).comp (MulAut.congr (u5Equiv f hf)).toMonoidHom

@[expose] def U5Inndiag (f : ℕ) : Subgroup (MulAut (projSU 5 2 f)) :=
  if hf : 1 ≤ f then (u5FieldFactor f hf).ker else ⊥

@[expose] def zOf {G : Type*} [Group G] (S : Subgroup G) : Subgroup G :=
  (Subgroup.center ↥S).map S.subtype

theorem mem_zOf_iff {G : Type*} [Group G] {S : Subgroup G} {v : G} :
    v ∈ zOf S ↔ v ∈ S ∧ ∀ s ∈ S, s * v = v * s := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, fun s hs => congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨s, hs⟩)⟩
  · rintro ⟨hv, hc⟩
    exact ⟨⟨v, hv⟩, Subgroup.mem_center_iff.2 fun s => Subtype.ext (hc s s.2), rfl⟩

theorem zOf_le {G : Type*} [Group G] (S : Subgroup G) : zOf S ≤ S := Subgroup.map_subtype_le _

structure U5ModelAt (f p : ℕ) (T : Subgroup (MulAut (projSU 5 2 f))) : Prop where
  le_inn : pushingUpS T ≤ U5Inn f
  irreducible : ∀ R : Subgroup (MulAut (projSU 5 2 f)), R ≤ pushingUpS T →
    U5Inn f ⊓ Subgroup.normalizer (pushingUpS T : Set (MulAut (projSU 5 2 f))) ≤
      Subgroup.normalizer (R : Set (MulAut (projSU 5 2 f))) →
    R = ⊥ ∨ R = zOf (pushingUpS T) ∨ R = pushingUpS T
  core : ∀ R : Subgroup (MulAut (projSU 5 2 f)), IsPGroup 2 R →
    U5Inn f ⊓ Subgroup.normalizer (pushingUpS T : Set (MulAut (projSU 5 2 f))) ≤
      Subgroup.normalizer (R : Set (MulAut (projSU 5 2 f))) → R ≤ pushingUpS T
  faithful : ∀ B : Subgroup (MulAut (projSU 5 2 f)),
    B ≤ Subgroup.normalizer (pushingUpS T : Set (MulAut (projSU 5 2 f))) ⊓ U5Inndiag f →
    IsElementaryAbelian p B → Nat.card B = p ^ 2 →
    ∃ b ∈ B, b ≠ 1 ∧ b ∈ Subgroup.centralizer (zOf (pushingUpS T) : Set (MulAut (projSU 5 2 f)))
  cyclic : ∀ P : Subgroup (MulAut (projSU 5 2 f)), IsPGroup p P →
    P ≤ Subgroup.centralizer (zOf (pushingUpS T) : Set (MulAut (projSU 5 2 f))) → IsCyclic ↥P

@[expose] def U5Model : Prop :=
  ∀ (f : ℕ), 1 ≤ f → ∀ (p : ℕ), p.Prime → 5 ≤ p → p ∣ 2 ^ f + 1 →
    ∀ H T : Subgroup (MulAut (projSU 5 2 f)), U5Inn f ≤ H → IsSylowOf 2 T H → U5ModelAt f p T

end CFSG.RankThree.PartOne.U5K
