module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofTitsCore

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Res423Two

open Equiv Equiv.Perm

structure ThetaLike {n : ℕ} (b : Perm (Fin n)) (P : Subgroup (Perm (Fin n))) : Prop where
  coprime : ∀ y ∈ P, Nat.Coprime (orderOf y) 3
  comm : ∀ y ∈ P, y * b = b * y
  even : P ≤ alternatingGroup (Fin n)
  conj : ∀ y ∈ P, ∀ g ∈ alternatingGroup (Fin n), g * b = b * g → g * y * g⁻¹ ∈ P

variable {n : ℕ}

@[expose] noncomputable def thetaPerm (b : alternatingGroup (Fin n)) : Subgroup (Perm (Fin n)) :=
  ((aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set (alternatingGroup (Fin n))))).map
    (Subgroup.centralizer ({b} : Set (alternatingGroup (Fin n)))).subtype).map
      (alternatingGroup (Fin n)).subtype

theorem thetaLike_thetaPerm (b : alternatingGroup (Fin n)) :
    ThetaLike (b : Perm (Fin n)) (thetaPerm b) := by
  set C := Subgroup.centralizer ({b} : Set (alternatingGroup (Fin n))) with hC
  set N := aschbacherSolvableCore 3 C with hN
  have hN3 : ¬ 3 ∣ Nat.card N :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    have h1 : orderOf (⟨t, ht⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    have h2 : orderOf ((alternatingGroup (Fin n)).subtype (C.subtype t)) =
        orderOf (⟨t, ht⟩ : N) := by
      rw [Subgroup.orderOf_mk]
      exact (orderOf_injective _ (alternatingGroup (Fin n)).subtype_injective _).trans
        (orderOf_injective _ C.subtype_injective t)
    rw [h2]
    exact Nat.Coprime.coprime_dvd_left h1
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3).symm
  · rintro _ ⟨_, ⟨t, -, rfl⟩, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp t.2
    exact congrArg Subtype.val h1
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ g hg hgb
    set g' : alternatingGroup (Fin n) := ⟨g, hg⟩
    have hg'C : g' ∈ C := by
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hgb
    set gc : C := ⟨g', hg'C⟩
    refine ⟨C.subtype (gc * t * gc⁻¹), ⟨gc * t * gc⁻¹, ?_, rfl⟩, rfl⟩
    exact (inferInstance : N.Normal).conj_mem t ht gc

theorem core_eq_bot_of_thetaPerm {b : alternatingGroup (Fin n)} (h : thetaPerm b = ⊥) :
    aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set (alternatingGroup (Fin n)))) = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp
    ((Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h)

theorem ThetaLike.congr {b b' : Perm (Fin n)} {P : Subgroup (Perm (Fin n))}
    (h : ∀ g : Perm (Fin n), g * b = b * g ↔ g * b' = b' * g) (hP : ThetaLike b P) :
    ThetaLike b' P :=
  ⟨hP.coprime, fun y hy => (h y).mp (hP.comm y hy), hP.even,
    fun y hy g hg hgb => hP.conj y hy g hg ((h g).mpr hgb)⟩

theorem commute_sq_iff {G : Type*} [Group G] {b : G} (hb : b ^ 3 = 1) (g : G) :
    g * b = b * g ↔ g * b ^ 2 = b ^ 2 * g := by
  constructor
  · intro h
    exact ((Commute.pow_right h 2).eq)
  · intro h
    have h4 : (b ^ 2) ^ 2 = b := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hb, one_mul, pow_one]
    have := (Commute.pow_right h 2).eq
    rwa [h4] at this

theorem ThetaLike.false_of_mem {b : Perm (Fin n)} {P : Subgroup (Perm (Fin n))}
    (hP : ThetaLike b P) {z : Perm (Fin n)} (hz : z ∈ P) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    False := by
  have h := hP.coprime z hz
  rw [orderOf_eq_prime hz3 hz1] at h
  exact absurd h (by norm_num)

theorem ThetaLike.commutator_mem {b : Perm (Fin n)} {P : Subgroup (Perm (Fin n))}
    (hP : ThetaLike b P) {y : Perm (Fin n)} (hy : y ∈ P) {g : Perm (Fin n)}
    (hg : g ∈ alternatingGroup (Fin n)) (hgb : g * b = b * g) : y * g * y⁻¹ * g⁻¹ ∈ P := by
  have h := mul_mem hy (hP.conj y⁻¹ (inv_mem hy) g hg hgb)
  simpa [mul_assoc] using h

end Res423Two

end CFSG.RankThree.PartTwo.Sec4
