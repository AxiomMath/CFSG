module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFS6
public import CFSG.RankThree.PartTwo.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Equiv

def s6T : Perm (Fin 6) := swap 0 1

def s6V1 : Perm (Fin 6) := swap 2 3 * swap 4 5

def s6V2 : Perm (Fin 6) := swap 2 4 * swap 3 5

def s6H : Perm (Fin 6) := swap 2 4 * swap 4 3

def s6X : Perm (Fin 6) := swap 0 2 * swap 2 3

theorem s6V1_mem : s6V1 ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem s6V2_mem : s6V2 ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem s6H_mem : s6H ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem s6X_mem : s6X ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem s6_relations :
    s6V1 ≠ 1 ∧ s6V2 ≠ 1 ∧ s6V1 ≠ s6V2 ∧ s6V1 * s6V1 = 1 ∧ s6V2 * s6V2 = 1 ∧
      s6V1 * s6V2 = s6V2 * s6V1 ∧ s6H * s6V1 * s6H⁻¹ = s6V2 ∧
      s6H * s6V2 * s6H⁻¹ = s6V1 * s6V2 ∧ s6T * s6V1 * s6T⁻¹ = s6V1 ∧
      s6T * s6V2 * s6T⁻¹ = s6V2 ∧ s6T * s6H * s6T⁻¹ = s6H ∧ s6T * s6T = 1 ∧
      s6T * s6X * s6T⁻¹ ≠ s6X := by
  unfold s6T s6V1 s6V2 s6H s6X
  decide

theorem exists_s6act_of_perm {Kb : Type} [Group Kb] [Finite Kb] (Cg : Subgroup Kb)
    (ι : Cg ≃* Perm (Fin 6)) {P : Subgroup Kb} (hPC : P ≤ Cg) (hPperf : Group.IsPerfect P)
    (hq : Nat.card (P ⧸ aschbacherSolvableCore 3 P) = 360) :
    ∃ t : Kb, t ∈ Cg ∧ t ^ 2 = 1 ∧ S6Act P t := by
  classical
  set φ : Perm (Fin 6) →* Kb := Cg.subtype.comp ι.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := fun x y h =>
    ι.symm.injective (Subtype.ext h)
  have hφCg : ∀ w, φ w ∈ Cg := fun w => (ι.symm w).2
  set P' : Subgroup Cg := P.subgroupOf Cg with hP'
  set Q : Subgroup (Perm (Fin 6)) := P'.map ι.toMonoidHom with hQ
  have hPP' : Nat.card P' = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv
  have hP'perf : Group.IsPerfect P' :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPC).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hQperf : Group.IsPerfect Q :=
    Group.IsPerfect.ofSurjective (f := (P'.equivMapOfInjective ι.toMonoidHom ι.injective
      ).toMonoidHom) (MulEquiv.surjective _)
  have hQalt : Q ≤ alternatingGroup (Fin 6) := by
    have h1 : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.mp hQperf
    rw [← h1, Subgroup.commutator_le]
    intro a _ b _
    rw [Equiv.Perm.mem_alternatingGroup, commutatorElement_def]
    simp only [map_mul, map_inv]
    rcases Int.units_eq_one_or (Equiv.Perm.sign a) with h | h <;>
      rcases Int.units_eq_one_or (Equiv.Perm.sign b) with h' | h' <;> simp [h, h']
  have h360 : 360 ∣ Nat.card P := hq ▸ Subgroup.card_quotient_dvd_card _
  have hQcard : Nat.card Q = Nat.card P := by
    rw [hQ, Subgroup.card_map_of_injective ι.injective, hPP']
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hPpos : 0 < Nat.card P := Nat.card_pos
  have hQeq : Q = alternatingGroup (Fin 6) := by
    apply Subgroup.eq_of_le_of_card_ge hQalt
    rw [hA6, hQcard]
    exact Nat.le_of_dvd hPpos h360
  have hPcard : Nat.card P = 360 := by
    rw [← hQcard, hQeq, hA6]
  have memP : ∀ z : Cg, (z : Kb) ∈ P ↔ ι z ∈ alternatingGroup (Fin 6) := by
    intro z
    constructor
    · intro hz
      rw [← hQeq]
      exact ⟨z, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
    · intro hz
      rw [← hQeq] at hz
      obtain ⟨y, hy, hyz⟩ := hz
      have : y = z := ι.injective hyz
      rw [this] at hy
      exact Subgroup.mem_subgroupOf.mp hy
  have hφP : ∀ w ∈ alternatingGroup (Fin 6), φ w ∈ P := by
    intro w hw
    have := (memP (ι.symm w)).mpr (by simpa using hw)
    exact this
  have hconj : ∀ g ∈ Cg, ∀ y ∈ P, g * y * g⁻¹ ∈ P := by
    intro g hg y hy
    have hyC : y ∈ Cg := hPC hy
    have h1 : ι ⟨y, hyC⟩ ∈ alternatingGroup (Fin 6) := (memP ⟨y, hyC⟩).mp hy
    have h2 : ι (⟨g, hg⟩ * ⟨y, hyC⟩ * ⟨g, hg⟩⁻¹) ∈ alternatingGroup (Fin 6) := by
      rw [map_mul, map_mul, map_inv]
      exact (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ h1 _
    exact (memP (⟨g, hg⟩ * ⟨y, hyC⟩ * ⟨g, hg⟩⁻¹)).mpr h2
  obtain ⟨hV1ne, hV2ne, hV12, hV1sq, hV2sq, hVc, hH1, hH2, hT1, hT2, hTH, hTsq, hTX⟩ :=
    s6_relations
  refine ⟨φ s6T, hφCg _, by rw [pow_two, ← map_mul, hTsq, map_one], ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hconj _ (hφCg _) y hy
    · intro hy
      have h1 := hconj ((φ s6T)⁻¹) (Cg.inv_mem (hφCg s6T)) _ hy
      have e : (φ s6T)⁻¹ * (φ s6T * y * (φ s6T)⁻¹) * ((φ s6T)⁻¹)⁻¹ = y := by group
      rwa [e] at h1
  ·
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 P)
    rw [hPcard, hq] at h1
    have h2 : Nat.card (aschbacherSolvableCore 3 P) = 1 := by omega
    exact Subgroup.eq_bot_of_card_eq _ h2
  ·
    refine ⟨φ s6V1, φ s6V2, φ s6H, hφP _ s6V1_mem, hφP _ s6V2_mem, hφP _ s6H_mem, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun h => hV1ne (hφinj (h.trans (map_one φ).symm))
    · exact fun h => hV2ne (hφinj (h.trans (map_one φ).symm))
    · exact fun h => hV12 (hφinj h)
    · rw [← map_mul, hV1sq, map_one]
    · rw [← map_mul, hV2sq, map_one]
    · rw [← map_mul, ← map_mul, hVc]
    · rw [← map_inv, ← map_mul, ← map_mul, hH1]
    · rw [← map_inv, ← map_mul, ← map_mul, hH2, map_mul]
    · rw [← map_inv, ← map_mul, ← map_mul, hT1]
    · rw [← map_inv, ← map_mul, ← map_mul, hT2]
    · rw [← map_inv, ← map_mul, ← map_mul, hTH]
  ·
    refine ⟨φ s6X, hφP _ s6X_mem, fun h => hTX (hφinj ?_)⟩
    rw [map_mul, map_mul, map_inv]
    exact h

end CFSG.RankThree.PartTwo.Sec8.Hering611
