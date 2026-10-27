module

public import CFSG.Monster.Schur.CentralEps
public import CFSG.Monster.Schur.M24.Words
public import CFSG.Monster.Schur.M24.CheckPlain
public import CFSG.Monster.Schur.M24.Checks
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.M24Exact
public import CFSG.Sporadic.Bridge.M24Surj
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9123
public import CFSG.Monster.Schur.M24Cast
public import CFSG.Monster.Schur.M24Lift
public import CFSG.Monster.Schur.M24.Twist
public import Certificates.Certificate9250
public import Certificates.Certificate9267
public import Certificates.Certificate9215
public import Certificates.Certificate9251
public import Certificates.Certificate9252
public import Certificates.Certificate9253
public import Certificates.Certificate9254
public import Certificates.Certificate9255
public import Certificates.Certificate9256
public import Certificates.Certificate9257
public import Certificates.Certificate9258
public import Certificates.Certificate9259
public import Certificates.Certificate9260
public import Certificates.Certificate9261
public import Certificates.Certificate9262
public import Certificates.Certificate9263
public import Certificates.Certificate9264
public import Certificates.Certificate9265
public import Certificates.Certificate9266
public import Certificates.Certificate3017
public meta import CFSG.Monster.Schur.M24.Words
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort

public section

namespace CFSG.Monster.Schur.M24

open TauCeti CFSG.CosetTable CFSG.Sporadic.Presentation

theorem a2_mem :
    castTo a2 ∈ pres.relators := by
  exact Certificates.certificate9267.1

theorem b3_mem :
    castTo b3 ∈ pres.relators := by
  exact Certificates.certificate9267.2.1

theorem ab23_mem :
    castTo ab23 ∈ pres.relators := by
  exact Certificates.certificate9267.2.2.1

theorem r5_mem :
    castTo r5 ∈ pres.relators := by
  exact Certificates.certificate9267.2.2.2.1

theorem r6_mem :
    castTo r6 ∈ pres.relators := by
  exact Certificates.certificate9267.2.2.2.2.1

theorem r7_mem :
    castTo r7 ∈ pres.relators := by
  exact Certificates.certificate9267.2.2.2.2.2

@[expose] def gen :
    Fin 2 → SporadicName.M24.Group := fun i => PresentedGroup.of (idx i)

theorem lift_gen_eq_one
    {w : List (Fin 2 × Bool)} (hw : castTo w ∈ pres.relators) :
    FreeGroup.lift gen (FreeGroup.mk w) = 1 := by
  have hmk : (PresentedGroup.mk pres.relatorSet : FreeGroup (Fin pres.generatorCount) →*
      SporadicName.M24.Group) = FreeGroup.lift PresentedGroup.of :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  have h1 : FreeGroup.lift gen (FreeGroup.mk w) =
      PresentedGroup.mk pres.relatorSet (FreeGroup.mk (castTo w)) := by
    rw [hmk]
    simp [castTo, gen, FreeGroup.lift_mk, List.map_map, Function.comp_def]
  rw [h1]
  exact PresentedGroup.one_of_mem (by rw [relatorSet_eq]; exact List.mem_map_of_mem hw)

theorem closure_gen : Subgroup.closure (Set.range gen) = ⊤ := by
  have h : Set.range gen = Set.range
      (PresentedGroup.of : Fin pres.generatorCount → SporadicName.M24.Group) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨idx i, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Fin.cast generatorCount_eq j, by simp [gen, idx]⟩
  rw [h]
  exact PresentedGroup.closure_range_of _

section Lifts

variable {E : Type*} [Group E]

theorem lift_b3 (f : Fin 2 → E) : FreeGroup.lift f (FreeGroup.mk b3) = f 1 ^ 3 := by
  simp [b3, FreeGroup.lift_mk, pow_succ, mul_assoc]

theorem lift_ab23 (f : Fin 2 → E) :
    FreeGroup.lift f (FreeGroup.mk ab23) = (f 0 * f 1) ^ 23 := by
  rw [ab23, mk_flatten_replicate, map_pow]
  simp [FreeGroup.lift_mk]

end Lifts

theorem gen_pow_three :
    gen 1 ^ 3 = 1 := by
  rw [← lift_b3 gen]
  exact lift_gen_eq_one b3_mem

theorem gen_pow_23 :
    (gen 0 * gen 1) ^ 23 = 1 := by
  rw [← lift_ab23 gen]
  exact lift_gen_eq_one ab23_mem

theorem exists_lifts
    (E : Type) [Group E] (π : E →* SporadicName.M24.Group)
    (hπ : Function.Surjective π) (hk : Nat.card π.ker = 2) :
    ∃ ĝ : Fin 2 → E, (∀ i, π (ĝ i) = gen i) ∧
      ∀ r ∈ U, FreeGroup.lift ĝ (FreeGroup.mk r) = 1 := by
  obtain ⟨a₀, ha₀⟩ := hπ (gen 0)
  obtain ⟨b₀, hb₀⟩ := hπ (gen 1)
  have hb : π b₀ ^ 3 = 1 := by rw [hb₀]; exact gen_pow_three
  have hab : (π a₀ * π b₀) ^ 23 = 1 := by rw [ha₀, hb₀]; exact gen_pow_23
  obtain ⟨a', b', ha', hb', hb3, hab23⟩ :=
    exists_lift_pair π hk a₀ b₀ ⟨1, rfl⟩ ⟨11, rfl⟩ hb hab
  refine ⟨![a', b'], fun i => ?_, fun r hr => ?_⟩
  · fin_cases i
    · simp [ha', ha₀]
    · simp [hb', hb₀]
  · simp only [U, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [lift_b3]
      simpa using hb3
    · rw [lift_ab23]
      simpa using hab23

theorem lift_gen_T
    (i : Fin 4) : FreeGroup.lift gen (FreeGroup.mk (T i)) = 1 := by
  fin_cases i
  · exact lift_gen_eq_one a2_mem
  · exact lift_gen_eq_one r5_mem
  · exact lift_gen_eq_one r6_mem
  · exact lift_gen_eq_one r7_mem

theorem r4_mem : castTo r4 ∈ pres.relators :=
  castTo_mem_relators (by rw [relatorLetters_eq]; decide +kernel)

theorem lift_gen_T5
    (i : Fin 5) : FreeGroup.lift gen (FreeGroup.mk (T5 i)) = 1 := by
  fin_cases i
  · exact lift_gen_eq_one a2_mem
  · exact lift_gen_eq_one r4_mem
  · exact lift_gen_eq_one r5_mem
  · exact lift_gen_eq_one r6_mem
  · exact lift_gen_eq_one r7_mem

theorem bound_pres :
    Finite (PG 2 (U ++ (List.finRange 5).map T5)) ∧
      Nat.card (PG 2 (U ++ (List.finRange 5).map T5)) ≤ Nat.card SporadicName.M24.Group := by
  have hmk : (FreeGroup.lift (PresentedGroup.of : Fin 2 → PG 2 (U ++ (List.finRange 5).map T5))) =
      PresentedGroup.mk _ :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  have hf : ∀ w ∈ [a2, b3, ab23, r4, r5, r6, r7],
      FreeGroup.lift (PresentedGroup.of : Fin 2 → PG 2 (U ++ (List.finRange 5).map T5))
        (FreeGroup.mk w) = 1 := by
    intro w hw
    have hmem : w ∈ U ++ (List.finRange 5).map T5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hmk]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hmem)
  set φ := liftHom _ hf
  have hs : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
      Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of (idx i), liftHom_of _ hf i⟩
  have hfin : Finite SporadicName.M24.Group := CFSG.Sporadic.Presentation.M24.finite_card_le.1
  exact ⟨Finite.of_surjective φ hs, Nat.card_le_card_of_surjective φ hs⟩

end CFSG.Monster.Schur.M24

namespace CFSG.Monster.Schur

open TauCeti CFSG.CosetTable CFSG.Sporadic.Presentation CFSG.Monster.Schur.M24

theorem noPerfectDoubleCover_M24 :
    NoPerfectDoubleCover SporadicName.M24.Group := by
  have hfin : Finite SporadicName.M24.Group :=
    CFSG.Sporadic.Presentation.M24.finite_card_le.1
  have hcard : 244823040 ≤ Nat.card SporadicName.M24.Group := by
    obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
    rw [← Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M24]
  refine noPerfectDoubleCover_of_eps_cases (m := 2) (k := 5) gen closure_gen U T5
    exists_lifts lift_gen_T5 bound_pres ?_
  · intro e he
    exact ⟨(bound_eps e he).1, (bound_eps e he).2.trans hcard⟩

theorem noPerfectDoubleCover_nativeM24 :
    NoPerfectDoubleCover CFSG.Blueprint.NativeSporadic.M24 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  exact NoPerfectDoubleCover.of_mulEquiv e.symm noPerfectDoubleCover_M24

end CFSG.Monster.Schur
