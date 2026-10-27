module

public import CFSG.LieType.Multipliers.PresentedCover

public section

namespace CFSG.Sporadic.Recognition.CoverTransfer

open Subgroup CFSG.LieType.Multipliers CFSG.RankThree.PerfectCover
open scoped commutatorElement

universe u

section Perturbation

variable {G : Type*} [Group G] {ι : Type*}

theorem inv_lift_mul_lift_mem_center {f f' : ι → G} (hc : ∀ i, (f i)⁻¹ * f' i ∈ center G)
    (x : FreeGroup ι) : (FreeGroup.lift f x)⁻¹ * FreeGroup.lift f' x ∈ center G := by
  induction x using FreeGroup.induction_on with
  | one => simp [one_mem]
  | of i => simpa using hc i
  | inv_of i _ =>
    have hci := hc i
    simp only [map_inv, FreeGroup.lift_apply_of, inv_inv]
    have e : f i * (f' i)⁻¹ = f i * ((f i)⁻¹ * f' i)⁻¹ * (f i)⁻¹ := by group
    rw [e, mem_center_iff.mp (inv_mem hci) (f i), mul_inv_cancel_right]
    exact inv_mem hci
  | mul x y hx hy =>
    have e : (FreeGroup.lift f (x * y))⁻¹ * FreeGroup.lift f' (x * y) =
        (FreeGroup.lift f y)⁻¹ * ((FreeGroup.lift f x)⁻¹ * FreeGroup.lift f' x) *
          FreeGroup.lift f' y := by
      simp only [map_mul]
      group
    rw [e, mem_center_iff.mp hx, mul_assoc]
    exact mul_mem hx hy

theorem eq_of_mem_commutator {H : Type*} [Group H] (φ φ' : H →* G)
    (hc : ∀ x, (φ x)⁻¹ * φ' x ∈ center G) {x : H} (hx : x ∈ commutator H) : φ x = φ' x := by
  have hle : commutator H ≤ MonoidHom.eqLocus φ φ' := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    change φ ⁅a, b⁆ = φ' ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement]
    have ha : φ' a = φ a * ((φ a)⁻¹ * φ' a) := by group
    have hb : φ' b = φ b * ((φ b)⁻¹ * φ' b) := by group
    rw [ha, hb, CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (hc a) (hc b)]
  exact hle hx

theorem lift_eq_lift_of_mem_commutator {f f' : ι → G} (hc : ∀ i, (f i)⁻¹ * f' i ∈ center G)
    {w : FreeGroup ι} (hw : w ∈ commutator (FreeGroup ι)) :
    FreeGroup.lift f' w = FreeGroup.lift f w :=
  (eq_of_mem_commutator (FreeGroup.lift f) (FreeGroup.lift f')
    (inv_lift_mul_lift_mem_center hc) hw).symm

theorem lift_mk_mem {f : ι → G} {K : Subgroup G} :
    ∀ {w : List (ι × Bool)}, (∀ l ∈ w, f l.1 ∈ K) → FreeGroup.lift f (FreeGroup.mk w) ∈ K
  | [], _ => by simp [one_mem]
  | l :: w, h => by
    rw [show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w by
      rw [FreeGroup.mul_mk]; rfl, map_mul]
    refine mul_mem ?_ (lift_mk_mem fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨i, b⟩ := l
    have hi : f i ∈ K := h (i, b) List.mem_cons_self
    cases b
    · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      exact inv_mem hi
    · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      exact hi

end Perturbation

section Quotients

variable {G : Type*} [Group G] {X : Type*} [Group X] {κ : Type*}

theorem coverRelators_lift_comm (π : G →* X) (hker : π.ker ≤ center G) {s : κ → G}
    {R' : Set (FreeGroup κ)} {w' : κ → FreeGroup κ} (hw' : ∀ k, w' k ∈ commutator (FreeGroup κ))
    (hR' : ∀ r ∈ R', FreeGroup.lift (π ∘ s) r = 1)
    (hs : ∀ k, FreeGroup.lift (π ∘ s) (w' k) = π (s k)) :
    ∀ r ∈ coverRelators R' w', FreeGroup.lift (fun k => FreeGroup.lift s (w' k)) r = 1 := by
  have hcomp : ∀ f : κ → G, π.comp (FreeGroup.lift f) = FreeGroup.lift (π ∘ f) := fun f =>
    FreeGroup.ext_hom _ _ fun i => by simp
  have hπ : ∀ x : FreeGroup κ, π (FreeGroup.lift s x) = FreeGroup.lift (π ∘ s) x := fun x => by
    rw [← MonoidHom.comp_apply, hcomp]
  have hy : ∀ k, π (FreeGroup.lift s (w' k)) = π (s k) := fun k => by rw [hπ, hs]
  have hπy : π ∘ (fun k => FreeGroup.lift s (w' k)) = π ∘ s := funext hy
  have hc : ∀ k, (s k)⁻¹ * FreeGroup.lift s (w' k) ∈ center G := fun k => hker <| by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
  refine lift_coverRelators_eq_one_iff.mpr ⟨fun k r hr => ?_, fun k => ?_⟩
  · have hz : FreeGroup.lift (fun k => FreeGroup.lift s (w' k)) r ∈ center G := hker <| by
      rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hcomp, hπy]
      exact hR' r hr
    exact (commutatorElement_eq_one_iff_mul_comm).mpr (mem_center_iff.mp hz _)
  · exact lift_eq_lift_of_mem_commutator hc (hw' k)

theorem card_closure_range_le {R' : Set (FreeGroup κ)} {w' : κ → FreeGroup κ} {y : κ → G}
    (hy : ∀ r ∈ coverRelators R' w', FreeGroup.lift y r = 1) [Finite (PresentedCover R' w')] :
    Nat.card (closure (Set.range y)) ≤ Nat.card (PresentedCover R' w') := by
  have hrange : (PresentedGroup.toGroup hy).range = closure (Set.range y) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← Set.range_comp]
    congr 2
    funext k
    exact PresentedGroup.toGroup.of hy
  rw [← hrange]
  exact Nat.card_le_card_of_surjective _ (PresentedGroup.toGroup hy).rangeRestrict_surjective

end Quotients

section Lifts

variable {X : Type} [Group X] {ι : Type u} {g : ι → X} {R : Set (FreeGroup ι)}
  {w : ι → FreeGroup ι}

theorem exists_surjective_lift (hP : IsPresentation g R)
    (hw : ∀ i, w i ∈ commutator (FreeGroup ι)) (hwg : ∀ i, FreeGroup.lift g (w i) = g i)
    {L : Type*} [Group L] [Group.IsPerfect L] (q : L →* X)
    (hq : Function.Surjective q) (hker : q.ker ≤ center L) :
    ∃ φ : PresentedCover R w →* L, Function.Surjective φ ∧ q.comp φ = coverMap hP hwg := by
  refine ⟨(hopfLift q hq hker).comp (presentedCoverEquiv hP hw hwg).toMonoidHom,
    (hopfLift_surjective q hq hker).comp (presentedCoverEquiv hP hw hwg).surjective,
    MonoidHom.ext fun x => ?_⟩
  change q (hopfLift q hq hker (presentedCoverEquiv hP hw hwg x)) = coverMap hP hwg x
  rw [← hopfCoverMap_presentedCoverEquiv hP hw hwg x, ← comp_hopfLift q hq hker,
    MonoidHom.comp_apply]

theorem exists_bijective_of_card_le (hP : IsPresentation g R)
    (hw : ∀ i, w i ∈ commutator (FreeGroup ι)) (hwg : ∀ i, FreeGroup.lift g (w i) = g i)
    {L : Type*} [Group L] [Group.IsPerfect L] (q : L →* X)
    (hq : Function.Surjective q) (hker : q.ker ≤ center L)
    [Finite (PresentedCover R w)] (hcard : Nat.card (PresentedCover R w) ≤ Nat.card L) :
    ∃ φ : PresentedCover R w →* L, Function.Bijective φ ∧ q.comp φ = coverMap hP hwg := by
  refine ⟨(hopfLift q hq hker).comp (presentedCoverEquiv hP hw hwg).toMonoidHom,
    ((hopfLift_surjective q hq hker).comp
      (presentedCoverEquiv hP hw hwg).surjective).bijective_of_nat_card_le hcard,
    MonoidHom.ext fun x => ?_⟩
  change q (hopfLift q hq hker (presentedCoverEquiv hP hw hwg x)) = coverMap hP hwg x
  rw [← hopfCoverMap_presentedCoverEquiv hP hw hwg x, ← comp_hopfLift q hq hker,
    MonoidHom.comp_apply]

end Lifts

section Squares

variable {L : Type*} [Group L] {X : Type*} [Group X]

theorem sq_eq_sq_of_conj (q : L →* X) (hq : Function.Surjective q) (hker : q.ker ≤ center L)
    (hexp : ∀ c ∈ q.ker, c ^ 2 = 1) {v p : L} {h : X} (hv : q v = h * q p * h⁻¹)
    (hp : q p ^ 2 = 1) : v ^ 2 = p ^ 2 := by
  obtain ⟨y, rfl⟩ := hq h
  have hyp : q (y * p * y⁻¹) = q v := by rw [hv, map_mul, map_mul, map_inv]
  obtain ⟨c, hc, rfl⟩ : ∃ c ∈ q.ker, v = y * p * y⁻¹ * c :=
    ⟨(y * p * y⁻¹)⁻¹ * v, by rw [MonoidHom.mem_ker, map_mul, map_inv, hyp, inv_mul_cancel],
      (mul_inv_cancel_left _ _).symm⟩
  have hp2 : p ^ 2 ∈ center L := hker (by rw [MonoidHom.mem_ker, map_pow, hp])
  have hcomm : c * (y * p * y⁻¹) = (y * p * y⁻¹) * c := (mem_center_iff.mp (hker hc) _).symm
  have e1 : (y * p * y⁻¹ * c) ^ 2 = y * p ^ 2 * y⁻¹ * c ^ 2 := by
    rw [pow_two, pow_two, pow_two]
    calc y * p * y⁻¹ * c * (y * p * y⁻¹ * c)
        = y * p * y⁻¹ * (c * (y * p * y⁻¹)) * c := by group
      _ = y * p * y⁻¹ * ((y * p * y⁻¹) * c) * c := by rw [hcomm]
      _ = y * (p * p) * y⁻¹ * (c * c) := by group
  have e2 : y * p ^ 2 * y⁻¹ = p ^ 2 := by
    rw [mul_assoc, (mem_center_iff.mp hp2 y⁻¹).symm, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [e1, e2, hexp c hc, mul_one]

end Squares

end CFSG.Sporadic.Recognition.CoverTransfer
