module

public import CFSG.Sporadic.Recognition.McLMultiplierMats
public import CFSG.Sporadic.Recognition.McLMultiplierTables
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.Sporadic.Recognition.McLMultiplier

open CFSG.Sporadic.McL CFSG.LieType.Multipliers CFSG.Sporadic.Th


theorem b_pow_five : b ^ 5 = 1 :=
  mat_injective (by rw [mat_pow, mat_one]; exact matrixFacts.B_pow)

theorem b_inv_eq : b⁻¹ = b ^ 4 :=
  (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact b_pow_five)).symm

theorem mat_mclGenG (z : ℤ) : mat (mclGenG z) = mclLetY z := by
  unfold mclGenG mclLetY
  split_ifs
  · rfl
  · rfl
  · rw [b_inv_eq, mat_pow]
    rfl

theorem mat_wordG_mclGenG (w : List ℤ) : mat (wordG mclGenG w) = (w.map mclLetY).prod := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    unfold wordG at ih ⊢
    rw [List.map_cons, List.prod_cons, mat_mul, ih, mat_mclGenG, List.map_cons, List.prod_cons]

theorem mat_mclGen (i : Fin 6) : mat (mclGen i) = mclY i := mat_wordG_mclGenG _

section Facts

variable (hrels : ∀ r ∈ mclRels, mclEvalY r = 1)
include hrels

theorem mclGen_mul_self (i : Fin 6) : mclGen i * mclGen i = 1 := by
  have hmem : [(i, true), (i, true)] ∈ mclRels :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange i)))
  have h := hrels _ hmem
  unfold mclEvalY at h
  rw [List.map_cons, List.map_cons, List.map_nil, List.prod_cons, List.prod_cons, List.prod_nil,
    mul_one] at h
  apply mat_injective
  rw [mat_mul, mat_one, mat_mclGen, h]

theorem mclGen_inv (i : Fin 6) : (mclGen i)⁻¹ = mclGen i :=
  inv_eq_of_mul_eq_one_right (mclGen_mul_self hrels i)

theorem mat_lift_mclGen (w : List (Fin 6 × Bool)) :
    mat (FreeGroup.lift mclGen (FreeGroup.mk w)) = mclEvalY w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    have e : FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w := rfl
    unfold mclEvalY at ih ⊢
    rw [e, map_mul, mat_mul, ih, List.map_cons, List.prod_cons]
    obtain ⟨i, b⟩ := l
    cases b
    · have e1 : FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ := rfl
      rw [e1, map_inv, FreeGroup.lift_apply_of, mclGen_inv hrels, mat_mclGen]
    · have e1 : FreeGroup.mk [(i, true)] = FreeGroup.of i := rfl
      rw [e1, FreeGroup.lift_apply_of, mat_mclGen]

theorem lift_mclGen_rels_of : ∀ r ∈ wordSet mclRels, FreeGroup.lift mclGen r = 1 := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
  apply mat_injective
  rw [mat_lift_mclGen hrels, hrels v hv, mat_one]

theorem lift_mclCommW_of (hcomm : ∀ i : Fin 6, mclEvalY (mclCommWord i) = mclY i) (i : Fin 6) :
    FreeGroup.lift mclGen (mclCommW i) = mclGen i := by
  apply mat_injective
  rw [mclCommW, mat_lift_mclGen hrels, hcomm i, mat_mclGen]

theorem closure_mclGen_of (hA : mclEvalY mclSurjA = mA) (hB : mclEvalY mclSurjB = mB) :
    Subgroup.closure (Set.range mclGen) = ⊤ := by
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  have ha : a = FreeGroup.lift mclGen (FreeGroup.mk mclSurjA) := by
    apply mat_injective
    rw [mat_lift_mclGen hrels, hA]
    rfl
  have hb : b = FreeGroup.lift mclGen (FreeGroup.mk mclSurjB) := by
    apply mat_injective
    rw [mat_lift_mclGen hrels, hB]
    rfl
  rintro _ (rfl | rfl)
  · rw [ha]
    exact lift_mclGen_mem_closure _
  · rw [hb]
    exact lift_mclGen_mem_closure _

end Facts

theorem card_presentedGroup_le_of_cover (hcard : Finite MclCover ∧ Nat.card MclCover ≤ 2694384000)
    (h3 : 3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk mclR0) : MclCover))
    (hid : ∀ i : Fin 6, PresentedGroup.mk (wordSet mclRels) (mclCommW i) = PresentedGroup.of i) :
    Finite (PresentedGroup (wordSet mclRels)) ∧
      Nat.card (PresentedGroup (wordSet mclRels)) ≤ 898128000 := by
  obtain ⟨hfin, hle⟩ := hcard
  set Q := PresentedGroup (wordSet mclRels)
  have hf : FreeGroup.lift (fun i => (PresentedGroup.of i : Q)) = PresentedGroup.mk (wordSet mclRels) :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  have hrel : ∀ r ∈ coverRelators (wordSet mclRels) mclCommW,
      FreeGroup.lift (fun i => (PresentedGroup.of i : Q)) r = 1 := by
    rintro _ (⟨i, r, hr, rfl⟩ | ⟨i, rfl⟩)
    · rw [map_commutatorElement, hf, PresentedGroup.one_of_mem hr, commutatorElement_one_right]
    · rw [map_mul, map_inv, FreeGroup.lift_apply_of, hf, hid i, inv_mul_cancel]
  let ψ : MclCover →* Q := PresentedGroup.toGroup hrel
  have hψ : ψ.comp (PresentedGroup.mk _) = PresentedGroup.mk (wordSet mclRels) := by
    rw [← hf]
    exact FreeGroup.ext_hom _ _ fun i => PresentedGroup.toGroup.of hrel
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := PresentedGroup.mk_surjective _ y
    exact ⟨PresentedGroup.mk _ x, DFunLike.congr_fun hψ x⟩
  have hQ : Finite Q := Finite.of_surjective ψ hsurj
  refine ⟨hQ, ?_⟩
  have hz : (PresentedGroup.mk _ (FreeGroup.mk mclR0) : MclCover) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    have e := DFunLike.congr_fun hψ (FreeGroup.mk mclR0)
    rw [MonoidHom.comp_apply] at e
    rw [e]
    have hmem : mclR0 ∈ mclRels := List.mem_append_right _ (by unfold mclExtra; simp)
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hmem)
  have hdvd : 3 ∣ Nat.card ψ.ker := by
    have h2 := orderOf_dvd_natCard (⟨_, hz⟩ : ψ.ker)
    rw [Subgroup.orderOf_mk] at h2
    exact h3.trans h2
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hP : Nat.card MclCover = Nat.card Q * Nat.card ψ.ker := by
    rw [ψ.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv]
  have h3le : 3 ≤ Nat.card ψ.ker := Nat.le_of_dvd hpos hdvd
  have : Nat.card Q * 3 ≤ 2694384000 :=
    (Nat.mul_le_mul_left _ h3le).trans (hP ▸ hle)
  omega

theorem isPresentation_mclGen_of (hrels : ∀ r ∈ mclRels, mclEvalY r = 1)
    (hA : mclEvalY mclSurjA = mA) (hB : mclEvalY mclSurjB = mB)
    (hcard : Finite MclCover ∧ Nat.card MclCover ≤ 2694384000)
    (h3 : 3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk mclR0) : MclCover))
    (hid : ∀ i : Fin 6, PresentedGroup.mk (wordSet mclRels) (mclCommW i) = PresentedGroup.of i) :
    IsPresentation mclGen (wordSet mclRels) := by
  obtain ⟨hfin, hle⟩ := card_presentedGroup_le_of_cover hcard h3 hid
  exact IsPresentation.of_card_le (lift_mclGen_rels_of hrels) (closure_mclGen_of hrels hA hB)
    (by rw [card_J]; exact hle)

end CFSG.Sporadic.Recognition.McLMultiplier

end
