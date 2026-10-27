module

public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestPairing
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest

open Subgroup CFSG.CosetTable
open scoped commutatorElement

section Words

variable {m : ℕ}

@[expose] def evalW {G : Type*} [Group G] (g : Fin m → G) (w : List (Fin m × Bool)) : G :=
  (w.map fun x => cond x.2 (g x.1) (g x.1)⁻¹).prod

@[expose] def invW (w : List (Fin m × Bool)) : List (Fin m × Bool) :=
  w.reverse.map fun x => (x.1, !x.2)

@[expose] def commW (a b : List (Fin m × Bool)) : List (Fin m × Bool) :=
  a ++ b ++ invW a ++ invW b

variable {G : Type*} [Group G]

theorem evalW_nil (g : Fin m → G) : evalW g [] = 1 := rfl

theorem evalW_cons (g : Fin m → G) (x : Fin m × Bool) (w : List (Fin m × Bool)) :
    evalW g (x :: w) = cond x.2 (g x.1) (g x.1)⁻¹ * evalW g w := by
  simp [evalW]

theorem evalW_append (g : Fin m → G) (a b : List (Fin m × Bool)) :
    evalW g (a ++ b) = evalW g a * evalW g b := by
  simp [evalW]

theorem evalW_invW (g : Fin m → G) (w : List (Fin m × Bool)) :
    evalW g (invW w) = (evalW g w)⁻¹ := by
  induction w with
  | nil => simp [evalW, invW]
  | cons x w ih =>
    have h : invW (x :: w) = invW w ++ [(x.1, !x.2)] := by simp [invW]
    rw [h, evalW_append, ih, evalW_cons g x w, mul_inv_rev]
    obtain ⟨i, b⟩ := x
    cases b <;> simp [evalW]

theorem evalW_commW (g : Fin m → G) (a b : List (Fin m × Bool)) :
    evalW g (commW a b) = ⁅evalW g a, evalW g b⁆ := by
  rw [commW, evalW_append, evalW_append, evalW_append, evalW_invW, evalW_invW,
    commutatorElement_def]

theorem map_evalW {G' F : Type*} [Group G'] [FunLike F G G'] [MonoidHomClass F G G'] (f : F)
    (g : Fin m → G) (w : List (Fin m × Bool)) : f (evalW g w) = evalW (fun i => f (g i)) w := by
  induction w with
  | nil => simp [evalW]
  | cons x w ih =>
    rw [evalW_cons, evalW_cons, map_mul, ih]
    obtain ⟨i, b⟩ := x
    cases b <;> simp

theorem lift_mk_eq_evalW (g : Fin m → G) (w : List (Fin m × Bool)) :
    FreeGroup.lift g (FreeGroup.mk w) = evalW g w :=
  FreeGroup.lift_mk

theorem evalW_mul_center (g c : Fin m → G) (hc : ∀ i, c i ∈ center G)
    (w : List (Fin m × Bool)) :
    ∃ z ∈ center G, evalW (fun i => g i * c i) w = evalW g w * z := by
  induction w with
  | nil => exact ⟨1, one_mem _, by simp [evalW]⟩
  | cons x w ih =>
    obtain ⟨z, hz, hw⟩ := ih
    obtain ⟨i, b⟩ := x
    have hzc : ∀ y : G, y * z = z * y := mem_center_iff.mp hz
    have hci : ∀ y : G, y * c i = c i * y := mem_center_iff.mp (hc i)
    cases b
    · refine ⟨(c i)⁻¹ * z, mul_mem (inv_mem (hc i)) hz, ?_⟩
      rw [evalW_cons, evalW_cons, hw]
      simp only [Bool.cond_false, mul_inv_rev]
      have h1 : (c i)⁻¹ * (g i)⁻¹ = (g i)⁻¹ * (c i)⁻¹ :=
        ((mem_center_iff.mp (inv_mem (hc i))) (g i)⁻¹).symm
      calc (c i)⁻¹ * (g i)⁻¹ * (evalW g w * z) = (g i)⁻¹ * (c i)⁻¹ * (evalW g w * z) := by
            rw [h1]
        _ = (g i)⁻¹ * ((c i)⁻¹ * evalW g w) * z := by group
        _ = (g i)⁻¹ * (evalW g w * (c i)⁻¹) * z := by
            rw [← (mem_center_iff.mp (inv_mem (hc i))) (evalW g w)]
        _ = (g i)⁻¹ * evalW g w * ((c i)⁻¹ * z) := by group
    · refine ⟨c i * z, mul_mem (hc i) hz, ?_⟩
      rw [evalW_cons, evalW_cons, hw]
      simp only [Bool.cond_true]
      calc g i * c i * (evalW g w * z) = g i * (c i * evalW g w) * z := by group
        _ = g i * (evalW g w * c i) * z := by rw [hci (evalW g w)]
        _ = g i * evalW g w * (c i * z) := by group

end Words

@[expose] def gammaWords {m : ℕ} (e : Fin m → ℕ)
    (cw : Fin m → List (Fin m × Bool) × List (Fin m × Bool))
    (rels : List (List (Fin m × Bool))) : List (List (Fin m × Bool)) :=
  ((List.finRange m).map fun i =>
      if e i = 0 then commW (cw i).1 (cw i).2 ++ [(i, false)]
      else List.replicate (e i) (i, true)) ++
    rels.flatMap fun w => (List.finRange m).map fun j => commW w [(j, true)]

section Lifts

variable {X S : Type*} [Group X] [Group S] {π : X →* S}

theorem exists_mul_pow_eq_one [Finite X] (hker : π.ker ≤ center X) (hp : IsPGroup 3 π.ker)
    (x : X) {o : ℕ} (ho : π x ^ o = 1) (hco : Nat.Coprime 3 o) :
    ∃ z ∈ π.ker, (x * z) ^ o = 1 := by
  have hxo : x ^ o ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, ho]
  let w : π.ker := (hp.powEquiv hco).symm (⟨x ^ o, hxo⟩⁻¹)
  have hw : w ^ o = (⟨x ^ o, hxo⟩ : π.ker)⁻¹ := (hp.powEquiv hco).apply_symm_apply _
  refine ⟨w, w.2, ?_⟩
  have hc : Commute x (w : X) := ((mem_center_iff.mp (hker w.2)) x)
  rw [hc.mul_pow, ← coe_pow, hw]
  simp

@[expose] noncomputable def lifts [Finite X] (hπ : Function.Surjective π)
    (hker : π.ker ≤ center X) (hp : IsPGroup 3 π.ker) {m : ℕ} (h : Fin m → S) (e : Fin m → ℕ)
    (cw : Fin m → List (Fin m × Bool) × List (Fin m × Bool))
    (he : ∀ i, e i ≠ 0 → h i ^ e i = 1 ∧ Nat.Coprime 3 (e i)) (i : Fin m) : X := by
  classical
  exact if hi : e i = 0 then
      ⁅evalW (fun j => Function.surjInv hπ (h j)) (cw i).1,
        evalW (fun j => Function.surjInv hπ (h j)) (cw i).2⁆
    else Function.surjInv hπ (h i) *
      Classical.choose (exists_mul_pow_eq_one hker hp (Function.surjInv hπ (h i))
        (by rw [Function.surjInv_eq hπ]; exact (he i hi).1) (he i hi).2)

variable [Finite X] (hπ : Function.Surjective π) (hker : π.ker ≤ center X)
  (hp : IsPGroup 3 π.ker) {m : ℕ} (h : Fin m → S) (e : Fin m → ℕ)
  (cw : Fin m → List (Fin m × Bool) × List (Fin m × Bool))
  (he : ∀ i, e i ≠ 0 → h i ^ e i = 1 ∧ Nat.Coprime 3 (e i))
  (hc : ∀ i, e i = 0 → h i = ⁅evalW h (cw i).1, evalW h (cw i).2⁆)
include hc

theorem map_lifts (i : Fin m) : π (lifts hπ hker hp h e cw he i) = h i := by
  unfold lifts
  split_ifs with hi
  · rw [map_commutatorElement, map_evalW, map_evalW]
    simp only [Function.surjInv_eq hπ]
    exact (hc i hi).symm
  · have hz := (Classical.choose_spec (exists_mul_pow_eq_one hker hp (Function.surjInv hπ (h i))
      (by rw [Function.surjInv_eq hπ]; exact (he i hi).1) (he i hi).2)).1
    rw [map_mul, Function.surjInv_eq hπ, MonoidHom.mem_ker.mp hz, mul_one]

theorem lifts_eq_mul_center (i : Fin m) :
    ∃ c ∈ center X, lifts hπ hker hp h e cw he i = Function.surjInv hπ (h i) * c := by
  refine ⟨(Function.surjInv hπ (h i))⁻¹ * lifts hπ hker hp h e cw he i, hker ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_lifts hπ hker hp h e cw he hc,
    Function.surjInv_eq hπ, inv_mul_cancel]

theorem lifts_rels (rels : List (List (Fin m × Bool))) (hrels : ∀ w ∈ rels, evalW h w = 1) :
    ∀ r ∈ ({r | r ∈ (gammaWords e cw rels).map FreeGroup.mk} : Set (FreeGroup (Fin m))),
      FreeGroup.lift (lifts hπ hker hp h e cw he) r = 1 := by
  set ĥ := lifts hπ hker hp h e cw he
  set h' : Fin m → X := fun j => Function.surjInv hπ (h j)
  choose c hcz hcz' using lifts_eq_mul_center hπ hker hp h e cw he hc
  have hĥ : ĥ = fun j => h' j * c j := funext hcz'
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  rw [lift_mk_eq_evalW]
  simp only [gammaWords, List.mem_append, List.mem_map, List.mem_finRange, true_and,
    List.mem_flatMap] at hw
  rcases hw with ⟨i, rfl⟩ | ⟨ρ, hρ, j, rfl⟩
  · by_cases hi : e i = 0
    · rw [ite_eq_left hi, evalW_append, evalW_commW]
      have h1 : evalW ĥ [(i, false)] = (ĥ i)⁻¹ := by simp [evalW]
      rw [h1]
      obtain ⟨z₁, hz₁, e₁⟩ := evalW_mul_center h' c hcz (cw i).1
      obtain ⟨z₂, hz₂, e₂⟩ := evalW_mul_center h' c hcz (cw i).2
      rw [hĥ, e₁, e₂, commutatorElement_mul_center_left hz₁,
        commutatorElement_mul_center_right hz₂]
      have : ĥ i = ⁅evalW h' (cw i).1, evalW h' (cw i).2⁆ := by
        simp only [ĥ, lifts, dite_eq_left hi, h']
      rw [← hĥ, ← this, mul_inv_cancel]
    · rw [ite_eq_right hi]
      have hpow : evalW ĥ (List.replicate (e i) (i, true)) = ĥ i ^ e i := by
        induction e i with
        | zero => simp [evalW]
        | succ n ih => rw [List.replicate_succ, evalW_cons, ih, pow_succ']; rfl
      rw [hpow]
      simp only [ĥ, lifts, dite_eq_right hi]
      exact (Classical.choose_spec (exists_mul_pow_eq_one hker hp (Function.surjInv hπ (h i))
        (by rw [Function.surjInv_eq hπ]; exact (he i hi).1) (he i hi).2)).2
  · rw [evalW_commW, commutatorElement_eq_one_iff_mul_comm]
    have hρk : evalW ĥ ρ ∈ π.ker := by
      have hf : (fun i => π (ĥ i)) = h := funext (map_lifts hπ hker hp h e cw he hc)
      rw [MonoidHom.mem_ker, map_evalW, hf]
      exact hrels ρ hρ
    have h1 : evalW ĥ [(j, true)] = ĥ j := by simp [evalW]
    rw [h1]
    exact ((mem_center_iff.mp (hker hρk)) (ĥ j)).symm

end Lifts

theorem card_closure_le_of_rels {G : Type*} [Group G] {m : ℕ} (g : Fin m → G)
    (ws : List (List (Fin m × Bool))) (hws : ∀ w ∈ ws, evalW g w = 1)
    (hfin : Finite (PG m ws)) : Nat.card (closure (Set.range g)) ≤ Nat.card (PG m ws) := by
  have hrel : ∀ r ∈ ({r | r ∈ ws.map FreeGroup.mk} : Set (FreeGroup (Fin m))),
      FreeGroup.lift g r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    rw [lift_mk_eq_evalW]
    exact hws w hw
  let φ : PG m ws →* G := PresentedGroup.toGroup hrel
  have hφ : φ.range = closure (Set.range g) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← Set.range_comp]
    congr 2
    funext i
    exact PresentedGroup.toGroup.of _
  rw [← hφ]
  exact Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective

theorem card_closure_mul_card_ker_le {X S : Type*} [Group X] [Group S] [Finite X]
    [Group.IsPerfect X] {π : X →* S} (hπ : Function.Surjective π) (hker : π.ker ≤ center X)
    (hp : IsPGroup 3 π.ker) {m : ℕ} (h : Fin m → S) (e : Fin m → ℕ)
    (cw : Fin m → List (Fin m × Bool) × List (Fin m × Bool))
    (he : ∀ i, e i ≠ 0 → h i ^ e i = 1 ∧ Nat.Coprime 3 (e i))
    (hc : ∀ i, e i = 0 → h i = ⁅evalW h (cw i).1, evalW h (cw i).2⁆)
    (rels : List (List (Fin m × Bool))) (hrels : ∀ w ∈ rels, evalW h w = 1)
    (hidx : ¬ 3 ∣ (closure (Set.range h)).index)
    (hfin : Finite (PG m (gammaWords e cw rels))) :
    Nat.card (closure (Set.range h)) * Nat.card π.ker ≤
      Nat.card (PG m (gammaWords e cw rels)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ĥ := lifts hπ hker hp h e cw he
  set H := closure (Set.range h)
  set Ĥ := closure (Set.range ĥ)
  have hmap : ∀ i, π (ĥ i) = h i := map_lifts hπ hker hp h e cw he hc
  let φ : PG m (gammaWords e cw rels) →* X :=
    PresentedGroup.toGroup (lifts_rels hπ hker hp h e cw he hc rels hrels)
  have hφ : φ.range = Ĥ := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← Set.range_comp]
    congr 2
    funext i
    exact PresentedGroup.toGroup.of _
  have hcardĤ : Nat.card Ĥ ≤ Nat.card (PG m (gammaWords e cw rels)) := by
    rw [← hφ]
    exact Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
  have hmapĤ : Ĥ.map π = H := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    congr 2
    funext i
    exact hmap i
  have hkerĤ : π.ker ≤ Ĥ := by
    set H' := H.comap π
    have hidx' : ¬ 3 ∣ H'.index := by rw [H.index_comap_of_surjective hπ]; exact hidx
    obtain ⟨Q⟩ : Nonempty (Sylow 3 H') := inferInstance
    have hQp : IsPGroup 3 ((Q : Subgroup H').map H'.subtype) :=
      Q.isPGroup'.map H'.subtype
    have hQi : ¬ 3 ∣ ((Q : Subgroup H').map H'.subtype).index := by
      rw [Subgroup.index_map_subtype, Nat.Prime.dvd_mul Fact.out]
      exact not_or.mpr ⟨Q.not_dvd_index, hidx'⟩
    set P : Sylow 3 X := hQp.toSylow hQi
    have hPH' : (P : Subgroup X) ≤ H' := by
      rw [IsPGroup.toSylow_coe]
      exact Subgroup.map_subtype_le _
    refine (CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived P π.ker hker
      hp).trans ?_
    rw [map_le_iff_le_comap, _root_.commutator_def, commutator_le]
    intro a _ b _
    rw [mem_comap, map_commutatorElement, coe_subtype]
    have hdecomp : ∀ x : X, x ∈ H' → ∃ y ∈ Ĥ, ∃ z ∈ center X, x = y * z := by
      intro x hx
      have hx' : π x ∈ Ĥ.map π := by rw [hmapĤ]; exact hx
      obtain ⟨y, hy, hyx⟩ := mem_map.mp hx'
      refine ⟨y, hy, y⁻¹ * x, hker ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    obtain ⟨ya, hya, za, hza, ha⟩ := hdecomp a (hPH' a.2)
    obtain ⟨yb, hyb, zb, hzb, hb⟩ := hdecomp b (hPH' b.2)
    rw [ha, hb, commutatorElement_mul_center_left hza, commutatorElement_mul_center_right hzb,
      commutatorElement_def]
    exact Ĥ.mul_mem (Ĥ.mul_mem (Ĥ.mul_mem hya hyb) (Ĥ.inv_mem hya)) (Ĥ.inv_mem hyb)
  have hsurj : Function.Surjective (π.subgroupMap Ĥ) := π.subgroupMap_surjective Ĥ
  have hk : (π.subgroupMap Ĥ).ker = π.ker.subgroupOf Ĥ := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      exact Subtype.ext hx
  have hcard : Nat.card Ĥ = Nat.card (Ĥ.map π) * Nat.card (π.subgroupMap Ĥ).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (π.subgroupMap Ĥ).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv]
  rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerĤ).toEquiv, hmapĤ] at hcard
  rw [← hcard]
  exact hcardĤ

end CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
