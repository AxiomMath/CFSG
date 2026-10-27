module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Model
public import CFSG.Quasithin.Vol2.Ch10SecEA5b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

@[expose] def eFour : Finset (Perm (Fin 5)) := {1, sA, sB, sA * sB}

theorem eFour_mem_iff (g : Perm (Fin 5)) : g ∈ eFour ↔ g = 1 ∨ g = sA ∨ g = sB ∨ g = sA * sB := by
  simp [eFour]

section Model

variable {Y : Subgroup (Perm (Fin 5))}

open Classical in
theorem card_eq_selCard (hY : ∀ g ∈ Y, g ∈ eFour) :
    Nat.card Y = selCard (decide (sA ∈ Y)) (decide (sB ∈ Y)) (decide (sA * sB ∈ Y)) := by
  have e : (Y : Set (Perm (Fin 5))) = ↑(eFour.filter (· ∈ Y)) := by
    ext g
    simp only [SetLike.mem_coe, Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨hY g h, h⟩, fun h => h.2⟩
  rw [← SetLike.coe_sort_coe, e, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have h1 : (1 : Perm (Fin 5)) ∈ Y := Y.one_mem
  have hd : ((({1, sA, sB, sA * sB} : Finset (Perm (Fin 5))).filter (· ∈ Y)).card =
      1 + (decide (sA ∈ Y)).toNat + (decide (sB ∈ Y)).toNat + (decide (sA * sB ∈ Y)).toNat) := by
    have hne : (1 : Perm (Fin 5)) ≠ sA ∧ (1 : Perm (Fin 5)) ≠ sB ∧
        (1 : Perm (Fin 5)) ≠ sA * sB ∧ sA ≠ sB ∧ sA ≠ sA * sB ∧ sB ≠ sA * sB := by decide
    obtain ⟨h12, h13, h14, h23, h24, h34⟩ := hne
    by_cases ha : sA ∈ Y <;> by_cases hb : sB ∈ Y <;> by_cases hc : sA * sB ∈ Y <;>
      simp [Finset.filter_insert, Finset.filter_singleton, ha, hb, hc, h1, h12, h13, h14, h23,
        h24, h34]
  exact hd

open Classical in
theorem card_fix_eq_fixCount (hY : ∀ g ∈ Y, g ∈ eFour) :
    (Finset.univ.filter fun x : Fin 5 → ZMod 2 => isEven x ∧ ∀ σ ∈ Y, pact σ x = x).card =
      fixCount (decide (sA ∈ Y)) (decide (sB ∈ Y)) (decide (sA * sB ∈ Y)) := by
  unfold fixCount
  congr 1
  apply Finset.filter_congr
  intro x _
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨he, hf⟩
    exact ⟨he, fun h => hf _ h, fun h => hf _ h, fun h => hf _ h⟩
  · rintro ⟨he, ha, hb, hc⟩
    refine ⟨he, fun σ hσ => ?_⟩
    rcases (eFour_mem_iff σ).mp (hY σ hσ) with rfl | rfl | rfl | rfl
    · funext i; simp [pact]
    · exact ha hσ
    · exact hb hσ
    · exact hc hσ

open Classical in
theorem selClosed_of_subgroup (Y : Subgroup (Perm (Fin 5))) :
    SelClosed (decide (sA ∈ Y)) (decide (sB ∈ Y)) (decide (sA * sB ∈ Y)) := by
  have hAA : sA * sA = 1 := by decide
  have hBB : sB * sB = 1 := by decide
  simp only [SelClosed, decide_eq_true_eq]
  refine ⟨fun ha hb => Y.mul_mem ha hb, fun ha hc => ?_, fun hb hc => ?_⟩
  · have h := Y.mul_mem ha hc
    rwa [← mul_assoc, hAA, one_mul] at h
  · have h := Y.mul_mem hc hb
    rwa [mul_assoc, hBB, mul_one] at h

end Model

variable {W : Type*} [CommGroup W] {K : Subgroup (MulAut W)} {θ : ↥K ≃* Perm (Fin 5)}
  {β : ↥(commV K) ≃* Multiplicative (evenWeight 5)}

open Classical in
theorem card_fixV_inf_commV
    (hβ : ∀ (h : ↥K) (u : ↥(commV K)) (hu : (h : MulAut W) (u : W) ∈ commV K) (i : Fin 5),
      ((Multiplicative.toAdd (β ⟨(h : MulAut W) u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) ((θ h)⁻¹ i))
    {Y : Subgroup (MulAut W)} (hYK : Y ≤ K) :
    Nat.card ↥(fixV Y ⊓ commV K) =
      (Finset.univ.filter fun x : Fin 5 → ZMod 2 =>
        isEven x ∧ ∀ σ ∈ (Y.subgroupOf K).map θ.toMonoidHom, pact σ x = x).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun w => ⟨((Multiplicative.toAdd (β ⟨w, w.2.2⟩) : evenWeight 5) : Fin 5 → ZMod 2),
        (Multiplicative.toAdd (β ⟨w, w.2.2⟩)).2, ?_⟩
      invFun := fun x => ⟨(β.symm (Multiplicative.ofAdd ⟨x.1, x.2.1⟩) : W), ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro σ ⟨⟨y, hyK⟩, hyY, rfl⟩
    have h1 := coord_apply θ β hβ ⟨y, hyK⟩ ⟨w, w.2.2⟩
    have hw : (y : MulAut W) (w : W) = w := w.2.1 y (Subgroup.mem_subgroupOf.mp hyY)
    have e : (⟨((⟨y, hyK⟩ : ↥K) : MulAut W) (w : W), commV_invariant K _ hyK _ w.2.2⟩ :
        ↥(commV K)) = ⟨w, w.2.2⟩ := Subtype.ext hw
    rw [e] at h1
    exact h1.symm
  · intro y hy
    obtain ⟨x, hx, hfx⟩ := x
    set u : ↥(commV K) := β.symm (Multiplicative.ofAdd ⟨x, hx⟩)
    have h1 := coord_apply θ β hβ ⟨y, hYK hy⟩ u
    have h2 : pact (θ ⟨y, hYK hy⟩) x = x :=
      hfx _ ⟨⟨y, hYK hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    have hu : ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) = x := by simp [u]
    rw [hu, h2, ← hu] at h1
    have h3 := β.injective (Multiplicative.toAdd.injective (Subtype.ext h1))
    exact congrArg Subtype.val h3
  · exact (β.symm _).2
  · intro w
    apply Subtype.ext
    have e : (⟨((Multiplicative.toAdd (β ⟨w, w.2.2⟩) : evenWeight 5) : Fin 5 → ZMod 2),
        (Multiplicative.toAdd (β ⟨w, w.2.2⟩)).2⟩ : evenWeight 5) =
        Multiplicative.toAdd (β ⟨w, w.2.2⟩) := Subtype.ext rfl
    show ((β.symm (Multiplicative.ofAdd _) : ↥(commV K)) : W) = w
    rw [e, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  · intro x
    apply Subtype.ext
    simp

open Classical in
theorem factor_bound
    (hβ : ∀ (h : ↥K) (u : ↥(commV K)) (hu : (h : MulAut W) (u : W) ∈ commV K) (i : Fin 5),
      ((Multiplicative.toAdd (β ⟨(h : MulAut W) u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) ((θ h)⁻¹ i))
    {P : Subgroup (MulAut W)} (hPK : P ≤ K) (hP : ∀ g (hg : g ∈ K), g ∈ P ↔ θ ⟨g, hg⟩ ∈ eFour)
    {Y : Subgroup (MulAut W)} (hYP : Y ≤ P) :
    Nat.card Y * Nat.card ↥(fixV Y ⊓ commV K) ≤ 16 ∧
      (Nat.card Y * Nat.card ↥(fixV Y ⊓ commV K) = 16 ↔
        ((θ.symm (sA * sB) : MulAut W) ∈ Y → (θ.symm sA : MulAut W) ∈ Y)) := by
  set Y' := (Y.subgroupOf K).map θ.toMonoidHom with hY'
  have hYK : Y ≤ K := hYP.trans hPK
  have hY'E : ∀ g ∈ Y', g ∈ eFour := by
    rintro g ⟨⟨y, hyK⟩, hyY, rfl⟩
    exact (hP y hyK).mp (hYP (Subgroup.mem_subgroupOf.mp hyY))
  have hmem : ∀ σ : Perm (Fin 5), σ ∈ Y' ↔ (θ.symm σ : MulAut W) ∈ Y := by
    intro σ
    constructor
    · rintro ⟨⟨y, hyK⟩, hyY, rfl⟩
      simpa using Subgroup.mem_subgroupOf.mp hyY
    · intro h
      exact ⟨θ.symm σ, Subgroup.mem_subgroupOf.mpr h, by simp⟩
  have hcard : Nat.card Y = Nat.card Y' := by
    rw [hY']
    refine (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv).symm.trans ?_
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ θ.injective).toEquiv
  rw [hcard, card_fixV_inf_commV hβ hYK, card_fix_eq_fixCount hY'E, card_eq_selCard hY'E]
  refine ⟨card_mul_fixCount_le _ _ _ (selClosed_of_subgroup Y'), ?_⟩
  rw [card_mul_fixCount_eq_iff _ _ _ (selClosed_of_subgroup Y')]
  simp only [decide_eq_true_eq, hmem]

omit [CommGroup W] in
theorem card_evenWeight_five : Nat.card ↥(evenWeight 5) = 16 := by
  classical
  have e : ↥(evenWeight 5) ≃ {x : Fin 5 → ZMod 2 // isEven x} :=
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_evenWeight

theorem card_commV_of_isA5Module (β : ↥(commV K) ≃* Multiplicative (evenWeight 5)) :
    Nat.card ↥(commV K) = 16 := by
  rw [Nat.card_congr β.toEquiv]
  exact (Nat.card_congr Multiplicative.toAdd).trans card_evenWeight_five

end CFSG.Quasithin.Vol2.Ch10.SecE
