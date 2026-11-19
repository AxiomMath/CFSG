module

public import CFSG.Sporadic.Recognition.JankoWongPresTables
public import CFSG.Sporadic.Recognition.JankoWongPresRelations
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open CFSG.CosetTable CFSG.Sporadic.McL

abbrev jwPresented (neg : Bool) : Type := PG 6 (jwRels neg)

theorem jwEnums_parts {neg : Bool} (h : jwEnums neg = true) :
    jwEnum6 neg = true ∧ jwEnum5 neg = true ∧ jwEnum4 neg = true := by
  simpa only [jwEnums, Bool.and_eq_true, and_assoc] using h

theorem jwChecks_parts {neg : Bool} (h : jwChecks neg = true) :
    jwEnums neg = true ∧ jwTabCheck neg = true := by
  simpa only [jwChecks, Bool.and_eq_true] using h

theorem jwPresented_card_le {neg : Bool} (h : jwEnums neg = true) :
    Finite (jwPresented neg) ∧ Nat.card (jwPresented neg) ≤ 898128000 := by
  obtain ⟨h6, h5, h4⟩ := jwEnums_parts h
  have h6' : subsetCheck (jwRels neg) [0, 1, 2, 3, 4] 200000 275 = true := h6
  have h5' : subsetCheck (jwRels5 neg) [0, 1, 2, 3] 200000 2835 = true := h5
  have h4' : subsetCheck (jwRels4 neg) [] 20000 1152 = true := h4
  obtain ⟨f1, c1⟩ := card_le_of_subsetCheck_nil (jwRels4 neg) h4'
  obtain ⟨f2, c2⟩ := card_le_of_subsetCheck (jwRels5 neg) [0, 1, 2, 3] h5'
  obtain ⟨f3, c3⟩ := card_le_of_subsetCheck (jwRels neg) [0, 1, 2, 3, 4] h6'
  refine ⟨f3, ?_⟩
  have := c3.trans <| Nat.mul_le_mul_left _ <| c2.trans <| Nat.mul_le_mul_left _ c1
  exact this.trans (by norm_num)

abbrev JWFacts (neg : Bool) : Prop :=
  (Finite (jwPresented neg) ∧ Nat.card (jwPresented neg) ≤ 898128000) ∧ jwTabCheck neg = true

section Model


noncomputable def jwPhi (neg : Bool) (h : jwTabCheck neg = true) : jwPresented neg →* J :=
  PresentedGroup.toGroup (f := jwGen neg) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact lift_jwGen_eq_one neg h hw

theorem jwPhi_of (neg : Bool) (h : jwTabCheck neg = true) (i : Fin 6) :
    jwPhi neg h (PresentedGroup.of i) = jwGen neg i :=
  PresentedGroup.toGroup.of _

theorem jwPhi_mk (neg : Bool) (h : jwTabCheck neg = true) (w : FreeGroup (Fin 6)) :
    jwPhi neg h (PresentedGroup.mk _ w) = FreeGroup.lift (jwGen neg) w := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of i => rw [FreeGroup.lift_apply_of]; exact jwPhi_of neg h i
  | inv_of i hi => simp only [map_inv, hi]
  | mul x y hx hy => simp only [map_mul, hx, hy]

theorem jwPhi_surjective (neg : Bool) (h : jwTabCheck neg = true) :
    Function.Surjective (jwPhi neg h) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_jwGen neg h, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, jwPhi_of neg h i⟩

theorem jwPhi_bijective {neg : Bool} (h : JWFacts neg) :
    Function.Bijective (jwPhi neg h.2) := by
  obtain ⟨hfin, hcard⟩ := h.1
  have := hfin
  refine (jwPhi_surjective neg _).bijective_of_nat_card_le ?_
  rw [card_J]
  exact hcard

noncomputable def jwPresentedEquivJ {neg : Bool} (h : JWFacts neg) :
    jwPresented neg ≃* J :=
  MulEquiv.ofBijective _ (jwPhi_bijective h)

noncomputable def jwPresentedEquivMcL {neg : Bool} (h : JWFacts neg) :
    jwPresented neg ≃* CFSG.Blueprint.NativeSporadic.McL :=
  (jwPresentedEquivJ h).trans mclEquivJ.symm

theorem isSimpleGroup_jwPresented {neg : Bool} (h : JWFacts neg) :
    IsSimpleGroup (jwPresented neg) := by
  exact @MulEquiv.isSimpleGroup (jwPresented neg) _ J _ isSimpleGroup_J (jwPresentedEquivJ h)

noncomputable def jwModel (neg : Bool) : JWElements J :=
  ⟨jwGen neg 0, jwGen neg 1, jwGen neg 2, jwGen neg 3, jwGen neg 5, jwGen neg 4⟩

theorem jwModel_gen (neg : Bool) : (jwModel neg).gen = jwGen neg := by
  funext i
  fin_cases i <;> rfl

theorem jwModel_relations (neg : Bool) (h : jwTabCheck neg = true) :
    JWRelations (if neg then -1 else 1) (jwModel neg) := by
  refine JWRelations.of_pairs fun p hp => ?_
  have hneg : decide ((if neg then -1 else 1 : ℤˣ) = -1) = neg := by cases neg <;> decide
  rw [hneg] at hp
  have h1 := lift_jwGen_eq_one neg h (w := p.1 ++ jwWInv p.2)
    (List.mem_map_of_mem (f := fun p : JWWord × JWWord => p.1 ++ jwWInv p.2) hp)
  rw [← jwModel_gen, JWElements.lift_mk, JWElements.eval_append, JWElements.eval_inv,
    mul_inv_eq_one] at h1
  exact h1

end Model

theorem lift_gen_rels {G : Type*} [Group G] (neg : Bool) (e : JWElements G)
    (hp : ∀ p ∈ jwPairs neg, e.eval p.1 = e.eval p.2) :
    ∀ r ∈ {r : FreeGroup (Fin 6) | r ∈ (jwRels neg).map FreeGroup.mk},
      FreeGroup.lift e.gen r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 hw
  rw [JWElements.lift_mk, JWElements.eval_append, JWElements.eval_inv, hp p hpm, mul_inv_cancel]

section Recognition


theorem exists_mulEquiv_mcl_of_pairs {G : Type*} [Group G] {neg : Bool} (e : JWElements G)
    (h : JWFacts neg) (hp : ∀ p ∈ jwPairs neg, e.eval p.1 = e.eval p.2)
    (hK : Subgroup.closure e.gens ≠ ⊥) :
    Nonempty (Subgroup.closure e.gens ≃* CFSG.Blueprint.NativeSporadic.McL) := by
  have hsimple := isSimpleGroup_jwPresented h
  let ψ : jwPresented neg →* G := PresentedGroup.toGroup (lift_gen_rels neg e hp)
  have hrange : ψ.range = Subgroup.closure e.gens := by
    have hcomp : (ψ ∘ PresentedGroup.of) = e.gen := funext fun i => PresentedGroup.toGroup.of _
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← e.range_gen, ← Set.range_comp, hcomp]
  have hker : ψ.ker = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal ψ.ker with h0 | h0
    · exact h0
    · exfalso
      apply hK
      rw [← hrange, MonoidHom.range_eq_bot_iff]
      exact MonoidHom.ker_eq_top_iff.1 h0
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hker
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans
    (jwPresentedEquivMcL h)⟩

theorem lift_eq_one_of_pairs {G : Type*} [Group G] {neg : Bool} (e : JWElements G)
    (h : JWFacts neg) (hp : ∀ p ∈ jwPairs neg, e.eval p.1 = e.eval p.2)
    {w : FreeGroup (Fin 6)} (hw : FreeGroup.lift (jwGen neg) w = 1) :
    FreeGroup.lift e.gen w = 1 := by
  have h1 : PresentedGroup.mk _ w = (1 : jwPresented neg) :=
    (jwPhi_bijective h).1 (by rw [jwPhi_mk, hw, map_one])
  have h2 := congrArg (PresentedGroup.toGroup (lift_gen_rels neg e hp)) h1
  rw [map_one] at h2
  exact h2

theorem exists_mulEquiv_mcl_of_relations {G : Type*} [Group G] {ι : ℤˣ} {e : JWElements G}
    (hrel : JWRelations ι e) (hc : JWFacts false ∧ JWFacts true)
    (hK : Subgroup.closure e.gens ≠ ⊥) :
    Nonempty (Subgroup.closure e.gens ≃* CFSG.Blueprint.NativeSporadic.McL) := by
  refine exists_mulEquiv_mcl_of_pairs e ?_ hrel.eval_pairs hK
  rcases Int.units_eq_one_or ι with rfl | rfl
  · have : decide ((1 : ℤˣ) = -1) = false := by decide
    rw [this]; exact hc.1
  · have : decide ((-1 : ℤˣ) = -1) = true := by decide
    rw [this]; exact hc.2

theorem lift_eq_one_of_relations {G : Type*} [Group G] {ι : ℤˣ} {e : JWElements G}
    (hrel : JWRelations ι e) (hc : JWFacts false ∧ JWFacts true)
    {w : FreeGroup (Fin 6)} (hw : FreeGroup.lift (jwGen (decide (ι = -1))) w = 1) :
    FreeGroup.lift e.gen w = 1 := by
  refine lift_eq_one_of_pairs e ?_ hrel.eval_pairs hw
  rcases Int.units_eq_one_or ι with rfl | rfl
  · have : decide ((1 : ℤˣ) = -1) = false := by decide
    rw [this]; exact hc.1
  · have : decide ((-1 : ℤˣ) = -1) = true := by decide
    rw [this]; exact hc.2

end Recognition

end CFSG.Sporadic.Recognition.JankoWong
