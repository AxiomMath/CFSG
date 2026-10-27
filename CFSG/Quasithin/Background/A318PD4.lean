module

public import CFSG.Quasithin.Background.A318PRW
public import CFSG.Quasithin.Background.A318PCRank
public import CFSG.Quasithin.Background.A318PInn
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersParabolic
public import CFSG.RankThree.PartTwo.KFacts.AutTriality
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank
  CFSG.LieType.Chevalley CFSG.LieType.Ree.LargeReeInvolution

section Membership

variable {τ : Tag} {n : ℕ}
  (W : RootWitness τ n) {K : Type} [Field K]

theorem pos_of_check
    (hW : W.check = true) (i : Fin n) : 0 < height (W.root i).1 := by
  simp only [RootWitness.check, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hW
  rw [RootWitness.root_val]
  exact (hW i).1.1.1

theorem elemA_mem_posUnipotent
    [Finite K] (hW : W.check = true) (i : Fin n) :
    ((W.elemA K i : adjointGroup τ K) : ModGL τ K) ∈ posUnipotent τ K := by
  have hx := W.elemA_mem K i
  have h1 : W.elemA K i ∈ (nativeData τ K).U :=
    RootGroupData.X_le_U (D := nativeData τ K) (pos_of_check W hW i) hx
  rw [← map_nativeU_eq_posUnipotent]
  exact Subgroup.mem_map_of_mem _ h1

theorem elemB_mem_negUnipotent
    (hW : W.check = true) (i : Fin n) :
    ((W.elemB K i : adjointGroup τ K) : ModGL τ K) ∈ negUnipotent τ K := by
  have hx := W.elemB_mem K i
  have hneg : height (-W.root i : Root τ).1 < 0 := by
    rw [coe_neg_root, height_neg]
    exact neg_neg_of_pos (pos_of_check W hW i)
  have h1 : W.elemB K i ∈ ⨆ (α : Root τ) (_ : height α.1 < 0), (nativeRootSubgroups τ K).X α :=
    (le_iSup₂ (f := fun (α : Root τ) (_ : height α.1 < 0) => (nativeRootSubgroups τ K).X α)
      (-W.root i) hneg) hx
  have h2 := map_iSup_nativeRootSubgroups (τ := τ) (K := K) (fun α => height α.1 < 0)
  have h3 : ((W.elemB K i : adjointGroup τ K) : ModGL τ K) ∈ rootSpan τ K
      {β | ∃ h : IsRoot τ β, height β < 0} := by
    rw [← h2]
    exact Subgroup.mem_map_of_mem _ h1
  refine (show rootSpan τ K {β | ∃ h : IsRoot τ β, height β < 0} ≤ negUnipotent τ K from ?_) h3
  refine iSup₂_le fun β hβ => ?_
  exact le_iSup₂ (f := fun β (_ : β ∈ {α | IsRoot τ α ∧ height α < 0}) => rootSubgroup τ K β) β
    ⟨hβ.1, hβ.2⟩

end Membership

section D4Elements

@[expose] def witnessD4 : RootWitness TwistTag.D4.tag 4 where
  word := ![([] : List (Fin 4)), ([] : List (Fin 4)), ([] : List (Fin 4)),
    ([2, 0, 1, 3] : List (Fin 4))]
  simple := ![(0 : Fin 4), (1 : Fin 4), (3 : Fin 4), (2 : Fin 4)]

abbrev d4W : List (Fin TwistTag.D4.tag.rank) := ([2, 0, 1, 3] : List (Fin 4))

abbrev d4k2 : Fin TwistTag.D4.tag.rank := (2 : Fin 4)

theorem witnessD4_check : witnessD4.check = true := by decide +kernel

theorem witnessD4_orthoCheck : witnessD4.orthoCheck = true := by decide +kernel

theorem d4_cartan_nbr : ∀ i : Fin 4,
    TwistTag.D4.tag.cartan (witnessD4.simple i) (![(2 : Fin 4), 2, 2, 0] i) = -1 := by
  decide

variable {K : Type} [Field K]

theorem d4_facts
    [CharP K 2] :
    (∀ i, witnessD4.elemZ K i ^ 3 = 1 ∧ ¬ Commute (witnessD4.elemZ K i) (witnessD4.elemA K i) ∧
      ¬ Commute (witnessD4.elemZ K i ^ 2) (witnessD4.elemA K i)) ∧
    (∀ i j, i ≠ j → Commute (witnessD4.elemZ K j) (witnessD4.elemA K i)) ∧
    (∀ i j, i ≠ j → Commute (witnessD4.elemZ K i) (witnessD4.elemZ K j)) ∧
    (∀ i j, i ≠ j → Commute (witnessD4.elemA K i) (witnessD4.elemA K j) ∧
      Commute (witnessD4.elemB K i) (witnessD4.elemB K j) ∧
      Commute (witnessD4.elemA K i) (witnessD4.elemB K j)) := by
  have h2 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact CharP.cast_eq_zero K 2
  exact charTwo_facts_of_rankOne witnessD4 witnessD4_check witnessD4_orthoCheck
    (fun i => rankOneZ_facts (d4_cartan_nbr i) h2)

omit [Field K] in
theorem elemA_zero_word
    {τ : Tag} {m : ℕ} (W : RootWitness τ m) [Field K] (i : Fin m)
    (h : W.word i = []) : W.elemA K i = xElement (W.simple i) 1 := by
  simp only [RootWitness.elemA, h, CoxeterSystem.wordProd_nil, nrep_one, one_mul, inv_one,
    mul_one, eltElement_simpleRoot]

theorem elemB_zero_word
    {τ : Tag} {m : ℕ} (W : RootWitness τ m) (i : Fin m)
    (h : W.word i = []) : W.elemB K i = yElement (W.simple i) 1 := by
  have : (rootOperatorFamily τ).eltElement (-simpleRoot τ (W.simple i)) (1 : K) =
      yElement (W.simple i) 1 := Subtype.ext ((rootOperatorFamily τ).eltUnit_neg_simple _ _)
  simp only [RootWitness.elemB, h, CoxeterSystem.wordProd_nil, nrep_one, one_mul, inv_one,
    mul_one, this]

end D4Elements

section D4Twist

variable {K : Type} [Field K] (σ : K →+* K)

theorem weylTwist_d4_w
    :
    weylTwist TwistTag.D4 ((coxeterSystem TwistTag.D4.tag).wordProd d4W) =
      (coxeterSystem TwistTag.D4.tag).wordProd d4W :=
  weylTwist_wordProd_eq (ω := d4W) (by decide +kernel)

theorem twistC_nrep_d4_w
    :
    twistC TwistTag.D4 K σ
        (nrep TwistTag.D4.tag K ((coxeterSystem TwistTag.D4.tag).wordProd d4W)) =
      nrep TwistTag.D4.tag K ((coxeterSystem TwistTag.D4.tag).wordProd d4W) := by
  rw [twistC_nrep, weylTwist_d4_w]

theorem twistC_elemA_zero
    : twistC TwistTag.D4 K σ (witnessD4.elemA K 0) = witnessD4.elemA K 1 := by
  rw [elemA_zero_word witnessD4 0 rfl, elemA_zero_word witnessD4 1 rfl, twistC_xElement, map_one]
  have : TwistTag.D4.perm (witnessD4.simple 0) = witnessD4.simple 1 := by decide
  rw [this]

theorem twistC_elemA_one
    : twistC TwistTag.D4 K σ (witnessD4.elemA K 1) = witnessD4.elemA K 2 := by
  rw [elemA_zero_word witnessD4 1 rfl, elemA_zero_word witnessD4 2 rfl, twistC_xElement, map_one]
  have : TwistTag.D4.perm (witnessD4.simple 1) = witnessD4.simple 2 := by decide
  rw [this]

theorem twistC_elemA_two
    : twistC TwistTag.D4 K σ (witnessD4.elemA K 2) = witnessD4.elemA K 0 := by
  rw [elemA_zero_word witnessD4 2 rfl, elemA_zero_word witnessD4 0 rfl, twistC_xElement, map_one]
  have : TwistTag.D4.perm (witnessD4.simple 2) = witnessD4.simple 0 := by decide
  rw [this]

theorem twistC_elemB_zero
    : twistC TwistTag.D4 K σ (witnessD4.elemB K 0) = witnessD4.elemB K 1 := by
  rw [elemB_zero_word witnessD4 0 rfl, elemB_zero_word witnessD4 1 rfl, twistC_yElement, map_one]
  have : TwistTag.D4.perm (witnessD4.simple 0) = witnessD4.simple 1 := by decide
  rw [this]

theorem twistC_elemB_one
    : twistC TwistTag.D4 K σ (witnessD4.elemB K 1) = witnessD4.elemB K 2 := by
  rw [elemB_zero_word witnessD4 1 rfl, elemB_zero_word witnessD4 2 rfl, twistC_yElement, map_one]
  have : TwistTag.D4.perm (witnessD4.simple 1) = witnessD4.simple 2 := by decide
  rw [this]

theorem twistC_elemB_two
    : twistC TwistTag.D4 K σ (witnessD4.elemB K 2) = witnessD4.elemB K 0 := by
  rw [elemB_zero_word witnessD4 2 rfl, elemB_zero_word witnessD4 0 rfl, twistC_yElement, map_one]
  have : TwistTag.D4.perm (witnessD4.simple 2) = witnessD4.simple 0 := by decide
  rw [this]

theorem twistC_elemA_three
    : twistC TwistTag.D4 K σ (witnessD4.elemA K 3) = witnessD4.elemA K 3 := by
  have hw : witnessD4.word 3 = d4W := rfl
  have hs : witnessD4.simple 3 = d4k2 := rfl
  have hp : TwistTag.D4.perm d4k2 = d4k2 := by decide
  simp only [RootWitness.elemA, hw, hs, eltElement_simpleRoot, map_mul, map_inv,
    twistC_nrep_d4_w, twistC_xElement, map_one, hp]

theorem twistC_elemB_three
    : twistC TwistTag.D4 K σ (witnessD4.elemB K 3) = witnessD4.elemB K 3 := by
  have hw : witnessD4.word 3 = d4W := rfl
  have hs : witnessD4.simple 3 = d4k2 := rfl
  have hp : TwistTag.D4.perm d4k2 = d4k2 := by decide
  have : (rootOperatorFamily TwistTag.D4.tag).eltElement
      (-simpleRoot TwistTag.D4.tag d4k2) (1 : K) = yElement d4k2 1 :=
    Subtype.ext ((rootOperatorFamily TwistTag.D4.tag).eltUnit_neg_simple _ _)
  simp only [RootWitness.elemB, hw, hs, this, map_mul, map_inv, twistC_nrep_d4_w,
    twistC_yElement, map_one, hp]

end D4Twist

section D4Fixed

variable {K : Type} [Field K]

theorem units_map_elemA
    (δ : K ≃+* K) {τ : Tag} {m : ℕ} (W : RootWitness τ m) (i : Fin m) :
    Units.map (entrywiseHom δ.toRingHom) ((W.elemA K i : adjointGroup τ K) : ModGL τ K) =
      (W.elemA K i : ModGL τ K) := by
  have hN : Units.map (entrywiseHom δ.toRingHom)
      ((nrep τ K ((coxeterSystem τ).wordProd (W.word i)) : adjointGroup τ K) : ModGL τ K) =
      ((nrep τ K ((coxeterSystem τ).wordProd (W.word i)) : adjointGroup τ K) : ModGL τ K) :=
    entrywise_canonicalRep δ _
  have hX : Units.map (entrywiseHom δ.toRingHom)
      (((rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1 : adjointGroup τ K) :
        ModGL τ K) =
      (((rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1 : adjointGroup τ K) :
        ModGL τ K) := by
    rw [eltElement_simpleRoot]
    exact (units_map_entrywiseHom_xUnit δ.toRingHom (W.simple i) 1).trans (by rw [map_one]; rfl)
  simp only [RootWitness.elemA, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hN, hX]

theorem units_map_elemB
    (δ : K ≃+* K) {τ : Tag} {m : ℕ} (W : RootWitness τ m) (i : Fin m) :
    Units.map (entrywiseHom δ.toRingHom) ((W.elemB K i : adjointGroup τ K) : ModGL τ K) =
      (W.elemB K i : ModGL τ K) := by
  have hN : Units.map (entrywiseHom δ.toRingHom)
      ((nrep τ K ((coxeterSystem τ).wordProd (W.word i)) : adjointGroup τ K) : ModGL τ K) =
      ((nrep τ K ((coxeterSystem τ).wordProd (W.word i)) : adjointGroup τ K) : ModGL τ K) :=
    entrywise_canonicalRep δ _
  have hY : Units.map (entrywiseHom δ.toRingHom)
      (((rootOperatorFamily τ).eltElement (-simpleRoot τ (W.simple i)) 1 : adjointGroup τ K) :
        ModGL τ K) =
      (((rootOperatorFamily τ).eltElement (-simpleRoot τ (W.simple i)) 1 : adjointGroup τ K) :
        ModGL τ K) := by
    have : (rootOperatorFamily τ).eltElement (-simpleRoot τ (W.simple i)) (1 : K) =
        yElement (W.simple i) 1 := Subtype.ext ((rootOperatorFamily τ).eltUnit_neg_simple _ _)
    rw [this]
    exact (units_map_entrywiseHom_yUnit δ.toRingHom (W.simple i) 1).trans (by rw [map_one]; rfl)
  simp only [RootWitness.elemB, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hN, hY]

theorem units_map_elemZ
    (δ : K ≃+* K) {τ : Tag} {m : ℕ} (W : RootWitness τ m) (i : Fin m) :
    Units.map (entrywiseHom δ.toRingHom) ((W.elemZ K i : adjointGroup τ K) : ModGL τ K) =
      (W.elemZ K i : ModGL τ K) := by
  rw [RootWitness.elemZ_eq, Subgroup.coe_mul, map_mul, units_map_elemA, units_map_elemB]

variable (σ : K →+* K)

theorem mem_graphFixedPos
    {g : adjointGroup TwistTag.D4.tag K}
    (hg : (g : ModGL TwistTag.D4.tag K) ∈ posUnipotent TwistTag.D4.tag K)
    (hF : twistC TwistTag.D4 K σ g = g) :
    (g : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K σ :=
  ⟨hg, g.2, by
    change twistHom TwistTag.D4 K σ (g : ModGL TwistTag.D4.tag K) = (g : ModGL TwistTag.D4.tag K)
    rw [← coe_twistC, hF]⟩

theorem mem_graphFixedNeg
    {g : adjointGroup TwistTag.D4.tag K}
    (hg : (g : ModGL TwistTag.D4.tag K) ∈ negUnipotent TwistTag.D4.tag K)
    (hF : twistC TwistTag.D4 K σ g = g) :
    (g : ModGL TwistTag.D4.tag K) ∈ graphFixedNegUnipotent TwistTag.D4 K σ :=
  ⟨hg, g.2, by
    change twistHom TwistTag.D4 K σ (g : ModGL TwistTag.D4.tag K) = (g : ModGL TwistTag.D4.tag K)
    rw [← coe_twistC, hF]⟩

end D4Fixed

section D4Nine

theorem isElemAbelian_subgroupOf {G : Type*} [Group G] {p : ℕ} {E H : Subgroup G}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.subgroupOf H) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE H

end D4Nine

section D4Member

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K →+* K)

omit [Finite K] in
theorem d4_ZZ0_eq
    :
    witnessD4.elemZ K 0 * witnessD4.elemZ K 1 * witnessD4.elemZ K 2 =
      (witnessD4.elemA K 0 * witnessD4.elemA K 1 * witnessD4.elemA K 2) *
        (witnessD4.elemB K 0 * witnessD4.elemB K 1 * witnessD4.elemB K 2) := by
  obtain ⟨-, -, -, hAB⟩ := d4_facts (K := K)
  have e1 : witnessD4.elemB K 0 * witnessD4.elemA K 1 = witnessD4.elemA K 1 * witnessD4.elemB K 0 :=
    ((hAB 1 0 (by decide)).2.2.eq).symm
  have e2 : witnessD4.elemB K 0 * witnessD4.elemA K 2 = witnessD4.elemA K 2 * witnessD4.elemB K 0 :=
    ((hAB 2 0 (by decide)).2.2.eq).symm
  have e3 : witnessD4.elemB K 1 * witnessD4.elemA K 2 = witnessD4.elemA K 2 * witnessD4.elemB K 1 :=
    ((hAB 2 1 (by decide)).2.2.eq).symm
  simp only [RootWitness.elemZ_eq]
  calc _ = witnessD4.elemA K 0 * (witnessD4.elemB K 0 * witnessD4.elemA K 1) *
        (witnessD4.elemB K 1 * witnessD4.elemA K 2) * witnessD4.elemB K 2 := by
        simp only [mul_assoc]
    _ = witnessD4.elemA K 0 * (witnessD4.elemA K 1 * witnessD4.elemB K 0) *
        (witnessD4.elemA K 2 * witnessD4.elemB K 1) * witnessD4.elemB K 2 := by rw [e1, e3]
    _ = witnessD4.elemA K 0 * witnessD4.elemA K 1 * (witnessD4.elemB K 0 * witnessD4.elemA K 2) *
        witnessD4.elemB K 1 * witnessD4.elemB K 2 := by simp only [mul_assoc]
    _ = witnessD4.elemA K 0 * witnessD4.elemA K 1 * (witnessD4.elemA K 2 * witnessD4.elemB K 0) *
        witnessD4.elemB K 1 * witnessD4.elemB K 2 := by rw [e2]
    _ = _ := by simp only [mul_assoc]

theorem d4_ZZ0_mem
    :
    ((witnessD4.elemZ K 0 * witnessD4.elemZ K 1 * witnessD4.elemZ K 2 :
      adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) ∈
        graphFixedRootGroup TwistTag.D4 K σ := by
  obtain ⟨-, -, -, hAB⟩ := d4_facts (K := K)
  rw [d4_ZZ0_eq, Subgroup.coe_mul]
  have hAF : twistC TwistTag.D4 K σ
      (witnessD4.elemA K 0 * witnessD4.elemA K 1 * witnessD4.elemA K 2) =
      witnessD4.elemA K 0 * witnessD4.elemA K 1 * witnessD4.elemA K 2 := by
    rw [map_mul, map_mul, twistC_elemA_zero, twistC_elemA_one, twistC_elemA_two]
    have c01 := (hAB 0 1 (by decide)).1.eq
    have c02 := (hAB 0 2 (by decide)).1.eq
    calc witnessD4.elemA K 1 * witnessD4.elemA K 2 * witnessD4.elemA K 0
        = witnessD4.elemA K 1 * (witnessD4.elemA K 2 * witnessD4.elemA K 0) := by rw [mul_assoc]
      _ = witnessD4.elemA K 1 * (witnessD4.elemA K 0 * witnessD4.elemA K 2) := by rw [← c02]
      _ = (witnessD4.elemA K 1 * witnessD4.elemA K 0) * witnessD4.elemA K 2 := by rw [mul_assoc]
      _ = _ := by rw [← c01]
  have hBF : twistC TwistTag.D4 K σ
      (witnessD4.elemB K 0 * witnessD4.elemB K 1 * witnessD4.elemB K 2) =
      witnessD4.elemB K 0 * witnessD4.elemB K 1 * witnessD4.elemB K 2 := by
    rw [map_mul, map_mul, twistC_elemB_zero, twistC_elemB_one, twistC_elemB_two]
    have c01 := (hAB 0 1 (by decide)).2.1.eq
    have c02 := (hAB 0 2 (by decide)).2.1.eq
    calc witnessD4.elemB K 1 * witnessD4.elemB K 2 * witnessD4.elemB K 0
        = witnessD4.elemB K 1 * (witnessD4.elemB K 2 * witnessD4.elemB K 0) := by rw [mul_assoc]
      _ = witnessD4.elemB K 1 * (witnessD4.elemB K 0 * witnessD4.elemB K 2) := by rw [← c02]
      _ = (witnessD4.elemB K 1 * witnessD4.elemB K 0) * witnessD4.elemB K 2 := by rw [mul_assoc]
      _ = _ := by rw [← c01]
  refine Subgroup.mul_mem_sup (mem_graphFixedPos σ ?_ hAF) (mem_graphFixedNeg σ ?_ hBF)
  · rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact mul_mem (mul_mem (elemA_mem_posUnipotent witnessD4 witnessD4_check 0)
      (elemA_mem_posUnipotent witnessD4 witnessD4_check 1))
      (elemA_mem_posUnipotent witnessD4 witnessD4_check 2)
  · rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact mul_mem (mul_mem (elemB_mem_negUnipotent witnessD4 witnessD4_check 0)
      (elemB_mem_negUnipotent witnessD4 witnessD4_check 1))
      (elemB_mem_negUnipotent witnessD4 witnessD4_check 2)

omit [CharP K 2] in
theorem d4_Z3_mem
    :
    ((witnessD4.elemZ K 3 : adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) ∈
      graphFixedRootGroup TwistTag.D4 K σ := by
  rw [RootWitness.elemZ_eq, Subgroup.coe_mul]
  exact Subgroup.mul_mem_sup
    (mem_graphFixedPos σ (elemA_mem_posUnipotent witnessD4 witnessD4_check 3)
      (twistC_elemA_three σ))
    (mem_graphFixedNeg σ (elemB_mem_negUnipotent witnessD4 witnessD4_check 3)
      (twistC_elemB_three σ))

end D4Member

section D4NineFrame

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K →+* K)

theorem not_commute_mul_of_commute {G : Type*} [Group G] {x y a : G} (hy : Commute y a)
    (hx : ¬ Commute x a) : ¬ Commute (x * y) a := fun h => hx (by
  have := h.mul_left hy.inv_left
  simpa using this)

theorem exists_nine_d4
    (δ : K ≃+* K) :
    ∃ E : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ), Nat.card E = 9 ∧ IsElemAbelian 3 E ∧
      ∀ y ∈ E, Units.map (entrywiseHom δ.toRingHom) (y : ModGL TwistTag.D4.tag K) =
        (y : ModGL TwistTag.D4.tag K) := by
  obtain ⟨hZ, hZA, hZZ, -⟩ := d4_facts (K := K)
  have hZ01 : Commute (witnessD4.elemZ K 0) (witnessD4.elemZ K 1) := hZZ 0 1 (by decide)
  have hZ02 : Commute (witnessD4.elemZ K 0) (witnessD4.elemZ K 2) := hZZ 0 2 (by decide)
  have hZ12 : Commute (witnessD4.elemZ K 1) (witnessD4.elemZ K 2) := hZZ 1 2 (by decide)
  have hZ03 : Commute (witnessD4.elemZ K 0) (witnessD4.elemZ K 3) := hZZ 0 3 (by decide)
  have hZ13 : Commute (witnessD4.elemZ K 1) (witnessD4.elemZ K 3) := hZZ 1 3 (by decide)
  have hZ23 : Commute (witnessD4.elemZ K 2) (witnessD4.elemZ K 3) := hZZ 2 3 (by decide)
  have hZ012 : Commute (witnessD4.elemZ K 0 * witnessD4.elemZ K 1) (witnessD4.elemZ K 2) :=
    hZ02.mul_left hZ12
  have hA0 : ∀ j : Fin 4, j ≠ 0 → Commute (witnessD4.elemZ K j) (witnessD4.elemA K 0) :=
    fun j hj => hZA 0 j (Ne.symm hj)
  have hA3 : ∀ j : Fin 4, j ≠ 3 → Commute (witnessD4.elemZ K j) (witnessD4.elemA K 3) :=
    fun j hj => hZA 3 j (Ne.symm hj)
  have hA0₁ := hA0 1 (by decide)
  have hA0₂ := hA0 2 (by decide)
  have hA0₃ := hA0 3 (by decide)
  have hA3₀ := hA3 0 (by decide)
  have hA3₁ := hA3 1 (by decide)
  have hA3₂ := hA3 2 (by decide)
  have hsq : (witnessD4.elemZ K 0 * witnessD4.elemZ K 1 * witnessD4.elemZ K 2) ^ 2 =
      witnessD4.elemZ K 0 ^ 2 * witnessD4.elemZ K 1 ^ 2 * witnessD4.elemZ K 2 ^ 2 := by
    rw [hZ012.mul_pow, hZ01.mul_pow]
  have hcube : (witnessD4.elemZ K 0 * witnessD4.elemZ K 1 * witnessD4.elemZ K 2) ^ 3 = 1 := by
    rw [hZ012.mul_pow, hZ01.mul_pow, (hZ 0).1, (hZ 1).1, (hZ 2).1]
    simp
  obtain ⟨E', hE'H, hE'el, hE'card⟩ := exists_elemAbelian_three (n := 2)
    (![witnessD4.elemZ K 0 * witnessD4.elemZ K 1 * witnessD4.elemZ K 2, witnessD4.elemZ K 3])
    (![witnessD4.elemA K 0, witnessD4.elemA K 3])
    (H := ((graphFixedRootGroup TwistTag.D4 K σ ⊓
      (Units.map (entrywiseHom δ.toRingHom)).eqLocus (MonoidHom.id _)).comap
        (adjointGroup TwistTag.D4.tag K).subtype))
    (fun i => by
      fin_cases i
      · exact hcube
      · exact (hZ 3).1)
    (fun i => by
      fin_cases i
      · exact not_commute_mul_of_commute hA0₂
          (not_commute_mul_of_commute hA0₁ (hZ 0).2.1)
      · exact (hZ 3).2.1)
    (fun i => by
      fin_cases i
      · change ¬ Commute ((witnessD4.elemZ K 0 * witnessD4.elemZ K 1 * witnessD4.elemZ K 2) ^ 2)
          (witnessD4.elemA K 0)
        rw [hsq]
        exact not_commute_mul_of_commute (hA0₂.pow_left 2)
          (not_commute_mul_of_commute (hA0₁.pow_left 2) (hZ 0).2.2)
      · exact (hZ 3).2.2)
    (fun i j hij => by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hA0₃
      · exact (hA3₀.mul_left hA3₁).mul_left hA3₂
      · exact absurd rfl hij)
    (fun i j hij => by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact (hZ03.mul_left hZ13).mul_left hZ23
      · exact ((hZ03.mul_left hZ13).mul_left hZ23).symm
      · exact absurd rfl hij)
    (fun i => by
      fin_cases i
      · refine ⟨?_, ?_⟩
        · exact d4_ZZ0_mem σ
        · change Units.map (entrywiseHom δ.toRingHom)
            ((witnessD4.elemZ K 0 * witnessD4.elemZ K 1 * witnessD4.elemZ K 2 :
              adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) = _
          simp only [Subgroup.coe_mul, map_mul, units_map_elemZ]
          rfl
      · refine ⟨d4_Z3_mem σ, ?_⟩
        change Units.map (entrywiseHom δ.toRingHom)
          ((witnessD4.elemZ K 3 : adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) = _
        exact units_map_elemZ δ witnessD4 3)
  set E₁ : Subgroup (ModGL TwistTag.D4.tag K) := E'.map (adjointGroup TwistTag.D4.tag K).subtype
    with hE₁
  have hE₁C : E₁ ≤ graphFixedRootGroup TwistTag.D4 K σ := by
    rintro _ ⟨e, he, rfl⟩
    exact (hE'H he).1
  refine ⟨E₁.subgroupOf (graphFixedRootGroup TwistTag.D4 K σ), ?_, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₁C).toEquiv, hE₁,
      Subgroup.card_map_of_injective (adjointGroup TwistTag.D4.tag K).subtype_injective, hE'card]
    norm_num
  · exact isElemAbelian_subgroupOf (CFSG.SectionRank.isElemAbelian_map hE'el _)
  · intro y hy
    obtain ⟨e, he, hey⟩ := (show (y : ModGL TwistTag.D4.tag K) ∈ E₁ from hy)
    rw [← hey]
    exact (hE'H he).2

end D4NineFrame

section D4Frame

open CFSG.RankThree.PartTwo.KFacts

@[expose] noncomputable def innFrameD4
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    InnFrame ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (K ≃+* K) where
  fld := fieldActorHom (t := TwistTag.D4) σ
  fld_inter := fun c hc => (isInnerAut_fieldActor_iff hf hK hσ).1 hc
  three_mem := fun α _ _ => by
    obtain ⟨g, δ, h⟩ := exists_conj_mul_fieldActor hf hK hσ α
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, δ, h⟩
  nine := fun c _ => by
    obtain ⟨E, hE9, hEel, hEfix⟩ := exists_nine_d4 σ.toRingHom c
    refine ⟨E, hE9, hEel, fun y hy => ?_⟩
    apply Subtype.ext
    rw [fieldActorHom_apply, coe_fieldActor]
    exact hEfix y hy

end D4Frame

section D4Core

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [S.Normal]

theorem d4_threeElements
    (hC : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1) {f : ℕ} (hf : 1 ≤ f)
    (hS : ChevalleyExceptionalModel ↥S .trialityD4 2 f)
    (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) :
    ∀ x : X, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ S := by
  classical
  obtain ⟨-, K, hKf, hKfin, hKcard, σ₀, hσ₀, ⟨e⟩⟩ := hS
  have hK : Nat.card K = (2 ^ f) ^ 3 := by rw [hKcard]; rfl
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow (f := 3 * f) (by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
  have hbij : Function.Bijective σ₀ :=
    ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩
  let σ : K ≃+* K := RingEquiv.ofBijective σ₀ hbij
  have hσ : ∀ c, σ c = c ^ (2 ^ f) := hσ₀
  obtain ⟨-, -, -, -, -, -, -, ⟨iso⟩⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  let ψ : ↥S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := e.trans iso
  exact innFrame_core hC ((innFrameD4 hf K hK σ hσ).ofMulEquiv ψ) hX

end D4Core

end A318P

end CFSG.Quasithin
