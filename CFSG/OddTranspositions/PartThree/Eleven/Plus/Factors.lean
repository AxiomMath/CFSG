module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.Perm
public import CFSG.OddTranspositions.PartThree.Eleven.PlusFacts
public import Certificates.Certificate1383003
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import TauCeti.GroupTheory.DerivedCentralQuotient

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native
open scoped commutatorElement

private theorem h_enumA : plusFactorsEnumA () = true := Certificates.certificate1383003.1

private theorem h_enumB : plusFactorsEnumB () = true := Certificates.certificate1383003.2.1

private theorem h_sizeA : plusFactorsSizeA () = true := Certificates.certificate1383003.2.2.1

private theorem h_sizeB : plusFactorsSizeB () = true :=
  Certificates.certificate1383003.2.2.2.1

private theorem h_simpleA : plusFactorsSimpleA () = true :=
  Certificates.certificate1383003.2.2.2.2.1

private theorem h_simpleB : plusFactorsSimpleB () = true :=
  Certificates.certificate1383003.2.2.2.2.2.1

private theorem h_tableOK : plusFactorsTableOK () = true :=
  Certificates.certificate1383003.2.2.2.2.2.2.1

private theorem h_memGens : plusFactorsMemGens () = true :=
  Certificates.certificate1383003.2.2.2.2.2.2.2.1

private theorem h_commGens : plusFactorsCommGens () = true :=
  Certificates.certificate1383003.2.2.2.2.2.2.2.2.1

private theorem h_disjoint : plusFactorsDisjoint () = true :=
  Certificates.certificate1383003.2.2.2.2.2.2.2.2.2.1

private theorem h_conjGens : plusFactorsConjGens () = true :=
  Certificates.certificate1383003.2.2.2.2.2.2.2.2.2.2.1

private theorem h_nonabelian : plusFactorsNonabelian () = true :=
  Certificates.certificate1383003.2.2.2.2.2.2.2.2.2.2.2.1

private theorem h_involutions : plusFactorsInvolutions () = true :=
  Certificates.certificate1383003.2.2.2.2.2.2.2.2.2.2.2.2

private theorem plusBase_lt : ∀ p ∈ plusBase, p < 60 := by
  intro p hp
  simp only [plusBase, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

private noncomputable def DA : Subgroup (Equiv.Perm (Fin 60)) :=
  Subgroup.closure (permsA 60 plusFactorsAgens)

private noncomputable def DB : Subgroup (Equiv.Perm (Fin 60)) :=
  Subgroup.closure (permsA 60 plusFactorsBgens)

private theorem DA_spec :
    (∀ x, x ∈ DA ↔ ∃ i < (plusFactorsCA ()).pts.size, permOfArr 60 (plusFactorsCA ()).pts[i]! = x) ∧
      Nat.card DA = (plusFactorsCA ()).pts.size ∧
      ∀ i < (plusFactorsCA ()).pts.size, validA 60 (plusFactorsCA ()).pts[i]! = true := by
  simpa only [DA] using enumOK_spec plusBase_lt h_enumA

private theorem DB_spec :
    (∀ x, x ∈ DB ↔ ∃ i < (plusFactorsCB ()).pts.size, permOfArr 60 (plusFactorsCB ()).pts[i]! = x) ∧
      Nat.card DB = (plusFactorsCB ()).pts.size ∧
      ∀ i < (plusFactorsCB ()).pts.size, validA 60 (plusFactorsCB ()).pts[i]! = true := by
  simpa only [DB] using enumOK_spec plusBase_lt h_enumB

private theorem sizeA_eq : (plusFactorsCA ()).pts.size = 60 := by
  simpa only [plusFactorsSizeA, beq_iff_eq] using h_sizeA

private theorem sizeB_eq : (plusFactorsCB ()).pts.size = 60 := by
  simpa only [plusFactorsSizeB, beq_iff_eq] using h_sizeB

private theorem cardDA : Nat.card DA = 60 := by
  rw [DA_spec.2.1, sizeA_eq]

private theorem cardDB : Nat.card DB = 60 := by
  rw [DB_spec.2.1, sizeB_eq]

private theorem simpleDA : IsSimpleGroup DA :=
  isSimpleGroup_of_conjSimpleOK plusBase_lt h_enumA (by rw [sizeA_eq]; norm_num)
    (by simpa only [plusFactorsSimpleA] using h_simpleA)

private theorem simpleDB : IsSimpleGroup DB :=
  isSimpleGroup_of_conjSimpleOK plusBase_lt h_enumB (by rw [sizeB_eq]; norm_num)
    (by simpa only [plusFactorsSimpleB] using h_simpleB)

private theorem Agens_valid {k : ℕ} (hk : k < plusFactorsAgens.size) :
    validA 60 plusFactorsAgens[k]! = true := enumOK_gens_valid h_enumA hk

private theorem Bgens_valid {k : ℕ} (hk : k < plusFactorsBgens.size) :
    validA 60 plusFactorsBgens[k]! = true := enumOK_gens_valid h_enumB hk

private theorem table_valid {i : ℕ} (hi : i < 60) : validA 60 plusTable[i]! = true :=
  allLt_spec (by simpa only [plusFactorsTableOK] using h_tableOK) hi

private theorem memGens_A :
    allLt plusFactorsAgens.size (fun k =>
      (plusEnum ()).pts.toList.any (eqA 60 plusFactorsAgens[k]!)) = true := by
  have h := h_memGens
  simp only [plusFactorsMemGens, Bool.and_eq_true] at h
  exact h.1

private theorem memGens_B :
    allLt plusFactorsBgens.size (fun k =>
      (plusEnum ()).pts.toList.any (eqA 60 plusFactorsBgens[k]!)) = true := by
  have h := h_memGens
  simp only [plusFactorsMemGens, Bool.and_eq_true] at h
  exact h.2

private theorem plusEnum_mem_of_any {t : Array ℕ} {x : Equiv.Perm (Fin 60)}
    (ht : Rep 60 t x) (hany : (plusEnum ()).pts.toList.any (eqA 60 t) = true) :
    x ∈ plusPerm := by
  rw [List.any_eq_true] at hany
  obtain ⟨a, ha, he⟩ := hany
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < (plusEnum ()).pts.size := by simpa using hi
  have he' : eqA 60 t (plusEnum ()).pts[i]! = true := by
    rw [Array.getElem_toList] at he
    rwa [getElem!_pos (plusEnum ()).pts i hi']
  refine (plusEnum_spec.1 x).2 ⟨i, hi', ?_⟩
  exact (rep_of_validA (plusEnum_spec.2.2 i hi')).unique (rep_of_eqA ht he')

private theorem Agens_mem_plusPerm {k : ℕ} (hk : k < plusFactorsAgens.size) :
    permOfArr 60 plusFactorsAgens[k]! ∈ plusPerm :=
  plusEnum_mem_of_any (rep_of_validA (Agens_valid hk)) (allLt_spec memGens_A hk)

private theorem Bgens_mem_plusPerm {k : ℕ} (hk : k < plusFactorsBgens.size) :
    permOfArr 60 plusFactorsBgens[k]! ∈ plusPerm :=
  plusEnum_mem_of_any (rep_of_validA (Bgens_valid hk)) (allLt_spec memGens_B hk)

private theorem DA_le_plusPerm : DA ≤ plusPerm := by
  rw [DA, Subgroup.closure_le]
  rintro g ⟨k, hk, rfl⟩
  exact Agens_mem_plusPerm hk

private theorem DB_le_plusPerm : DB ≤ plusPerm := by
  rw [DB, Subgroup.closure_le]
  rintro g ⟨k, hk, rfl⟩
  exact Bgens_mem_plusPerm hk

private noncomputable def A : Subgroup plusPerm := DA.subgroupOf plusPerm

private noncomputable def B : Subgroup plusPerm := DB.subgroupOf plusPerm

private theorem cardA : Nat.card A = 60 := by
  have h1 : Nat.card A = Nat.card DA :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe DA_le_plusPerm).toEquiv
  rw [h1, cardDA]

private theorem cardB : Nat.card B = 60 := by
  have h1 : Nat.card B = Nat.card DB :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe DB_le_plusPerm).toEquiv
  rw [h1, cardDB]

private theorem simpleA : IsSimpleGroup A :=
  (MulEquiv.isSimpleGroup_congr
    (Subgroup.subgroupOfEquivOfLe DA_le_plusPerm)).mpr simpleDA

private theorem simpleB : IsSimpleGroup B :=
  (MulEquiv.isSimpleGroup_congr
    (Subgroup.subgroupOfEquivOfLe DB_le_plusPerm)).mpr simpleDB

private theorem commGens_check :
    allLt plusFactorsAgens.size (fun i => allLt plusFactorsBgens.size fun j =>
      eqA 60 (commutatorA 60 plusFactorsAgens[i]! plusFactorsBgens[j]!) (idA 60)) = true := by
  simpa only [plusFactorsCommGens] using h_commGens

private theorem commGens_commute (k : ℕ) (hk : k < plusFactorsAgens.size) (l : ℕ)
    (hl : l < plusFactorsBgens.size) :
    Commute (permOfArr 60 plusFactorsAgens[k]!) (permOfArr 60 plusFactorsBgens[l]!) := by
  have heq : eqA 60 (commutatorA 60 plusFactorsAgens[k]! plusFactorsBgens[l]!) (idA 60) = true :=
    allLt_spec (allLt_spec commGens_check hk) hl
  have h1 : ⁅permOfArr 60 plusFactorsAgens[k]!, permOfArr 60 plusFactorsBgens[l]!⁆ = 1 :=
    eq_of_eqA (rep_commutatorA (Agens_valid hk) (Bgens_valid hl)) rep_idA heq
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

private theorem commute_closure {G : Type*} [Group G] {S T : Set G}
    (h : ∀ s ∈ S, ∀ t ∈ T, Commute s t) :
    ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure T, Commute a b := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem s hs =>
    intro b hb
    induction hb using Subgroup.closure_induction with
    | mem t ht => exact h s hs t ht
    | one => exact Commute.one_right s
    | mul x y _ _ ihx ihy => exact ihx.mul_right ihy
    | inv x _ ihx => exact ihx.inv_right
  | one => intro b _; exact Commute.one_left b
  | mul x y _ _ ihx ihy => intro b hb; exact (ihx b hb).mul_left (ihy b hb)
  | inv x _ ihx => intro b hb; exact (ihx b hb).inv_left

private theorem DA_commute_DB : ∀ a ∈ DA, ∀ b ∈ DB, Commute a b := by
  rw [DA, DB]
  refine commute_closure ?_
  intro s hs t ht
  obtain ⟨k, hk, rfl⟩ := hs
  obtain ⟨l, hl, rfl⟩ := ht
  exact commGens_commute k hk l hl

private theorem inf_eq : A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxA, hxB⟩ := hx
  obtain ⟨i, hi, hix⟩ := (DA_spec.1 (x : Equiv.Perm (Fin 60))).1 hxA
  obtain ⟨j, hj, hjx⟩ := (DB_spec.1 (x : Equiv.Perm (Fin 60))).1 hxB
  have he : eqA 60 (plusFactorsCA ()).pts[i]! (plusFactorsCB ()).pts[j]! = true := by
    rw [eqA_iff (rep_of_validA (DA_spec.2.2 i hi)) (rep_of_validA (DB_spec.2.2 j hj))]
    rw [hix, hjx]
  have hd : allLt (plusFactorsCA ()).pts.size (fun i =>
      allLt (plusFactorsCB ()).pts.size fun j =>
        (eqA 60 (plusFactorsCA ()).pts[i]! (plusFactorsCB ()).pts[j]!) == false ||
          eqA 60 (plusFactorsCA ()).pts[i]! (idA 60)) = true := by
    simpa only [plusFactorsDisjoint] using h_disjoint
  have hH := allLt_spec (allLt_spec hd hi) hj
  rw [he] at hH
  simp at hH
  have hone : (x : Equiv.Perm (Fin 60)) = 1 := by
    rw [← hix]
    exact eq_of_eqA (rep_of_validA (DA_spec.2.2 i hi)) rep_idA hH
  rw [Subgroup.mem_bot]
  exact Subtype.ext hone

private theorem A_not_commutative : ¬ IsMulCommutative A := by
  intro hcomm
  have hk0 : (0 : ℕ) < plusFactorsAgens.size := by simp [plusFactorsAgens]
  have hk1 : (1 : ℕ) < plusFactorsAgens.size := by simp [plusFactorsAgens]
  have h0 : permOfArr 60 plusFactorsAgens[0]! ∈ DA :=
    Subgroup.subset_closure ⟨0, hk0, rfl⟩
  have h1 : permOfArr 60 plusFactorsAgens[1]! ∈ DA :=
    Subgroup.subset_closure ⟨1, hk1, rfl⟩
  have hp0 : permOfArr 60 plusFactorsAgens[0]! ∈ plusPerm := DA_le_plusPerm h0
  have hp1 : permOfArr 60 plusFactorsAgens[1]! ∈ plusPerm := DA_le_plusPerm h1
  let a : A := ⟨⟨permOfArr 60 plusFactorsAgens[0]!, hp0⟩, h0⟩
  let b : A := ⟨⟨permOfArr 60 plusFactorsAgens[1]!, hp1⟩, h1⟩
  have hab : a * b = b * a := hcomm.is_comm.comm a b
  have hab' : (↑(a * b) : plusPerm) = (↑(b * a) : plusPerm) := congrArg Subtype.val hab
  have hcoe : (↑(↑(a * b) : plusPerm) : Equiv.Perm (Fin 60)) =
      (↑(↑(b * a) : plusPerm) : Equiv.Perm (Fin 60)) := congrArg Subtype.val hab'
  have hcommG : permOfArr 60 plusFactorsAgens[0]! * permOfArr 60 plusFactorsAgens[1]! =
      permOfArr 60 plusFactorsAgens[1]! * permOfArr 60 plusFactorsAgens[0]! := by
    exact hcoe
  have hna :
      eqA 60 (commutatorA 60 plusFactorsAgens[0]! plusFactorsAgens[1]!) (idA 60) = false := by
    simpa only [plusFactorsNonabelian, beq_iff_eq] using h_nonabelian
  have heq : eqA 60 (commutatorA 60 plusFactorsAgens[0]! plusFactorsAgens[1]!) (idA 60) = true := by
    rw [eqA_iff (rep_commutatorA (Agens_valid hk0) (Agens_valid hk1)) rep_idA]
    rw [commutatorElement_def]
    rw [hcommG]
    group
  rw [heq] at hna
  exact Bool.false_ne_true hna.symm

private theorem A_perfect : Group.IsPerfect A := by
  haveI : IsSimpleGroup A := simpleA
  exact TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative A_not_commutative

private theorem A_le_commutator : A ≤ commutator plusPerm := by
  haveI : Group.IsPerfect A := A_perfect
  have h : ⁅A, A⁆ = A := Subgroup.commutator_eq_self
  calc A = ⁅A, A⁆ := h.symm
    _ ≤ ⁅(⊤ : Subgroup plusPerm), ⊤⁆ := Subgroup.commutator_mono le_top le_top
    _ = commutator plusPerm := by rw [commutator_def]

private theorem B_le_commutator : B ≤ commutator plusPerm := by
  haveI : IsSimpleGroup B := simpleB
  have hnc : ¬ IsMulCommutative B := by
    intro hcomm
    haveI : IsMulCommutative B := hcomm
    have hprime := (Group.is_simple_iff_prime_card (α := B)).mp simpleB
    rw [cardB] at hprime
    exact (by norm_num : ¬ Nat.Prime 60) hprime
  haveI : Group.IsPerfect B :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc
  have h : ⁅B, B⁆ = B := Subgroup.commutator_eq_self
  calc B = ⁅B, B⁆ := h.symm
    _ ≤ ⁅(⊤ : Subgroup plusPerm), ⊤⁆ := Subgroup.commutator_mono le_top le_top
    _ = commutator plusPerm := by rw [commutator_def]

private theorem card_sup_eq : Nat.card (A ⊔ B : Subgroup plusPerm) = 3600 := by
  have hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext (DA_commute_DB (x : Equiv.Perm (Fin 60)) hx
      (y : Equiv.Perm (Fin 60)) hy)
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hc).1
  have h1 : Nat.card (A ⊔ B : Subgroup plusPerm) * Nat.card (A ⊓ B : Subgroup plusPerm) =
      Nat.card A * Nat.card B := h
  have h2 : Nat.card (A ⊓ B : Subgroup plusPerm) = 1 := by
    rw [inf_eq]
    exact Subgroup.card_bot
  have h3 : Nat.card A * Nat.card B = 3600 := by rw [cardA, cardB]
  rw [h2, h3, mul_one] at h1
  exact h1

set_option maxRecDepth 10000 in
private theorem index_sup_eq : (A ⊔ B).index = 2 := by
  have h := Subgroup.index_mul_card (A ⊔ B)
  have hc : Nat.card (A ⊔ B : Subgroup plusPerm) = 3600 := card_sup_eq
  have h2 : (A ⊔ B).index * 3600 = 7200 := by
    rw [← hc]
    exact h.trans card_plusPerm
  omega

private theorem commutator_le_sup : commutator plusPerm ≤ A ⊔ B := by
  have hidx : (A ⊔ B).index = 2 := index_sup_eq
  have hnormal : (A ⊔ B).Normal := Subgroup.normal_of_index_eq_two hidx
  haveI : (A ⊔ B).Normal := hnormal
  rw [commutator_def]
  refine Subgroup.commutator_le.2 ?_
  intro g₁ _ g₂ _
  have hmem_norm : g₁ ∈ Subgroup.normalizer ((A ⊔ B : Subgroup plusPerm) : Set plusPerm) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g₁
  have hconj : g₁ * g₂ * g₁⁻¹ ∈ (A ⊔ B) ↔ g₂ ∈ (A ⊔ B) :=
    (Subgroup.mem_normalizer_iff.1 hmem_norm g₂).symm
  have hinv : g₂⁻¹ ∈ (A ⊔ B) ↔ g₂ ∈ (A ⊔ B) := (A ⊔ B).inv_mem_iff
  have hmem := (Subgroup.mul_mem_iff_of_index_two hidx
    (a := g₁ * g₂ * g₁⁻¹) (b := g₂⁻¹)).2 (hconj.trans hinv.symm)
  simpa only [commutatorElement_def] using hmem

private theorem sup_eq_commutator : A ⊔ B = commutator plusPerm :=
  le_antisymm (sup_le A_le_commutator B_le_commutator) commutator_le_sup

private noncomputable def conjG (i : ℕ) : Equiv.Perm (Fin 60) ≃* Equiv.Perm (Fin 60) :=
  MulAut.conj (permOfArr 60 plusTable[i]!)

private theorem conjGens_check :
    allLt 60 (fun i =>
      (allLt plusFactorsAgens.size fun k =>
        (plusFactorsCB ()).pts.toList.any (eqA 60 (conjA 60 plusTable[i]! plusFactorsAgens[k]!))) &&
      (allLt plusFactorsBgens.size fun k =>
        (plusFactorsCA ()).pts.toList.any
          (eqA 60 (conjA 60 plusTable[i]! plusFactorsBgens[k]!)))) = true := by
  simpa only [plusFactorsConjGens] using h_conjGens

private theorem Agens_conj_mem_DB (i : ℕ) (hi : i < 60) (k : ℕ)
    (hk : k < plusFactorsAgens.size) :
    conjG i (permOfArr 60 plusFactorsAgens[k]!) ∈ DB := by
  have hall := allLt_spec conjGens_check hi
  simp only [Bool.and_eq_true] at hall
  have hany := allLt_spec hall.1 hk
  have hrep := rep_conjA (table_valid hi) (rep_of_validA (Agens_valid hk))
  have hval : conjG i (permOfArr 60 plusFactorsAgens[k]!) =
      permOfArr 60 plusTable[i]! * permOfArr 60 plusFactorsAgens[k]! *
        (permOfArr 60 plusTable[i]!)⁻¹ := by
    simp only [conjG, MulAut.conj_apply]
  rw [hval]
  exact enumOK_mem_of_any plusBase_lt h_enumB hrep hany

private theorem DA_map_conjG_le_DB (i : ℕ) (hi : i < 60) :
    DA.map (conjG i).toMonoidHom ≤ DB := by
  rw [DA, MonoidHom.map_closure, Subgroup.closure_le]
  rintro g ⟨s, ⟨k, hk, rfl⟩, rfl⟩
  exact Agens_conj_mem_DB i hi k hk

private theorem swap (r : plusPerm) (hr : r ∈ plusClass) :
    A.map (MulAut.conj r).toMonoidHom = B := by
  obtain ⟨k, hk⟩ := hr
  have hle : A.map (MulAut.conj r).toMonoidHom ≤ B := by
    rintro x ⟨a, ha, rfl⟩
    show ((MulAut.conj r a : plusPerm) : Equiv.Perm (Fin 60)) ∈ DB
    have hcoe : ((MulAut.conj r a : plusPerm) : Equiv.Perm (Fin 60)) =
        conjG (k : ℕ) (a : Equiv.Perm (Fin 60)) := by
      change (r : Equiv.Perm (Fin 60)) * (a : Equiv.Perm (Fin 60)) *
          (r : Equiv.Perm (Fin 60))⁻¹ =
        conjG (k : ℕ) (a : Equiv.Perm (Fin 60))
      rw [hk]
      simp only [conjG, MulAut.conj_apply, plusRefl]
    rw [hcoe]
    refine DA_map_conjG_le_DB (k : ℕ) k.isLt ?_
    exact Subgroup.mem_map_of_mem (conjG (k : ℕ)).toMonoidHom ha
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective (f := (MulAut.conj r).toMonoidHom)
    (MulAut.conj r).injective, cardA, cardB]

private theorem invCheck_all :
    allLt (plusEnum ()).pts.size (fun k =>
      let p := (plusEnum ()).pts[k]!
      (eqA 60 (compA 60 p p) (idA 60)) == false || eqA 60 p (idA 60) ||
        plusFactorsRowMem p || plusFactorsProdMem p ||
        plusFactorsEnumMem (plusFactorsCA ()) p ||
        plusFactorsEnumMem (plusFactorsCB ()) p) = true := by
  simpa only [plusFactorsInvolutions] using h_involutions

private theorem invCheck (k : ℕ) (hk : k < (plusEnum ()).pts.size) :
    (((eqA 60 (compA 60 ((plusEnum ()).pts[k]!) ((plusEnum ()).pts[k]!)) (idA 60))
      == false) = true) ∨
      eqA 60 (plusEnum ()).pts[k]! (idA 60) = true ∨
      plusFactorsRowMem ((plusEnum ()).pts[k]!) = true ∨
      plusFactorsProdMem ((plusEnum ()).pts[k]!) = true ∨
      plusFactorsEnumMem (plusFactorsCA ()) ((plusEnum ()).pts[k]!) = true ∨
      plusFactorsEnumMem (plusFactorsCB ()) ((plusEnum ()).pts[k]!) = true := by
  have h := allLt_spec invCheck_all hk
  simpa only [Bool.or_eq_true, or_assoc] using h

private theorem mem_rowMem {p : Array ℕ} (h : plusFactorsRowMem p = true) :
    ∃ i < 60, eqA 60 plusTable[i]! p = true := by
  rw [plusFactorsRowMem, List.any_eq_true] at h
  obtain ⟨i, hi, he⟩ := h
  exact ⟨i, by simpa using hi, he⟩

private theorem mem_prodMem {p : Array ℕ} (h : plusFactorsProdMem p = true) :
    ∃ i < 60, ∃ j < 60, i ≠ j ∧ (plusTable[i]!)[j]! = j ∧
      eqA 60 (compA 60 plusTable[i]! plusTable[j]!) p = true := by
  rw [plusFactorsProdMem, List.any_eq_true] at h
  obtain ⟨i, hi, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨j, hj, h⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨i, by simpa using hi, j, by simpa using hj, h.1.1, h.1.2, h.2⟩

private theorem mem_enumMem {c : ArrCert} {p : Array ℕ}
    (h : plusFactorsEnumMem c p = true) :
    ∃ m < c.pts.size, eqA 60 p c.pts[m]! = true := by
  rw [plusFactorsEnumMem, List.any_eq_true] at h
  obtain ⟨a, ha, he⟩ := h
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem ha
  have hm' : m < c.pts.size := by simpa using hm
  refine ⟨m, hm', ?_⟩
  rw [Array.getElem_toList] at he
  rw [getElem!_pos c.pts m hm']
  exact he

private theorem involutions_spec : ∀ x : plusPerm, orderOf x = 2 →
    x ∈ plusClass ∨ (∃ a ∈ plusClass, ∃ b ∈ plusClass, a ≠ b ∧ Commute a b ∧ x = a * b) ∨
      x ∈ A ∨ x ∈ B := by
  intro x hord
  have hx2 : (x : Equiv.Perm (Fin 60)) * (x : Equiv.Perm (Fin 60)) = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hord] at h
    simpa [pow_two] using congrArg Subtype.val h
  have hxne : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    norm_num at hord
  obtain ⟨i, hi, hix⟩ := (plusEnum_spec.1 (x : Equiv.Perm (Fin 60))).1 x.2
  set p := (plusEnum ()).pts[i]! with hp
  have hpv : validA 60 p = true := by rw [hp]; exact plusEnum_spec.2.2 i hi
  have hpx : permOfArr 60 p = (x : Equiv.Perm (Fin 60)) := by rw [hp]; exact hix
  have hcomp : eqA 60 (compA 60 p p) (idA 60) = true := by
    refine (eqA_iff (rep_compA (rep_of_validA hpv) (rep_of_validA hpv)) rep_idA).2 ?_
    rw [hpx]
    exact hx2
  have hnot : ((eqA 60 (compA 60 p p) (idA 60)) == false) = false := by
    rw [hcomp]
    rfl
  have hcases := invCheck i hi
  rw [← hp] at hcases
  rw [hnot] at hcases
  simp only [Bool.false_eq_true, false_or] at hcases
  rcases hcases with hid | hcases
  · exfalso
    apply hxne
    apply Subtype.ext
    rw [← hpx]
    exact eq_of_eqA (rep_of_validA hpv) rep_idA hid
  · rcases hcases with hrow | hcases
    · left
      obtain ⟨r, hr, he⟩ := mem_rowMem hrow
      refine ⟨⟨r, hr⟩, ?_⟩
      have hv : permOfArr 60 plusTable[r]! = (x : Equiv.Perm (Fin 60)) :=
        (eq_of_eqA (rep_of_validA (table_valid hr)) (rep_of_validA hpv) he).trans hpx
      simpa only [plusRefl] using hv.symm
    · rcases hcases with hprod | hcases
      · right; left
        obtain ⟨r, hr, s, hs, hrs, hcomm, he⟩ := mem_prodMem hprod
        let av : plusPerm := ⟨plusRefl (⟨r, hr⟩ : Fin 60), plusRefl_mem _⟩
        let bv : plusPerm := ⟨plusRefl (⟨s, hs⟩ : Fin 60), plusRefl_mem _⟩
        have hav : av ∈ plusClass := ⟨⟨r, hr⟩, rfl⟩
        have hbv : bv ∈ plusClass := ⟨⟨s, hs⟩, rfl⟩
        have hne : av ≠ bv := by
          intro h
          have h1 : plusRefl (⟨r, hr⟩ : Fin 60) = plusRefl (⟨s, hs⟩ : Fin 60) :=
            congrArg Subtype.val h
          have h2 : (⟨r, hr⟩ : Fin 60) = ⟨s, hs⟩ := plusRefl_injective h1
          exact hrs (congrArg Fin.val h2)
        have hcab : Commute av bv := by
          apply Subtype.ext
          have h3 : plusRefl (⟨r, hr⟩ : Fin 60) (⟨s, hs⟩ : Fin 60) = (⟨s, hs⟩ : Fin 60) := by
            apply Fin.ext
            rw [plusRefl_apply]
            exact hcomm
          exact (commute_plusRefl_iff _ _).2 h3
        have hxab : x = av * bv := by
          apply Subtype.ext
          show (x : Equiv.Perm (Fin 60)) =
            plusRefl (⟨r, hr⟩ : Fin 60) * plusRefl (⟨s, hs⟩ : Fin 60)
          exact ((eq_of_eqA (rep_compA (rep_of_validA (table_valid hr))
            (rep_of_validA (table_valid hs))) (rep_of_validA hpv) he).trans hpx).symm
        exact ⟨av, hav, bv, hbv, hne, hcab, hxab⟩
      · rcases hcases with hA | hB
        · right; right; left
          obtain ⟨m, hm, he⟩ := mem_enumMem hA
          have hxg : (x : Equiv.Perm (Fin 60)) ∈ DA := by
            have hv : permOfArr 60 p = permOfArr 60 (plusFactorsCA ()).pts[m]! :=
              eq_of_eqA (rep_of_validA hpv) (rep_of_validA (DA_spec.2.2 m hm)) he
            rw [hpx] at hv
            exact (DA_spec.1 _).2 ⟨m, hm, hv.symm⟩
          exact hxg
        · right; right; right
          obtain ⟨m, hm, he⟩ := mem_enumMem hB
          have hxg : (x : Equiv.Perm (Fin 60)) ∈ DB := by
            have hv : permOfArr 60 p = permOfArr 60 (plusFactorsCB ()).pts[m]! :=
              eq_of_eqA (rep_of_validA hpv) (rep_of_validA (DB_spec.2.2 m hm)) he
            rw [hpx] at hv
            exact (DB_spec.1 _).2 ⟨m, hm, hv.symm⟩
          exact hxg

theorem index_commutator_plusPerm : (commutator plusPerm).index = 2 := by
  rw [← sup_eq_commutator]
  exact index_sup_eq

theorem exists_plusFactors : ∃ A B : Subgroup plusPerm, O4PlusFactors plusClass A B :=
  ⟨A, B,
    { sup_eq := sup_eq_commutator
      inf_eq := inf_eq
      commute := fun a ha b hb =>
        Subtype.ext (DA_commute_DB (a : Equiv.Perm (Fin 60)) ha (b : Equiv.Perm (Fin 60)) hb)
      simpleA := simpleA
      cardA := cardA
      simpleB := simpleB
      cardB := cardB
      swap := swap
      involutions := involutions_spec }⟩

end CFSG.OddTranspositions.PartThree
