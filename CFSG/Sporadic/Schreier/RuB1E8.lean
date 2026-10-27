module

public import CFSG.Sporadic.Schreier.RuB1XList
public import CFSG.Sporadic.Schreier.RuSEnum
public import CFSG.Sporadic.Schreier.RuWitReps

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native RuB1

theorem pickBy_sublist {α : Type} (r : α → α → Bool) : ∀ l : List α, (pickBy r l).Sublist l
  | [] => List.Sublist.slnil
  | a :: l => by
    simp only [pickBy]
    split
    · exact (pickBy_sublist r l).cons a
    · exact (pickBy_sublist r l).cons_cons a

theorem pickBy_pairwise {α : Type} (r : α → α → Bool) :
    ∀ l : List α, (pickBy r l).Pairwise fun a b => r a b = false
  | [] => List.Pairwise.nil
  | a :: l => by
    simp only [pickBy]
    split
    · exact pickBy_pairwise r l
    · rename_i h
      refine List.Pairwise.cons (fun b hb => ?_) (pickBy_pairwise r l)
      cases hab : r a b
      · rfl
      · exact absurd (List.any_eq_true.2 ⟨b, hb, hab⟩) h

theorem length_mul_card_inf_le {G : Type*} [Group G] {S H : Subgroup G} [Finite S] {l : List G}
    (hl : ∀ s ∈ l, s ∈ S) (hp : l.Pairwise fun s u => s⁻¹ * u ∉ H) :
    l.length * Nat.card ↥(S ⊓ H) ≤ Nat.card S := by
  set K : Subgroup S := H.subgroupOf S
  have hK : Nat.card K = Nat.card ↥(S ⊓ H) := by
    rw [show K = (S ⊓ H).subgroupOf S from (inf_subgroupOf_left H S).symm]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hidx : l.length ≤ K.index := by
    let f : Fin l.length → S ⧸ K := fun i => QuotientGroup.mk ⟨l[i], hl _ (List.getElem_mem _)⟩
    have hf : Function.Injective f := by
      intro i j hij
      by_contra hne
      have hmem : l[i]⁻¹ * l[j] ∈ H := by
        have := QuotientGroup.eq.1 hij
        rwa [mem_subgroupOf] at this
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · exact List.pairwise_iff_getElem.1 hp i j i.2 j.2 h hmem
      · refine List.pairwise_iff_getElem.1 hp j i j.2 i.2 h ?_
        simpa using H.inv_mem hmem
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin, ← index_eq_card] at this
  calc l.length * Nat.card ↥(S ⊓ H) = l.length * Nat.card K := by rw [hK]
    _ ≤ K.index * Nat.card K := Nat.mul_le_mul_right _ hidx
    _ = Nat.card S := by rw [mul_comm]; exact K.card_mul_index

@[expose] def ruSWordElt (w : List ℤ) : Equiv.Perm (Fin 4060) := evalSigned ruSGens w

theorem ruSWordElt_mem (w : List ℤ) : ruSWordElt w ∈ ruS :=
  evalSigned_mem (fun _ hg => subset_closure hg) w

theorem conj_eq_of_mem_centralizer {G : Type*} [Group G] {s s' g : G}
    (hc : s⁻¹ * s' ∈ centralizer ({g} : Set G)) : s' * g * s'⁻¹ = s * g * s⁻¹ := by
  have hcg := mem_centralizer_singleton_iff.1 hc
  calc s' * g * s'⁻¹ = s * ((s⁻¹ * s') * g) * (s⁻¹ * s')⁻¹ * s⁻¹ := by group
    _ = s * g * s⁻¹ := by rw [hcg]; group

theorem mul_comm_of_sq {G : Type*} [Group G] {E : Subgroup G} (hsq : ∀ x ∈ E, x * x = 1)
    {a b : G} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  have hab := hsq _ (E.mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
  rw [← inv_eq_of_mul_eq_one_right hab, mul_inv_rev, ha', hb']

theorem e8BigIdx_getD_lt (m : ℕ) : e8BigIdx.getD m 0 < 35 := by
  rcases m with _ | _ | _ | _ | _ | _ | _ | _ | m <;> simp [e8BigIdx]

theorem e8Check_parts (h : ruB1E8Check = true) :
    (e8ConjWords.all fun w => lettersOK 4 w) = true ∧
    (e8W.all fun q => isInvA 4060 q.2.1 q.2.2) = true ∧
    all2 4060 ruLevS (fun t => !ruIsInvolA t ||
      (Nat.any 15 fun k _ => eqA 4060 t (bigElt ruEArr xList k)) ||
      decide (9 ≤ (pickBy (fun p p' => eqA 4060 p.2 p'.2)
        (e8W.map fun q => (q, conjBy q t))).length)) = true ∧
    (allLt 8 fun k => allLt 15 fun k' =>
      let a := bigElt ruEArr xList (7 + k)
      let b := bigElt ruEArr xList k'
      !pairCond a b || decide (9 ≤ (pickBy (fun p p' => eqA 4060 p.2.1 p'.2.1 &&
        eqA 4060 p.2.2 p'.2.2) (e8W.map fun q => (q, conjBy q a, conjBy q b))).length)) = true := by
  simpa only [ruB1E8Check, e8CheckWith, Bool.and_eq_true, and_assoc] using h

theorem rep_e8W (h : ruB1E8Check = true)
    {q : List ℤ × Array ℕ × Array ℕ} (hq : q ∈ e8W) :
    Rep 4060 q.2.1 (ruSWordElt q.1) ∧ Rep 4060 q.2.2 (ruSWordElt q.1)⁻¹ := by
  obtain ⟨h1, h2, -⟩ := e8Check_parts h
  have hrep : Rep 4060 q.2.1 (ruSWordElt q.1) := by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hq
    exact rep_wordA_evalSigned (k := 4) rep_ruSGens rep_ruSGensInv w
      (List.all_eq_true.1 h1 w hw)
  exact ⟨hrep, rep_inv_of_isInvA hrep (List.all_eq_true.1 h2 q hq)⟩

theorem rep_conjBy (h : ruB1E8Check = true)
    {q : List ℤ × Array ℕ × Array ℕ} (hq : q ∈ e8W)
    {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    Rep 4060 (conjBy q t) (ruSWordElt q.1 * g * (ruSWordElt q.1)⁻¹) :=
  rep_compA (rep_compA (rep_e8W h hq).1 ht) (rep_e8W h hq).2

theorem nine_mul_card_le_of_pick
    {β : Type}
    (key : List ℤ × Array ℕ × Array ℕ → β) (r : β → β → Bool)
    {H : Subgroup (Equiv.Perm (Fin 4060))}
    (hr : ∀ q ∈ e8W, ∀ q' ∈ e8W, (ruSWordElt q.1)⁻¹ * ruSWordElt q'.1 ∈ H →
      r (key q) (key q') = true)
    (hlen : 9 ≤ (pickBy (fun p p' => r p.2 p'.2) (e8W.map fun q => (q, key q))).length) :
    9 * Nat.card ↥(ruS ⊓ H) ≤ 16384 := by
  have hmem : ∀ p ∈ pickBy (fun p p' => r p.2 p'.2) (e8W.map fun q => (q, key q)),
      p.1 ∈ e8W ∧ p.2 = key p.1 := fun p hp => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ((pickBy_sublist _ _).subset hp)
    exact ⟨hq, rfl⟩
  have hpair : ((pickBy (fun p p' => r p.2 p'.2) (e8W.map fun q => (q, key q))).map
      fun p => ruSWordElt p.1.1).Pairwise fun s u => s⁻¹ * u ∉ H := by
    rw [List.pairwise_map]
    refine (pickBy_pairwise _ _).imp_of_mem fun hp hp' hr' hH => ?_
    obtain ⟨hq, hk⟩ := hmem _ hp
    obtain ⟨hq', hk'⟩ := hmem _ hp'
    have := hr _ hq _ hq' hH
    rw [← hk, ← hk'] at this
    exact Bool.false_ne_true (hr'.symm.trans this)
  generalize pickBy (fun p p' => r p.2 p'.2) (e8W.map fun q => (q, key q)) = L at hpair hlen
  have key' := length_mul_card_inf_le (S := ruS) (l := L.map fun p => ruSWordElt p.1.1)
    (fun s hs => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hs
      exact ruSWordElt_mem _) hpair
  rw [List.length_map, card_ruS] at key'
  exact (Nat.mul_le_mul_right _ hlen).trans key'

@[expose] def ruBigElt (k : ℕ) : Equiv.Perm (Fin 4060) :=
  if k < 7 then ruEElt k else ruXElt (e8BigIdx.getD (k - 7) 0)

theorem rep_bigElt (k : ℕ) :
    Rep 4060 (bigElt ruEArr xList k) (ruBigElt k) := by
  unfold bigElt ruBigElt
  split
  · exact rep_ruEElt ‹_›
  · exact rep_xList (e8BigIdx_getD_lt _)

theorem ruBigElt_of_card
    (h : ruB1E8Check = true) {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruS) (hg2 : orderOf g = 2)
    (hc : 2048 ≤ Nat.card ↥(ruS ⊓ centralizer ({g} : Set _))) :
    ∃ k < 15, g = ruBigElt k := by
  refine ruS_forall (P := fun g => orderOf g = 2 →
      2048 ≤ Nat.card ↥(ruS ⊓ centralizer ({g} : Set (Equiv.Perm (Fin 4060)))) →
      ∃ k < 15, g = ruBigElt k) (fun t g ht hp hg2 hc => ?_) (e8Check_parts h).2.2.1 g hg hg2 hc
  simp only [(ruIsInvolA_iff ht).2 hg2, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    decide_eq_true_eq] at hp
  rcases hp with hp | hp
  · obtain ⟨k, hk, hk'⟩ := nat_any_iff'.1 hp
    exact ⟨k, hk, eq_of_eqA ht (rep_bigElt k) hk'⟩
  · have := nine_mul_card_le_of_pick (fun q => conjBy q t) (eqA 4060)
      (H := centralizer ({g} : Set _)) (fun q hq q' hq' hH =>
        (eqA_iff (rep_conjBy h hq ht) (rep_conjBy h hq' ht)).2
          (conj_eq_of_mem_centralizer hH).symm) hp
    omega

theorem ruESub_char_of_check
    (h : ruB1E8Check = true) :
    ∀ E : Subgroup (Equiv.Perm (Fin 4060)), E ≤ ruS → ruZ ∈ E → Nat.card E = 8 →
      (∀ x ∈ E, x * x = 1) →
      Nat.card ↥(ruS ⊓ centralizer (E : Set (Equiv.Perm (Fin 4060)))) = 2048 → E = ruESub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro E hES hzE hE8 hsq hC
  have hle : ∀ T : Subgroup (Equiv.Perm (Fin 4060)),
      centralizer (E : Set (Equiv.Perm (Fin 4060))) ≤ T → 2048 ≤ Nat.card ↥(ruS ⊓ T) :=
    fun T hT => hC ▸ card_le_of_le (inf_le_inf_left _ hT)
  have hbig : ∀ e ∈ E, e ≠ 1 → ∃ k < 15, e = ruBigElt k := fun e he he1 =>
    ruBigElt_of_card h (hES he) (orderOf_eq_prime (by rw [pow_two]; exact hsq e he) he1)
      (hle _ (centralizer_le (Set.singleton_subset_iff.2 he)))
  by_contra hne
  have hnle : ¬ E ≤ ruESub := fun hEA =>
    hne (eq_of_le_of_card_ge hEA (card_ruESub.trans hE8.symm).le)
  obtain ⟨a, haE, haA⟩ : ∃ a ∈ E, a ∉ ruESub := by
    by_contra hc
    push Not at hc
    exact hnle hc
  obtain ⟨k, hk, rfl⟩ := hbig _ haE fun h1 => haA (h1 ▸ ruESub.one_mem)
  have hk7 : 7 ≤ k := by
    by_contra hlt
    refine haA ?_
    rw [ruBigElt, ite_eq_left (by omega)]
    exact mem_ruESub.2 (Or.inr ⟨k, by omega, rfl⟩)
  obtain ⟨b, hbE, hb1, hbz, hba, hbza⟩ : ∃ b ∈ E, b ≠ 1 ∧ b ≠ ruZ ∧ b ≠ ruBigElt k ∧
      b ≠ ruZ * ruBigElt k := by
    by_contra hno
    push Not at hno
    have hsub : (E : Set (Equiv.Perm (Fin 4060))) ⊆
        (({1, ruZ, ruBigElt k, ruZ * ruBigElt k} : Finset _) : Set _) := fun x hx => by
      by_cases h1 : x = 1
      · simp [h1]
      by_cases h2 : x = ruZ
      · simp [h2]
      by_cases h3 : x = ruBigElt k
      · simp [h3]
      simp [hno x hx h1 h2 h3]
    have h4 : Nat.card E ≤ 4 := by
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      exact (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans
        ((Set.ncard_coe_finset _).trans_le Finset.card_le_four)
    omega
  obtain ⟨k', hk', rfl⟩ := hbig _ hbE hb1
  have hpk := allLt_spec (allLt_spec (e8Check_parts h).2.2.2 (show k - 7 < 8 by omega)) hk'
  simp only [show 7 + (k - 7) = k by omega] at hpk
  have ha := rep_bigElt k
  have hb := rep_bigElt k'
  have hcond : pairCond (bigElt ruEArr xList k) (bigElt ruEArr xList k') = true := by
    have hne' : ∀ {t u : Array ℕ} {g g' : Equiv.Perm (Fin 4060)}, Rep 4060 t g → Rep 4060 u g' →
        g ≠ g' → (!eqA 4060 t u) = true := fun ht hu hgg' => by
      rw [Bool.not_eq_true']
      cases e : eqA 4060 _ _
      · rfl
      · exact absurd ((eqA_iff ht hu).1 e) hgg'
    simp only [pairCond, Bool.and_eq_true]
    exact ⟨⟨⟨hne' hb rep_ruZ hbz, hne' hb ha hba⟩, hne' hb (rep_compA rep_ruZ ha) hbza⟩,
      (eqA_iff (rep_compA ha hb) (rep_compA hb ha)).2 (mul_comm_of_sq hsq haE hbE)⟩
  simp only [hcond, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hpk
  have hH := nine_mul_card_le_of_pick
    (fun q => (conjBy q (bigElt ruEArr xList k), conjBy q (bigElt ruEArr xList k')))
    (fun x y => eqA 4060 x.1 y.1 && eqA 4060 x.2 y.2)
    (H := centralizer ({ruBigElt k} : Set _) ⊓ centralizer ({ruBigElt k'} : Set _))
    (fun q hq q' hq' hH => by
      have e1 : eqA 4060 (conjBy q (bigElt ruEArr xList k)) (conjBy q' (bigElt ruEArr xList k)) =
          true := (eqA_iff (rep_conjBy h hq ha) (rep_conjBy h hq' ha)).2
            (conj_eq_of_mem_centralizer (mem_inf.1 hH).1).symm
      have e2 : eqA 4060 (conjBy q (bigElt ruEArr xList k')) (conjBy q' (bigElt ruEArr xList k')) =
          true := (eqA_iff (rep_conjBy h hq hb) (rep_conjBy h hq' hb)).2
            (conj_eq_of_mem_centralizer (mem_inf.1 hH).2).symm
      dsimp only
      rw [e1, e2]
      rfl) hpk
  have := hle _ (le_inf (centralizer_le (Set.singleton_subset_iff.2 haE))
    (centralizer_le (Set.singleton_subset_iff.2 hbE)))
  omega


end CFSG.Sporadic.RuSchreier
