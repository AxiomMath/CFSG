module

public import CFSG.RankThree.Native.Co3FiveDefs
public import CFSG.RankThree.Native.Co3FiveCheck
public import CFSG.RankThree.Native.PrimeLines
public import CFSG.Sporadic.Schreier.Co3Order
public import CFSG.Monster.B.Mathieu.SylowSound

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3 CFSG.Monster.B.Mathieu
open scoped commutatorElement

theorem co3FiveKeyPts_lt : ∀ p ∈ co3FiveKeyPts, p < 276 := by decide

theorem mem_co3P_of_sift {g : Array ℕ} {G : Equiv.Perm (Fin 276)} (hG : Rep 276 g G)
    (h : siftA 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3ChainBaseArr 0 g = true) :
    G ∈ co3P :=
  (siftA_iff_mem_originalSubgroup co3ChainArrays (by norm_num) co3Order_check.1 hG).1 h

theorem co3Chain_baseCount : co3Chain.baseCount = 7 := by decide

theorem co3ChainBaseArr_get {m : ℕ} (hm : m < 7) : co3ChainBaseArr[m]! = m := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 := by omega
  all_goals decide

structure Co3FiveChainFacts : Prop where
  sift : ∀ a ∈ co3FiveSiftArrs,
    siftA 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3ChainBaseArr 0 a = true
  z0 : co3FiveZArr[0]! = 0
  z1 : co3FiveZArr[1]! = 1
  z2 : co3FiveZArr[2]! = 2
  z3 : co3FiveZArr[3]! = 3
  fix0 : fixLevCount 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3FiveZArr 0 = 6
  fix1 : fixLevCount 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3FiveZArr 1 = 5
  fix2 : fixLevCount 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3FiveZArr 2 = 2
  fix3 : fixLevCount 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3FiveZArr 3 = 1
  tail : tailOK 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3FiveZArr co3FiveZPows 3 4
    (idA 276) = true
  rels : ∀ r ∈ co3FiveRels, r.2.2 < co3FiveX25PowArrs.size ∧ r.1 < co3ChainBaseArr.size ∧
    r.2.1 < co3ChainBaseArr.size ∧
      (co3FiveX25PowArrs[r.2.2]!)[co3ChainBaseArr[r.1]!]! = co3ChainBaseArr[r.2.1]!
  ptail : ptailOK 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3ChainBaseArr co3FiveX25Arr
    co3FiveX25PowArrs co3FiveRels co3FiveC25Cert.pts.toList 7 0 (idA 276) = true

theorem co3Five_chain_facts : Co3FiveChainFacts := by
  have h := co3Five_chain_check
  simp only [co3FiveChainCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, ⟨⟨⟨h20, h21⟩, h22⟩, h23⟩⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h20, h21, h22, h23, h3, h4, h5, h6, h7, fun r hr => ?_, h9⟩
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h8 r hr
  exact ⟨a, b, c, d⟩

theorem co3Five_sift {a : Array ℕ} (ha : a ∈ co3FiveSiftArrs) :
    siftA 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3ChainBaseArr 0 a = true :=
  co3Five_chain_facts.sift a ha

structure Co3FiveQFacts : Prop where
  enum : enumOK 276 co3FiveQGenArrs co3FiveKeyPts co3FiveQCert = true
  size : co3FiveQCert.pts.size = 125
  pow : allLt 125 (fun k => eqA 276 (powArr 276 co3FiveQCert.pts[k]! 5) (idA 276)) = true
  cover : allLt 125 (fun k => eqA 276 co3FiveQCert.pts[k]! (idA 276) ||
    (List.range 31).any fun j => (List.range 5).any fun e =>
      eqA 276 co3FiveQCert.pts[k]! (powArr 276 co3FiveLines[j]! e)) = true
  dist : allLt 31 (fun j => allLt 31 fun j' => j == j' ||
    allLt 5 fun e => !(eqA 276 co3FiveLines[j]! (powArr 276 co3FiveLines[j']! e))) = true
  lines : allLt 31 (fun j => validA 276 co3FiveLines[j]! &&
    eqA 276 (powArr 276 co3FiveLines[j]! 5) (idA 276) &&
    !(eqA 276 co3FiveLines[j]! (idA 276)) &&
    co3FiveQCert.pts.toList.any (eqA 276 co3FiveLines[j]!)) = true
  hValid : allLt 31 (fun j => validA 276 (co3FiveHArr j)) = true

theorem co3Five_Q_facts : Co3FiveQFacts := by
  have h := co3Five_Q_check
  simp only [co3FiveQCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hE, hS⟩, hP⟩, hC⟩, hD⟩, hL⟩, hH⟩ := h
  exact ⟨hE, hS, hP, hC, hD, hL, hH⟩

theorem co3FiveLines_get {j : ℕ} (hj : j < 31) : co3FiveLines[j]! = co3FiveLineArr j := by
  rw [co3FiveLines, getElem!_pos _ j (by simp [hj]), Array.getElem_ofFn]

theorem co3FiveLine_facts (j : Fin 31) :
    validA 276 (co3FiveLineArr j) = true ∧
    eqA 276 (powArr 276 (co3FiveLineArr j) 5) (idA 276) = true ∧
    eqA 276 (co3FiveLineArr j) (idA 276) = false ∧
    co3FiveQCert.pts.toList.any (eqA 276 (co3FiveLineArr j)) = true := by
  have h := allLt_spec co3Five_Q_facts.lines j.2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [co3FiveLines_get j.2] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem rep_co3FiveLine (j : Fin 31) : Rep 276 (co3FiveLineArr j) (co3FiveLine j) :=
  rep_of_validA (co3FiveLine_facts j).1

theorem co3FiveLineArr_zero : co3FiveLineArr 0 = co3FiveX0Arr := by simp [co3FiveLineArr]

theorem co3FiveLineArr_25 : co3FiveLineArr 25 = co3FiveX25Arr := by simp [co3FiveLineArr]

theorem rep_co3FiveLine_zero : Rep 276 co3FiveX0Arr (co3FiveLine 0) := by
  have h := rep_co3FiveLine 0
  rwa [Fin.val_zero, co3FiveLineArr_zero] at h

theorem rep_co3FiveLine_25 : Rep 276 co3FiveX25Arr (co3FiveLine 25) := by
  have h := rep_co3FiveLine 25
  rwa [show ((25 : Fin 31) : ℕ) = 25 from rfl, co3FiveLineArr_25] at h

theorem co3FiveQ_spec :
    (∀ x, x ∈ co3FiveQ ↔ ∃ k < co3FiveQCert.pts.size,
      permOfArr 276 co3FiveQCert.pts[k]! = x) ∧
    Nat.card co3FiveQ = 125 ∧ ∀ k < co3FiveQCert.pts.size,
      validA 276 co3FiveQCert.pts[k]! = true := by
  obtain ⟨h1, h2, h3⟩ := enumOK_spec co3FiveKeyPts_lt co3Five_Q_facts.enum
  exact ⟨h1, h2.trans co3Five_Q_facts.size, h3⟩

theorem co3FiveQ_elem {x : Equiv.Perm (Fin 276)} (hx : x ∈ co3FiveQ) :
    ∃ k < 125, Rep 276 co3FiveQCert.pts[k]! x := by
  obtain ⟨k, hk, rfl⟩ := (co3FiveQ_spec.1 x).1 hx
  exact ⟨k, co3Five_Q_facts.size ▸ hk, rep_of_validA (co3FiveQ_spec.2.2 k hk)⟩

theorem co3Five_sift_of_mem_gens {gs : Array (Array ℕ)} {k : ℕ} (hk : k < gs.size)
    (hgs : gs.toList ⊆ co3FiveSiftArrs) :
    siftA 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3ChainBaseArr 0 gs[k]! = true := by
  apply co3Five_sift
  apply hgs
  rw [getElem!_pos gs k hk]
  exact Array.getElem_mem_toList hk

theorem co3FiveQGenArrs_sub : co3FiveQGenArrs.toList ⊆ co3FiveSiftArrs := by
  intro a ha
  rw [co3FiveSiftArrs]
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr ha))

theorem co3FiveC25GenArrs_sub : co3FiveC25GenArrs.toList ⊆ co3FiveSiftArrs := by
  intro a ha
  rw [co3FiveSiftArrs]
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr ha)))

theorem co3FiveC0GenArrs_sub : co3FiveC0GenArrs.toList ⊆ co3FiveSiftArrs := by
  intro a ha
  rw [co3FiveSiftArrs]
  simp only [List.mem_append]
  exact Or.inl (Or.inr ha)

theorem co3FiveQ_le_P : co3FiveQ ≤ co3P := by
  rw [co3FiveQ, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact mem_co3P_of_sift (rep_of_validA (enumOK_gens_valid co3Five_Q_facts.enum hk))
    (co3Five_sift_of_mem_gens hk co3FiveQGenArrs_sub)

theorem co3FiveQ_pow_five {g : Equiv.Perm (Fin 276)} (hg : g ∈ co3FiveQ) : g ^ 5 = 1 := by
  obtain ⟨k, hk, hkg⟩ := co3FiveQ_elem hg
  exact (eqA_iff (rep_powArr hkg 5) rep_idA).1 (allLt_spec co3Five_Q_facts.pow hk)

theorem card_co3FiveQ : Nat.card co3FiveQ = 125 := co3FiveQ_spec.2.1

theorem co3FiveLine_mem_Q (j : Fin 31) : co3FiveLine j ∈ co3FiveQ :=
  enumOK_mem_of_any co3FiveKeyPts_lt co3Five_Q_facts.enum (rep_co3FiveLine j)
    (co3FiveLine_facts j).2.2.2

theorem co3FiveLine_ne_one (j : Fin 31) : co3FiveLine j ≠ 1 := fun h => by
  have := (eqA_iff (rep_co3FiveLine j) rep_idA).2 h
  rw [(co3FiveLine_facts j).2.2.1] at this
  exact Bool.false_ne_true this

theorem co3FiveLine_pow_five (j : Fin 31) : co3FiveLine j ^ 5 = 1 :=
  (eqA_iff (rep_powArr (rep_co3FiveLine j) 5) rep_idA).1 (co3FiveLine_facts j).2.1

theorem orderOf_co3FiveLine (j : Fin 31) : orderOf (co3FiveLine j) = 5 :=
  orderOf_eq_prime (co3FiveLine_pow_five j) (co3FiveLine_ne_one j)

theorem exponent_co3FiveQ : Monoid.exponent co3FiveQ = 5 := by
  have hdvd : Monoid.exponent co3FiveQ ∣ 5 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (co3FiveQ_pow_five g.2)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hdvd with h | h
  · exfalso
    have hs := Monoid.exp_eq_one_iff.1 h
    have := congrArg Subtype.val
      (hs.elim (⟨co3FiveLine 0, co3FiveLine_mem_Q 0⟩ : co3FiveQ) 1)
    exact co3FiveLine_ne_one 0 this
  · exact h

theorem factorization_card_co3P_five : (Nat.card co3P).factorization 5 = 3 := by
  rw [card_co3P, show (495766656000 : ℕ) = 5 ^ 3 * 3966133248 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem co3FiveQ_sylow :
    ∃ S : Sylow 5 co3P, (S : Subgroup co3P) = co3FiveQ.subgroupOf co3P := by
  have hcard : Nat.card (co3FiveQ.subgroupOf co3P) = 5 ^ (Nat.card co3P).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe co3FiveQ_le_P).toEquiv, card_co3FiveQ,
      factorization_card_co3P_five]
    norm_num
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem co3FiveQ_lines :
    {H : Subgroup (Equiv.Perm (Fin 276)) | H ≤ co3FiveQ ∧ Nat.card H = 5} =
        Set.range (fun j : Fin 31 => Subgroup.zpowers (co3FiveLine j)) ∧
      Function.Injective (fun j : Fin 31 => Subgroup.zpowers (co3FiveLine j)) := by
  apply prime_subgroups_eq_range co3FiveLine co3FiveLine_mem_Q co3FiveLine_ne_one
    co3FiveLine_pow_five
  · intro g hg hg1
    obtain ⟨k, hk, hkg⟩ := co3FiveQ_elem hg
    have h := allLt_spec co3Five_Q_facts.cover hk
    simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range] at h
    rcases h with h | ⟨j, hj, e, he, hje⟩
    · exact absurd ((eqA_iff hkg rep_idA).1 h) hg1
    · rw [co3FiveLines_get hj] at hje
      exact ⟨⟨j, hj⟩, e, (eqA_iff hkg (rep_powArr (rep_co3FiveLine ⟨j, hj⟩) e)).1 hje⟩
  · intro j j' k hk hjj'
    have h := allLt_spec (allLt_spec co3Five_Q_facts.dist j.2) j'.2
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact Fin.ext h
    · have h' := allLt_spec h hk
      rw [co3FiveLines_get j.2, co3FiveLines_get j'.2, Bool.not_eq_true'] at h'
      have := (eqA_iff (rep_co3FiveLine j) (rep_powArr (rep_co3FiveLine j') k)).2 hjj'
      rw [h'] at this
      exact absurd this Bool.false_ne_true

theorem rep_co3FiveH (j : Fin 31) : Rep 276 (co3FiveHArr j) (co3FiveTransporter j) :=
  rep_of_validA (allLt_spec co3Five_Q_facts.hValid j.2)

theorem co3FiveTransporter_mem_P (j : Fin 31) : co3FiveTransporter j ∈ co3P := by
  refine mem_co3P_of_sift (rep_co3FiveH j) (co3Five_sift ?_)
  rw [co3FiveSiftArrs, List.mem_append]
  exact Or.inr (List.mem_map.2 ⟨j, List.mem_range.2 j.2, rfl⟩)

theorem co3FiveTransporter_eq_one {j : Fin 31} (hj : (j : ℕ) = 0 ∨ (j : ℕ) = 25) :
    co3FiveTransporter j = 1 := by
  rw [co3FiveTransporter, co3FiveHArr, ite_eq_left hj]
  exact permOfArr_eq_of_rep rep_idA

theorem co3FiveTransporter_spec (j : Fin 31) :
    co3FiveTransporter j ∈ co3P ∧
      co3FiveTransporter j * co3FiveLine (co3FiveRecordOf j) * (co3FiveTransporter j)⁻¹ =
        co3FiveLine j := by
  refine ⟨co3FiveTransporter_mem_P j, ?_⟩
  by_cases h25 : (j : ℕ) = 25
  · have hj : j = 25 := Fin.ext h25
    subst hj
    rw [co3FiveTransporter_eq_one (Or.inr rfl)]
    simp [co3FiveRecordOf]
  · have hrec : co3FiveRecordOf j = 0 := by simp [co3FiveRecordOf, h25]
    rw [hrec]
    by_cases h0 : (j : ℕ) = 0
    · have hj : j = 0 := Fin.ext h0
      subst hj
      rw [co3FiveTransporter_eq_one (Or.inl rfl)]
      simp
    · have hne : ¬ ((j : ℕ) = 0 ∨ (j : ℕ) = 25) := by omega
      have hval : validA 276 (co3FiveHArr j) = true := allLt_spec co3Five_Q_facts.hValid j.2
      have hrep := rep_conjA hval rep_co3FiveLine_zero
      have hline : co3FiveLineArr j = conjA 276 (co3FiveHArr j) co3FiveX0Arr := by
        rw [co3FiveLineArr, ite_eq_right h0, ite_eq_right h25]
      have e1 : co3FiveLine j = permOfArr 276 (co3FiveHArr j) * co3FiveLine 0 *
          (permOfArr 276 (co3FiveHArr j))⁻¹ := by
        rw [co3FiveLine, hline]
        exact permOfArr_eq_of_rep hrep
      rw [e1]
      rfl

theorem co3FiveRecordOf_eq_zero_iff (j : Fin 31) : co3FiveRecordOf j = 0 ↔ (j : ℕ) ≠ 25 := by
  unfold co3FiveRecordOf
  split_ifs with h
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h h'⟩
  · exact ⟨fun _ => h, fun _ => rfl⟩

theorem co3FiveRecordOf_eq_25_iff (j : Fin 31) : co3FiveRecordOf j = 25 ↔ (j : ℕ) = 25 := by
  unfold co3FiveRecordOf
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

structure Co3FiveC25Facts : Prop where
  enum : enumOK 276 co3FiveC25GenArrs co3FiveKeyPts co3FiveC25Cert = true
  size : co3FiveC25Cert.pts.size = 1500
  comm : allLt 4 (fun k => commA 276 co3FiveC25GenArrs[k]! co3FiveX25Arr) = true
  aMem : allLt 2 (fun k => co3FiveC25Cert.pts.toList.any (eqA 276 co3FiveAGenArrs[k]!)) = true
  norm : allLt 4 (fun k => allLt 2 fun l => co3FiveQCert.pts.toList.any
    (eqA 276 (conjA 276 co3FiveC25GenArrs[k]! co3FiveAGenArrs[l]!))) = true
  cent : allLt 1500 (fun k => !(commA 276 co3FiveC25Cert.pts[k]! co3FiveAGenArrs[0]! &&
      commA 276 co3FiveC25Cert.pts[k]! co3FiveAGenArrs[1]!) ||
    (List.range 5).any fun e => eqA 276 co3FiveC25Cert.pts[k]! (powArr 276 co3FiveX25Arr e)) =
    true

theorem co3Five_C25_facts : Co3FiveC25Facts := by
  have h := co3Five_C25_check
  simp only [co3FiveC25Check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem co3FiveAGenArrs_eq : co3FiveAGenArrs = co3FiveQGenArrs := rfl

theorem co3FiveA_eq_Q : co3FiveA = co3FiveQ := by
  rw [co3FiveA, co3FiveQ, co3FiveAGenArrs_eq]

theorem rep_c25gen {k : ℕ} (hk : k < 4) :
    Rep 276 co3FiveC25GenArrs[k]! (permOfArr 276 co3FiveC25GenArrs[k]!) :=
  rep_of_validA (enumOK_gens_valid co3Five_C25_facts.enum hk)

theorem rep_co3agen {k : ℕ} (hk : k < 2) :
    Rep 276 co3FiveAGenArrs[k]! (permOfArr 276 co3FiveAGenArrs[k]!) :=
  rep_of_validA (enumOK_gens_valid co3Five_Q_facts.enum hk)

theorem co3FiveC25_le_centralizer : co3FiveC25 ≤ Subgroup.centralizer {co3FiveLine 25} := by
  rw [co3FiveC25, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.2 ((commA_iff (rep_c25gen hk)
    rep_co3FiveLine_25).1 (allLt_spec co3Five_C25_facts.comm hk))

theorem co3FiveC25_le_P : co3FiveC25 ≤ co3P := by
  rw [co3FiveC25, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact mem_co3P_of_sift (rep_c25gen hk) (co3Five_sift_of_mem_gens hk co3FiveC25GenArrs_sub)

theorem card_co3FiveC25 : Nat.card co3FiveC25 = 1500 :=
  (enumOK_spec co3FiveKeyPts_lt co3Five_C25_facts.enum).2.1.trans co3Five_C25_facts.size

theorem rep_co3FiveX25Pow {e : ℕ} (he : e < co3FiveX25PowArrs.size) :
    Rep 276 co3FiveX25PowArrs[e]! (co3FiveLine 25 ^ e) := by
  rw [getElem!_pos co3FiveX25PowArrs e he]
  simp only [co3FiveX25PowArrs, Array.getElem_ofFn]
  exact rep_powArr rep_co3FiveLine_25 e

theorem co3FiveC25_eq : co3FiveC25 = Subgroup.centralizer {co3FiveLine 25} ⊓ co3P := by
  apply le_antisymm (le_inf co3FiveC25_le_centralizer co3FiveC25_le_P)
  intro g hg
  have F := co3Five_chain_facts
  have htail : ptailOK 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3ChainBaseArr
      co3FiveX25Arr co3FiveX25PowArrs co3FiveRels co3FiveC25Cert.pts.toList co3Chain.baseCount 0
        (idA 276) = true := by
    rw [co3Chain_baseCount]
    exact F.ptail
  obtain ⟨e, he, hre⟩ := centralizer_subset_of_ptailOK co3ChainArrays
    (chainCheckFacts co3Order_check.1) co3Chain_valid.1 rep_co3FiveLine_25
    (fun e he => rep_co3FiveX25Pow he) F.rels htail hg
  exact enumOK_mem_of_mem co3FiveKeyPts_lt co3Five_C25_facts.enum hre he

theorem co3FiveLine_25_mem_A : co3FiveLine 25 ∈ co3FiveA := by
  rw [co3FiveA_eq_Q]
  exact co3FiveLine_mem_Q 25

theorem co3FiveA_le_C25 : co3FiveA ≤ co3FiveC25 := by
  rw [co3FiveA, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact enumOK_mem_of_any co3FiveKeyPts_lt co3Five_C25_facts.enum (rep_co3agen hk)
    (allLt_spec co3Five_C25_facts.aMem hk)

theorem co3FiveA_normal : (co3FiveA.subgroupOf co3FiveC25).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer co3FiveA_le_C25, co3FiveC25, co3FiveA]
  apply closure_le_normalizer_closure
  rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
  have h := allLt_spec (allLt_spec co3Five_C25_facts.norm hk) hl
  have hmem := enumOK_mem_of_any co3FiveKeyPts_lt co3Five_Q_facts.enum
    (rep_conjA (enumOK_gens_valid co3Five_C25_facts.enum hk) (rep_co3agen hl)) h
  rwa [← co3FiveAGenArrs_eq] at hmem

theorem card_co3FiveA : Nat.card co3FiveA = 125 := by
  rw [co3FiveA_eq_Q]
  exact card_co3FiveQ

theorem exponent_co3FiveA : Monoid.exponent co3FiveA = 5 := by
  rw [co3FiveA_eq_Q]
  exact exponent_co3FiveQ

theorem co3FiveCentA_eq :
    Subgroup.centralizer (co3FiveA : Set (Equiv.Perm (Fin 276))) ⊓ co3FiveC25 =
      Subgroup.zpowers (co3FiveLine 25) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgA, hgC⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep co3FiveKeyPts_lt co3Five_C25_facts.enum hgC
    rw [co3Five_C25_facts.size] at hk
    have hc : ∀ l < 2, commA 276 co3FiveC25Cert.pts[k]! co3FiveAGenArrs[l]! = true := by
      intro l hl
      have ha : permOfArr 276 co3FiveAGenArrs[l]! ∈ co3FiveA :=
        Subgroup.subset_closure (mem_permsA hl)
      exact (commA_iff hkg (rep_co3agen hl)).2 (Subgroup.mem_centralizer_iff.1 hgA _ ha).symm
    have h := allLt_spec co3Five_C25_facts.cent hk
    rw [hc 0 (by norm_num), hc 1 (by norm_num)] at h
    simp only [Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true,
      List.mem_range] at h
    obtain ⟨e, -, he⟩ := h
    rw [(eqA_iff hkg (rep_powArr rep_co3FiveLine_25 e)).1 he]
    exact Subgroup.npow_mem_zpowers _ e
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun a ha => ?_,
      co3FiveA_le_C25 co3FiveLine_25_mem_A⟩
    exact Subgroup.mem_centralizer_singleton_iff.1
      (co3FiveC25_le_centralizer (co3FiveA_le_C25 ha))

theorem card_co3FiveCentA :
    Nat.card (Subgroup.centralizer (co3FiveA : Set (Equiv.Perm (Fin 276))) ⊓ co3FiveC25 :
      Subgroup (Equiv.Perm (Fin 276))) = 5 := by
  rw [co3FiveCentA_eq, Nat.card_zpowers, orderOf_co3FiveLine]

theorem co3FiveCentA_le_A :
    Subgroup.centralizer (co3FiveA : Set (Equiv.Perm (Fin 276))) ⊓ co3FiveC25 ≤ co3FiveA := by
  rw [co3FiveCentA_eq, Subgroup.zpowers_le]
  exact co3FiveLine_25_mem_A

structure Co3FiveC0Facts : Prop where
  cEnum : enumOK 276 co3FiveC0GenArrs co3FiveKeyPts co3FiveC0Cert = true
  cSize : co3FiveC0Cert.pts.size = 300
  dEnum : enumOK 276 co3FiveDGenArrs co3FiveKeyPts co3FiveDCert = true
  dSize : co3FiveDCert.pts.size = 60
  commX : allLt 3 (fun k => commA 276 co3FiveC0GenArrs[k]! co3FiveX0Arr) = true
  gValid : validA 276 co3FiveGArr = true
  kValid : validA 276 co3FiveKArr = true
  gMem : co3FiveC0Cert.pts.toList.any (eqA 276 co3FiveGArr) = true
  kMem : co3FiveC0Cert.pts.toList.any (eqA 276 co3FiveKArr) = true
  bComm : eqA 276 co3FiveC0GenArrs[2]! (commutatorA 276 co3FiveGArr co3FiveKArr) = true
  norm : allLt 3 (fun k => allLt 2 fun l => co3FiveDCert.pts.toList.any
    (eqA 276 (conjA 276 co3FiveC0GenArrs[k]! co3FiveDGenArrs[l]!))) = true
  comm : allLt 3 (fun k => allLt 3 fun l => co3FiveDCert.pts.toList.any
    (eqA 276 (commutatorA 276 co3FiveC0GenArrs[k]! co3FiveC0GenArrs[l]!))) = true
  nonab : commA 276 co3FiveDGenArrs[0]! co3FiveDGenArrs[1]! = false
  simple : conjSimpleOK 276 co3FiveKeyPts co3FiveDCert = true
  cent : allLt 300 (fun k => !(commA 276 co3FiveC0Cert.pts[k]! co3FiveDGenArrs[0]! &&
      commA 276 co3FiveC0Cert.pts[k]! co3FiveDGenArrs[1]!) ||
    (List.range 5).any fun e => eqA 276 co3FiveC0Cert.pts[k]! (powArr 276 co3FiveX0Arr e)) =
    true
  tValid : validA 276 co3FiveTArr = true

theorem co3Five_C0_facts : Co3FiveC0Facts := by
  have h := co3Five_C0_check
  simp only [co3FiveC0Check, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem valid_c0gen {k : ℕ} (hk : k < 3) : validA 276 co3FiveC0GenArrs[k]! = true :=
  enumOK_gens_valid co3Five_C0_facts.cEnum hk

theorem rep_c0gen3 {k : ℕ} (hk : k < 3) :
    Rep 276 co3FiveC0GenArrs[k]! (permOfArr 276 co3FiveC0GenArrs[k]!) :=
  rep_of_validA (valid_c0gen hk)

theorem rep_co3dgen {l : ℕ} (hl : l < 2) :
    Rep 276 co3FiveDGenArrs[l]! (permOfArr 276 co3FiveDGenArrs[l]!) :=
  rep_of_validA (enumOK_gens_valid co3Five_C0_facts.dEnum hl)

theorem co3FiveC0GenArrs_zero : co3FiveC0GenArrs[0]! = co3FiveX0Arr := by
  simp [co3FiveC0GenArrs]

theorem c0gen_zero : permOfArr 276 co3FiveC0GenArrs[0]! = co3FiveLine 0 := by
  rw [co3FiveC0GenArrs_zero]
  exact permOfArr_eq_of_rep rep_co3FiveLine_zero

theorem c0gen_mem {k : ℕ} (hk : k < 3) : permOfArr 276 co3FiveC0GenArrs[k]! ∈ co3FiveC0 :=
  Subgroup.subset_closure (mem_permsA hk)

theorem co3FiveLine_zero_mem_C0 : co3FiveLine 0 ∈ co3FiveC0 := by
  rw [← c0gen_zero]
  exact c0gen_mem (by norm_num)

theorem co3FiveC0_le_centralizer : co3FiveC0 ≤ Subgroup.centralizer {co3FiveLine 0} := by
  rw [co3FiveC0, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.2 ((commA_iff (rep_c0gen3 hk)
    rep_co3FiveLine_zero).1 (allLt_spec co3Five_C0_facts.commX hk))

theorem co3FiveC0_le_P : co3FiveC0 ≤ co3P := by
  rw [co3FiveC0, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact mem_co3P_of_sift (rep_c0gen3 hk) (co3Five_sift_of_mem_gens hk co3FiveC0GenArrs_sub)

theorem card_co3FiveC0 : Nat.card co3FiveC0 = 300 :=
  (enumOK_spec co3FiveKeyPts_lt co3Five_C0_facts.cEnum).2.1.trans co3Five_C0_facts.cSize

theorem rep_co3FiveZ : Rep 276 co3FiveZArr (permOfArr 276 co3FiveTArr * co3FiveLine 0 *
    (permOfArr 276 co3FiveTArr)⁻¹) :=
  rep_conjA co3Five_C0_facts.tValid rep_co3FiveLine_zero

theorem co3FiveT_mem_P : permOfArr 276 co3FiveTArr ∈ co3P :=
  mem_co3P_of_sift (rep_of_validA co3Five_C0_facts.tValid) (co3Five_sift (by
    rw [co3FiveSiftArrs]
    simp))

theorem co3FiveZ_fix {p : Fin 276} (hp : co3FiveZArr[(p : ℕ)]! = p) :
    (permOfArr 276 co3FiveTArr * co3FiveLine 0 * (permOfArr 276 co3FiveTArr)⁻¹) p = p :=
  Fin.ext ((rep_co3FiveZ p).symm.trans hp)

theorem card_centralizer_co3FiveZ_le :
    Nat.card (Subgroup.centralizer {permOfArr 276 co3FiveTArr * co3FiveLine 0 *
      (permOfArr 276 co3FiveTArr)⁻¹} ⊓ co3P : Subgroup _) ≤ 300 := by
  have hA := co3ChainArrays
  have hF := chainCheckFacts co3Order_check.1
  have hQ := co3Chain_valid.1
  have F := co3Five_chain_facts
  have hbc : co3Chain.baseCount = 7 := co3Chain_baseCount
  have hb : ∀ (m : ℕ) (hm : m < co3Chain.baseCount), ((co3Chain.base.get ⟨m, hm⟩ : Fin 276) : ℕ) =
      co3ChainBaseArr[m]! := fun m hm => hA.base_val ⟨m, hm⟩
  have hbase : ∀ (m : ℕ) (hm : m < co3Chain.baseCount), m < 4 →
      (permOfArr 276 co3FiveTArr * co3FiveLine 0 * (permOfArr 276 co3FiveTArr)⁻¹)
        (co3Chain.base.get ⟨m, hm⟩) = co3Chain.base.get ⟨m, hm⟩ := by
    intro m hm hm4
    apply co3FiveZ_fix
    rw [hb m hm, co3ChainBaseArr_get (by omega)]
    obtain rfl | rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
    · exact F.z0
    · exact F.z1
    · exact F.z2
    · exact F.z3
  have e0 := card_centralizer_inf_levelSubgroup_le hA hF hQ rep_co3FiveZ (i := 0)
    (by rw [hbc]; norm_num) (hbase 0 _ (by norm_num))
  have e1 := card_centralizer_inf_levelSubgroup_le hA hF hQ rep_co3FiveZ (i := 1)
    (by rw [hbc]; norm_num) (hbase 1 _ (by norm_num))
  have e2 := card_centralizer_inf_levelSubgroup_le hA hF hQ rep_co3FiveZ (i := 2)
    (by rw [hbc]; norm_num) (hbase 2 _ (by norm_num))
  have e3 := card_centralizer_inf_levelSubgroup_le hA hF hQ rep_co3FiveZ (i := 3)
    (by rw [hbc]; norm_num) (hbase 3 _ (by norm_num))
  have htail : tailOK 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3FiveZArr co3FiveZPows
      (co3Chain.baseCount - 4) 4 (idA 276) = true := by
    rw [hbc]
    exact F.tail
  have e4 := card_centralizer_inf_levelSubgroup_le_of_tailOK hA hF hQ rep_co3FiveZ (m := 4)
    (by rw [hbc]; norm_num) htail
  have hlen : co3FiveZPows.length = 5 := by simp [co3FiveZPows]
  rw [F.fix0] at e0
  rw [F.fix1] at e1
  rw [F.fix2] at e2
  rw [F.fix3] at e3
  rw [hlen] at e4
  have hP : co3P = co3Chain.levelSubgroup 0 := (co3Chain.levelSubgroup_zero_eq_original hQ).symm
  rw [hP]
  calc _ ≤ 6 * _ := e0
    _ ≤ 6 * (5 * _) := Nat.mul_le_mul_left _ e1
    _ ≤ 6 * (5 * (2 * _)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e2)
    _ ≤ 6 * (5 * (2 * (1 * _))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e3))
    _ ≤ 6 * (5 * (2 * (1 * 5))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e4)))
    _ = 300 := by norm_num

theorem co3FiveC0_eq : co3FiveC0 = Subgroup.centralizer {co3FiveLine 0} ⊓ co3P := by
  apply Subgroup.eq_of_le_of_card_ge (le_inf co3FiveC0_le_centralizer co3FiveC0_le_P)
  rw [card_co3FiveC0, card_centralizer_inf_conj co3P co3FiveT_mem_P rfl]
  exact card_centralizer_co3FiveZ_le

theorem co3FiveDGenArrs_size : co3FiveDGenArrs.size = 2 := by simp [co3FiveDGenArrs]

theorem co3dgen_zero : permOfArr 276 co3FiveDGenArrs[0]! =
    ⁅permOfArr 276 co3FiveC0GenArrs[1]!, permOfArr 276 co3FiveC0GenArrs[2]!⁆ := by
  have e : co3FiveDGenArrs[0]! = commutatorA 276 co3FiveC0GenArrs[1]! co3FiveC0GenArrs[2]! := by
    simp [co3FiveDGenArrs]
  rw [e]
  exact permOfArr_eq_of_rep (rep_commutatorA (valid_c0gen (by norm_num))
    (valid_c0gen (by norm_num)))

theorem co3dgen_one : permOfArr 276 co3FiveDGenArrs[1]! = permOfArr 276 co3FiveC0GenArrs[2]! := by
  have e : co3FiveDGenArrs[1]! = co3FiveC0GenArrs[2]! := by simp [co3FiveDGenArrs]
  rw [e]

theorem co3FiveG_mem_C0 : permOfArr 276 co3FiveGArr ∈ co3FiveC0 :=
  enumOK_mem_of_any co3FiveKeyPts_lt co3Five_C0_facts.cEnum
    (rep_of_validA co3Five_C0_facts.gValid) co3Five_C0_facts.gMem

theorem co3FiveK_mem_C0 : permOfArr 276 co3FiveKArr ∈ co3FiveC0 :=
  enumOK_mem_of_any co3FiveKeyPts_lt co3Five_C0_facts.cEnum
    (rep_of_validA co3Five_C0_facts.kValid) co3Five_C0_facts.kMem

theorem c0gen_two_eq_commutator :
    permOfArr 276 co3FiveC0GenArrs[2]! =
      ⁅permOfArr 276 co3FiveGArr, permOfArr 276 co3FiveKArr⁆ :=
  (eqA_iff (rep_c0gen3 (by norm_num))
    (rep_commutatorA co3Five_C0_facts.gValid co3Five_C0_facts.kValid)).1 co3Five_C0_facts.bComm

theorem co3FiveD_eq : co3FiveD = Subgroup.closure (permsA 276 co3FiveDGenArrs) := by
  have F := co3Five_C0_facts
  have hA : permOfArr 276 co3FiveC0GenArrs[1]! ∈ co3FiveC0 := c0gen_mem (by norm_num)
  have hB : permOfArr 276 co3FiveC0GenArrs[2]! ∈ co3FiveC0 := c0gen_mem (by norm_num)
  rw [co3FiveD]
  conv_lhs => rw [co3FiveC0]
  apply commutator_closure_eq_closure
  · rintro _ ⟨l, hl, rfl⟩
    have hl2 : l < 2 := hl
    obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
    · dsimp only
      rw [co3dgen_zero]
      exact Subgroup.commutator_mem_commutator hA hB
    · dsimp only
      rw [co3dgen_one, c0gen_two_eq_commutator]
      exact Subgroup.commutator_mem_commutator co3FiveG_mem_C0 co3FiveK_mem_C0
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
    exact enumOK_mem_of_any co3FiveKeyPts_lt F.dEnum
      (rep_conjA (valid_c0gen hk) (rep_co3dgen hl)) (allLt_spec (allLt_spec F.norm hk) hl)
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
    exact enumOK_mem_of_any co3FiveKeyPts_lt F.dEnum
      (rep_commutatorA (valid_c0gen hk) (valid_c0gen hl)) (allLt_spec (allLt_spec F.comm hk) hl)

theorem card_co3FiveD : Nat.card co3FiveD = 60 := by
  rw [co3FiveD_eq]
  exact (enumOK_spec co3FiveKeyPts_lt co3Five_C0_facts.dEnum).2.1.trans co3Five_C0_facts.dSize

theorem co3FiveD_isSimpleGroup : IsSimpleGroup co3FiveD := by
  rw [co3FiveD_eq]
  exact isSimpleGroup_of_conjSimpleOK co3FiveKeyPts_lt co3Five_C0_facts.dEnum
    (by rw [co3Five_C0_facts.dSize]; norm_num) co3Five_C0_facts.simple

theorem co3FiveD_nonabelian : ∃ g ∈ co3FiveD, ∃ h ∈ co3FiveD, g * h ≠ h * g := by
  rw [co3FiveD_eq]
  refine ⟨_, Subgroup.subset_closure
    (mem_permsA (k := 0) (by rw [co3FiveDGenArrs_size]; norm_num)), _,
    Subgroup.subset_closure (mem_permsA (k := 1) (by rw [co3FiveDGenArrs_size]; norm_num)),
    fun h => ?_⟩
  have := (commA_iff (rep_co3dgen (by norm_num)) (rep_co3dgen (by norm_num))).2 h
  rw [co3Five_C0_facts.nonab] at this
  exact Bool.false_ne_true this

theorem co3FiveD_le_C0 : co3FiveD ≤ co3FiveC0 := by
  rw [co3FiveD, Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact co3FiveC0.mul_mem (co3FiveC0.mul_mem (co3FiveC0.mul_mem ha hb) (co3FiveC0.inv_mem ha))
    (co3FiveC0.inv_mem hb)

theorem co3FiveCentD_eq :
    Subgroup.centralizer (co3FiveD : Set (Equiv.Perm (Fin 276))) ⊓ co3FiveC0 =
      Subgroup.zpowers (co3FiveLine 0) := by
  have F := co3Five_C0_facts
  apply le_antisymm
  · intro g hg
    obtain ⟨hgD, hgC⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep co3FiveKeyPts_lt F.cEnum hgC
    rw [F.cSize] at hk
    have hc : ∀ l < 2, commA 276 co3FiveC0Cert.pts[k]! co3FiveDGenArrs[l]! = true := by
      intro l hl
      have hd : permOfArr 276 co3FiveDGenArrs[l]! ∈ co3FiveD := by
        rw [co3FiveD_eq]
        exact Subgroup.subset_closure (mem_permsA (by rw [co3FiveDGenArrs_size]; exact hl))
      exact (commA_iff hkg (rep_co3dgen hl)).2 (Subgroup.mem_centralizer_iff.1 hgD _ hd).symm
    have h := allLt_spec F.cent hk
    rw [hc 0 (by norm_num), hc 1 (by norm_num)] at h
    simp only [Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true,
      List.mem_range] at h
    obtain ⟨e, -, he⟩ := h
    rw [(eqA_iff hkg (rep_powArr rep_co3FiveLine_zero e)).1 he]
    exact Subgroup.npow_mem_zpowers _ e
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun d hd => ?_,
      co3FiveLine_zero_mem_C0⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (co3FiveC0_le_centralizer (co3FiveD_le_C0 hd))

theorem card_co3FiveCentD :
    Nat.card (Subgroup.centralizer (co3FiveD : Set (Equiv.Perm (Fin 276))) ⊓ co3FiveC0 :
      Subgroup (Equiv.Perm (Fin 276))) = 5 := by
  rw [co3FiveCentD_eq, Nat.card_zpowers, orderOf_co3FiveLine]

theorem R3E_Co3_full_five_centralizer_structures :
    (co3FiveQ ≤ co3P ∧ (∃ S : Sylow 5 co3P, (S : Subgroup co3P) = co3FiveQ.subgroupOf co3P) ∧
      Nat.card co3FiveQ = 125 ∧ Monoid.exponent co3FiveQ = 5) ∧
    ({H : Subgroup (Equiv.Perm (Fin 276)) | H ≤ co3FiveQ ∧ Nat.card H = 5} =
        Set.range (fun j : Fin 31 => Subgroup.zpowers (co3FiveLine j)) ∧
      Function.Injective (fun j : Fin 31 => Subgroup.zpowers (co3FiveLine j))) ∧
    (∀ j : Fin 31, co3FiveTransporter j ∈ co3P ∧
      co3FiveTransporter j * co3FiveLine (co3FiveRecordOf j) * (co3FiveTransporter j)⁻¹ =
        co3FiveLine j) ∧
    (∀ j : Fin 31, co3FiveRecordOf j = 0 ↔ (j : ℕ) ≠ 25) ∧
    (∀ j : Fin 31, co3FiveRecordOf j = 25 ↔ (j : ℕ) = 25) ∧
    co3FiveC0 = Subgroup.centralizer {co3FiveLine 0} ⊓ co3P ∧ Nat.card co3FiveC0 = 300 ∧
    IsSimpleGroup co3FiveD ∧ (∃ g ∈ co3FiveD, ∃ h ∈ co3FiveD, g * h ≠ h * g) ∧
    Nat.card co3FiveD = 60 ∧
    Subgroup.centralizer (co3FiveD : Set (Equiv.Perm (Fin 276))) ⊓ co3FiveC0 =
      Subgroup.zpowers (co3FiveLine 0) ∧
    Nat.card (Subgroup.centralizer (co3FiveD : Set (Equiv.Perm (Fin 276))) ⊓ co3FiveC0 :
      Subgroup (Equiv.Perm (Fin 276))) = 5 ∧
    co3FiveC25 = Subgroup.centralizer {co3FiveLine 25} ⊓ co3P ∧ Nat.card co3FiveC25 = 1500 ∧
    co3FiveA ≤ co3FiveC25 ∧ (co3FiveA.subgroupOf co3FiveC25).Normal ∧
    Nat.card co3FiveA = 125 ∧ Monoid.exponent co3FiveA = 5 ∧
    Nat.card (Subgroup.centralizer (co3FiveA : Set (Equiv.Perm (Fin 276))) ⊓ co3FiveC25 :
      Subgroup (Equiv.Perm (Fin 276))) = 5 ∧
    Subgroup.centralizer (co3FiveA : Set (Equiv.Perm (Fin 276))) ⊓ co3FiveC25 ≤ co3FiveA :=
  ⟨⟨co3FiveQ_le_P, co3FiveQ_sylow, card_co3FiveQ, exponent_co3FiveQ⟩, co3FiveQ_lines,
    co3FiveTransporter_spec, co3FiveRecordOf_eq_zero_iff, co3FiveRecordOf_eq_25_iff,
    co3FiveC0_eq, card_co3FiveC0, co3FiveD_isSimpleGroup, co3FiveD_nonabelian, card_co3FiveD,
    co3FiveCentD_eq, card_co3FiveCentD, co3FiveC25_eq, card_co3FiveC25, co3FiveA_le_C25,
    co3FiveA_normal, card_co3FiveA, exponent_co3FiveA, card_co3FiveCentA, co3FiveCentA_le_A⟩

end CFSG.RankThree.Native
