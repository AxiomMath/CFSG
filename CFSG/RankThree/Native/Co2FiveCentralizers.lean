module

public import CFSG.RankThree.Native.Co2FiveCheck

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Co2Cert CFSG.Monster.B.Mathieu
open scoped commutatorElement

theorem rep_co2FiveLine (j : Fin 31) :
    Rep 2300 (co2FiveLineArr j) (co2FiveLine j) :=
  co2Five_structures.line_rep j

theorem co2FiveQ_spec :
    (∀ x, x ∈ co2FiveQ ↔ ∃ k < co2FiveQCert.pts.size,
      permOfArr 2300 co2FiveQCert.pts[k]! = x) ∧
    Nat.card co2FiveQ = 125 ∧ ∀ k < co2FiveQCert.pts.size,
      Rep 2300 co2FiveQCert.pts[k]! (permOfArr 2300 co2FiveQCert.pts[k]!) :=
  ⟨co2Five_structures.q_enum, co2Five_structures.card_Q, co2Five_structures.q_rep⟩

theorem co2FiveQ_le_P :
    co2FiveQ ≤ co2P :=
  co2Five_structures.q_le_P

theorem card_co2FiveQ : Nat.card co2FiveQ = 125 :=
  co2Five_structures.card_Q

theorem exponent_co2FiveQ : Monoid.exponent co2FiveQ = 5 :=
  co2Five_structures.exponent_Q

theorem co2FiveQ_pow_five {g : Equiv.Perm (Fin 2300)}
    (hg : g ∈ co2FiveQ) : g ^ 5 = 1 := by
  have h := Monoid.pow_exponent_eq_one (⟨g, hg⟩ : co2FiveQ)
  rw [exponent_co2FiveQ] at h
  exact congrArg Subtype.val h

theorem co2FiveQ_lines :
    {H : Subgroup (Equiv.Perm (Fin 2300)) | H ≤ co2FiveQ ∧ Nat.card H = 5} =
        Set.range (fun j : Fin 31 => Subgroup.zpowers (co2FiveLine j)) ∧
      Function.Injective (fun j : Fin 31 => Subgroup.zpowers (co2FiveLine j)) :=
  co2Five_structures.lines

theorem zpowers_co2FiveLine_mem (j : Fin 31) :
    Subgroup.zpowers (co2FiveLine j) ≤ co2FiveQ ∧ Nat.card (Subgroup.zpowers (co2FiveLine j)) = 5 := by
  have h : Subgroup.zpowers (co2FiveLine j) ∈
      {H : Subgroup (Equiv.Perm (Fin 2300)) | H ≤ co2FiveQ ∧ Nat.card H = 5} := by
    rw [co2FiveQ_lines.1]
    exact ⟨j, rfl⟩
  exact h

theorem co2FiveLine_mem_Q (j : Fin 31) : co2FiveLine j ∈ co2FiveQ :=
  (zpowers_co2FiveLine_mem j).1 (Subgroup.mem_zpowers _)

theorem orderOf_co2FiveLine (j : Fin 31) :
    orderOf (co2FiveLine j) = 5 := by
  rw [← Nat.card_zpowers]
  exact (zpowers_co2FiveLine_mem j).2

theorem factorization_card_co2P_five :
    (Nat.card co2P).factorization 5 = 3 := by
  rw [card_co2P, show (42305421312000 : ℕ) = 5 ^ 3 * 338443370496 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem co2FiveTransporter_spec
    (j : Fin 31) :
    co2FiveTransporter j ∈ co2P ∧
      co2FiveTransporter j * co2FiveLine (co2FiveRepLine (co2FiveRecordOf j)) *
        (co2FiveTransporter j)⁻¹ = co2FiveLine j :=
  co2Five_structures.transporter j

theorem co2FiveRecordOf_eq_zero_iff (j : Fin 31) : co2FiveRecordOf j = 0 ↔ (j : ℕ) = 0 := by
  unfold co2FiveRecordOf
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

theorem co2FiveC0_eq :
    co2FiveC0 = Subgroup.centralizer {co2FiveLine 0} ⊓ co2P :=
  co2Five_structures.c0_eq

theorem co2FiveC0_le_centralizer :
    co2FiveC0 ≤ Subgroup.centralizer {co2FiveLine 0} := by
  rw [co2Five_structures.c0_eq]
  exact inf_le_left

theorem card_co2FiveC0 : Nat.card co2FiveC0 = 3000 :=
  co2Five_structures.card_C0

theorem co2FiveC0_exists_rep {x : Equiv.Perm (Fin 2300)}
    (hx : x ∈ co2FiveC0) : ∃ i < co2FiveC0Cert.pts.size, Rep 2300 co2FiveC0Cert.pts[i]! x := by
  obtain ⟨i, hi, rfl⟩ := (co2Five_structures.c0_enum x).1 hx
  exact ⟨i, hi, co2Five_structures.c0_rep i hi⟩

theorem co2FiveAGenArrs_eq : co2FiveAGenArrs = co2FiveQGenArrs := rfl

theorem co2FiveA_eq_Q : co2FiveA = co2FiveQ := by
  rw [co2FiveA, co2FiveQ, co2FiveAGenArrs_eq]

theorem co2FiveA_le_C0 : co2FiveA ≤ co2FiveC0 :=
  co2Five_structures.a_le_C0

theorem co2FiveA_normal : (co2FiveA.subgroupOf co2FiveC0).Normal :=
  co2Five_structures.a_normal

theorem card_co2FiveA : Nat.card co2FiveA = 125 := by
  rw [co2FiveA_eq_Q]
  exact card_co2FiveQ

theorem exponent_co2FiveA : Monoid.exponent co2FiveA = 5 := by
  rw [co2FiveA_eq_Q]
  exact exponent_co2FiveQ

theorem co2FiveCentA_eq :
    Subgroup.centralizer (co2FiveA : Set (Equiv.Perm (Fin 2300))) ⊓ co2FiveC0 =
      Subgroup.zpowers (co2FiveLine 0) :=
  co2Five_structures.centA_eq

theorem card_co2FiveCentA :
    Nat.card (Subgroup.centralizer (co2FiveA : Set (Equiv.Perm (Fin 2300))) ⊓ co2FiveC0 :
      Subgroup (Equiv.Perm (Fin 2300))) = 5 := by
  rw [co2FiveCentA_eq, Nat.card_zpowers, orderOf_co2FiveLine]

theorem co2FiveCentA_le_A :
    Subgroup.centralizer (co2FiveA : Set (Equiv.Perm (Fin 2300))) ⊓ co2FiveC0 ≤ co2FiveA := by
  rw [co2FiveCentA_eq, Subgroup.zpowers_le, co2FiveA_eq_Q]
  exact co2FiveLine_mem_Q 0

theorem co2FiveC1_eq :
    co2FiveC1 = Subgroup.centralizer {co2FiveLine 1} ⊓ co2P :=
  co2Five_structures.c1_eq

theorem card_co2FiveC1 : Nat.card co2FiveC1 = 600 :=
  co2Five_structures.card_C1

theorem card_co2FiveD : Nat.card co2FiveD = 60 :=
  co2Five_structures.card_D

theorem co2FiveD_isSimpleGroup : IsSimpleGroup co2FiveD :=
  co2Five_structures.d_simple

theorem co2FiveD_nonabelian :
    ∃ g ∈ co2FiveD, ∃ h ∈ co2FiveD, g * h ≠ h * g :=
  co2Five_structures.d_nonabelian

theorem co2FiveD_le_C1 : co2FiveD ≤ co2FiveC1 := by
  rw [co2FiveD, Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact co2FiveC1.mul_mem (co2FiveC1.mul_mem (co2FiveC1.mul_mem ha hb) (co2FiveC1.inv_mem ha))
    (co2FiveC1.inv_mem hb)

theorem co2FiveCentD_eq :
    Subgroup.centralizer (co2FiveD : Set (Equiv.Perm (Fin 2300))) ⊓ co2FiveC1 =
      Subgroup.zpowers (co2FiveLine 1) :=
  co2Five_structures.centD_eq

theorem card_co2FiveCentD :
    Nat.card (Subgroup.centralizer (co2FiveD : Set (Equiv.Perm (Fin 2300))) ⊓ co2FiveC1 :
      Subgroup (Equiv.Perm (Fin 2300))) = 5 := by
  rw [co2FiveCentD_eq, Nat.card_zpowers, orderOf_co2FiveLine]

theorem R3E_Co2_full_five_centralizer_structures :
    (co2FiveQ ≤ co2P ∧ (∃ S : Sylow 5 co2P, (S : Subgroup co2P) = co2FiveQ.subgroupOf co2P) ∧
      Nat.card co2FiveQ = 125 ∧ Monoid.exponent co2FiveQ = 5) ∧
    ({H : Subgroup (Equiv.Perm (Fin 2300)) | H ≤ co2FiveQ ∧ Nat.card H = 5} =
        Set.range (fun j : Fin 31 => Subgroup.zpowers (co2FiveLine j)) ∧
      Function.Injective (fun j : Fin 31 => Subgroup.zpowers (co2FiveLine j))) ∧
    (∀ j : Fin 31, co2FiveTransporter j ∈ co2P ∧
      co2FiveTransporter j * co2FiveLine (co2FiveRepLine (co2FiveRecordOf j)) *
        (co2FiveTransporter j)⁻¹ = co2FiveLine j) ∧
    (∀ j : Fin 31, co2FiveRecordOf j = 0 ↔ (j : ℕ) = 0) ∧
    co2FiveC0 = Subgroup.centralizer {co2FiveLine 0} ⊓ co2P ∧ Nat.card co2FiveC0 = 3000 ∧
    co2FiveA ≤ co2FiveC0 ∧ (co2FiveA.subgroupOf co2FiveC0).Normal ∧
    Nat.card co2FiveA = 125 ∧ Monoid.exponent co2FiveA = 5 ∧
    Nat.card (Subgroup.centralizer (co2FiveA : Set (Equiv.Perm (Fin 2300))) ⊓ co2FiveC0 :
      Subgroup (Equiv.Perm (Fin 2300))) = 5 ∧
    Subgroup.centralizer (co2FiveA : Set (Equiv.Perm (Fin 2300))) ⊓ co2FiveC0 ≤ co2FiveA ∧
    co2FiveC1 = Subgroup.centralizer {co2FiveLine 1} ⊓ co2P ∧ Nat.card co2FiveC1 = 600 ∧
    IsSimpleGroup co2FiveD ∧ (∃ g ∈ co2FiveD, ∃ h ∈ co2FiveD, g * h ≠ h * g) ∧
    Nat.card co2FiveD = 60 ∧
    Subgroup.centralizer (co2FiveD : Set (Equiv.Perm (Fin 2300))) ⊓ co2FiveC1 =
      Subgroup.zpowers (co2FiveLine 1) ∧
    Nat.card (Subgroup.centralizer (co2FiveD : Set (Equiv.Perm (Fin 2300))) ⊓ co2FiveC1 :
      Subgroup (Equiv.Perm (Fin 2300))) = 5 :=
  ⟨⟨co2FiveQ_le_P, co2Five_structures.q_sylow, card_co2FiveQ, exponent_co2FiveQ⟩,
    co2FiveQ_lines, co2FiveTransporter_spec, co2FiveRecordOf_eq_zero_iff, co2FiveC0_eq,
    card_co2FiveC0, co2FiveA_le_C0, co2FiveA_normal, card_co2FiveA, exponent_co2FiveA,
    card_co2FiveCentA, co2FiveCentA_le_A, co2FiveC1_eq, card_co2FiveC1, co2FiveD_isSimpleGroup,
    co2FiveD_nonabelian, card_co2FiveD, co2FiveCentD_eq, card_co2FiveCentD⟩

end CFSG.RankThree.Native
