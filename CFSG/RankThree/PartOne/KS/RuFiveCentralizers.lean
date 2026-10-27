module

public import CFSG.RankThree.PartOne.KS.RuFiveCheck
public import CFSG.RankThree.Native.HSMcLFiveCentralizers

public noncomputable section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.Sporadic.Schreier
  CFSG.RankThree.Native CFSG.Sporadic.RuSchreier
open scoped commutatorElement

section Generic

variable {n : ℕ}

theorem originalSubgroup_ofArrays_two {S : Array (Array ℕ)} {hn : 1 ≤ n} {hk : 2 ≤ S.size}
    {bs : List (Fin n)} {hb : bs.Nodup} {W' : Array (List ℤ)}
    (hc : rawChainOK n (S.extract 0 2) S (bs.map Fin.val).toArray W' 1 = true)
    {a b : Array ℕ} {A B : Equiv.Perm (Fin n)} (ha : Rep n a A) (hb' : Rep n b B)
    (e0 : eqA n S[0]! a = true) (e1 : eqA n S[1]! b = true) :
    (RawSchreierDatum.ofArrays n hn S 2 hk bs hb W').originalSubgroup =
      Subgroup.closure {A, B} := by
  have hinv := (chainCheckFacts hc).strong_inv
  have hrep : ∀ j < S.size, Rep n S[j]! (permOfArr n S[j]!) := fun j hj =>
    (rep_permOfArr (hinv j hj)).1
  have g0 : permOfArr n S[0]! = A := eq_of_eqA (hrep 0 (by omega)) ha e0
  have g1 : permOfArr n S[1]! = B := eq_of_eqA (hrep 1 (by omega)) hb' e1
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl g0
    · exact Or.inr g1
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, g0⟩
    · exact ⟨1, by norm_num, g1⟩

theorem case_centralizer2 {S : Array (Array ℕ)} (hn : 1 ≤ n) (hk : 2 ≤ S.size)
    {bs : List (Fin n)} (hb : bs.Nodup) {W : Array (List ℤ)} {a b : Array ℕ}
    {A B : Equiv.Perm (Fin n)} (ha : Rep n a A) (hb' : Rep n b B)
    (hchain : caseChainOK2 n S (bs.map Fin.val).toArray W a b = true) {x : Array ℕ}
    {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {rels : List (ℕ × ℕ × ℕ)}
    {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} {N : ℕ} (hps : ∀ p ∈ ps, p < n)
    (hcent : centOK n S (bs.map Fin.val).toArray x rels gs ps c N = true) :
    closure (permsA n gs) = centralizer {X} ⊓ closure {A, B} ∧
      Nat.card (closure (permsA n gs)) = N := by
  simp only [caseChainOK2, Bool.and_eq_true] at hchain
  obtain ⟨⟨hc, e0⟩, e1⟩ := hchain
  simp only [centOK, Bool.and_eq_true, beq_iff_eq] at hcent
  obtain ⟨⟨⟨⟨⟨hrels, hC⟩, hsize⟩, hcomm⟩, hsift⟩, htail⟩ := hcent
  have hA : ChainArrays (RawSchreierDatum.ofArrays n hn S 2 hk bs hb W) (S.extract 0 2) S
      (bs.map Fin.val).toArray W := chainArrays_ofArrays (chainCheckFacts hc).strong_inv
  have horig := originalSubgroup_ofArrays_two (hn := hn) (hk := hk) (hb := hb) hc ha hb' e0 e1
  refine ⟨?_, (enumOK_spec hps hC).2.1.trans hsize⟩
  rw [← horig]
  exact centralizer_eq_of_ptailOK hA hc hx hrels hps hC hcomm hsift htail

end Generic

theorem ruFiveKeys_lt : ∀ p ∈ ruFiveKeys, p < 4060 := by decide

theorem ruFive_case0_chain : rawChainOK 4060 (ruCase0Arrs.extract 0 2) ruCase0Arrs ruCase0BaseArr
    ruCase0Words 1 = true := by
  have h := ruFive_case0_check.1
  simp only [caseChainOK2, Bool.and_eq_true] at h
  exact h.1.1

theorem rep_ruA0' : Rep 4060 (ruArr4060 0) ruA0 := rep_of_validA ruFive_case0_check.2.2.1

theorem rep_ruA1' : Rep 4060 (ruArr4060 1) ruA1 := rep_of_validA ruFive_case0_check.2.2.2.1

theorem ruCase0ChainArrays :
    ChainArrays ruCase0Chain (ruCase0Arrs.extract 0 2) ruCase0Arrs ruCase0BaseArr ruCase0Words :=
  chainArrays_ofArrays (chainCheckFacts ruFive_case0_chain).strong_inv

theorem ruP_eq_original : ruP = ruCase0Chain.originalSubgroup := by
  have h := ruFive_case0_check.1
  simp only [caseChainOK2, Bool.and_eq_true] at h
  exact (originalSubgroup_ofArrays_two ruFive_case0_chain rep_ruA0' rep_ruA1' h.1.2 h.2).symm

theorem mem_ruP_of_sift {g : Array ℕ} {G : Equiv.Perm (Fin 4060)} (hG : Rep 4060 g G)
    (h : siftA 4060 ruPLevels ruCase0BaseArr 0 g = true) : G ∈ ruP := by
  rw [ruP_eq_original]
  exact mem_of_siftA ruCase0ChainArrays ruFive_case0_chain hG h

theorem card_ruP_five : Nat.card ruP = 145926144000 := by
  rw [ruP_eq_original, card_originalSubgroup_of_chainOK ruCase0ChainArrays (by norm_num)
    ruFive_case0_chain, ruFive_case0_check.2.1]
  rfl

theorem ruFive_lines_ok :
    linesOK 4060 ruFiveQGens ruFiveKeys ruFiveQCert ruFiveLines = true := ruFive_Q_check.1

theorem rep_ruFiveLine (j : Fin 31) : Rep 4060 ruFiveLines[(j : ℕ)]! (ruFiveLine j) :=
  linesOK_rep ruFive_lines_ok j

theorem ruFiveQ_le_P : ruFiveQ ≤ ruP := by
  rw [ruFiveQ, closure_le]
  rintro _ ⟨l, hl, rfl⟩
  have hv := enumOK_gens_valid (linesOK_parts ruFive_lines_ok).1 hl
  exact mem_ruP_of_sift (rep_of_validA hv) (allLt_spec ruFive_Q_check.2.1 hl)

theorem card_ruFiveQ : Nat.card ruFiveQ = 125 :=
  linesOK_card ruFiveKeys_lt ruFive_lines_ok

theorem factorization_card_ruP_five : (Nat.card ruP).factorization 5 = 3 := by
  rw [card_ruP_five, show (145926144000 : ℕ) = 5 ^ 3 * 1167409152 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem ruFiveQ_sylow :
    ∃ S : Sylow 5 ruP, (S : Subgroup ruP) = ruFiveQ.subgroupOf ruP := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card (ruFiveQ.subgroupOf ruP) = 5 ^ (Nat.card ruP).factorization 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe ruFiveQ_le_P).toEquiv, card_ruFiveQ,
      factorization_card_ruP_five]
    norm_num
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem ruFiveTransporter_spec (j : Fin 31) :
    ruFiveTransporter j ∈ ruP ∧
      ruFiveTransporter j * ruFiveLine (ruFiveRecordOf j) * (ruFiveTransporter j)⁻¹ =
        ruFiveLine j := by
  have h := allLt_spec ruFive_Q_check.2.2.1 j.2
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hv, hs⟩, he⟩ := h
  refine ⟨mem_ruP_of_sift (rep_of_validA hv) hs, ?_⟩
  exact eq_of_eqA (rep_conjA hv (rep_ruFiveLine (ruFiveRecordOf j))) (rep_ruFiveLine j) he

theorem ruFiveRecordOf_mem (j : Fin 31) : (ruFiveRecordOf j : ℕ) ∈ ({0, 1} : Finset ℕ) := by
  have h := allLt_spec ruFive_Q_check.2.2.2.2.2 j.2
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  change ruFiveRec.getD j 0 % 31 ∈ ({0, 1} : Finset ℕ)
  rcases h with h | h <;> rw [h] <;> decide

theorem ruFiveRecordOf_reps : ruFiveRecordOf 0 = 0 ∧ ruFiveRecordOf 1 = 1 := by
  obtain ⟨-, -, -, h0, h1, -⟩ := ruFive_Q_check
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩
  · change ruFiveRec.getD 0 0 % 31 = 0
    rw [h0]
  · change ruFiveRec.getD 1 0 % 31 = 1
    rw [h1]

theorem ruFiveC0_spec :
    ruFiveC0 = centralizer {ruFiveLine 0} ⊓ ruP ∧ Nat.card ruFiveC0 = 1000 := by
  have h := case_centralizer2 (by norm_num) (by simp [ruCase0Arrs]) (by decide)
    rep_ruA0' rep_ruA1' ruFive_case0_check.1 (rep_ruFiveLine 0) ruFiveKeys_lt
    ruFive_case0_check.2.2.2.2.1
  exact h

theorem ruFiveC1_spec :
    ruFiveC1 = centralizer {ruFiveLine 1} ⊓ ruP ∧ Nat.card ruFiveC1 = 300 := by
  have h := case_centralizer2 (by norm_num) (by simp [ruCase1Arrs]) (by decide)
    rep_ruA0' rep_ruA1' ruFive_case1_check.1 (rep_ruFiveLine 1) ruFiveKeys_lt
    ruFive_case1_check.2.1
  exact h

theorem ruFiveC0_enum : enumOK 4060 ruFiveC0Gens ruFiveKeys ruFiveC0Cert = true := by
  have h := ruFive_case0_check.2.2.2.2.1
  simp only [centOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem ruFiveC1_enum : enumOK 4060 ruFiveC1Gens ruFiveKeys ruFiveC1Cert = true := by
  have h := ruFive_case1_check.2.1
  simp only [centOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem ruFiveA0_spec :
    ruFiveA0 ≤ ruFiveC0 ∧ (ruFiveA0.subgroupOf ruFiveC0).Normal ∧ ruFiveA0 ≤ ruP ∧
      Nat.card ruFiveA0 = 125 ∧ Monoid.exponent ruFiveA0 = 5 ∧
      Nat.card (centralizer (ruFiveA0 : Set (Equiv.Perm (Fin 4060))) ⊓ ruFiveC0 :
        Subgroup (Equiv.Perm (Fin 4060))) = 5 ∧
      centralizer (ruFiveA0 : Set (Equiv.Perm (Fin 4060))) ⊓ ruFiveC0 ≤ ruFiveA0 := by
  obtain ⟨hAe, -, hle, hnorm, hP, hcard, hexp⟩ := normal_five ruFiveKeys_lt
    ruFiveC0_enum ruFive_case0_check.2.2.2.2.2.1 mem_ruP_of_sift (by norm_num)
  have hz := ruFive_case0_check.2.2.2.2.2.2.1
  simp only [zCentOK, Bool.and_eq_true] at hz
  have hxC : ruFiveLine 0 ∈ ruFiveC0 :=
    mem_of_gen_zero (rep_ruFiveLine 0) (by simp [ruFiveC0Gens])
      (enumOK_gens_valid ruFiveC0_enum (by simp [ruFiveC0Gens]))
      ruFive_case0_check.2.2.2.2.2.2.2
  have hxA : ruFiveLine 0 ∈ ruFiveA0 :=
    enumOK_mem_of_any ruFiveKeys_lt hAe (rep_ruFiveLine 0) hz.1
  have hxcent : ruFiveLine 0 ∈ centralizer (ruFiveA0 : Set (Equiv.Perm (Fin 4060))) := by
    rw [mem_centralizer_iff]
    intro a ha
    have := (ruFiveC0_spec.1 ▸ hle ha : a ∈ centralizer {ruFiveLine 0} ⊓ ruP)
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 this).1
  have hcent : centralizer (ruFiveA0 : Set (Equiv.Perm (Fin 4060))) ⊓ ruFiveC0 =
      zpowers (ruFiveLine 0) :=
    centralizer_eq_zpowers_kit ruFiveKeys_lt ruFiveC0_enum hAe (rep_ruFiveLine 0) hxC hxcent hz.2
  refine ⟨hle, hnorm, hP, hcard, hexp, ?_, ?_⟩
  · rw [hcent, Nat.card_zpowers]
    exact linesOK_orderOf ruFive_lines_ok 0
  · rw [hcent, zpowers_le]
    exact hxA

theorem ruFiveD1_spec :
    IsSimpleGroup ruFiveD1 ∧ (∃ g ∈ ruFiveD1, ∃ h ∈ ruFiveD1, g * h ≠ h * g) ∧
      Nat.card ruFiveD1 = 60 ∧ ruFiveD1 ≤ ruP ∧
      centralizer (ruFiveD1 : Set (Equiv.Perm (Fin 4060))) ⊓ ruFiveC1 =
        zpowers (ruFiveLine 1) ∧
      Nat.card (centralizer (ruFiveD1 : Set (Equiv.Perm (Fin 4060))) ⊓ ruFiveC1 :
        Subgroup (Equiv.Perm (Fin 4060))) = 5 := by
  have h := ruFive_case1_check.2.2.1
  simp only [derivedOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hDe, hDs⟩, hcv⟩, hdv⟩, hcm⟩, hdm⟩, hb⟩, hnorm⟩, hcomm⟩, hnab⟩,
    hsimple⟩, hcent⟩, hsift⟩ := h
  have hgD : ruFiveDGens = #[commutatorA 4060 ruFiveC1Gens[1]! ruFiveC1Gens[2]!,
      ruFiveC1Gens[2]!] := rfl
  have hD : ruFiveD1 = closure (permsA 4060 ruFiveDGens) :=
    derived_kit ruFiveKeys_lt ruFiveC1_enum hDe (by simp [ruFiveC1Gens]) hgD hcv hdv
      hcm hdm hb hnorm hcomm
  have hDsize : ruFiveDGens.size = 2 := by simp [ruFiveDGens]
  have hrepD : ∀ l < ruFiveDGens.size,
      Rep 4060 ruFiveDGens[l]! (permOfArr 4060 ruFiveDGens[l]!) := fun l hl =>
    rep_of_validA (enumOK_gens_valid hDe hl)
  have hcard : Nat.card ruFiveD1 = 60 := by
    rw [hD]
    exact (enumOK_spec ruFiveKeys_lt hDe).2.1.trans hDs
  have hxC : ruFiveLine 1 ∈ ruFiveC1 :=
    mem_of_gen_zero (rep_ruFiveLine 1) (by simp [ruFiveC1Gens])
      (enumOK_gens_valid ruFiveC1_enum (by simp [ruFiveC1Gens]))
      ruFive_case1_check.2.2.2
  have hDC : ruFiveD1 ≤ ruFiveC1 := by
    rw [ruFiveD1, commutator_le]
    intro a ha b hb'
    rw [commutatorElement_def]
    exact ruFiveC1.mul_mem (ruFiveC1.mul_mem (ruFiveC1.mul_mem ha hb')
      (ruFiveC1.inv_mem ha)) (ruFiveC1.inv_mem hb')
  have hxcent : ruFiveLine 1 ∈ centralizer (ruFiveD1 : Set (Equiv.Perm (Fin 4060))) := by
    rw [mem_centralizer_iff]
    intro a ha
    have := (ruFiveC1_spec.1 ▸ hDC ha : a ∈ centralizer {ruFiveLine 1} ⊓ ruP)
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 this).1
  have hcentD : centralizer (ruFiveD1 : Set (Equiv.Perm (Fin 4060))) ⊓ ruFiveC1 =
      zpowers (ruFiveLine 1) := by
    rw [hD] at hxcent ⊢
    exact centralizer_eq_zpowers_kit ruFiveKeys_lt ruFiveC1_enum hDe
      (rep_ruFiveLine 1) hxC hxcent hcent
  refine ⟨?_, ?_, hcard, ?_, hcentD, ?_⟩
  · rw [hD]
    exact isSimpleGroup_of_conjSimpleOK ruFiveKeys_lt hDe (by rw [hDs]; norm_num) hsimple
  · rw [hD]
    refine ⟨_, subset_closure (mem_permsA (k := 0) (by rw [hDsize]; norm_num)), _,
      subset_closure (mem_permsA (k := 1) (by rw [hDsize]; norm_num)), fun e => ?_⟩
    have := (commA_iff (hrepD 0 (by rw [hDsize]; norm_num))
      (hrepD 1 (by rw [hDsize]; norm_num))).2 e
    rw [hnab] at this
    exact Bool.false_ne_true this
  · rw [hD, closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact mem_ruP_of_sift (hrepD l hl) (allLt_spec hsift hl)
  · rw [hcentD, Nat.card_zpowers]
    exact linesOK_orderOf ruFive_lines_ok 1

theorem R3E_Ru_full_five_centralizer_structures :
    (ruFiveQ ≤ ruP ∧ (∃ S : Sylow 5 ruP, (S : Subgroup ruP) = ruFiveQ.subgroupOf ruP) ∧
      Nat.card ruFiveQ = 125 ∧ Monoid.exponent ruFiveQ = 5) ∧
    ({H : Subgroup (Equiv.Perm (Fin 4060)) | H ≤ ruFiveQ ∧ Nat.card H = 5} =
        Set.range (fun j : Fin 31 => zpowers (ruFiveLine j)) ∧
      Function.Injective (fun j : Fin 31 => zpowers (ruFiveLine j))) ∧
    (∀ j : Fin 31, ruFiveTransporter j ∈ ruP ∧
      ruFiveTransporter j * ruFiveLine (ruFiveRecordOf j) * (ruFiveTransporter j)⁻¹ =
        ruFiveLine j) ∧
    (∀ j : Fin 31, (ruFiveRecordOf j : ℕ) ∈ ({0, 1} : Finset ℕ)) ∧
    (ruFiveRecordOf 0 = 0 ∧ ruFiveRecordOf 1 = 1) ∧
    (ruFiveC0 = centralizer {ruFiveLine 0} ⊓ ruP ∧ Nat.card ruFiveC0 = 1000) ∧
    (ruFiveC1 = centralizer {ruFiveLine 1} ⊓ ruP ∧ Nat.card ruFiveC1 = 300) ∧
    (ruFiveA0 ≤ ruFiveC0 ∧ (ruFiveA0.subgroupOf ruFiveC0).Normal ∧ ruFiveA0 ≤ ruP ∧
      Nat.card ruFiveA0 = 125 ∧ Monoid.exponent ruFiveA0 = 5 ∧
      Nat.card (centralizer (ruFiveA0 : Set (Equiv.Perm (Fin 4060))) ⊓ ruFiveC0 :
        Subgroup (Equiv.Perm (Fin 4060))) = 5 ∧
      centralizer (ruFiveA0 : Set (Equiv.Perm (Fin 4060))) ⊓ ruFiveC0 ≤ ruFiveA0) ∧
    (IsSimpleGroup ruFiveD1 ∧ (∃ g ∈ ruFiveD1, ∃ h ∈ ruFiveD1, g * h ≠ h * g) ∧
      Nat.card ruFiveD1 = 60 ∧ ruFiveD1 ≤ ruP ∧
      centralizer (ruFiveD1 : Set (Equiv.Perm (Fin 4060))) ⊓ ruFiveC1 =
        zpowers (ruFiveLine 1) ∧
      Nat.card (centralizer (ruFiveD1 : Set (Equiv.Perm (Fin 4060))) ⊓ ruFiveC1 :
        Subgroup (Equiv.Perm (Fin 4060))) = 5) :=
  ⟨⟨ruFiveQ_le_P, ruFiveQ_sylow, card_ruFiveQ, linesOK_exponent ruFiveKeys_lt ruFive_lines_ok⟩,
    linesOK_lines ruFiveKeys_lt ruFive_lines_ok, ruFiveTransporter_spec, ruFiveRecordOf_mem,
    ruFiveRecordOf_reps, ruFiveC0_spec, ruFiveC1_spec, ruFiveA0_spec, ruFiveD1_spec⟩

end CFSG.RankThree.PartOne
