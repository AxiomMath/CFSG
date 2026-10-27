module

public import CFSG.RankThree.PartOne.KS.J2FiveCheck
public import CFSG.RankThree.PartOne.KS.Lines
public import CFSG.Sporadic.SmallOddCore.J2

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

@[expose] noncomputable def j2FiveQ : Subgroup (Equiv.Perm (Fin 315)) :=
  Subgroup.closure (permsA 315 j2FiveQGenArrs)

@[expose] noncomputable def j2FiveLine (i : Fin 6) : Equiv.Perm (Fin 315) :=
  permOfArr 315 (j2FiveX i)

@[expose] noncomputable def j2FiveC (i : ℕ) : Subgroup (Equiv.Perm (Fin 315)) :=
  Subgroup.closure (permsA 315 (j2FiveCG i))

@[expose] noncomputable def j2FiveD (i : ℕ) : Subgroup (Equiv.Perm (Fin 315)) :=
  Subgroup.closure (permsA 315 (j2FiveDG i))

theorem j2FiveKeyPts_lt : ∀ p ∈ j2FiveKeyPts, p < 315 := by decide

theorem j2FiveGensR_size : j2FiveGensR.size = 3 := by decide

theorem valid_j2FiveGensR {k : ℕ} (hk : k < 3) : validA 315 j2FiveGensR[k]! = true := by
  have h := j2Five_gensR_valid
  rw [List.all_eq_true] at h
  exact h k (List.mem_range.mpr hk)

theorem j2FiveGensR_zero : j2FiveGensR[0]! = j2StrongArrs[0]! := by simp [j2FiveGensR]

theorem j2FiveGensR_one : j2FiveGensR[1]! = j2StrongArrs[1]! := by simp [j2FiveGensR]

theorem j2FiveGensR_two' : j2FiveGensR[2]! = natArr j2OuterTbl := by simp [j2FiveGensR]

theorem closure_j2FiveGensR : Subgroup.closure (permsA 315 j2FiveGensR) = j2R := by
  have h0 : permOfArr 315 j2FiveGensR[0]! = j2Gen 0 := by rw [j2FiveGensR_zero]; rfl
  have h1 : permOfArr 315 j2FiveGensR[1]! = j2Gen 1 := by rw [j2FiveGensR_one]; rfl
  have h2 : permOfArr 315 j2FiveGensR[2]! = j2u := by rw [j2FiveGensR_two']; rfl
  have hset : permsA 315 j2FiveGensR =
      ({j2Gen 0, j2Gen 1} : Set (Equiv.Perm (Fin 315))) ∪ {j2u} := by
    ext g
    simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk3 : k < 3 := by simpa [j2FiveGensR_size] using hk
      interval_cases k
      · exact Or.inl (Or.inl h0)
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h2
    · rintro ((rfl | rfl) | rfl)
      · exact ⟨0, by simp [j2FiveGensR_size], h0⟩
      · exact ⟨1, by simp [j2FiveGensR_size], h1⟩
      · exact ⟨2, by simp [j2FiveGensR_size], h2⟩
  rw [hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure]
  rfl

theorem closure_three_j2FiveGensR : Subgroup.closure ({permOfArr 315 j2FiveGensR[0]!,
    permOfArr 315 j2FiveGensR[1]!, permOfArr 315 j2FiveGensR[2]!} :
      Set (Equiv.Perm (Fin 315))) = j2R := by
  rw [← closure_j2FiveGensR]
  congr 1
  ext g
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by simp [j2FiveGensR_size], rfl⟩
    · exact ⟨1, by simp [j2FiveGensR_size], rfl⟩
    · exact ⟨2, by simp [j2FiveGensR_size], rfl⟩
  · rintro ⟨k, hk, rfl⟩
    have hk3 : k < 3 := by simpa [j2FiveGensR_size] using hk
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem card_j2R : Nat.card j2R = 1209600 := by
  obtain ⟨e, -, -, -, hcard⟩ := ctuc_j2_full_automorphism_permutation_model
  rw [Nat.card_congr e.toEquiv, hcard]

theorem mem_j2P_of_inP {g : Array ℕ} {G : Equiv.Perm (Fin 315)} (hG : Rep 315 g G)
    (h : j2FiveInP g = true) : G ∈ j2P := by
  have := (siftA_iff_mem_originalSubgroup j2ChainArrays (by norm_num) PairJ2.chain_check.1
    hG).1 h
  rw [j2P_eq_original]
  exact this

structure J2FiveQFacts : Prop where
  enum : enumOK 315 j2FiveQGenArrs j2FiveKeyPts j2FiveQCert = true
  size : j2FiveQCert.pts.size = 25
  pow : allLt 25 (fun k => eqA 315 (powArr 315 j2FiveQCert.pts[k]! 5) (idA 315)) = true
  cover : allLt 25 (fun k => eqA 315 j2FiveQCert.pts[k]! (idA 315) ||
    (List.range 6).any fun j => (List.range 5).any fun e =>
      eqA 315 j2FiveQCert.pts[k]! (powArr 315 (j2FiveX j) e)) = true
  dist : allLt 6 (fun j => allLt 6 fun j' => j == j' ||
    allLt 5 fun e => !(eqA 315 (j2FiveX j) (powArr 315 (j2FiveX j') e))) = true
  lines : allLt 6 (fun j => validA 315 (j2FiveX j) &&
    eqA 315 (powArr 315 (j2FiveX j) 5) (idA 315) &&
    !(eqA 315 (j2FiveX j) (idA 315)) && j2FiveQCert.pts.toList.any (eqA 315 (j2FiveX j))) = true
  sift : allLt 2 (fun k => j2FiveInP (j2FiveQG k)) = true
  comm : commA 315 (j2FiveQG 0) (j2FiveQG 1) = true

theorem j2Five_Q_facts : J2FiveQFacts := by
  have h := j2Five_Q_check
  simp only [j2FiveQCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hE, hS⟩, hP⟩, hC⟩, hD⟩, hL⟩, hI⟩, hcomm⟩ := h
  exact ⟨hE, hS, hP, hC, hD, hL, hI, hcomm⟩

theorem j2FiveQ_spec :
    (∀ x, x ∈ j2FiveQ ↔ ∃ k < j2FiveQCert.pts.size, permOfArr 315 j2FiveQCert.pts[k]! = x) ∧
      Nat.card j2FiveQ = 25 ∧
        ∀ k < j2FiveQCert.pts.size, validA 315 j2FiveQCert.pts[k]! = true := by
  obtain ⟨h1, h2, h3⟩ := enumOK_spec j2FiveKeyPts_lt j2Five_Q_facts.enum
  exact ⟨h1, h2.trans j2Five_Q_facts.size, h3⟩

theorem card_j2FiveQ : Nat.card j2FiveQ = 25 := j2FiveQ_spec.2.1

theorem j2FiveQ_elem {x : Equiv.Perm (Fin 315)} (hx : x ∈ j2FiveQ) :
    ∃ k < 25, Rep 315 j2FiveQCert.pts[k]! x := by
  obtain ⟨k, hk, rfl⟩ := (j2FiveQ_spec.1 x).1 hx
  exact ⟨k, j2Five_Q_facts.size ▸ hk, rep_of_validA (j2FiveQ_spec.2.2 k hk)⟩

theorem j2FiveQG_valid {k : ℕ} (hk : k < 2) : validA 315 (j2FiveQG k) = true :=
  enumOK_gens_valid j2Five_Q_facts.enum hk

theorem j2FiveQGenArrs_size : j2FiveQGenArrs.size = 2 := by decide

theorem j2FiveQ_le_P : j2FiveQ ≤ j2P := by
  rw [j2FiveQ, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk2 : k < 2 := by simpa [j2FiveQGenArrs_size] using hk
  exact mem_j2P_of_inP (rep_of_validA (j2FiveQG_valid hk2))
    (allLt_spec j2Five_Q_facts.sift hk2)

theorem j2FiveQ_pow_five {g : Equiv.Perm (Fin 315)} (hg : g ∈ j2FiveQ) : g ^ 5 = 1 := by
  obtain ⟨k, hk, hkg⟩ := j2FiveQ_elem hg
  exact (eqA_iff (rep_powArr hkg 5) rep_idA).1 (allLt_spec j2Five_Q_facts.pow hk)

theorem j2FiveLine_facts (j : Fin 6) :
    validA 315 (j2FiveX j) = true ∧ eqA 315 (powArr 315 (j2FiveX j) 5) (idA 315) = true ∧
      eqA 315 (j2FiveX j) (idA 315) = false ∧
      j2FiveQCert.pts.toList.any (eqA 315 (j2FiveX j)) = true := by
  have h := allLt_spec j2Five_Q_facts.lines j.2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem rep_j2FiveLine (j : Fin 6) : Rep 315 (j2FiveX j) (j2FiveLine j) :=
  rep_of_validA (j2FiveLine_facts j).1

theorem j2FiveLine_mem_Q (j : Fin 6) : j2FiveLine j ∈ j2FiveQ :=
  enumOK_mem_of_any j2FiveKeyPts_lt j2Five_Q_facts.enum (rep_j2FiveLine j)
    (j2FiveLine_facts j).2.2.2

theorem j2FiveLine_ne_one (j : Fin 6) : j2FiveLine j ≠ 1 := fun h => by
  have := (eqA_iff (rep_j2FiveLine j) rep_idA).2 h
  rw [(j2FiveLine_facts j).2.2.1] at this
  exact Bool.false_ne_true this

theorem j2FiveLine_pow_five (j : Fin 6) : j2FiveLine j ^ 5 = 1 :=
  (eqA_iff (rep_powArr (rep_j2FiveLine j) 5) rep_idA).1 (j2FiveLine_facts j).2.1

theorem orderOf_j2FiveLine (j : Fin 6) : orderOf (j2FiveLine j) = 5 :=
  orderOf_eq_prime (j2FiveLine_pow_five j) (j2FiveLine_ne_one j)

theorem factorization_card_j2P_five : (Nat.card j2P).factorization 5 = 2 := by
  rw [card_j2P, show (604800 : ℕ) = 5 ^ 2 * 24192 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem j2FiveQ_sylow :
    ∃ S : Sylow 5 j2P, (S : Subgroup j2P) = j2FiveQ.subgroupOf j2P := by
  have hcard : Nat.card (j2FiveQ.subgroupOf j2P) = 5 ^ (Nat.card j2P).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe j2FiveQ_le_P).toEquiv, card_j2FiveQ,
      factorization_card_j2P_five]
    norm_num
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem j2FiveQ_lines :
    {H : Subgroup (Equiv.Perm (Fin 315)) | H ≤ j2FiveQ ∧ Nat.card H = 5} =
        Set.range (fun j : Fin 6 => Subgroup.zpowers (j2FiveLine j)) ∧
      Function.Injective (fun j : Fin 6 => Subgroup.zpowers (j2FiveLine j)) := by
  apply prime_subgroups_eq_range j2FiveLine j2FiveLine_mem_Q j2FiveLine_ne_one
    j2FiveLine_pow_five
  · intro g hg hg1
    obtain ⟨k, hk, hkg⟩ := j2FiveQ_elem hg
    have h := allLt_spec j2Five_Q_facts.cover hk
    simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range] at h
    rcases h with h | ⟨j, hj, e, he, hje⟩
    · exact absurd ((eqA_iff hkg rep_idA).1 h) hg1
    · exact ⟨⟨j, hj⟩, e, (eqA_iff hkg (rep_powArr (rep_j2FiveLine ⟨j, hj⟩) e)).1 hje⟩
  · intro j j' k hk hjj'
    have h := allLt_spec (allLt_spec j2Five_Q_facts.dist j.2) j'.2
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact Fin.ext h
    · have h' := allLt_spec h hk
      rw [Bool.not_eq_true'] at h'
      have := (eqA_iff (rep_j2FiveLine j) (rep_powArr (rep_j2FiveLine j') k)).2 hjj'
      rw [h'] at this
      exact absurd this Bool.false_ne_true

theorem j2FiveC_eq {i : ℕ} (hi : i < 6) {Nc : ℕ}
    (hO : j2FiveCentCheck i Nc = true) :
    j2FiveC i = j2R ⊓ Subgroup.centralizer ({j2FiveLine ⟨i, hi⟩} : Set (Equiv.Perm (Fin 315))) ∧
      Nat.card (j2FiveC i) = Nc := by
  simp only [j2FiveCentCheck, Bool.and_eq_true] at hO
  obtain ⟨hch, hcent⟩ := hO
  have hk : 3 ≤ (j2FiveRS i).size := by interval_cases i <;> decide
  have hb : (j2FiveRBase i).Nodup := by interval_cases i <;> decide
  obtain ⟨h1, h2⟩ := case_centralizerP (p := 5) (by norm_num) hk hb
    (rep_of_validA (valid_j2FiveGensR (by norm_num)))
    (rep_of_validA (valid_j2FiveGensR (by norm_num)))
    (rep_of_validA (valid_j2FiveGensR (by norm_num))) hch (rep_j2FiveLine ⟨i, hi⟩)
    j2FiveKeyPts_lt hcent
  rw [closure_three_j2FiveGensR, inf_comm] at h1
  exact ⟨h1, h2⟩

theorem j2FiveQ_le_centralizer :
    j2FiveQ ≤ Subgroup.centralizer (j2FiveQ : Set (Equiv.Perm (Fin 315))) := by
  rw [j2FiveQ]
  apply closure_le_centralizer_closure_of_forall_comm
  have hc : permOfArr 315 (j2FiveQG 0) * permOfArr 315 (j2FiveQG 1) =
      permOfArr 315 (j2FiveQG 1) * permOfArr 315 (j2FiveQG 0) :=
    (commA_iff (rep_of_validA (j2FiveQG_valid (by norm_num)))
      (rep_of_validA (j2FiveQG_valid (by norm_num)))).1 j2Five_Q_facts.comm
  rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
  have hk2 : k < 2 := by simpa [j2FiveQGenArrs_size] using hk
  have hl2 : l < 2 := by simpa [j2FiveQGenArrs_size] using hl
  interval_cases k <;> interval_cases l
  · rfl
  · exact hc
  · exact hc.symm
  · rfl

theorem j2FiveQPart_facts {i N : ℕ} (hE : enumOK 315 (j2FiveCG i) j2FiveKeyPts
    (j2FiveCCert i) = true) (hsz : (j2FiveCCert i).pts.size = N)
    (h : j2FiveQPart N (j2FiveCCert i) j2FiveQCert = true) :
    j2FiveQ ≤ j2FiveC i ∧
      j2FiveC i ⊓ Subgroup.centralizer (j2FiveQ : Set (Equiv.Perm (Fin 315))) ≤ j2FiveQ := by
  simp only [j2FiveQPart, Bool.and_eq_true] at h
  obtain ⟨hQin, hcent⟩ := h
  refine ⟨?_, ?_⟩
  · rw [j2FiveQ, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk2 : k < 2 := by simpa [j2FiveQGenArrs_size] using hk
    exact enumOK_mem_of_any j2FiveKeyPts_lt hE (rep_of_validA (j2FiveQG_valid hk2))
      (allLt_spec hQin hk2)
  · intro g hg
    obtain ⟨hgC, hgQc⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep j2FiveKeyPts_lt hE hgC
    rw [hsz] at hk
    have hc : ∀ l < 2, commA 315 (j2FiveCCert i).pts[k]! (j2FiveQG l) = true := by
      intro l hl
      have ha : permOfArr 315 (j2FiveQG l) ∈ j2FiveQ :=
        Subgroup.subset_closure (mem_permsA (by simpa [j2FiveQGenArrs_size] using hl))
      exact (commA_iff hkg (rep_of_validA (j2FiveQG_valid hl))).2
        (Subgroup.mem_centralizer_iff.1 hgQc _ ha).symm
    have h := allLt_spec hcent hk
    rw [hc 0 (by norm_num), hc 1 (by norm_num)] at h
    simp only [Bool.and_self, Bool.not_true, Bool.false_or] at h
    exact enumOK_mem_of_any j2FiveKeyPts_lt j2Five_Q_facts.enum hkg h

theorem j2FiveGood_normal {i : ℕ} (hE : enumOK 315 (j2FiveCG i) j2FiveKeyPts
    (j2FiveCCert i) = true) (hQC : j2FiveQ ≤ j2FiveC i)
    (h : allLt (j2FiveCG i).size (fun k => allLt 2 fun l =>
      j2FiveQCert.pts.toList.any (eqA 315 (conjA 315 (j2FiveCG i)[k]! (j2FiveQG l)))) = true) :
    (j2FiveQ.subgroupOf (j2FiveC i)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQC, j2FiveC, j2FiveQ]
  apply closure_le_normalizer_closure
  rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
  have hk' : k < (j2FiveCG i).size := hk
  have hl2 : l < 2 := by simpa [j2FiveQGenArrs_size] using hl
  have h' := allLt_spec (allLt_spec h hk') hl2
  exact enumOK_mem_of_any j2FiveKeyPts_lt j2Five_Q_facts.enum
    (rep_conjA (enumOK_gens_valid hE hk') (rep_of_validA (j2FiveQG_valid hl2))) h'

theorem j2FiveGood_structure {i : ℕ} (hi : i < 6)
    (hO : j2FiveCentCheck i 50 = true)
    (h : j2FiveGoodCheck i (j2FiveCCert i) j2FiveQCert = true) :
    j2FiveC i = j2R ⊓ Subgroup.centralizer ({j2FiveLine ⟨i, hi⟩} :
        Set (Equiv.Perm (Fin 315))) ∧ Nat.card (j2FiveC i) = 50 ∧ j2FiveQ ≤ j2FiveC i ∧
      Subgroup.centralizer (j2FiveQ : Set (Equiv.Perm (Fin 315))) ⊓ j2FiveC i = j2FiveQ ∧
      (j2FiveQ.subgroupOf (j2FiveC i)).Normal := by
  simp only [j2FiveGoodCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hCP, hQP⟩, hnorm⟩ := h
  have hCP' := hCP
  simp only [j2FiveCPart, Bool.and_eq_true, beq_iff_eq] at hCP'
  obtain ⟨⟨⟨hE, hsz⟩, -⟩, -⟩ := hCP'
  obtain ⟨hCeq, hcard⟩ := j2FiveC_eq hi hO
  obtain ⟨hQC, hQcent⟩ := j2FiveQPart_facts hE hsz hQP
  refine ⟨hCeq, hcard, hQC, ?_, j2FiveGood_normal hE hQC hnorm⟩
  apply le_antisymm
  · rw [inf_comm]
    exact hQcent
  · exact le_inf j2FiveQ_le_centralizer hQC

theorem j2FiveBad_structure {i : ℕ} (hi : i < 6)
    (hO : j2FiveCentCheck i 300 = true)
    (h : j2FiveBadCheck i (j2FiveCCert i) (j2FiveDCert i) j2FiveQCert = true) :
    j2FiveC i = j2R ⊓ Subgroup.centralizer ({j2FiveLine ⟨i, hi⟩} :
        Set (Equiv.Perm (Fin 315))) ∧ Nat.card (j2FiveC i) = 300 ∧ j2FiveQ ≤ j2FiveC i ∧
      Subgroup.centralizer (j2FiveQ : Set (Equiv.Perm (Fin 315))) ⊓ j2FiveC i = j2FiveQ ∧
      j2FiveD i ≤ j2FiveC i ∧ j2FiveD i ≤ j2P ∧ ((j2FiveD i).subgroupOf (j2FiveC i)).Normal ∧
      IsSimpleGroup (j2FiveD i) ∧ (∃ g ∈ j2FiveD i, ∃ h ∈ j2FiveD i, g * h ≠ h * g) ∧
      Nat.card (j2FiveD i) = 60 ∧
      Subgroup.centralizer (j2FiveD i : Set (Equiv.Perm (Fin 315))) ⊓ j2FiveC i =
        Subgroup.zpowers (j2FiveLine ⟨i, hi⟩) := by
  simp only [j2FiveBadCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hCP, hQP⟩, hDE⟩, hDS⟩, hDC⟩, hDP⟩, hnorm⟩, hnonab⟩, hsimple⟩, hcent⟩ := h
  have hCP' := hCP
  simp only [j2FiveCPart, Bool.and_eq_true, beq_iff_eq] at hCP'
  obtain ⟨⟨⟨hE, hsz⟩, -⟩, -⟩ := hCP'
  obtain ⟨hCeq, hcard⟩ := j2FiveC_eq hi hO
  obtain ⟨hQC, hQcent⟩ := j2FiveQPart_facts hE hsz (by simpa [j2FiveQPart] using hQP)
  have hDvalid : ∀ {k : ℕ}, k < (j2FiveDG i).size → validA 315 (j2FiveDG i)[k]! = true :=
    fun hk => enumOK_gens_valid hDE hk
  have hDC' : j2FiveD i ≤ j2FiveC i := by
    rw [j2FiveD, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < (j2FiveDG i).size := hk
    exact enumOK_mem_of_any j2FiveKeyPts_lt hE (rep_of_validA (hDvalid hk'))
      (allLt_spec hDC hk')
  have hDP' : j2FiveD i ≤ j2P := by
    rw [j2FiveD, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < (j2FiveDG i).size := hk
    exact mem_j2P_of_inP (rep_of_validA (hDvalid hk')) (allLt_spec hDP hk')
  have hDnormal : ((j2FiveD i).subgroupOf (j2FiveC i)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDC', j2FiveC, j2FiveD]
    apply closure_le_normalizer_closure
    rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
    have hk' : k < (j2FiveCG i).size := hk
    have hl' : l < (j2FiveDG i).size := hl
    exact enumOK_mem_of_any j2FiveKeyPts_lt hDE
      (rep_conjA (enumOK_gens_valid hE hk') (rep_of_validA (hDvalid hl')))
      (allLt_spec (allLt_spec hnorm hk') hl')
  have hDcard : Nat.card (j2FiveD i) = 60 := (enumOK_spec j2FiveKeyPts_lt hDE).2.1.trans hDS
  have hDsimple : IsSimpleGroup (j2FiveD i) :=
    isSimpleGroup_of_conjWordsOK j2FiveKeyPts_lt hDE (by omega) hsimple
  have hDnonab : ∃ g ∈ j2FiveD i, ∃ h ∈ j2FiveD i, g * h ≠ h * g := by
    simp only [List.any_eq_true, List.mem_range, Bool.not_eq_true'] at hnonab
    obtain ⟨k, hk, l, hl, hkl⟩ := hnonab
    refine ⟨permOfArr 315 (j2FiveDG i)[k]!, Subgroup.subset_closure (mem_permsA hk),
      permOfArr 315 (j2FiveDG i)[l]!, Subgroup.subset_closure (mem_permsA hl), fun heq => ?_⟩
    have := (commA_iff (rep_of_validA (hDvalid hk)) (rep_of_validA (hDvalid hl))).2 heq
    rw [this] at hkl
    simp at hkl
  have hxC : j2FiveLine ⟨i, hi⟩ ∈ j2FiveC i := by
    rw [hCeq]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left (j2FiveQ_le_P (j2FiveLine_mem_Q _)),
      Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hcentD : Subgroup.centralizer (j2FiveD i : Set (Equiv.Perm (Fin 315))) ⊓ j2FiveC i =
      Subgroup.zpowers (j2FiveLine ⟨i, hi⟩) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgD, hgC⟩ := Subgroup.mem_inf.1 hg
      obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep j2FiveKeyPts_lt hE hgC
      rw [hsz] at hk
      have hc : ∀ l < (j2FiveDG i).size,
          commA 315 (j2FiveCCert i).pts[k]! (j2FiveDG i)[l]! = true := by
        intro l hl
        have ha : permOfArr 315 (j2FiveDG i)[l]! ∈ j2FiveD i :=
          Subgroup.subset_closure (mem_permsA hl)
        exact (commA_iff hkg (rep_of_validA (hDvalid hl))).2
          (Subgroup.mem_centralizer_iff.1 hgD _ ha).symm
      have h := allLt_spec hcent hk
      rw [show (allLt (j2FiveDG i).size fun l =>
          commA 315 (j2FiveCCert i).pts[k]! (j2FiveDG i)[l]!) = true from
        allLt_iff.2 hc] at h
      simp only [Bool.not_true, Bool.false_or, List.any_eq_true, List.mem_range] at h
      obtain ⟨e, -, he⟩ := h
      rw [(eqA_iff hkg (rep_powArr (rep_j2FiveLine ⟨i, hi⟩) e)).1 he]
      exact Subgroup.npow_mem_zpowers _ e
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun d hd => ?_, hxC⟩
      have hdC : d ∈ j2R ⊓ Subgroup.centralizer ({j2FiveLine ⟨i, hi⟩} :
          Set (Equiv.Perm (Fin 315))) := hCeq ▸ hDC' hd
      exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hdC).2
  have hQeq : Subgroup.centralizer (j2FiveQ : Set (Equiv.Perm (Fin 315))) ⊓ j2FiveC i =
      j2FiveQ :=
    le_antisymm (by rw [inf_comm]; exact hQcent) (le_inf j2FiveQ_le_centralizer hQC)
  exact ⟨hCeq, hcard, hQC, hQeq, hDC', hDP', hDnormal, hDsimple, hDnonab, hDcard, hcentD⟩

end CFSG.RankThree.PartOne
