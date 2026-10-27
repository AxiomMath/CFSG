module

public import CFSG.RankThree.Native.HSMcLFiveCheck
public import CFSG.RankThree.Native.HSMcLAut

public noncomputable section

namespace CFSG.RankThree.Native

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.Sporadic.Schreier
open scoped commutatorElement

section Generic

variable {n : ℕ}

theorem case_centralizer {S : Array (Array ℕ)} (hn : 1 ≤ n) (hk : 3 ≤ S.size)
    {bs : List (Fin n)} (hb : bs.Nodup) {W : Array (List ℤ)} {a b u : Array ℕ}
    {A B U : Equiv.Perm (Fin n)} (ha : Rep n a A) (hb' : Rep n b B) (hu : Rep n u U)
    (hchain : caseChainOK n S (bs.map Fin.val).toArray W a b u = true) {x : Array ℕ}
    {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {rels : List (ℕ × ℕ × ℕ)}
    {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} {N : ℕ} (hps : ∀ p ∈ ps, p < n)
    (hcent : centOK n S (bs.map Fin.val).toArray x rels gs ps c N = true) :
    closure (permsA n gs) = centralizer {X} ⊓ closure {A, B, U} ∧
      Nat.card (closure (permsA n gs)) = N := by
  simp only [caseChainOK, Bool.and_eq_true] at hchain
  obtain ⟨⟨⟨hc, e0⟩, e1⟩, e2⟩ := hchain
  simp only [centOK, Bool.and_eq_true, beq_iff_eq] at hcent
  obtain ⟨⟨⟨⟨⟨hrels, hC⟩, hsize⟩, hcomm⟩, hsift⟩, htail⟩ := hcent
  have hA : ChainArrays (RawSchreierDatum.ofArrays n hn S 3 hk bs hb W) (S.extract 0 3) S
      (bs.map Fin.val).toArray W := chainArrays_ofArrays (chainCheckFacts hc).strong_inv
  have horig := originalSubgroup_ofArrays_three (hn := hn) (hk := hk) (hb := hb) hc ha hb' hu e0
    e1 e2
  refine ⟨?_, (enumOK_spec hps hC).2.1.trans hsize⟩
  rw [← horig]
  exact centralizer_eq_of_ptailOK hA hc hx hrels hps hC hcomm hsift htail

theorem mem_of_gen_zero {gs : Array (Array ℕ)} {x : Array ℕ} {X : Equiv.Perm (Fin n)}
    (hx : Rep n x X) (h0 : 0 < gs.size) (hv : validA n gs[0]! = true)
    (he : eqA n gs[0]! x = true) : X ∈ closure (permsA n gs) := by
  rw [← eq_of_eqA (rep_of_validA hv) hx he]
  exact subset_closure (mem_permsA h0)

theorem normal_five {gC gA : Array (Array ℕ)} {ps : List ℕ} {cC cA : ArrCert} {N : ℕ}
    {PL : Array Level} {Pb : Array ℕ} {P : Subgroup (Equiv.Perm (Fin n))}
    (hps : ∀ p ∈ ps, p < n) (hC : enumOK n gC ps cC = true)
    (h : normalOK n gC gA ps cC cA N PL Pb = true)
    (hmemP : ∀ {g : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n g G → siftA n PL Pb 0 g = true →
      G ∈ P) (hN : 1 < N) :
    enumOK n gA ps cA = true ∧
    allLt gA.size (fun l => cC.pts.toList.any (eqA n gA[l]!)) = true ∧
    closure (permsA n gA) ≤ closure (permsA n gC) ∧
      ((closure (permsA n gA)).subgroupOf (closure (permsA n gC))).Normal ∧
      closure (permsA n gA) ≤ P ∧ Nat.card (closure (permsA n gA)) = N ∧
      Monoid.exponent (closure (permsA n gA)) = 5 := by
  simp only [normalOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hAe, hsize⟩, hpow⟩, hmem⟩, hnorm⟩, hsift⟩ := h
  have hcard : Nat.card (closure (permsA n gA)) = N := (enumOK_spec hps hAe).2.1.trans hsize
  refine ⟨hAe, hmem, le_of_gens_mem hps hC hAe hmem, normal_kit hps hC hAe hmem hnorm, ?_, hcard,
    ?_⟩
  · rw [closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact hmemP (rep_of_validA (enumOK_gens_valid hAe hl)) (allLt_spec hsift hl)
  · have hdvd : Monoid.exponent (closure (permsA n gA)) ∣ 5 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (pow_five_of_enum hps hAe hpow g.2)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hdvd with he | he
    · exfalso
      have hs := Monoid.exp_eq_one_iff.1 he
      have : Nat.card (closure (permsA n gA)) ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hs
      omega
    · exact he

end Generic

theorem hs100FiveKeys_lt : ∀ p ∈ hs100FiveKeys, p < 100 := by decide

theorem mcl275FiveKeys_lt : ∀ p ∈ mcl275FiveKeys, p < 275 := by decide

theorem mem_hs100P_of_sift {g : Array ℕ} {G : Equiv.Perm (Fin 100)} (hG : Rep 100 g G)
    (h : siftA 100 hs100PLevels hs100BaseArr 0 g = true) : G ∈ hs100P := by
  rw [hs100P_eq_original]
  exact mem_of_siftA hs100ChainArrays hs100_chain_check.1 hG h

theorem mem_hs100R_of_sift {g : Array ℕ} {G : Equiv.Perm (Fin 100)} (hG : Rep 100 g G)
    (h : siftA 100 hs100RLevels hs100RBaseArr 0 g = true) : G ∈ hs100R := by
  rw [hs100R_eq_original]
  exact mem_of_siftA hs100RChainArrays hs100R_chain_check.1 hG h

theorem mem_mcl275P_of_sift {g : Array ℕ} {G : Equiv.Perm (Fin 275)} (hG : Rep 275 g G)
    (h : siftA 275 mcl275PLevels PairMcL.baseArr 0 g = true) : G ∈ mcl275P := by
  rw [mcl275P_eq, mclP_eq_original]
  exact (siftA_iff_mem_originalSubgroup mclChainArrays (by norm_num) PairMcL.chain_check.1 hG).1 h

theorem rep_mcl275U : Rep 275 (CFSG.Sporadic.SmallOddCore.Native.natArr
    CFSG.Sporadic.SmallOddCore.mclOuterTbl) mcl275U :=
  (rep_permOfArr mcl275R_chain_check.2.2.2.2.2).1

theorem rep_mcl275A : Rep 275 mclStrongArrs[0]! mcl275A := rep_mclGen (by norm_num)

theorem rep_mcl275B : Rep 275 mclStrongArrs[1]! mcl275B := rep_mclGen (by norm_num)

theorem mcl275RChainArrays :
    ChainArrays mcl275RChain (mcl275RArrs.extract 0 3) mcl275RArrs mcl275RBaseArr mcl275RWords :=
  chainArrays_ofArrays (chainCheckFacts mcl275R_chain_check.1).strong_inv

theorem mcl275R_eq_original : mcl275R = mcl275RChain.originalSubgroup :=
  (originalSubgroup_ofArrays_three mcl275R_chain_check.1 rep_mcl275A rep_mcl275B rep_mcl275U
    mcl275R_chain_check.2.2.1 mcl275R_chain_check.2.2.2.1 mcl275R_chain_check.2.2.2.2.1).symm

theorem mem_mcl275R_of_sift {g : Array ℕ} {G : Equiv.Perm (Fin 275)} (hG : Rep 275 g G)
    (h : siftA 275 mcl275RLevels mcl275RBaseArr 0 g = true) : G ∈ mcl275R := by
  rw [mcl275R_eq_original]
  exact mem_of_siftA mcl275RChainArrays mcl275R_chain_check.1 hG h

theorem hs100Five_lines_ok :
    linesOK 100 hs100FiveQGens hs100FiveKeys hs100FiveQCert hs100FiveLines = true :=
  hs100Five_Q_check.1

theorem rep_hs100FiveLine (j : Fin 31) : Rep 100 hs100FiveLines[(j : ℕ)]! (hs100FiveLine j) :=
  linesOK_rep hs100Five_lines_ok j

theorem hs100FiveQ_le_P : hs100FiveQ ≤ hs100P := by
  rw [hs100FiveQ, closure_le]
  rintro _ ⟨l, hl, rfl⟩
  have hv := enumOK_gens_valid (linesOK_parts hs100Five_lines_ok).1 hl
  exact mem_hs100P_of_sift (rep_of_validA hv) (allLt_spec hs100Five_Q_check.2.1 hl)

theorem card_hs100FiveQ : Nat.card hs100FiveQ = 125 :=
  linesOK_card hs100FiveKeys_lt hs100Five_lines_ok

theorem factorization_card_hs100P_five : (Nat.card hs100P).factorization 5 = 3 := by
  rw [card_hs100P, show (44352000 : ℕ) = 5 ^ 3 * 354816 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem hs100FiveQ_sylow :
    ∃ S : Sylow 5 hs100P, (S : Subgroup hs100P) = hs100FiveQ.subgroupOf hs100P := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card (hs100FiveQ.subgroupOf hs100P) = 5 ^ (Nat.card hs100P).factorization 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hs100FiveQ_le_P).toEquiv, card_hs100FiveQ,
      factorization_card_hs100P_five]
    norm_num
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem hs100FiveTransporter_spec (j : Fin 31) :
    hs100FiveTransporter j ∈ hs100R ∧
      hs100FiveTransporter j * hs100FiveLine (hs100FiveRecordOf j) *
        (hs100FiveTransporter j)⁻¹ = hs100FiveLine j := by
  have h := allLt_spec hs100Five_Q_check.2.2.1 j.2
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hv, hs⟩, he⟩ := h
  refine ⟨mem_hs100R_of_sift (rep_of_validA hv) hs, ?_⟩
  exact eq_of_eqA (rep_conjA hv (rep_hs100FiveLine (hs100FiveRecordOf j)))
    (rep_hs100FiveLine j) he

theorem hs100FiveRecordOf_mem (j : Fin 31) :
    (hs100FiveRecordOf j : ℕ) ∈ ({0, 2, 23} : Finset ℕ) := by
  have h := allLt_spec hs100Five_Q_check.2.2.2.2.2.2 j.2
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  change hs100FiveRec.getD j 0 % 31 ∈ ({0, 2, 23} : Finset ℕ)
  rcases h with (h | h) | h <;> rw [h] <;> decide

theorem hs100FiveRecordOf_reps :
    hs100FiveRecordOf 0 = 0 ∧ hs100FiveRecordOf 2 = 2 ∧ hs100FiveRecordOf 23 = 23 := by
  obtain ⟨-, -, -, h0, h2, h23, -⟩ := hs100Five_Q_check
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩
  · change hs100FiveRec.getD 0 0 % 31 = 0
    rw [h0]
  · change hs100FiveRec.getD 2 0 % 31 = 2
    rw [h2]
  · change hs100FiveRec.getD 23 0 % 31 = 23
    rw [h23]

theorem hs100FiveC0_spec :
    hs100FiveC0 = centralizer {hs100FiveLine 0} ⊓ hs100R ∧ Nat.card hs100FiveC0 = 50 :=
  case_centralizer (by norm_num) (by simp [hs100Case0Arrs]) (by decide) rep_hs100A rep_hs100B
    rep_hs100U hs100Five_case0_check.1 (rep_hs100FiveLine 0) hs100FiveKeys_lt
    hs100Five_case0_check.2.1

theorem hs100FiveC2_spec :
    hs100FiveC2 = centralizer {hs100FiveLine 2} ⊓ hs100R ∧ Nat.card hs100FiveC2 = 600 :=
  case_centralizer (by norm_num) (by simp [hs100Case2Arrs]) (by decide) rep_hs100A rep_hs100B
    rep_hs100U hs100Five_case2_check.1 (rep_hs100FiveLine 2) hs100FiveKeys_lt
    hs100Five_case2_check.2.1

theorem hs100FiveC23_spec :
    hs100FiveC23 = centralizer {hs100FiveLine 23} ⊓ hs100R ∧ Nat.card hs100FiveC23 = 1000 :=
  case_centralizer (by norm_num) (by simp [hs100Case23Arrs]) (by decide) rep_hs100A rep_hs100B
    rep_hs100U hs100Five_case23_check.1 (rep_hs100FiveLine 23) hs100FiveKeys_lt
    hs100Five_case23_check.2.1

theorem hs100FiveC0_enum : enumOK 100 hs100FiveC0Gens hs100FiveKeys hs100FiveC0Cert = true := by
  have h := hs100Five_case0_check.2.1
  simp only [centOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem hs100FiveC2_enum : enumOK 100 hs100FiveC2Gens hs100FiveKeys hs100FiveC2Cert = true := by
  have h := hs100Five_case2_check.2.1
  simp only [centOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem hs100FiveC23_enum :
    enumOK 100 hs100FiveC23Gens hs100FiveKeys hs100FiveC23Cert = true := by
  have h := hs100Five_case23_check.2.1
  simp only [centOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem hs100FiveA0_spec :
    hs100FiveA0 ≤ hs100FiveC0 ∧ (hs100FiveA0.subgroupOf hs100FiveC0).Normal ∧
      hs100FiveA0 ≤ hs100P ∧ Nat.card hs100FiveA0 = 25 ∧ Monoid.exponent hs100FiveA0 = 5 ∧
      Nat.card (centralizer (hs100FiveA0 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC0 :
        Subgroup (Equiv.Perm (Fin 100))) = 25 ∧
      centralizer (hs100FiveA0 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC0 ≤ hs100FiveA0 := by
  obtain ⟨hAe, hmem, hle, hnorm, hP, hcard, hexp⟩ := normal_five hs100FiveKeys_lt
    hs100FiveC0_enum hs100Five_case0_check.2.2.1 mem_hs100P_of_sift (by norm_num)
  have hself : centralizer (hs100FiveA0 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC0 =
      hs100FiveA0 := by
    have h := hs100Five_case0_check.2.2.2.1
    simp only [selfCentOK, Bool.and_eq_true] at h
    exact centralizer_eq_self_kit hs100FiveKeys_lt hs100FiveC0_enum hAe hmem h.1 h.2
  refine ⟨hle, hnorm, hP, hcard, hexp, ?_, hself.le⟩
  rw [hself]
  exact hcard

theorem hs100FiveA23_spec :
    hs100FiveA23 ≤ hs100FiveC23 ∧ (hs100FiveA23.subgroupOf hs100FiveC23).Normal ∧
      hs100FiveA23 ≤ hs100P ∧ Nat.card hs100FiveA23 = 125 ∧ Monoid.exponent hs100FiveA23 = 5 ∧
      Nat.card (centralizer (hs100FiveA23 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC23 :
        Subgroup (Equiv.Perm (Fin 100))) = 5 ∧
      centralizer (hs100FiveA23 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC23 ≤ hs100FiveA23 := by
  obtain ⟨hAe, -, hle, hnorm, hP, hcard, hexp⟩ := normal_five hs100FiveKeys_lt
    hs100FiveC23_enum hs100Five_case23_check.2.2.1 mem_hs100P_of_sift (by norm_num)
  have hz := hs100Five_case23_check.2.2.2.1
  simp only [zCentOK, Bool.and_eq_true] at hz
  have hxC : hs100FiveLine 23 ∈ hs100FiveC23 :=
    mem_of_gen_zero (rep_hs100FiveLine 23) (by simp [hs100FiveC23Gens])
      (enumOK_gens_valid hs100FiveC23_enum (by simp [hs100FiveC23Gens]))
      hs100Five_case23_check.2.2.2.2
  have hxA : hs100FiveLine 23 ∈ hs100FiveA23 :=
    enumOK_mem_of_any hs100FiveKeys_lt hAe (rep_hs100FiveLine 23) hz.1
  have hxcent : hs100FiveLine 23 ∈
      centralizer (hs100FiveA23 : Set (Equiv.Perm (Fin 100))) := by
    rw [mem_centralizer_iff]
    intro a ha
    have := (hs100FiveC23_spec.1 ▸ hle ha : a ∈ centralizer {hs100FiveLine 23} ⊓ hs100R)
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 this).1
  have hcent : centralizer (hs100FiveA23 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC23 =
      zpowers (hs100FiveLine 23) :=
    centralizer_eq_zpowers_kit hs100FiveKeys_lt hs100FiveC23_enum hAe (rep_hs100FiveLine 23) hxC
      hxcent hz.2
  refine ⟨hle, hnorm, hP, hcard, hexp, ?_, ?_⟩
  · rw [hcent, Nat.card_zpowers]
    exact linesOK_orderOf hs100Five_lines_ok 23
  · rw [hcent, zpowers_le]
    exact hxA

theorem hs100FiveD2_spec :
    IsSimpleGroup hs100FiveD2 ∧ (∃ g ∈ hs100FiveD2, ∃ h ∈ hs100FiveD2, g * h ≠ h * g) ∧
      Nat.card hs100FiveD2 = 60 ∧ hs100FiveD2 ≤ hs100P ∧
      centralizer (hs100FiveD2 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC2 =
        zpowers (hs100FiveLine 2) ∧
      Nat.card (centralizer (hs100FiveD2 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC2 :
        Subgroup (Equiv.Perm (Fin 100))) = 5 := by
  have h := hs100Five_case2_check.2.2.1
  simp only [derivedOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hDe, hDs⟩, hcv⟩, hdv⟩, hcm⟩, hdm⟩, hb⟩, hnorm⟩, hcomm⟩, hnab⟩,
    hsimple⟩, hcent⟩, hsift⟩ := h
  have hgD : hs100FiveDGens = #[commutatorA 100 hs100FiveC2Gens[1]! hs100FiveC2Gens[2]!,
      hs100FiveC2Gens[2]!] := rfl
  have hD : hs100FiveD2 = closure (permsA 100 hs100FiveDGens) :=
    derived_kit hs100FiveKeys_lt hs100FiveC2_enum hDe (by simp [hs100FiveC2Gens]) hgD hcv hdv
      hcm hdm hb hnorm hcomm
  have hDsize : hs100FiveDGens.size = 2 := by simp [hs100FiveDGens]
  have hrepD : ∀ l < hs100FiveDGens.size,
      Rep 100 hs100FiveDGens[l]! (permOfArr 100 hs100FiveDGens[l]!) := fun l hl =>
    rep_of_validA (enumOK_gens_valid hDe hl)
  have hcard : Nat.card hs100FiveD2 = 60 := by
    rw [hD]
    exact (enumOK_spec hs100FiveKeys_lt hDe).2.1.trans hDs
  have hxC : hs100FiveLine 2 ∈ hs100FiveC2 :=
    mem_of_gen_zero (rep_hs100FiveLine 2) (by simp [hs100FiveC2Gens])
      (enumOK_gens_valid hs100FiveC2_enum (by simp [hs100FiveC2Gens]))
      hs100Five_case2_check.2.2.2
  have hDC : hs100FiveD2 ≤ hs100FiveC2 := by
    rw [hs100FiveD2, commutator_le]
    intro a ha b hb'
    rw [commutatorElement_def]
    exact hs100FiveC2.mul_mem (hs100FiveC2.mul_mem (hs100FiveC2.mul_mem ha hb')
      (hs100FiveC2.inv_mem ha)) (hs100FiveC2.inv_mem hb')
  have hxcent : hs100FiveLine 2 ∈ centralizer (hs100FiveD2 : Set (Equiv.Perm (Fin 100))) := by
    rw [mem_centralizer_iff]
    intro a ha
    have := (hs100FiveC2_spec.1 ▸ hDC ha : a ∈ centralizer {hs100FiveLine 2} ⊓ hs100R)
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 this).1
  have hcentD : centralizer (hs100FiveD2 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC2 =
      zpowers (hs100FiveLine 2) := by
    rw [hD] at hxcent ⊢
    exact centralizer_eq_zpowers_kit hs100FiveKeys_lt hs100FiveC2_enum hDe
      (rep_hs100FiveLine 2) hxC hxcent hcent
  refine ⟨?_, ?_, hcard, ?_, hcentD, ?_⟩
  · rw [hD]
    exact isSimpleGroup_of_conjSimpleOK hs100FiveKeys_lt hDe (by rw [hDs]; norm_num) hsimple
  · rw [hD]
    refine ⟨_, subset_closure (mem_permsA (k := 0) (by rw [hDsize]; norm_num)), _,
      subset_closure (mem_permsA (k := 1) (by rw [hDsize]; norm_num)), fun e => ?_⟩
    have := (commA_iff (hrepD 0 (by rw [hDsize]; norm_num))
      (hrepD 1 (by rw [hDsize]; norm_num))).2 e
    rw [hnab] at this
    exact Bool.false_ne_true this
  · rw [hD, closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact mem_hs100P_of_sift (hrepD l hl) (allLt_spec hsift hl)
  · rw [hcentD, Nat.card_zpowers]
    exact linesOK_orderOf hs100Five_lines_ok 2

theorem mcl275Five_lines_ok :
    linesOK 275 mcl275FiveQGens mcl275FiveKeys mcl275FiveQCert mcl275FiveLines = true :=
  mcl275Five_Q_check.1

theorem rep_mcl275FiveLine (j : Fin 31) : Rep 275 mcl275FiveLines[(j : ℕ)]! (mcl275FiveLine j) :=
  linesOK_rep mcl275Five_lines_ok j

theorem mcl275FiveQ_le_P : mcl275FiveQ ≤ mcl275P := by
  rw [mcl275FiveQ, closure_le]
  rintro _ ⟨l, hl, rfl⟩
  have hv := enumOK_gens_valid (linesOK_parts mcl275Five_lines_ok).1 hl
  exact mem_mcl275P_of_sift (rep_of_validA hv) (allLt_spec mcl275Five_Q_check.2.1 hl)

theorem card_mcl275FiveQ : Nat.card mcl275FiveQ = 125 :=
  linesOK_card mcl275FiveKeys_lt mcl275Five_lines_ok

theorem factorization_card_mcl275P_five : (Nat.card mcl275P).factorization 5 = 3 := by
  rw [mcl275P_eq, card_mclP, show (898128000 : ℕ) = 5 ^ 3 * 7185024 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem mcl275FiveQ_sylow :
    ∃ S : Sylow 5 mcl275P, (S : Subgroup mcl275P) = mcl275FiveQ.subgroupOf mcl275P := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card (mcl275FiveQ.subgroupOf mcl275P) =
      5 ^ (Nat.card mcl275P).factorization 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe mcl275FiveQ_le_P).toEquiv, card_mcl275FiveQ,
      factorization_card_mcl275P_five]
    norm_num
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem mcl275FiveTransporter_spec (j : Fin 31) :
    mcl275FiveTransporter j ∈ mcl275R ∧
      mcl275FiveTransporter j * mcl275FiveLine (mcl275FiveRecordOf j) *
        (mcl275FiveTransporter j)⁻¹ = mcl275FiveLine j := by
  have h := allLt_spec mcl275Five_Q_check.2.2.1 j.2
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hv, hs⟩, he⟩ := h
  refine ⟨mem_mcl275R_of_sift (rep_of_validA hv) hs, ?_⟩
  exact eq_of_eqA (rep_conjA hv (rep_mcl275FiveLine (mcl275FiveRecordOf j)))
    (rep_mcl275FiveLine j) he

theorem mcl275FiveRecordOf_mem (j : Fin 31) :
    (mcl275FiveRecordOf j : ℕ) ∈ ({0, 1} : Finset ℕ) := by
  have h := allLt_spec mcl275Five_Q_check.2.2.2.2.2 j.2
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  change mcl275FiveRec.getD j 0 % 31 ∈ ({0, 1} : Finset ℕ)
  rcases h with h | h <;> rw [h] <;> decide

theorem mcl275FiveRecordOf_reps : mcl275FiveRecordOf 0 = 0 ∧ mcl275FiveRecordOf 1 = 1 := by
  obtain ⟨-, -, -, h0, h1, -⟩ := mcl275Five_Q_check
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩
  · change mcl275FiveRec.getD 0 0 % 31 = 0
    rw [h0]
  · change mcl275FiveRec.getD 1 0 % 31 = 1
    rw [h1]

theorem mcl275FiveC0_spec :
    mcl275FiveC0 = centralizer {mcl275FiveLine 0} ⊓ mcl275R ∧ Nat.card mcl275FiveC0 = 50 :=
  case_centralizer (by norm_num) (by simp [mcl275Case0Arrs]) (by decide) rep_mcl275A rep_mcl275B
    rep_mcl275U mcl275Five_case0_check.1 (rep_mcl275FiveLine 0) mcl275FiveKeys_lt
    mcl275Five_case0_check.2.1

theorem mcl275FiveC1_spec :
    mcl275FiveC1 = centralizer {mcl275FiveLine 1} ⊓ mcl275R ∧ Nat.card mcl275FiveC1 = 1500 :=
  case_centralizer (by norm_num) (by simp [mcl275Case1Arrs]) (by decide) rep_mcl275A rep_mcl275B
    rep_mcl275U mcl275Five_case1_check.1 (rep_mcl275FiveLine 1) mcl275FiveKeys_lt
    mcl275Five_case1_check.2.1

theorem mcl275FiveC0_enum :
    enumOK 275 mcl275FiveC0Gens mcl275FiveKeys mcl275FiveC0Cert = true := by
  have h := mcl275Five_case0_check.2.1
  simp only [centOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem mcl275FiveC1_enum :
    enumOK 275 mcl275FiveC1Gens mcl275FiveKeys mcl275FiveC1Cert = true := by
  have h := mcl275Five_case1_check.2.1
  simp only [centOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem mcl275FiveA0_spec :
    mcl275FiveA0 ≤ mcl275FiveC0 ∧ (mcl275FiveA0.subgroupOf mcl275FiveC0).Normal ∧
      mcl275FiveA0 ≤ mcl275P ∧ Nat.card mcl275FiveA0 = 25 ∧ Monoid.exponent mcl275FiveA0 = 5 ∧
      Nat.card (centralizer (mcl275FiveA0 : Set (Equiv.Perm (Fin 275))) ⊓ mcl275FiveC0 :
        Subgroup (Equiv.Perm (Fin 275))) = 25 ∧
      centralizer (mcl275FiveA0 : Set (Equiv.Perm (Fin 275))) ⊓ mcl275FiveC0 ≤ mcl275FiveA0 := by
  obtain ⟨hAe, hmem, hle, hnorm, hP, hcard, hexp⟩ := normal_five mcl275FiveKeys_lt
    mcl275FiveC0_enum mcl275Five_case0_check.2.2.1 mem_mcl275P_of_sift (by norm_num)
  have hself : centralizer (mcl275FiveA0 : Set (Equiv.Perm (Fin 275))) ⊓ mcl275FiveC0 =
      mcl275FiveA0 := by
    have h := mcl275Five_case0_check.2.2.2.1
    simp only [selfCentOK, Bool.and_eq_true] at h
    exact centralizer_eq_self_kit mcl275FiveKeys_lt mcl275FiveC0_enum hAe hmem h.1 h.2
  refine ⟨hle, hnorm, hP, hcard, hexp, ?_, hself.le⟩
  rw [hself]
  exact hcard

theorem mcl275FiveA1_spec :
    mcl275FiveA1 ≤ mcl275FiveC1 ∧ (mcl275FiveA1.subgroupOf mcl275FiveC1).Normal ∧
      mcl275FiveA1 ≤ mcl275P ∧ Nat.card mcl275FiveA1 = 125 ∧ Monoid.exponent mcl275FiveA1 = 5 ∧
      Nat.card (centralizer (mcl275FiveA1 : Set (Equiv.Perm (Fin 275))) ⊓ mcl275FiveC1 :
        Subgroup (Equiv.Perm (Fin 275))) = 5 ∧
      centralizer (mcl275FiveA1 : Set (Equiv.Perm (Fin 275))) ⊓ mcl275FiveC1 ≤ mcl275FiveA1 := by
  obtain ⟨hAe, -, hle, hnorm, hP, hcard, hexp⟩ := normal_five mcl275FiveKeys_lt
    mcl275FiveC1_enum mcl275Five_case1_check.2.2.1 mem_mcl275P_of_sift (by norm_num)
  have hz := mcl275Five_case1_check.2.2.2.1
  simp only [zCentOK, Bool.and_eq_true] at hz
  have hxC : mcl275FiveLine 1 ∈ mcl275FiveC1 :=
    mem_of_gen_zero (rep_mcl275FiveLine 1) (by simp [mcl275FiveC1Gens])
      (enumOK_gens_valid mcl275FiveC1_enum (by simp [mcl275FiveC1Gens]))
      mcl275Five_case1_check.2.2.2.2
  have hxA : mcl275FiveLine 1 ∈ mcl275FiveA1 :=
    enumOK_mem_of_any mcl275FiveKeys_lt hAe (rep_mcl275FiveLine 1) hz.1
  have hxcent : mcl275FiveLine 1 ∈
      centralizer (mcl275FiveA1 : Set (Equiv.Perm (Fin 275))) := by
    rw [mem_centralizer_iff]
    intro a ha
    have := (mcl275FiveC1_spec.1 ▸ hle ha : a ∈ centralizer {mcl275FiveLine 1} ⊓ mcl275R)
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 this).1
  have hcent : centralizer (mcl275FiveA1 : Set (Equiv.Perm (Fin 275))) ⊓ mcl275FiveC1 =
      zpowers (mcl275FiveLine 1) :=
    centralizer_eq_zpowers_kit mcl275FiveKeys_lt mcl275FiveC1_enum hAe (rep_mcl275FiveLine 1) hxC
      hxcent hz.2
  refine ⟨hle, hnorm, hP, hcard, hexp, ?_, ?_⟩
  · rw [hcent, Nat.card_zpowers]
    exact linesOK_orderOf mcl275Five_lines_ok 1
  · rw [hcent, zpowers_le]
    exact hxA


theorem R3E_HS_full_five_centralizer_structures :
    (hs100FiveQ ≤ hs100P ∧
      (∃ S : Sylow 5 hs100P, (S : Subgroup hs100P) = hs100FiveQ.subgroupOf hs100P) ∧
      Nat.card hs100FiveQ = 125 ∧ Monoid.exponent hs100FiveQ = 5) ∧
    ({H : Subgroup (Equiv.Perm (Fin 100)) | H ≤ hs100FiveQ ∧ Nat.card H = 5} =
        Set.range (fun j : Fin 31 => zpowers (hs100FiveLine j)) ∧
      Function.Injective (fun j : Fin 31 => zpowers (hs100FiveLine j))) ∧
    (∀ j : Fin 31, hs100FiveTransporter j ∈ hs100R ∧
      hs100FiveTransporter j * hs100FiveLine (hs100FiveRecordOf j) *
        (hs100FiveTransporter j)⁻¹ = hs100FiveLine j) ∧
    (∀ j : Fin 31, (hs100FiveRecordOf j : ℕ) ∈ ({0, 2, 23} : Finset ℕ)) ∧
    (hs100FiveRecordOf 0 = 0 ∧ hs100FiveRecordOf 2 = 2 ∧ hs100FiveRecordOf 23 = 23) ∧
    (hs100FiveC0 = centralizer {hs100FiveLine 0} ⊓ hs100R ∧ Nat.card hs100FiveC0 = 50) ∧
    (hs100FiveC2 = centralizer {hs100FiveLine 2} ⊓ hs100R ∧ Nat.card hs100FiveC2 = 600) ∧
    (hs100FiveC23 = centralizer {hs100FiveLine 23} ⊓ hs100R ∧ Nat.card hs100FiveC23 = 1000) ∧
    (hs100FiveA0 ≤ hs100FiveC0 ∧ (hs100FiveA0.subgroupOf hs100FiveC0).Normal ∧
      hs100FiveA0 ≤ hs100P ∧ Nat.card hs100FiveA0 = 25 ∧ Monoid.exponent hs100FiveA0 = 5 ∧
      Nat.card (centralizer (hs100FiveA0 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC0 :
        Subgroup (Equiv.Perm (Fin 100))) = 25 ∧
      centralizer (hs100FiveA0 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC0 ≤ hs100FiveA0) ∧
    (hs100FiveA23 ≤ hs100FiveC23 ∧ (hs100FiveA23.subgroupOf hs100FiveC23).Normal ∧
      hs100FiveA23 ≤ hs100P ∧ Nat.card hs100FiveA23 = 125 ∧ Monoid.exponent hs100FiveA23 = 5 ∧
      Nat.card (centralizer (hs100FiveA23 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC23 :
        Subgroup (Equiv.Perm (Fin 100))) = 5 ∧
      centralizer (hs100FiveA23 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC23 ≤ hs100FiveA23) ∧
    (IsSimpleGroup hs100FiveD2 ∧ (∃ g ∈ hs100FiveD2, ∃ h ∈ hs100FiveD2, g * h ≠ h * g) ∧
      Nat.card hs100FiveD2 = 60 ∧ hs100FiveD2 ≤ hs100P ∧
      centralizer (hs100FiveD2 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC2 =
        zpowers (hs100FiveLine 2) ∧
      Nat.card (centralizer (hs100FiveD2 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC2 :
        Subgroup (Equiv.Perm (Fin 100))) = 5) :=
  ⟨⟨hs100FiveQ_le_P, hs100FiveQ_sylow, card_hs100FiveQ,
      linesOK_exponent hs100FiveKeys_lt hs100Five_lines_ok⟩,
    linesOK_lines hs100FiveKeys_lt hs100Five_lines_ok, hs100FiveTransporter_spec,
    hs100FiveRecordOf_mem, hs100FiveRecordOf_reps, hs100FiveC0_spec, hs100FiveC2_spec,
    hs100FiveC23_spec, hs100FiveA0_spec, hs100FiveA23_spec, hs100FiveD2_spec⟩

theorem R3E_McL_full_five_centralizer_structures :
    (mcl275FiveQ ≤ mcl275P ∧
      (∃ S : Sylow 5 mcl275P, (S : Subgroup mcl275P) = mcl275FiveQ.subgroupOf mcl275P) ∧
      Nat.card mcl275FiveQ = 125 ∧ Monoid.exponent mcl275FiveQ = 5) ∧
    ({H : Subgroup (Equiv.Perm (Fin 275)) | H ≤ mcl275FiveQ ∧ Nat.card H = 5} =
        Set.range (fun j : Fin 31 => zpowers (mcl275FiveLine j)) ∧
      Function.Injective (fun j : Fin 31 => zpowers (mcl275FiveLine j))) ∧
    (∀ j : Fin 31, mcl275FiveTransporter j ∈ mcl275R ∧
      mcl275FiveTransporter j * mcl275FiveLine (mcl275FiveRecordOf j) *
        (mcl275FiveTransporter j)⁻¹ = mcl275FiveLine j) ∧
    (∀ j : Fin 31, (mcl275FiveRecordOf j : ℕ) ∈ ({0, 1} : Finset ℕ)) ∧
    (mcl275FiveRecordOf 0 = 0 ∧ mcl275FiveRecordOf 1 = 1) ∧
    (mcl275FiveC0 = centralizer {mcl275FiveLine 0} ⊓ mcl275R ∧ Nat.card mcl275FiveC0 = 50) ∧
    (mcl275FiveC1 = centralizer {mcl275FiveLine 1} ⊓ mcl275R ∧ Nat.card mcl275FiveC1 = 1500) ∧
    (mcl275FiveA0 ≤ mcl275FiveC0 ∧ (mcl275FiveA0.subgroupOf mcl275FiveC0).Normal ∧
      mcl275FiveA0 ≤ mcl275P ∧ Nat.card mcl275FiveA0 = 25 ∧ Monoid.exponent mcl275FiveA0 = 5 ∧
      Nat.card (centralizer (mcl275FiveA0 : Set (Equiv.Perm (Fin 275))) ⊓ mcl275FiveC0 :
        Subgroup (Equiv.Perm (Fin 275))) = 25 ∧
      centralizer (mcl275FiveA0 : Set (Equiv.Perm (Fin 275))) ⊓ mcl275FiveC0 ≤ mcl275FiveA0) ∧
    (mcl275FiveA1 ≤ mcl275FiveC1 ∧ (mcl275FiveA1.subgroupOf mcl275FiveC1).Normal ∧
      mcl275FiveA1 ≤ mcl275P ∧ Nat.card mcl275FiveA1 = 125 ∧ Monoid.exponent mcl275FiveA1 = 5 ∧
      Nat.card (centralizer (mcl275FiveA1 : Set (Equiv.Perm (Fin 275))) ⊓ mcl275FiveC1 :
        Subgroup (Equiv.Perm (Fin 275))) = 5 ∧
      centralizer (mcl275FiveA1 : Set (Equiv.Perm (Fin 275))) ⊓ mcl275FiveC1 ≤ mcl275FiveA1) :=
  ⟨⟨mcl275FiveQ_le_P, mcl275FiveQ_sylow, card_mcl275FiveQ,
      linesOK_exponent mcl275FiveKeys_lt mcl275Five_lines_ok⟩,
    linesOK_lines mcl275FiveKeys_lt mcl275Five_lines_ok, mcl275FiveTransporter_spec,
    mcl275FiveRecordOf_mem, mcl275FiveRecordOf_reps, mcl275FiveC0_spec, mcl275FiveC1_spec,
    mcl275FiveA0_spec, mcl275FiveA1_spec⟩

theorem R3E_HS_McL_full_five_centralizer_structures :
    ((hs100FiveQ ≤ hs100P ∧
      (∃ S : Sylow 5 hs100P, (S : Subgroup hs100P) = hs100FiveQ.subgroupOf hs100P) ∧
      Nat.card hs100FiveQ = 125 ∧ Monoid.exponent hs100FiveQ = 5) ∧
    ({H : Subgroup (Equiv.Perm (Fin 100)) | H ≤ hs100FiveQ ∧ Nat.card H = 5} =
        Set.range (fun j : Fin 31 => zpowers (hs100FiveLine j)) ∧
      Function.Injective (fun j : Fin 31 => zpowers (hs100FiveLine j))) ∧
    (∀ j : Fin 31, hs100FiveTransporter j ∈ hs100R ∧
      hs100FiveTransporter j * hs100FiveLine (hs100FiveRecordOf j) *
        (hs100FiveTransporter j)⁻¹ = hs100FiveLine j) ∧
    (∀ j : Fin 31, (hs100FiveRecordOf j : ℕ) ∈ ({0, 2, 23} : Finset ℕ)) ∧
    (hs100FiveRecordOf 0 = 0 ∧ hs100FiveRecordOf 2 = 2 ∧ hs100FiveRecordOf 23 = 23) ∧
    (hs100FiveC0 = centralizer {hs100FiveLine 0} ⊓ hs100R ∧ Nat.card hs100FiveC0 = 50) ∧
    (hs100FiveC2 = centralizer {hs100FiveLine 2} ⊓ hs100R ∧ Nat.card hs100FiveC2 = 600) ∧
    (hs100FiveC23 = centralizer {hs100FiveLine 23} ⊓ hs100R ∧ Nat.card hs100FiveC23 = 1000) ∧
    (hs100FiveA0 ≤ hs100FiveC0 ∧ (hs100FiveA0.subgroupOf hs100FiveC0).Normal ∧
      hs100FiveA0 ≤ hs100P ∧ Nat.card hs100FiveA0 = 25 ∧ Monoid.exponent hs100FiveA0 = 5 ∧
      Nat.card (centralizer (hs100FiveA0 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC0 :
        Subgroup (Equiv.Perm (Fin 100))) = 25 ∧
      centralizer (hs100FiveA0 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC0 ≤ hs100FiveA0) ∧
    (hs100FiveA23 ≤ hs100FiveC23 ∧ (hs100FiveA23.subgroupOf hs100FiveC23).Normal ∧
      hs100FiveA23 ≤ hs100P ∧ Nat.card hs100FiveA23 = 125 ∧ Monoid.exponent hs100FiveA23 = 5 ∧
      Nat.card (centralizer (hs100FiveA23 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC23 :
        Subgroup (Equiv.Perm (Fin 100))) = 5 ∧
      centralizer (hs100FiveA23 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC23 ≤ hs100FiveA23) ∧
    (IsSimpleGroup hs100FiveD2 ∧ (∃ g ∈ hs100FiveD2, ∃ h ∈ hs100FiveD2, g * h ≠ h * g) ∧
      Nat.card hs100FiveD2 = 60 ∧ hs100FiveD2 ≤ hs100P ∧
      centralizer (hs100FiveD2 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC2 =
        zpowers (hs100FiveLine 2) ∧
      Nat.card (centralizer (hs100FiveD2 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC2 :
        Subgroup (Equiv.Perm (Fin 100))) = 5)) ∧
    ((mcl275FiveQ ≤ mcl275P ∧
      (∃ S : Sylow 5 mcl275P, (S : Subgroup mcl275P) = mcl275FiveQ.subgroupOf mcl275P) ∧
      Nat.card mcl275FiveQ = 125 ∧ Monoid.exponent mcl275FiveQ = 5) ∧
    ({H : Subgroup (Equiv.Perm (Fin 275)) | H ≤ mcl275FiveQ ∧ Nat.card H = 5} =
        Set.range (fun j : Fin 31 => zpowers (mcl275FiveLine j)) ∧
      Function.Injective (fun j : Fin 31 => zpowers (mcl275FiveLine j))) ∧
    (∀ j : Fin 31, mcl275FiveTransporter j ∈ mcl275R ∧
      mcl275FiveTransporter j * mcl275FiveLine (mcl275FiveRecordOf j) *
        (mcl275FiveTransporter j)⁻¹ = mcl275FiveLine j) ∧
    (∀ j : Fin 31, (mcl275FiveRecordOf j : ℕ) ∈ ({0, 1} : Finset ℕ)) ∧
    (mcl275FiveRecordOf 0 = 0 ∧ mcl275FiveRecordOf 1 = 1) ∧
    (mcl275FiveC0 = centralizer {mcl275FiveLine 0} ⊓ mcl275R ∧ Nat.card mcl275FiveC0 = 50) ∧
    (mcl275FiveC1 = centralizer {mcl275FiveLine 1} ⊓ mcl275R ∧ Nat.card mcl275FiveC1 = 1500) ∧
    (mcl275FiveA0 ≤ mcl275FiveC0 ∧ (mcl275FiveA0.subgroupOf mcl275FiveC0).Normal ∧
      mcl275FiveA0 ≤ mcl275P ∧ Nat.card mcl275FiveA0 = 25 ∧ Monoid.exponent mcl275FiveA0 = 5 ∧
      Nat.card (centralizer (mcl275FiveA0 : Set (Equiv.Perm (Fin 275))) ⊓ mcl275FiveC0 :
        Subgroup (Equiv.Perm (Fin 275))) = 25 ∧
      centralizer (mcl275FiveA0 : Set (Equiv.Perm (Fin 275))) ⊓ mcl275FiveC0 ≤ mcl275FiveA0) ∧
    (mcl275FiveA1 ≤ mcl275FiveC1 ∧ (mcl275FiveA1.subgroupOf mcl275FiveC1).Normal ∧
      mcl275FiveA1 ≤ mcl275P ∧ Nat.card mcl275FiveA1 = 125 ∧ Monoid.exponent mcl275FiveA1 = 5 ∧
      Nat.card (centralizer (mcl275FiveA1 : Set (Equiv.Perm (Fin 275))) ⊓ mcl275FiveC1 :
        Subgroup (Equiv.Perm (Fin 275))) = 5 ∧
      centralizer (mcl275FiveA1 : Set (Equiv.Perm (Fin 275))) ⊓ mcl275FiveC1 ≤ mcl275FiveA1)) :=
  ⟨R3E_HS_full_five_centralizer_structures, R3E_McL_full_five_centralizer_structures⟩

end CFSG.RankThree.Native
