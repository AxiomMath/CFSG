
module

public import CFSG.Quasithin.Recognition.CertTitsSimpleMainBase
import all CFSG.Quasithin.Recognition.CertTitsSimpleMainBase

public import CFSG.Quasithin.Recognition.CertTitsSimple

public section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

attribute [local irreducible] titsPairO titsPairStrong titsGens titsStrong

private theorem titsPair_mem_closure :
    permOfArr 1755 titsA ∈ Subgroup.closure {permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData1),
      permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData2)} ∧
    permOfArr 1755 titsB ∈ Subgroup.closure {permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData1),
      permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData2)} := by
  obtain ⟨hp1, hp2, -⟩ := titsChain_check
  obtain ⟨hA, hB, hlA, hlB, -⟩ := titsPair_check
  have hinv : ∀ j < 2, isInvA 1755 titsGens[j]! (rawInvs 1755 titsGens)[j]! = true := by
    intro j hj
    have hj' : j < titsGens.size := by rw [titsGens_size']; exact hj
    rw [rawInvs_getElem! hj']
    interval_cases j
    · rw [titsGens_zero']; exact hp1
    · rw [titsGens_one']; exact hp2
  have hmem : ∀ j < 2, permOfArr 1755 titsGens[j]! ∈ Subgroup.closure
      {permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData1),
        permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData2)} := by
    intro j hj
    interval_cases j
    · rw [titsGens_zero']
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [titsGens_one']
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have key : ∀ w : List ℤ, lettersOK titsGens.size w = true →
      ∃ g ∈ Subgroup.closure {permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData1),
        permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData2)},
        Rep 1755 (wordA 1755 titsGens (rawInvs 1755 titsGens) w) g := by
    intro w hw
    rw [titsGens_size'] at hw
    exact wordA_mem' (K := Subgroup.closure {permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData1),
        permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData2)}) (m := 2) (fun _ => True)
      (fun j hj => (rep_permOfArr (hinv j hj)).1) (fun j hj => (rep_permOfArr (hinv j hj)).2)
      (fun j hj _ => hmem j hj) w hw (fun _ _ => trivial)
  constructor
  · obtain ⟨g, hg, hrep⟩ := key _ hlA
    have := (rep_permOfArr hA).1.unique (show Rep 1755 titsA g from hrep)
    rw [this]
    exact hg
  · obtain ⟨g, hg, hrep⟩ := key _ hlB
    have := (rep_permOfArr hB).1.unique (show Rep 1755 titsB g from hrep)
    rw [this]
    exact hg

theorem isSimpleGroup_quasithinTits
    : IsSimpleGroup CFSG.Open.quasithinTits := by
  obtain ⟨hA, hB, -, -, hOS, hSO, hchain, horb, hprim, hA2, hA1, hB3, hB1, hab13, hab1⟩ :=
    titsPair_check
  have hrA := (rep_permOfArr hA).1
  have hrB := (rep_permOfArr hB).1
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have ha : orderOf (permOfArr 1755 titsPairO[0]!) = 2 := by
    rw [titsPairO_zero]
    exact orderOf_eq_prime_of_rep hrA hA2 hA1
  have hb : orderOf (permOfArr 1755 titsPairO[1]!) = 3 := by
    rw [titsPairO_one]
    exact orderOf_eq_prime_of_rep hrB hB3 hB1
  have hab : orderOf (permOfArr 1755 titsPairO[0]! * permOfArr 1755 titsPairO[1]!) = 13 := by
    rw [titsPairO_zero, titsPairO_one]
    exact orderOf_eq_prime_of_rep (rep_compA hrA hrB) hab13 hab1
  have hJ' := isSimpleGroup_of_chain_primitive (n := 1755) (k := 5) (by norm_num) (by norm_num)
    (O := titsPairO) (S := titsPairStrong) (W := titsPairRawWords) (base := titsPairBase)
    (by decide) (chunks := 4) (by norm_num) titsPairO_size hOS hSO hchain hprim
    (fun hx => tits_labelsDivisorOK) (m := 10240) (pa := 2) (pb := 3) (pc := 13)
    (by rw [horb]; norm_num) ha hb hab (by norm_num) (by norm_num)
  have hle : Subgroup.closure {g | ∃ k < titsPairO.size, permOfArr 1755 titsPairO[k]! = g} ≤
      Subgroup.closure {permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData1),
        permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData2)} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨k, hk, rfl⟩
    rw [titsPairO_size] at hk
    interval_cases k
    · rw [titsPairO_zero]
      exact titsPair_mem_closure.1
    · rw [titsPairO_one]
      exact titsPair_mem_closure.2
  have hcard' : Nat.card (Subgroup.closure {g | ∃ k < titsPairO.size,
      permOfArr 1755 titsPairO[k]! = g}) = 17971200 := by
    have := card_closure_permOfArr_of_rawChainOK (n := 1755) (by norm_num) (O := titsPairO)
      (S := titsPairStrong) (W := titsPairRawWords) (by decide) (chunks := 4) (by norm_num)
      hOS hSO hchain
    rw [horb] at this
    rw [this]
    norm_num
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [card_closure_tits_perm, hcard'])
  have hJ0 : IsSimpleGroup ↥(Subgroup.closure {permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData1),
      permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData2)}) := by
    rw [← heq]
    exact hJ'
  obtain ⟨hp1, hp2, -⟩ := titsChain_check
  exact (unitsClosurePairEquiv _ _ _ _ (coe_permOfArr_titsArray CFSG.Open.quasithinTitsData1 hp1)
    (coe_permOfArr_titsArray CFSG.Open.quasithinTitsData2 hp2)).isSimpleGroup

end CFSG.Quasithin
