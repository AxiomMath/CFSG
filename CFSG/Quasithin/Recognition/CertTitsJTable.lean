module

public import CFSG.Sporadic.Schreier.TitsCentral
public import CFSG.Quasithin.Recognition.CertTitsJCheck
public import CFSG.Sporadic.Schreier.TitsPrim

public noncomputable section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier.Tits

theorem permOfArr_eq_of_rep' {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n t g) :
    permOfArr n t = g := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j :=
    ⟨fun i hi => h.lt hi, fun i hi j hj hij => by
      rw [h.apply hi, h.apply hj] at hij
      have := g.injective (Fin.ext hij)
      simpa using this⟩
  ext x
  rw [permOfArr, dite_eq_left hc]
  change t[(x : ℕ)]! = _
  exact h x

@[expose] def jEl (i : Fin 512) : Equiv.Perm (Fin 1755) := permOfArr 1755 jPel[(i : ℕ)]!

theorem jPel_size : jPel.size = 512 := jModel_check.1

theorem titsQJ_chainArrays :
    ChainArrays titsQJ (titsJArrs.extract 0 4) titsJArrs (baseArr 1755 titsJBase)
      (wordsArr 4 9 titsJDerivations) :=
  chainArrays_ofArrays' titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsQJ_baseCount : titsQJ.baseCount = 4 := rfl

theorem jPel_spec :
    (∀ i < jPel.size, ∃ g ∈ titsJ, Rep 1755 jPel[i]! g) ∧
    (∀ g ∈ titsJ, ∃ i < jPel.size, Rep 1755 jPel[i]! g) := by
  have h := table4_spec titsQJ_chainArrays (by norm_num : 0 < 4) titsLocalChains_check.2.2.2.1
    titsQJ_baseCount
  rw [titsQJ_facts.2.2.1] at h
  exact h

theorem jEl_rep
    (i : Fin 512) : Rep 1755 jPel[(i : ℕ)]! (jEl i) := by
  obtain ⟨g, -, hg⟩ := jPel_spec.1 i (by rw [jPel_size]; exact i.2)
  rw [jEl, permOfArr_eq_of_rep' hg]
  exact hg

theorem jEl_mem
    (i : Fin 512) : jEl i ∈ titsJ := by
  obtain ⟨g, hgJ, hg⟩ := jPel_spec.1 i (by rw [jPel_size]; exact i.2)
  rw [jEl, permOfArr_eq_of_rep' hg]
  exact hgJ

theorem jEl_surj
    {g : Equiv.Perm (Fin 1755)} (hg : g ∈ titsJ) : ∃ i, jEl i = g := by
  obtain ⟨i, hi, hrep⟩ := jPel_spec.2 g hg
  refine ⟨⟨i, by rwa [jPel_size] at hi⟩, ?_⟩
  rw [jEl]
  exact permOfArr_eq_of_rep' hrep

theorem jEl_inj
    : Function.Injective jEl := by
  intro i j hij
  by_contra hne
  have h := (jModel_check.2.2.2.2.2.2.2.2.2.1)
  have := allLt_spec (allLt_spec h i.2) j.2
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
  rcases this with h1 | h1
  · exact hne (Fin.ext h1)
  · have := (eqA_iff (jEl_rep i) (jEl_rep j)).2 hij
    rw [this] at h1
    exact Bool.noConfusion h1

theorem titsQJ_base_toList
    : titsQJ.base.toList = finList 1755 titsJBase := by
  rw [titsQJ, RawSchreierDatum.ofArrays_base_toList]

theorem titsQJ_base_mem
    {b : Fin 1755} (hb : b ∈ titsQJ.base.toList) :
    (b : ℕ) = 5 ∨ (b : ℕ) = 1 ∨ (b : ℕ) = 24 ∨ (b : ℕ) = 12 := by
  rw [titsQJ_base_toList, finList, jModel_check.2.1] at hb
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> simp [finPt]

theorem jEl_agree
    {g h : Equiv.Perm (Fin 1755)} (hg : g ∈ titsJ) (hh : h ∈ titsJ)
    (hbase : ∀ b : Fin 1755, ((b : ℕ) = 5 ∨ (b : ℕ) = 1 ∨ (b : ℕ) = 24 ∨ (b : ℕ) = 12) →
      g b = h b) : g = h := by
  refine eq_of_agree_base (Q := titsQJ) titsQJ_facts.1 ?_ ?_ fun b hb => hbase b (titsQJ_base_mem hb)
  · rw [titsQJ_facts.2.2.1]; exact hg
  · rw [titsQJ_facts.2.2.1]; exact hh

theorem jEl_mul
    (i j : Fin 512) : jEl (jOps.mul i j) = jEl i * jEl j := by
  have h := allLt_spec (allLt_spec jModel_check.2.2.2.1 i.2) j.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlt, hall⟩ := h
  have hk : ((jOps.mul i j : Fin 512) : ℕ) = (jMulT[(i : ℕ)]!)[(j : ℕ)]! := finPt_val hlt
  refine jEl_agree (jEl_mem _) (mul_mem (jEl_mem i) (jEl_mem j)) fun b hb => ?_
  have hb' : (b : ℕ) ∈ titsJBase := by
    rw [jModel_check.2.1]
    simpa using hb
  have h1 := List.all_eq_true.1 hall (b : ℕ) hb'
  rw [beq_iff_eq, ← hk] at h1
  have e1 := jEl_rep (jOps.mul i j) b
  have e2 := jEl_rep j b
  have e3 := jEl_rep i (jEl j b)
  apply Fin.ext
  rw [Equiv.Perm.mul_apply, ← e1, h1, e2]
  exact e3

theorem jEl_inv
    (i : Fin 512) : jEl (jOps.inv i) = (jEl i)⁻¹ := by
  have h := allLt_spec jModel_check.2.2.2.2.1 i.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlt, hinv⟩, heq⟩ := h
  have hk : ((jOps.inv i : Fin 512) : ℕ) = jInvT[(i : ℕ)]! := finPt_val hlt
  have hrep := rep_inv_of_isInvA (jEl_rep i) hinv
  rw [← hk] at heq
  exact ((eqA_iff hrep (jEl_rep (jOps.inv i))).1 heq).symm

theorem jEl_one
    : jEl jOps.one = 1 := by
  have hlt : jOneI < 512 := jModel_check.2.2.2.2.2.1
  have hk : ((jOps.one : Fin 512) : ℕ) = jOneI := finPt_val hlt
  have h := jModel_check.2.2.2.2.2.2.1
  rw [← hk] at h
  exact ((eqA_iff (jEl_rep jOps.one) rep_idA).1 h)

theorem jEl_z
    : jEl jOps.zI = titsZ := by
  have hlt : jZI < 512 := jModel_check.2.2.2.2.2.2.2.1
  have hk : ((jOps.zI : Fin 512) : ℕ) = jZI := finPt_val hlt
  have h := jModel_check.2.2.2.2.2.2.2.2.1
  rw [← hk] at h
  exact (eqA_iff (jEl_rep jOps.zI) titsZ_rep).1 h

@[expose] def jGen (k : Fin 3) : Equiv.Perm (Fin 1755) :=
  wordIn 13 titsT (titsHWords.getD (k : ℕ) [])

theorem titsHWords_letters
    {w : List ℤ} (hw : w ∈ titsHWords) : lettersOK 13 w = true :=
  titsLocalWords_letters titsLocalWords_mem.1 hw

theorem jGen_rep
    (k : Fin 3) : Rep 1755 jGenArrs[(k : ℕ)]! (jGen k) := by
  have hi' : (k : ℕ) < titsHWords.length := by rw [titsHWords_eq]; exact k.2
  have e : jGenArrs[(k : ℕ)]! = wordArr 1755 titsDerivedArrs titsHWords[(k : ℕ)] := by
    rw [jGenArrs, getElem!_pos _ (k : ℕ) (by simp [titsHWords_eq])]
    simp
  rw [e, jGen, getD_eq_get hi']
  exact rep_wordArr_titsT (titsHWords_letters (List.getElem_mem _))

theorem jGen_mem (k : Fin 3) : jGen k ∈ titsH := by
  have hi' : (k : ℕ) < titsHWords.length := by rw [titsHWords_eq]; exact k.2
  rw [jGen, getD_eq_get hi']
  exact titsH_word_mem (List.getElem_mem _)

theorem jEl_cj
    (k : Fin 3) (i : Fin 512) : jEl (jCj k i) = jGen k * jEl i * (jGen k)⁻¹ := by
  have h := allLt_spec (allLt_spec jModel_check.2.2.2.2.2.2.2.2.2.2.2.1 k.2) i.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlt, heq⟩ := h
  have hk : ((jCj k i : Fin 512) : ℕ) = (jCjT[(k : ℕ)]!)[(i : ℕ)]! := finPt_val hlt
  have hinvA := allLt_spec jModel_check.2.2.2.2.2.2.2.2.2.2.1 k.2
  have hrinv := rep_inv_of_isInvA (jGen_rep k) hinvA
  have hr := rep_compA (rep_compA (jGen_rep k) (jEl_rep i)) hrinv
  rw [← hk] at heq
  exact ((eqA_iff hr (jEl_rep (jCj k i))).1 heq).symm

@[expose] def jC0 : Equiv.Perm (Fin 1755) := wordIn 13 titsT [3, 4, 13]

@[expose] def jC : Equiv.Perm (Fin 1755) := jC0 * jC0

theorem jC0_rep : Rep 1755 jC0Arr jC0 :=
  rep_wordArr_titsT (by decide : lettersOK 13 [3, 4, 13] = true)

theorem jC_rep : Rep 1755 jCArr jC := rep_compA jC0_rep jC0_rep

theorem jC_mem
    : jC ∈ titsH := mul_mem mem_titsH_3_4_13 mem_titsH_3_4_13

theorem jEl_cc
    (i : Fin 512) : jEl (jCc i) = jC * jEl i * jC⁻¹ := by
  have h := allLt_spec jModel_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlt, heq⟩ := h
  have hk : ((jCc i : Fin 512) : ℕ) = jCcT[(i : ℕ)]! := finPt_val hlt
  have hrinv := rep_inv_of_isInvA jC_rep jModel_check.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hr := rep_compA (rep_compA jC_rep (jEl_rep i)) hrinv
  rw [← hk] at heq
  exact ((eqA_iff hr (jEl_rep (jCc i))).1 heq).symm

theorem jC_pow_five : jC ^ 5 = 1 := by
  have hr := rep_compA (rep_compA (rep_compA (rep_compA jC_rep jC_rep) jC_rep) jC_rep) jC_rep
  have h := (eqA_iff hr rep_idA).1 jModel_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_one]
  exact h

end CFSG.Quasithin
