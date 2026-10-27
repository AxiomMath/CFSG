module

public import CFSG.RankThree.PartTwo.Sec13.K135ZmBasis
public import CFSG.RankThree.PartTwo.Sec13.F135LastKDefs
public import CFSG.RankThree.Asc83Table.MatCert
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import Certificates.Certificate40400

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last.K135

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

theorem inv_mem_triples : ∀ i j k : ZMod 4, i + i = 0 → j + j = 0 → k + k = 0 →
    ¬ (i = 0 ∧ j = 0 ∧ k = 0) → (i.val, j.val, k.val) ∈ invTriples := by
  decide

theorem inv_mem_facts (i j k : ZMod 4) (hi : i + i = 0) (hj : j + j = 0) (hk : k + k = 0)
    (hnz : ¬ (i = 0 ∧ j = 0 ∧ k = 0)) : MFact.ne (wA i.val j.val k.val) [] 0 ∈ onFacts := by
  have h := inv_mem_triples i j k hi hj hk hnz
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨_, h, rfl⟩))

theorem inv_mem_facts_conj (i j k : ZMod 4) (hi : i + i = 0) (hj : j + j = 0) (hk : k + k = 0)
    (hnz : ¬ (i = 0 ∧ j = 0 ∧ k = 0)) :
    MFact.ne (conjX (wA i.val j.val k.val)) (wA i.val j.val k.val) 0 ∈ onFacts := by
  have h := inv_mem_triples i j k hi hj hk hnz
  exact List.mem_append_right _ (List.mem_map.2 ⟨_, h, rfl⟩)

theorem four_mul_zmod (z : ZMod 4) : z + z + (z + z) = 0 := by
  revert z
  decide

theorem fin3_eta {α : Type*} (f : Fin 3 → α) : f = ![f 0, f 1, f 2] := by
  funext i
  fin_cases i <;> rfl

theorem val_zmod4_zero : (0 : ZMod 4).val = 0 := rfl
theorem val_zmod4_one : (1 : ZMod 4).val = 1 := rfl
theorem val_zmod4_two : (2 : ZMod 4).val = 2 := rfl

noncomputable section

section Check

variable (hC : mcertCheck (opsP 3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2 onCert = true)

def ru (r : Nat) : NativeSporadic.ON := regUnit (specP 3 154) hC r

def wu (w : Word) : NativeSporadic.ON := wordUnit (specP 3 154) hC w

def aU : Fin 3 → NativeSporadic.ON
  | 0 => ru hC regA0
  | 1 => ru hC regA1
  | 2 => ru hC regA2

theorem hasOrd_of_regs {w : Word}
    (h : ∀ q ∈ w, q.1 = regA0 ∨ q.1 = regA1 ∨ q.1 = regA2 ∨ q.1 = regX) : HasOrd onCert w := by
  intro q hq
  rcases h q hq with h | h | h | h <;> rw [h]
  · exact ⟨4, by simp [onCert, onFacts]⟩
  · exact ⟨4, by simp [onCert, onFacts]⟩
  · exact ⟨4, by simp [onCert, onFacts]⟩
  · exact ⟨7, by simp [onCert, onFacts]⟩

theorem hasOrd_wA (i j k : Nat) : HasOrd onCert (wA i j k) := by
  refine hasOrd_of_regs fun q hq => ?_
  simp only [wA, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> simp

theorem hasOrd_conjX {w : Word} (hw : HasOrd onCert w) : HasOrd onCert (conjX w) := by
  unfold conjX
  refine hasOrd_append (hasOrd_append ?_ hw) ?_
  · exact hasOrd_of_regs fun q hq => by simp at hq; simp [hq]
  · exact hasOrd_of_regs fun q hq => by simp at hq; simp [hq]

theorem ru_pow4 : ∀ i, aU hC i ^ 4 = 1
  | 0 => regUnit_pow (specP 3 154) hC (e := 4) (by simp [onCert, onFacts])
  | 1 => regUnit_pow (specP 3 154) hC (e := 4) (by simp [onCert, onFacts])
  | 2 => regUnit_pow (specP 3 154) hC (e := 4) (by simp [onCert, onFacts])

theorem wu_nil : wu hC [] = 1 := wordUnit_nil (specP 3 154) hC

theorem wu_cons (q : Nat × Nat) (w : Word) : wu hC (q :: w) = ru hC q.1 ^ q.2 * wu hC w :=
  wordUnit_cons (specP 3 154) hC q w

theorem wu_append (w₁ w₂ : Word) : wu hC (w₁ ++ w₂) = wu hC w₁ * wu hC w₂ :=
  wordUnit_append (specP 3 154) hC w₁ w₂

theorem wu_wA (i j k : Nat) : wu hC (wA i j k) = aU hC 0 ^ i * aU hC 1 ^ j * aU hC 2 ^ k := by
  simp [wA, wu_cons, wu_nil, aU, mul_assoc]

theorem fcBasisProd_eq_wu (f : Fin 3 → ZMod 4) :
    fcBasisProd (aU hC) f = wu hC (wA (f 0).val (f 1).val (f 2).val) := by
  rw [wu_wA]
  simp [fcBasisProd, List.ofFn_succ, mul_assoc]

theorem ru_comm {r s : Nat} (hr : MFact.eq [(r, 1), (s, 1)] [(s, 1), (r, 1)] ∈ onCert.facts)
    (h1 : HasOrd onCert [(r, 1), (s, 1)]) (h2 : HasOrd onCert [(s, 1), (r, 1)]) :
    Commute (ru hC r) (ru hC s) := by
  have := regUnit_eq (specP 3 154) hC hr h1 h2
  have e : ru hC r * ru hC s = ru hC s * ru hC r := by
    simpa [wordUnit_cons, wordUnit_nil, ru] using this
  exact e

theorem ru_comm01 : Commute (ru hC regA0) (ru hC regA1) :=
  ru_comm hC (by simp [onCert, onFacts])
    (hasOrd_of_regs fun q hq => by simp at hq; rcases hq with rfl | rfl <;> simp)
    (hasOrd_of_regs fun q hq => by simp at hq; rcases hq with rfl | rfl <;> simp)

theorem ru_comm02 : Commute (ru hC regA0) (ru hC regA2) :=
  ru_comm hC (by simp [onCert, onFacts])
    (hasOrd_of_regs fun q hq => by simp at hq; rcases hq with rfl | rfl <;> simp)
    (hasOrd_of_regs fun q hq => by simp at hq; rcases hq with rfl | rfl <;> simp)

theorem ru_comm12 : Commute (ru hC regA1) (ru hC regA2) :=
  ru_comm hC (by simp [onCert, onFacts])
    (hasOrd_of_regs fun q hq => by simp at hq; rcases hq with rfl | rfl <;> simp)
    (hasOrd_of_regs fun q hq => by simp at hq; rcases hq with rfl | rfl <;> simp)

theorem aU_comm : ∀ i j, Commute (aU hC i) (aU hC j)
  | 0, 0 => Commute.refl _
  | 0, 1 => ru_comm01 hC
  | 0, 2 => ru_comm02 hC
  | 1, 0 => (ru_comm01 hC).symm
  | 1, 1 => Commute.refl _
  | 1, 2 => ru_comm12 hC
  | 2, 0 => (ru_comm02 hC).symm
  | 2, 1 => (ru_comm12 hC).symm
  | 2, 2 => Commute.refl _

theorem ru_pow7 : ru hC regX ^ 7 = 1 :=
  regUnit_pow (specP 3 154) hC (e := 7) (by simp [onCert, onFacts])

theorem wu_ne_one {w : Word} (hw : HasOrd onCert w) (hf : MFact.ne w [] 0 ∈ onFacts) :
    wu hC w ≠ 1 := by
  have := regUnit_ne (specP 3 154) hC (w₁ := w) (w₂ := []) (t := 0) hf hw (hasOrd_nil onCert)
  simpa [wordUnit_nil, wu] using this

theorem ru_ne_one : ru hC regX ≠ 1 := by
  have h := wu_ne_one hC (w := [(regX, 1)])
    (hasOrd_of_regs fun q hq => by simp at hq; simp [hq]) (by simp [onFacts])
  simpa [wu_cons, wu_nil] using h

theorem orderOf_ru_x : orderOf (ru hC regX) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime (ru_pow7 hC) (ru_ne_one hC)

theorem ker_four (f : Fin 3 → ZMod 4) (hf : f + f = 0) (h1 : fcBasisProd (aU hC) f = 1) :
    f = 0 := by
  by_contra hf0
  have h0 : f 0 + f 0 = 0 := by simpa using congrFun hf 0
  have h1' : f 1 + f 1 = 0 := by simpa using congrFun hf 1
  have h2 : f 2 + f 2 = 0 := by simpa using congrFun hf 2
  have hnz : ¬ (f 0 = 0 ∧ f 1 = 0 ∧ f 2 = 0) := by
    rintro ⟨a, b, c⟩
    exact hf0 (by rw [fin3_eta f, a, b, c]; funext i; fin_cases i <;> rfl)
  have hmem := inv_mem_facts (f 0) (f 1) (f 2) h0 h1' h2 hnz
  rw [fcBasisProd_eq_wu hC] at h1
  exact wu_ne_one hC (hasOrd_wA _ _ _) hmem h1

theorem aU_inj : Function.Injective (fcBasisProd (aU hC)) := by
  have hc := aU_comm hC
  have ha := ru_pow4 hC
  intro f g hfg
  have hsub : fcBasisProd (aU hC) (f - g) = 1 := by
    have h := fcBasisProd_add ha hc (f - g) g
    rw [sub_add_cancel] at h
    rw [h] at hfg
    exact mul_right_cancel (hfg.trans (one_mul _).symm)
  have hz : f - g = 0 := by
    have h2 : fcBasisProd (aU hC) ((f - g) + (f - g)) = 1 := by
      rw [fcBasisProd_add ha hc, hsub, one_mul]
    have h4 : ((f - g) + (f - g)) + ((f - g) + (f - g)) = 0 :=
      funext fun i => four_mul_zmod ((f - g) i)
    have hdd : (f - g) + (f - g) = 0 := ker_four hC _ h4 h2
    exact ker_four hC _ hdd hsub
  exact sub_eq_zero.mp hz

def Mmat : Fin 3 → Fin 3 → ZMod 4 := ![![0, 0, 1], ![1, 0, 2], ![0, 1, 1]]

theorem conj_ru {r : Nat} {w : Word} (hf : MFact.conj regX [(r, 1)] w ∈ onCert.facts)
    (hu : HasOrd onCert [(r, 1)]) (hw : HasOrd onCert w) :
    ru hC regX * ru hC r * (ru hC regX)⁻¹ = wu hC w := by
  have := regUnit_conj (specP 3 154) hC (h := regX) (e₁ := 7) (u := [(r, 1)]) (w := w) hf
    (by simp [onCert, onFacts]) hu hw
  simpa [wordUnit_cons, wordUnit_nil, ru, wu] using this

theorem hconj_aU (j : Fin 3) :
    ru hC regX * aU hC j * (ru hC regX)⁻¹ = fcBasisProd (aU hC) fun i => Mmat i j := by
  rw [fcBasisProd_eq_wu hC]
  fin_cases j
  · exact conj_ru hC (r := regA0) (w := wA 0 1 0) (by simp [onCert, onFacts])
      (hasOrd_of_regs fun q hq => by simp at hq; simp [hq]) (hasOrd_wA _ _ _)
  · exact conj_ru hC (r := regA1) (w := wA 0 0 1) (by simp [onCert, onFacts])
      (hasOrd_of_regs fun q hq => by simp at hq; simp [hq]) (hasOrd_wA _ _ _)
  · exact conj_ru hC (r := regA2) (w := wA 1 2 1) (by simp [onCert, onFacts])
      (hasOrd_of_regs fun q hq => by simp at hq; simp [hq]) (hasOrd_wA _ _ _)

theorem inv_ru_x : (ru hC regX)⁻¹ = ru hC regX ^ 6 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ']
  exact ru_pow7 hC

theorem hfpf_aU (f : Fin 3 → ZMod 4) (hff : f + f = 0) (hf0 : f ≠ 0) :
    ru hC regX * fcBasisProd (aU hC) f * (ru hC regX)⁻¹ ≠ fcBasisProd (aU hC) f := by
  have h0 : f 0 + f 0 = 0 := by simpa using congrFun hff 0
  have h1' : f 1 + f 1 = 0 := by simpa using congrFun hff 1
  have h2 : f 2 + f 2 = 0 := by simpa using congrFun hff 2
  have hnz : ¬ (f 0 = 0 ∧ f 1 = 0 ∧ f 2 = 0) := by
    rintro ⟨a, b, c⟩
    exact hf0 (by rw [fin3_eta f, a, b, c]; funext i; fin_cases i <;> rfl)
  have hmem := inv_mem_facts_conj (f 0) (f 1) (f 2) h0 h1' h2 hnz
  have hne := regUnit_ne (specP 3 154) hC hmem (hasOrd_conjX (hasOrd_wA _ _ _))
    (hasOrd_wA _ _ _)
  intro heq
  apply hne
  have e1 : wordUnit (specP 3 154) hC (conjX (wA (f 0).val (f 1).val (f 2).val)) =
      ru hC regX * wu hC (wA (f 0).val (f 1).val (f 2).val) * (ru hC regX)⁻¹ := by
    rw [inv_ru_x hC]
    change wu hC (conjX (wA (f 0).val (f 1).val (f 2).val)) = _
    simp [conjX, wu_append, wu_cons, wu_nil, mul_assoc]
  rw [e1]
  rw [fcBasisProd_eq_wu hC] at heq
  exact heq

theorem fourCubeSeven_of_check :
    FourCubeSeven (Subgroup.closure (Set.range (aU hC))) (ru hC regX) :=
  fourCubeSeven_of_basis (ru_pow4 hC) (aU_comm hC) (aU_inj hC) (orderOf_ru_x hC) Mmat
    (fun j => by rw [← hconj_aU hC j]) (hfpf_aU hC)

end Check

end

end CFSG.RankThree.PartTwo.Sec13.F135Last.K135

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

theorem kFactFourCubeSeven_holds : KFactFourCubeSeven :=
  ⟨_, _, K135.fourCubeSeven_of_check Certificates.certificate40400⟩

end CFSG.RankThree.PartTwo.Sec13.F135Last
