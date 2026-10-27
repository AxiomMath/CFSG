module

public import CFSG.Sporadic.HNSchreier.Primitive
public import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNSchreier.StrongSpec
public import CFSG.Sporadic.HNSchreier.MaskSpec
public import CFSG.Sporadic.HN.Local.AltAbstract
public import Certificates.Certificate2100

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier Matrix
open CFSG.Sporadic.HN.Local (IsCanon Part card_part)

@[expose] def jRegs0 (r : ℕ) : JH := if r = 1 then aJ else if r = 2 then bJ else 1

@[expose] def jRegs : ℕ → JH := runProg jRegs0 Data.subgroupProgram

abbrev h1J : JH := jRegs 1

abbrev h2J : JH := jRegs 2

@[expose] def HJ : Subgroup JH := Subgroup.closure {h1J, h2J}

@[expose] def hJ (j : ℕ) : JH := gStrong [h1J, h2J] LocalData.strongWords j

@[expose] def seedWordJ (w : List ℕ) : JH := (w.map fun l => if l = 1 then aJ else bJ).prod

@[expose] def hWordJ (w : List ℤ) : JH :=
  (w.map fun l => if 0 < l then hJ (l.natAbs - 1) else (hJ (l.natAbs - 1))⁻¹).prod

@[expose] def xVecAux : ℕ → ℕ → Vec
  | 0, _ => matJ (seedWordJ LocalData.rootWord) *ᵥ fixedVector
  | f + 1, i =>
    if i = 0 then matJ (seedWordJ LocalData.rootWord) *ᵥ fixedVector
    else matJ (hJ (LocalData.parents[i]!.2 - 1)) *ᵥ xVecAux f LocalData.parents[i]!.1

@[expose] def xVec (i : ℕ) : Vec := xVecAux 462 i

@[expose, irreducible] def matS : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  decode 5 133 1 LocalData.normalizerPayload

theorem matS_eq : matS = decode 5 133 1 LocalData.normalizerPayload := by unfold matS; rfl

@[expose] def matCx : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  matJ (hWordJ LocalData.innerWord) * matJ (seedWordJ LocalData.outerWord)⁻¹ * matS

@[expose] def labelSet (k : ℕ) : Finset (Fin 12) := maskSet12 labMasks[k]!

theorem label_parts :
    labMasks.size = 462 ∧ LocalData.lperm1.size = 462 ∧
    LocalData.lperm2.size = 462 ∧
    (∀ k < 462, labMasks[k]! < 4096 ∧ popc12 labMasks[k]! = 6 ∧ labMasks[k]!.testBit 0 = true) ∧
    (∀ k < 462, ∀ k' < 462, k ≠ k' → labMasks[k]! ≠ labMasks[k']!) ∧
    (∀ k < 462, LocalData.lperm1[k]! < 462 ∧ LocalData.lperm2[k]! < 462 ∧
      labMasks[LocalData.lperm1[k]!]! = canonMask (permMask (natArr LocalData.natGen1)
        labMasks[k]!) ∧
      labMasks[LocalData.lperm2[k]!]! = canonMask (permMask (natArr LocalData.natGen2)
        labMasks[k]!)) := by
  have h := label_cert
  unfold labelChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, fun k hk => ?_, fun k hk k' hk' hkk => ?_, fun k hk => ?_⟩
  · have := allBelowN_spec h4 hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := allBelowN_spec (allBelowN_spec h5 hk) hk'
    simp only [Bool.or_eq_true, beq_iff_eq, hkk, false_or, bne_iff_ne, ne_eq] at this
    exact this
  · have := allBelowN_spec h6 hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

theorem labelSet_canon
    {k : ℕ} (hk : k < 462) : IsCanon (labelSet k) := by
  obtain ⟨-, -, -, h, -⟩ := label_parts
  obtain ⟨-, hc, h0⟩ := h k hk
  exact ⟨by rw [labelSet, card_maskSet12, hc], by rw [labelSet, mem_maskSet12]; exact h0⟩

@[expose] def labPart (k : Fin 462) : CFSG.Sporadic.HN.Local.Part :=
  ⟨labelSet k, labelSet_canon k.isLt⟩

theorem maskSet12_inj {m m' : ℕ} (hm : m < 4096) (hm' : m' < 4096)
    (h : maskSet12 m = maskSet12 m') : m = m' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · have := congrArg (fun S : Finset (Fin 12) => (⟨i, hi⟩ : Fin 12) ∈ S) h
    simpa [maskSet12] using this
  · have h1 : m < 2 ^ i := lt_of_lt_of_le hm (by
      calc 4096 = 2 ^ 12 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : m' < 2 ^ i := lt_of_lt_of_le hm' (by
      calc 4096 = 2 ^ 12 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt h2]

theorem labPart_injective : Function.Injective labPart := by
  intro k k' h
  obtain ⟨-, -, -, hb, hd, -⟩ := label_parts
  by_contra hne
  apply hd k k.isLt k' k'.isLt (fun e => hne (Fin.ext e))
  exact maskSet12_inj (hb k k.isLt).1 (hb k' k'.isLt).1 (congrArg Subtype.val h)

theorem labPart_bijective : Function.Bijective labPart :=
  (Fintype.bijective_iff_injective_and_card labPart).2
    ⟨labPart_injective, by simp [card_part]⟩

theorem local_parts_data' :
    (∀ l ∈ LocalData.rootWord, l = 1 ∨ l = 2) ∧ (∀ l ∈ LocalData.outerWord, l = 1 ∨ l = 2) ∧
    LocalData.parents.length = 462 ∧
    (∀ i < 462, 0 < i → LocalData.parents[i]!.1 < i ∧
      (LocalData.parents[i]!.2 = 1 ∨ LocalData.parents[i]!.2 = 2)) ∧
    LocalData.natGen1.length = 12 ∧ LocalData.natGen1.Nodup ∧ (∀ x ∈ LocalData.natGen1, x < 12) ∧
    LocalData.natGen2.length = 12 ∧ LocalData.natGen2.Nodup ∧ (∀ x ∈ LocalData.natGen2, x < 12) ∧
    LocalData.strongWords.size = 17 ∧ LocalData.strongWords[0]! = [] ∧
    LocalData.strongWords[1]! = [] ∧
    (∀ j < 17, 2 ≤ j → ∀ l ∈ LocalData.strongWords[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
    LocalData.tripleWords.size = 10 ∧
    (∀ i < 10, ∀ l ∈ LocalData.tripleWords[i]!, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ l ∈ LocalData.innerWord, l ≠ 0 ∧ l.natAbs ≤ 17) := by
  decide +kernel

theorem local_parts_data :
    (∀ l ∈ LocalData.rootWord, l = 1 ∨ l = 2) ∧ (∀ l ∈ LocalData.outerWord, l = 1 ∨ l = 2) ∧
    LocalData.parents.length = 462 ∧
    (∀ i, 0 < i → i < 462 → LocalData.parents[i]!.1 < i ∧
      (LocalData.parents[i]!.2 = 1 ∨ LocalData.parents[i]!.2 = 2)) ∧
    LocalData.natGen1.length = 12 ∧ LocalData.natGen1.Nodup ∧ (∀ x ∈ LocalData.natGen1, x < 12) ∧
    LocalData.natGen2.length = 12 ∧ LocalData.natGen2.Nodup ∧ (∀ x ∈ LocalData.natGen2, x < 12) ∧
    LocalData.strongWords.size = 17 ∧ LocalData.strongWords[0]! = [] ∧
    LocalData.strongWords[1]! = [] ∧
    (∀ j < 17, 2 ≤ j → ∀ l ∈ LocalData.strongWords[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
    LocalData.tripleWords.size = 10 ∧
    (∀ i < 10, ∀ l ∈ LocalData.tripleWords[i]!, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ l ∈ LocalData.innerWord, l ≠ 0 ∧ l.natAbs ≤ 17) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := local_parts_data'
  exact ⟨h1, h2, h3, fun i hi0 hi => h4 i hi hi0, h5⟩

theorem ctuc_hn_local_alternating_outer_data :
    (h1J = jRegs 1 ∧ h2J = jRegs 2 ∧ HJ = Subgroup.closure {h1J, h2J}) ∧
    (∀ l ∈ LocalData.rootWord, l = 1 ∨ l = 2) ∧ (∀ l ∈ LocalData.outerWord, l = 1 ∨ l = 2) ∧
    LocalData.parents.length = 462 ∧
    (∀ i, 0 < i → i < 462 → LocalData.parents[i]!.1 < i ∧
      (LocalData.parents[i]!.2 = 1 ∨ LocalData.parents[i]!.2 = 2)) ∧
    xVec 0 = matJ (seedWordJ LocalData.rootWord) *ᵥ fixedVector ∧
    (∀ i, 0 < i → i < 462 →
      xVec i = matJ (hJ (LocalData.parents[i]!.2 - 1)) *ᵥ xVec LocalData.parents[i]!.1) ∧
    (LocalData.lperm1.size = 462 ∧ LocalData.lperm2.size = 462 ∧
      ∀ k < 462, LocalData.lperm1[k]! < 462 ∧ LocalData.lperm2[k]! < 462) ∧
    (LocalData.natGen1.length = 12 ∧ LocalData.natGen1.Nodup ∧ (∀ x ∈ LocalData.natGen1, x < 12)) ∧
    (LocalData.natGen2.length = 12 ∧ LocalData.natGen2.Nodup ∧ (∀ x ∈ LocalData.natGen2, x < 12)) ∧
    Function.Bijective labPart ∧
    (LocalData.strongWords.size = 17 ∧ LocalData.strongWords[0]! = [] ∧
      LocalData.strongWords[1]! = [] ∧
      ∀ j < 17, 2 ≤ j → ∀ l ∈ LocalData.strongWords[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
    (∀ j, 2 ≤ j → hJ j = Quiver.SchreierGraph.evalWord (fun h : Fin j => hJ h)
      (ptoLetters j LocalData.strongWords[j]!)) ∧ hJ 0 = h1J ∧ hJ 1 = h2J ∧
    (LocalData.tripleWords.size = 10 ∧
      ∀ i < 10, ∀ l ∈ LocalData.tripleWords[i]!, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ l ∈ LocalData.innerWord, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    matS = decode 5 133 1 LocalData.normalizerPayload ∧
    matCx = matJ (hWordJ LocalData.innerWord) * matJ (seedWordJ LocalData.outerWord)⁻¹ * matS := by
  obtain ⟨hr, hu, hpl, hp, hn1, hn1', hn1'', hn2, hn2', hn2'', hws, hw0, hw1, hw, hts, ht, hd⟩ :=
    local_parts_data
  obtain ⟨-, hl1, hl2, -, -, hl⟩ := label_parts
  refine ⟨⟨rfl, rfl, rfl⟩, hr, hu, hpl, hp, by rw [xVec, xVecAux, ite_eq_left rfl], ?_,
    ⟨hl1, hl2, fun k hk => ⟨(hl k hk).1, (hl k hk).2.1⟩⟩, ⟨hn1, hn1', hn1''⟩,
    ⟨hn2, hn2', hn2''⟩, labPart_bijective, ⟨hws, hw0, hw1, hw⟩,
    fun j hj => gStrong_of_ge _ _ (by simpa using hj), gStrong_of_lt _ _ (by simp),
    gStrong_of_lt _ _ (by simp), ⟨hts, ht⟩, hd, matS_eq, rfl⟩
  intro i hi0 hi
  have key : ∀ i < 462, ∀ f, i < f → xVecAux f i = xVecAux 462 i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi f hf
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      obtain ⟨g', hg'⟩ : ∃ g', 462 = g' + 1 := ⟨461, rfl⟩
      rw [hg', xVecAux, xVecAux]
      split_ifs with h0
      · rfl
      · obtain ⟨hj, -⟩ := hp i (Nat.pos_of_ne_zero h0) hi
        rw [ih _ hj (by omega) f' (by omega), ih _ hj (by omega) g' (by omega)]
  obtain ⟨hj, -⟩ := hp i hi0 hi
  rw [xVec, show (462 : ℕ) = 461 + 1 from rfl, xVecAux, ite_eq_right (by omega), xVec]
  rw [key _ (by omega) 461 (by omega)]

end CFSG.Sporadic.HNSchreier
