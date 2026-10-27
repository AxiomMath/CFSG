module

public import CFSG.Sporadic.Ly.ActSpec

public section

namespace CFSG.Sporadic.Ly

open Native Matrix
open CFSG.Sporadic.Th (allIn_eq_true parAll_eq_true)
open CFSG.Sporadic.Th.Native (ap)

@[expose] def Canon (key : ByteArray) : Prop :=
  ValidKey key ∧ keyDigit key 826 = 0 ∧ keyDigit key 827 = 0 ∧ (∃ p, IsRREF (keyU key) p) ∧
    ∃ Si, keyC key * Si = 1

theorem get!_mk (d : Array UInt8) (q : ℕ) : (ByteArray.mk d).get! q = d[q]! := rfl

theorem key_eq_of_digits {k k' : ByteArray} (hk : ValidKey k) (hk' : ValidKey k')
    (h : ∀ p < 828, keyDigit k p = keyDigit k' p) : k = k' := by
  have hb : ∀ q < 276, (k.get! q).toNat = (k'.get! q).toNat := by
    intro q hq
    have h0 := h (3 * q + 0) (by omega)
    have h1 := h (3 * q + 1) (by omega)
    have h2 := h (3 * q + 2) (by omega)
    rw [keyDigit_byte k q 0 (by norm_num), keyDigit_byte k' q 0 (by norm_num)] at h0
    rw [keyDigit_byte k q 1 (by norm_num), keyDigit_byte k' q 1 (by norm_num)] at h1
    rw [keyDigit_byte k q 2 (by norm_num), keyDigit_byte k' q 2 (by norm_num)] at h2
    have hlt := hk.2 q hq
    have hlt' := hk'.2 q hq
    simp only [pow_zero, Nat.div_one, pow_one, show (5 : ℕ) ^ 2 = 25 by norm_num] at h0 h1 h2
    omega
  cases k with
  | mk d =>
  cases k' with
  | mk d' =>
  congr 1
  have hs : d.size = 276 := hk.1
  have hs' : d'.size = 276 := hk'.1
  apply Array.ext (by rw [hs, hs'])
  intro q hq hq'
  have e := hb q (by rw [← hs]; exact hq)
  rw [get!_mk, get!_mk, getElem!_pos d q hq, getElem!_pos d' q hq'] at e
  exact UInt8.toNat_inj.1 e

theorem natCast_inj_lt5 {x y : ℕ} (hx : x < 5) (hy : y < 5) (h : (x : ZMod 5) = (y : ZMod 5)) :
    x = y := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
  exact h

theorem keyT_inj {k k' : ByteArray} (hk : Canon k) (hk' : Canon k') (h : keyT k = keyT k') :
    k = k' := by
  obtain ⟨hv, h826, h827, ⟨p, hp⟩, Si, hSi⟩ := hk
  obtain ⟨hv', h826', h827', ⟨p', hp'⟩, -, -⟩ := hk'
  obtain ⟨hU, hC⟩ := eq_of_isRREF_tensor hp hp' hSi h
  apply key_eq_of_digits hv hv'
  intro q hq
  by_cases h1 : q < 777
  · have e := congrFun (congrFun hU ⟨q % 111, by omega⟩) ⟨q / 111, by omega⟩
    simp only [keyU, of_apply] at e
    rw [show 111 * (q / 111) + q % 111 = q by omega] at e
    exact natCast_inj_lt5 (keyDigit_lt _ _) (keyDigit_lt _ _) e
  · by_cases h2 : q < 826
    · have e := congrFun (congrFun hC ⟨(q - 777) / 7, by omega⟩) ⟨(q - 777) % 7, by omega⟩
      simp only [keyC, of_apply] at e
      rw [show 777 + 7 * ((q - 777) / 7) + (q - 777) % 7 = q by omega] at e
      exact natCast_inj_lt5 (keyDigit_lt _ _) (keyDigit_lt _ _) e
    · obtain rfl | rfl : q = 826 ∨ q = 827 := by omega
      · rw [h826, h826']
      · rw [h827, h827']

theorem canon_actKey (M : Array (Array ℕ)) {key key' : ByteArray} (hk : Canon key)
    (h : actKey (frTable M) key = some key') : Canon key' := by
  obtain ⟨hv, -, -, -, Si, hSi⟩ := hk
  obtain ⟨hv', hR, -⟩ := actKey_spec M hv h
  refine ⟨hv', ?_, ?_, hR, keyC_inv_actKey M hv h hSi⟩
  all_goals
    unfold actKey at h
    simp only at h
    split at h
    · obtain rfl := (Option.some.inj h).symm
      rw [keyDigit_encodeDigits _ (by omega)]
      unfold keyFun
      simp
    · exact absurd h (by simp)

theorem byteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  have h' : (a.data == b.data) = true := h
  exact ByteArray.ext (beq_iff_eq.1 h')

theorem option_byteArray_eq_of_beq {x : Option ByteArray} {y : ByteArray}
    (h : (x == some y) = true) : x = some y := by
  cases x with
  | none => cases h
  | some a => exact congrArg some (byteArray_eq_of_beq h)

structure KFacts (MA MB : Array (Array ℕ)) (k₀ : ByteArray) (O : KOrbit) : Prop where
  size_pos : 0 < O.keys.size
  size_lt : O.keys.size < 2 ^ 30
  root : O.keys[0]! = k₀
  inj : ∀ i < O.keys.size, ∀ j < O.keys.size, O.keys[i]! = O.keys[j]! → i = j
  alpha : ∀ i < O.keys.size, ap O.alpha i < O.keys.size ∧
    actKey (frTable MA) O.keys[i]! = some O.keys[ap O.alpha i]!
  beta : ∀ i < O.keys.size, ap O.beta i < O.keys.size ∧
    actKey (frTable MB) O.keys[i]! = some O.keys[ap O.beta i]!
  tree : ∀ k < O.keys.size, 0 < k → ap O.par k < k ∧
    ((ap O.lab k = 1 ∧ ap O.alpha (ap O.par k) = k) ∨ (ap O.lab k = 2 ∧ ap O.beta (ap O.par k) = k))

theorem orbitOK_facts {MA MB : Array (Array ℕ)} {k₀ : ByteArray} {O : KOrbit} {c : ℕ}
    (h : orbitOK (frTable MA) (frTable MB) k₀ O c = true) : KFacts MA MB k₀ O := by
  unfold orbitOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hpos, hlt⟩, hroot⟩, hall⟩ := h
  set pos : ByteArray → ℕ := fun X => O.index.getD X O.keys.size
  have hat := parAll_eq_true hall
  have hk : ∀ k < O.keys.size, pos O.keys[k]! = k ∧ ap O.alpha k < O.keys.size ∧
      ap O.beta k < O.keys.size ∧ actKey (frTable MA) O.keys[k]! = some O.keys[ap O.alpha k]! ∧
      actKey (frTable MB) O.keys[k]! = some O.keys[ap O.beta k]! ∧
      (k = 0 ∨ (ap O.par k < k ∧ ((ap O.lab k = 1 ∧ ap O.alpha (ap O.par k) = k) ∨
        (ap O.lab k = 2 ∧ ap O.beta (ap O.par k) = k)))) := by
    intro k hk
    have := hat k hk
    simp only [orbitCheckAt, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      beq_iff_eq] at this
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := this
    exact ⟨h1, h2, h3, option_byteArray_eq_of_beq h4, option_byteArray_eq_of_beq h5, h6⟩
  refine ⟨hpos, hlt, byteArray_eq_of_beq hroot, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    rw [← (hk i hi).1, ← (hk j hj).1, hij]
  · intro i hi
    exact ⟨(hk i hi).2.1, (hk i hi).2.2.2.1⟩
  · intro i hi
    exact ⟨(hk i hi).2.2.1, (hk i hi).2.2.2.2.1⟩
  · intro k hk' hk0
    rcases (hk k hk').2.2.2.2.2 with h0 | h1
    · omega
    · exact h1

theorem KFacts.canon {MA MB : Array (Array ℕ)} {k₀ : ByteArray} {O : KOrbit}
    (hF : KFacts MA MB k₀ O) (h0 : Canon k₀) : ∀ i < O.keys.size, Canon O.keys[i]! := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hF.root]; exact h0
    · obtain ⟨hp, hlab⟩ := hF.tree i hi hpos
      have hcp := ih _ hp (lt_trans hp hi)
      rcases hlab with ⟨-, he⟩ | ⟨-, he⟩
      · have := (hF.alpha _ (lt_trans hp hi)).2
        rw [he] at this
        exact canon_actKey MA hcp this
      · have := (hF.beta _ (lt_trans hp hi)).2
        rw [he] at this
        exact canon_actKey MB hcp this

end CFSG.Sporadic.Ly
