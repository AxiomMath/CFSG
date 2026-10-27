module

public import CFSG.Permutation.FinPackEven6

public section

namespace CFSG.Quasithin.H13.NQS134Pack

open Equiv CFSG.Permutation.FinPack

@[expose] noncomputable def inPD (Dc Pc : List ℕ) (w : ℕ) : Bool :=
  memK w Pc && !memK w Dc

@[expose] noncomputable def wordSide (Dc Pc : List ℕ) (x y : ℕ) : Bool :=
  anyK (fun b' => inPD Dc Pc (mulK 6 (mulK 6 x b') x) ||
    inPD Dc Pc (mulK 6 (mulK 6 y b') y)) Dc

@[expose] noncomputable def wordConcl (Dc Pc : List ℕ) (g gi : ℕ) : Bool :=
  anyK (fun b => wordSide Dc Pc (mulK 6 (mulK 6 g b) gi) (mulK 6 (mulK 6 gi b) g)) Dc

@[expose] noncomputable def wordHyp (k : ℕ) (Pc : List ℕ) (g : ℕ) : Bool :=
  Nat.beq (rd g 0) k && !(Nat.beq (rd g 4) 4 && Nat.beq (rd g 5) 5) &&
    !(Nat.beq (rd g 4) 5 && Nat.beq (rd g 5) 4) && !memK g Pc

@[expose] noncomputable def wordEntry (k : ℕ) (Dc Pc : List ℕ) (g gi : ℕ) : Bool :=
  !wordHyp k Pc g || wordConcl Dc Pc g gi

@[expose] noncomputable def wordCheck (k : ℕ) (E Dc Pc : List ℕ) : Bool :=
  allK (fun c => wordEntry k Dc Pc (lo6 c) (hi6 c)) E

@[expose] def a6DCodes : List ℕ :=
  [5517840, 4530960, 4534785, 5513985, 5509170, 4522290, 4526115, 5505315]

@[expose] def a6P2Codes : List ℕ :=
  [5517840, 4530960, 3298320, 2311440, 4534785, 5513985, 2315265, 3294465, 5509170, 4522290,
    1070130, 83250, 4526115, 5505315, 87075, 1066275, 3280980, 2294100, 1061460, 74580, 2297925,
    3277125, 78405, 1057605]

theorem rd_enc6(g : Perm (Fin 6)) (i : Fin 6) : rd (enc g) i = g i := rd_enc (by norm_num) g i

theorem enc_mul6 (σ τ : Perm (Fin 6)) : mulK 6 (enc σ) (enc τ) = enc (σ * τ) :=
  (enc_mul (by norm_num) σ τ).symm

theorem inPD_enc {D P : List (Perm (Fin 6))} {Dc Pc : List ℕ} (hD : D.map enc = Dc)
    (hP : P.map enc = Pc) (w : Perm (Fin 6)) : inPD Dc Pc (enc w) = true ↔ w ∈ P ∧ w ∉ D := by
  rw [inPD, Bool.and_eq_true, Bool.not_eq_true', memK_iff,
    ← Bool.not_eq_true, memK_iff, ← hD, ← hP, ← mem_iff_enc (by norm_num),
    ← mem_iff_enc (by norm_num)]

theorem word_of_check (k : Fin 6) (D P : List (Perm (Fin 6))) (E Dc Pc : List ℕ)
    (hE : ∀ g : Perm (Fin 6), Perm.sign g = 1 → memK (pc6 g) E = true)
    (hD : (D.map enc == Dc) = true) (hP : (P.map enc == Pc) = true)
    (hc : wordCheck k E Dc Pc = true) :
    ∀ g : Perm (Fin 6), g 0 = k → Perm.sign g = 1 → ¬ (g 4 = 4 ∧ g 5 = 5) →
      ¬ (g 4 = 5 ∧ g 5 = 4) → g ∉ P →
      ∃ b ∈ D, ∃ b' ∈ D,
        (g * b * g⁻¹ * b' * (g * b * g⁻¹) ∈ P ∧
          g * b * g⁻¹ * b' * (g * b * g⁻¹) ∉ D) ∨
        (g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∈ P ∧
          g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∉ D) := by
  intro g h0 hs h1 h2 hgP
  obtain rfl := beq_iff_eq.1 hD
  obtain rfl := beq_iff_eq.1 hP
  have hm : wordEntry k (D.map enc) (P.map enc) (lo6 (pc6 g)) (hi6 (pc6 g)) = true :=
    allK_iff.1 hc _ (memK_iff.1 (hE g hs))
  rw [lo6_pc6, hi6_pc6, wordEntry, Bool.or_eq_true, Bool.not_eq_true'] at hm
  have hh : wordHyp k (P.map enc) (enc g) = true := by
    have e0 : rd (enc g) 0 = (g 0 : ℕ) := rd_enc6 g 0
    have e4 : rd (enc g) 4 = (g 4 : ℕ) := rd_enc6 g 4
    have e5 : rd (enc g) 5 = (g 5 : ℕ) := rd_enc6 g 5
    have hm' : memK (enc g) (P.map enc) = false := by
      rw [← Bool.not_eq_true, memK_iff, ← mem_iff_enc (by norm_num)]
      exact hgP
    rw [wordHyp, e0, e4, e5, hm', h0]
    simp only [Nat.beq_refl, Bool.true_and, Bool.not_false, Bool.and_true, Bool.and_eq_true,
      Bool.not_eq_true', Bool.and_eq_false_iff]
    refine ⟨?_, ?_⟩ <;> by_contra hc <;> simp only [not_or, Bool.not_eq_false, Nat.beq_eq] at hc
    · exact h1 ⟨Fin.ext hc.1, Fin.ext hc.2⟩
    · exact h2 ⟨Fin.ext hc.1, Fin.ext hc.2⟩
  rcases hm with hm | hm
  · rw [hh] at hm
    exact absurd hm (by decide)
  rw [wordConcl, anyK_iff] at hm
  obtain ⟨bc, hbc, hm⟩ := hm
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hbc
  simp only [enc_mul6] at hm
  rw [wordSide, anyK_iff] at hm
  obtain ⟨bc', hbc', hm⟩ := hm
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hbc'
  simp only [enc_mul6] at hm
  rw [Bool.or_eq_true, inPD_enc rfl rfl, inPD_enc rfl rfl] at hm
  exact ⟨b, hb, b', hb', hm⟩

end CFSG.Quasithin.H13.NQS134Pack
