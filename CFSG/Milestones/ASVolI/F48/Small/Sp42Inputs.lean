module

public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.Certificates.CosetTablePresented
public import CFSG.Milestones.ASVolI.F48.Small.EngCheck
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.ASVolI

open CFSG.CosetTable

@[expose] def burnsideF48s_sp42Letter (c : Char) : Fin 5 × Bool :=
  (⟨"abcde".toList.idxOf c.toLower % 5, Nat.mod_lt _ (by norm_num)⟩, c.isLower)

@[expose] def burnsideF48s_sp42Word (s : String) : List (Fin 5 × Bool) :=
  s.toList.map burnsideF48s_sp42Letter

@[expose] def burnsideF48s_sp42RelA : List String :=
  ["aa", "dd", "bb", "bCbC", "aCac", "abab", "adad", "dcbdcc", "dbdbdb"]

@[expose] def burnsideF48s_sp42RelB : List String :=
  ["bb", "aa", "ee", "beae", "caCa", "baba", "cccc", "bCbC", "ceCeCea", "bCCaecce"]

@[expose] def burnsideF48s_sp42CandA : List String := ["D", "D", "AD", "AD"]

@[expose] def burnsideF48s_sp42CandB : List String := ["E", "ECCB", "E", "ECCB"]

@[expose] def burnsideF48s_sp42Ext (j : ℕ) : List (Fin 5 × Bool) :=
  (List.replicate 4 (burnsideF48s_sp42Word (burnsideF48s_sp42CandA.getD j "") ++
    burnsideF48s_sp42Word (burnsideF48s_sp42CandB.getD j ""))).flatten

@[expose] def burnsideF48s_sp42Ws (j : ℕ) : List (List (Fin 5 × Bool)) :=
  (burnsideF48s_sp42RelA ++ burnsideF48s_sp42RelB).map burnsideF48s_sp42Word ++
    [burnsideF48s_sp42Ext j]

abbrev burnsideF48s_sp42WsA (j : ℕ) :=
  restrictWords (subsetOf 5 [0, 1, 2, 3]) (burnsideF48s_sp42Ws j)

open Equiv in
@[expose] def burnsideF48s_sp42L : Fin 5 → Perm (Fin 6)
  | 0 => swap 4 5
  | 1 => swap 2 3
  | 2 => List.formPerm [0, 2, 1, 3]
  | 3 => swap 1 2
  | 4 => swap 2 4 * swap 3 5

open Equiv in
@[expose] def burnsideF48s_sp42e1 : Perm (Fin 6) := swap 4 5

open Equiv in
@[expose] def burnsideF48s_sp42e2 : Perm (Fin 6) := swap 0 1 * swap 2 3 * swap 4 5

@[expose] def burnsideF48s_sp42CoverA : List String :=
  ["", "a", "b", "c", "C", "d", "ab", "ac", "aC", "ad",
    "bc", "bC", "bd", "cc", "cd", "Cd", "db", "dc", "dC", "abc",
    "abC", "abd", "acc", "acd", "aCd", "adb", "adc", "adC", "bcc", "bcd",
    "bCd", "bdb", "bdc", "bdC", "ccd", "cdc", "abcc", "abcd", "abCd", "abdb",
    "abdc", "abdC", "accd", "acdc", "bccd", "bcdc", "abccd", "abcdc"]

@[expose] def burnsideF48s_sp42CoverB : List String :=
  ["", "a", "b", "c", "C", "e", "ab", "ac", "aC", "ae",
    "bc", "bC", "be", "cc", "ce", "Ce", "ec", "eC", "abc", "abC",
    "abe", "acc", "ace", "aCe", "aec", "aeC", "bcc", "bce", "bCe", "bec",
    "beC", "cce", "cec", "ceC", "Cec", "CeC", "ecc", "ece", "eCe", "abcc",
    "abce", "abCe", "abec", "abeC", "acce", "acec", "aCeC", "aecc"]

@[expose] def burnsideF48s_sp42Ev (s : String) : Equiv.Perm (Fin 6) :=
  burnsideF48s_ev burnsideF48s_sp42L (burnsideF48s_sp42Word s)

open Equiv in
@[expose] def burnsideF48s_sp42UV : Fin 2 → Perm (Fin 6)
  | 0 => swap 1 2
  | 1 => List.formPerm [0, 3, 5, 1, 2, 4]

@[expose] def burnsideF48s_sp42LetterUV (c : Char) : Fin 2 × Bool :=
  (⟨"uv".toList.idxOf c.toLower % 2, Nat.mod_lt _ (by norm_num)⟩, c.isLower)

@[expose] def burnsideF48s_sp42WordUV (s : String) : List (Fin 2 × Bool) :=
  s.toList.map burnsideF48s_sp42LetterUV

@[expose] def burnsideF48s_sp42RelUV : List String :=
  ["uu", "vuVVuvvuVVuv", "uvuVuvuVuvuV", "uVuVuvvvvvuVuV", "vuVVVuvvvuVVVuvv",
    "uVuvvvuVuVVuVVVuVuvvuvuv"]

@[expose] def burnsideF48s_sp42WG1 : List String :=
  ["UvUvvvuvvuvuvvUVV", "UVUvvvvUVUV", "VVUvUVUvv", "VVuvuvUvUVV"]

@[expose] def burnsideF48s_sp42WG2 : List String := ["UvUVUvvvUvUVUV", "vvuVuVUvUvu"]

@[expose] def burnsideF48s_sp42EvUV (h : Fin 2 → Equiv.Perm (Fin 6)) (s : String) :
    Equiv.Perm (Fin 6) :=
  burnsideF48s_ev h (burnsideF48s_sp42WordUV s)

@[expose] def burnsideF48s_sp42AutCond (h₁ h₂ : Equiv.Perm (Fin 6)) : Bool :=
  decide (h₁ * burnsideF48s_sp42e1 = burnsideF48s_sp42e1 * h₁) &&
  decide (h₂ * burnsideF48s_sp42e2 = burnsideF48s_sp42e2 * h₂) && decide (h₁ ≠ h₂) &&
  burnsideF48s_sp42RelUV.all (fun s => decide (burnsideF48s_sp42EvUV ![h₁, h₂] s = 1)) &&
  burnsideF48s_sp42WG1.all (fun s => decide (burnsideF48s_sp42EvUV ![h₁, h₂] s * burnsideF48s_sp42e1 =
      burnsideF48s_sp42e1 * burnsideF48s_sp42EvUV ![h₁, h₂] s)) &&
  burnsideF48s_sp42WG2.all (fun s => decide (burnsideF48s_sp42EvUV ![h₁, h₂] s * burnsideF48s_sp42e2 =
      burnsideF48s_sp42e2 * burnsideF48s_sp42EvUV ![h₁, h₂] s))

@[expose] def burnsideF48s_sp42PermFacts : Prop :=
  (∀ i : Fin 5, i ≠ 4 →
      burnsideF48s_sp42L i * burnsideF48s_sp42e1 = burnsideF48s_sp42e1 * burnsideF48s_sp42L i) ∧
  (∀ i : Fin 5, i ≠ 3 →
      burnsideF48s_sp42L i * burnsideF48s_sp42e2 = burnsideF48s_sp42e2 * burnsideF48s_sp42L i) ∧
  (∀ s ∈ burnsideF48s_sp42RelA ++ burnsideF48s_sp42RelB, burnsideF48s_sp42Ev s = 1) ∧
  (∀ x : Equiv.Perm (Fin 6), x * burnsideF48s_sp42e1 = burnsideF48s_sp42e1 * x →
      ∃ s ∈ burnsideF48s_sp42CoverA, burnsideF48s_sp42Ev s = x) ∧
  (∀ x : Equiv.Perm (Fin 6), x * burnsideF48s_sp42e2 = burnsideF48s_sp42e2 * x →
      ∃ s ∈ burnsideF48s_sp42CoverB, burnsideF48s_sp42Ev s = x) ∧
  (∀ s ∈ burnsideF48s_sp42CoverA ++ burnsideF48s_sp42CandA ++ burnsideF48s_sp42RelA,
      ∀ l ∈ burnsideF48s_sp42Word s, l.1 ≠ 4) ∧
  (∀ s ∈ burnsideF48s_sp42CoverB ++ burnsideF48s_sp42CandB ++ burnsideF48s_sp42RelB,
      ∀ l ∈ burnsideF48s_sp42Word s, l.1 ≠ 3) ∧
  (∀ x : Equiv.Perm (Fin 6), x * burnsideF48s_sp42e1 = burnsideF48s_sp42e1 * x →
    ¬ x * burnsideF48s_sp42e2 = burnsideF48s_sp42e2 * x → x * x = 1 →
    ∀ y : Equiv.Perm (Fin 6), y * burnsideF48s_sp42e2 = burnsideF48s_sp42e2 * y →
    ¬ y * burnsideF48s_sp42e1 = burnsideF48s_sp42e1 * y → y * y = 1 →
    ∃ g : Equiv.Perm (Fin 6), g * burnsideF48s_sp42e1 = burnsideF48s_sp42e1 * g ∧
      g * burnsideF48s_sp42e2 = burnsideF48s_sp42e2 * g ∧ ∃ j < 4,
      g * x * g⁻¹ = burnsideF48s_sp42Ev (burnsideF48s_sp42CandA.getD j "") ∧
      g * y * g⁻¹ = burnsideF48s_sp42Ev (burnsideF48s_sp42CandB.getD j "")) ∧
  burnsideF48s_ev burnsideF48s_sp42L (burnsideF48s_sp42Ext 1) = 1 ∧
  (∀ s ∈ burnsideF48s_sp42RelUV, burnsideF48s_sp42EvUV burnsideF48s_sp42UV s = 1) ∧
  (∀ s ∈ burnsideF48s_sp42WG1, burnsideF48s_sp42EvUV burnsideF48s_sp42UV s * burnsideF48s_sp42e1 =
      burnsideF48s_sp42e1 * burnsideF48s_sp42EvUV burnsideF48s_sp42UV s) ∧
  (∀ s ∈ burnsideF48s_sp42WG2, burnsideF48s_sp42EvUV burnsideF48s_sp42UV s * burnsideF48s_sp42e2 =
      burnsideF48s_sp42e2 * burnsideF48s_sp42EvUV burnsideF48s_sp42UV s) ∧
  (∀ h₁ h₂ : Equiv.Perm (Fin 6), burnsideF48s_sp42AutCond h₁ h₂ = true →
    ∃ g : Equiv.Perm (Fin 6), g * burnsideF48s_sp42UV 0 * g⁻¹ = h₁ ∧
      g * burnsideF48s_sp42UV 1 * g⁻¹ = h₂)

end CFSG.ASVolI
