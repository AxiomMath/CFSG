module

public import CFSG.RankThree.Asc83Table.MatCert
public import CFSG.RankThree.Asc83Table.Reduction
public import CFSG.Open.Defs

public section

namespace CFSG.RankThree.Asc83Table

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open scoped commutatorElement

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d) [Inhabited M]
  {sA sB : String} {C : MCert} (hC : mcertCheck O sA sB C = true)

local notation "u" => regUnit Sp hC

theorem wordUnit_one (r : ℕ) : wordUnit Sp hC [(r, 1)] = u r := by
  simp [wordUnit]

theorem wordUnit_pair (r a s b : ℕ) :
    wordUnit Sp hC [(r, a), (s, b)] = u r ^ a * u s ^ b := by
  simp [wordUnit]

theorem regUnit_comm' {r s : ℕ} (hf : MFact.eq [(r, 1), (s, 1)] [(s, 1), (r, 1)] ∈ C.facts)
    (hw₁ : HasOrd C [(r, 1), (s, 1)]) (hw₂ : HasOrd C [(s, 1), (r, 1)]) :
    Commute (u r) (u s) := by
  have h := regUnit_eq Sp hC hf hw₁ hw₂
  rw [wordUnit_pair, wordUnit_pair] at h
  simp only [pow_one] at h
  exact h

theorem regUnit_ne_one' {r t : ℕ} (hf : MFact.ne [(r, 1)] [] t ∈ C.facts)
    (hw : HasOrd C [(r, 1)]) : u r ≠ 1 := by
  have h := regUnit_ne Sp hC hf hw (hasOrd_nil C)
  rwa [wordUnit_one, wordUnit_nil] at h

theorem regUnit_ne_pow' {r s e t : ℕ} (hf : MFact.ne [(s, 1)] [(r, e)] t ∈ C.facts)
    (hw₁ : HasOrd C [(s, 1)]) (hw₂ : HasOrd C [(r, e)]) : u s ≠ u r ^ e := by
  have h := regUnit_ne Sp hC hf hw₁ hw₂
  rwa [wordUnit_one, show wordUnit Sp hC [(r, e)] = u r ^ e by simp [wordUnit]] at h

theorem regUnit_conj' {h e₁ r s a b : ℕ} {r' : ℕ}
    (hf : MFact.conj h [(r', 1)] [(r, a), (s, b)] ∈ C.facts) (hh : MFact.ord h e₁ ∈ C.facts)
    (hu : HasOrd C [(r', 1)]) (hw : HasOrd C [(r, a), (s, b)]) :
    u h * u r' * (u h)⁻¹ = u r ^ a * u s ^ b := by
  have := regUnit_conj Sp hC hf hh hu hw
  rwa [wordUnit_one, wordUnit_pair] at this

theorem regUnit_eq' {r : ℕ} {w : Word} (hf : MFact.eq [(r, 1)] w ∈ C.facts)
    (hw₁ : HasOrd C [(r, 1)]) (hw₂ : HasOrd C w) : u r = wordUnit Sp hC w := by
  have := regUnit_eq Sp hC hf hw₁ hw₂
  rwa [wordUnit_one] at this

structure E9Facts (C : MCert) (rx ry t₁ t₂ t₃ t₄ : ℕ) : Prop where
  hx : MFact.ord rx 3 ∈ C.facts
  hy : MFact.ord ry 3 ∈ C.facts
  hxy : MFact.eq [(rx, 1), (ry, 1)] [(ry, 1), (rx, 1)] ∈ C.facts
  hx1 : MFact.ne [(rx, 1)] [] t₁ ∈ C.facts
  hy1 : MFact.ne [(ry, 1)] [] t₂ ∈ C.facts
  hyx : MFact.ne [(ry, 1)] [(rx, 1)] t₃ ∈ C.facts
  hyx2 : MFact.ne [(ry, 1)] [(rx, 2)] t₄ ∈ C.facts

section E9

variable {rx ry t₁ t₂ t₃ t₄ : ℕ} (hF : E9Facts C rx ry t₁ t₂ t₃ t₄)
include hF

omit [Inhabited M] in
theorem E9Facts.hasOrd {e : ℕ} {w : Word} (hw : ∀ q ∈ w, q.1 = rx ∨ q.1 = ry)
    (_ : e = e) : HasOrd C w := by
  intro q hq
  rcases hw q hq with h | h
  · exact ⟨3, h ▸ hF.hx⟩
  · exact ⟨3, h ▸ hF.hy⟩

@[expose] noncomputable def E9Facts.basis : E9Basis (certMonoid p d sA sB)ˣ :=
  E9Basis.ofNe (regUnit_pow Sp hC hF.hx) (regUnit_pow Sp hC hF.hy)
    (regUnit_comm' Sp hC hF.hxy (hF.hasOrd (e := 0) (by simp) rfl)
      (hF.hasOrd (e := 0) (by simp) rfl))
    (regUnit_ne_one' Sp hC hF.hx1 (hF.hasOrd (e := 0) (by simp) rfl))
    (regUnit_ne_one' Sp hC hF.hy1 (hF.hasOrd (e := 0) (by simp) rfl))
    (by
      have := regUnit_ne_pow' Sp hC hF.hyx (hF.hasOrd (e := 0) (by simp) rfl)
        (hF.hasOrd (e := 0) (by simp) rfl)
      rwa [pow_one] at this)
    (regUnit_ne_pow' Sp hC hF.hyx2 (hF.hasOrd (e := 0) (by simp) rfl)
      (hF.hasOrd (e := 0) (by simp) rfl))

theorem E9Facts.basis_a : (hF.basis Sp hC).a = regUnit Sp hC rx := rfl

theorem E9Facts.basis_b : (hF.basis Sp hC).b = regUnit Sp hC ry := rfl

theorem E9Facts.mem_range {g o pp q r s : ℕ} {M : GL23} (hg : MFact.ord g o ∈ C.facts)
    (h₁ : MFact.conj g [(rx, 1)] [(rx, pp), (ry, r)] ∈ C.facts)
    (h₂ : MFact.conj g [(ry, 1)] [(rx, q), (ry, s)] ∈ C.facts)
    (hM : (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![(pp : ZMod 3), q; r, s]) :
    M ∈ (hF.basis Sp hC).rhoE.range :=
  (hF.basis Sp hC).mem_range_of_conj pp q r s
    (regUnit_conj' Sp hC h₁ hg (hF.hasOrd (e := 0) (by simp) rfl)
      (hF.hasOrd (e := 0) (by simp) rfl))
    (regUnit_conj' Sp hC h₂ hg (hF.hasOrd (e := 0) (by simp) rfl)
      (hF.hasOrd (e := 0) (by simp) rfl)) hM

end E9

@[expose] def commWord (rx ry : ℕ) : Word := [(rx, 1), (ry, 1), (rx, 2), (ry, 2)]

@[expose] def repWord (rx ry : ℕ) : Fin 4 → Word :=
  ![[(rx, 1)], [(ry, 1)], [(rx, 1), (ry, 1)], [(rx, 1), (ry, 2)]]

structure Ex27Facts (C : MCert) (rx ry t : ℕ) : Prop where
  hx : MFact.ord rx 3 ∈ C.facts
  hy : MFact.ord ry 3 ∈ C.facts
  hzx : MFact.eq (commWord rx ry ++ [(rx, 1)]) ([(rx, 1)] ++ commWord rx ry) ∈ C.facts
  hzy : MFact.eq (commWord rx ry ++ [(ry, 1)]) ([(ry, 1)] ++ commWord rx ry) ∈ C.facts
  hz1 : MFact.ne (commWord rx ry) [] t ∈ C.facts

theorem commutatorElement_eq_of_cube {G : Type*} [Group G] {x y : G} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) : ⁅x, y⁆ = x * y * x ^ 2 * y ^ 2 := by
  have hx' : x⁻¹ = x ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hx]
  have hy' : y⁻¹ = y ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hy]
  rw [commutatorElement_def, hx', hy']

omit [Inhabited M] in
instance finite_certUnits [NeZero p] : Finite (certMonoid p d sA sB)ˣ :=
  Finite.of_injective (fun x : (certMonoid p d sA sB)ˣ => (x : certMonoid p d sA sB))
    fun _ _ h => Units.ext h

section Ex27

variable {rx ry t : ℕ} (hF : Ex27Facts C rx ry t)
include hF

omit [Inhabited M] in
theorem Ex27Facts.hasOrd {w : Word} (hw : ∀ q ∈ w, q.1 = rx ∨ q.1 = ry) : HasOrd C w := by
  intro q hq
  rcases hw q hq with h | h
  · exact ⟨3, h ▸ hF.hx⟩
  · exact ⟨3, h ▸ hF.hy⟩

omit [Inhabited M] in
theorem Ex27Facts.hasOrd_comm : HasOrd C (commWord rx ry) :=
  hF.hasOrd (by simp [commWord])

omit [Inhabited M] in
theorem Ex27Facts.hasOrd_rep (i : Fin 4) : HasOrd C (repWord rx ry i) :=
  hF.hasOrd (by fin_cases i <;> simp [repWord])

theorem Ex27Facts.x_cube : regUnit Sp hC rx ^ 3 = 1 := regUnit_pow Sp hC hF.hx

theorem Ex27Facts.y_cube : regUnit Sp hC ry ^ 3 = 1 := regUnit_pow Sp hC hF.hy

theorem Ex27Facts.wordUnit_comm :
    wordUnit Sp hC (commWord rx ry) = ⁅regUnit Sp hC rx, regUnit Sp hC ry⁆ := by
  rw [commutatorElement_eq_of_cube (hF.x_cube Sp hC) (hF.y_cube Sp hC)]
  simp [wordUnit, commWord, mul_assoc]

omit hF in
theorem Ex27Facts.wordUnit_rep (i : Fin 4) :
    wordUnit Sp hC (repWord rx ry i) = ex27Rep (regUnit Sp hC rx) (regUnit Sp hC ry) i := by
  fin_cases i <;> simp [wordUnit, repWord, ex27Rep]

theorem Ex27Facts.z_x : Commute ⁅regUnit Sp hC rx, regUnit Sp hC ry⁆ (regUnit Sp hC rx) := by
  have h := regUnit_eq Sp hC hF.hzx (hasOrd_append hF.hasOrd_comm (hF.hasOrd (by simp)))
    (hasOrd_append (hF.hasOrd (by simp)) hF.hasOrd_comm)
  rw [wordUnit_append, wordUnit_append, hF.wordUnit_comm Sp hC, wordUnit_one] at h
  exact h

theorem Ex27Facts.z_y : Commute ⁅regUnit Sp hC rx, regUnit Sp hC ry⁆ (regUnit Sp hC ry) := by
  have h := regUnit_eq Sp hC hF.hzy (hasOrd_append hF.hasOrd_comm (hF.hasOrd (by simp)))
    (hasOrd_append (hF.hasOrd (by simp)) hF.hasOrd_comm)
  rw [wordUnit_append, wordUnit_append, hF.wordUnit_comm Sp hC, wordUnit_one] at h
  exact h

theorem Ex27Facts.z_ne : ⁅regUnit Sp hC rx, regUnit Sp hC ry⁆ ≠ 1 := by
  have h := regUnit_ne Sp hC hF.hz1 hF.hasOrd_comm (hasOrd_nil C)
  rwa [hF.wordUnit_comm Sp hC, wordUnit_nil] at h

noncomputable abbrev Ex27Facts.basis [Finite (certMonoid p d sA sB)ˣ] (i : Fin 4) :
    E9Basis (certMonoid p d sA sB)ˣ :=
  ex27Basis (hF.x_cube Sp hC) (hF.y_cube Sp hC) (hF.z_x Sp hC) (hF.z_y Sp hC) (hF.z_ne Sp hC) i

theorem Ex27Facts.mem_range [Finite (certMonoid p d sA sB)ˣ] (i : Fin 4) {g o pp q r s : ℕ}
    {M : GL23}
    (hg : MFact.ord g o ∈ C.facts)
    (h₁ : MFact.conj g (commWord rx ry)
      (wordPow (commWord rx ry) pp ++ wordPow (repWord rx ry i) r) ∈ C.facts)
    (h₂ : MFact.conj g (repWord rx ry i)
      (wordPow (commWord rx ry) q ++ wordPow (repWord rx ry i) s) ∈ C.facts)
    (hM : (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![(pp : ZMod 3), q; r, s]) :
    M ∈ (hF.basis Sp hC i).rhoE.range := by
  have hA := hF.hasOrd_comm
  have hB := hF.hasOrd_rep i
  have e₁ := regUnit_conj Sp hC h₁ hg hA (hasOrd_append (hasOrd_wordPow hA _)
    (hasOrd_wordPow hB _))
  have e₂ := regUnit_conj Sp hC h₂ hg hB (hasOrd_append (hasOrd_wordPow hA _)
    (hasOrd_wordPow hB _))
  rw [wordUnit_append, wordUnit_wordPow, wordUnit_wordPow, hF.wordUnit_comm Sp hC,
    Ex27Facts.wordUnit_rep Sp hC] at e₁ e₂
  exact (hF.basis Sp hC i).mem_range_of_conj pp q r s e₁ e₂ hM

end Ex27

end CFSG.RankThree.Asc83Table
