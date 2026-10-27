module

public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassBig
public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassHup
public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassSL2Aux
public import CFSG.Quasithin.Background.DicksonPerfectBasic
public import CFSG.RankThree.PartTwo.KFacts.K72List

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

open CFSG.PSL2Table
open scoped MatrixGroups

@[expose] def slEquivOfRingEquiv {F L : Type} [Field F] [Field L] (e : F ≃+* L) :
    SL(2, F) ≃* SL(2, L) :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map (n := Fin 2) (e : F →+* L))
    (Matrix.SpecialLinearGroup.map (n := Fin 2) (e.symm : L →+* F))
    (by
      ext a : 1
      apply Subtype.ext
      ext i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe])
    (by
      ext a : 1
      apply Subtype.ext
      ext i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe])

section Main

variable {F : Type} [Field F] [Fintype F]

theorem false_of_card_three (hcard : Fintype.card F = 3) (hperf : commutator SL(2, F) = ⊤) :
    False := by
  let e : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by rw [hcard, ZMod.card])
  haveI : Group.IsPerfect SL(2, F) := Group.isPerfect_def.mpr hperf
  haveI : Group.IsPerfect SL(2, ZMod 3) :=
    Group.IsPerfect.ofSurjective (f := (slEquivOfRingEquiv e).toMonoidHom)
      (slEquivOfRingEquiv e).surjective
  have hbot := CFSG.Quasithin.Dickson.sl2_three_perfect_eq_bot ⊤
    (Subgroup.commutator_eq_self (H := (⊤ : Subgroup SL(2, ZMod 3))))
  have h1 : (-1 : SL(2, ZMod 3)) ∈ (⊥ : Subgroup SL(2, ZMod 3)) := hbot ▸ Subgroup.mem_top _
  exact neg_one_ne_one_SL (F := ZMod 3) (by decide) (Subgroup.mem_bot.mp h1)

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  {ρ : Representation (ZMod p) SL(2, F) V}

theorem card_eq_ringChar (hF : ringChar F ≠ 2) (hρ : Function.Injective ρ) (hf : Fpf ρ) :
    Fintype.card F = ringChar F := by
  have hrp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  haveI : Fact (ringChar F).Prime := ⟨hrp⟩
  have hle : Nat.card (unipSL F) ≤ ringChar F := by
    refine CFSG.RankThree.PartTwo.KFacts.card_le_of_isCyclic_sylow
      (fun Q : Sylow (ringChar F) SL(2, F) => hf.isCyclic_sylow hρ hF Q) ?_
    intro x hx
    rw [eq_unip_of_mem_unipSL hx, unip_pow, CharP.cast_eq_zero, zero_mul, unip_zero]
  rw [card_unipSL] at hle
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  have hn1 : (n : ℕ) = 1 := by
    by_contra h
    have h2 : 2 ≤ (n : ℕ) := by have := n.pos; omega
    have h3 : ringChar F ^ 2 ≤ ringChar F ^ (n : ℕ) := Nat.pow_le_pow_right hrp.pos h2
    rw [← hn] at h3
    nlinarith [hrp.two_le]
  rw [hn, hn1, pow_one]

theorem seven_le_of_prime {r : ℕ} (hr : r.Prime) (h2 : r ≠ 2) (h3 : r ≠ 3) (h5 : r ≠ 5) :
    7 ≤ r := by
  by_contra h
  interval_cases r <;> first | omega | exact absurd hr (by norm_num)

theorem thirtyTwo_dvd_card {q : ℕ} (hq : 16 ∣ q - 1) (hq1 : 1 ≤ q) : 32 ∣ q * (q ^ 2 - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, q = 16 * a + 1 := ⟨(q - 1) / 16, by omega⟩
  have h : (16 * a + 1) ^ 2 - 1 = 32 * (8 * a ^ 2 + a) := by
    have : (16 * a + 1) ^ 2 = 32 * (8 * a ^ 2 + a) + 1 := by ring
    omega
  rw [h]
  exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _

theorem false_of_sixteen_dvd (hp : p ≠ 2) (hF : ringChar F ≠ 2)
    (hρ : Function.Injective ρ) (hf : Fpf ρ) (h16 : 16 ∣ Fintype.card F - 1)
    (hodd : Odd (Fintype.card F)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, j, w, z, hz, hz1, hi, hj, hji, hw3, hwi, hwj⟩ := exists_quaternion_relations hF
  obtain ⟨S, hS⟩ := (isPGroup_closure_of_quaternion hz hi hj hji).exists_le_sylow
  have hiS : i ∈ S := hS (Subgroup.subset_closure (by simp))
  have hjS : j ∈ S := hS (Subgroup.subset_closure (by simp))
  haveI : Finite F := inferInstance
  have hodd' : Odd (Nat.card F) := by rwa [Nat.card_eq_fintype_card]
  obtain ⟨n, hn, ⟨e⟩⟩ := CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion F hodd' S
  have hcardS : Nat.card (S : Subgroup SL(2, F)) = 4 * 2 ^ (n - 2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hdvd : 32 ∣ Nat.card SL(2, F) := by
    rw [card_SL]
    exact thirtyTwo_dvd_card h16 Fintype.card_pos
  have hmult := Sylow.card_eq_multiplicity S
  have h5 : 5 ≤ (Nat.card SL(2, F)).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp
      (by simpa using hdvd)
  have h8 : 8 ≤ 2 ^ (n - 2) := by
    have h1 : 2 ^ 5 ≤ 2 ^ (Nat.card SL(2, F)).factorization 2 := Nat.pow_le_pow_right (by omega) h5
    rw [← hmult, hcardS] at h1
    omega
  have ht : 3 ≤ n - 2 := by
    by_contra h
    have : 2 ^ (n - 2) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  exact no_fpf_of_quaternion_cycle hp hρ hf ht e hiS hjS hz hz1 hi hj hji hw3 hwi hwj

end Main

section Final

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Finite V] {ρ : Representation (ZMod p) SL(2, F) V}

theorem card_eq_five_of_fpf_sl2 (hp : p ≠ 2) (hF : ringChar F ≠ 2)
    (hperf : commutator SL(2, F) = ⊤) (hρ : Function.Injective ρ) (hf : Fpf ρ) :
    Nat.card F = 5 := by
  haveI := Fintype.ofFinite F
  have hcard := card_eq_ringChar hF hρ hf
  have hrp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  rw [Nat.card_eq_fintype_card, hcard]
  by_contra h5
  have h3 : ringChar F ≠ 3 := fun h => false_of_card_three (hcard.trans h) hperf
  have h7 := seven_le_of_prime hrp hF h3 h5
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (ringChar F - 1) with
      ⟨k, hk⟩ | ⟨ℓ, hℓ, hℓd, hℓodd⟩
  · have hk3 : 3 ≤ k := by
      by_contra h
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hk4 : 4 ≤ k := by
      by_contra h
      have hk' : k = 3 := by omega
      subst hk'
      have h9 : ringChar F = 9 := by omega
      rw [h9] at hrp
      exact absurd hrp (by norm_num)
    refine false_of_sixteen_dvd hp hF hρ hf ?_ ?_
    · rw [hcard, hk]
      exact (pow_dvd_pow 2 hk4 : 2 ^ 4 ∣ 2 ^ k)
    · rw [hcard]
      exact hrp.odd_of_ne_two hF
  · refine false_of_odd_prime_dvd hrp hℓ ?_ hcard hℓd
      (fun H hH => hf.isCyclic_of_card_eq_mul hρ hrp hℓ hH)
    rintro rfl
    exact absurd hℓodd (by decide)

end Final

end CFSG.LocalAnalysis.UniquenessCase.UCK.Zass
