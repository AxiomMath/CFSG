module

public import Mathlib.GroupTheory.PGroup
import CFSG.RankThree.PartTwo.Sec13.Item135CritProof

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement

theorem s16c1_G47_crit {Hs : Type} [Group Hs] [Finite Hs] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {P : Subgroup Hs} (hPn : P.Normal) (hP : IsPGroup q P) {u : Hs} (hu2 : u * u = 1)
    (hu : ∃ n ∈ P, u * n * u⁻¹ ≠ n) :
    ∃ D : Subgroup Hs, D ≤ P ∧ D.Normal ∧ (∀ d ∈ D, d ^ q = 1) ∧
      (∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅⁅a, b⁆, c⁆ = 1) ∧ ∃ d ∈ D, u * d * u⁻¹ ≠ d := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : P.Normal := hPn
  obtain ⟨C, -, -, -, -, hD₀char, -, hD₀comm, hD₀exp, -, hstar⟩ :=
    CFSG.RankThree.PartTwo.Sec13.CritProof.exists_isThompsonCritical_omega (p := q) hq2 hP
  set D₀ := CFSG.RankThree.PartTwo.Sec13.CritProof.omegaOneIn q C
  haveI : D₀.Characteristic := hD₀char
  refine ⟨D₀.map P.subtype, Subgroup.map_subtype_le D₀, ?_, ?_, ?_, ?_⟩
  · exact inferInstance
  · rintro d ⟨y, hy, rfl⟩
    rw [← map_pow P.subtype y q, hD₀exp y hy, map_one]
  · intro a ha b hb c hc
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.1 hc
    have h1 : ⁅a', b'⁆ ∈ ⁅D₀, (⊤ : Subgroup P)⁆ :=
      Subgroup.commutator_mem_commutator ha' (Subgroup.mem_top b')
    obtain ⟨-, h3⟩ := hD₀comm h1
    have h4 : c' * ⁅a', b'⁆ = ⁅a', b'⁆ * c' := Subgroup.mem_centralizer_iff.1 h3 c' hc'
    have h5 : ⁅⁅a', b'⁆, c'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h4.symm
    have h6 := congrArg P.subtype h5
    simpa only [map_one, map_commutatorElement] using h6
  · by_contra hcon
    push Not at hcon
    obtain ⟨n, hnP, hnu⟩ := hu
    refine hnu ?_
    have hα2 : MulAut.conjNormal (H := P) u * MulAut.conjNormal (H := P) u = 1 := by
      have h := map_mul (MulAut.conjNormal (H := P)) u u
      rw [hu2, map_one] at h
      exact h.symm
    have hαord : orderOf (MulAut.conjNormal (H := P) u) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hα2)
    have h2q : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2)
    have hcop : Nat.Coprime (orderOf (MulAut.conjNormal (H := P) u)) q :=
      h2q.coprime_dvd_left hαord
    have hfixD₀ : ∀ x ∈ D₀, MulAut.conjNormal (H := P) u x = x := by
      intro x hx
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, hcon (x : Hs) (Subgroup.mem_map_of_mem P.subtype hx)]
    have hα1 : MulAut.conjNormal (H := P) u = 1 := hstar _ hcop hfixD₀
    have h1 : MulAut.conjNormal (H := P) u ⟨n, hnP⟩ = ⟨n, hnP⟩ := by
      rw [hα1, MulAut.one_apply]
    have h2 := congrArg (fun z : P => (z : Hs)) h1
    simpa only [MulAut.conjNormal_apply] using h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
