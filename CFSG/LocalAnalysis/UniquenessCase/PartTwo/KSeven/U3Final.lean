module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Induction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.U3Conj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.U3Step

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open Subgroup

private theorem ksu3z_card_sylow_three {J : Type} [Group J] [Finite J] (Z : Sylow 3 J)
    (h3 : 3 ∣ Nat.card J) (h9 : ¬ 9 ∣ Nat.card J) : Nat.card (Z : Subgroup J) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ0 : Nat.card J ≠ 0 := Nat.card_pos.ne'
  have hpos : 0 < Nat.factorization (Nat.card J) 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three hJ0 h3
  have hle : Nat.factorization (Nat.card J) 3 ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ Nat.factorization (Nat.card J) 3 := by omega
    have hdvd : 3 ^ 2 ∣ Nat.card J :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hJ0).mpr h2
    exact h9 (by simpa using hdvd)
  have hfac : Nat.factorization (Nat.card J) 3 = 1 := by omega
  rw [Sylow.card_eq_multiplicity Z, hfac, pow_one]

theorem u3_stepConcl_model {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) (h9 : ¬ 9 ∣ Nat.card (U3 h))
    (h7 : ¬ 7 ∣ Nat.card (U3 h)) (W : Subgroup (MulAut (U3 h))) (hW7 : Nat.card W = 7)
    (Z : Subgroup (U3 h)) (hZ3 : Nat.card Z = 3) (hZ : ∀ w ∈ W, ∀ z ∈ Z, w z = z) :
    StepConcl GoodU3 W Z := by
  obtain ⟨g, σ, hσ, _hK, hW⟩ := exists_conj_zpowers_u3Field_of_card_seven h hq h7 W hW7
  let e : U3 h ≃* U3 h := g.symm
  have he : e = g.symm := rfl
  have hcongr : MulAut.congr e = MulAut.conj e := by
    ext ψ x
    rfl
  have hcomp : (MulAut.conj e).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id (MulAut (U3 h)) := by
    rw [he]
    ext ψ x
    simp [MulAut.conj_apply, MulAut.mul_apply]
  have hmap : W.map (MulAut.congr e).toMonoidHom = Subgroup.zpowers (u3Field h σ) := by
    rw [hW, Subgroup.map_map, hcongr, hcomp, Subgroup.map_id]
  have hZ3' : Nat.card (Z.map e.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hZ3]
  have hZ' : ∀ w ∈ Subgroup.zpowers (u3Field h σ), ∀ z ∈ Z.map e.toMonoidHom, w z = z := by
    intro w hw z hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
    have hwW : MulAut.conj g w ∈ W := by
      rw [hW]
      exact Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
    have hfix : (MulAut.conj g w) z' = z' := hZ (MulAut.conj g w) hwW z' hz'
    apply g.injective
    simpa [e, MulAut.conj_apply, MulAut.mul_apply] using hfix
  refine stepConcl_of_mulEquiv GoodU3 goodU3_of_mulEquiv e W Z ?_
  rw [hmap]
  exact u3_stepConcl_zpowers h hq h9 h7 σ hσ (Z.map e.toMonoidHom) hZ3' hZ'

theorem u3_stepConcl {J : Type} [Group J] [Finite J] (hJ : GoodU3 J)
    (W : Subgroup (MulAut J)) (hW7 : Nat.card W = 7) (Z : Sylow 3 J)
    (hZ : ∀ w ∈ W, ∀ z ∈ (Z : Subgroup J), w z = z) : StepConcl GoodU3 W (Z : Subgroup J) := by
  obtain ⟨_hfin, h3, h9, h7, p, f, K, hK, h, hq, he⟩ := hJ
  obtain ⟨e⟩ := he
  letI : Field K := hK
  have hcard : Nat.card J = Nat.card (U3 h) := Nat.card_congr e.toEquiv
  have h9U3 : ¬ 9 ∣ Nat.card (U3 h) := by
    rw [← hcard]
    exact h9
  have h7U3 : ¬ 7 ∣ Nat.card (U3 h) := by
    rw [← hcard]
    exact h7
  have hW7' : Nat.card (W.map (MulAut.congr e).toMonoidHom) = 7 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hW7]
  have hZ3J : Nat.card (Z : Subgroup J) = 3 := ksu3z_card_sylow_three Z h3 h9
  have hZ3' : Nat.card ((Z : Subgroup J).map e.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hZ3J]
  have hZ' : ∀ w ∈ W.map (MulAut.congr e).toMonoidHom,
      ∀ z ∈ (Z : Subgroup J).map e.toMonoidHom, w z = z := by
    intro w hw z hz
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
    have hfix : w₀ z' = z' := hZ w₀ hw₀ z' hz'
    apply e.symm.injective
    simpa [MulAut.congr_apply] using hfix
  exact stepConcl_of_mulEquiv GoodU3 goodU3_of_mulEquiv e W (Z : Subgroup J)
    (u3_stepConcl_model h hq h9U3 h7U3 (W.map (MulAut.congr e).toMonoidHom) hW7'
      ((Z : Subgroup J).map e.toMonoidHom) hZ3' hZ')

theorem sevenFree_of_goodU3 {J : Type} [Group J] (hJ : GoodU3 J) :
    SevenFree J :=
  sevenFree_of_prime_step GoodU3 (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun _ _ _ hJ W _ hW7 Z hZ => u3_stepConcl hJ W hW7 Z hZ) J hJ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven
