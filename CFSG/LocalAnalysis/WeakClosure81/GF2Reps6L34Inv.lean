module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Balance

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

open Subgroup CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

theorem derived_le_C₄ : ambientDerived C₄ 2 ≤ C₄ := by
  change ⁅ambientDerived C₄ 1, ambientDerived C₄ 1⁆ ≤ C₄
  refine (Subgroup.commutator_le_self _).trans ?_
  change ⁅ambientDerived C₄ 0, ambientDerived C₄ 0⁆ ≤ C₄
  exact Subgroup.commutator_le_self _

private theorem card_ambientDerived_two :
    Nat.card (ambientDerived C₄ 2) = 9 := by
  rw [← card_derivedSeries]
  exact card_derivedSeries_C₄.2.2.1

private theorem card_ambientDerived_three :
    Nat.card (ambientDerived C₄ 3) = 1 := by
  rw [← card_derivedSeries]
  exact card_derivedSeries_C₄.2.2.2

private theorem commute_of_mem_ambientDerived_two
    {a b : Equiv.Perm (Fin 42)}
    (ha : a ∈ ambientDerived C₄ 2) (hb : b ∈ ambientDerived C₄ 2) : a * b = b * a := by
  have hbot : ⁅ambientDerived C₄ 2, ambientDerived C₄ 2⁆ = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    simpa only [ambientDerived] using card_ambientDerived_three
  have hmem : ⁅a, b⁆ ∈ ⁅ambientDerived C₄ 2, ambientDerived C₄ 2⁆ :=
    Subgroup.commutator_mem_commutator ha hb
  rw [hbot, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.1 hmem

private theorem conj_mem_ambientDerived {c : Equiv.Perm (Fin 42)} (hc : c ∈ C₄) :
    ∀ (k : ℕ) {x : Equiv.Perm (Fin 42)}, x ∈ ambientDerived C₄ k →
      c * x * c⁻¹ ∈ ambientDerived C₄ k := by
  intro k
  induction k with
  | zero =>
    intro x hx
    change c * x * c⁻¹ ∈ C₄
    exact C₄.mul_mem (C₄.mul_mem hc hx) (C₄.inv_mem hc)
  | succ k ih =>
    intro x hx
    change c * x * c⁻¹ ∈ ⁅ambientDerived C₄ k, ambientDerived C₄ k⁆
    have hleD : (ambientDerived C₄ k).map (MulAut.conj c).toMonoidHom ≤
        ambientDerived C₄ k := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      change (MulAut.conj c) z ∈ ambientDerived C₄ k
      simpa only [MulAut.conj_apply] using ih hz
    have hle : (⁅ambientDerived C₄ k, ambientDerived C₄ k⁆).map
        (MulAut.conj c).toMonoidHom ≤ ⁅ambientDerived C₄ k, ambientDerived C₄ k⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hleD hleD
    have hmem := hle (Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hx)
    change (MulAut.conj c) x ∈ ⁅ambientDerived C₄ k, ambientDerived C₄ k⁆ at hmem
    rwa [MulAut.conj_apply] at hmem

theorem conj_eq_inv_of_mem_derived {u p : Equiv.Perm (Fin 42)}
    (hu : u ∈ C₄) (hu2 : u * u = 1) (hu1 : u ≠ 1) (hp : p ∈ ambientDerived C₄ 2) :
    u * p * u⁻¹ = p⁻¹ := by
  have hC₄S : C₄ ≤ S := inf_le_right
  have huR : u ∈ R := S_le_R (hC₄S hu)
  let uR : R := ⟨u, huR⟩
  have hord : orderOf uR = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rwa [pow_two]) hu1
  have hconj₁ : IsConj uR r₁R := by
    rcases (orderOf_eq_two_iff uR).1 hord with h | h | h | h
    · exact h
    · exact absurd (hC₄S hu) (not_mem_S_of_isConj h not_mem_S_r₂)
    · exact absurd (hC₄S hu) (not_mem_S_of_isConj h not_mem_S_r₃)
    · exact absurd (hC₄S hu) (not_mem_S_of_isConj h not_mem_S_r₄)
  have hcardC : Nat.card ↥(Subgroup.centralizer ({u} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 64 := by
    have h := CFSG.ComponentClassification.GrSLit.card_centralizer_S_of_isConj
      (x := uR) (r := r₁R) hconj₁
    rw [h]
    simpa only [C₁, r₁R] using card_C₁
  have hcardP : Nat.card (ambientDerived C₄ 2) = 9 := card_ambientDerived_two
  set q : Equiv.Perm (Fin 42) := u * p * u⁻¹ with hqdef
  have hqP : q ∈ ambientDerived C₄ 2 := conj_mem_ambientDerived hu 2 hp
  have hu_inv : u⁻¹ = u := mul_eq_one_iff_inv_eq.1 hu2
  have huq : u * q * u⁻¹ = p := by
    rw [hqdef]
    calc
      u * (u * p * u⁻¹) * u⁻¹ = (u * u) * p * (u⁻¹ * u⁻¹) := by group
      _ = p := by rw [hu2, hu_inv, hu2]; simp
  have huv : u * (p * q) * u⁻¹ = p * q := by
    calc
      u * (p * q) * u⁻¹ = q * (u * q * u⁻¹) := by rw [hqdef]; group
      _ = q * p := by rw [huq]
      _ = p * q := commute_of_mem_ambientDerived_two hqP hp
  have hvcent : p * q ∈ Subgroup.centralizer ({u} : Set (Equiv.Perm (Fin 42))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.1 huv).symm
  have hvS : p * q ∈ S :=
    hC₄S (derived_le_C₄ (Subgroup.mul_mem _ hp hqP))
  have hvmem : p * q ∈ Subgroup.centralizer ({u} : Set (Equiv.Perm (Fin 42))) ⊓ S :=
    ⟨hvcent, hvS⟩
  have h64 : orderOf (p * q) ∣ 64 := by
    have h := Subgroup.orderOf_dvd_natCard
      (Subgroup.centralizer ({u} : Set (Equiv.Perm (Fin 42))) ⊓ S) hvmem
    rwa [hcardC] at h
  have h9 : orderOf (p * q) ∣ 9 := by
    have h := Subgroup.orderOf_dvd_natCard (ambientDerived C₄ 2) (Subgroup.mul_mem _ hp hqP)
    rwa [hcardP] at h
  have hone : p * q = 1 := by
    apply orderOf_eq_one_iff.1
    have hdvd : orderOf (p * q) ∣ Nat.gcd 64 9 := Nat.dvd_gcd h64 h9
    simpa using hdvd
  exact mul_eq_one_iff_eq_inv'.1 hone

end CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

end
