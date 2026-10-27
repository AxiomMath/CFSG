module

public import Certificates.Certificate7208

public section

namespace CFSG.Quasithin.E6.HSInsp

open Subgroup CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

theorem card_C2 :
    Nat.card hsC2 = 2880 :=
  hs_reps.2.2.2.1

theorem cent_le_four {S : Subgroup (Equiv.Perm (Fin 3850))}
    (hS : S ≤ hsC2) (hc : Nat.card S = 64) :
    Nat.card ↥(hsR ⊓ centralizer (S : Set (Equiv.Perm (Fin 3850)))) ≤ 4 :=
  Certificates.certificate7208.1 S hS hc

theorem not_pure {b c : Equiv.Perm (Fin 3850)} (hb : b ∈ hsC2)
    (hc : c ∈ hsC2) (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hb2 : b * b = 1) (hc2 : c * c = 1)
    (hbc : b * c = c * b) (hbt : b ≠ hsT2) (hct : c ≠ hsT2) (hcb : c ≠ b) (hctb : c ≠ hsT2 * b)
    (hfb : ∃ g ∈ hsP, b = g * hsT2 * g⁻¹) (hfc : ∃ g ∈ hsP, c = g * hsT2 * g⁻¹)
    (hfbc : ∃ g ∈ hsP, b * c = g * hsT2 * g⁻¹) (hftb : ∃ g ∈ hsP, hsT2 * b = g * hsT2 * g⁻¹)
    (hftc : ∃ g ∈ hsP, hsT2 * c = g * hsT2 * g⁻¹)
    (hftbc : ∃ g ∈ hsP, hsT2 * (b * c) = g * hsT2 * g⁻¹) : False := by
  refine Certificates.certificate7208.2 b c hb hc hbc hb1 hc1 hb2 hc2 hbt hct hcb hctb ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hfb
  · exact hfc
  · exact hfbc
  · exact hftb
  · exact hftc
  · exact hftbc

theorem involution_cases
    {s : Equiv.Perm (Fin 3850)} (hs : s ∈ hsR)
    (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    (∃ g ∈ hsP, s = g * hsT2 * g⁻¹) ∨
      (s ∈ hsP ∧ Nat.card ↥(hsP ⊓ centralizer ({s} : Set (Equiv.Perm (Fin 3850)))) = 7680) ∨
      (s ∉ hsP ∧ 2 ^ 7 ∣ Nat.card ↥(hsP ⊓ centralizer ({s} : Set (Equiv.Perm (Fin 3850))))) := by
  have hord : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hs2) hs1
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover s hs hord
  obtain ⟨-, -, hout, -, hcard, -⟩ := hrows r hr
  have hC : Nat.card ↥(hsP ⊓ centralizer ({g * tp 3850 r.rep * g⁻¹} :
      Set (Equiv.Perm (Fin 3850)))) = r.centOrder := by
    rw [inf_centralizer_conj hsP hg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      hcard]
  have hP : g * tp 3850 r.rep * g⁻¹ ∈ hsP ↔ tp 3850 r.rep ∈ hsP := by
    constructor
    · intro h
      have := hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hg) h) hg
      rwa [show g⁻¹ * (g * tp 3850 r.rep * g⁻¹) * g = tp 3850 r.rep by group] at this
    · intro h
      exact hsP.mul_mem (hsP.mul_mem hg h) (hsP.inv_mem hg)
  rw [hC, hP]
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr | hr <;>
    simp only [hr, Bool.false_eq_true, false_iff, not_not, true_iff] at hout ⊢
  · exact Or.inr (Or.inl ⟨hout, trivial⟩)
  · exact Or.inl ⟨g, hg, rfl⟩
  · exact Or.inr (Or.inr ⟨hout, by norm_num⟩)
  · exact Or.inr (Or.inr ⟨hout, by norm_num⟩)

end CFSG.Quasithin.E6.HSInsp
