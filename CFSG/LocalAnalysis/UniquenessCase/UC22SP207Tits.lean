module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Defs
public import CFSG.GroupTheory.TitsSystem.Basic
import CFSG.Milestones.ASVolI.I2BNWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.GH74.BNPair
open CFSG.GroupTheory.TitsSystem (IsBNPair)
open CFSG.ASVolI.ChIJK (IsSplitBNPair burnsideI2BN_exists_isBNPair burnsideI2BN_toPre)

theorem uc22sp207_isBNPair_of_isTitsSystem {X : Type} [Group X] {B N : Subgroup X}
    [(cartan B N).Normal] {S : Finset (WeylGroup B N)} (h : IsTitsSystem B N S) :
    IsBNPair B N (S : Set (WeylGroup B N)) where
  gen := h.gen
  orderOf_eq_two s hs := h.involution s hs
  closure_eq := h.closure_eq
  mul_subset n m hn := (h.mul_subset n m hn).trans (Set.union_comm _ _).le
  ne n hn := h.ne n hn

theorem uc22sp207_sup_conj_eq_top {X : Type} [Group X] {B N : Subgroup X} [(cartan B N).Normal]
    {S : Set (WeylGroup B N)} (h : IsBNPair B N S) {n₀ : N}
    (hmax : ∀ w, wordLength S w ≤ wordLength S (n₀ : WeylGroup B N)) :
    B ⊔ B.map (MulAut.conj (n₀ : X)).toMonoidHom = ⊤ := by
  obtain ⟨J, hJ, hPJ⟩ :=
    h.exists_parabolic (le_sup_left : B ≤ B ⊔ B.map (MulAut.conj (n₀ : X)).toMonoidHom)
  have hn₀J : (n₀ : X) ∈ parabolic B N J := by
    refine (h.mem_and_subset_of_conj_le (Set.empty_subset S) hJ fun x hx => ?_).1
    rw [parabolic_empty] at hx
    rw [← hPJ]
    exact mem_sup_right ⟨x, hx, rfl⟩
  have hw₀J : (n₀ : WeylGroup B N) ∈ Subgroup.closure J :=
    (h.mem_parabolic_iff_of_mem_dc hJ (coe_mem_dc n₀)).1 hn₀J
  have hJS : J = S := by
    refine Set.Subset.antisymm hJ fun s hs => ?_
    by_contra hsJ
    have hlt := CFSG.ASVolI.burnsideI25b_length_lt_mul_right h hJ hw₀J hs hsJ
    have hle := hmax ((n₀ : WeylGroup B N) * s)
    omega
  rw [hPJ, hJS, h.parabolic_univ]

theorem uc22sp207_hasCentralLongest_of_isBNPair {X : Type} [Group X] {B N : Subgroup X}
    [(cartan B N).Normal] (hBN : IsSplitBNPair 2 B N) {S : Set (WeylGroup B N)}
    (h : IsBNPair B N S) {n₀ : N}
    (hmax : ∀ w, wordLength S w ≤ wordLength S (n₀ : WeylGroup B N))
    (hcomm : ∀ w : WeylGroup B N, (n₀ : WeylGroup B N) * w = w * (n₀ : WeylGroup B N)) :
    HasCentralLongest X := by
  refine ⟨B, N, hBN, n₀, n₀.2, uc22sp207_sup_conj_eq_top h hmax, fun x hx => ?_⟩
  have h1 : ((n₀ * ⟨x, hx⟩ * n₀⁻¹ * (⟨x, hx⟩ : N)⁻¹ : N) : WeylGroup B N) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcomm]
    group
  simpa using mk_eq_one_iff.1 h1

theorem uc22sp207_hasCentralLongest_of_cell {X : Type} [Group X] [Finite X] {B N : Subgroup X}
    (hBN : IsSplitBNPair 2 B N) {w : X}
    (hcell : ∀ g : X, g ∈ B ∨ ∃ b ∈ B, ∃ b' ∈ B, g = b * w * b') : HasCentralLongest X := by
  have : (cartan B N).Normal := hBN.normal_inter
  obtain ⟨S, hS⟩ :=
    burnsideI2BN_exists_isBNPair (burnsideI2BN_toPre hBN)
  obtain ⟨v, hv⟩ := hS.exists_mem_dc w
  have hW : ∀ u : WeylGroup B N, u = 1 ∨ u = v := by
    intro u
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective u
    rcases hcell n with hn | ⟨b, hb, b', hb', hnw⟩
    · exact Or.inl (mk_eq_one_iff.2 hn)
    · refine Or.inr (hS.eq_of_mem_dc (coe_mem_dc n) ?_)
      rw [hnw]
      exact mul_mem_dc hv hb hb'
  obtain ⟨n₀, -, hmax⟩ := CFSG.ASVolI.burnsideI25b_exists_max (B := B) (N := N) S S
  refine uc22sp207_hasCentralLongest_of_isBNPair hBN hS (n₀ := n₀)
    (fun u => hmax u (hS.mem_closure u)) fun u => ?_
  rcases hW (n₀ : WeylGroup B N) with h0 | h0 <;> rcases hW u with h1 | h1 <;> simp [h0, h1]

end CFSG.LocalAnalysis.UniquenessCase.UC22
