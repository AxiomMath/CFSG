module

public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.RankThree.PartOne.K159H.O3Class

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.RankThree.OrthogonalInvolutions Module

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ} {qA : QuadraticForm K A}
  (S : Subgroup (Fin r → Kˣ))

@[expose] def Wsub : Submodule K ((Fin r ⊕ Fin r → K) × A) where
  carrier := {v | ∀ j, ¬ TrivOn S j → v.1 j = 0}
  add_mem' {a b} ha hb := fun j hj => by
    have ha' : a.1 j = 0 := ha j hj
    have hb' : b.1 j = 0 := hb j hj
    simp [ha', hb']
  zero_mem' := fun j _ => rfl
  smul_mem' c v hv := fun j hj => by
    have hv' : v.1 j = 0 := hv j hj
    simp [hv']

variable {S}

theorem mem_Wsub {v : (Fin r ⊕ Fin r → K) × A} : v ∈ Wsub S ↔ ∀ j, ¬ TrivOn S j → v.1 j = 0 := Iff.rfl

theorem hypVec_mem_Wsub {j : Fin r ⊕ Fin r} (hj : TrivOn S j) : hypVec K A j ∈ Wsub S := by
  intro c hc
  rw [hypVec_fst, ite_eq_right]
  rintro rfl
  exact hc hj

theorem tail_mem_Wsub (a : A) : ((0 : Fin r ⊕ Fin r → K), a) ∈ Wsub S := fun _ _ => rfl

theorem polarNondegOn_Wsub (hreg : (polarBilin qA).Nondegenerate) :
    PolarNondegOn (quadTail r qA) (Wsub (K := K) (A := A) S) := by
  intro x hx hperp
  have h1 : ∀ c, x.1 c = 0 := by
    intro c
    by_cases hc : TrivOn S c
    · have := hperp (hypVec K A c.swap) (hypVec_mem_Wsub (hc.swap S))
      rwa [polar_hypVec, Sum.swap_swap] at this
    · exact hx c hc
  have h2 : x.2 = 0 := by
    refine eq_zero_of_polar_eq_zero hreg fun a => ?_
    have := hperp ((0 : Fin r ⊕ Fin r → K), a) (tail_mem_Wsub a)
    rw [polar_quadTail, polar_zero_right, zero_add] at this
    exact this
  exact Prod.ext (funext h1) h2

theorem coord_of_fix_nontriv {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA))
    (hgf : ∀ j, ¬ TrivOn S j → g (hypVec K A j) = hypVec K A j) (x : (Fin r ⊕ Fin r → K) × A)
    {c : Fin r ⊕ Fin r} (hc : ¬ TrivOn S c) : (g x).1 c = x.1 c := by
  have h := polar_map_of_mem hgO x (hypVec K A c.swap)
  rw [hgf c.swap (fun h => hc ((trivOn_swap_iff S c).1 h)), polar_hypVec, polar_hypVec, Sum.swap_swap] at h
  exact h

theorem supp_Wsub {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA))
    (hgf : ∀ j, ¬ TrivOn S j → g (hypVec K A j) = hypVec K A j) :
    ∀ x, x ∈ Wsub (K := K) (A := A) S ↔ g x ∈ Wsub (K := K) (A := A) S := by
  intro x
  constructor
  · intro hx c hc
    rw [coord_of_fix_nontriv hgO hgf x hc]
    exact hx c hc
  · intro hx c hc
    rw [← coord_of_fix_nontriv hgO hgf x hc]
    exact hx c hc

theorem perp_Wsub (hreg : (polarBilin qA).Nondegenerate) {z : (Fin r ⊕ Fin r → K) × A}
    (hz : ∀ x ∈ Wsub (K := K) (A := A) S, polar (quadTail r qA) z x = 0) :
    z.2 = 0 ∧ ∀ c, TrivOn S c → z.1 c = 0 := by
  refine ⟨?_, fun c hc => ?_⟩
  · refine eq_zero_of_polar_eq_zero hreg fun a => ?_
    have := hz ((0 : Fin r ⊕ Fin r → K), a) (tail_mem_Wsub a)
    rw [polar_quadTail, polar_zero_right, zero_add] at this
    exact this
  · have := hz (hypVec K A c.swap) (hypVec_mem_Wsub (hc.swap S))
    rwa [polar_hypVec, Sum.swap_swap] at this

theorem fix_perp_Wsub (hreg : (polarBilin qA).Nondegenerate)
    {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hgf : ∀ j, ¬ TrivOn S j → g (hypVec K A j) = hypVec K A j) {z : (Fin r ⊕ Fin r → K) × A}
    (hz : ∀ x ∈ Wsub (K := K) (A := A) S, polar (quadTail r qA) z x = 0) : g z = z := by
  obtain ⟨h2, h1⟩ := perp_Wsub hreg hz
  conv_lhs => rw [vec_expand z]
  conv_rhs => rw [vec_expand z]
  rw [h2]
  have h0 : ((0 : Fin r ⊕ Fin r → K), (0 : A)) = (0 : (Fin r ⊕ Fin r → K) × A) := rfl
  rw [h0, add_zero, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : TrivOn S c
  · rw [h1 c hc, zero_smul, map_zero]
  · rw [map_smul, hgf c hc]

end CFSG.RankThree.PartOne.K159H
