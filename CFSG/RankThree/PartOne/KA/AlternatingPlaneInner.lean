module

public import CFSG.RankThree.PartOne.KC.PlaneReduction
public import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingPlaneCore
public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.Sporadic.SchreierLemmas.OuterAlternatingSix

public section

namespace CFSG.RankThree.PartOne

open Equiv Equiv.Perm Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] noncomputable def alternatingConjEquiv {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) :
    Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
  MulEquiv.ofBijective (CFSG.Quasithin.SteinbergCB.conjPerm n)
    ⟨CFSG.Quasithin.SteinbergCB.conjPerm_injective (by omega),
      CFSG.Quasithin.SteinbergCB.conjPerm_surjective hn⟩

theorem alternatingConjEquiv_map_alternatingGroup {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) :
    (alternatingGroup (Fin n)).map (alternatingConjEquiv hn).toMonoidHom =
      (MulAut.conj : alternatingGroup (Fin n) →* MulAut (alternatingGroup (Fin n))).range :=
  CFSG.Quasithin.SteinbergCB.map_conjPerm_alternatingGroup n

theorem alternating_autPlaneProduct_eq_bot {p n : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hn : n = 5 ∨ 7 ≤ n) (hnp : n < p ^ 2)
    {B A : Subgroup (MulAut (alternatingGroup (Fin n)))}
    (hB : (MulAut.conj : alternatingGroup (Fin n) →* MulAut (alternatingGroup (Fin n))).range ≤
      B)
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2)
    {t : MulAut (alternatingGroup (Fin n))} (htA : t ∈ A) (ht1 : t ≠ 1) :
    autPlaneProduct p B A t = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  set φ := alternatingConjEquiv hn with hφ
  set H : Subgroup (Perm (Fin n)) := B.map φ.symm.toMonoidHom with hH
  set E : Subgroup (Perm (Fin n)) := A.map φ.symm.toMonoidHom with hE
  have hAH : alternatingGroup (Fin n) ≤ H := by
    intro g hg
    have hInn : φ g ∈ (MulAut.conj :
        alternatingGroup (Fin n) →* MulAut (alternatingGroup (Fin n))).range := by
      rw [← alternatingConjEquiv_map_alternatingGroup hn]
      exact Subgroup.mem_map_of_mem _ hg
    exact Subgroup.mem_map.mpr ⟨φ g, hB hInn, φ.symm_apply_apply g⟩
  have hEel : IsElementaryAbelian p E := IsElementaryAbelian.map φ.symm.toMonoidHom
  have hEcard : Nat.card E = p ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective φ.symm.injective, hAcard]
  have htE : φ.symm t ∈ E := Subgroup.mem_map_of_mem _ htA
  have ht1' : φ.symm t ≠ 1 := fun h => ht1 (by simpa using congrArg φ h)
  obtain ⟨h1, h2⟩ := (alternating_plane_cycle_local_core_calculation hp hp3 hAH hEel
    hEcard).2.2.2.2 hnp _ htE ht1'
  have hbot : autPlaneProduct p H E (φ.symm t) = ⊥ := by
    show ⁅permLocalCore p H (φ.symm t), E⁆ ⊔
      ⨅ (a : Perm (Fin n)) (_ : a ∈ E) (_ : a ≠ 1), permLocalCore p H a = ⊥
    rw [h1, h2, sup_idem]
  have hHB : H.map φ.toMonoidHom = B := by
    ext x
    simp [hH, Subgroup.mem_map]
  have hEA : E.map φ.toMonoidHom = A := by
    ext x
    simp [hE, Subgroup.mem_map]
  have hmap := map_autPlaneProduct_mulEquiv hp φ H E (φ.symm t)
  rw [hbot, Subgroup.map_bot, hHB, hEA, φ.apply_symm_apply] at hmap
  exact hmap.symm

theorem not_card_eq_sq_of_le_inner_alternating_six {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {A : Subgroup (MulAut (alternatingGroup (Fin 6)))}
    (hA : A ≤
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range) :
    Nat.card A ≠ p ^ 2 := by
  intro hcard
  have h1 := Subgroup.card_dvd_of_le hA
  have h2 := Subgroup.card_range_dvd
    (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6)))
  have h3 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card]
    decide
  rw [h3] at h2
  have h4 : p ^ 2 ∣ 360 := hcard ▸ h1.trans h2
  have h5 : p ≤ 18 := by
    have := Nat.le_of_dvd (by norm_num) h4
    nlinarith
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem planeLocalCoreInner_alternating {p n : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hn5 : 5 ≤ n)
    (hnp : n < p ^ 2) : PlaneLocalCoreInner p (alternatingGroup (Fin n)) (fun _ => True) := by
  intro B hB A hAInn hA hAcard _ t htA ht1
  by_cases h6 : n = 6
  · subst h6
    exact absurd hAcard (not_card_eq_sq_of_le_inner_alternating_six hp hp3 hAInn)
  · exact alternating_autPlaneProduct_eq_bot hp hp3 (by omega) hnp hB hA hAcard htA ht1

theorem card_outer_alternating_le_four {n : ℕ} (hn5 : 5 ≤ n) :
    Nat.card (Outer (alternatingGroup (Fin n))) ≤ 4 := by
  by_cases h6 : n = 6
  · subst h6
    exact CFSG.Sporadic.SchreierLemmas.outer_alternating_six.1
  · have hn : n = 5 ∨ 7 ≤ n := by omega
    exact (Nat.le_of_dvd (by norm_num)
      (CFSG.Quasithin.SteinbergCB.isSolvable_outer_alternatingGroup hn).2).trans (by norm_num)

theorem not_dvd_outer_alternating {p n : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hn5 : 5 ≤ n) :
    ¬ p ∣ Nat.card (Outer (alternatingGroup (Fin n))) := by
  intro h
  have : Finite (MulAut (alternatingGroup (Fin n))) := MulEquiv.finite_left
  have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin n))) := Nat.card_pos
  have h1 := Nat.le_of_dvd hpos h
  have h2 := card_outer_alternating_le_four hn5
  have := hp.five_le_of_ne_two_of_ne_three (by omega) (by omega)
  omega

end CFSG.RankThree.PartOne
