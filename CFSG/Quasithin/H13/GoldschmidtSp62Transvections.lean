module

public import CFSG.Quasithin.H13.GoldschmidtSp62Base
public import CFSG.Quasithin.H13.U3S1349F
public import Certificates.Certificate4196
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U CFSG.Blueprint
  CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

theorem sp62X2_check : sp62X2OK = true :=
  Certificates.certificate4196

theorem exists_conj_tH_two_of_transvections
    {d e : H6} (hd : orderOf d = 2)
    (h5 : 5 ∣ Nat.card ↥(Subgroup.centralizer ({d} : Set H6))) (hde : IsConj d e)
    (hc : d * e = e * d) (hne : e ≠ d) : ∃ g : H6, d * e = g * tH 2 * g⁻¹ := by
  obtain ⟨i, g, hg⟩ := exists_conj_of_sylow_classes SH_isPGroup SH_index exists_conj_of_mem_SH hd
  have hi : i = 0 := by
    rw [hg, card_centralizer_conj, centralizer_tH_eq, card_XH] at h5
    fin_cases i
    · rfl
    · exact absurd h5 (by decide)
    · exact absurd h5 (by decide)
    · exact absurd h5 (by decide)
  subst hi
  have hdt : IsConj (tH 0) d := isConj_iff.mpr ⟨g, hg.symm⟩
  have het : IsConj (tH 0) e := hdt.trans hde
  obtain ⟨k, hk⟩ := exists_orbElt_of_isConj hdt
  obtain ⟨k', hk'⟩ := exists_orbElt_of_isConj het
  have hsize : (orbTab 0).size = 63 := by
    have h := orbitsOK_parts 0
    simp only [orbitOK, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1
  have hlt : (k : ℕ) < (orbTab 0).size := by
    rw [hsize]
    exact k.2
  have hlt' : (k' : ℕ) < (orbTab 0).size := by
    rw [hsize]
    exact k'.2
  have hmd : mat6 d = dec6 ((orbTab 0).getD k []) := by
    rw [← hk]
    exact mat6_orbElt 0 hlt
  have hme : mat6 e = dec6 ((orbTab 0).getD k' []) := by
    rw [← hk']
    exact mat6_orbElt 0 hlt'
  have hcheck := sp62X2_check
  simp only [sp62X2OK, Array.all_eq_true_iff_forall_mem] at hcheck
  have hmem : ∀ j : ℕ, j < (orbTab 0).size → (orbTab 0).getD j [] ∈ orbit0 := fun j hj => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]
    exact Array.getElem_mem hj
  have h1 := hcheck _ (hmem k hlt) _ (hmem k' hlt')
  have hcomm6 : commutes6 ((orbTab 0).getD k []) ((orbTab 0).getD k' []) = true :=
    commutes6_of_commute hmd hme hc
  have hne6 : ((orbTab 0).getD k [] == (orbTab 0).getD k' []) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    apply hne
    apply mat6_injective
    rw [hme, ← h, hmd]
  simp only [hcomm6, hne6, Bool.not_true, Bool.false_or, Bool.or_false] at h1
  have hprod : mat6 (d * e) = dec6 (mul6 ((orbTab 0).getD k []) ((orbTab 0).getD k' [])) := by
    rw [map_mul, hmd, hme, dec6_mul6]
  exact eq_conj_of_found 2 hprod h1

theorem sp62TransvectionProduct_H6
    {d e : H6} (hd : orderOf d = 2) (h5 : 5 ∣ Nat.card ↥(Subgroup.centralizer ({d} : Set H6)))
    (hde : IsConj d e) (hc : d * e = e * d) (hne : e ≠ d) :
    ∃ P : Sylow 2 H6, (P : Subgroup H6) ≤ Subgroup.centralizer ({d * e} : Set H6) := by
  obtain ⟨g, hg⟩ := exists_conj_tH_two_of_transvections hd h5 hde hc hne
  have hcard : 512 ∣ Nat.card ↥(Subgroup.centralizer ({d * e} : Set H6)) := by
    rw [hg, card_centralizer_conj, centralizer_tH_eq, card_XH]
    decide
  exact exists_sylow_le_of_dvd hcard

theorem sp62TransvectionProduct_of :
    Sp62TransvectionProduct := by
  intro X _ _ hX d e hd h5 hde hc hne
  obtain ⟨φ⟩ := nonempty_mulEquiv_statedSp_of_lieModel hX
  have hd' : orderOf (φ d) = 2 := (MulEquiv.orderOf_eq φ d).trans hd
  have h5' : 5 ∣ Nat.card ↥(Subgroup.centralizer ({φ d} : Set H6)) := by
    rw [card_centralizer_map_equiv]
    exact h5
  have hde' : IsConj (φ d) (φ e) := by
    obtain ⟨c, hc'⟩ := isConj_iff.mp hde
    exact isConj_iff.mpr ⟨φ c, by rw [← map_mul, ← map_inv, ← map_mul, hc']⟩
  have hc'' : φ d * φ e = φ e * φ d := by rw [← map_mul, ← map_mul, hc]
  have hne' : φ e ≠ φ d := fun h => hne (φ.injective h)
  have h := sp62TransvectionProduct_H6 hd' h5' hde' hc'' hne'
  rw [← map_mul] at h
  exact exists_sylow_le_centralizer_of_equiv φ h

end CFSG.Quasithin.H13.U3
