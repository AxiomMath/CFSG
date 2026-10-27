module

public import CFSG.Quasithin.Vol2.Ch11SecE3PerH
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch7Setup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem wParam_le_nPrime_of_e22
    (hE22 : E2.E22StatementC) (h331 : Stmt3_3_1) (hyp : Hyp7_0_2 G T L I)
    (hV : IsElemAbelian 2 (fsuV T I)) (hE : HypE336 T (fsuV T I) (fsuM T L))
    (hCM : Subgroup.centralizer (fsuV T I : Set G) ≤ fsuM T L)
    (hr : (nPrime (autI hV ⊤) : ℕ∞) < rParam (fsuV T I)) :
    (∀ H : Subgroup G, IsHStar T (fsuM T L) H →
        wParam T (fsuV T I) ≤ E1.nParam H ∧ E1.nParam H ≤ (nPrime (autI hV ⊤) : ℕ∞)) ∧
      wParam T (fsuV T I) ≤ (nPrime (autI hV ⊤) : ℕ∞) := by
  have hall : ∀ H : Subgroup G, IsHStar T (fsuM T L) H →
      wParam T (fsuV T I) ≤ E1.nParam H ∧ E1.nParam H ≤ (nPrime (autI hV ⊤) : ℕ∞) :=
    fun H hH => (Vol2.Ch11.SecE3.as_e_3_39_of_e22 hE22 hV (fsuV_ne_bot hyp.fsu)
      hyp.fsu.simple hyp.fsu.nonabelian hE hCM hr hH).1
  obtain ⟨H, hH⟩ := ((h331 G T hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.sylow).2 L hyp.fsu.maximal hyp.fsu.quasisimple).2.2.1
  exact ⟨hall, ((hall H hH).1).trans (hall H hH).2⟩

end CFSG.Quasithin.H13

end
