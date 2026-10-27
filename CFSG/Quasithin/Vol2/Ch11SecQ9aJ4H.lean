module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aJ4E
public import CFSG.Quasithin.Vol2.Ch11SecQ9aJ4G
public import CFSG.Quasithin.H13.J4TypeFinal
public import CFSG.Quasithin.Vol2.Ch11SecQ9aJ4A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.J4U

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT


theorem isTypeJ4Centralizer_z0 : CFSG.Quasithin.H13.J4.IsTypeJ4Centralizer J z0 := by
  have hF := j4Facts
  have hM := hF.mat
  have := finite_J
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := CFSG.Quasithin.H13.J4.tJ_twoCentral
  let P : Sylow 2 J := Sylow.ofCard P0 (by rw [card_P0 hM hF, card_J_factorization hF])
  have hz : z0 ∈ (Subgroup.center (P : Subgroup J)).map (P : Subgroup J).subtype := by
    refine ⟨⟨z0, (z0_central hM hF).1⟩, Subgroup.mem_center_iff.mpr fun x => Subtype.ext ?_, rfl⟩
    exact (z0_central hM hF).2 x x.2
  have htJ : CFSG.Quasithin.H13.J4.tJ ≠ 1 := fun h => by
    have h1 := CFSG.Quasithin.H13.J4.orderOf_tJ
    rw [h, orderOf_one] at h1
    norm_num at h1
  obtain ⟨c, hc⟩ := isConj_iff.mp (CFSG.Quasithin.H13.J4.isConj_of_twoCentral
    CFSG.Quasithin.H13.J4.card_center_sylow_J htJ (z0_ne_one hM) hT hz)
  exact CFSG.Quasithin.H13.J4.isTypeJ4Centralizer_tJ.of_mulEquiv (MulAut.conj c)
    (by rw [MulAut.conj_apply, hc])

theorem l24Unique_P0 : O11.L24Unique P0 := by
  have hF := j4Facts
  have hM := hF.mat
  have := finite_J
  have hP0z : P0 ≤ Subgroup.centralizer ({z0} : Set J) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((z0_central hM hF).2 x hx)
  intro B₁ B₂ h₁ h₂
  exact eq_of_le_centralizer isTypeJ4Centralizer_z0 isSylowTwoOf_P0 hP0z h₁ h₂
    (le_centralizer_z0 h₁) (le_centralizer_z0 h₂)

theorem _root_.CFSG.Quasithin.Vol2.Ch11.SecS.factJ4UniqueL24_holds : FactJ4UniqueL24 := by
  intro Q _ _ hQ S hS
  obtain ⟨e⟩ := hQ
  exact O11.l24Unique_of_equiv isSylowTwoOf_P0 l24Unique_P0 ⟨e.trans (seedEquiv j4Facts.mat)⟩ hS

end CFSG.Quasithin.Vol2.Ch11.SecS.J4U
