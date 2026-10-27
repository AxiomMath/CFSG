module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Emb
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Klein
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44DataG2Y
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Shape
import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G2YBounded

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)

theorem isTISub_conj {G : Type} [Group G] (h : G) (A : Subgroup G) :
    IsTISub G (A.map (MulAut.conj h).toMonoidHom) ↔ IsTISub G A :=
  Sp44.w183finSp44G2Y_isTISub_map_iff (MulAut.conj h) A

theorem corConfig_conj {G : Type} [Group G] (h : G) (A : Subgroup G) :
    CorConfig G (A.map (MulAut.conj h).toMonoidHom) → CorConfig G A :=
  (Sp44.w183finSp44G2Y_corConfig_map_iff (MulAut.conj h) A).mpr

theorem ticorConfigHolds_of_equiv {G H : Type} [Group G] [Group H] (σ : G ≃* H)
    (h : TICorConfigHolds H) : TICorConfigHolds G := by
  intro A hcard hel hTI
  have hcard' : Nat.card (A.map σ.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective σ.injective]; exact hcard
  have hel' : IsElemAbelian 2 (A.map σ.toMonoidHom) := hel.map σ.toMonoidHom
  have hTI' : IsTISub H (A.map σ.toMonoidHom) :=
    (Sp44.w183finSp44G2Y_isTISub_map_iff σ A).mpr hTI
  exact (Sp44.w183finSp44G2Y_corConfig_map_iff σ A).mpr (h _ hcard' hel' hTI')

namespace Sp44

theorem not_isTISub_of_check {p : Nat × Nat} (hp : p ∈ pairsL) {e : Nat} (he : 0 < e)
    (he' : (e - 1) / 3 < g2Pool.length)
    (hc : checkTIfail invsA[p.1]! invsA[p.2]! e = true) :
    ¬ IsTISub (MulAut S4) (kleinSub invsA[p.1]! invsA[p.2]!) :=
  w183finSp44G2Y_not_isTISub_of_check_aux hp he he' hc

theorem corConfig_of_check {p : Nat × Nat} (hp : p ∈ pairsL)
    {c : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat}
    (hc : checkCor invsA[p.1]! invsA[p.2]! c = true)
    (hgA : validB (c.2.1, c.2.2.1) = true)
    (hg1 : validB (c.2.2.2.1, c.2.2.2.2.1) = true)
    (hg2 : validB (c.2.2.2.2.2.1, c.2.2.2.2.2.2.1) = true)
    (hy : validB (c.2.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.2) = true) :
    CorConfig (MulAut S4) (kleinSub invsA[p.1]! invsA[p.2]!) :=
  w183finSp44G2Y_corConfig_of_check_aux hp hc hgA hg1 hg2 hy

theorem ticorConfigHolds_S4 : TICorConfigHolds (MulAut S4) := by
  intro A hcard hel hTI
  obtain ⟨k, p, hp, hk⟩ := exists_conj_klein A hel hcard
  have hTI' : IsTISub (MulAut S4) (kleinSub invsA[p.1]! invsA[p.2]!) := by
    rw [← hk]
    exact (isTISub_conj k A).mpr hTI
  rcases w183finSp44G2Y_g2_complete_bounded p hp with ⟨e, he, he', hc⟩ | ⟨c, hc, hvalid⟩
  · exact absurd hTI' (not_isTISub_of_check hp he he' hc)
  · have hcor : CorConfig (MulAut S4) (kleinSub invsA[p.1]! invsA[p.2]!) := by
      have hv := hvalid
      simp only [w183finSp44G2Y_corRowValid, Bool.and_eq_true] at hv
      obtain ⟨⟨⟨hgA, hg1⟩, hg2⟩, hy⟩ := hv
      exact corConfig_of_check hp hc hgA hg1 hg2 hy
    rw [← hk] at hcor
    exact corConfig_conj k A hcor

end Sp44

theorem finG2Y_holds : FinG2Y := by
  intro Y _ _ L hLn hSp hC hτ
  obtain ⟨f, hf_inj, hfL⟩ := Sp44.exists_emb Y L hLn hSp hC
  have hf_bij : Function.Bijective f := Sp44.emb_bijective Y L f hf_inj hfL hτ
  exact ticorConfigHolds_of_equiv (MulEquiv.ofBijective f hf_bij) Sp44.ticorConfigHolds_S4

end CFSG.LocalAnalysis.WeakClosure81

end
