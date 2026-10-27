module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTypeA
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBTorus
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem card_inf_centralizer_ge {M : Type} [Group M] [Finite M]
    {L' E : Subgroup M} {R : Type} [Group R] {I : Set (MulAut R)}
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    {p : ℕ} (hP : GGTableBPosition p L' E I θ hE) (hp : p.Prime)
    (hne : E ⊓ Subgroup.centralizer (L' : Set M) ≠ ⊥) :
    p ≤ Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) := by
  obtain ⟨-, hEA, -⟩ := hP
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hxE : (x : M) ∈ E := x.2.1
  have hxp : x ^ p = 1 := Subtype.ext (by simpa using hEA.2 (x : M) hxE)
  have hdiv : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  have hord : orderOf x = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf x) hdiv with h | h
    · exact absurd h hne1
    · exact h
  haveI : Finite (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) :=
    Finite.of_injective (fun y => (y : M)) Subtype.coe_injective
  rw [← hord]
  exact orderOf_le_card

theorem ggTorusGenTableB_of_rk {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) {R : Type} [Group R]
    {I : Set (MulAut R)} (hL : GGTorusLift p (r - 1) R) (h : GGTorusGenTableBRk p R I r) :
    GGTorusGenTableB p R I := by
  intro M _ _ L' E E₁ D' J' d θ hE hpos hne hE₁ hbot hcard hnorm hD'E hDE hD'd hd hJ
  have hpr : p ^ r ≤ Nat.card E := by
    have hge := card_inf_centralizer_ge hpos hp hne
    have hmul := TableBBridge.card_eq_card_range_mul (L' := L') (E := E) hE
    have hrank := TableBBridge.pow_le_card_range_of_torusLift (L' := L') (E := E) hpos hp hL
    rw [hmul]
    calc p ^ r = p ^ ((r - 1) + 1) := by rw [Nat.sub_add_cancel hr]
      _ = p ^ (r - 1) * p := by rw [Nat.pow_succ]
      _ ≤ Nat.card (ggGamma L' hE).range *
            Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) :=
          Nat.mul_le_mul hrank hge
  exact h M L' E E₁ D' J' d θ hE hpos hpr hne hE₁ hbot hcard hnorm hD'E hDE hD'd hd hJ

private theorem ggLAut_trans_eq_congr {G : Type*} [Group G] (L : Subgroup G)
    {R R' : Type} [Group R] [Group R'] (θ : L ⧸ Subgroup.center L ≃* R) (e : R ≃* R')
    (g : Subgroup.normalizer (L : Set G)) :
    ggLAut L (θ.trans e) g = MulAut.congr e (ggLAut L θ g) := by
  ext a
  obtain ⟨q, rfl⟩ := (θ.trans e).surjective a
  induction q using QuotientGroup.induction_on with
  | H l =>
      rw [ggLAut_apply, MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [ggLAut_apply]

private theorem position_of_mulEquiv {p : ℕ} {M : Type} [Group M]
    {L' E : Subgroup M} {R R' : Type} [Group R] [Group R']
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (e : R ≃* R')
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hP : GGTableBPosition p L' E I θ hE) :
    GGTableBPosition p L' E I' (θ.trans e) hE := by
  obtain ⟨hperf, hEA, hcard, h4, h5, h6, h7⟩ := hP
  exact ⟨hperf, hEA, hcard, fun x => by
    rw [ggLAut_trans_eq_congr]
    exact hI _ (h4 x), h5, h6, h7⟩

theorem ggTorusGenTableB_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R']
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (e : R ≃* R')
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTorusGenTableB p R' I') :
    GGTorusGenTableB p R I := by
  intro M _ _ L' E E₁ D' J' d θ hE hpos hne hE₁ hbot hcard hnorm hD'E hDE hD'd hd hJ
  exact h M L' E E₁ D' J' d (θ.trans e) hE (position_of_mulEquiv e hI hpos)
    hne hE₁ hbot hcard hnorm hD'E hDE hD'd hd hJ

end CFSG.StandardType
