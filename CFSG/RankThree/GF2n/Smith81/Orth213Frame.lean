module

public import CFSG.RankThree.GF2n.Smith81.Orth213Stmts
public import CFSG.RankThree.GF2n.Smith81.SmithOrthCfgConj

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

namespace Orth213

theorem concl_of_isConj {G : Type} [Group G] {z a x y : G} (h : IsConj z a)
    (hc : Orth213Concl a x y) : Orth213Concl z x y :=
  ⟨hc.1, fun h4 => h.trans (hc.2 h4)⟩

end Orth213

theorem orth213Frame_of (hE : Orth213ElemStatement) :
    Orth213FrameStatement := by
  intro G _ _ M Q Z B hc z hz hz1 A hA x y hxz hyz hxA hyA
  have H := hc.ctx.hyp
  obtain ⟨g, rfl⟩ := hA
  have hc' := hc.conj g
  have haA : g * z * g⁻¹ ∈ conjSubgroup g Z :=
    mem_conjSubgroup.mpr (by simpa [mul_assoc] using hz)
  have ha1 : g * z * g⁻¹ ≠ 1 := by
    intro h
    apply hz1
    have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [this, h]; group
  have haz : IsConj z (g * z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  have hQx : x ∈ conjSubgroup g Q := by rw [← QB_conj_eq H g]; exact hxA
  have hxM : x ∈ conjSubgroup g M := Subgroup.map_mono H.Q_normal.1 hQx
  have hyM : y ∈ conjSubgroup g M := by
    rw [← normalizer_conj_eq H g]
    exact Subgroup.centralizer_le_normalizer _ hyA
  exact Orth213.concl_of_isConj haz
    (hE G (conjSubgroup g M) (conjSubgroup g Q) (conjSubgroup g Z) (conjSubgroup g B) hc'
      (g * z * g⁻¹) haA ha1 x y hxM hyM (haz.symm.trans hxz) (haz.symm.trans hyz)
      (Or.inl hQx))

end CFSG.RankThree.GF2n.Smith81
