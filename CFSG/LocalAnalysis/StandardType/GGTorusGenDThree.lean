module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLDvd

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem largeEvenLabelAll_torusGenTableB_dThree {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .D) (hl : lab.rank = 3)
    (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hpn hlab ⊢
  subst htag hl
  exact largeEvenLabelAll_torusGenTableB_typeA hp (lab := ⟨.A, 3, n⟩)
    ⟨hlab.1, by norm_num, fun h => absurd h (by norm_num)⟩ rfl le_rfl hpn

end CFSG.StandardType
