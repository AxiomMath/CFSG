module

public import CFSG.RankThree.PartTwo.Sec4.E27.Core
public import CFSG.RankThree.PartTwo.Sec10.Item1015Proof

public section

open CFSG.Open
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.RankThree.PartTwo.Sec10.Item1015Proof

namespace CFSG.RankThree.PartTwo.Sec4.E27

theorem seitz27_of_card_le_nine {X : Type} [Group X]
    (h : ∀ B : Subgroup (MulAut X), IsElemAbelian 3 B → Nat.card B ≤ 9) : Seitz27 X := by
  intro E hE hc
  exfalso
  have := h E hE
  omega

theorem seitz27_projSL_vac {p f : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) (hf1 : 1 ≤ f) (hf : ¬ 3 ∣ f)
    {X : Type} [Group X] (e : X ≃* projSL 3 (GaloisField p f)) : Seitz27 X :=
  seitz27_of_card_le_nine fun B hB =>
    card_le_nine_of_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
      (fun B' hB' => card_le_nine_of_mulAut_projSL hp3 hf1 hf B' hB') B hB

theorem seitz27_projSU_vac {p f : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) (hf1 : 1 ≤ f) (hq : 2 < p ^ f)
    (hf : ¬ 3 ∣ f) {X : Type} [Group X] (e : X ≃* projSU 3 p f) : Seitz27 X :=
  seitz27_of_card_le_nine fun B hB =>
    card_le_nine_of_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
      (fun B' hB' => card_le_nine_of_mulAut_projSU hp3 hf1 hq hf B' hB') B hB

end CFSG.RankThree.PartTwo.Sec4.E27
