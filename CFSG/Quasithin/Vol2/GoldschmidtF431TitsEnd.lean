module

public import CFSG.Quasithin.Recognition.F4Thirtyone
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsOrd

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w' v

namespace LieSetting

variable {S : LieSetting.{u, w}} {Y : Type w'} [Group Y] {M : Type v} [Group M]

theorem lemma_F444I [Finite M] {T : Subgroup S.ι.G0} {z t : S.ι.G0} (β : S.α.Completion Y)
    (hβ : β.IsFaithful) (ε : Y →* M) (hε : Function.Injective ε)
    (D : F431LieI T S.Mb1 S.Mb2 z t)
    (hb : Subgroup.centralizer ({amalgamMap (bOne S.hι β ε) (bTwo S.hι β ε) z} : Set M) ≤
      (bOne S.hι β ε).range)
    (hnc : ¬ IsConj (amalgamMap (bOne S.hι β ε) (bTwo S.hι β ε) z)
      (amalgamMap (bOne S.hι β ε) (bTwo S.hι β ε) t))
    (h442 : Subgroup.centralizer ({amalgamMap (bOne S.hι β ε) (bTwo S.hι β ε) t} : Set M) ≤
      (bTwo S.hι β ε).range)
    (hF424 : Nat.card Y ≤ Nat.card S.Yb → Nat.card Y = Nat.card S.Yb ∧
      ∃ (Ġ : Type w') (_ : Group Ġ), S.IsExtension Ġ ∧ Nonempty (Y ≃* Ġ)) :
    Nat.card M = Nat.card S.Yb ∧
      ∃ (Ġ : Type w') (_ : Group Ġ), S.IsExtension Ġ ∧ Nonempty (M ≃* Ġ) ∧
        Nat.card Ġ = Nat.card S.Yb := by
  have hC := fComp S.hι β hβ ε hε
  have h443 := D.lemma_F443 hC hb hnc h442
  have hG0 : Nat.card S.ι.G0 = Nat.card S.Yb := card_G0 S.ι
  have hle : Nat.card Y ≤ Nat.card S.Yb := by
    have := Nat.card_le_card_of_injective ε hε
    omega
  obtain ⟨hY, Ġ, hG, hext, ⟨φ⟩⟩ := hF424 hle
  have hMY : Nat.card M = Nat.card S.Yb := by omega
  have hbij : Function.Bijective ε :=
    hε.bijective_of_nat_card_le (by omega)
  have hGY : Nat.card Ġ = Nat.card S.Yb := by
    rw [← Nat.card_congr φ.toEquiv, hY]
  exact ⟨hMY, Ġ, hG, hext, ⟨(MulEquiv.ofBijective ε hbij).symm.trans φ⟩, hGY⟩

end LieSetting

end CFSG.Quasithin
