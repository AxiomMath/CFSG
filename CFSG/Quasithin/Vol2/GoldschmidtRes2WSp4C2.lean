module

public import CFSG.Quasithin.Vol2.Ch3E213MP6BI
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WSp4Pkg

public section

namespace CFSG.Quasithin.Res2

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M

theorem pkgSp4C2215W
    (hG41 : FactSp4TransvW)
    (hCTwo : FactSp4CTwo) (hE : Sp4MemberE215W) : PkgSp4C2215W := by
  intro G _ _ H T M V K hS _ _ hB k _ _ _ n hn hk D hl hμ
  obtain ⟨h, r, hh, hσ⟩ := P6B.swap_data hS D
  have hsp := P6B.spansCenter_coordIn D hμ
  rcases P6B.exists_member_or_suzuki hG41 hCTwo hn hk D.V_le_center hl hsp hh hσ with
    ⟨F₀, c, g, hc, hgY, hY⟩ | ⟨F₀, a, ha, hcard, d, hd, hW⟩
  · obtain ⟨g', hg'⟩ := exists_sp4Member_of_subfieldSp hS hB D hc hgY hY
    exact hE G H T M V g' ↥F₀ hg'
  · obtain ⟨Y, g, hgY, hY, hSyl, hcore, hO2, hO2B, hexact, m, hm3, hYcard, hWm⟩ :=
      P6B.exists_sz_member_card D.V_le_center (P6B.four_le_card_coordIn hS D) ha hcard hd hW
    obtain ⟨g', hg', hpair, hc2, hne, -, ⟨φ, hφs, hφk⟩, hVB⟩ :=
      exists_coord_member hS hB D hgY hY hSyl hcore hO2 hO2B hexact
    have hcardX : (kerIn (M ⊓ Ch3n.pairI V g') (Ch3n.pairI V g')).relIndex (Ch3n.pairI V g') =
        (2 ^ m) ^ 2 * (((2 ^ m) ^ 2 + 1) * (2 ^ m - 1)) := by
      rw [Subgroup.relIndex, Subgroup.index, ← hφk, ← hYcard]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv
    intro _
    exact ⟨g', hg', hpair, hc2, hne, relIndex_le_of_sz hpair hc2 hm3 hcardX,
      e215DataW_of_sz hpair hc2 hm3 hcardX (hVB.trans hWm)⟩

end CFSG.Quasithin.Res2
