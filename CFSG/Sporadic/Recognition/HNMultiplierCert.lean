module

public import Certificates.Certificate24321
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.HN

public section

namespace CFSG.Sporadic.Recognition.HNMultiplier

open CFSG.CosetTable

noncomputable def hnEquiv :
    CFSG.Blueprint.NativeSporadic.HN ≃* HNJ :=
  CFSG.Sporadic.HN.hnSeedEquiv

theorem card_HNJ : Nat.card HNJ = 273030912000000 := by
  rw [← Nat.card_congr hnEquiv.toEquiv, CFSG.Sporadic.HN.card_HN]

theorem center_eq_bot_of_certificate
    {Q : Type} [Group Q] [Finite Q] (hQ : Group.IsPerfect Q)
    (hZ : IsPGroup 2 (Subgroup.center Q))
    (e : Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.HN) : Subgroup.center Q = ⊥ := by
  obtain ⟨⟨g, H⟩, hfin, hle⟩ := Certificates.certificate24321
  have hX : Finite HNJ := Nat.finite_of_card_ne_zero (by rw [card_HNJ]; norm_num)
  exact CFSG.Sporadic.Recognition.CoverRecipe.center_eq_bot_of_cover₂ (g := g) (R := hnRels)
    (cw := hnCommWord) H.gen H.rels mk_hnCommWord_mem H.comm hfin (hle.trans card_HNJ.ge) hQ hZ
    (e.trans hnEquiv)

end CFSG.Sporadic.Recognition.HNMultiplier
