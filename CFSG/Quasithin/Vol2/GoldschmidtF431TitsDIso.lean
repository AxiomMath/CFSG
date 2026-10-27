module

public import CFSG.Quasithin.Recognition.RuTypeJ47a
public import CFSG.Quasithin.Recognition.CertTitsAmalgamLocal
public import CFSG.Quasithin.Recognition.CertSzZero
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDModel

public section

namespace CFSG.Quasithin.H13.F431.TitsD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RuType CFSG.Sporadic.Schreier.Tits

set_option linter.unusedSectionVars false


theorem exists_amalgamIso_of_clause1 {G : Type} [Group G] [Finite G] {H L2 : Subgroup G}
    (hα : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H L2)
      (fun Y _ => Nonempty (Y ≃* quasithinTits)))
    (hq : Nonempty (oTwoQuot ↥H ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥H ≃* Sz 0)) :
    Nonempty ((RankTwoAmalgam.ofSubgroups titsH titsN).Iso (RankTwoAmalgam.ofSubgroups H L2)) := by
  obtain ⟨Y, _, ⟨e⟩, T, M₁, M₂, hpair, ⟨iso⟩⟩ := hα
  let φ : Y ≃* titsD := e.trans quasithinTitsEquivD
  have hpair' := IsYAmalgamPair.map φ hpair
  obtain ⟨ρ, hρ⟩ := exists_mulEquiv_map_sylow sylow_D hpair'.1
  let f : Y ≃* titsD := φ.trans ρ
  have hmap : ∀ M : Subgroup Y,
      (M.map φ.toMonoidHom).map ρ.toMonoidHom = M.map f.toMonoidHom := fun M =>
    Subgroup.map_map _ _ _
  have hpairf := IsYAmalgamPair.map ρ hpair'
  rw [hρ, hmap, hmap] at hpairf
  have hlocal : ∀ M : Subgroup Y, (M = M₁ ∨ M = M₂) →
      (M.map f.toMonoidHom = titsHD ∨ M.map f.toMonoidHom = titsND) := by
    intro M hM
    obtain ⟨hmax, hnorm⟩ := (hpairf.2.2 (M.map f.toMonoidHom)).2
      (by rcases hM with rfl | rfl <;> simp)
    exact titsTwoLocalLattice.eq_P₁_or_P₂_of_maxTwoLocal hmax (Subgroup.le_normalizer.trans hnorm)
  have hne : M₁.map f.toMonoidHom ≠ M₂.map f.toMonoidHom := fun h =>
    hpair.2.1 (Subgroup.map_injective f.injective h)
  rcases hlocal M₁ (Or.inl rfl) with h1 | h1 <;> rcases hlocal M₂ (Or.inr rfl) with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact ⟨amIsoSymm (amIsoTrans iso (amIsoTrans (ofSubgroupsMapIso f M₁ M₂)
      (amIsoTrans (ofSubgroupsCongr h1 h2)
        (ofSubgroupsSubgroupOfIso titsH_le_titsD titsN_le_titsD))))⟩
  · exfalso
    let ψ : ↥H ≃* ↥titsND := (iso.φ1.trans (f.subgroupMap M₁)).trans
      (MulEquiv.subgroupCongr h1)
    have hd : Nat.card (oTwoQuot ↥H) ∣ Nat.card ↥H := Subgroup.card_quotient_dvd_card _
    rw [Nat.card_congr ψ.toEquiv, card_titsND] at hd
    rcases hq with ⟨⟨χ⟩⟩ | ⟨⟨χ⟩⟩
    · rw [Nat.card_congr χ.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card] at hd
      norm_num at hd
    · rw [Nat.card_congr χ.toEquiv, card_sz_zero_eq_twenty] at hd
      norm_num at hd
  · exact absurd (h1.trans h2.symm) hne

end CFSG.Quasithin.H13.F431.TitsD
