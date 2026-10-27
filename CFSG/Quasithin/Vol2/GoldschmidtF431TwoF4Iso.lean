module

public import CFSG.Quasithin.Recognition.RuTypeJ47k
public import CFSG.Quasithin.Recognition.CertSzZero
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Model

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RuType CFSG.Quasithin.RuType.J47
  CFSG.Sporadic.Schreier.Tits

set_option linter.unusedSectionVars false


theorem card_twoF4N : Nat.card twoF4N = 12288 := by
  have h := Subgroup.card_mul_index (titsN.subgroupOf twoF4N)
  have h2 : (titsN.subgroupOf twoF4N).index = 2 :=
    relIndex_extSub (fun hq => tπ_not_mem_D (titsN_le_titsD hq))
  have hle : titsN ≤ twoF4N := le_extSub
  rw [h2, card_subgroupOf_eq hle, (titsQN_facts).2.2.2] at h
  omega

theorem exists_amalgamIso_of_clause2 {G : Type} [Group G] [Finite G] {H L2 : Subgroup G}
    (hα : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H L2) (IsTwistedF4Over 1))
    (hq : Nonempty (oTwoQuot ↥H ≃* Sz 0)) :
    Nonempty ((RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso
      (RankTwoAmalgam.ofSubgroups H L2)) := by
  obtain ⟨Y, _, hTw, T, M₁, M₂, hpair, ⟨iso⟩⟩ := hα
  obtain ⟨e⟩ : Nonempty (Y ≃* MulAut CFSG.Open.quasithinTits) := by
    rcases hTw with ⟨-, h⟩ | ⟨h, -, -⟩
    · exact h
    · omega
  let φ : Y ≃* twoF4M := e.trans (twoF4AutEquiv titsOutBound)
  have hpair' := IsYAmalgamPair.map φ hpair
  obtain ⟨ρ, hρ⟩ := exists_mulEquiv_map_sylow twoF4Lattice.isSylowTwoOf_top hpair'.1
  let f : Y ≃* twoF4M := φ.trans ρ
  have hmap : ∀ M : Subgroup Y,
      (M.map φ.toMonoidHom).map ρ.toMonoidHom = M.map f.toMonoidHom := fun M =>
    Subgroup.map_map _ _ _
  have hpairf := IsYAmalgamPair.map ρ hpair'
  rw [hρ, hmap, hmap] at hpairf
  have hlocal : ∀ M : Subgroup Y, (M = M₁ ∨ M = M₂) →
      (M.map f.toMonoidHom = twoF4Lattice.P₁ ∨ M.map f.toMonoidHom = twoF4Lattice.P₂) := by
    intro M hM
    obtain ⟨hmax, hnorm⟩ := (hpairf.2.2 (M.map f.toMonoidHom)).2
      (by rcases hM with rfl | rfl <;> simp)
    exact twoF4Lattice.eq_P₁_or_P₂_of_maxTwoLocal hmax (Subgroup.le_normalizer.trans hnorm)
  have hne : M₁.map f.toMonoidHom ≠ M₂.map f.toMonoidHom := fun h =>
    hpair.2.1 (Subgroup.map_injective f.injective h)
  rcases hlocal M₁ (Or.inl rfl) with h1 | h1 <;> rcases hlocal M₂ (Or.inr rfl) with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · have h1' : M₁.map (f : Y →* twoF4M) = twoF4H.subgroupOf twoF4M := h1.trans twoF4Lattice_P₁
    have h2' : M₂.map (f : Y →* twoF4M) = twoF4N.subgroupOf twoF4M := h2.trans twoF4Lattice_P₂
    exact ⟨amIsoSymm (amIsoTrans iso (amIsoTrans (ofSubgroupsMapIso f M₁ M₂)
      (amIsoTrans (ofSubgroupsCongr h1' h2')
        (ofSubgroupsSubgroupOfIso twoF4H_le_twoF4M twoF4N_le_M))))⟩
  · exfalso
    let ψ : ↥H ≃* ↥twoF4N := (iso.φ1.trans (f.subgroupMap M₁)).trans
      ((MulEquiv.subgroupCongr h1).trans ((MulEquiv.subgroupCongr twoF4Lattice_P₂).trans
        (Subgroup.subgroupOfEquivOfLe twoF4N_le_M)))
    obtain ⟨χ⟩ := hq
    have h20 : Nat.card (oTwoQuot ↥H) = 20 := by
      rw [Nat.card_congr χ.toEquiv, card_sz_zero_eq_twenty]
    have hd : Nat.card (oTwoQuot ↥H) ∣ Nat.card ↥H := Subgroup.card_quotient_dvd_card _
    rw [h20, Nat.card_congr ψ.toEquiv, card_twoF4N] at hd
    norm_num at hd
  · exact absurd (h1.trans h2.symm) hne

end CFSG.Quasithin.H13.F431.TwoF4
