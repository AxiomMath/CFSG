module

public import CFSG.LocalAnalysis.StandardType.GGE6OppCentre
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeE6Rank
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZCatalogue
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGTwistedLabelModels
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcG2Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcRed

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc
open CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

private theorem inf_center_eq_bot_of_not_three_dvd {H : Type} [Group H] [Finite H]
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center H)) {B : Subgroup H} (hB : IsElemAbelian 3 B) :
    B ⊓ Subgroup.center H = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (B ⊓ Subgroup.center H : Subgroup H) :=
    (hB.mono (inf_le_left : B ⊓ Subgroup.center H ≤ B)).isPGroup
  have hdvd : Nat.card (B ⊓ Subgroup.center H : Subgroup H) ∣ Nat.card (Subgroup.center H) :=
    Subgroup.card_dvd_of_le (inf_le_right : B ⊓ Subgroup.center H ≤ Subgroup.center H)
  rcases hP.card_eq_or_dvd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exact absurd (h3.trans hdvd) hZ

private theorem card_map_comp_mk'_eq {H G : Type} [Group H] [Finite H] [Group G]
    {B : Subgroup H} (hBZ : B ⊓ Subgroup.center H = ⊥)
    (e : H ⧸ Subgroup.center H ≃* G) :
    Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H)))) = Nat.card B := by
  classical
  let ψ : H →* G := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
  let g : ↥B →* G := ψ.comp B.subtype
  have hker : g.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxZ : (x : H) ∈ Subgroup.center H := by
      have h1 : QuotientGroup.mk' (Subgroup.center H) (x : H) = 1 := by
        apply e.injective
        rw [map_one]
        exact hx
      exact (QuotientGroup.eq_one_iff (x : H)).1 h1
    have hxbot : (x : H) ∈ B ⊓ Subgroup.center H := ⟨x.2, hxZ⟩
    rw [hBZ, Subgroup.mem_bot] at hxbot
    rw [Subgroup.mem_bot]
    exact Subtype.ext hxbot
  have hg : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).mp hker
  have hrange : g.range = B.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  calc Nat.card (B.map ψ) = Nat.card g.range := by rw [hrange]
    _ = Nat.card B := (Nat.card_congr (MonoidHom.ofInjective hg).toEquiv).symm

private theorem two_pow_mod_three_of_dvd_add_one {f : ℕ} (h : 3 ∣ 2 ^ f + 1) :
    2 ^ f % 3 = 2 := by
  have h1 : (2 ^ f + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  rw [Nat.add_mod] at h1
  have h2 : 2 ^ f % 3 < 3 := Nat.mod_lt _ (by norm_num)
  omega

private theorem two_pow_mod_three_of_dvd_sub_one {f : ℕ} (h : 3 ∣ 2 ^ f - 1) :
    2 ^ f % 3 = 1 := by
  have h1 : (2 ^ f - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h3 : 2 ^ f % 3 < 3 := Nat.mod_lt _ (by norm_num)
  omega

theorem card_le_pow_four_of_e6Opp
    {H : Type} [Group H] [Finite H]
    [Group.IsPerfect H] {f : ℕ} (hf : 1 ≤ f)
    (hH : (GGHasLabel ⟨.E6, 0, f⟩ (H ⧸ Subgroup.center H) ∧ 3 ∣ 2 ^ f + 1) ∨
      (GGHasLabel ⟨.twE6, 0, f⟩ (H ⧸ Subgroup.center H) ∧ 3 ∣ 2 ^ f - 1))
    {B : Subgroup H} (hB : IsElemAbelian 3 B) : Nat.card B ≤ 3 ^ 4 := by
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center H) :=
    not_three_dvd_card_center_of_e6Opp hf hH
  have hBZ : B ⊓ Subgroup.center H = ⊥ := inf_center_eq_bot_of_not_three_dvd hZ hB
  rcases hH with ⟨hE6, h3⟩ | ⟨htwE6, h3⟩
  · obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hE6
    have hK3 : Nat.card K % 3 = 2 := by rw [hK]; exact two_pow_mod_three_of_dvd_add_one h3
    have e' : (H ⧸ Subgroup.center H) ≃* adjointGroup .E6 K :=
      e.trans (TableBExc.recipeEquiv .E6 K)
    let ψ : H →* adjointGroup .E6 K :=
      e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
    calc Nat.card B = Nat.card (B.map ψ) := (card_map_comp_mk'_eq hBZ e').symm
      _ ≤ 3 ^ 4 := card_le_pow_four_E6_three_of_mod_two hK3 (hB.map ψ)
  · obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := htwE6
    obtain ⟨K', hF', hfin', σ', hK', hσ', eZ, -⟩ :=
      TablePThreeKG.tableZ_recipe_catalogue (n := f) hf K hK
    have hq3 : 2 ^ f % 3 = 1 := two_pow_mod_three_of_dvd_sub_one h3
    have e' : (H ⧸ Subgroup.center H) ≃* ↥(twistedE6RootGroup K' σ') := e.trans eZ
    let ψ : H →* ↥(twistedE6RootGroup K' σ') :=
      e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
    calc Nat.card B = Nat.card (B.map ψ) := (card_map_comp_mk'_eq hBZ e').symm
      _ ≤ 3 ^ 4 := card_le_pow_four_twistedE6_three_of_mod_one
          (F₀ := GaloisField 2 f) (q := 2 ^ f) (GaloisField.card 2 f (by omega))
          hK' σ' hσ' hq3 (hB.map ψ)

end CFSG.StandardType

end
