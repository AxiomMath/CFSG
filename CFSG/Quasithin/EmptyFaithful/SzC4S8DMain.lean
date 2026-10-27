module

public import CFSG.Quasithin.EmptyFaithful.SzC4S8CMain
public import CFSG.Quasithin.EmptyFaithful.SzC4S8DCore

public section

namespace CFSG.Quasithin.SzC4S8D

open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Quasithin.SBc11

theorem card_eq_two_of_modO2Surj {G : Type} [Group G] [Finite G] {L : Subgroup G} {F F₀ : Type}
    [Field F] [Fintype F] [Field F₀] [Fintype F₀] {α : ↥L →* ↥(StatedSL 3 F)}
    {α₀ : ↥L →* ↥(StatedSL 3 F₀)} (hmod : IsModO2Surj L α) (hmod₀ : IsModO2Surj L α₀)
    (hcard₀ : Fintype.card F₀ = 2) : Fintype.card F = 2 := by
  have hcs := S1567.card_statedSL_eq_of_same_ker α α₀ hmod.1 hmod₀.1
    (hmod.2.trans hmod₀.2.symm)
  rw [card_statedSL_three1527d, card_statedSL_three1527d] at hcs
  have hF₀ : Nat.card F₀ = 2 := by rw [Nat.card_eq_fintype_card]; exact hcard₀
  rw [hF₀] at hcs
  have hp : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  rw [← Nat.card_eq_fintype_card]
  exact SzC4S8C.card_eq_two_of_sl3 hp hcs

end CFSG.Quasithin.SzC4S8D

namespace CFSG.Quasithin.SzC4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SBc11
open scoped commutatorElement Pointwise

theorem zq2_of_abW {G : Type} [Group G] [Finite G] {G₀ R L : Subgroup G}
    (hcorr : MS93.IsC134Case4Corr G₀ R L)
    (hn1 : ∃ (F : Type) (_ : Field F) (_ : Fintype F)
        (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
      Fintype.card F = 2 ∧ IsModO2Surj L α)
    (hW : ∃ W : Subgroup G, frattiniIn (c134Q G₀ L) ≤ W ∧
      W ≤ c134Q G₀ L ⊓ Subgroup.centralizer (frattiniIn (c134Q G₀ L) : Set G) ∧
      L ≤ Subgroup.normalizer (W : Set G) ∧ (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧
      ¬ W ≤ centerOf (c134Q G₀ L ⊓ Subgroup.centralizer (frattiniIn (c134Q G₀ L) : Set G))) :
    centerOf (c134Q G₀ L ⊓ Subgroup.centralizer (frattiniIn (c134Q G₀ L) : Set G)) =
      frattiniIn (c134Q G₀ L) := by
  obtain ⟨W, hΦW, hWQ₂, hLW, hWab, hWc⟩ := hW
  obtain ⟨⟨n, F, _, _, α, hcard, hmod, hE2, -, -, -, hΦ, hQ₂, hQ⟩, -⟩ := hcorr
  obtain ⟨F₀, _, _, α₀, hcard₀, hmod₀⟩ := hn1
  have hF2 : Fintype.card F = 2 := SzC4S8D.card_eq_two_of_modO2Surj hmod hmod₀ hcard₀
  obtain ⟨u, hu⟩ := SzC4S8C.exists_gl hF2
  obtain ⟨g, hg⟩ := hmod.1 ⟨u, S1567.mem_statedSL_of_card_two hF2 u⟩
  have hgN : moduleAct true (α g : Matrix.GeneralLinearGroup (Fin 3) F) = SzC4S8C.cmF hF2 := by
    rw [hg]
    exact hu
  have hΦc : frattiniIn (c134Q G₀ L) ≤
      centerOf (c134Q G₀ L ⊓ Subgroup.centralizer (frattiniIn (c134Q G₀ L) : Set G)) := by
    intro f hf
    refine ⟨hQ₂.2.1 hf, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hv.2 f hf).symm
  exact le_antisymm
    (SzC4S8D.centerOf_le_of_abelian hF2 hQ₂ g hgN hΦc hΦW hWQ₂
      (fun x hx => (Subgroup.mem_normalizer_iff.mp (hLW g.2) x).mp hx) hWab hWc) hΦc

end CFSG.Quasithin.SzC4
