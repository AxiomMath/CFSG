module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11RouteF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg10Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s1611e3_card_of_isElemAbelianOfRank {p n : ℕ} [Fact p.Prime] {X : Type*}
    [Group X] (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have h1 : Nat.card (Multiplicative (Fin n → ZMod p)) = Nat.card (Fin n → ZMod p) :=
    Nat.card_congr Multiplicative.toAdd
  rw [h1, Nat.card_fun]
  simp

private theorem s1611e3_pow_of_isElemAbelianOfRank {p n : ℕ} {X : Type*} [Group X]
    (h : IsElemAbelianOfRank p n X) (x : X) : x ^ p = 1 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  ext i
  simp

theorem s1611e3_normalizer_le_of_case8 (D : Data G) (h61 : UC6.R6_1 D) (h1610 : R16_10_2 D)
    (h169 : R16_9 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h8 : Case168_8 D V₀ V hV) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp : 3 ∈ D.sig := by
    rw [h8.2.2]
    exact Set.mem_singleton 3
  have hF := s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)
  have hexp : ∀ x ∈ Fstar (Mbar D.M V₀ V hV), x ^ 3 = 1 := fun x hx =>
    congrArg Subtype.val (s1611e3_pow_of_isElemAbelianOfRank h8.1 ⟨x, hx⟩)
  have hcard : Nat.card ↥(Fstar (Mbar D.M V₀ V hV)) = 3 ^ 2 :=
    s1611e3_card_of_isElemAbelianOfRank h8.1
  have hdvd : 3 ^ 2 ∣ Nat.card ↥(Fstar (Mbar D.M V₀ V hV)) := by
    simpa [hcard] using pow_dvd_pow 3 (le_refl 2)
  refine s16c11_normalizer_le_of_routeF_normal D h61 h1610 h169 hV hc hp hF.1
    (IsPGroup.of_card hcard)
    (s16c11_not_isCyclic_of_exponent (by norm_num) hexp hdvd) ?_
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => hF.2.1 g hg h hh
  · intro hh
    have h1 := hF.2.1 g⁻¹ ((Mbar D.M V₀ V hV).inv_mem hg) _ hh
    simpa [mul_assoc] using h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
