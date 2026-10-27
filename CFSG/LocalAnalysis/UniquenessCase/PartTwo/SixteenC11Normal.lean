module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11RouteF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NormLbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg10Defs
public import CFSG.ClassicalGroups.PCoreSection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c11_card_of_isElemAbelianOfRank {p n : ℕ} [Fact p.Prime] {X : Type*}
    [Group X] (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have h1 : Nat.card (Multiplicative (Fin n → ZMod p)) = Nat.card (Fin n → ZMod p) :=
    Nat.card_congr Multiplicative.toAdd
  rw [h1, Nat.card_fun]
  simp

private theorem s16c11_pow_of_isElemAbelianOfRank {p n : ℕ} {X : Type*} [Group X]
    (h : IsElemAbelianOfRank p n X) (x : X) : x ^ p = 1 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  ext i
  simp

theorem s16c11_normalizer_le_of_case3 (D : Data G) (h61 : UC6.R6_1 D) (h1610 : R16_10_2 D)
    (h169 : R16_9 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h3 : Case168_3 D V₀ V hV L) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hcard : Nat.card ↥(lBar V₀ V hV L) = 3 ^ 3 := h3.1.2.1
  have hp : 3 ∈ D.sig := by
    rw [h3.2.2]
    exact Set.mem_singleton 3
  have hPM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV hc.setting.hyp151.le
  have hPp : IsPGroup 3 ↥(lBar V₀ V hV L) := IsPGroup.of_card hcard
  have hPc : ¬ IsCyclic ↥(lBar V₀ V hV L) :=
    s16c11_not_isCyclic_of_exponent (by norm_num)
      (fun x hx => congrArg Subtype.val (h3.1.2.2 ⟨x, hx⟩))
      (by rw [hcard]; exact pow_dvd_pow 3 (by norm_num))
  exact s16c11_normalizer_le_of_routeF_normal D h61 h1610 h169 hV hc hp hPM hPp hPc
    (s16c1610_mbar_le_normalizer_lbar D hV hc h3)

theorem s16c11_normalizer_le_of_case4 (D : Data G) (h61 : UC6.R6_1 D) (h1610 : R16_10_2 D)
    (h169 : R16_9 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h4 : Case168_4 D V₀ V hV L) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  obtain ⟨p, r, hp37, hr, h4At⟩ := h4
  have hpp : p.Prime := by rcases hp37 with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hpp⟩
  have hL : lBar V₀ V hV L ≤ pCoreOf p (Mbar D.M V₀ V hV) :=
    s16n9b_case4_pcore D hV hc hpp hr h4At.1
  have hLexp : ∀ x ∈ lBar V₀ V hV L, x ^ p = 1 := fun x hx =>
    congrArg Subtype.val (s16c11_pow_of_isElemAbelianOfRank h4At.1 ⟨x, hx⟩)
  have hLcard : Nat.card ↥(lBar V₀ V hV L) = p ^ r := s16c11_card_of_isElemAbelianOfRank h4At.1
  have hLc : ¬ IsCyclic ↥(lBar V₀ V hV L) :=
    s16c11_not_isCyclic_of_exponent hpp hLexp
      (by rw [hLcard]; exact pow_dvd_pow p (by omega))
  have hPc : ¬ IsCyclic ↥(pCoreOf p (Mbar D.M V₀ V hV)) := by
    intro hcyc
    refine hLc ?_
    haveI : IsCyclic ↥((lBar V₀ V hV L).subgroupOf (pCoreOf p (Mbar D.M V₀ V hV))) :=
      Subgroup.isCyclic _
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hL).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hL).surjective
  refine s16c11_normalizer_le_of_routeF_normal D h61 h1610 h169 hV hc h4At.2.2
    (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le p _)
    (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf p _) hPc ?_
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hg hh
  · intro hh
    have h1 := CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf ((Mbar D.M V₀ V hV).inv_mem hg) hh
    simpa [mul_assoc] using h1

theorem s16c11_normalizer_le_of_case10 (D : Data G) (h61 : UC6.R6_1 D) (h1610 : R16_10_2 D)
    (h169 : R16_9 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h10 : Case168_10 D V₀ V hV L) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  obtain ⟨p, hp37, -, -, -, hsig, hE⟩ := h10
  have hpp : p.Prime := by rcases hp37 with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp : p ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton p
  have hF := s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)
  have hexp : ∀ x ∈ Fstar (Mbar D.M V₀ V hV), x ^ p = 1 := fun x hx =>
    congrArg Subtype.val (s16c11_pow_of_isElemAbelianOfRank hE ⟨x, hx⟩)
  have hcard : Nat.card ↥(Fstar (Mbar D.M V₀ V hV)) = p ^ 3 :=
    s16c11_card_of_isElemAbelianOfRank hE
  refine s16c11_normalizer_le_of_routeF_normal D h61 h1610 h169 hV hc hp hF.1
    (IsPGroup.of_card hcard)
    (s16c11_not_isCyclic_of_exponent hpp hexp (by rw [hcard]; exact pow_dvd_pow p (by norm_num)))
    ?_
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => hF.2.1 g hg h hh
  · intro hh
    have h1 := hF.2.1 g⁻¹ ((Mbar D.M V₀ V hV).inv_mem hg) _ hh
    simpa [mul_assoc] using h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
