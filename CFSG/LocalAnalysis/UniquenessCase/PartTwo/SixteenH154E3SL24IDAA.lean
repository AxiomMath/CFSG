module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Rows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24CoverCA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24IDAAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24IDAAB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24IDAB
public import CFSG.Milestones.ASVolI.I2Natural
public import CFSG.Quasithin.H13.VolII16Restrict

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.GH74.KGroups Subgroup CFSG.ASVolI CFSG.ASVolI.ChIJK

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl24_sec_gf4 (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hU : ∀ l ∈ L, ∀ u ∈ commSub ⊤ L, l u ∈ commSub ⊤ L) :
    ∃ (π : ↥(StatedSL 2 GF4) →* ↥L)
      (β : ↥(commSub ⊤ L) →* ↥(i23NaturalModel 1 GF4).sec ⧸
        (i23NaturalModel 1 GF4).ker.subgroupOf (i23NaturalModel 1 GF4).sec),
      Function.Surjective π ∧
      I23SectionMap (i23NaturalModel 1 GF4)
        ((CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).range)
        ((commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L))
        ((CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).rangeRestrict.comp π) β := by
  obtain ⟨K, hKf, hKfin, hKcard, π₀, β₀, hπ₀, hβ₀s, hβ₀k, hβ₀e⟩ :=
    s16h_sl24_cover_coord (L := L) (U := commSub ⊤ L)
      (Z := commSub ⊤ L ⊓ fixV L) hrow
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = Fintype.card GF4 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKcard,
      Nat.card_eq_fintype_card]
    decide
  let ρ : K ≃+* GF4 := FiniteField.ringEquivOfCardEq hcardK
  have hβ₀k' : β₀.ker = (commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβ₀k u
  obtain ⟨π, β, hπ, hβs, hβk, hβe⟩ :=
    s16h_sl24_transport_coord (W := W) ρ hπ₀ hβ₀s hβ₀k' hβ₀e
  obtain ⟨β', _, hsec⟩ :=
    s16h_sl24_i23SectionMap_of_coord (K := GF4) hU hπ hβs hβk hβe
  exact ⟨π, β', hπ, hsec⟩

theorem s16h_sl24_cover_plumb (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hU : ∀ l ∈ L, ∀ u ∈ commSub ⊤ L, l u ∈ commSub ⊤ L)
    (huniv : IsUniversalCovering
      (CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).range
      ((commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L))) :
    ∃ (ψ : ↥(commSub ⊤ L) ≃* Multiplicative ((Fin 2 → GF4) × GF4))
      (π : ↥(StatedSL 2 GF4) →* ↥L)
      (A : ↥(StatedSL 2 GF4) →* ((Fin 2 → GF4) ≃ₗ[GF4] (Fin 2 → GF4)))
      (hA : ∀ γ, (burnsideI23x_sd1 GF4).Symp (A γ)),
      Function.Surjective π ∧
      (∀ γ x, A γ x = (burnsideI23x_LM1 GF4).lin γ x) ∧
      (∀ (γ : ↥(StatedSL 2 GF4)) (u : W) (hu : u ∈ commSub ⊤ L)
        (hu' : (π γ : MulAut W) u ∈ commSub ⊤ L),
        ψ ⟨(π γ : MulAut W) u, hu'⟩ =
          (burnsideI23x_sd1 GF4).liftHom A hA γ (ψ ⟨u, hu⟩)) ∧
      (∀ u : ↥(commSub ⊤ L), (Multiplicative.toAdd (ψ u)).1 = 0 ↔ (u : W) ∈ fixV L) := by
  obtain ⟨π, β, hπ, hsec⟩ := s16h_sl24_sec_gf4 hW hrow hU
  have hβk : β.ker = (commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L) := hsec.2.2.1
  have hU2 : ∀ u : ↥(commSub ⊤ L), u ^ 2 = 1 :=
    CFSG.Quasithin.H13.VolI.sq_eq_one_of_subgroup (U := commSub ⊤ L) hW
  have hF : Nat.card GF4 = 2 ^ 2 := by rw [Nat.card_eq_fintype_card]; decide
  obtain ⟨a, ha0, ha1⟩ := burnsideI23x_exists_ne_zero_one hF (by norm_num : 2 ≤ 2)
  have htv' : ∀ (e : Fin 2 → GF4) (c : GF4), e ≠ 0 → ∃ γ : ↥(StatedSL 2 GF4), ∀ x,
      (burnsideI23x_LM1 GF4).lin γ x = (burnsideI23x_sd1 GF4).tvEquiv e c x :=
    fun e c _ => burnsideI23x_htv1 GF4 e c
  have hgenM : (burnsideI23x_sd1 GF4).GenW' (burnsideI23x_LM1 GF4).lin :=
    burnsideI23x_SD.genW'_of_tv (burnsideI23x_sd1 GF4) (burnsideI23x_LM1 GF4).lin htv' ha0 ha1
  obtain ⟨A, hA, ψ, hAlin, -, -, -, hψact, hψfst⟩ :=
    burnsideI23x_plumb (burnsideI23x_LM1 GF4) (burnsideI23x_sd1 GF4)
      (burnsideI23x_hsymp1 GF4) (burnsideI23x_hfaith1 GF4) hgenM
      (burnsideI23x_hbound1 (n := 2) (by norm_num) hF) hU2 huniv hsec
  refine ⟨ψ, π, A, hA, hπ, hAlin, ?_, ?_⟩
  · intro γ u hu hu'
    have hmark : (((CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).rangeRestrict.comp π) γ
        : MulAut ↥(commSub ⊤ L)) ⟨u, hu⟩ = ⟨(π γ : MulAut W) u, hu'⟩ := Subtype.ext rfl
    rw [← hmark]
    exact hψact γ ⟨u, hu⟩
  · intro u
    rw [hψfst u, toAdd_eq_zero, (burnsideI23x_LM1 GF4).e.map_eq_one_iff,
      ← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
