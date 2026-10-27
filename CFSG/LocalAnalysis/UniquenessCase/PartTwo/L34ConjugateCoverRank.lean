module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.L34ComponentCoverFacts
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.Quasithin.EmptyFaithful.R3cBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem barImage_inf_eq_bot_and_four_le_pRank_three_of_l34_field_centralizer
    {M K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ calC M) (hK₂ : K₂ ∈ calC M)
    {Y : Type} [Group Y] (ψ : Bar2 M →* Y) {H₁ H₂ : Subgroup Y}
    (himage₁ : (UC22.barImage M K₁).map ψ = H₁)
    (himage₂ : (UC22.barImage M K₂).map ψ = H₂)
    (hL₁ : IsLn ↥H₁ 3 2) (hL₂ : IsLn ↥H₂ 3 2) (hne : H₁ ≠ H₂)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (π : Matrix.SpecialLinearGroup (Fin 3) F →* ↥H₁)
    (hπ : Function.Surjective π)
    (hπker : π.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F))
    (A : Matrix.GeneralLinearGroup (Fin 3) F) (x : Bar2 M)
    (hxN : ψ x ∈ Subgroup.normalizer (H₁ : Set Y))
    (hfield : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F,
      ψ x * (π g : Y) * (ψ x)⁻¹ =
        (π (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
          3 F A (Matrix.SpecialLinearGroup.map
            (CFSG.Quasithin.H.SU3.bar 1 : F ≃+* F).toRingHom g)) : Y))
    (hxC₂ : ψ x ∈ Subgroup.centralizer (H₂ : Set Y)) :
    UC22.barImage M K₁ ⊓ UC22.barImage M K₂ = ⊥ ∧ 4 ≤ CFSG.Open.pRank 3 M := by
  classical
  let C₁ : Subgroup (Bar2 M) := UC22.barImage M K₁
  let C₂ : Subgroup (Bar2 M) := UC22.barImage M K₂
  have hC₁ : CFSG.IsComponent C₁ := UC22.uc22p22l_barImage_isComponent hK₁
  have hC₂ : CFSG.IsComponent C₂ := UC22.uc22p22l_barImage_isComponent hK₂
  have hneC : C₁ ≠ C₂ := by
    intro h
    apply hne
    have hmap := congrArg (fun D : Subgroup (Bar2 M) => D.map ψ) h
    simpa only [C₁, C₂, himage₁, himage₂] using hmap
  have hsimple₂ : IsSimpleGroup ↥H₂ :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL₂
  have hna₂ : ∃ a ∈ C₂.map ψ, ∃ b ∈ C₂.map ψ, a * b ≠ b * a :=
    CFSG.ComponentImage.exists_noncommuting_map_of_isSimpleGroup ψ hC₂ himage₂ hsimple₂
  have hxNormal₂ : ψ x ∈ Subgroup.centralizer (C₂.map ψ : Set Y) := by
    rwa [himage₂]
  have hxC₂' : x ∈ Subgroup.centralizer (C₂ : Set (Bar2 M)) :=
    CFSG.ComponentImage.mem_centralizer_of_map_mem_centralizer ψ hC₂ hna₂ hxNormal₂
  have hcomm : C₁ ≤ Subgroup.centralizer (C₂ : Set (Bar2 M)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hC₁ hC₂).resolve_left hneC)
  have hcommute : ∀ a ∈ C₁, ∀ b ∈ C₂, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hcomm ha) b hb).symm
  obtain ⟨hcard₁, E₁, hE₁le, hE₁ab, hE₁card⟩ :=
    barImage_l34_center_card_and_exists_e9 hK₁ ψ himage₁ hL₁
  obtain ⟨_, E₂, hE₂le, hE₂ab, hE₂card⟩ :=
    barImage_l34_center_card_and_exists_e9 hK₂ ψ himage₂ hL₂
  have hinv : ∀ z : ↥C₁, z ∈ Subgroup.center C₁ →
      x * (z : Bar2 M) * x⁻¹ = (z : Bar2 M)⁻¹ :=
    barImage_l34_center_inverted_of_field_action hK₁ ψ himage₁ hL₁ hF π hπ hπker A x hxN hfield
  have hodd₁ : Odd (Nat.card (Subgroup.center C₁)) := by
    rcases hcard₁ with h | h <;> rw [h] <;> norm_num
  have hinf : C₁ ⊓ C₂ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyC₁ : y ∈ C₁ := hy.1
    have hyC₂ : y ∈ C₂ := hy.2
    have hyZ : (⟨y, hyC₁⟩ : C₁) ∈ Subgroup.center C₁ := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      exact hcommute c c.2 y hyC₂
    have hfix : x * (y : Bar2 M) * x⁻¹ = y := by
      have h := Subgroup.mem_centralizer_iff.mp hxC₂' y hyC₂
      rw [← h]
      group
    have hyinv : x * (y : Bar2 M) * x⁻¹ = (y : Bar2 M)⁻¹ := hinv ⟨y, hyC₁⟩ hyZ
    have hy_eq_inv : (y : Bar2 M) = (y : Bar2 M)⁻¹ := by
      calc (y : Bar2 M) = x * (y : Bar2 M) * x⁻¹ := hfix.symm
        _ = (y : Bar2 M)⁻¹ := hyinv
    have hy_sq : (y : Bar2 M) * (y : Bar2 M) = 1 := by
      have h := congrArg (fun t : Bar2 M => t * (y : Bar2 M)) hy_eq_inv
      simpa using h
    have hy2 : orderOf (y : Bar2 M) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    have hy2' : orderOf (⟨y, hyC₁⟩ : C₁) ∣ 2 := by
      rw [show orderOf (⟨y, hyC₁⟩ : C₁) = orderOf (y : Bar2 M) from
        (Subgroup.orderOf_coe (⟨y, hyC₁⟩ : C₁)).symm]
      exact hy2
    have hy3 : orderOf (⟨y, hyC₁⟩ : C₁) ∣ Nat.card (Subgroup.center C₁) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center C₁) hyZ
    have hcop : Nat.Coprime 2 (Nat.card (Subgroup.center C₁)) :=
      Nat.coprime_two_left.mpr hodd₁
    have hy1 : (⟨y, hyC₁⟩ : C₁) = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hy2' hy3)
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hy1
  refine ⟨hinf, ?_⟩
  have hC₁rank : 2 ≤ CFSG.Open.pRank 3 C₁ :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hE₁le hE₁ab
      (by rw [hE₁card]; norm_num)
  have hC₂rank : 2 ≤ CFSG.Open.pRank 3 C₂ :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hE₂le hE₂ab
      (by rw [hE₂card]; norm_num)
  have hcop : Nat.Coprime 3 (Nat.card (C₁ ⊓ C₂ : Subgroup (Bar2 M))) := by
    rw [hinf]
    simp
  have hadd := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime
    (q := 3) Nat.prime_three hcommute hcop
  have h4sup : 4 ≤ CFSG.Open.pRank 3 (C₁ ⊔ C₂) := by omega
  have htop : CFSG.Open.pRank 3 (C₁ ⊔ C₂) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 M)) :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top
  rw [CFSG.Quasithin.R3c.pRank_three_eq_pCore_quotient M]
  exact h4sup.trans htop

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
