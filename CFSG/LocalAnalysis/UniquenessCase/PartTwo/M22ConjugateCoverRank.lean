module

public import CFSG.GroupTheory.ComponentImageUniqueness
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.M22ComponentCoverFacts
public import CFSG.Quasithin.Background.HM22Out
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.Quasithin.EmptyFaithful.R3cBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem barImage_inf_eq_bot_and_four_le_pRank_three_of_m22_outer_centralizer
    {M K1 K2 : Subgroup G} (hK1 : K1 ∈ calC M) (hK2 : K2 ∈ calC M)
    {Y : Type} [Group Y] (ψ : Bar2 M →* Y) {H1 H2 : Subgroup Y}
    (himage1 : (barImage M K1).map ψ = H1)
    (himage2 : (barImage M K2).map ψ = H2)
    (hM1 : IsSpor H1 .M22) (hM2 : IsSpor H2 .M22) (hne : H1 ≠ H2)
    (x : Bar2 M)
    (hxN : ψ x ∈ Subgroup.normalizer (H1 : Set Y))
    (hxOuter : ¬ ∃ h0 ∈ H1, ∀ h ∈ H1,
      ψ x * h * (ψ x)⁻¹ = h0 * h * h0⁻¹)
    (hxC : ψ x ∈ Subgroup.centralizer (H2 : Set Y)) :
    barImage M K1 ⊓ barImage M K2 = ⊥ ∧ 4 ≤ CFSG.Open.pRank 3 M := by
  classical
  let C1 : Subgroup (Bar2 M) := barImage M K1
  let C2 : Subgroup (Bar2 M) := barImage M K2
  have hC1 : CFSG.IsComponent C1 := uc22p22l_barImage_isComponent hK1
  have hC2 : CFSG.IsComponent C2 := uc22p22l_barImage_isComponent hK2
  have hM22simple : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    CFSG.Quasithin.KGC31.KG443.isSimpleGroup_m22
  have hsimple1 : IsSimpleGroup ↥H1 := by
    obtain ⟨e⟩ := hM1
    exact e.isSimpleGroup_congr.mpr hM22simple
  have hsimple2 : IsSimpleGroup ↥H2 := by
    obtain ⟨e⟩ := hM2
    exact e.isSimpleGroup_congr.mpr hM22simple
  have hna1 : ∃ a ∈ C1.map ψ, ∃ b ∈ C1.map ψ, a * b ≠ b * a :=
    CFSG.ComponentImage.exists_noncommuting_map_of_isSimpleGroup ψ hC1 himage1 hsimple1
  have hna2 : ∃ a ∈ C2.map ψ, ∃ b ∈ C2.map ψ, a * b ≠ b * a :=
    CFSG.ComponentImage.exists_noncommuting_map_of_isSimpleGroup ψ hC2 himage2 hsimple2
  have hxC1N : x ∈ Subgroup.normalizer (C1 : Set (Bar2 M)) := by
    apply CFSG.ComponentImage.mem_normalizer_of_map_mem_normalizer ψ hC1 hna1
    rwa [himage1]
  have hxC2C : x ∈ Subgroup.centralizer (C2 : Set (Bar2 M)) := by
    apply CFSG.ComponentImage.mem_centralizer_of_map_mem_centralizer ψ hC2 hna2
    rwa [himage2]
  let α : MulAut ↥C1 := C1.normalizerMonoidHom ⟨x, hxC1N⟩
  have hαouter : ∀ c0 : ↥C1, α ≠ MulAut.conj c0 := by
    intro c0 hα
    apply hxOuter
    refine ⟨ψ (c0 : Bar2 M), ?_, ?_⟩
    · rw [← himage1]
      exact Subgroup.mem_map_of_mem ψ c0.2
    · intro h hh
      have hh' : (h : Y) ∈ C1.map ψ := by
        rwa [himage1]
      obtain ⟨c, hc, hψc⟩ := Subgroup.mem_map.1 hh'
      have hαc : ((α ⟨c, hc⟩ : ↥C1) : Bar2 M) = x * c * x⁻¹ :=
        Subgroup.normalizerMonoidHom_apply_apply_coe C1 ⟨x, hxC1N⟩ ⟨c, hc⟩
      have hconj : ((α ⟨c, hc⟩ : ↥C1) : Bar2 M) =
          ((c0 * ⟨c, hc⟩ * c0⁻¹ : ↥C1) : Bar2 M) := by
        rw [hα, MulAut.conj_apply]
      have hψeq : ψ (((α ⟨c, hc⟩ : ↥C1) : Bar2 M)) =
          ψ (((c0 * ⟨c, hc⟩ * c0⁻¹ : ↥C1) : Bar2 M)) :=
        congrArg ψ hconj
      rw [hαc] at hψeq
      have hψeq' : ψ x * ψ c * (ψ x)⁻¹ =
          ψ (c0 : Bar2 M) * ψ c * (ψ (c0 : Bar2 M))⁻¹ := by
        simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
          Subtype.coe_mk] using hψeq
      rw [hψc] at hψeq'
      exact hψeq'
  have hCne : C1 ≠ C2 := by
    intro hC
    apply hne
    calc
      H1 = C1.map ψ := himage1.symm
      _ = C2.map ψ := by rw [hC]
      _ = H2 := himage2
  have hcomm : C1 ≤ Subgroup.centralizer (C2 : Set (Bar2 M)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hC1 hC2).resolve_left hCne)
  have hcommute : ∀ a ∈ C1, ∀ b ∈ C2, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hcomm ha) b hb).symm
  obtain ⟨hcenter1, E1, hE1le, hE1ea, hE1card⟩ :=
    barImage_m22_center_card_and_exists_e9 hK1 himage1 hM1
  obtain ⟨hcenter2, E2, hE2le, hE2ea, hE2card⟩ :=
    barImage_m22_center_card_and_exists_e9 hK2 himage2 hM2
  have hinf : C1 ⊓ C2 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hzc : (⟨z, hz.1⟩ : ↥C1) ∈ Subgroup.center ↥C1 := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcommute y y.2 z hz.2)
    rcases hcenter1 with hZ1 | hZ1
    · have hZbot : Subgroup.center ↥C1 = ⊥ :=
        Subgroup.eq_bot_of_card_eq (H := Subgroup.center ↥C1) hZ1
      have hmem : (⟨z, hz.1⟩ : ↥C1) ∈ (⊥ : Subgroup ↥C1) := by
        rw [← hZbot]
        exact hzc
      exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem)
    ·
      have hq1 : CFSG.Open.IsQuasisimple ↥C1 :=
        ⟨hC1.1.1.commutator_eq_top, hC1.1.2.1⟩
      have hSpor1 : IsSpor (↥C1 ⧸ Subgroup.center ↥C1) .M22 := by
        let ρ1 : ↥C1 →* ↥H1 :=
          (ψ.comp C1.subtype).codRestrict H1 (fun c => by
            have hc : ψ (c : Bar2 M) ∈ C1.map ψ := Subgroup.mem_map_of_mem ψ c.2
            rwa [himage1] at hc)
        have hρ1ker : ρ1.ker = Subgroup.center ↥C1 := by
          calc
            ρ1.ker = (ψ.comp C1.subtype).ker := MonoidHom.ker_codRestrict _ _ _
            _ = Subgroup.center ↥C1 :=
              CFSG.ComponentImage.ker_comp_subtype_eq_center ψ hC1 himage1 hsimple1
        have hρ1surj : Function.Surjective ρ1 := by
          intro h
          have hh : (h : Y) ∈ C1.map ψ := by
            rw [himage1]
            exact h.2
          obtain ⟨c, hc, hψc⟩ := Subgroup.mem_map.1 hh
          exact ⟨⟨c, hc⟩, Subtype.ext (by
            change ψ (c : Bar2 M) = (h : Y)
            exact hψc)⟩
        obtain ⟨eH1⟩ := hM1
        exact ⟨(QuotientGroup.quotientMulEquivOfEq hρ1ker.symm).trans
          ((QuotientGroup.quotientKerEquivOfSurjective ρ1 hρ1surj).trans eH1)⟩
      have hαinv : α ⟨z, hz.1⟩ = (⟨z, hz.1⟩ : ↥C1)⁻¹ :=
        CFSG.Quasithin.H.Mathieu.M22Link.kg82HatM22Out_holds
          (↥C1) hq1 hZ1 hSpor1 α hαouter ⟨z, hz.1⟩ hzc
      have hxcomm : (z : Bar2 M) * x = x * (z : Bar2 M) :=
        Subgroup.mem_centralizer_iff.mp hxC2C (z : Bar2 M) hz.2
      have hfix : α ⟨z, hz.1⟩ = ⟨z, hz.1⟩ := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        show x * (z : Bar2 M) * x⁻¹ = z
        rw [← hxcomm]
        group
      have hz2 : (⟨z, hz.1⟩ : ↥C1) ^ 2 = 1 := by
        have h : (⟨z, hz.1⟩ : ↥C1) = (⟨z, hz.1⟩ : ↥C1)⁻¹ := hfix.symm.trans hαinv
        rw [pow_two]
        nth_rewrite 2 [h]
        exact mul_inv_cancel _
      have hz3 : (⟨z, hz.1⟩ : ↥C1) ^ 3 = 1 := by
        have h := (pow_card_eq_one' :
          (⟨⟨z, hz.1⟩, hzc⟩ : ↥(Subgroup.center ↥C1)) ^
            Nat.card ↥(Subgroup.center ↥C1) = 1)
        rw [hZ1] at h
        exact congrArg Subtype.val h
      have hz1 : (⟨z, hz.1⟩ : ↥C1) = 1 := by
        calc
          (⟨z, hz.1⟩ : ↥C1) =
              (⟨z, hz.1⟩ : ↥C1) ^ 3 * ((⟨z, hz.1⟩ : ↥C1) ^ 2)⁻¹ := by group
          _ = 1 := by rw [hz3, hz2, inv_one, mul_one]
      exact Subtype.ext_iff.mp hz1
  have hrank1 : 2 ≤ CFSG.Open.pRank 3 C1 := by
    apply CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hE1le hE1ea
    rw [hE1card]
    norm_num
  have hrank2 : 2 ≤ CFSG.Open.pRank 3 C2 := by
    apply CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hE2le hE2ea
    rw [hE2card]
    norm_num
  have hcop : Nat.Coprime 3 (Nat.card (C1 ⊓ C2 : Subgroup (Bar2 M))) := by
    rw [hinf]
    simp
  have hadd := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime
    (q := 3) Nat.prime_three hcommute hcop
  have h4sup : 4 ≤ CFSG.Open.pRank 3 (C1 ⊔ C2) := by omega
  refine ⟨hinf, ?_⟩
  have htop : CFSG.Open.pRank 3 (C1 ⊔ C2) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 M)) :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top
  rw [CFSG.Quasithin.R3c.pRank_three_eq_pCore_quotient M]
  exact h4sup.trans htop

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
