module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeDefs
import Certificates
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf
import CFSG.LocalAnalysis.ComponentClassification.PerfectCentralQuotient
public import Certificates.Certificate1322030

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

private theorem charP_two_of_card_pow {F : Type} [Field F] [Finite F] {k : ℕ} (hk : 1 ≤ k)
    (h : Nat.card F = 2 ^ k) : CharP F 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  apply ringChar.of_eq
  rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, h]
  apply Nat.mod_eq_zero_of_dvd
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact ⟨2 ^ t, by rw [pow_succ]; ring⟩

private theorem eq_of_ggLabelIso_twA4 {lab labH : LargeEvenLabel}
    (hiso : GGLabelIso lab labH) (htag : labH.tag = .twA) (hrank : labH.rank = 4) :
    lab = labH := by
  simp only [GGLabelIso] at hiso
  rcases hiso with heq | hbc | h | h | h | h | h | h
  · exact heq
  · rcases hbc.2.1 with hb | hc
    · rw [htag] at hb; exact nomatch hb
    · rw [htag] at hc; exact nomatch hc
  · rw [h.2] at htag; exact nomatch htag
  · rw [h.2] at htag; exact nomatch htag
  · rw [h.2] at hrank; exact nomatch hrank
  · rw [h.2] at htag; exact nomatch htag
  · rw [h.2] at htag; exact nomatch htag
  · rw [h.1] at htag; exact nomatch htag

section U5OfRCerts

theorem u5_of_R
    (h : Uni5KG7OnR) : GGTablePThreeU5NoTwoGroupKnown := by
  unfold GGTablePThreeU5NoTwoGroupKnown
  unfold Uni5KG7OnR at h
  intro X _ _ hcomm A δ J hD hA27 hMarkH hMarkJ hJcenter
  obtain ⟨hKLocal, huniq, hA3, hMarkD⟩ := hD
  obtain ⟨-, labM, hlabM_in, hrawM₀⟩ := hMarkD
  have hrawM : CFSG.StandardType.LargeEvenRawDatum labM
      (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R,
          LargeEvenSplit 3 labM ∧ GGInducedInn A θ I) :=
    (CFSG.StandardType.largeEvenRawDatum_legacy labM _).mpr hrawM₀
  obtain ⟨-, labH, hlabH_in, hrawH₀⟩ := hMarkH
  have hrawH : CFSG.StandardType.LargeEvenRawDatum labH
      (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R,
          labH.tag = .twA ∧ labH.rank = 4 ∧ 3 ∣ 2 ^ labH.n + 1) :=
    (CFSG.StandardType.largeEvenRawDatum_legacy labH _).mpr hrawH₀
  obtain ⟨RH, hRH, IH, FH, hQH⟩ := CFSG.StandardType.largeEvenRawDatum_exists hrawH
  obtain ⟨-, -, hθH⟩ := hQH
  obtain ⟨-, htagH, hrankH, hsplitH⟩ := hθH
  have hGGM : CFSG.StandardType.GGHasLabel labM (X ⧸ Subgroup.center X) :=
    CFSG.StandardType.largeEvenRawDatum_mono (fun R _ _ _ hQ => ⟨hQ.2.2.choose⟩) hrawM
  have hGGH : CFSG.StandardType.GGHasLabel labH (X ⧸ Subgroup.center X) :=
    CFSG.StandardType.largeEvenRawDatum_mono (fun R _ _ _ hQ => ⟨hQ.2.2.choose⟩) hrawH
  have hiso : CFSG.StandardType.GGLabelIso labM labH :=
    CFSG.StandardType.ggLabelRigidInput_holds labM labH (X ⧸ Subgroup.center X)
      hlabM_in hlabH_in hGGM hGGH
  have hlabM_eq : labM = labH := eq_of_ggLabelIso_twA4 hiso htagH hrankH
  subst labM
  obtain ⟨tagH, rankH, nH⟩ := labH
  subst htagH
  subst hrankH
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hrawM
  obtain ⟨K, hfieldK, hfiniteK, hcardK, hQK⟩ := hrawM
  letI : Field K := hfieldK
  letI : Finite K := hfiniteK
  obtain ⟨hsimpleK, hnaK, hθK⟩ := hQK
  obtain ⟨θM, hsplitM, hGGInducedInnM⟩ := hθK
  have hq3 : 3 ∣ 2 ^ nH + 1 := hsplitH
  have hnH : 1 ≤ nH := hlabH_in.1
  have hcardK2 : Nat.card K = 2 ^ (2 * nH) := by
    rw [hcardK, ← pow_mul, Nat.mul_comm]
  haveI : CharP K 2 := charP_two_of_card_pow (by omega) hcardK2
  have hleaf := leafR_holds X hcomm
    (LargeEvenProj (LargeEvenSUGroup (Fin 5) K (2 ^ nH))) θM A δ J hKLocal huniq hA3
  obtain ⟨Ā, δ', J', hRdat, hcardĀ, hδ'eq, hAmap, hJ'eq, hcenter⟩ := hleaf
  have hcardĀ' : Nat.card Ā = 3 ^ 3 := by rw [hcardĀ, hA27]
  have hinj : Function.Injective (ggInducedAut θM) :=
    ggInducedAut_injective_of_perfect hcomm θM
  have hsubmap : A.map (ggInducedAut θM) ≤ Ā := by
    rintro a ⟨a₀, ha₀, rfl⟩
    exact hAmap a₀ ha₀
  have hcardmap : Nat.card (A.map (ggInducedAut θM)) = Nat.card A :=
    Subgroup.card_map_of_injective hinj
  have hAeq : A.map (ggInducedAut θM) = Ā :=
    Subgroup.eq_of_le_of_card_ge hsubmap (by rw [hcardmap, hcardĀ])
  have hĀI : ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K (2 ^ nH)))
      (LargeEvenGUSet (Fin 5) K (2 ^ nH)) := by
    intro a ha
    rw [← hAeq] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    exact hGGInducedInnM a₀ ha₀
  obtain ⟨hJcomm, labJ, hlabJ_in, hrawJ₀⟩ := hMarkJ
  have hrawJ : CFSG.StandardType.LargeEvenRawDatum labJ
      (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : J ⧸ Subgroup.center J ≃* R,
          GGLabelA2 labJ ∧ labJ.tag = .twA) :=
    (CFSG.StandardType.largeEvenRawDatum_legacy labJ _).mpr hrawJ₀
  obtain ⟨RJ, hRJ, IJ, FJ, hQJ₀⟩ := CFSG.StandardType.largeEvenRawDatum_exists hrawJ
  obtain ⟨-, -, hθJ₀⟩ := hQJ₀
  obtain ⟨θJ₀, hA2J, htagJ⟩ := hθJ₀
  obtain ⟨tagJ, rankJ, nJ⟩ := labJ
  dsimp only [GGLabelA2] at hA2J
  have hrankJ : rankJ = 2 := hA2J.1
  subst htagJ
  subst hrankJ
  have hnJ : 2 ≤ nJ := hlabJ_in.2.2 rfl
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hrawJ
  obtain ⟨KJ, hfieldKJ, hfiniteKJ, hcardKJ, hQJ⟩ := hrawJ
  letI : Field KJ := hfieldKJ
  letI : Finite KJ := hfiniteKJ
  obtain ⟨-, -, hθJ⟩ := hQJ
  obtain ⟨θJ, -, -⟩ := hθJ
  have h4J : 4 ≤ 2 ^ nJ := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ nJ := Nat.pow_le_pow_right (by norm_num) hnJ
  let f : J →* J' :=
    { toFun := fun x => ⟨proj θM (x : X), by
        rw [hJ'eq]; exact Subgroup.mem_map_of_mem (proj θM) x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hf_surj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [hJ'eq] at hy
    obtain ⟨x, hxJ, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hxJ⟩, Subtype.ext hxy⟩
  have hker_le : f.ker ≤ Subgroup.center J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : proj θM (x : X) = 1 := congrArg Subtype.val hx
    have hkerproj : (proj θM).ker = Subgroup.center X := by
      unfold proj
      rw [MonoidHom.ker_comp_of_injective _ _ (EquivLike.injective θM), QuotientGroup.ker_mk']
    have hxcenter : (x : X) ∈ Subgroup.center X := by
      rw [← hkerproj]; exact MonoidHom.mem_ker.mpr hx1
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxcenter (g : X))
  haveI : Group.IsPerfect J := ⟨hJcomm⟩
  let eJ : J ⧸ Subgroup.center J ≃* J' ⧸ Subgroup.center J' :=
    CFSG.ComponentClassification.PerfectCentralQuotient.equivalence f hf_surj hker_le
  have hisoJ : Nonempty (J' ⧸ Subgroup.center J' ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 3) KJ (2 ^ nJ))) :=
    ⟨eJ.symm.trans θJ⟩
  rintro ⟨U, hUne, hU2, hUnorm⟩
  have hŪne : U.map (ggInducedAut θM) ≠ ⊥ := by
    intro hbot
    apply hUne
    rw [eq_bot_iff]
    intro u hu
    have hmem : ggInducedAut θM u ∈ U.map (ggInducedAut θM) := Subgroup.mem_map_of_mem _ hu
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (hinj (hmem.trans (map_one _).symm))
  have hŪ2 : IsPGroup 2 (U.map (ggInducedAut θM)) := by
    haveI : IsPGroup 2 U := hU2
    exact IsPGroup.of_equiv hU2 (Subgroup.equivMapOfInjective U (ggInducedAut θM) hinj)
  have hŪnorm : ∀ a ∈ Ā, ∀ u ∈ U.map (ggInducedAut θM),
      a * u * a⁻¹ ∈ U.map (ggInducedAut θM) := by
    intro a ha u hu
    rw [← hAeq] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
    have hmul : ggInducedAut θM a₀ * ggInducedAut θM u₀ * (ggInducedAut θM a₀)⁻¹ =
        ggInducedAut θM (a₀ * u₀ * a₀⁻¹) := by
      simp only [map_mul, map_inv]
    rw [hmul]
    exact Subgroup.mem_map_of_mem _ (hUnorm a₀ ha₀ u₀ hu₀)
  exact h K (2 ^ nH) hcardK hq3 Ā δ' J' hRdat hcardĀ' hĀI
    ⟨KJ, hfieldKJ, hfiniteKJ, 2 ^ nJ, hcardKJ, h4J, hisoJ⟩
    ⟨U.map (ggInducedAut θM), hŪne, hŪ2, hŪnorm⟩

end U5OfRCerts

end CFSG.StandardType.TablePThreeKG

end
