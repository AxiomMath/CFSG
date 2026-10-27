module

public import CFSG.RankThree.PartTwo.Sec19.F194Item316Leaves
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.EightTenI.AltTypeOdd
public import CFSG.Adapters.RankThreeOutcomesReverse
import CFSG.Adapters.ClassicalCatalogReverse

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartOne CFSG.CGT.PushingUp

theorem two_pow_ne_two_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    ((2 : ℕ), (2 : ℕ) ^ k) ≠ ((2 : ℕ), (2 : ℕ)) := by
  intro h
  have h2 : (2 : ℕ) ^ k = 2 := congrArg Prod.snd h
  have h4 : (2 : ℕ) ^ 2 ≤ (2 : ℕ) ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [h2] at h4
  norm_num at h4

theorem inCatalog_of_mulEquiv_projSL_three {G : Type} [Group G]
    {k : ℕ} (hk : 2 ≤ k) (e : G ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 k)) :
    CFSG.Assembly.InCatalog G := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 3 2 k :=
    ⟨Nat.prime_two, by omega, by norm_num, by simp, by simp⟩
  exact CFSG.ClassicalModels.inCatalog_of_statedClassicalModel G .PSL 3 2 k
    (CFSG.Assembly.RankThreeEven.statedClassicalModel_of_projSL hadm e)

theorem inCatalog_of_mulEquiv_projSp_two {G : Type} [Group G]
    {k : ℕ} (hk : 2 ≤ k) (e : G ≃* CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 2 k)) :
    CFSG.Assembly.InCatalog G := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSp 2 2 k :=
    ⟨Nat.prime_two, by omega, by norm_num, two_pow_ne_two_of_two_le hk⟩
  exact CFSG.ClassicalModels.inCatalog_of_statedClassicalModel G .PSp 2 2 k
    (CFSG.Assembly.RankThreeEven.statedClassicalModel_of_projSp hadm e)

section Transport

variable {G : Type} [Group G] [Finite G]

theorem isShortGroup_of_isShort {L : Subgroup G} (hL : IsShort L) :
    CFSG.RankThree.PartOne.IsShortGroup ↥L := by
  obtain ⟨hres, hfit, hUQ, htype, hlt, hirr⟩ := hL
  have hQ := CFSG.AGLEmbedding.NoXBlock.blockQ_eq_map L
  have hU := CFSG.AGLEmbedding.NoXBlock.map_shortU_eq_blockU L
  have hC := CFSG.AGLEmbedding.NoXBlock.map_shortC_eq_blockZ L
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hfit
  · refine CGT.PushingUpLit.oResidualTwo_eq_top_iff.2 fun N hN hpow => ?_
    exact hres N ((CGT.PushingUpLit.isPGroup_two_quotient_iff N).2 hpow)
  · exact htype
  · refine CGT.PushingUpLit.shortU_le_center_iff.2 fun u hu => ?_
    have hu' : (u : G) ∈ QuasithinUnique.blockU L := by
      rw [← hU]; exact Subgroup.mem_map_of_mem _ hu
    have hu2 := hUQ hu'
    have hmem : (u : G) ∈ (CFSG.pCore 2 ↥L).map L.subtype := by
      rw [← hQ]; exact hu2.1
    obtain ⟨u0, hu0, hu0e⟩ := hmem
    refine ⟨by rwa [← Subtype.ext hu0e], fun r hr => Subtype.ext ?_⟩
    have hr' : (r : G) ∈ blockQ L := by
      rw [hQ]; exact Subgroup.mem_map_of_mem _ hr
    exact (Subgroup.mem_centralizer_iff.mp hu2.2 r hr').symm
  · rw [← Subgroup.map_lt_map_iff_of_injective L.subtype_injective, hU, hC]
    exact hlt
  · intro N hN hNU hCN
    have hNU' : N.map L.subtype ≤ QuasithinUnique.blockU L := by
      rw [← hU]; exact Subgroup.map_mono hNU
    have hCN' : QuasithinUnique.blockZ L ≤ N.map L.subtype := by
      rw [← hC]; exact Subgroup.map_mono hCN
    have hLN : L ≤ Subgroup.normalizer (N.map L.subtype : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨k, hk⟩ * n * ⟨k, hk⟩⁻¹, hN.conj_mem n hn _, rfl⟩
      · rintro ⟨n, hn, hne⟩
        have hx : x ∈ L := by
          have h1 : k * x * k⁻¹ ∈ L := hne ▸ n.2
          simpa [mul_assoc] using L.mul_mem (L.mul_mem (L.inv_mem hk) h1) hk
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        have h2 := hN.conj_mem n hn ⟨k, hk⟩⁻¹
        have e : (⟨k, hk⟩⁻¹ * n * (⟨k, hk⟩⁻¹)⁻¹ : ↥L) = ⟨x, hx⟩ := by
          have hn' : (n : G) = k * x * k⁻¹ := hne
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, hn']
          group
        rwa [e] at h2
    rcases hirr _ hCN' hNU' hLN with h | h
    · left
      apply Subgroup.map_injective L.subtype_injective
      rw [h, hC]
    · right
      apply Subgroup.map_injective L.subtype_injective
      rw [h, hU]

theorem ne_zero_of_isLin2Type {L : Subgroup G} {n : ℕ} (h : IsLin2Type L n) : n ≠ 0 := by
  rintro rfl
  obtain ⟨F, _, _, hcard, -⟩ := h
  have h1 : 1 < Fintype.card F := Fintype.one_lt_card
  rw [hcard, pow_zero] at h1
  exact lt_irrefl _ h1

theorem false_of_isAltNaturalType_one {L : Subgroup G} (hL : IsShort L)
    (h : IsAltNaturalType L 1) : False := by
  rcases hL.quasisimple_or_prime with hq | hp
  · have h3 := three_le_of_isAltNaturalType hq h
    omega
  · obtain ⟨α, -, hker, -⟩ := h
    haveI : Subsingleton (alternatingGroup (Fin 1)) :=
      alternatingGroup_fin_subsingleton 1 (by norm_num)
    have hQ : Subsingleton (L ⧸ CFSG.pCore 2 L) := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
      rw [QuotientGroup.eq, ← hker, MonoidHom.mem_ker]
      exact Subsingleton.elim _ _
    have h1 : Nat.card (L ⧸ CFSG.pCore 2 L) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hQ, ⟨1⟩⟩
    rw [h1] at hp
    exact Nat.not_prime_one hp

theorem inClassX_of_isScriptXType {L : Subgroup G} (hL : IsShort L)
    (hS : CFSG.RankThree.PartOne.IsShortGroup ↥L) (h : IsScriptXType L) :
    CFSG.RankThree.PartOne.InClassX ↥L := by
  rcases h with ⟨n, hn⟩ | ⟨n, hodd, hA⟩
  · have hn0 : n ≠ 0 := ne_zero_of_isLin2Type hn
    exact ⟨hS, Or.inr ⟨n, Nat.one_le_iff_ne_zero.mpr hn0,
      CFSG.AGLEmbedding.NoXBlock.isNaturalSLTwoModule_of_isLin2Type hn0 hn⟩⟩
  · obtain ⟨k, rfl⟩ := hodd
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      exact (false_of_isAltNaturalType_one hL hA).elim
    · have hT :=
        CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.isAltType_of_isAltNaturalType_odd
          (⟨k, rfl⟩ : Odd (2 * k + 1)) hA
      have hM := CFSG.AGLEmbedding.NoXBlock.isNaturalAltModule_of_isAltType hT
      exact ⟨hS, Or.inl ⟨k, by omega, hM⟩⟩

end Transport

@[expose] def SectionalTwoRankFourCatalog : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → CFSG.Assembly.IsCharTwoType G →
    CFSG.GH74.SectionalTwoRankLE G 4 → CFSG.Assembly.InCatalog G

theorem item316ScriptX_of_kforms
    (hOne : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (hTwo : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (hSol : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (hGH : SectionalTwoRankFourCatalog) : Item316ScriptX := by
  intro G _ _ hsimple hnonab hK hchar M L hM hB hT
  have hS : IsShortGroup ↥L := isShortGroup_of_isShort hB.1
  have hX : InClassX ↥L := inClassX_of_isScriptXType hB.1 hS hT
  have hΩ : InOmega L := ⟨hX, M, hM, hB.2.1, hB.2.2⟩
  obtain ⟨Y, hYΩ, hYmax⟩ := exists_maximal_inOmega hΩ
  obtain ⟨M', hM'⟩ := hOne G hK hchar Y hYΩ hYmax
  obtain ⟨hYX, N, hN, hYN, hYsub⟩ := hYΩ
  have hNmem : N ∈ CFSG.maximalTwoLocalsContaining (Y : Set G) := ⟨hN, fun y hy => hYN hy⟩
  rw [hM'] at hNmem
  have hNM' : N = M' := hNmem
  subst hNM'
  rcases hYX.2 with ⟨k, hk, hAlt⟩ | ⟨k, hk, hSL⟩
  · exact hGH G hsimple hnonab hK hchar
      (hSol G hK hsimple hchar N Y hN hYN hYsub hYX ⟨k, hk, hAlt⟩ hM')
  · have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk1 : k = 1 := by omega
      subst hk1
      exact not_isNaturalSLTwoModule_one hYX.1 hSL
    rcases hTwo G hK hsimple hchar Y N hYX hN hYN hYsub hM' k hk2 hSL with h | h | ⟨-, hrk⟩
    · obtain ⟨e⟩ := h
      exact inCatalog_of_mulEquiv_projSL_three hk2 e
    · obtain ⟨e⟩ := h
      exact inCatalog_of_mulEquiv_projSp_two hk2 e
    · refine hGH G hsimple hnonab hK hchar ?_
      have h4 := CFSG.GH74.sectionalTwoRankLE_sectionalTwoRank (X := G)
      rw [hrk] at h4
      exact h4

end CFSG.RankThree.PartTwo.Sec19
