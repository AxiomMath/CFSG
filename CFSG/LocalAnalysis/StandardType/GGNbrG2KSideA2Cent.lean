module

public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2OddA
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2OddB
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2G2
public import CFSG.CharacterTheory.Wreathed.CentralSL2.Basic
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper
public import CFSG.RankThree.PartOne.D4RC.RxIso
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartOne.SEITZ7.D4Final
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofKFacts
public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofBlockMain
public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofG2Data

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.Chevalley (torusTorsion)
open CFSG.RankThree.Chevalley (fin_G2_cases torusTorsion_le_torusGroup
  rootDiagUnit_mem_torusTorsion_iff)
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LieType.Steinberg.RankTwo

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

namespace G2KAuxA2Cent

theorem threeB_card_lt {q : ℕ} (hq : 2 ≤ q) :
    q * (q ^ 2 - 1) * (q - 1) < q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by
  have hqpos : 0 < q := by omega
  have hq1 : 1 < q := by omega
  have h2 : 0 < q ^ 2 - 1 := by
    have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hq1
    omega
  have h3 : 0 < q ^ 3 - 1 := by
    have : 1 < q ^ 3 := Nat.one_lt_pow (by norm_num : 3 ≠ 0) hq1
    omega
  have hkey : q - 1 < q ^ 2 * (q ^ 3 - 1) := by
    calc q - 1 < q := by omega
      _ ≤ q ^ 2 := Nat.le_self_pow (by norm_num : 2 ≠ 0) q
      _ ≤ q ^ 2 * (q ^ 3 - 1) := Nat.le_mul_of_pos_right _ h3
  have hcab : q * (q ^ 2 - 1) * (q - 1) <
      q * (q ^ 2 - 1) * (q ^ 2 * (q ^ 3 - 1)) :=
    Nat.mul_lt_mul_of_pos_left hkey (Nat.mul_pos hqpos h2)
  calc q * (q ^ 2 - 1) * (q - 1) < q * (q ^ 2 - 1) * (q ^ 2 * (q ^ 3 - 1)) := hcab
    _ = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by ring

theorem a2_centralizer_caseA
    {F : Type} [Field F] [Finite F]
    {s : adjointGroup Tag.G2 F} {b : Fin Tag.G2.rank → Fˣ}
    (hsb : (s : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 b) (hb3 : b ^ 3 = 1)
    (hia : b g2ia = 1) (hs1 : s ≠ 1) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 3) F →* adjointGroup Tag.G2 F,
      Function.Injective φ ∧ φ.range = Subgroup.centralizer ({s} : Set (adjointGroup Tag.G2 F)) ∧
        ∀ γ ∈ RA2, ∀ c : F,
          φ (CFSG.LieType.Steinberg.SL.x 2 F γ c) =
            CFSG.GH74.GLS.Stage2.Bender.Thm1.a2y γ c := by
  set t : Fˣ := b g2ir with ht
  have hb_eq : b = Pi.mulSingle g2ir t := by
    funext j
    rcases fin_G2_cases j with rfl | rfl
    · rw [Pi.mulSingle_eq_of_ne (by decide : g2ia ≠ g2ir)]
      exact hia
    · rw [Pi.mulSingle_eq_same]
  have ht3 : t ^ 3 = 1 := by
    have := congrFun hb3 g2ir
    simpa [ht, Pi.pow_apply] using this
  have ht1 : t ≠ 1 := by
    intro h
    apply hs1
    apply Subtype.ext
    rw [hsb, hb_eq, h, Pi.mulSingle_one, rootDiagUnit_one]
    rfl
  have htord : orderOf t = 3 := orderOf_eq_prime ht3 ht1
  obtain ⟨φ, hφinj, hφ⟩ := exists_a2Hom_injective (K := F)
  refine ⟨φ, hφinj, ?_, hφ⟩
  have hsb' : (s : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 (Pi.mulSingle g2ir t) := by
    rw [hsb, hb_eq]
  have heq : Subgroup.centralizer ({s} : Set (adjointGroup Tag.G2 F)) = φ.range := by
    apply le_antisymm
    · intro x hx
      have hx' := (mem_centralizer_iff_toral hsb').mp hx
      obtain ⟨w, hw, hwx⟩ :=
        CFSG.RankThree.PartTwo.Sec4.Res417Seven.toralCentralizer_threeA_le_range_a2
          φ hφ htord hx'
      have : w = x := Subtype.ext hwx
      rwa [← this]
    · refine range_le_of_a2y φ hφ _ fun γ hγ c => ?_
      rw [mem_centralizer_iff_toral hsb', mem_toralCentralizer]
      refine ⟨(CFSG.GH74.GLS.Stage2.Bender.Thm1.a2y γ c).2, ?_⟩
      rw [coe_a2y hγ]
      have hmem : g2CommRoot (a2pos (γ 0, γ 1)) ∈
          rootCharKernel (Pi.mulSingle g2ir t) := by
        rw [rootCharKernel_threeA htord]
        exact a2_long_roots hγ
      rw [rootDiagUnit_conj_pinnedX _ hmem.1, hmem.2, Units.val_one, one_mul]
  exact heq.symm

theorem card_centralizer_threeB_le
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {s : adjointGroup Tag.G2 F} {b : Fin Tag.G2.rank → Fˣ}
    (hsb : (s : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 b) (hb3 : b ^ 3 = 1)
    (hia : b g2ia ≠ 1) :
    Nat.card ↥(Subgroup.centralizer ({s} : Set (adjointGroup Tag.G2 F))) ≤
      Nat.card F * (Nat.card F ^ 2 - 1) * (Nat.card F - 1) := by
  haveI hfin : Finite (ModGL Tag.G2 F) := finite_modGL
  obtain ⟨w, ζ, hζ, hw⟩ := exists_weyl_threeB (K := F) hb3 hia
  have h1 := (rootDiagUnit_eq_conj_canonicalRep_iff b (Pi.mulSingle g2ia ζ) w).mpr hw
  let n : adjointGroup Tag.G2 F :=
    ⟨canonicalRep (coxeterSystem .G2) F w, canonicalRep_mem_adjointGroup _ F w⟩
  let d'' : adjointGroup Tag.G2 F := n⁻¹ * s * n
  have hn : (n : ModGL Tag.G2 F) = canonicalRep (coxeterSystem .G2) F w := rfl
  have hzd'' : (d'' : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 (Pi.mulSingle g2ia ζ) := by
    change ((n⁻¹ * s * n : adjointGroup Tag.G2 F) : ModGL Tag.G2 F) = _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hsb, hn, h1]
    group
  have hs_eq : n * d'' * n⁻¹ = s := by
    change n * (n⁻¹ * s * n) * n⁻¹ = s
    group
  have hcard_eq : Nat.card ↥(Subgroup.centralizer ({d''} : Set (adjointGroup Tag.G2 F))) =
      Nat.card ↥(Subgroup.centralizer ({s} : Set (adjointGroup Tag.G2 F))) := by
    rw [← hs_eq]
    exact Nat.card_congr
      (CFSG.RankThree.PartTwo.Sec4.E27.centralizerConjEquiv n d'').toEquiv
  have hmap_le : (Subgroup.centralizer ({d''} : Set (adjointGroup Tag.G2 F))).map
      (adjointGroup Tag.G2 F).subtype ≤
        (CFSG.RankThree.PartTwo.Sec4.Res417Seven.kappaB F).range := by
    rintro y ⟨x, hx, rfl⟩
    exact CFSG.RankThree.PartTwo.Sec4.Res417Seven.toralCentralizer_threeB_le_range_kappaB
      (L := F) hζ ((mem_centralizer_iff_toral hzd'').mp hx)
  have hrange : Nat.card (CFSG.RankThree.PartTwo.Sec4.Res417Seven.kappaB F).range =
      Nat.card (CFSG.LieType.Chevalley.SL2 F × Fˣ) := by
    rw [MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective
        (CFSG.RankThree.PartTwo.Sec4.Res417Seven.kappaB_injective (L := F)),
      Subgroup.card_top]
  calc Nat.card ↥(Subgroup.centralizer ({s} : Set (adjointGroup Tag.G2 F)))
      = Nat.card ↥(Subgroup.centralizer ({d''} : Set (adjointGroup Tag.G2 F))) :=
        hcard_eq.symm
    _ = Nat.card ((Subgroup.centralizer ({d''} : Set (adjointGroup Tag.G2 F))).map
          (adjointGroup Tag.G2 F).subtype) :=
        (Subgroup.card_map_of_injective (adjointGroup Tag.G2 F).subtype_injective).symm
    _ ≤ Nat.card (CFSG.RankThree.PartTwo.Sec4.Res417Seven.kappaB F).range :=
        Subgroup.card_le_of_le hmap_le
    _ = Nat.card (CFSG.LieType.Chevalley.SL2 F × Fˣ) := hrange
    _ = Nat.card (CFSG.LieType.Chevalley.SL2 F) * Nat.card Fˣ := Nat.card_prod _ _
    _ = Nat.card F * (Nat.card F ^ 2 - 1) * (Nat.card F - 1) := by
        rw [CFSG.Wreathed.CentralSL2.card_SL_two, Nat.card_units]

end G2KAuxA2Cent

theorem ggNbrG2K_a2_centralizer
    {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (h6 : 6 ∣ n) {s : adjointGroup Tag.G2 F} (hs : (s : ModGL Tag.G2 F) ∈ torusTorsion F 3)
    (hs1 : s ≠ 1)
    (hcard : Nat.card ↥(Subgroup.centralizer ({s} : Set (adjointGroup Tag.G2 F))) =
      ggG2SL3Card n) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 3) F →* adjointGroup Tag.G2 F,
      Function.Injective φ ∧ φ.range = Subgroup.centralizer ({s} : Set (adjointGroup Tag.G2 F)) ∧
        ∀ γ ∈ RA2, ∀ c : F, φ (CFSG.LieType.Steinberg.SL.x 2 F γ c) =
          CFSG.GH74.GLS.Stage2.Bender.Thm1.a2y γ c := by
  haveI hchar : CharP F 2 := charP_two_of_card hF
  obtain ⟨c, hsc, hc3⟩ : ∃ c : Fin Tag.G2.rank → Fˣ,
      (s : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 c ∧ c ^ 3 = 1 := by
    have hH : (s : ModGL Tag.G2 F) ∈ torusGroup Tag.G2 F := torusTorsion_le_torusGroup 3 hs
    obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hH
    refine ⟨c, hc, ?_⟩
    rw [hc] at hs
    exact (rootDiagUnit_mem_torusTorsion_iff 3 c).1 hs
  by_cases hia : c g2ia = 1
  · exact G2KAuxA2Cent.a2_centralizer_caseA hsc hc3 hia hs1
  · exfalso
    have hle := G2KAuxA2Cent.card_centralizer_threeB_le hsc hc3 hia
    have hcard' : Nat.card ↥(Subgroup.centralizer ({s} : Set (adjointGroup Tag.G2 F))) =
        Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) := by
      rw [hcard]
      simp only [ggG2SL3Card]
      rw [← hF]
    rw [hcard'] at hle
    have hq2 : 2 ≤ Nat.card F := by
      have hn0 : n ≠ 0 := by
        intro hn'
        have hg0 : ggG2SL3Card n = 0 := by simp [ggG2SL3Card, hn']
        have hpos : 0 < Nat.card ↥(Subgroup.centralizer
            ({s} : Set (adjointGroup Tag.G2 F))) := Nat.card_pos
        omega
      have hn1 : 1 ≤ n := by
        obtain ⟨k, hk⟩ := h6
        omega
      rw [hF]
      exact two_le_two_pow hn1
    have hlt := G2KAuxA2Cent.threeB_card_lt hq2
    exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)

end CFSG.StandardType

end
