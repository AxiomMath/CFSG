module

public import CFSG.LocalAnalysis.StandardType.GGResReflFixRootTwo
public import CFSG.LocalAnalysis.StandardType.GGResReflFixLift
public import CFSG.LocalAnalysis.StandardType.GGTorusReflFixTransfer
public import CFSG.LocalAnalysis.StandardType.GGTwE6PlusReflFix
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
import CFSG.LocalAnalysis.StandardType.GGBstarLemmaC

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem largeEvenLabelAll_twE6Plus_reflFix
    {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 ≤ lab.n)
    (ht : lab.tag = .twE6) (hpq : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusLift p 5 R ∧ GGOutdiagOdd p R I ∧ GGTorusReflFix p 5 5 R I := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  refine TwE6Delta.labelAll ht ?_
  intro K _ _ hK
  obtain ⟨σ, hσ, ⟨ε, -⟩⟩ := TwE6Transport.exists_recipeConj hn hK
  have hZ : Subgroup.center (TwE6Delta.RecipeR K lab.n) = ⊥ :=
    TwE6Delta.center_recipeR_eq_bot hn hK
  have hIp : GGOutdiagPrime p (TwE6Delta.RecipeR K lab.n) (TwE6Delta.RecipeI K lab.n) :=
    TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3
  have hcp : GGCenterPrime p (TwE6Delta.RecipeR K lab.n) :=
    TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3
  have hIp' : ∀ φ ∈ TwE6Delta.RecipeI K lab.n, φ ^ p = 1 →
      φ ∈ Set.range
        (MulAut.conj : TwE6Delta.RecipeR K lab.n →* MulAut (TwE6Delta.RecipeR K lab.n)) :=
    fun φ hφ hφp => hIp φ hφ hφp
  have hlift := ggTorusLift_twE6Add_holds hn hK hp hpq
  rw [TwE6Delta.liftRank_of_ne hp3] at hlift
  exact ⟨hlift, TwE6Delta.ggOutdiagOdd_twE6 hn hK p,
    ggTorusReflFix_of_kgReflFix hp hIp' hZ hcp
      ((ggKGReflFix_twE6Plus σ hp hp5 hK hσ hpq).of_mulEquiv ε)⟩

theorem GGResHyp.exists_reflection_fix_of_twE6Plus
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hp5 : 5 ≤ p)
    (hM : GGInnerDiagOnLabel (fun p lab => lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) p Bs L)
    (hne : B ≠ Bs) :
    ∃ t ∈ ggInduced L Bs, GGIsReflection p t ∧ B ≤ ggFixG Bs t := by
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hH.1.tableB_facts
  have hBBs : B ≤ Bs := hH.1.2.1.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1)
    (fun lab hlab hs => largeEvenLabelAll_twE6Plus_reflFix hp hp5 hlab.1 hs.1 hs.2)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3⟩, hlift, hOD, hRF⟩ :=
    largeEvenRawDatum_exists hraw
  have hge := card_range_ggGamma_bstar_ge hH.1 hL θ hBsN hlift
  have hTB : GGTorusTBGroup p 5 R I L (ggQuotHom θ) (ggGamma L hBsN).range :=
    ggTorusTBGroup_of_marking hp hBs hSC hL θ hBsN
      (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hge.1 hge.2
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hBsN
  let H : Subgroup (MulAut L) := (ggGamma L hBN).range
  have hHA : H ≤ (ggGamma L hBsN).range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  have hS : LargeEvenSStar p B x L := hH.1.1.2.2.2.2.2.2.1
  have hHcard : p ^ 5 ≤ Nat.card H := by
    have hcB := card_range_ggGamma_mul L hBN hp hS
    have h1 : 5 + 1 ≤ LargeEvenTwoLocalRank p G :=
      succ_le_twoLocalRank_of_torusLift hp hLx (hS.1.1.2 x hS.2.1) hS.2.2.1 hL θ hlift
    have h2 : p ^ (5 + 1) ≤ Nat.card H * p := by
      rw [hcB, hS.1.2.1]
      exact Nat.pow_le_pow_right hp.pos h1
    rw [pow_succ] at h2
    exact Nat.le_of_mul_le_mul_right h2 hp.pos
  have h3B : ∀ b ∈ B, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ :=
    fun b hb => h3 b (hBBs hb)
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S :=
    ggLNoncyclicInput_holds (G := G) p B x L hH.1.1
  obtain ⟨V, hV1, hV2, hVstab⟩ :=
    GGConfig.beta_twoLocal_of_ne hH.1 hnc hL θ hBN h3B hOD hne
  have hV : ∃ V : Subgroup R, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∀ h ∈ H, ∀ l : L, ggQuotHom θ l ∈ V → ggQuotHom θ (h l) ∈ V := by
    refine ⟨V, hV1, hV2, ?_⟩
    intro h hh l hl
    obtain ⟨b, rfl⟩ := hh
    rw [← ggBeta_ggQuotHom L hBN θ b l]
    exact hVstab (ggBeta L θ hBN b) ⟨b, rfl⟩ (ggQuotHom θ l) hl
  obtain ⟨φ, hφmem, hφrefl, hφfix⟩ :=
    hRF L (ggQuotHom θ) (ggGamma L hBsN).range hTB H hHA hHcard hV
  refine hH.1.exists_reflection_fix_of_automizer hH.2.2.1 hp5 hBsN hφmem hφrefl ?_
  intro b hb
  have hbH : ggGamma L hBsN b ∈ H := ⟨⟨b, hb⟩, rfl⟩
  exact hφfix (ggGamma L hBsN b) ⟨b, rfl⟩ hbH

theorem GGResHyp.iOne_of_twE6Plus_L
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hp5 : 5 ≤ p)
    (hM : GGInnerDiagOnLabel (fun p lab => lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) p Bs L) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  by_cases hB : B = Bs
  · exact hH.iOne_of_eq_bstar hB
  · obtain ⟨t, ht, htr, hfix⟩ := hH.exists_reflection_fix_of_twE6Plus hp5 hM hB
    exact hH.iOne_of_rootTwo
      (hH.1.rootTwo_of_reflection_fix hH.2.2.1 hH.2.2.2.1 hp5 ht htr hfix)

end CFSG.StandardType

end
