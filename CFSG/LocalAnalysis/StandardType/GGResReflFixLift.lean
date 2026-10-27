module

public import CFSG.LocalAnalysis.StandardType.GGKGForkOneDone
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLift
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem GGConfig.exists_reflection_fix_of_automizer
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hInn : GGInnerDiagAll p B Bs x L D J) (hp5 : 5 ≤ p)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) {φ : MulAut ↥(ggGamma L hBsN).range}
    (hφ : φ ∈ ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range (ggGamma L hBsN).range)
    (hrefl : GGIsReflection p φ)
    (hfix : ∀ b : ↥Bs, (b : G) ∈ B →
      φ ((ggGamma L hBsN).rangeRestrict b) = (ggGamma L hBsN).rangeRestrict b) :
    ∃ t ∈ ggInduced L Bs, GGIsReflection p t ∧ B ≤ ggFixG Bs t := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := by omega
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hM : GGInnerDiagOnLabel GGForkRootSL2Label p Bs L := by
    have hmarkL := hcfg.1.2.2.2.2.2.2.2.1
    obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hH⟩ := largeEvenMarking_exists_hasLabel hmarkL
    have hsplit : LargeEvenSplit p lab := hH.1
    have hmark := ggInnerDiagOn_relabel (ggLabelRigidInput_holds) hInn.1 hlab hhas
    refine largeEvenMarking_mono ?_ hmark
    rintro lab' R' _ I' F' θ' ⟨h1, h2, h3⟩
    subst h1
    exact ⟨⟨hp5, hsplit⟩, h2, h3⟩
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGForkRootSL2Label p lab)
    (fun lab hlab hs => ggForkRootSL2KGInput_holds p lab hp hlab hs)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, h3⟩, r₀, hlift, hT⟩ :=
    largeEvenRawDatum_exists hraw
  obtain ⟨hr₀, h3'⟩ := card_range_ggGamma_bstar_ge hcfg hL θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hr₀ h3'
  obtain ⟨n, hn, -, hW, hnφ, -, -, -, -⟩ :=
    hT L (ggQuotHom θ) (ggGamma L hBsN).range hTB φ hφ hrefl
  obtain ⟨m, hg, htr, hover⟩ :=
    exists_pow_isReflection_overGamma_of_weylElt hp hp2 hBs hSC hBsN hW hn (hnφ ▸ hrefl)
  have hgL : (n : G) ^ m ∈ L := L.pow_mem n.2 m
  have hmem : ggConjAut Bs hg ∈ ggInduced L Bs :=
    ⟨(n : G) ^ m, hgL, hg, fun b => ggConjAut_apply Bs hg b⟩
  refine ⟨ggConjAut Bs hg, hmem, htr, ?_⟩
  intro b hb
  have hbBs : b ∈ Bs := hcfg.2.1.1 hb
  let bb : ↥Bs := ⟨b, hbBs⟩
  let c : ↥Bs := bb⁻¹ * ggConjAut Bs hg bb
  have h1 : (ggGamma L hBsN).rangeRestrict c = 1 := by
    change (ggGamma L hBsN).rangeRestrict (bb⁻¹ * ggConjAut Bs hg bb) = 1
    rw [map_mul, map_inv, hover bb, hnφ, hfix bb hb, inv_mul_cancel]
  have hcent : (c : G) ∈ Subgroup.centralizer (L : Set G) :=
    (ggGamma_eq_one_iff L hBsN c).mp (by
      have := congrArg Subtype.val h1
      simpa using this)
  have hgc : (n : G) ^ m * (c : G) * ((n : G) ^ m)⁻¹ = (c : G) := by
    have hcomm := Subgroup.mem_centralizer_iff.mp hcent ((n : G) ^ m) hgL
    rw [hcomm]
    group
  have htc : ggConjAut Bs hg c = c := by
    apply Subtype.ext
    rw [ggConjAut_apply Bs hg]
    exact hgc
  have htbb : ggConjAut Bs hg bb = bb * c := by
    change ggConjAut Bs hg bb = bb * (bb⁻¹ * ggConjAut Bs hg bb)
    group
  have ht2 : ggConjAut Bs hg (ggConjAut Bs hg bb) = bb := by
    have h := congrArg (fun f : MulAut ↥Bs => f bb) htr.1
    simpa [pow_two, MulAut.mul_apply] using h
  have ht2' : ggConjAut Bs hg (ggConjAut Bs hg bb) = bb * c * c := by
    rw [htbb, map_mul, htbb, htc]
  have hcc : c * c = 1 := by
    rw [ht2'] at ht2
    have h4 : bb⁻¹ * (bb * c * c) = bb⁻¹ * bb := congrArg (fun x => bb⁻¹ * x) ht2
    simpa [mul_assoc] using h4
  have hcc2 : c ^ 2 = 1 := by
    rw [pow_two]
    exact hcc
  have hcp : c ^ p = 1 := by
    apply Subtype.ext
    simpa using hBs.2 (c : G) c.2
  have hc1 : c = 1 := TableBOrth.eq_one_of_sq_of_pow_prime hp hp2 hcc2 hcp
  refine ⟨bb, ?_, rfl⟩
  change ggConjAut Bs hg bb = bb
  rw [htbb, hc1, mul_one]

end CFSG.StandardType

end
