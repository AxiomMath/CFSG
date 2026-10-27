module

public import CFSG.LocalAnalysis.StandardType.GGResRowF4ThreeOn
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofFinal
import CFSG.LocalAnalysis.StandardType.GGStdSubExist
import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem false_of_original_torusLift_ge_four {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hcard : Nat.card Bs = p ^ 4)
    {S : ℕ → LargeEvenLabel → Prop} (hM : GGInnerDiagOnLabel S p Bs L)
    (hlift : ∀ (lab : LargeEvenLabel), LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ _ _ => ∃ r, 4 ≤ r ∧ GGTorusLift p r R) :
    False := by
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨_, _, _, _, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hP₀⟩ := hQ₀
  obtain ⟨hSlab, -, -⟩ := hP₀
  obtain ⟨R, _, I, F, hQ, hliftR⟩ :=
    largeEvenRawDatum_exists (hlift lab hlab hSlab _ hraw)
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨-, hN, -⟩ := hP
  obtain ⟨r, hr4, hlift'⟩ := hliftR
  have hge := card_range_ggGamma_bstar_ge hcfg hperf θ hN hlift'
  have hp4 : p ^ 4 ≤ Nat.card (ggGamma L hN).range :=
    (Nat.pow_le_pow_right hp.pos hr4).trans hge.1
  have hmul := card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hN
  rw [hcard, show p ^ 4 = p ^ 3 * p by ring] at hmul
  have hγ : Nat.card (ggGamma L hN).range = p ^ 3 :=
    Nat.eq_of_mul_eq_mul_right hp.pos hmul
  rw [hγ] at hp4
  have h43 : 4 ≤ 3 := (pow_le_pow_iff_right₀ hp.one_lt).mp hp4
  omega

theorem largeEvenSplit_of_unitDvd63 {p : ℕ} {lab : LargeEvenLabel}
    (h : GGUnitDvd63Label p lab) : LargeEvenSplit p lab := by
  rcases lab with ⟨t, l, n⟩
  simp only [GGUnitDvd63Label, GGUnitDvdLabel] at h
  obtain ⟨⟨ht, -, hpq, -⟩, -, hp⟩ := h
  subst ht
  subst hp
  exact Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted], by simp, hpq⟩)

theorem no_original_unitSix_at_card_four
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hM : GGInnerDiagOnLabel GGUnitDvd63Label p Bs L)
    (hcard : Nat.card Bs = p ^ 4) : False := by
  have hM' : GGInnerDiagOnLab GGUnitDvd63Label p Bs L :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ hP =>
      ⟨hP.1, largeEvenSplit_of_unitDvd63 hP.1, hP.2.1, hP.2.2⟩) hM
  have hp : p.Prime := hcfg.tableB_facts.1
  have h5 : p ^ 5 ≤ Nat.card Bs :=
    Line63.H5.ggUnitDvd63BstarRankInput_holds G p B Bs x L D J hcfg hM'
  rw [hcard] at h5
  have h54 : (5 : ℕ) ≤ 4 := (pow_le_pow_iff_right₀ hp.one_lt).mp h5
  omega

theorem no_original_f4Three_at_card_four
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hT : GGNoTransvection p Bs)
    (hM : GGInnerDiagOnLabel GGF4ThreeLabel p Bs L)
    (hcard : Nat.card Bs = p ^ 4) : False := by
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hMkeep := hM
  obtain ⟨_, _, _, hraw⟩ := hM
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hP⟩ := hQ
  obtain ⟨-, hN, -⟩ := hP
  have hge := ggF4Three_rank_of_innerDiagOnLabel hcfg hT hMkeep hN
  have hmul := card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hN
  rw [hcard, show p ^ 4 = p ^ 3 * p by ring] at hmul
  have hγ : Nat.card (ggGamma L hN).range = p ^ 3 :=
    Nat.eq_of_mul_eq_mul_right hp.pos hmul
  rw [hγ] at hge
  have h43 : 4 ≤ 3 := (pow_le_pow_iff_right₀ hp.one_lt).mp hge
  omega

end CFSG.StandardType

end
