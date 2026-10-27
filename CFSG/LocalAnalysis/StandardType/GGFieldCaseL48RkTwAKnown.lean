module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBPosition
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Subgroup

@[expose] def GGL48TwATorusLift : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → lab.tag = .twA →
    6 ≤ lab.rank → p ∣ lab.rank + 1 → p ∣ 2 ^ lab.n + 1 →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (lab.rank - 2) R

@[expose] def GGL48TwAKnownGroup : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → lab.tag = .twA →
    6 ≤ lab.rank → p ∣ lab.rank + 1 → p ∣ 2 ^ lab.n + 1 →
      LargeEvenLabelAll lab fun R _ I _ =>
        ∀ (M : Type) [Group M] [Finite M] (L' E : Subgroup M)
          (θ : L' ⧸ Subgroup.center L' ≃* R) (hE : E ≤ Subgroup.normalizer (L' : Set M)),
          GGTableBPosition p L' E I θ hE → E ⊓ Subgroup.centralizer (L' : Set M) ≠ ⊥ →
          p ^ (lab.rank - 1) ≤ Nat.card E → p ^ lab.rank ≤ Nat.card E

theorem ggL48TB0TwConfigInputTwA_of_known (hT : GGL48TwATorusLift) (hK : GGL48TwAKnownGroup) :
    GGL48TB0TwConfigInputTwA := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS hJD r hr hmark
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  obtain ⟨hp, -, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hSStar : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSStar.2.2.1
  have hx : x ^ p = 1 := hSStar.1.1.2 x hSStar.2.1
  obtain ⟨R₀, _, I₀, F₀, -, -, θ₀, ⟨hSp, -, -, -⟩⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨htag, hd1, hd2, hrk⟩ := hSp
  have hrank6 : 6 ≤ lab.rank := by omega
  have hAll := largeEvenLabelAll_and (hT p lab hp hlab htag hrank6 hd1 hd2)
    (hK p lab hp hlab htag hrank6 hd1 hd2)
  have hraw' := hAll _ hraw
  obtain ⟨R, _, I, F, ⟨-, -, θ, ⟨-, -, hBsN, h3⟩⟩, hlift, hKG⟩ := largeEvenRawDatum_exists hraw'
  have hrank_le := succ_le_twoLocalRank_of_torusLift hp hLx hx hx1 hperf θ hlift
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hSStar.1.2.1
  have hpow1 : p ^ (lab.rank - 1) ≤ Nat.card Bs := by
    calc p ^ (lab.rank - 1) = p ^ ((lab.rank - 2) + 1) := by
          rw [show lab.rank - 1 = (lab.rank - 2) + 1 by omega]
      _ ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos hrank_le
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1
  have hpos := tableBPosition_of_setup hS θ hperf hBsN h3
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hne : Bs ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
    intro hbot
    have hxmem : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨hxBs, hxC⟩
    rw [hbot] at hxmem
    exact hx1 (Subgroup.mem_bot.mp hxmem)
  have hfin := hKG G L Bs θ hBsN hpos hne hpow1
  simpa [hrk] using hfin

end CFSG.StandardType

end
