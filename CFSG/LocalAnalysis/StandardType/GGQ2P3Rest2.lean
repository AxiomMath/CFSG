module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoP3Heart
public import CFSG.LocalAnalysis.StandardType.GGQ2P3Hyp
public import CFSG.LocalAnalysis.StandardType.GGQ2LDatumLongest
import CFSG.LocalAnalysis.StandardType.GGQ2LDatumDims

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2P3_lieRank_ge_four {lab : LargeEvenLabel} (hlab : GGQ2TBLabel lab) :
    4 ≤ GGQ2LieRank lab := by
  unfold GGQ2TBLabel at hlab
  rcases hlab with ⟨htag, hr⟩ | ⟨hBC, hr⟩ | ⟨htag, -, hr⟩ | ⟨htag, -, hr⟩ | htag | htag |
    htag | htag
  · have h : GGQ2LieRank lab = lab.rank := by simp [GGQ2LieRank, htag]
    omega
  · rcases hBC with htag | htag
    · have h : GGQ2LieRank lab = lab.rank := by simp [GGQ2LieRank, htag]
      omega
    · have h : GGQ2LieRank lab = lab.rank := by simp [GGQ2LieRank, htag]
      omega
  · have h : GGQ2LieRank lab = lab.rank := by simp [GGQ2LieRank, htag]
    omega
  · have h : GGQ2LieRank lab = lab.rank := by simp [GGQ2LieRank, htag]
    omega
  · have h : GGQ2LieRank lab = 4 := by simp [GGQ2LieRank, htag]
    omega
  · have h : GGQ2LieRank lab = 6 := by simp [GGQ2LieRank, htag]
    omega
  · have h : GGQ2LieRank lab = 7 := by simp [GGQ2LieRank, htag]
    omega
  · have h : GGQ2LieRank lab = 8 := by simp [GGQ2LieRank, htag]
    omega

theorem ggQ2_p3_of_tbDatum (hK : GGReflClassOmegaInput) {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G} {x : G} (hNT : GGNoTransvection 3 Bs) (hAbs : ¬ GGQ2ReflAbsIrred 3 Bs)
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel} (hW : GGQ2LabelWeyl labL M.coxeter)
    (hlab : GGQ2TBLabel labL) (hsh : M.Shape)
    (hhrt : Module.finrank (ZMod 3) M.V ≤ Fintype.card M.Λ →
      (labL.tag = .twA ∧ 3 ∣ labL.rank + 1) ∨ labL.tag = .twE6) :
    GGQ2P3 3 Bs x := by
  rcases labL with ⟨tag, rank, n⟩
  have hcard_lie : Fintype.card M.Λ = GGQ2LieRank ⟨tag, rank, n⟩ :=
    ggQ2LD_card_lie hW hlab
  have hrank4 : 4 ≤ GGQ2LieRank ⟨tag, rank, n⟩ := ggQ2P3_lieRank_ge_four hlab
  have hcard : 3 ≤ Fintype.card M.Λ := by omega
  rcases hsh with hF | hA | hB | hC | hD
  ·
    have hLI : LinearIndependent (ZMod 3) M.coroot := hF.2.1
    have hHdim : Module.finrank (ZMod 3) M.coSpan = Fintype.card M.Λ := by
      rw [GGQ2LDatum.coSpan]
      exact finrank_span_eq_card hLI
    have hVdim : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ + 1 :=
      ggQ2LD_dim_nonheart M (Or.inl hF)
    have hhyp : Module.finrank (ZMod 3) M.coSpan + 1 = Module.finrank (ZMod 3) M.V := by
      omega
    by_cases h5 : 5 ≤ Module.finrank (ZMod 3) M.coSpan
    · exact ggQ2_p3_of_hypDatum hK hNT hAbs M hcard hhyp h5
    · have hcard4 : Fintype.card M.Λ = 4 := by omega
      by_cases htag : tag = .twA
      · have hLie : GGQ2LieRank ⟨tag, rank, n⟩ = 4 := by omega
        have hrank : rank = 4 := by simpa [GGQ2LieRank, htag] using hLie
        exact ggQ2_p3_of_A4FullDatum hNT hAbs M hW htag hrank hF
      · exact ggQ2_p3_of_negDatum hNT hAbs M hcard hhyp (by omega)
          (ggQ2LD_negW_of_rankFour M hW hlab hcard4 htag)
  ·
    have hLI : LinearIndependent (ZMod 3) M.coroot := hA.2.1
    have hxH : M.xV ∈ M.coSpan := hA.2.2.1
    have hdimA : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ + 1 := hA.2.2.2.1
    have hHdim : Module.finrank (ZMod 3) M.coSpan = Fintype.card M.Λ := by
      rw [GGQ2LDatum.coSpan]
      exact finrank_span_eq_card hLI
    have hhyp : Module.finrank (ZMod 3) M.coSpan + 1 = Module.finrank (ZMod 3) M.V := by
      omega
    by_cases h5 : 5 ≤ Module.finrank (ZMod 3) M.coSpan
    · exact ggQ2_p3_of_hypDatum hK hNT hAbs M hcard hhyp h5
    · have hcard4 : Fintype.card M.Λ = 4 := by omega
      by_cases htag : tag = .twA
      · have hrank : rank = 4 := by
          have hLie : GGQ2LieRank ⟨tag, rank, n⟩ = 4 := by omega
          simpa [GGQ2LieRank, htag] using hLie
        exact ggQ2_p3_of_kerDatum M hxH (ggQ2LD_cartanKer_A4 M hW hlab htag hrank)
      · exact ggQ2_p3_of_negDatum hNT hAbs M hcard hhyp (by omega)
          (ggQ2LD_negW_of_rankFour M hW hlab hcard4 htag)
  ·
    have hco1 : Module.finrank (ZMod 3) M.coSpan + 1 = Fintype.card M.Λ := hB.2.1
    have hVdim : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ :=
      ggQ2LD_dim_heart M (Or.inl hB)
    have hhyp : Module.finrank (ZMod 3) M.coSpan + 1 = Module.finrank (ZMod 3) M.V := by
      omega
    rcases hhrt (le_of_eq hVdim) with ⟨htag, h3⟩ | htag
    · have htagA : tag = .twA := htag
      have hcardrank : Fintype.card M.Λ = rank := by
        rw [hcard_lie]
        simp [GGQ2LieRank, htagA]
      by_cases hrank5 : rank = 5
      · exact ggQ2_p3_of_A5HeartDatum hNT hAbs M hW htagA hrank5 hB
      · have h5 : 5 ≤ Module.finrank (ZMod 3) M.coSpan := by
          have h3' : 3 ∣ rank + 1 := h3
          obtain ⟨k, hk⟩ := h3'
          omega
        exact ggQ2_p3_of_hypDatum hK hNT hAbs M hcard hhyp h5
    · have htagE : tag = .twE6 := htag
      have hcard6 : Fintype.card M.Λ = 6 := by
        rw [hcard_lie]
        simp [GGQ2LieRank, htagE]
      have h5 : 5 ≤ Module.finrank (ZMod 3) M.coSpan := by omega
      exact ggQ2_p3_of_hypDatum hK hNT hAbs M hcard hhyp h5
  ·
    exact ggQ2_p3_of_shapeCDatum hK hNT hAbs M hW hlab hC
  ·
    have htop : M.coSpan = ⊤ := hD.2.2
    have hVdim : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ :=
      ggQ2LD_dim_heart M (Or.inr hD)
    exact ggQ2_p3_of_topDatum hAbs M hcard htop (by omega)

theorem ggQ2_p3Rest_holds (hK : GGReflClassOmegaInput) (hTB : GGQ2TableBI1Fail) :
    GGQ2P3OffI1RestInput := by
  intro G _ _ p B Bs x L D J hS hp hI1 _ _ hAbs _
  obtain ⟨labL, -, hlab, -, M, hW, hsh, hhrt⟩ := hTB hS hp hI1
  subst hp
  exact ggQ2_p3_of_tbDatum hK hS.1.2.2.2.1 hAbs M hW hlab hsh hhrt

end CFSG.StandardType

end
