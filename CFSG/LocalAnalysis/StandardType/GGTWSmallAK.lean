module

public import CFSG.LocalAnalysis.StandardType.GGTWSmallADefs
public import CFSG.LocalAnalysis.StandardType.GGTWSmallARow
public import CFSG.LocalAnalysis.StandardType.GGTWSmallAClose
public import CFSG.LocalAnalysis.StandardType.GGTWSmallAKClose
public import CFSG.LocalAnalysis.StandardType.GGTWSmallCarried
public import CFSG.LocalAnalysis.StandardType.GGTWSmallRowdata
public import CFSG.LocalAnalysis.StandardType.GGTWSmallRowdataK
public import CFSG.LocalAnalysis.StandardType.GGTWSmallRowdataLrow
public import CFSG.LocalAnalysis.StandardType.GGTWTwA5Defs
public import CFSG.LocalAnalysis.StandardType.GGPZMultA
public import CFSG.LocalAnalysis.StandardType.GGPZMultTwA
public import CFSG.LocalAnalysis.StandardType.GGPZMultD4
public import CFSG.LocalAnalysis.StandardType.GGTWAlignOne
public import CFSG.LocalAnalysis.StandardType.GGTWAlignTwo
public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.StandardType.GGHL58NbrFrom
public import CFSG.LocalAnalysis.StandardType.GGTWTwA5Datum
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLarge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nS3_not_dvd_succ {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ r + 3) : ¬ p ∣ r + 1 := by
  intro hd
  have hsub : p ∣ (r + 3) - (r + 1) := Nat.dvd_sub h hd
  have he : (r + 3) - (r + 1) = 2 := by omega
  rw [he] at hsub
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hsub)

theorem ggTWSmallA_K
    (hRig : GGLabelRigidInput) (hT : GGTBTorAFrom 4) (hLift : GGTBTorLiftAFrom 4)
    (hW : GGTBWNormLabelInput) (hR : GGTBXDatumResInput) (hTw : GGTWTwA5Open)
    (hJ : GGTBJInputR) (hJ2S : GGTBJTwoNodeSmallInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input)
    (hLE3 : GGResTwoNodeLE3SmallInput) (hIndep : GGResTwoNodeIndepInput)
    (hC : GGTWSmallCells) (hPZ : GGPZInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    (hMult : GGTWMultLeaves) (hZ : GGTWZKInput)
    (hHL : GGTWHLSmall) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hrow : GGResRowAt ggRowTwoNodeSmallJA p J K) (hyK : y ∉ K)
    (hLread : GGResRowAt ggRowTwoNode p J L → x ∉ L →
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hrowK0 : GGResRowAt ggRowTwoNodeSmallJA p J K := hrow
  obtain ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrowJA⟩ := hrow
  have hrowSmall : ggRowTwoNodeSmall p labJ labK := hrowJA.1
  have hJtag : labJ.tag = .A ∨ labJ.tag = .twA := hrowJA.2
  have hrow2 : ggRowTwoNode p labJ labK := hrowSmall.1
  have hKle9 : labK.rank ≤ 9 := hrowSmall.2
  have hp : p.Prime := hH.1.tableB_facts.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have h4K : 4 ≤ labK.rank := ggTWSmallA_rank_ge hp hp2 hJΛ hJtag hrow2
  obtain ⟨-, hKtag, hKrank_eq, hdvdK, hKtdvdM⟩ := l05nQD_row_facts hrow2 h4K
  have hN : labK.rank + 1 = 5 ∨ labK.rank + 1 = 6 ∨ labK.rank + 1 = 7 ∨
      labK.rank + 1 = 9 ∨ labK.rank + 1 = 10 := by
    rcases l05nQD_cell hp hp2 h4K hKle9 hdvdK with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      omega
  have hrowKsmall : GGResRowAt ggRowTwoNodeSmall p J K :=
    ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrowSmall⟩
  have hrowK : GGResRowAt ggRowTwoNode p J K :=
    ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrow2⟩
  rcases ggTWSmall_shapeRow_L hJ hJ2S hX h6c h6d h6e h6f h6g hH
      (fun h2 => ggTWSmallA_row_small_of_row hRig hrowK0 h2) hF hS hE with
    hLside | hL3 | ⟨hrowL, _hsideL⟩ | hweyl
  · have hKdatum : GGResXDatumA p Bs K (labK.rank + 1 - 1) :=
      ggTWSmall_rowdata_K (r₀ := 4) (N := labK.rank + 1) (le_refl 4) hRig hT hLift
        (fun _ => hR) (fun _ => hTw) hH hN (by omega) hJΛ hJl hJtag (by omega) hrowK
    have hKX : GGResXDatum p Bs K := l6a_xdatum_of_A hKdatum
    have hKside : GGResTwoNodeSideDatum p Bs K J :=
      (hJ2S G p B Bs x L D J y K hH).2 hKX hrowK0
    have hN5 : 5 ≤ labK.rank + 1 := by rcases hN with h | h | h | h | h <;> omega
    have hA : GGTWAligned p (labK.rank + 1) 1 Bs K J L :=
      ggTW_align_one (N := labK.rank + 1) hp2 hBs hN5 hKdatum hKside hLside
    have hZJ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J) := by
      have hJperf : commutator ↥J = ⊤ := hH.1.2.2.1.2.2.2.2.2.1.2.2.1
      refine hMult ↥J p labJ hp2 hJΛ hJperf hJl ?_
      rcases hrow2 with ⟨hA', hq, hpJ, _⟩ | ⟨htw, hq, hpJ, _⟩ | ⟨hD, -, -, -⟩ |
        ⟨htwD, -, -, -⟩
      · exact Or.inl ⟨hA', l05nS3_not_dvd_succ hp hp2 hpJ⟩
      · exact Or.inr (Or.inl ⟨htw, l05nS3_not_dvd_succ hp hp2 hpJ, hq⟩)
      · exfalso
        have htagD : labJ.tag = .D := by simpa using congrArg LargeEvenLabel.tag hD
        rcases hJtag with h | h <;> rw [htagD] at h <;> exact absurd h (by decide)
      · exfalso
        have htagD : labJ.tag = .D := by simpa using congrArg LargeEvenLabel.tag htwD
        rcases hJtag with h | h <;> rw [htagD] at h <;> exact absurd h (by decide)
    have hHK : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y →
        GGTWHLAt p Bs K y := by
      intro hCent
      by_cases hEnn : p = 3 ∧ labK.rank = 5 ∧ p ∣ 2 ^ labK.n + 1
      · have htw : labK.tag = .twA ∧ labK.rank = 5 ∧ 3 ∣ 2 ^ labK.n + 1 := by
          refine ⟨?_, hEnn.2.1, by simpa [hEnn.1] using hEnn.2.2⟩
          rcases hrow2 with ⟨hA', hq, _, hXeq⟩ | ⟨htw', _, _, hXeq⟩ | ⟨hD, -, -, -⟩ |
            ⟨htwD, -, -, -⟩
          · exfalso
            subst hXeq
            have h2 : p ∣ 2 := by
              have hsub := Nat.dvd_sub (by simpa using hEnn.2.2) hq
              have he : 2 ^ labJ.n + 1 - (2 ^ labJ.n - 1) = 2 := by
                have hA : 0 < 2 ^ labJ.n := by positivity
                omega
              rwa [he] at hsub
            exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
          · subst hXeq
            rfl
          · exfalso
            have htagD : labJ.tag = .D := by simpa using congrArg LargeEvenLabel.tag hD
            rcases hJtag with h | h <;> rw [htagD] at h <;> exact absurd h (by decide)
          · exfalso
            have htagD : labJ.tag = .D := by simpa using congrArg LargeEvenLabel.tag htwD
            rcases hJtag with h | h <;> rw [htagD] at h <;> exact absurd h (by decide)
        exact (ggTWTwA5_datum hRig hR hTw hH (X := K) (z := y) (Or.inr ⟨rfl, rfl⟩) hEnn.1
          hKΛ hKl htw).2.2 ⟨rfl, rfl⟩ hyK hCent
      · have hPredK : GGTWRowPred 4 p labK := ⟨hKtag, h4K, hdvdK, hKtdvdM, fun h => hEnn h⟩
        exact ggHL58Nbr_of_inputs_from (le_refl 4) hRig hT hLift hW hH hCent
          (l05nQK_innerDiagOnLabel_K hRig hH hKΛ hKl hPredK h4K)
    have hCard : Nat.card ↥Bs = p ^ (labK.rank + 1 - 1) :=
      le_antisymm (ggTW_card_le_oneNode hFix hH hA)
        (ggTW_card_ge hp3 hdvdK hN hH (Or.inl rfl) hZJ (Or.inr hA))
    have hHL' : (labK.rank + 1 = 5 ∨ labK.rank + 1 = 6 ∨ labK.rank + 1 = 9) →
        GGTWHLAt p Bs L x :=
      fun h9 => hHL G p (labK.rank + 1) B Bs x L D J y K hH hyK hp3 hdvdK h9 hCard hA
    have hXrank : labK.rank = (labK.rank + 1) - 1 := by omega
    have hJrank : labJ.rank = (labK.rank + 1) - 3 := by omega
    exact ggTWSmallA_close_K (N := labK.rank + 1) hC hPZ hFix hFixK (Or.inl rfl) hp3 hdvdK hN hH
      hyK hJΛ hKΛ hJl hKl hrowSmall hKtag hXrank hJrank hZJ hCard hHK hHL' hA
  · exact hLE3 G p B Bs x L D J y K hH hF hS hE (Or.inr ⟨hrowKsmall, hyK, hL3⟩)
  · by_cases hxL : x ∈ L
    · exact hIndep G p B Bs x L D J y K hH hF hS hE (Or.inl ⟨hrowL, hxL⟩)
    · exact hLread hrowL hxL
  · exact hweyl

end CFSG.StandardType

end
