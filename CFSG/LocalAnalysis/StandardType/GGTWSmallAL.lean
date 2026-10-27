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
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLarge
import CFSG.LocalAnalysis.StandardType.GGTWHLNormalizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTWSmallA_L_twoA
    (hRig : GGLabelRigidInput) (hT : GGTBTorAFrom 4) (hLift : GGTBTorLiftAFrom 4)
    (hW : GGTBWNormLabelInput) (hR : GGTBXDatumResInput) (hTw : GGTWTwA5Open)
    (hJ2S : GGTBJTwoNodeSmallInput) (hC : GGTWSmallCells) (hPZ : GGPZInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hMult : GGTWMultLeaves)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowTwoNodeSmallJA p J L)
    (hxL : x ∉ L) (hKd : GGResTwoNodeSideDatum p Bs K J) {n : ℕ}
    (hKA : GGResXDatumA p Bs K n) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hp3 : 3 ≤ p := by
    have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hrow' := ggTWSmallA_row_narrow hp2 hrow
  obtain ⟨N, labJ, labX, hcell, hJΛ, hXΛ, hJl, hXl, hrowSmall, hAtag, hJtag, hXrank, hJrank,
    hdatL, hHL⟩ :=
    ggTWSmall_rowdata (r₀ := 4) (by norm_num) hRig hT hLift hW (fun _ => hR) (fun _ => hTw) hH
      hrow' hxL
  have hpN : p ∣ N := by
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num
  have hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10 := by
    rcases hcell with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  have hN5 : 5 ≤ N := by rcases hN with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hJperf : commutator ↥J = ⊤ := hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  have hJdvd : p ∣ labJ.rank + 3 := by rw [hJrank]; exact hpN
  have hpnot : ¬ p ∣ labJ.rank + 1 := by
    intro hdvd
    have h2 : p ∣ 2 := by
      have hsub := Nat.dvd_sub hJdvd hdvd
      have he : labJ.rank + 3 - (labJ.rank + 1) = 2 := by omega
      rwa [he] at hsub
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h2)
  have hZJ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J) := by
    refine hMult ↥J p labJ hp2 hJΛ hJperf hJl ?_
    rcases hrowSmall.1 with hrowA | hrowT | hrowD | hrowD
    · obtain ⟨hA, -, -, -⟩ := hrowA
      exact Or.inl ⟨hA, hpnot⟩
    · obtain ⟨hT, hpq, -, -⟩ := hrowT
      exact Or.inr (Or.inl ⟨hT, hpnot, hpq⟩)
    · obtain ⟨hJeq, -, -, -⟩ := hrowD
      rw [hJeq] at hJtag
      exact absurd hJtag (by simp)
    · obtain ⟨hJeq, -, -, -⟩ := hrowD
      rw [hJeq] at hJtag
      exact absurd hJtag (by simp)
  have hLdX : GGResXDatum p Bs L := l6a_xdatum_of_A hdatL
  have hLd : GGResTwoNodeSideDatum p Bs L J := (hJ2S G p B Bs x L D J y K hH).1 hLdX hrow
  have hAligned : GGTWAligned p N 2 Bs L J K :=
    ggTW_align_two hp2 hBs hN5 hdatL hKA hLd hKd
  refine ggTWSmallA_L_of_aligned hC hPZ hFix hFixK (Or.inr rfl) hp3 hpN hN hH hxL hJΛ hXΛ
    hJl hXl hrowSmall hAtag (by omega) (by omega) hZJ hHL ?_ hAligned
  exact fun _ _ => ggTWHLAt_nbr_of_autWeylThree hH (hAligned.autWeylThree_K hN5 (by norm_num))

theorem ggTWSmallA_L
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
    (hHK : GGTWHKSmall) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hrow : GGResRowAt ggRowTwoNodeSmallJA p J L) (hxL : x ∉ L) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hp3 : 3 ≤ p := by
    have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hrow' := ggTWSmallA_row_narrow hp2 hrow
  obtain ⟨N, labJ, labX, hcell, hJΛ, hXΛ, hJl, hXl, hrowSmall, hAtag, hJtag, hXrank, hJrank,
    hdatL, hHL⟩ :=
    ggTWSmall_rowdata (r₀ := 4) (by norm_num) hRig hT hLift hW (fun _ => hR) (fun _ => hTw) hH
      hrow' hxL
  have hpN : p ∣ N := by
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num
  have hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10 := by
    rcases hcell with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  have hN5 : 5 ≤ N := by rcases hN with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hrowSmallAtL : GGResRowAt ggRowTwoNodeSmall p J L :=
    ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hrowSmall⟩
  have hJperf : commutator ↥J = ⊤ := hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  have hJdvd : p ∣ labJ.rank + 3 := by rw [hJrank]; exact hpN
  have hpnot : ¬ p ∣ labJ.rank + 1 := by
    intro hdvd
    have h2 : p ∣ 2 := by
      have hsub := Nat.dvd_sub hJdvd hdvd
      have he : labJ.rank + 3 - (labJ.rank + 1) = 2 := by omega
      rwa [he] at hsub
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h2)
  have hZJ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J) := by
    refine hMult ↥J p labJ hp2 hJΛ hJperf hJl ?_
    rcases hrowSmall.1 with hrowA | hrowT | hrowD | hrowD
    · obtain ⟨hA, -, -, -⟩ := hrowA
      exact Or.inl ⟨hA, hpnot⟩
    · obtain ⟨hT, hpq, -, -⟩ := hrowT
      exact Or.inr (Or.inl ⟨hT, hpnot, hpq⟩)
    · obtain ⟨hJeq, -, -, -⟩ := hrowD
      rw [hJeq] at hJtag
      exact absurd hJtag (by simp)
    · obtain ⟨hJeq, -, -, -⟩ := hrowD
      rw [hJeq] at hJtag
      exact absurd hJtag (by simp)
  have hLdX : GGResXDatum p Bs L := l6a_xdatum_of_A hdatL
  have hLd : GGResTwoNodeSideDatum p Bs L J := (hJ2S G p B Bs x L D J y K hH).1 hLdX hrow
  rcases ggTWSmall_shapeRow_K hJ hJ2S hX h6c h6d h6e h6f h6g hH
      (fun h2 => ggTWSmallA_row_small_of_row hRig hrow h2) hF hS hE with
    hK1 | hK3 | htwo | hW
  ·
    obtain ⟨hcommK, labK, hKΛ, hrawK⟩ :=
      (hH.2.2.1.2 y K hH.2.2.2.2.1 : GGInnerDiagOn Bs K)
    have hKl : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) := by
      refine largeEvenRawDatum_mono ?_ hrawK
      rintro R _ I F ⟨hs, hna, θ, hP⟩
      exact ⟨θ⟩
    have hA : ((labK.tag = .A ∧ ¬ p ∣ labK.rank + 1) ∨
        (labK.tag = .twA ∧ ¬ p ∣ labK.rank + 1 ∧ p ∣ 2 ^ labK.n + 1) ∨
        (p = 3 ∧ labK.tag = .D ∧ labK.rank = 4)) →
        ¬ p ∣ Nat.card ↥(Subgroup.center ↥K) :=
      fun hcov => hMult ↥K p labK hp2 hKΛ hcommK hKl hcov
    have hyK : y ∉ K :=
      ggTWSmall_yK_of_Z hZ hH hJΛ hKΛ hJl hKl hJtag hJdvd hA hK1
    have hAligned : GGTWAligned p N 1 Bs L J K :=
      ggTW_align_one hp2 hBs hN5 hdatL hLd hK1
    refine ggTWSmallA_L_of_aligned hC hPZ hFix hFixK (Or.inl rfl) hp3 hpN hN hH hxL hJΛ hXΛ
      hJl hXl hrowSmall hAtag (by omega) (by omega) hZJ hHL ?_ hAligned
    exact fun h9 hcard => hHK G p N 1 B Bs x L D J y K hH hxL hyK (Or.inl rfl) hp3 hpN h9
      hcard hAligned
  ·
    exact hLE3 G p B Bs x L D J y K hH hF hS hE (Or.inl ⟨hrowSmallAtL, hxL, hK3⟩)
  ·
    obtain ⟨hrowK, hKd⟩ := htwo
    by_cases hyK : y ∈ K
    · exact hIndep G p B Bs x L D J y K hH hF hS hE (Or.inr ⟨hrowK, hyK⟩)
    · exact ggTWSmallA_L_twoA hRig hT hLift hW hR hTw hJ2S hC hPZ hFix hFixK hMult hH hrow
        hxL hKd
        (ggTWSmall_rowdata_K (r₀ := 4) (by norm_num) hRig hT hLift (fun _ => hR) (fun _ => hTw)
          hH hN (by omega) hJΛ hJl hJtag hJrank hrowK)
  · exact hW

end CFSG.StandardType

end
