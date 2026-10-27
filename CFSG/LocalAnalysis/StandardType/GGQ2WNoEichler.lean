module

public import CFSG.LocalAnalysis.StandardType.GGQ2EichlerTransfer
public import CFSG.LocalAnalysis.StandardType.GGWeylNoEichlerA
public import CFSG.LocalAnalysis.StandardType.GGWeylNoEichlerBC
public import CFSG.LocalAnalysis.StandardType.GGWeylNoEichlerD
public import CFSG.LocalAnalysis.StandardType.GGWeylNoEichlerE7
public import CFSG.LocalAnalysis.StandardType.GGQ2LDatumDims
public import CFSG.LocalAnalysis.StandardType.GGQ2LabelCartan

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2_W_noEichler {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel} (hW : GGQ2LabelWeyl labL M.coxeter)
    (hlab : GGQ2TBLabel labL) (hne : labL.tag ≠ .twE6) (hsh : M.Shape) (hx : M.xV ≠ 0)
    (hev : Even (Module.finrank (ZMod 3) M.V)) (h6 : 6 ≤ Module.finrank (ZMod 3) M.V)
    (hhrt : Module.finrank (ZMod 3) M.V ≤ Fintype.card M.Λ →
      (labL.tag = .twA ∧ 3 ∣ labL.rank + 1) ∨ labL.tag = .twE6)
    (hE7 : GGWeylE7NoEichler) (φ : MulAut ↥Bs) (hφ : φ ∈ ggAutomizer L Bs) :
    ¬ GGEichler (ggLin (p := 3) M.model φ) := by
  have _ := hx
  have hcard_lie : Fintype.card M.Λ = GGQ2LieRank labL := ggQ2LD_card_lie hW hlab
  have hcartan := ggQ2_label_cartan M hW hlab
  unfold GGQ2TBLabel at hlab
  rcases hlab with hA | hBC | hD | htwD | hF4 | htwE6 | hE7l | hE8
  ·
    obtain ⟨htag, -⟩ := hA
    have hr5 : 5 ≤ labL.rank := by
      have h := hcard_lie
      simp only [GGQ2LieRank, htag] at h
      have hd := ggQ2LD_finrank_le_card_succ M hsh
      omega
    have hc := hcartan
    simp [htag] at hc
    obtain ⟨e, hC⟩ := hc
    exact ggQ2_noEichler_of_rho M
      (ggWeylNoEichlerRhoOn_of_fin (ggWeylNoEichlerRho_A hr5) e hC) φ hφ
  ·
    obtain ⟨htag, -⟩ := hBC
    have hrank : GGQ2LieRank labL = labL.rank := by
      rcases htag with htB | htC
      · simp [GGQ2LieRank, htB]
      · simp [GGQ2LieRank, htC]
    have hr5 : 5 ≤ labL.rank := by
      have hd := ggQ2LD_finrank_le_card_succ M hsh
      rw [hcard_lie, hrank] at hd
      omega
    rcases htag with htB | htC
    · have hc := hcartan
      simp [htB] at hc
      obtain ⟨e, hBCorC⟩ := hc
      rcases hBCorC with hCB | hCC
      · exact ggQ2_noEichler_of_rho M
          (ggWeylNoEichlerRhoOn_of_fin (ggWeylNoEichlerRho_B hr5) e hCB) φ hφ
      · exact ggQ2_noEichler_of_rho M
          (ggWeylNoEichlerRhoOn_of_fin (ggWeylNoEichlerRho_C hr5) e hCC) φ hφ
    · have hc := hcartan
      simp [htC] at hc
      obtain ⟨e, hBCorC⟩ := hc
      rcases hBCorC with hCB | hCC
      · exact ggQ2_noEichler_of_rho M
          (ggWeylNoEichlerRhoOn_of_fin (ggWeylNoEichlerRho_B hr5) e hCB) φ hφ
      · exact ggQ2_noEichler_of_rho M
          (ggWeylNoEichlerRhoOn_of_fin (ggWeylNoEichlerRho_C hr5) e hCC) φ hφ
  ·
    obtain ⟨htag, -⟩ := hD
    have hr5 : 5 ≤ labL.rank := by
      have h := hcard_lie
      simp only [GGQ2LieRank, htag] at h
      have hd := ggQ2LD_finrank_le_card_succ M hsh
      omega
    have hc := hcartan
    simp [htag] at hc
    obtain ⟨e, hC⟩ := hc
    exact ggQ2_noEichler_of_rho M
      (ggWeylNoEichlerRhoOn_of_fin (ggWeylNoEichlerRho_D hr5) e hC) φ hφ
  ·
    obtain ⟨htag, -⟩ := htwD
    have hr5 : 5 ≤ labL.rank := by
      have h := hcard_lie
      simp only [GGQ2LieRank, htag] at h
      have hd := ggQ2LD_finrank_le_card_succ M hsh
      omega
    have hc := hcartan
    simp [htag] at hc
    obtain ⟨e, hC⟩ := hc
    exact ggQ2_noEichler_of_rho M
      (ggWeylNoEichlerRhoOn_of_fin (ggWeylNoEichlerRho_D hr5) e hC) φ hφ
  ·
    have hcard4 : Fintype.card M.Λ = 4 := by
      have h := hcard_lie
      simp only [GGQ2LieRank, hF4] at h
      exact h
    have hd := ggQ2LD_finrank_le_card_succ M hsh
    omega
  ·
    exact absurd htwE6 hne
  ·
    have hc := hcartan
    simp [hE7l] at hc
    obtain ⟨e, hC⟩ := hc
    exact ggQ2_noEichler_of_rho M
      (ggWeylNoEichlerRhoOn_of_fin (ggWeylNoEichlerRho_E7 hE7) e hC) φ hφ
  ·
    have hcard8 : Fintype.card M.Λ = 8 := by
      have h := hcard_lie
      simp only [GGQ2LieRank, hE8] at h
      exact h
    have hheart : Module.finrank (ZMod 3) M.V ≤ Fintype.card M.Λ := by
      rcases hsh with hF | hA | hB | hC | hD
      · have hd := ggQ2LD_dim_nonheart M (Or.inl hF)
        rw [hcard8] at hd
        rw [hd] at hev
        obtain ⟨k, hk⟩ := hev
        omega
      · have hd := ggQ2LD_dim_nonheart M (Or.inr (Or.inl hA))
        rw [hcard8] at hd
        rw [hd] at hev
        obtain ⟨k, hk⟩ := hev
        omega
      · have hd := ggQ2LD_dim_heart M (Or.inl hB)
        rw [hcard8] at hd
        omega
      · have hd := ggQ2LD_dim_nonheart M (Or.inr (Or.inr hC))
        rw [hcard8] at hd
        rw [hd] at hev
        obtain ⟨k, hk⟩ := hev
        omega
      · have hd := ggQ2LD_dim_heart M (Or.inr hD)
        rw [hcard8] at hd
        omega
    rcases hhrt hheart with ⟨htwA, -⟩ | htwE6'
    · rw [hE8] at htwA
      exact absurd htwA (by decide)
    · exact absurd htwE6' hne

end CFSG.StandardType

end
