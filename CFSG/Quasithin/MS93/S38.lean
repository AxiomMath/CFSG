module

public import CFSG.Quasithin.MS93.S38EndStmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem PUHyp.isSp4U_of_isSp4DerSec (h : PUHyp M T L) {k : ℕ} (hk : 2 ≤ k)
    (hs : IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) k) : IsSp4U M T L := by
  rcases hs with ⟨rfl, -⟩ | ⟨-, F, iF, fF, α, hF, hα, hsum⟩
  · omega
  · refine Or.inl ⟨k, F, iF, fF, α, hk, hF, hα, ?_⟩
    rwa [← h.Uq_inf_Zq]

theorem PUHyp.not_vv_le_qv_of_xOffData (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hD : XOffData M T) {ε ε' : Vtx (puAmalgam h.le)} (hc : IsCritical _ ε ε') :
    ¬ Vv (puAmalgam h.le) ε ≤ Qv (puAmalgam h.le) (geo _ ε' ε 2) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  refine ms23_step3 _ h20 hb0 hb hC (fun γ ρ hγ hγρ => h.gen23At hγ hγρ) (fun γ γ' hcr => ?_) hc
  have hcr' := ms22_iii _ h20 hb0 hC hcr
  exact zc23At_of_offData h20 hb0 hC hcr
    (h.offDataAt hD hcr.1 (adj_geo_one_of_isCritical _ hb0 hcr))
    (h.offDataAt hD (hcr.isMVtx_right _ h20) (adj_geo_one_of_isCritical _ hb0 hcr'))

theorem s38_of_offData (h32 : S32) (hEnd : S38End) (hG2 : S38G2)
    (hD : ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
      2 < critDist (puAmalgam h.le) → ⁅Xq M, L⁆ ≤ Uq M T L →
      (IsHatA6U M T L ∨ IsDoubleSL3U M T L ∨ IsSL3TwoU M T L ∨ IsSL3TwoZ M T L ∨
        IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1) →
      ¬ IsSL3U M T L → ¬ IsSp4U M T L →
      XOffData M T ∧ XOffCentU M T L ∧
        ((∀ F : Subgroup G, IsXOff M T F → (pCoreOf 2 M).relIndex F ≤ 4) ∨
          IsDoubleSL3U M T L)) : S38 := by
  intro G _ _ M T L h hb
  obtain ⟨hcent, hXL, hcases⟩ := h32 G M T L h
  by_cases h1 : IsSL3U M T L
  · exact Or.inl h1
  by_cases h2 : IsSp4U M T L
  · exact Or.inr h2
  exfalso
  have hbad : IsHatA6U M T L ∨ IsDoubleSL3U M T L ∨ IsSL3TwoU M T L ∨ IsSL3TwoZ M T L ∨
      IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1 := by
    rcases hcases with h' | h' | h' | h' | h' | ⟨k, hk⟩ | h'
    · exact absurd h' h1
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      rcases hk with ⟨rfl, hk'⟩ | hk''
      · exact Or.inl ⟨rfl, hk'⟩
      · exact absurd (h.isSp4U_of_isSp4DerSec hk''.1 (Or.inr hk'')) h2
    · exact (hG2 G M T L h hcent hXL h' hb).elim
  obtain ⟨hX, hXC, hXO⟩ := hD G M T L h hb hXL hbad h1 h2
  obtain ⟨h4, hstar⟩ := h.ms23_of_xOffData hb hX
  exact hEnd G M T L h hcent hXL hbad h1 h2 hX hXC hXO h4 hstar
    fun ε ε' hc => h.not_vv_le_qv_of_xOffData hb hX hc

end CFSG.Quasithin.MS93
