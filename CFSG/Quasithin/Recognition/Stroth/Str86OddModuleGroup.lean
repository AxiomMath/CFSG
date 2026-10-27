module

public import CFSG.Quasithin.Vol2.Ch3g316Red

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem relIndex_inf_le_relIndex_of_isMaxElemAbelian {T A Y R : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hYT : Y ≤ T) (hY : IsElemAbelian 2 Y) (hRA : R ≤ A)
    (hRY : R ≤ Subgroup.centralizer (Y : Set G)) :
    (Y ⊓ A).relIndex Y ≤ R.relIndex A := by
  have h := Ch3g316.relIndex_centralizer_le (T := T) (A := A) (U := Y) hA hYT hY
  have hL : (Subgroup.centralizer (A : Set G)).relIndex Y = (Y ⊓ A).relIndex Y := by
    calc (Subgroup.centralizer (A : Set G)).relIndex Y
        = (Y ⊓ Subgroup.centralizer (A : Set G)).relIndex Y :=
          (Subgroup.inf_relIndex_left Y (Subgroup.centralizer (A : Set G))).symm
      _ = (A ⊓ Y).relIndex Y := by
          rw [CFSG.QuasithinUnique.Setup.Campbell.maxElem_inf_centralizer_eq hA hYT hY]
      _ = (Y ⊓ A).relIndex Y := by rw [inf_comm]
  have hR : (Subgroup.centralizer (Y : Set G)).relIndex A =
      (A ⊓ Subgroup.centralizer (Y : Set G)).relIndex A :=
    (Subgroup.inf_relIndex_left A (Subgroup.centralizer (Y : Set G))).symm
  have hR0 : R.relIndex A ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_index hRA
    rw [h0, Nat.zero_mul] at h
    exact Subgroup.index_ne_zero_of_finite h.symm
  rw [hL, hR] at h
  exact h.trans (Subgroup.relIndex_le_of_le_left (le_inf hRA hRY) hR0)

private lemma g2_commutator_le_oTwoUpper {U X H : Subgroup G}
    (hXH : X ≤ H) (hXU : X ≤ Subgroup.centralizer (U : Set G))
    (hOX : oTwoUpper H ⊔ X = H) :
    ⁅U, H⁆ ≤ ⁅U, oTwoUpper H⁆ := by
  have hKPsup : ⁅U, oTwoUpper H ⊔ X⁆ ≤ ⁅U, oTwoUpper H⁆ := by
    refine Subgroup.commutator_le.mpr ?_
    intro u hu h hh
    change h ∈ (↑(oTwoUpper H ⊔ X) : Set G) at hh
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (oTwoUpper H) X
      (hXH.trans (le_normalizer_oTwoUpper H))] at hh
    obtain ⟨p, hp, x, hx, rfl⟩ := Set.mem_mul.1 hh
    have hux : ⁅u, x⁆ = 1 :=
      Subgroup.mem_centralizer_iff_commutator_eq_one.mp (hXU hx) u hu
    have hux' : u * x * u⁻¹ * x⁻¹ = 1 := by
      rw [← commutatorElement_def]
      exact hux
    have heq : ⁅u, p * x⁆ = ⁅u, p⁆ := by
      have h1 : u * (p * x) * u⁻¹ * (p * x)⁻¹ = u * p * u⁻¹ * p⁻¹ := by
        rw [mul_inv_rev]
        calc u * (p * x) * u⁻¹ * (x⁻¹ * p⁻¹)
            = (u * p * u⁻¹ * p⁻¹) * (p * (u * x * u⁻¹ * x⁻¹) * p⁻¹) := by
              group
          _ = u * p * u⁻¹ * p⁻¹ := by rw [hux']; group
      simpa only [commutatorElement_def] using h1
    rw [heq]
    exact Subgroup.commutator_mem_commutator hu hp
  simpa only [hOX] using hKPsup

private lemma g2_minimal_of_count_one {H U X : Subgroup G} (hU : IsPGroup 2 U)
    (hUX : U ≤ X) (hXH : X ≤ H) (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hXU : X ≤ Subgroup.centralizer (U : Set G)) (hOX : oTwoUpper H ⊔ X = H)
    (hUC : U ⊓ Subgroup.centralizer (H : Set G) = ⊥)
    (hchief : IsChiefSeriesFrom H U U 1) {K' : Subgroup G}
    (hK'norm : IsNormalIn H X K') (hK'K : K' ≤ ⁅U, H⁆) :
    K' = ⊥ ∨ K' = ⁅U, H⁆ := by
  have hKU : ⁅U, H⁆ ≤ U := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hHU
  by_cases hK'bot : K' = ⊥
  · exact Or.inl hK'bot
  · right
    have hK'U : K' ≤ U := hK'K.trans hKU
    have hHK' : H ≤ Subgroup.normalizer (K' : Set G) :=
      CFSG.Quasithin.D14.le_normalizer_of_isNormalIn hK'norm
    have hK'P_ne : ⁅K', oTwoUpper H⁆ ≠ ⊥ := by
      intro hbot
      have hK'centP : K' ≤ Subgroup.centralizer (oTwoUpper H : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      have hPcentK' : oTwoUpper H ≤ Subgroup.centralizer (K' : Set G) :=
        Subgroup.le_centralizer_iff.mpr hK'centP
      have hXcentK' : X ≤ Subgroup.centralizer (K' : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact Subgroup.mem_centralizer_iff.mp (hXU hx) k (hK'U hk)
      have hHcentK' : H ≤ Subgroup.centralizer (K' : Set G) := by
        rw [← hOX]
        exact sup_le hPcentK' hXcentK'
      have hle : K' ≤ U ⊓ Subgroup.centralizer (H : Set G) :=
        le_inf hK'U (Subgroup.le_centralizer_iff.mp hHcentK')
      rw [hUC] at hle
      exact hK'bot (le_bot_iff.mp hle)
    have hUPle : ⁅U, oTwoUpper H⁆ ≤ K' :=
      CFSG.Quasithin.D14.commutator_le_of_ne_bot hU (hUX.trans hXH) hHU hchief
        hK'U hHK' hK'P_ne
    exact le_antisymm hK'K
      ((g2_commutator_le_oTwoUpper hXH hXU hOX).trans hUPle)

theorem isChiefStep_commutator_of_count_one {H U X : Subgroup G} (hU : IsPGroup 2 U)
    (hUX : U ≤ X) (hXH : X ≤ H) (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hXU : X ≤ Subgroup.centralizer (U : Set G)) (hOX : oTwoUpper H ⊔ X = H)
    (hUC : U ⊓ Subgroup.centralizer (H : Set G) = ⊥) (hchief : IsChiefSeriesFrom H U U 1) :
    IsChiefStep H X ⊥ ⁅U, H⁆ ∧ ¬ IsCentralStep H ⊥ ⁅U, H⁆ := by
  classical
  have hKU : ⁅U, H⁆ ≤ U := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hHU
  have hKX : ⁅U, H⁆ ≤ X := hKU.trans hUX
  have hHK : H ≤ Subgroup.normalizer ((⁅U, H⁆ : Subgroup G) : Set G) :=
    CFSG.Quasithin.D14.le_normalizer_commutator hHU Subgroup.le_normalizer
  obtain ⟨K₀, L₀, hstep₀, -, -⟩ :=
    CFSG.Quasithin.D14.exists_chiefStep_of_one hU (hUX.trans hXH) hchief rfl
  have hU_ne : U ≠ ⊥ := bot_lt_iff_ne_bot.mp
    (lt_of_le_of_lt bot_le (lt_of_lt_of_le hstep₀.2.2.1 hstep₀.1.1))
  have hK_ne : ⁅U, H⁆ ≠ ⊥ := by
    intro hbot
    have hHU' : ⁅H, U⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hbot
    have hHcent : H ≤ Subgroup.centralizer (U : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hHU'
    apply hU_ne
    rw [eq_bot_iff]
    intro u hu
    have huC : u ∈ Subgroup.centralizer (H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact ((Subgroup.mem_centralizer_iff.mp (hHcent hh)) u hu).symm
    have hmem : u ∈ U ⊓ Subgroup.centralizer (H : Set G) := ⟨hu, huC⟩
    rwa [hUC] at hmem
  refine ⟨⟨⟨hKX, fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hHK hg) x).mp hx⟩,
    CFSG.Quasithin.D15Proof.isNormalIn_bot H X, bot_lt_iff_ne_bot.mpr hK_ne, ?_⟩, ?_⟩
  · intro K' hK' _ hK'K
    exact g2_minimal_of_count_one hU hUX hXH hHU hXU hOX hUC hchief hK' hK'K
  · intro hc
    have hHcent : H ≤ Subgroup.centralizer ((⁅U, H⁆ : Subgroup G) : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 : g * x * g⁻¹ * x⁻¹ = 1 := by
        have := hc g hg x hx
        rwa [Subgroup.mem_bot] at this
      have h2 : g * x * g⁻¹ = x := by
        have := congrArg (fun t => t * x) h1
        simpa [mul_assoc] using this
      calc x * g = (g * x * g⁻¹) * g := by rw [h2]
        _ = g * x := by group
    have hKcent : ⁅U, H⁆ ≤ Subgroup.centralizer (H : Set G) :=
      Subgroup.le_centralizer_iff.mp hHcent
    have hle : ⁅U, H⁆ ≤ U ⊓ Subgroup.centralizer (H : Set G) := le_inf hKU hKcent
    rw [hUC] at hle
    exact hK_ne (le_bot_iff.mp hle)

end CFSG.Quasithin.Stroth

end
