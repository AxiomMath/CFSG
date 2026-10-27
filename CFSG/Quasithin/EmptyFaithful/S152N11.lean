module

public import CFSG.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Quasithin.EmptyFaithful.S152NBasic
public import CFSG.Quasithin.EmptyFaithful.S152NMod
public import CFSG.Quasithin.EmptyFaithful.S152NFix

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S152N

open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_le_of_le_normalizer {V B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (V : Set G)) : ⁅V, B⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv b hb
  have h1 : b * v⁻¹ * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hB hb) _).mp (V.inv_mem hv)
  have h2 : ⁅v, b⁆ = v * (b * v⁻¹ * b⁻¹) := by
    rw [commutatorElement_def]; group
  rw [h2]
  exact V.mul_mem hv h1

end S152N

open S152N

variable {G : Type} [Group G] [Finite G]

theorem stageLemma15211_of (h15112 : StageLemma15112) (h15208 : StageLemma15208)
    (h15210 : StageLemma15210) (hord : Input15209Order) : StageLemma15211 := by
  intro G _ _ T Mc M hs H hH B hB
  have hTM : T ≤ M := hs.mf.1.1.2
  have hVe := isElemAbelian_V154 hs
  have hMN := le_normalizer_V154 T Mc M
  have hTN : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hTM.trans hMN
  have hTsyl := isSylowTwoOf_hStar hs hH
  obtain ⟨φ⟩ := h15208 G T Mc M hs H hH
  have hc := (h15112 G T Mc M hs.qtfe hs.mf hs.ce H hH).1
  obtain ⟨⟨A, hAΔ, hBA⟩, hBnot⟩ := hB
  have hord' := hord G T Mc M hs H hH A hAΔ
  have hAT : ¬ A ≤ T := fun hle => hBnot ⟨A, hAΔ, hle, hBA⟩
  subst hBA
  have hQT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hTsyl
  have hBT : A ⊓ pCoreOf 2 H ≤ T := inf_le_right.trans hQT
  have hBM : A ⊓ pCoreOf 2 H ≤ M := hBT.trans hTM
  have hBe : IsElemAbelian 2 (A ⊓ pCoreOf 2 H) := isElemAbelian_mono151 inf_le_left hAΔ.1.2.1
  have hVU : V154 T Mc M ≤ conjClosure (V154 T Mc M) H := le_conjClosure _ _
  have hAH : A ≤ H := hAΔ.1.1
  have hne : ⁅V154 T Mc M, A ⊓ pCoreOf 2 H⁆ ≠ ⊥ :=
    delta_commutator_ne_bot hs hH φ hc hAΔ hord' hAT
  have hquadA := delta_quadratic hAΔ
  have hquad : ⁅⁅V154 T Mc M, A ⊓ pCoreOf 2 H⁆, A ⊓ pCoreOf 2 H⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono (Subgroup.commutator_mono hVU inf_le_left)
      inf_le_left).trans hquadA.le)
  have hcount := delta_count hTsyl hAΔ hord' hc hne
  have hqM := mem_QsetOn_of_counts hVe hMN hBM hBe hne hcount hquad
  have hqT := mem_QsetOn_of_counts hVe hTN hBT hBe hne hcount hquad
  obtain ⟨-, -, hcard, hnorm⟩ := h15210 G T Mc M hs _ hqT
  rw [commutator_preOn_autOn hVe hTN hBT] at hcard hnorm
  have hZV : ⁅V154 T Mc M, A ⊓ pCoreOf 2 H⁆ ≤ V154 T Mc M :=
    commutator_le_of_le_normalizer (hBM.trans hMN)
  have hZe : IsElemAbelian 2 (⁅V154 T Mc M, A ⊓ pCoreOf 2 H⁆ : Subgroup G) :=
    isElemAbelian_mono151 hZV hVe
  have hAZ : A ≤ Subgroup.centralizer ((⁅V154 T Mc M, A ⊓ pCoreOf 2 H⁆ : Subgroup G) : Set G) := by
    exact le_centralizer_of_commutator_eq_bot (le_bot_iff.mp
      ((Subgroup.commutator_mono (Subgroup.commutator_mono hVU inf_le_left) le_rfl).trans
        hquadA.le))
  have hfix := normalizes_and_oTwoUpper_le_centralizer hTsyl
    (fun Y hTY hYH => eq_or_eq_of_le hTsyl φ hTY hYH) (relIndex_eq_nine hTsyl φ)
    (hZV.trans (V154_le_T hs)) hZe hcard hnorm hAH hAT hAZ
  exact ⟨hqM, hfix.2, hcard, hZe, hnorm⟩

end CFSG.Quasithin
