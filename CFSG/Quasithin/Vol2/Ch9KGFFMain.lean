module

public import CFSG.Quasithin.Vol2.Ch9KGFFB51
public import CFSG.Quasithin.Vol2.Ch9Sec4Facts
public import CFSG.Quasithin.Vol2.Ch9KGFFC

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def A314FFCohomParabFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y T K KY U U₀ : Subgroup G) (v : G), SQTKGroup ↥Y →
    IsSylowTwoOf T Y → K ≤ Y → K ∈ lFamily T → T ≤ Subgroup.normalizer (K : Set G) →
    Nonempty (O2Q K ≃* alternatingGroup (Fin 5)) → KY ∈ cComp Y → K < KY →
    Y ≤ Subgroup.normalizer (KY : Set G) → IsTwoReducedIn Y U →
    ¬ ⁅KY, thompsonJ T⁆ ≤ Subgroup.centralizer (U : Set G) →
    ¬ KY ≤ K ⊔ (KY ⊓ Subgroup.centralizer (U : Set G)) →
    (IsPSp4 2 2 (O2Q KY) ∨ IsG2 2 2 (O2Q KY)) →
    U₀ ≤ U → U₀ ≤ ⁅U₀, K⁆ → pCoreOf 2 K ≤ Subgroup.centralizer (U₀ : Set G) →
    v ∈ U₀ → v ≠ 1 → KY ≤ Subgroup.centralizer ({v} : Set G) → False

theorem a314FFCohomFact_of
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts) (h51 : AsB51) (h56 : AsB56)
    (hP : A314FFCohomParabFact) : A314FFCohomFact := by
  intro G _ _ Y T K KY U U₀ v hSQ hT hKY hKl hTK hA5 hKYc hlt hYKY hred hJ hnK hU₀ hU₀K hO2K
    hv hv1 hKYv
  have : IsMulCommutative ↥U := hred.2.2.1.1
  have hKYY : KY ≤ Y := le_of_mem_cComp hKYc
  have hKYN : KY ≤ Subgroup.normalizer (U : Set G) := hKYY.trans hred.2.1
  have hKU : ¬ K ≤ Subgroup.centralizer (U : Set G) := by
    intro hKC
    have h0 : ⁅U₀, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (Subgroup.mem_centralizer_iff.mp (hKC hk) u (hU₀ hu)).symm
    have := hU₀K hv
    rw [h0, Subgroup.mem_bot] at this
    exact hv1 this
  obtain ⟨hqKY, hqA, hlist, h60, -, hcase⟩ :=
    KGFF.kyStar_cases h36 h312 h314 h56 hSQ hT hKY hKl hTK hA5 hKYc hlt hYKY hred hJ hnK hKU
  rcases hcase with hSL | hSp | hG2 | hA7
  · exact KGFF.false_of_isIntDirect hKYN hlt.le
      (KGFF.isIntDirect_of_sl34 h51 h56 hSQ hT hKYc hYKY hred hJ hqKY hqA hlist h60 hSL)
      hU₀ hU₀K hv hv1 hKYv
  · exact hP G Y T K KY U U₀ v hSQ hT hKY hKl hTK hA5 hKYc hlt hYKY hred hJ hnK (Or.inl hSp)
      hU₀ hU₀K hO2K hv hv1 hKYv
  · exact hP G Y T K KY U U₀ v hSQ hT hKY hKl hTK hA5 hKYc hlt hYKY hred hJ hnK (Or.inr hG2)
      hU₀ hU₀K hO2K hv hv1 hKYv
  · exact KGFF.false_of_isIntDirect hKYN hlt.le
      (FFD.b51_alt7 h51 h56 hSQ hT le_rfl hKYY hYKY hred hA7 hJ).1 hU₀ hU₀K hv hv1 hKYv

end CFSG.Quasithin.H13.Ch9
