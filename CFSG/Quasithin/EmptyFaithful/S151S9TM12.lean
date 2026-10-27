module

public import CFSG.Quasithin.EmptyFaithful.S151S9TKInputs
public import CFSG.Quasithin.EmptyFaithful.S151S9TLat
public import CFSG.Quasithin.EmptyFaithful.S151S9TCen
public import CFSG.Quasithin.Background.HSporLatMathieu
import all CFSG.Quasithin.Background.HSporLatMathieu

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Quasithin.H.MathieuLat
open CFSG.Sporadic.Mathieu (m12a m12b)

section K

@[expose] noncomputable def m12CtxF (h : m12FactsK) :
    LatCtx ↥CFSG.Blueprint.NativeSporadic.M12 12 (List ℕ) :=
  LatFactsK.ctx codeSetLab_lawful m12_delta_valid m12_ta m12_tb CFSG.Sporadic.Mathieu.m12_hyp.gen
    m12_sGens.1 m12_sGens.2 1485 (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num)
    h.choose_spec.1

theorem m12F_S_sylow (h : m12FactsK) : IsSylowTwoOf (m12CtxF h).S ⊤ := by
  have hN : (m12CtxF h).D.O.lbl.size = 1485 := LatFactsK.ctx_O_size ..
  refine K1.isSylowTwoOf_top_iff.mpr ⟨(m12CtxF h).S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index (m12CtxF h).S
  rw [(m12CtxF h).S_card, (m12CtxF h).hΓ, hN] at h1
  have h2 : (m12CtxF h).S.index = 1485 := by
    have : (m12CtxF h).k = 6 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

theorem m12F_centre (h : m12FactsK) :
    ∃ z₀ : ↥CFSG.Blueprint.NativeSporadic.M12, orderOf z₀ = 2 ∧
      centerOf (m12CtxF h).S = Subgroup.zpowers z₀ ∧ (tab 12 z₀).toArray = m12SLP[153]! := by
  have hc : BaseCertS 12 (List.range 12)
      (slpTabsA (tab 12 m12a).toArray (tab 12 m12b).toArray m12Prog) m12Qp
      153 204 208 206 210 m12Enum.1 m12Enum.2.1 m12Enum.2.2 6 := by
    rw [m12_ta, m12_tb]
    exact m12_cert
  obtain ⟨z₀, hz2, hZ, hzT⟩ := centre_of_baseCertS (m12CtxF h) (by show 0 < 6; decide) m12a m12b
    m12Prog m12_valid m12Qp 153 204 208 206 210 m12Enum.1 m12Enum.2.1 m12Enum.2.2 6 hc rfl
  exact ⟨z₀, hz2, hZ, by rw [hzT, m12_ta, m12_tb]; rfl⟩

theorem m12_idx3Model (h : m12FactsK) :
    Idx3Model ↥CFSG.Blueprint.NativeSporadic.M12 (m12CtxF h).S ((m12CtxF h).Y 2) := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := m12F_centre h
  have hok : m12Wit.Ok 12 (m12CtxF h).A.act (m12CtxF h).Δ (m12CtxF h).D (tab 12 z₀).toArray := by
    rw [hzT]
    exact h.choose_spec.2.2
  have hN : (m12CtxF h).D.O.lbl.size = 1485 := LatFactsK.ctx_O_size ..
  exact idx3Model_of_lat (m12CtxF h) (m12F_S_sylow h) hz2 hZ m12Wit hok h.choose_spec.2.1
    (by decide) (by decide) (by rw [hN]; decide) (by decide)

theorem m12_threeD (h : m12FactsK) :
    ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G), IsSporadic .M12 ↥L → IsPGroup 2 ↥S →
      S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L →
      ∀ z ∈ centerOf (S ⊓ L), ¬ L ≤ Subgroup.centralizer ({z} : Set G) →
        ∃ P : Subgroup G, P ≤ L ∧ S ⊓ L ≤ P ∧ S ≤ Subgroup.normalizer (P : Set G) ∧
          ¬ P ≤ Subgroup.centralizer ({z} : Set G) ∧ CharTwo P ∧
          IsMinParabolicOf (P ⊔ S) (P ⊔ S) ∧ NumC126 (P ⊔ S) ∧
          oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P := by
  intro G _ _ L S hL hS2 hSN hSyl z hz hnc
  obtain ⟨e₀⟩ := hL
  have e₁ : ↥L ≃* ↥CFSG.Blueprint.NativeSporadic.M12 := e₀
  exact threeD_of_idx3Model hS2 hSN hSyl hz hnc e₁ (m12_idx3Model h)

end K

end CFSG.Quasithin.S151S9T
