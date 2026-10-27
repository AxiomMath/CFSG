module

public import CFSG.Quasithin.EmptyFaithful.S151S9TKInputs
public import CFSG.Quasithin.EmptyFaithful.S151S9TLat
public import CFSG.Quasithin.EmptyFaithful.S151S9TCen
public import CFSG.Quasithin.Background.HSporLatMathieu
public import CFSG.Quasithin.Background.A3StructureDefs
import all CFSG.Quasithin.Background.HSporLatMathieu

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.H.MathieuLat CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m22a m22b card_M22)

section K

@[expose] noncomputable def m22CtxF (h : m22FactsK) :
    LatCtx ↥CFSG.Blueprint.NativeSporadic.M22 22 (List ℕ) :=
  LatFactsK.ctx codeSetLab_lawful m22_delta_valid m22_ta m22_tb CFSG.Sporadic.Mathieu.m22_hyp.gen
    m22_sGens.1 m22_sGens.2 3465 (by rw [card_M22]; norm_num) h.choose_spec.1

theorem m22F_S_sylow (h : m22FactsK) : IsSylowTwoOf (m22CtxF h).S ⊤ := by
  refine K1.isSylowTwoOf_top_iff.mpr ⟨(m22CtxF h).S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index (m22CtxF h).S
  rw [(m22CtxF h).S_card, card_M22] at h1
  have h2 : (m22CtxF h).S.index = 3465 := by
    have : (m22CtxF h).k = 7 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

theorem m22F_centre (h : m22FactsK) :
    ∃ z₀ : ↥CFSG.Blueprint.NativeSporadic.M22, orderOf z₀ = 2 ∧
      centerOf (m22CtxF h).S = Subgroup.zpowers z₀ ∧ (tab 22 z₀).toArray = m22SLP[163]! := by
  have hcert : BaseCertS 22 (List.range 22)
      (slpTabsA (tab 22 m22a).toArray (tab 22 m22b).toArray m22Prog) m22Qp
      163 205 209 207 211 m22Enum.1 m22Enum.2.1 m22Enum.2.2 7 := by
    rw [m22_ta, m22_tb]
    exact m22_cert
  obtain ⟨z₀, hz2, hZ, htab⟩ := centre_of_baseCertS (m22CtxF h) (show 0 < 7 by norm_num) m22a
    m22b m22Prog m22_valid m22Qp 163 205 209 207 211 m22Enum.1 m22Enum.2.1 m22Enum.2.2 7 hcert rfl
  refine ⟨z₀, hz2, hZ, ?_⟩
  rw [htab, m22_ta, m22_tb]
  rfl

theorem m22_idx3Model (h : m22FactsK) :
    Idx3Model ↥CFSG.Blueprint.NativeSporadic.M22 (m22CtxF h).S ((m22CtxF h).Y 2) := by
  obtain ⟨z₀, hz2, hZ, htab⟩ := m22F_centre h
  have hok : m22Wit.Ok 22 (m22CtxF h).A.act (m22CtxF h).Δ (m22CtxF h).D (tab 22 z₀).toArray := by
    rw [htab]
    exact h.choose_spec.2.2
  have hN : (m22CtxF h).D.O.lbl.size ≠ 3 := by
    have h3465 : (m22CtxF h).D.O.lbl.size = 3465 := LatFactsK.ctx_O_size ..
    rw [h3465]
    decide
  exact idx3Model_of_lat (m22CtxF h) (m22F_S_sylow h) hz2 hZ m22Wit hok
    (Ls := #[1, 45, 3, 15, 3]) h.choose_spec.2.1 (by decide) (by decide) hN (by decide)

theorem m22_threeD (h : m22FactsK) :
    ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G), CFSG.Quasithin.IsSporadic .M22 ↥L →
      IsPGroup 2 ↥S → S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L →
      ∀ z ∈ centerOf (S ⊓ L), ¬ L ≤ Subgroup.centralizer ({z} : Set G) →
        ∃ P : Subgroup G, P ≤ L ∧ S ⊓ L ≤ P ∧ S ≤ Subgroup.normalizer (P : Set G) ∧
          ¬ P ≤ Subgroup.centralizer ({z} : Set G) ∧ CharTwo P ∧
          IsMinParabolicOf (P ⊔ S) (P ⊔ S) ∧ NumC126 (P ⊔ S) ∧
          oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P := by
  intro G _ _ L S hL hS2 hSN hSyl z hz hnc
  obtain ⟨e₀⟩ := hL
  exact threeD_of_idx3Model hS2 hSN hSyl hz hnc (Γ := ↥CFSG.Blueprint.NativeSporadic.M22) e₀
    (m22_idx3Model h)

end K

end CFSG.Quasithin.S151S9T
