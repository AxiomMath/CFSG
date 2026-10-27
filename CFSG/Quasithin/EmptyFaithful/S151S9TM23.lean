module

public import CFSG.Quasithin.EmptyFaithful.S151S9TM23Inputs
public import CFSG.Quasithin.EmptyFaithful.S151S9TLat
public import CFSG.Quasithin.EmptyFaithful.S151S9TCen
public import CFSG.Quasithin.Background.E2TwoProofSporM23
import CFSG.Quasithin.Background.HSporLatMathieu

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Quasithin.E2P.SporB CFSG.Quasithin.H.MathieuLat
open CFSG.Sporadic.Schreier (m23GenA m23GenB)

@[expose] def m23CheckD :
    Prop :=
  m23Wit.Ok 23 (codeSetAct 23) m23Delta m23CtxB.D m23SLP[159]!

theorem m23B_S_sylow :
    IsSylowTwoOf m23CtxB.S ⊤ := by
  have hN : m23CtxB.D.O.lbl.size = 79695 := m23_lat_cert.2.1
  refine K1.isSylowTwoOf_top_iff.mpr ⟨m23CtxB.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index m23CtxB.S
  rw [m23CtxB.S_card, m23CtxB.hΓ, hN] at h1
  have h2 : m23CtxB.S.index = 79695 := by
    have : m23CtxB.k = 7 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

theorem m23B_centre :
    ∃ z₀ : ↥CFSG.Blueprint.NativeSporadic.M23, orderOf z₀ = 2 ∧
      centerOf m23CtxB.S = Subgroup.zpowers z₀ ∧ (tab 23 z₀).toArray = m23SLP[159]! := by
  have hc : BaseCertS 23 (List.range 23)
      (slpTabsA (tab 23 m23GenA).toArray (tab 23 m23GenB).toArray m23Prog) m23Qp
      159 199 203 201 205 m23Enum.1 m23Enum.2.1 m23Enum.2.2 7 := by
    rw [m23_ta, m23_tb]
    exact m23_cert
  obtain ⟨z₀, hz2, hZ, hzT⟩ := centre_of_baseCertS m23CtxB (by show 0 < 7; norm_num) m23GenA
    m23GenB m23Prog m23_valid m23Qp 159 199 203 201 205 m23Enum.1 m23Enum.2.1 m23Enum.2.2 7 hc rfl
  exact ⟨z₀, hz2, hZ, by rw [hzT, m23_ta, m23_tb]; rfl⟩

@[expose] def m23Ls : Array ℕ := #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9]

theorem m23_tiebreak : ∀ j < 16, m23Ls[j]! = 3 → j ≠ 10 → m23Wit.czv[j]! ≠ true →
    1 ∉ m23Incl[j]! := by
  decide

theorem m23_idx3Model
    (h : m23CheckD) :
    Idx3Model ↥CFSG.Blueprint.NativeSporadic.M23 m23CtxB.S (m23CtxB.Y 10) := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := m23B_centre
  have hok : m23Wit.Ok 23 m23CtxB.A.act m23CtxB.Δ m23CtxB.D (tab 23 z₀).toArray := by
    rw [hzT]
    exact h
  have hL : m23CtxB.D.Om.map (fun o => o.lbl.size) = m23Ls := m23_lat_cert.2.2
  have hN : m23CtxB.D.O.lbl.size = 79695 := m23_lat_cert.2.1
  have hpq : m23CtxB.Y 10 ≤ m23CtxB.Y 1 :=
    (m23_Y_le_iff (j := 10) (jj := 1) (by norm_num) (by norm_num)).mpr (by decide)
  have huniq : ∀ j < m23Ls.size, m23Ls[j]! = 3 → j ≠ m23Wit.p →
      m23Wit.czv[j]! = true ∨ ¬ m23CtxB.Y j ≤ m23CtxB.Y 1 := by
    intro j hj hj3 hjp
    have hj16 : j < 16 := hj
    by_cases hc : m23Wit.czv[j]! = true
    · exact Or.inl hc
    · refine Or.inr fun hle => ?_
      exact m23_tiebreak j hj16 hj3 hjp hc ((m23_Y_le_iff hj16 (by norm_num)).mp hle)
  exact idx3Model_of_lat_incl m23CtxB m23B_S_sylow hz2 hZ m23Wit hok hL (by decide) (by decide)
    (by rw [hN]; norm_num) (q := 1) (by decide) (by decide) (by rw [hN]; decide) hpq huniq

theorem m23_threeD
    (h : m23CheckD) :
    ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G), IsSporadic .M23 ↥L → IsPGroup 2 ↥S →
      S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L →
      ∀ z ∈ centerOf (S ⊓ L), ¬ L ≤ Subgroup.centralizer ({z} : Set G) →
        ∃ P : Subgroup G, P ≤ L ∧ S ⊓ L ≤ P ∧ S ≤ Subgroup.normalizer (P : Set G) ∧
          ¬ P ≤ Subgroup.centralizer ({z} : Set G) ∧ CharTwo P ∧
          IsMinParabolicOf (P ⊔ S) (P ⊔ S) ∧ NumC126 (P ⊔ S) ∧
          oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P := by
  intro G _ _ L S hL hS2 hSN hSyl z hz hnc
  obtain ⟨e₀⟩ := hL
  exact threeD_of_idx3Model (Γ := ↥CFSG.Blueprint.NativeSporadic.M23) hS2 hSN hSyl hz hnc e₀
    (m23_idx3Model h)

end CFSG.Quasithin.S151S9T
