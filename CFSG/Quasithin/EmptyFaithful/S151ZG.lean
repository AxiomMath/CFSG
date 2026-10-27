module

public import CFSG.Quasithin.EmptyFaithful.S151ZD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

@[expose] def RankTwoSimpleNotA38 : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G), (IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L) →
    ¬ A38Types (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def Input15122ThreeCLat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L B : Subgroup G),
    (IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L) → IsSylowTwoOf B L →
      L ⊓ Subgroup.normalizer (B : Set G) ≤ B ∧
      IsMaxSubgroupIn L (L ⊓ Subgroup.centralizer (centerOf B : Set G)) ∧
      ∃ P : Subgroup G, IsMaxSubgroupIn L P ∧ B ≤ P ∧ B ≠ P ∧
        P ≠ L ⊓ Subgroup.centralizer (centerOf B : Set G) ∧
        (∀ K : Subgroup G, IsMaxSubgroupIn L K → B ≤ K →
          K = L ⊓ Subgroup.centralizer (centerOf B : Set G) ∨ K = P) ∧
        (∀ K : Subgroup G, B ≤ K → K ≤ P → K = B ∨ K = P)

@[expose] def Input15122ThreeCGood : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S P : Subgroup G),
    (IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L) → IsPGroup 2 ↥S → S ≤ Subgroup.normalizer (L : Set G) →
    IsSylowTwoOf (S ⊓ L) L → SMin L S P → ¬ P ≤ L ⊓ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) →
      CharTwo P ∧ ¬ C126Third (P ⊔ S) S ∧ oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P

@[expose] def Input15122ThreeCZL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120ThreeC T Mc Z₁ L → ZL2 (s1516 T Z₁) L

theorem input15122ThreeC_of (h118 : TheoremC118) (h126 : TheoremC126) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (kN : RankTwoSimpleNotA38) (hlat : Input15122ThreeCLat)
    (hgood : Input15122ThreeCGood) (hzl : Input15122ThreeCZL2) : Input15122ThreeC := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc h3C
  have h3C' := h3C
  obtain ⟨htype, hMLeq⟩ := h3C
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  set S := s1516 T Z₁ with hSdef
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hS2 : IsPGroup 2 ↥S := hc.h18.four.2.1
  have hsyl : IsSylowTwoOf (S ⊓ L) L := hc.h20.sylow
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := by
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
        (hSet.pCore_g1_ne_bot hq hMf) hc.hL.comp with hn | ⟨-, h2⟩
    · exact (s1516_le_g1 T Z₁).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn)
    · exact absurd h2 (kN G L htype)
  obtain ⟨hselfN, hMLmax, P, hPmax, hBP, hBPne, hPne, honly, hPmin⟩ := hlat G L (S ⊓ L) htype hsyl
  rw [← hMLeq] at hMLmax hPne honly
  have hSMZ : S ≤ mZ1516 Mc Z₁ := fun x hx => ⟨s1516_le_g1 T Z₁ hx, hq.t_le_mc (s1516_le T Z₁ hx)⟩
  have hSM : S ≤ M := (s1516_le T Z₁).trans hMf.1.1.2
  have hBML : S ⊓ L ≤ mZ1516 Mc Z₁ ⊓ L := inf_le_inf_right _ hSMZ
  have hSML : S ≤ Subgroup.normalizer ((mZ1516 Mc Z₁ ⊓ L : Subgroup G) : Set G) :=
    fun s hs => zb_mem_normalizer_inf (Subgroup.le_normalizer (hSMZ hs)) (hSN hs)
  have hSB : S ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    fun s hs => zb_mem_normalizer_inf (Subgroup.le_normalizer hs) (hSN hs)
  have hSP : S ≤ Subgroup.normalizer (P : Set G) := by
    intro s hs
    have hmax' := zb_isMax_conj (hSN hs) hPmax
    have hB' : S ⊓ L ≤ B6.conjSub s P := by
      intro x hx
      rw [B6.mem_conjSub]
      have hx' : s⁻¹ * x * s ∈ S ⊓ L := by
        have := (Subgroup.mem_normalizer_iff.mp (hSB (S.inv_mem hs)) x).mp hx
        simpa using this
      exact hBP hx'
    rcases honly _ hmax' hB' with h | h
    · exfalso
      apply hPne
      have h1 : B6.conjSub s⁻¹ (B6.conjSub s P) = B6.conjSub s⁻¹ (mZ1516 Mc Z₁ ⊓ L) := by rw [h]
      rwa [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one,
        B6.conjSub_eq_self (inv_mem (hSML hs))] at h1
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      have hxm : x ∈ P ↔ s * x * s⁻¹ ∈ P := by
        have h2 : s * x * s⁻¹ ∈ B6.conjSub s P ↔ s⁻¹ * (s * x * s⁻¹) * s ∈ P := B6.mem_conjSub
        rw [h] at h2
        simpa [mul_assoc] using h2.symm
      exact hxm
  have hPS : SMin L S P := ⟨hPmax.1.le, hBP, hBPne, hSP, fun K _ hBK hKP => hPmin K hBK hKP⟩
  have hPnot : ¬ P ≤ mZ1516 Mc Z₁ := by
    intro hPM
    have hPML : P ≤ mZ1516 Mc Z₁ ⊓ L := le_inf hPM hPmax.1.le
    rcases lt_or_eq_of_le hPML with hlt | heq
    · exact hMLmax.1.ne (hPmax.2 _ hlt inf_le_right)
    · exact hPne heq
  have hPnotML : ¬ P ≤ L ⊓ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) := by
    rw [← hMLeq]
    exact fun h => hPnot (h.trans inf_le_left)
  obtain ⟨hchP, hno, hoP⟩ := hgood G L S P htype hS2 hSN hsyl hPS hPnotML
  have hchH : CharTwo (P ⊔ S) := zb_charTwo_sup hSP hS2 hchP
  have hmin : IsMinParabolicOf (P ⊔ S) (P ⊔ S) := hPS.isMinParabolic hS2 hsyl hselfN
  have hPM : P ≤ M := (bang_of_good h118 h126 hc hPmax.1.le hchH hmin hno).resolve_right hPnot
  have hMLP : M ⊓ L = P := by
    have h1 : P ≤ M ⊓ L := le_inf hPM hPmax.1.le
    have h2 : M ⊓ L ≠ L := fun h => hc.h20.one (by rw [← h]; exact inf_le_left)
    rcases lt_or_eq_of_le h1 with hlt | heq
    · exact absurd (hPmax.2 _ hlt inf_le_right) h2
    · exact heq.symm
  have hMLpar : IsMaxParabolic2 L (mZ1516 Mc Z₁ ⊓ L) := by
    refine ⟨⟨inf_le_right, S ⊓ L, hsyl, hselfN.trans hBML⟩, hMLmax.1.ne, fun Q hQ hQne hMQ => ?_⟩
    rcases lt_or_eq_of_le hMQ with hlt | heq
    · exact absurd (hMLmax.2 _ hlt hQ.1) hQne
    · exact heq.symm
  refine ⟨htype, hMLeq, hMLpar, ?_, ?_, ?_⟩
  · rw [hMLP]
    refine ⟨⟨hPmax.1.le, S ⊓ L, hsyl, hselfN.trans hBP⟩, hPmax.1.ne, fun Q hQ hQne hPQ => ?_⟩
    rcases lt_or_eq_of_le hPQ with hlt | heq
    · exact absurd (hPmax.2 _ hlt hQ.1) hQne
    · exact heq.symm
  · rw [hMLP]
    exact fun h => hPne h.symm
  · exact centS15122_of hc hSN (hzl G T Mc M Z₁ Z₂ V₁ V₂ L hc h3C') (hMLP ▸ le_rfl) hPnot hoP

end CFSG.Quasithin
