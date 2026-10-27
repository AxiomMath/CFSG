module

public import CFSG.Quasithin.EmptyFaithful.S151ZB
public import CFSG.Quasithin.EmptyFaithful.S151ZA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem par2_le_M (h118 : TheoremC118) (h126 : TheoremC126)
    {T Mc M Z₁ Z₂ V₁ V₂ L P : Subgroup G} (hc : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hL : CharTwo L) (hpar : Par2 L (s1516 T Z₁) P) (hbig : ParBig L P)
    (hnot : ¬ P ≤ mZ1516 Mc Z₁) : P ≤ M := by
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hHG : P ⊔ s1516 T Z₁ ≤ g1_1516 Z₁ := sup_le (hpar.le.trans hLG) (s1516_le_g1 T Z₁)
  rcases star_general h118 h126 hc le_sup_right hHG (hpar.charTwo hL) hpar.isMinParabolic
      (hpar.not_C126Third hL hbig) with h | h
  · exact le_sup_left.trans h
  · exact (hnot (le_sup_left.trans h)).elim

structure OtherPar (L B M' P : Subgroup G) : Prop where
  max : IsMaxSubgroupIn L P
  ge : B ≤ P
  ne : P ≠ M'
  only : ∀ K : Subgroup G, IsMaxSubgroupIn L K → B ≤ K → K = M' ∨ K = P
  card3 : Nat.card ↥P = 3 * Nat.card ↥B
  nn : ¬ P ≤ Subgroup.normalizer (B : Set G)
  big : ParBig L P

@[expose] def Input15122Rank2Normal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120TwoB T Mc Z₁ L →
    (IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L) →
    s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G)

@[expose] def Input15122Rank2Lat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L B : Subgroup G),
    (IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L) → IsSylowTwoOf B L →
      L ⊓ Subgroup.normalizer (B : Set G) ≤ B ∧
      ∀ M' : Subgroup G, IsMaxSubgroupIn L M' → B ≤ M' → ∃ P : Subgroup G, OtherPar L B M' P

@[expose] def Input15122Rank2ZL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120TwoB T Mc Z₁ L →
    (IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L) → ZL2 (s1516 T Z₁) L

theorem input15122Rank2Block_of (h118 : TheoremC118) (h126 : TheoremC126)
    (hnorm : Input15122Rank2Normal) (hlat : Input15122Rank2Lat) (hzl : Input15122Rank2ZL2) :
    Input15122Rank2Block := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc h2B htype
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  set S := s1516 T Z₁ with hSdef
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hshort : IsShort2 L := by
    rcases htype with h | h | h
    · exact h.1
    · exact h.1
    · exact h.1
  have hLchar : CharTwo L := hshort.2.1
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := hnorm G T Mc M Z₁ Z₂ V₁ V₂ L hc h2B htype
  have hS2 : IsPGroup 2 ↥S := hc.h18.four.2.1
  have hsyl : IsSylowTwoOf (S ⊓ L) L := hc.h20.sylow
  obtain ⟨hselfN, hother⟩ := hlat G L (S ⊓ L) htype hsyl
  obtain ⟨hMLeq, hMLpar⟩ := h2B.2.2.1 hc.hL.comp htype
  have hSMZ : S ≤ mZ1516 Mc Z₁ := fun x hx => ⟨s1516_le_g1 T Z₁ hx, hq.t_le_mc (s1516_le T Z₁ hx)⟩
  have hBML : S ⊓ L ≤ mZ1516 Mc Z₁ ⊓ L := inf_le_inf_right _ hSMZ
  have hMLmax : IsMaxSubgroupIn L (mZ1516 Mc Z₁ ⊓ L) := by
    refine ⟨lt_of_le_of_ne inf_le_right hMLpar.2.1, fun K hK hKL => ?_⟩
    by_contra hKne
    have hKpar : IsParabolic2 L K := ⟨hKL, S ⊓ L, hsyl, hselfN.trans (hBML.trans hK.le)⟩
    exact hK.ne (hMLpar.2.2 K hKpar hKne hK.le).symm
  obtain ⟨P, hP⟩ := hother _ hMLmax hBML
  have hSML : S ≤ Subgroup.normalizer ((mZ1516 Mc Z₁ ⊓ L : Subgroup G) : Set G) :=
    fun s hs => zb_mem_normalizer_inf (Subgroup.le_normalizer (hSMZ hs)) (hSN hs)
  have hSB : S ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    fun s hs => zb_mem_normalizer_inf (Subgroup.le_normalizer hs) (hSN hs)
  have hSP : S ≤ Subgroup.normalizer (P : Set G) := by
    intro s hs
    have hmax' := zb_isMax_conj (hSN hs) hP.max
    have hB' : S ⊓ L ≤ B6.conjSub s P := by
      intro x hx
      rw [B6.mem_conjSub]
      have hx' : s⁻¹ * x * s ∈ S ⊓ L := by
        have := (Subgroup.mem_normalizer_iff.mp (hSB (S.inv_mem hs)) x).mp hx
        simpa using this
      exact hP.ge hx'
    rcases hP.only _ hmax' hB' with h | h
    · exfalso
      apply hP.ne
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
  have hpar : Par2 L S P := ⟨hS2, hSN, hsyl, hP.max.1.le, hP.ge, hSP, hP.card3, hP.nn⟩
  have hnot : ¬ P ≤ mZ1516 Mc Z₁ := by
    intro hPM
    have hPML : P ≤ mZ1516 Mc Z₁ ⊓ L := le_inf hPM hP.max.1.le
    rcases lt_or_eq_of_le hPML with hlt | heq
    · exact hMLpar.2.1 (hP.max.2 _ hlt inf_le_right)
    · exact hP.ne heq
  have hPM : P ≤ M := par2_le_M h118 h126 hc hLchar hpar hP.big hnot
  have hMLP : M ⊓ L = P := by
    have h1 : P ≤ M ⊓ L := le_inf hPM hP.max.1.le
    have h2 : M ⊓ L ≠ L := fun h => hc.h20.one (by rw [← h]; exact inf_le_left)
    rcases lt_or_eq_of_le h1 with hlt | heq
    · exact absurd (hP.max.2 _ hlt inf_le_right) h2
    · exact heq.symm
  refine ⟨htype, hMLeq, hMLpar, ?_, ?_, ?_⟩
  · rw [hMLP]
    refine ⟨⟨hP.max.1.le, S ⊓ L, hsyl, hselfN.trans hP.ge⟩, hP.max.1.ne, fun Q hQ hQne hPQ => ?_⟩
    rcases lt_or_eq_of_le hPQ with hlt | heq
    · exact absurd (hP.max.2 _ hlt hQ.1) hQne
    · exact heq.symm
  · rw [hMLP]
    exact fun h => hP.ne h.symm
  ·
    unfold CentS15122
    rw [hMLP]
    have hzl' : ZL2 S L := hzl G T Mc M Z₁ Z₂ V₁ V₂ L hc h2B htype
    have hZ₁T : Z₁ ≤ T := hSet.z1_le_T hq hMf
    have hZS : quasithinOmegaOneCenter T ≤ S := fun z hz =>
      ⟨(zb_omega_le_center T hz).1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp (zb_omega_le_center T hz).2 y (hZ₁T hy)⟩
    have hZc : ∀ z ∈ quasithinOmegaOneCenter T, ∀ c ∈ S, z * c = c * z := fun z hz c hc' =>
      (Subgroup.mem_centralizer_iff.mp (zb_omega_le_center T hz).2 c (s1516_le T Z₁ hc')).symm
    have hX : ¬ ∀ x ∈ oPrimeResidualOf 3 P, ∀ z ∈ quasithinOmegaOneCenter T, x * z = z * x := by
      intro hall
      apply hnot
      have hXML : oPrimeResidualOf 3 P ≤ mZ1516 Mc Z₁ ⊓ L := by
        rw [hMLeq]
        refine le_inf (zb_oPrime_le.trans hP.max.1.le) ?_
        intro x hx
        exact Subgroup.mem_centralizer_iff.mpr fun z hz => (hall x hx z hz).symm
      have hPeq : oPrimeResidualOf 3 P ⊔ S ⊓ L = P := zb_oPrime_sup_eq hP.ge hP.card3 (hS2.to_le inf_le_left)
      rw [← hPeq]
      exact (sup_le hXML hBML).trans inf_le_left
    exact centS_of_zl2 hSN hS2 (zb_oPrime_le.trans hP.max.1.le)
      (fun s hs => zb_normalizes_oPrime (hSP hs)) hZS (zb_omega_sq T) hZc hzl' hX

end CFSG.Quasithin
