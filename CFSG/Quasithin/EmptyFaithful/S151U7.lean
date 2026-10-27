module

public import CFSG.Quasithin.EmptyFaithful.S151U6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

@[expose] def Input15122L3WreathStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L P : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120TwoB T Mc Z₁ L → IsLnBlock L 3 →
    ¬ s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) →
    Par2 L (s1516 T Z₁ ⊓ Subgroup.normalizer (L : Set G)) P → ParBig L P →
    ¬ P ≤ mZ1516 Mc Z₁ → P ≤ M

variable {G : Type} [Group G] [Finite G]

theorem s151u_rank2Block_pt
    (h37 : A37ForSQTK)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L)
    (h2B : Case15120TwoB T Mc Z₁ L) (htype : IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L)
    (hstar : ∀ P : Subgroup G,
      Par2 L (s1516 T Z₁ ⊓ Subgroup.normalizer (L : Set G)) P → ParBig L P →
        ¬ P ≤ mZ1516 Mc Z₁ → P ≤ M) :
    Case15122Two T M Mc Z₁ L := by
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  obtain ⟨SH, hSHdef⟩ : ∃ SH : Subgroup G, SH = s1516 T Z₁ ⊓ Subgroup.normalizer (L : Set G) :=
    ⟨_, rfl⟩
  have hSHS : SH ≤ s1516 T Z₁ := by
    rw [hSHdef]
    exact inf_le_left
  have hSHN : SH ≤ Subgroup.normalizer (L : Set G) := by
    rw [hSHdef]
    exact inf_le_right
  have hstar' : ∀ P : Subgroup G, Par2 L SH P → ParBig L P → ¬ P ≤ mZ1516 Mc Z₁ → P ≤ M := by
    intro P h1 h2 h3
    rw [hSHdef] at h1
    exact hstar P h1 h2 h3
  have hSHL : SH ⊓ L = s1516 T Z₁ ⊓ L := by
    rw [hSHdef]
    exact s151u_inf_normalizer_inf _ _
  have hshort : IsShort2 L := by
    rcases htype with h | h | h
    · exact h.1
    · exact h.1
    · exact h.1
  have hS2 : IsPGroup 2 ↥(s1516 T Z₁) := hc.h18.four.2.1
  have hSH2 : IsPGroup 2 ↥SH := hS2.to_le hSHS
  have hsyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := hc.h20.sylow
  obtain ⟨hselfN, hother⟩ := input15122Rank2Lat_holds G L (s1516 T Z₁ ⊓ L) htype hsyl
  have hselfN' : L ⊓ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) ≤
      s1516 T Z₁ ⊓ L := hselfN
  obtain ⟨hMLeq, hMLpar⟩ := h2B.2.2.1 hc.hL.comp htype
  have hSMZ : s1516 T Z₁ ≤ mZ1516 Mc Z₁ := fun x hx =>
    ⟨s1516_le_g1 T Z₁ hx, hq.t_le_mc (s1516_le T Z₁ hx)⟩
  have hBML : s1516 T Z₁ ⊓ L ≤ mZ1516 Mc Z₁ ⊓ L := inf_le_inf_right _ hSMZ
  have hMLmax : IsMaxSubgroupIn L (mZ1516 Mc Z₁ ⊓ L) := by
    refine ⟨lt_of_le_of_ne inf_le_right hMLpar.2.1, fun K hK hKL => ?_⟩
    by_contra hKne
    have hKpar : IsParabolic2 L K := ⟨hKL, s1516 T Z₁ ⊓ L, hsyl, hselfN'.trans (hBML.trans hK.le)⟩
    exact hK.ne (hMLpar.2.2 K hKpar hKne hK.le).symm
  obtain ⟨P, hP⟩ := hother _ hMLmax hBML
  have hSHML : SH ≤ Subgroup.normalizer ((mZ1516 Mc Z₁ ⊓ L : Subgroup G) : Set G) :=
    fun s hs => zb_mem_normalizer_inf (Subgroup.le_normalizer (hSMZ (hSHS hs))) (hSHN hs)
  have hSHB : SH ≤ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) :=
    fun s hs => zb_mem_normalizer_inf (Subgroup.le_normalizer (hSHS hs)) (hSHN hs)
  have hSHP : SH ≤ Subgroup.normalizer (P : Set G) := by
    intro s hs
    have hmax' := zb_isMax_conj (hSHN hs) hP.max
    have hB' : s1516 T Z₁ ⊓ L ≤ B6.conjSub s P := by
      intro x hx
      rw [B6.mem_conjSub]
      have hx' : s⁻¹ * x * s ∈ s1516 T Z₁ ⊓ L := by
        have := (Subgroup.mem_normalizer_iff.mp (hSHB (SH.inv_mem hs)) x).mp hx
        simpa using this
      exact hP.ge hx'
    rcases hP.only _ hmax' hB' with h | h
    · exfalso
      apply hP.ne
      have h1 : B6.conjSub s⁻¹ (B6.conjSub s P) = B6.conjSub s⁻¹ (mZ1516 Mc Z₁ ⊓ L) := by rw [h]
      rwa [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one,
        B6.conjSub_eq_self (inv_mem (hSHML hs))] at h1
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      have hxm : x ∈ P ↔ s * x * s⁻¹ ∈ P := by
        have h2 : s * x * s⁻¹ ∈ B6.conjSub s P ↔ s⁻¹ * (s * x * s⁻¹) * s ∈ P := B6.mem_conjSub
        rw [h] at h2
        simpa [mul_assoc] using h2.symm
      exact hxm
  have hpar : Par2 L SH P := by
    refine ⟨hSH2, hSHN, ?_, hP.max.1.le, ?_, hSHP, ?_, ?_⟩
    · rw [hSHL]
      exact hsyl
    · rw [hSHL]
      exact hP.ge
    · rw [hSHL]
      exact hP.card3
    · rw [hSHL]
      exact hP.nn
  have hnot : ¬ P ≤ mZ1516 Mc Z₁ := by
    intro hPM
    have hPML : P ≤ mZ1516 Mc Z₁ ⊓ L := le_inf hPM hP.max.1.le
    rcases lt_or_eq_of_le hPML with hlt | heq
    · exact hMLpar.2.1 (hP.max.2 _ hlt inf_le_right)
    · exact hP.ne heq
  have hPM : P ≤ M := hstar' P hpar hP.big hnot
  have hMLP : M ⊓ L = P := by
    have h1 : P ≤ M ⊓ L := le_inf hPM hP.max.1.le
    have h2 : M ⊓ L ≠ L := fun h => hc.h20.one (by rw [← h]; exact inf_le_left)
    rcases lt_or_eq_of_le h1 with hlt | heq
    · exact absurd (hP.max.2 _ hlt inf_le_right) h2
    · exact heq.symm
  refine ⟨htype, hMLeq, hMLpar, ?_, ?_, ?_⟩
  · rw [hMLP]
    refine ⟨⟨hP.max.1.le, s1516 T Z₁ ⊓ L, hsyl, hselfN'.trans hP.ge⟩, hP.max.1.ne,
      fun Q hQ hQne hPQ => ?_⟩
    rcases lt_or_eq_of_le hPQ with hlt | heq
    · exact absurd (hP.max.2 _ hlt hQ.1) hQne
    · exact heq.symm
  · rw [hMLP]
    exact fun h => hP.ne h.symm
  ·
    unfold CentS15122
    rw [hMLP]
    have hpc : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := hSet.pCore_g1_ne_bot hq hMf
    have hZ₁T : Z₁ ≤ T := hSet.z1_le_T hq hMf
    have hZS : quasithinOmegaOneCenter T ≤ s1516 T Z₁ := fun z hz =>
      ⟨(zb_omega_le_center T hz).1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp (zb_omega_le_center T hz).2 y (hZ₁T hy)⟩
    have hZc : ∀ z ∈ quasithinOmegaOneCenter T, ∀ c ∈ s1516 T Z₁, z * c = c * z := fun z hz c hc' =>
      (Subgroup.mem_centralizer_iff.mp (zb_omega_le_center T hz).2 c (s1516_le T Z₁ hc')).symm
    have hZN : quasithinOmegaOneCenter T ≤ Subgroup.normalizer (L : Set G) := by
      intro z hz
      refine s151u_mem_normalizer_of_comm hq.qtke hq.simple hq.nonabelian h37 hpc hc.hL.comp hsyl
        hselfN' (s1516_le_g1 T Z₁ (hZS hz)) ?_
      intro c hc'
      have h1 : z * c * z⁻¹ * c⁻¹ = 1 := by
        rw [hZc z hz c hc'.1]
        group
      rw [commutatorElement_def, h1]
      exact Subgroup.one_mem _
    have hzl' : ZL2 SH L := by
      rw [hSHdef]
      exact s151u_zl2_SH hc htype
    have hZSH : quasithinOmegaOneCenter T ≤ SH := by
      rw [hSHdef]
      exact fun z hz => ⟨hZS hz, hZN hz⟩
    have hZc' : ∀ z ∈ quasithinOmegaOneCenter T, ∀ c ∈ SH, z * c = c * z := fun z hz c hc' =>
      hZc z hz c (hSHS hc')
    have hX : ¬ ∀ x ∈ oPrimeResidualOf 3 P, ∀ z ∈ quasithinOmegaOneCenter T, x * z = z * x := by
      intro hall
      apply hnot
      have hXML : oPrimeResidualOf 3 P ≤ mZ1516 Mc Z₁ ⊓ L := by
        rw [hMLeq]
        refine le_inf (zb_oPrime_le.trans hP.max.1.le) ?_
        intro x hx
        exact Subgroup.mem_centralizer_iff.mpr fun z hz => (hall x hx z hz).symm
      have hPeq : oPrimeResidualOf 3 P ⊔ s1516 T Z₁ ⊓ L = P :=
        zb_oPrime_sup_eq hP.ge hP.card3 (hS2.to_le inf_le_left)
      rw [← hPeq]
      exact (sup_le hXML hBML).trans inf_le_left
    have hcentSH := centS_of_zl2 hSHN hSH2 (zb_oPrime_le.trans hP.max.1.le)
      (fun s hs => zb_normalizes_oPrime (hSHP hs)) hZSH (zb_omega_sq T) hZc' hzl' hX
    apply le_antisymm
    · intro d hd
      have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
        s151u_cent_le_normalizer hq.qtke hq.simple hq.nonabelian h37 hpc hc.hL.comp hsyl
          hP.max.1.le hP.ge hP.card3 hP.nn (s1516_le_g1 T Z₁ hd.1)
          (fun x hx => (Subgroup.mem_centralizer_iff.mp hd.2 x hx).symm)
      have hdSH : d ∈ SH := by
        rw [hSHdef]
        exact ⟨hd.1, hdN⟩
      exact ⟨hd.1, (hcentSH.le ⟨hdSH, hd.2⟩).2⟩
    · exact inf_le_inf_left _ (Subgroup.centralizer_le
        (SetLike.coe_subset_coe.mpr (zb_oPrime_le.trans hP.max.1.le)))

theorem input15122Rank2Block_of_wreath
    (h118 : TheoremC118) (h126 : TheoremC126) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (hwr : Input15122L3WreathStar) : Input15122Rank2Block := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc h2B htype
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hshort : IsShort2 L := by
    rcases htype with h | h | h
    · exact h.1
    · exact h.1
    · exact h.1
  have hLchar : CharTwo L := hshort.2.1
  have key : ¬ A38Types (↥L ⧸ CFSG.pCore 2 ↥L) → s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := by
    intro hnot
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
        (hSet.pCore_g1_ne_bot hq hMf) hc.hL.comp with hn | ⟨-, h2⟩
    · exact (s1516_le_g1 T Z₁).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn)
    · exact absurd h2 hnot
  refine s151u_rank2Block_pt h37 hc h2B htype ?_
  intro P hpar hbig hnot
  by_cases hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G)
  · rw [inf_eq_left.mpr hSN] at hpar
    exact par2_le_M h118 h126 hc hLchar hpar hbig hnot
  · rcases htype with h3 | h6 | hg
    · exact hwr G T Mc M Z₁ Z₂ V₁ V₂ L P hc h2B h3 hSN hpar hbig hnot
    · obtain ⟨-, α, hα⟩ := h6
      exact absurd (key (a6NotA38Type_holds G L ⟨α, hα.1, hα.2.1⟩)) hSN
    · exact absurd (key (g2NotA38Type_holds G L hg.2.1)) hSN

end CFSG.Quasithin
