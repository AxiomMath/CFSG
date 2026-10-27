module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFlip4Cuts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFlip4Cent
public import CFSG.Quasithin.EmptyFaithful.S151S0
public import CFSG.Quasithin.EmptyFaithful.T1515eA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Pointwise commutatorElement

theorem flip4_star_all {G : Type} [Group G] [Finite G] (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h36 : A36ForSQTK) (hF : A318Facts) (kN : L45NotA38Type)
    (hl42 : ∀ (X : Type) [Group X] [Finite X], IsPSL 4 2 1 X → A318Exclusion X)
    {T Mc M Z₁ Z₂ V₁ V₂ L P : Subgroup G} (hc : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hsmall : Ce15Small T Mc M) (h3E : Case15120ThreeE T Mc Z₁ L) (h4 : IsPSL 4 2 1 ↥L)
    (hfl : ¬ SActsTrivially L (s1516 T Z₁)) (hP : SMin L (s1516 T Z₁) P) :
    P ≤ M ∨ P ≤ mZ1516 Mc Z₁ := by
  obtain ⟨htype, hMLpar, hMLne, hCML⟩ := h3E
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  set S := s1516 T Z₁ with hSdef
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hsyl : IsSylowTwoOf (S ⊓ L) L := hc.h20.sylow
  have htypeq : IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) :=
    htype.imp (isPSL_quotient_pCore (by norm_num)) (isPSL_quotient_pCore (by norm_num))
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := by
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
        (hSet.pCore_g1_ne_bot hq hMf) hc.hL.comp with hn | ⟨-, h2⟩
    · exact (s1516_le_g1 T Z₁).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn)
    · exact absurd h2 (kN G L htypeq)
  have hY : ¬ oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) ≤ mZ1516 Mc Z₁ := (hSet.y_facts hsmall).1.2.1
  have hLeq : L = oPrimeResidualOf 3 (g1_1516 Z₁) := by
    obtain ⟨S', _, _, ⟨e⟩, hS'⟩ := exists_model_of_exclusion_self (hl42 ↥L h4)
    have hpc : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := hSet.pCore_g1_ne_bot hq hMf
    have hH : SQTKGroup ↥(g1_1516 Z₁) :=
      sqtkGroup_of_pCoreOf_ne_bot hq.qtke hq.simple hq.nonabelian hpc
    exact eq_oPrimeResidualOf_three_of_exclusion hF h36 h38 hH hc.hL.comp hc.hL.quasi e hS'
  have hYL : oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) ≤ L :=
    hLeq ▸ oPrimeResidualOf_mono1516 3 (inf_le_right : M ⊓ g1_1516 Z₁ ≤ g1_1516 Z₁)
  have hYM : oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) ≤ M :=
    (Subgroup.closure_le M).mpr fun _ hx => hx.1.1
  have hYK : oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) ≤ M ⊓ L := le_inf hYM hYL
  have hKnotML : ¬ M ⊓ L ≤ mZ1516 Mc Z₁ ⊓ L := fun h => hY fun y hy => (h (hYK hy)).1
  have hSM : S ≤ M := (s1516_le T Z₁).trans hMf.1.1.2
  have hSMZ : S ≤ mZ1516 Mc Z₁ := s1516_le_mZ1516 hc.h18
  have hKS : S ≤ Subgroup.normalizer ((M ⊓ L : Subgroup G) : Set G) := fun s hs =>
    zb_mem_normalizer_inf (Subgroup.le_normalizer (hSM hs)) (hSN hs)
  have hMLS : S ≤ Subgroup.normalizer ((mZ1516 Mc Z₁ ⊓ L : Subgroup G) : Set G) := fun s hs =>
    zb_mem_normalizer_inf (Subgroup.le_normalizer (hSMZ hs)) (hSN hs)
  have hBK : S ⊓ L ≤ M ⊓ L := le_inf (inf_le_left.trans hSM) inf_le_right
  have hBM : S ⊓ L ≤ mZ1516 Mc Z₁ ⊓ L := le_inf (inf_le_left.trans hSMZ) inf_le_right
  have hKL' : M ⊓ L ≠ L := fun h => hc.h20.one (by rw [← h]; exact inf_le_left)
  have hKB : M ⊓ L ≠ S ⊓ L := fun h => hKnotML (h ▸ hBM)
  obtain ⟨e₀⟩ := nonempty_equiv_SLt_of_isPSL h4
  obtain ⟨D'⟩ := exists_borelIso (n := 4) (by norm_num) hsyl e₀
  let D : SurjBorel 4 L (S ⊓ L) := borelIso_toSurjBorel D' hsyl.1
  have hk : ∀ s ∈ S, ∀ hs : s ∈ Subgroup.normalizer (L : Set G), ∀ x : ↥L, D.e x = 1 →
      D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) = 1 := by
    intro s hs hsN x hx
    have hx' : D'.e x = 1 := hx
    have : x = 1 := (MulEquiv.map_eq_one_iff D'.e).mp hx'
    subst this
    rw [map_one, map_one]
  have hMLB : mZ1516 Mc Z₁ ⊓ L ≠ S ⊓ L := by
    intro h
    obtain ⟨x, hxL, hxC, hxB⟩ := flip4_cent_not_le hsyl.1 D'
    exact hxB (h ▸ hCML ⟨hxL, hxC⟩)
  obtain ⟨s₀, hs₀, hfl₀⟩ := flip4_exists_flip rfl D hSN hk hfl
  rcases flip4_smin_cases rfl D hs₀ hfl₀ hBK inf_le_right hKS hKB hKL' hBM inf_le_right hMLS
      hMLB hMLne hKnotML hP with h | h
  · exact Or.inl (h ▸ inf_le_left)
  · exact Or.inr (h ▸ inf_le_left)

theorem input15122ThreeEFlip4Star_holds (h23 : Lemma15123Standalone) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h36 : A36ForSQTK) (hF : A318Facts) (kN : L45NotA38Type)
    (hl42 : ∀ (X : Type) [Group X] [Finite X], IsPSL 4 2 1 X → A318Exclusion X) :
    Input15122ThreeEFlip4Star := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L P hc h3E h4 hfl hP _
  have hsmall : Ce15Small T Mc M :=
    ce15Small_of_not_six_five hc.ctx.setting.ce15
      (h23 G T Mc M hc.ctx.qtfe hc.ctx.mf hc.ctx.ce)
  exact flip4_star_all h37 h38 h36 hF kN hl42 hc hsmall h3E h4 hfl hP

end CFSG.Quasithin
