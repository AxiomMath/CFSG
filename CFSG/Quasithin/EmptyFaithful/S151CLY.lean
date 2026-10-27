module

public import CFSG.Quasithin.EmptyFaithful.S151XF
public import CFSG.Quasithin.EmptyFaithful.S14110D8
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5115
public import CFSG.Quasithin.Background.C1PackS15348
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma33
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem le_mc_of_le_centralizer_oTwoUpper {T Mc L : Subgroup G}
    (hq : quasithinQTFE14Cat G T Mc)
    (hL : L ≤ Subgroup.centralizer
      (oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) : Set G)) :
    L ≤ Mc := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZ
  set H := Subgroup.centralizer (Z : Set G) with hH
  have hZT : ∀ z ∈ Z, z ∈ T ∧ ∀ t ∈ T, t * z = z * t := fun z hz => by
    have h := quasithinOmegaOneCenter_le_center T hz
    exact ⟨h.1, fun t ht => (Subgroup.mem_centralizer_iff.mp h.2 t ht)⟩
  have hTH : T ≤ H := fun t ht => Subgroup.mem_centralizer_iff.mpr fun z hz =>
    ((hZT z hz).2 t ht).symm
  have hZH : Z ≤ H := fun z hz => Subgroup.mem_centralizer_iff.mpr fun w hw =>
    ((hZT z hz).2 w (hZT w hw).1)
  have hZ2 : IsPGroup 2 Z := hq.sylow.1.to_le (fun z hz => (hZT z hz).1)
  have hZO : Z ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 hZH (fun x hx => Subgroup.centralizer_le_normalizer _ hx) hZ2
  have hpc : pCoreOf 2 H ≠ ⊥ := fun h =>
    hq.omegaOneCenter_ne_bot (le_bot_iff.mp (h ▸ hZO))
  have hF : CharTwo H := charTwo_of_inH' hq.qtke hq.sylow ⟨hTH, hpc⟩
  have hHsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le151 hq.sylow hTH
  have hYne : oTwoUpper H ≠ ⊥ := by
    intro hY
    apply centralizer_omegaOneCenter_ne hq
    have := eq_oTwoUpper_sup_of_isSylowTwoOf hHsyl
    rw [hY, bot_sup_eq] at this
    exact this
  have hYn : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hPY : pCoreOf 2 (oTwoUpper H) ≠ ⊥ :=
    C1Pack153.pCoreOf_ne_bot_of_normal hF (oTwoUpper_le H) hYn hYne (C1Pack153.oTwoUpper_idem' H)
  set P := pCoreOf 2 (oTwoUpper H) with hP
  have hPle : P ≤ oTwoUpper H := pCoreOf_le 2 _
  have hHP : H ≤ Subgroup.normalizer (P : Set G) :=
    hYn.trans (normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H))
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := fun l hl =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hPle (hL hl))
  have hPLH : P ≤ L ⊔ H := hPle.trans ((oTwoUpper_le H).trans le_sup_right)
  have hLH : pCoreOf 2 (L ⊔ H) ≠ ⊥ := fun h =>
    hPY (le_bot_iff.mp (h ▸ le_pCoreOf_of_le_normalizer 2 hPLH (sup_le hLP hHP)
      (pCoreOf_isPGroup 2 _)))
  exact H13.le_of_pCoreOf_sup_ne_bot hq.isUniqueM_mc hLH

theorem oTwoUpper_le_normalizer_component (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M Z₁ Z₂ V₁ V₂ L X : Subgroup G} (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hcomp : IsComponentOf L (g1_1516 Z₁)) (hX : X ≤ g1_1516 Z₁) :
    oTwoUpper X ≤ Subgroup.normalizer (L : Set G) := by
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  have hLcomp : L ∈ cComp (g1_1516 Z₁) :=
    Id2519.mem_cComp_of_isComponentIn (DoubleA3.isComponentIn_iff_open.mpr hcomp)
  have hLH : L ≤ g1_1516 Z₁ := le_of_mem_cComp hLcomp
  have hc' : (L.subgroupOf (g1_1516 Z₁)).Normal ∨ (conjSubgroupsBy (g1_1516 Z₁) L).ncard = 2 :=
    (lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
      (hSet.pCore_g1_ne_bot hq hMf) hLcomp).imp id And.left
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact odd_mem_normalizer_conjSubgroupsBy1516 hLH hc' (hX hx.1) hx.2
    ⟨1, Subgroup.one_mem _, (conjByElt_one1516 L).symm⟩

end CFSG.Quasithin
