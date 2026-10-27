module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC134ResZ
public import CFSG.Quasithin.EmptyFaithful.FLc2EndNode
public import CFSG.Quasithin.EmptyFaithful.FLc6MS
public import CFSG.Quasithin.EmptyFaithful.FLcRank2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem normalizes_Y2_Q2_15129 {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G}
    (hc : Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L) (hF : FlagData15129 T Mc M Z₁ Z₂ V₂ L n W) :
    T ≤ Subgroup.normalizer (oTwoUpper (pPar15129 T Z₁ L n W 2) : Set G) ∧
      T ≤ Subgroup.normalizer (pCoreOf 2 (pPar15129 T Z₁ L n W 2) : Set G) := by
  have hM := hc.base.ctx.mf
  have h18 := hc.base.h18
  obtain ⟨-, hP1b, -⟩ := input15129P0_holds G T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF
  have hQCS := cs15129 G T Mc M Z₁ Z₂ V₁ V₂ L hc hF.four
  obtain ⟨hR1, hR2, -⟩ := input15129Rank2_holds G T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF
  have hEnd := input15129EndNode_holds G T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF
  have hTM : T ≤ M := hM.1.1.2
  have hQT : T ≤ Subgroup.normalizer (pCoreOf 2 (pPar15129 T Z₁ L n W 1) : Set G) := by
    rw [hP1b, hQCS]
    have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
      hTM.trans (le_normalizer_V154 T Mc M)
    have hTC := hTV.trans (normalizer_le_normalizer_centralizer (V154 T Mc M))
    exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, hTC hx⟩
  have hY2 : ∀ t ∈ T, conjByElt t (oTwoUpper (pPar15129 T Z₁ L n W 2)) =
      oTwoUpper (pPar15129 T Z₁ L n W 2) := by
    intro t ht
    rcases hEnd t ht with h | h
    · exact h
    · exfalso
      apply hR2
      intro x hx
      have hx' : t * x * t⁻¹ ∈ pCoreOf 2 (oTwoUpper (pPar15129 T Z₁ L n W (n - 1))) := by
        rw [← h, conjByElt, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj t)]
        exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
      exact (Subgroup.mem_normalizer_iff.mp (hQT ht) x).mpr (hR1 hx')
  have hY2' : T ≤ Subgroup.normalizer (oTwoUpper (pPar15129 T Z₁ L n W 2) : Set G) := fun t ht =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hY2 t ht)
  refine ⟨hY2', ?_⟩
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.base.hL.comp
  have hSG : s1516 T Z₁ ≤ g1_1516 Z₁ := s1516_le_g1 T Z₁
  have hSP : s1516 T Z₁ ≤ pPar15129 T Z₁ L n W 2 := by
    unfold pPar15129 flagParab
    exact le_inf le_sup_right (le_iInf₂ fun j hj => (hF.flag.2 j hj.1 hj.2.1).2.2.1)
  have hPG : pPar15129 T Z₁ L n W 2 ≤ g1_1516 Z₁ :=
    (flagParab_le _ n W 2).trans (sup_le hLG hSG)
  have hPSyl : IsSylowTwoOf (s1516 T Z₁) (pPar15129 T Z₁ L n W 2) :=
    FLc.isSylowTwoOf_restrict h18.four hSP hPG
  have hTS : T ≤ Subgroup.normalizer (s1516 T Z₁ : Set G) :=
    (hc.base.ctx.setting.extra_small (Or.inl hF.four)).s_normal
  have hTP2 : T ≤ Subgroup.normalizer (pPar15129 T Z₁ L n W 2 : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have e : pPar15129 T Z₁ L n W 2 = oTwoUpper (pPar15129 T Z₁ L n W 2) ⊔ s1516 T Z₁ :=
      eq_oTwoUpper_sup_of_isSylowTwoOf hPSyl
    have h1 := hY2 t ht
    have h2 : (s1516 T Z₁).map (MulAut.conj t).toMonoidHom = s1516 T Z₁ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTS ht)
    unfold conjByElt at h1
    conv_lhs => rw [e]
    rw [Subgroup.map_sup]
    exact (congrArg₂ (· ⊔ ·) h1 h2).trans e.symm
  exact fun t ht => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hTP2 ht)

theorem not_c134NotCentralizerCore_15129 {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} {n : ℕ}
    {W : ℕ → Subgroup G} (hc : Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hF : FlagData15129 T Mc M Z₁ Z₂ V₂ L n W) :
    ¬ C134NotCentralizerCore
      (kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2))
      (pCoreOf 2 (pPar15129 T Z₁ L n W 2)) := by
  obtain ⟨D⟩ := nonempty_p0Setup15129 hc hF
  have hn := hF.n_eq
  have h28 := hc.h28
  have hUL : uLOf1527 Z₂ L ≤ L ⊔ s1516 T Z₁ :=
    (facts_of_ctx hc.base).ULU.trans (uOf1527_le_sup hc.base)
  have hT : IsPGroup 2 T := hc.base.ctx.qtfe.sylow.1
  obtain ⟨hTY, hTQ⟩ := normalizes_Y2_Q2_15129 hc hF
  have hZ : ∀ x ∈ T, (∀ t ∈ T, t * x = x * t) → x ^ 2 = 1 →
      ∀ y ∈ FLc.yNode L (s1516 T Z₁) n W 2, y * x = x * y := by
    intro x hxT hxc hx2 y hy
    have hyL : y ∈ L := D.yNode_le_L 2 hy
    have hyN : y ∈ Subgroup.normalizer (zUOf1528 Z₂ L : Set G) := by
      rw [← hF.w1]
      exact FLc.P0Setup.yNode_le_normalizer_W 2 1 le_rfl (by rcases hn with h | h <;> omega)
        (by norm_num) hy
    have hyz : y ∈ L ⊓ Subgroup.normalizer (zUOf1528 Z₂ L : Set G) := ⟨hyL, hyN⟩
    rw [← h28.2.2.2, h28.2.2.1] at hyz
    have hxZ : x ∈ quasithinOmegaOneCenter T :=
      Subgroup.subset_closure ⟨⟨hxT, Subgroup.mem_centralizer_iff.2 hxc⟩, hx2⟩
    exact (Subgroup.mem_centralizer_iff.1 hyz.2 x hxZ).symm
  intro h
  obtain ⟨S', hS', hQS', heq⟩ :=
    D.exists_sylow_pCoreOf_eq hn hUL hT (s1516_le T Z₁) hTQ hTY hZ
  exact h S' hS' hQS' heq

end CFSG.Quasithin
