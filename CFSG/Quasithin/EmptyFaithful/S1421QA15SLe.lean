module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15Bang
public import CFSG.Quasithin.EmptyFaithful.S1421QA15Z

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem Core3Ctx.oTwoUpper_le_centralizer (h209 : Lemma14209Used)
    (c : Core3Ctx T M H K1 L M₁) :
    oTwoUpper H ≤ Subgroup.centralizer (omegaOneCenterOf (sOf T K1) : Set G) := by
  obtain ⟨Kc, hKc, -, hKT, -⟩ := h209 G T M H K1 c.st c.lt
  exact oTwoUpper_le_centralizer_omegaOneCenter_sOf c.st c.lt hKc hKT

theorem Core3Ctx.exists_inM_ge_oTwoUpper (h2 : Lemma14215Step2) (h209 : Lemma14209Used)
    (c : Core3Ctx T M H K1 L M₁) (hq : CFSG.IsQuasisimple ↥L)
    (hLS : g0Of T M H K1 = L ⊔ sOf T K1) :
    ∃ M₁' : Subgroup G, InM (g0Of T M H K1) M₁' ∧ ¬ T ≤ M₁' ∧ IsSylowTwoOf (sOf T K1) M₁' ∧
      oTwoUpper H ≤ M₁' := by
  obtain ⟨ZL, hZL, hZLle, hc⟩ := exists_zL c hq hLS
  have hZ2 : IsPGroup 2 ZL := (isPGroup_sOf c.st).to_le (hZLle.trans (A4.omegaOneCenterOf_le _))
  obtain ⟨M₁', hN, hG0, hT, hS⟩ := exists_inM_normalizer h2 c hZL hZ2 hc
  refine ⟨M₁', hG0, hT, hS, ?_⟩
  have hcc : Subgroup.centralizer (omegaOneCenterOf (sOf T K1) : Set G) ≤
      Subgroup.centralizer (ZL : Set G) := Subgroup.centralizer_le (fun x hx => hZLle hx)
  exact (c.oTwoUpper_le_centralizer h209).trans
    (hcc.trans ((Subgroup.centralizer_le_normalizer (s := (ZL : Set G))).trans hN.2))

end S1421

end CFSG.Quasithin
