module

public import CFSG.Quasithin.EmptyFaithful.SBc11Cent
public import CFSG.Quasithin.EmptyFaithful.SBc11List

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace SBc11

section Ctx

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem exists_quot_center_equiv (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hcen : Subgroup.center ↥(Star153 T I L) = ⊥) :
    Nonempty (((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ≃*
      ↥(Star153 T I L)) := by
  obtain ⟨ψ, hψs, hψk, -⟩ := exists_star_hom c
  have hker : ψ.ker = Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
    le_antisymm hψk (center_le_ker_of_center_eq_bot ψ hψs hcen)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)⟩

theorem isRankTwoLie2Derived_quot_of_ctx (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hlist : IsPSL 3 2 1 ↥(Star153 T I L) ∨ IsAlt 6 ↥(Star153 T I L) ∨ IsPSU 3 3 1 ↥(Star153 T I L)) :
    IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  obtain ⟨e⟩ := exists_quot_center_equiv c (center_eq_bot_of_list hlist)
  refine isRankTwoLie2Derived_of_list ?_
  rcases hlist with h | h | h
  · exact Or.inl (IsPSL.of_mulEquiv e.symm h)
  · exact Or.inr (Or.inl (IsAlt.of_mulEquiv e.symm h))
  · exact Or.inr (Or.inr (IsPSU.of_mulEquiv e.symm h))

theorem not_two_dvd_relIndex_normalizer {I S : Subgroup G} (hS : IsSylowTwoOf S I) :
    ¬ 2 ∣ (Subgroup.normalizer (S : Set G) ⊓ I).relIndex I := by
  have key : (Subgroup.normalizer ((S.subgroupOf I : Subgroup ↥I) : Set ↥I)).index =
      Nat.card (Sylow 2 ↥I) := by
    rw [Sylow.card_eq_index_normalizer (B6.toSylow2 hS), ← Sylow.coe_coe, B6.toSylow2_coe hS]
  rw [Subgroup.inf_relIndex_right, Subgroup.relIndex,
    Subgroup.subgroupOf_normalizer_eq hS.1, key]
  have h := card_sylow_modEq_one 2 ↥I
  intro hd
  have h2 : Nat.card (Sylow 2 ↥I) % 2 = 1 := h
  omega

theorem pCoreOf_normalizer_eq {I S : Subgroup G} (hS : IsSylowTwoOf S I) :
    S = pCoreOf 2 (Subgroup.normalizer (S : Set G) ⊓ I) := by
  have hSle : S ≤ Subgroup.normalizer (S : Set G) ⊓ I := le_inf Subgroup.le_normalizer hS.1
  have hge : S ≤ pCoreOf 2 (Subgroup.normalizer (S : Set G) ⊓ I) :=
    le_pCoreOf_of_le_normalizer 2 hSle inf_le_left hS.2.1
  refine le_antisymm hge ?_
  exact (A4.isSylowTwoOf_iff_maximal.mp hS).2.2 _
    ((pCoreOf_le 2 _).trans inf_le_right) (pCoreOf_isPGroup 2 _) hge

theorem coe_eq_mul_of_ctx (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) :
    (I : Set G) = (L : Set G) * (Sgp153 T V₁ : Set G) := by
  obtain ⟨-, -, hIL, hIeq, hsyl, -⟩ := ctx_basic c
  have h := Subgroup.coe_mul_of_right_le_normalizer_left L (Sgp153 T V₁) (hsyl.1.trans hIL)
  rwa [← hIeq] at h

theorem isMSPair_of_ctx (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hlist : IsPSL 3 2 1 ↥(Star153 T I L) ∨ IsAlt 6 ↥(Star153 T I L) ∨ IsPSU 3 3 1 ↥(Star153 T I L)) :
    IsMSPair I (Sgp153 T V₁) := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  obtain ⟨hLc, -, -, -, hsyl, -⟩ := ctx_basic c
  have hV₁S : V₁ ≤ Sgp153 T V₁ :=
    le_inf (c.ctx.hyp.decomp.le₁.trans c.ctx.hyp.hyp.VZ_le_T) Subgroup.le_normalizer
  have hSne : Sgp153 T V₁ ≠ ⊥ := by
    intro h
    have h1 : V₁ = ⊥ := le_bot_iff.mp (h ▸ hV₁S)
    have h2 := c.ctx.hyp.decomp.card₁
    rw [h1, Subgroup.card_bot] at h2
    omega
  unfold IsMSPair
  refine ⟨⟨?_, c25.ctx.charTwo, L, hLc, ?_, isRankTwoLie2Derived_quot_of_ctx c hlist⟩,
    Or.inl ⟨Subgroup.normalizer (Sgp153 T V₁ : Set G) ⊓ I, ?_,
      not_two_dvd_relIndex_normalizer hsyl, pCoreOf_normalizer_eq hsyl⟩, c.c29.no_char⟩
  · exact sqtkGroup_of_pCoreOf_ne_bot c.ctx.hyp.hyp.qtfe.qtke c.ctx.hyp.hyp.qtfe.simple
      c.ctx.hyp.hyp.qtfe.nonabelian c.ctx.inH.1.2
  · exact coe_eq_mul_of_ctx c
  · refine lt_of_le_of_ne inf_le_right fun h => ?_
    have hIN : I ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) := by
      have h1 := inf_le_left (a := Subgroup.normalizer (Sgp153 T V₁ : Set G)) (b := I)
      rwa [h] at h1
    have hchar : ((Sgp153 T V₁).subgroupOf (Sgp153 T V₁)).Characteristic := by
      rw [Subgroup.subgroupOf_self]
      infer_instance
    exact c.c29.no_char (Sgp153 T V₁) le_rfl hSne hchar hIN

end Ctx

end SBc11

end CFSG.Quasithin
