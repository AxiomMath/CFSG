module

public import CFSG.Quasithin.EmptyFaithful.S151TBDef
public import CFSG.Quasithin.EmptyFaithful.S151ZI
public import CFSG.Quasithin.EmptyFaithful.A38cA7

public section

namespace CFSG.Quasithin.S151TB

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}

theorem center_eq_bot_of_simple {Q : Type} [Group Q] (hs : IsSimpleGroup Q)
    (hq : CFSG.IsQuasisimple Q) : Subgroup.center Q = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    have hsub : Subsingleton (Q ⧸ Subgroup.center Q) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    exact (not_nontrivial_iff_subsingleton.mpr hsub) hq.2.1.toNontrivial

omit [Finite G] in
theorem exists_epi_of_center_bot {X : Type} [Group X] {L : Subgroup G}
    (hcen : Subgroup.center (LStar L) = ⊥)
    (e : (LStar L ⧸ Subgroup.center (LStar L)) ≃* X) :
    ∃ α : ↥L →* X, Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L := by
  let α : ↥L →* X := e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center (LStar L))).comp
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))
  refine ⟨α, e.surjective.comp ((QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective _)), ?_⟩
  ext x
  simp only [α, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [hcen, Subgroup.mem_bot, QuotientGroup.eq_one_iff]

theorem g1_le_normalizer
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hcomp : L ∈ cComp (g1_1516 Z₁)) (hD : ListD' L) :
    g1_1516 Z₁ ≤ Subgroup.normalizer (L : Set G) := by
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hcomp
  rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
      (hSet.pCore_g1_ne_bot hq hMf) hcomp with hn | ⟨-, hA⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn
  · exfalso
    have hs : IsSimpleGroup (LStar L) :=
      CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hA
    have hcen := center_eq_bot_of_simple hs hc.hL.quasi
    rcases hD with h | h | h
    · obtain ⟨e⟩ : Nonempty ((LStar L ⧸ Subgroup.center (LStar L)) ≃* alternatingGroup (Fin 7)) := h
      exact a7NotA38Type_holds G L (exists_epi_of_center_bot hcen e) hA
    · obtain ⟨e⟩ : Nonempty ((LStar L ⧸ Subgroup.center (LStar L)) ≃* alternatingGroup (Fin 6)) := h
      exact a6NotA38Type_holds G L (exists_epi_of_center_bot hcen e) hA
    · let e : (LStar L ⧸ Subgroup.center (LStar L)) ≃* LStar L :=
        (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
      obtain ⟨hadm, K, _, _, hK, ⟨e'⟩⟩ := h
      exact g2NotA38Type_holds G L ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e.symm.trans e'⟩⟩ hA

end CFSG.Quasithin.S151TB
