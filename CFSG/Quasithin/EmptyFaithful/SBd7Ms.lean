module

public import CFSG.Quasithin.EmptyFaithful.SBd7Gen
public import CFSG.Quasithin.EmptyFaithful.S146F3
public import CFSG.Quasithin.EmptyFaithful.S153E59C
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.EmptyFaithful.SBd5Dec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

namespace SBd7

section MS

variable {G : Type} [Group G]

omit [Group G] in
theorem isRankTwoLie2Derived_of_modO2 {G : Type} [Group G] {L : Subgroup G}
    (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) :
    IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  let e1 : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have hc : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hcomm : ∀ t, e1 z * t = t * e1 z := fun t => by
      obtain ⟨w, rfl⟩ := e1.surjective t
      rw [← map_mul, ← map_mul]
      exact congrArg e1 (Subgroup.mem_center_iff.mp hz w).symm
    have h1 : e1 z = 1 := S153E59.statedSL_center hcomm
    have h2 : z = 1 := e1.injective (h1.trans (map_one e1).symm)
    rw [h2]
    exact Subgroup.one_mem _
  let e2 : ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ≃*
      (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine Or.inl ⟨1, isPSL_three_two_iff.mpr ⟨?_⟩⟩
  exact (e2.trans e1).trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm

theorem isSylowTwoOf_of_le_of_le' {P C A : Subgroup G} (hP : IsSylowTwoOf P A) (hPC : P ≤ C)
    (hCA : C ≤ A) : IsSylowTwoOf P C := by
  refine ⟨hPC, hP.2.1, fun hdvd => hP.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex P C A hPC hCA
  have h2 : 2 ∣ P.relIndex A := by rw [← h1]; exact Dvd.dvd.mul_right hdvd _
  exact h2

variable [Finite G]

open CFSG.Quasithin.S153D in
theorem isMSPair_sup_S {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G)) :
    IsMSPair (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  obtain ⟨hLc, hLn, -, -, -, hLq⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hSI : Sgp153 T V₁ ≤ I := c.facts.sylow.1
  have hsqI : SQTKGroup ↥I := (lemma_15_3_15_one c.ctx.hyp c.ctx.inH c.facts).sqtk
  have hLSI : L ⊔ Sgp153 T V₁ ≤ I := sup_le hLle hSI
  have hSp : IsPGroup 2 ↥(Sgp153 T V₁) := hyp.qtfe.sylow.1.to_le inf_le_left
  have hcharL : CharTwo L :=
    charTwo_of_isSubnormal_of_charTwo c.ctx.charTwo (subnormal_of_mem_cComp hLI)
  have hcomp : L ∈ cComp (L ⊔ Sgp153 T V₁) := SBd5.mem_cComp_sup' hLI hSL
  have hset : ((L ⊔ Sgp153 T V₁ : Subgroup G) : Set G) = (L : Set G) * (Sgp153 T V₁ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L _ hSL
  obtain ⟨e⟩ := hq
  let α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hαs : Function.Surjective α := e.surjective.comp (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L))
  have hαk : α.ker = CFSG.pCore 2 ↥L := by
    show (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).ker = CFSG.pCore 2 ↥L
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) e.toMonoidHom
      e.injective, QuotientGroup.ker_mk']
  have hLie := isRankTwoLie2Derived_of_modO2 α hαs hαk
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) (L ⊔ Sgp153 T V₁) :=
    isSylowTwoOf_of_le_of_le' c.facts.sylow le_sup_right hLSI
  have hV₁S : V₁ ≤ Sgp153 T V₁ :=
    le_inf (hh.decomp.le₁.trans hyp.VZ_le_T) Subgroup.le_normalizer
  have hS0 : Sgp153 T V₁ ≠ ⊥ := by
    intro hb
    have h1 : V₁ = ⊥ := le_bot_iff.mp (hb ▸ hV₁S)
    have h4 := hh.decomp.card₁
    rw [h1, Subgroup.card_bot] at h4
    omega
  have hLM : ¬ L ≤ M := fun hLM => hLn (le_inf hLM hLle)
  have hV' : ⁅VZ T M, oTwoUpper (Y153 Mc M ⊓ L)⁆ ≠ ⊥ := by
    subst hYY
    exact hV
  have hno : ∀ C : Subgroup G, C ≤ Sgp153 T V₁ → C ≠ ⊥ →
      (C.subgroupOf (Sgp153 T V₁)).Characteristic →
        ¬ (L ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (C : Set G)) := fun C hCS hC1 hchar =>
    hyp.lemma_15_3_11_twelve hh.decomp hV' hLM hCS hC1 hchar
  have hH'le : (L ⊔ Sgp153 T V₁) ⊓ Subgroup.normalizer (Sgp153 T V₁ : Set G) ≤ L ⊔ Sgp153 T V₁ :=
    inf_le_left
  have hSH' : Sgp153 T V₁ ≤ (L ⊔ Sgp153 T V₁) ⊓ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    le_inf le_sup_right Subgroup.le_normalizer
  have hchS : ((Sgp153 T V₁).subgroupOf (Sgp153 T V₁)).Characteristic :=
    ⟨fun φ => by rw [Subgroup.subgroupOf_self]; exact Subgroup.comap_top _⟩
  have hlt : (L ⊔ Sgp153 T V₁) ⊓ Subgroup.normalizer (Sgp153 T V₁ : Set G) < L ⊔ Sgp153 T V₁ := by
    refine lt_of_le_of_ne hH'le fun h => hno _ le_rfl hS0 hchS ?_
    calc L ⊔ Sgp153 T V₁ = (L ⊔ Sgp153 T V₁) ⊓ Subgroup.normalizer (Sgp153 T V₁ : Set G) := h.symm
      _ ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) := inf_le_right
  have hodd : ¬ 2 ∣ ((L ⊔ Sgp153 T V₁) ⊓ Subgroup.normalizer (Sgp153 T V₁ : Set G)).relIndex
      (L ⊔ Sgp153 T V₁) := by
    intro hdvd
    apply hsyl.2.2
    have h1 := Subgroup.relIndex_mul_relIndex (Sgp153 T V₁)
      ((L ⊔ Sgp153 T V₁) ⊓ Subgroup.normalizer (Sgp153 T V₁ : Set G)) (L ⊔ Sgp153 T V₁) hSH' hH'le
    have h2 : 2 ∣ (Sgp153 T V₁).relIndex (L ⊔ Sgp153 T V₁) := by
      rw [← h1]; exact Dvd.dvd.mul_left hdvd _
    exact h2
  have hcore : Sgp153 T V₁ = pCoreOf 2 ((L ⊔ Sgp153 T V₁) ⊓ Subgroup.normalizer (Sgp153 T V₁ : Set G)) := by
    apply le_antisymm
    · exact le_pCoreOf_of_le_normalizer 2 hSH' (fun g hg => hg.2) hSp
    · exact pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le_of_le' hsyl hSH' hH'le)
  exact ⟨⟨B5.sqtk_of_le hsqI hLSI, charTwo_sup_of_normalizing hcharL hSp hSL, L, hcomp, hset, hLie⟩,
    Or.inl ⟨_, hlt, hodd, hcore⟩, hno⟩

omit [Finite G] in
theorem c134Q_sup_eq {L X Y : Subgroup G} [Finite G] (hperf : ⁅L, L⁆ = L)
    (hX : X ≤ Subgroup.normalizer (L : Set G)) (hY : Y ≤ Subgroup.normalizer (L : Set G)) :
    c134Q (L ⊔ X) L = c134Q (L ⊔ Y) L := by
  unfold c134Q
  rw [commutator_pCoreOf_sup_eq hperf hX, commutator_pCoreOf_sup_eq hperf hY]

end MS

end SBd7

end CFSG.Quasithin
