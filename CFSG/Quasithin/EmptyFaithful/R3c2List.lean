module

public import CFSG.Quasithin.EmptyFaithful.S153I37
public import CFSG.Quasithin.EmptyFaithful.S153F17
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp

public section

namespace CFSG.Quasithin.R3c2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Input15333Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I : Subgroup G) (t : G),
    CtxComp T Mc M V₁ V₂ Yp I t → ∃ z : G, Lemma115Hyp I (Sgp153 T V₁) Mc z

@[expose] def RankOneListCatalogue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G),
    Lemma115Cases L z → CFSG.IsQuasisimple ↥L → centerOf L = pCoreOf 2 L →
      (¬ ∃ e : ℕ, IsSz e (↥L ⧸ Subgroup.center ↥L)) → CFSG.Open.pRank 3 L = 1 →
      (∃ Q : Subgroup G, Q ≤ L ∧ Group.IsSolvable ↥Q ∧
        (∃ P : Subgroup G, IsSylowTwoOf P L ∧ P ≤ Q) ∧ 3 ∣ Nat.card ↥Q) →
        ((∃ n : ℕ, Even n ∧ IsPSL 2 2 n (↥L ⧸ Subgroup.center ↥L)) ∨
          (∃ n : ℕ, Even n ∧ IsPSU 3 2 n (↥L ⧸ Subgroup.center ↥L)) ∨
          IsPSL 3 2 1 (↥L ⧸ Subgroup.center ↥L))

@[expose] def Input15337OneInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → L = conjClosure L (Sgp153 T V₁) → CFSG.Open.pRank 3 L = 1 →
      ((∃ n : ℕ, Even n ∧ IsPSL 2 2 n (↥L ⧸ Subgroup.center ↥L)) ∨
        (∃ n : ℕ, Even n ∧ IsPSU 3 2 n (↥L ⧸ Subgroup.center ↥L)) ∨
        IsPSL 3 2 1 (↥L ⧸ Subgroup.center ↥L)) → InducesInnerModO2153 Yp L

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem exists_solvable_sylow_three (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) :
    ∃ Q : Subgroup G, Q ≤ L ∧ Group.IsSolvable ↥Q ∧
      (∃ P : Subgroup G, IsSylowTwoOf P L ∧ P ≤ Q) ∧ 3 ∣ Nat.card ↥Q := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hF : Facts15311 T M V₁ Yp I := c.facts11
  have hLc : L ∈ cComp I := c.c33.mem
  have hSY : Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer (Yp : Set G) :=
    inf_le_left.trans (S153D.Sgp153_le_normalizer_Yp hh)
  have hSn : Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer (YL153 Yp L : Set G) :=
    (F7.le_normalizer_inf hSY (inf_le_right.trans Subgroup.le_normalizer)).trans
      (normalizer_le_normalizer_oTwoUpper _)
  have hYLle : YL153 Yp L ≤ Yp ⊓ L := oTwoUpper_le _
  have hYsolv : Group.IsSolvable ↥Yp := S153D.isSolvable_Yp hF
  have hYLsolv : Group.IsSolvable ↥(YL153 Yp L) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (hYLle.trans inf_le_left)) (Subgroup.inclusion_injective _)
  have hSL : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    S153D.isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hLc) hF.sylow
  have hSLsolv : Group.IsSolvable ↥(Sgp153 T V₁ ⊓ L) := F1.isSolvable_of_isPGroup_two hSL.2.1
  refine ⟨YL153 Yp L ⊔ (Sgp153 T V₁ ⊓ L), sup_le (hYLle.trans inf_le_right) inf_le_right,
    F1.isSolvable_sup_of_le_normalizer hYLsolv hSLsolv hSn, ⟨_, hSL, le_sup_right⟩, ?_⟩
  have hYL : YL153 Yp L ≠ ⊥ :=
    S153D.YL153_ne_bot h37 h38 hh c.inH c.rank hLc c.c34.rank
  obtain ⟨x, hxY, hxo, hx1⟩ : ∃ x ∈ Yp ⊓ L, Odd (orderOf x) ∧ x ≠ 1 := by
    by_contra hno
    push Not at hno
    apply hYL
    rw [eq_bot_iff]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, ho⟩
    exact Subgroup.mem_bot.mpr (hno x hx ho)
  obtain ⟨k, hk⟩ := S153F.exists_orderOf_eq_three_pow hF hxY.1 hxo
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.mp (by simpa using hk))
  have h3 : 3 ∣ orderOf x := by
    rw [hk]
    exact dvd_pow_self 3 hk1
  have hxYL : x ∈ YL153 Yp L := mem_oTwoUpper_of_odd hxY hxo
  have hz : orderOf (x ^ (orderOf x / 3)) = 3 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' h3
  have hzX : x ^ (orderOf x / 3) ∈ YL153 Yp L ⊔ (Sgp153 T V₁ ⊓ L) :=
    (le_sup_left : YL153 Yp L ≤ _) (Subgroup.pow_mem _ hxYL _)
  have := Subgroup.orderOf_dvd_natCard _ hzX
  rwa [hz] at this

theorem input15337OneList_of_inputs (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hlist115 : Lemma115_3_List) (hA : Input15333Two) (hB : RankOneListCatalogue)
    (hC : Input15337OneInner) : Input15337OneList := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hL0 hr
  have hq := c.hyp.hyp.qtfe
  have hsimple : IsSimpleGroup G := hq.simple
  have hcore : QTKECore G := qtkeCore_of_cat hq.nonabelian hq.qtke
  obtain ⟨z, hz⟩ := hA G T Mc M V₁ V₂ Yp I t c.toCtxComp
  have hcomp : IsComponentIn L I :=
    Id2519.isComponentIn_of_mem_cComp c.c33.mem c.c33.quasisimple
  have hcases : Lemma115Cases L z :=
    (Lemma115_3_List.component_cases hlist115 hsimple hq.nonabelian hcore hz hcomp).2.2.2
  have hlist := hB G L z hcases c.c33.quasisimple c.c33.center_eq c.c34.not_Sz hr
    (exists_solvable_sylow_three h37 h38 c)
  exact ⟨hlist, hC G T Mc M V₁ V₂ Yp I L t c hL0 hr hlist⟩

end CFSG.Quasithin.R3c2
