module

public import CFSG.Quasithin.EmptyFaithful.S153D0All

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def MinCE153 {G : Type} [Group G] [Finite G] (T V₁ Yp M I : Subgroup G) : Prop :=
  ∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → CharTwo K → K ≤ I → K = I

structure Ctx15316Min {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G) :
    Prop extends Ctx15316 T Mc M V₁ V₂ Yp I L t where
  minimal : MinCE153 T V₁ Yp M I

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I : Subgroup G} {t : G}

theorem exists_minCE (hI : IsHPlus Yp (Sgp153 T V₁) M I) (hc : CharTwo I) :
    ∃ J : Subgroup G, J ≤ I ∧ IsHPlus Yp (Sgp153 T V₁) M J ∧ CharTwo J ∧
      MinCE153 T V₁ Yp M J := by
  obtain ⟨J, ⟨hJ, hJc, hJI⟩, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min
    {K : Subgroup G | IsHPlus Yp (Sgp153 T V₁) M K ∧ CharTwo K ∧ K ≤ I} ⟨I, hI, hc, le_rfl⟩
  refine ⟨J, hJI, hJ, hJc, fun K hK hKc hKJ => ?_⟩
  by_contra hne
  exact hmin K ⟨hK, hKc, hKJ.trans hJI⟩ (lt_of_le_of_ne hKJ hne)

theorem le_M_of_minCE (c : Ctx15313 T Mc M V₁ V₂ Yp I t) (hF : Facts15311 T M V₁ Yp I)
    (hmin : MinCE153 T V₁ Yp M I) {X : Subgroup G} (hXI : X ≤ I)
    (hYSX : Yp ⊔ Sgp153 T V₁ ≤ X) (hne : X ≠ I) : X ≤ M := by
  by_contra hXM
  have cX := ctx_of_le c hF hXI hYSX hXM
  exact hne (hmin X cX.inH cX.charTwo hXI)

end S153D

@[expose] def Input15320M : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316Min T Mc M V₁ V₂ Yp I L t → Concl15317 T V₁ Yp I L → ¬ IsLin2Block I L →
      ¬ IsLin2Quot L → ¬ IsSL3Quot L ∧ ¬ IsSp4Quot L

@[expose] def Input15324M : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316Min T Mc M V₁ V₂ Yp I L t → Concl15317 T V₁ Yp I L →
      ¬ IsLnTwoQuot L 4 ∧ ¬ IsLnTwoQuot L 5

theorem theorem15313_of_inputs_min
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hcover : AsA36NoOddCover)
    (hFacts : Facts15311All) (h15 : Input15315Two) (h16 : Input15316One) (h17 : Input15317)
    (h18 : Input15318) (h19 : Input15319) (h20 : Input15320M) (h21 : Input15321)
    (h23 : Input15323) (h24 : Input15324M) : Stage15313 := by
  intro G _ _ T Mc M V₁ V₂ Yp t hyp hrank I hI hchar
  obtain ⟨J, -, hJ, hJchar, hmin⟩ := S153D.exists_minCE hI hchar
  have c0 : Ctx15313 T Mc M V₁ V₂ Yp J t := ⟨hyp, hJ, hrank, hJchar⟩
  have hF : Facts15311 T M V₁ Yp J := hFacts G T Mc M V₁ V₂ Yp t hyp hrank J hJ
  obtain ⟨L, hL⟩ := S153D.lemma_15_3_15_two h15 h37 h38 c0 hF
  have cL : Ctx15313L T Mc M V₁ V₂ Yp J L t := ⟨c0, hF, hL⟩
  have cc : Ctx15316 T Mc M V₁ V₂ Yp J L t :=
    ⟨cL, S153D.lemma_15_3_16 (hC27 G) h16 h37 h38 cL⟩
  have ccm : Ctx15316Min T Mc M V₁ V₂ Yp J L t := { cc with minimal := hmin }
  have c17 := h17 G T Mc M V₁ V₂ Yp J L t cc
  have n18 := h18 G T Mc M V₁ V₂ Yp J L t cc c17
  have n19 := h19 G T Mc M V₁ V₂ Yp J L t cc c17 n18
  have n20 := h20 G T Mc M V₁ V₂ Yp J L t ccm c17 n18 n19
  have n21 := h21 G T Mc M V₁ V₂ Yp J L t cc c17 n18 n19 n20.1 n20.2
  rcases S153D.lemma_15_3_22 hcover cc n18 n19 n20 n21 with h | h | h
  · exact h23 G T Mc M V₁ V₂ Yp J L t cc h
  · exact (h24 G T Mc M V₁ V₂ Yp J L t ccm c17).1 h
  · exact (h24 G T Mc M V₁ V₂ Yp J L t ccm c17).2 h

theorem theorem15313_of_stages_min
    (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hcover : AsA36NoOddCover)
    (h15 : Input15315Two) (h16 : Input15316One) (h17 : Input15317)
    (h18 : Input15318) (h19 : Input15319) (h20 : Input15320M) (h21 : Input15321)
    (h23 : Input15323) (h24 : Input15324M) : Stage15313 :=
  theorem15313_of_inputs_min hC27 h37 h38 hcover (S153D.facts15311All_of_stages h11 h113) h15 h16 h17
    h18 h19 h20 h21 h23 h24

end CFSG.Quasithin
