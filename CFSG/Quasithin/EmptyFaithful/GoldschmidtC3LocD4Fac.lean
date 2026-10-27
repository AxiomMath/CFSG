module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocD4Par
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocD4Cen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxD4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X6

namespace GoldC3

open CFSG.QuasithinUnique.Vol2Native.L239.Lie (ParabolicFacts)

@[expose] def HasBorelData (X : Type) [Group X] (U : Subgroup X) : Prop :=
  ∃ P₁ Q₁ : Subgroup X, Subgroup.normalizer (U : Set X) ⋖ P₁ ∧
    (Subgroup.normalizer (U : Set X)).relIndex P₁ = 3 ∧
    ¬ 3 ∣ Nat.card (Subgroup.normalizer (U : Set X)) ∧ IsMaxSubgroupIn ⊤ P₁ ∧
    ParabolicFacts P₁ Q₁ ∧ ∀ α : MulAut X, U.map α.toMonoidHom = U → P₁.map α.toMonoidHom = P₁

theorem HasBorelData.map {X X' : Type} [Group X] [Group X'] [Finite X] [Finite X']
    {U : Subgroup X} (h : HasBorelData X U) (e : X ≃* X') :
    HasBorelData X' (U.map e.toMonoidHom) := by
  obtain ⟨P₁, Q₁, hcov, hidx, h3, hmax, hF, hinv⟩ := h
  have hn : Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup X') : Set X') =
      (Subgroup.normalizer (U : Set X)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq U e).symm
  have key : ∀ x y : Subgroup X, x.map e.toMonoidHom ⋖ y.map e.toMonoidHom ↔ x ⋖ y :=
    fun x y => apply_covBy_apply_iff (MulEquiv.mapSubgroup e)
  refine ⟨P₁.map e.toMonoidHom, Q₁.map e.toMonoidHom, ?_, ?_, ?_, isMaxSubgroupIn_map e hmax,
    hF.map e.toMonoidHom e.injective, ?_⟩
  · rw [hn]
    exact (key _ _).2 hcov
  · rw [hn, Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    exact hidx
  · rw [hn, Subgroup.card_map_of_injective e.injective]
    exact h3
  · intro α' hα'
    set α : MulAut X := e.trans (α'.trans e.symm) with hα
    have hαU : U.map α.toMonoidHom = U := by
      have h1 := hα'
      rw [map_comm_equiv] at h1
      exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h1
    rw [map_comm_equiv, ← hα, hinv α hαU]

theorem ParabolicFacts.of_le_solvable {X : Type} [Group X] [Finite X] {P P₁ Q : Subgroup X}
    (hF : ParabolicFacts P₁ Q) (hP : P ≤ P₁) (hQP : Q ≤ P) (hsolv : Group.IsSolvable ↥P) :
    ParabolicFacts P Q where
  le := hQP
  normalizes := hP.trans hF.normalizes
  pGroup := hF.pGroup
  selfCentralizing := fun x hx => hF.selfCentralizing ⟨hP hx.1, hx.2⟩
  center_le := hF.center_le
  nonabelian := hF.nonabelian
  levi := Or.inl (by
    rw [(isSolvable_iff_perfectCore_eq_bot P).1 hsolv]
    exact bot_le)

theorem normalizer_le_centralizer_centerOf_of_card_two {X : Type} [Group X] {U : Subgroup X}
    (h : Nat.card (centerOf U) = 2) :
    Subgroup.normalizer (U : Set X) ≤ Subgroup.centralizer (centerOf U : Set X) := by
  obtain ⟨z, hz2, hcen⟩ := GoldCMax.exists_zpowers_of_card_two h
  refine (GoldCMax.normalizer_le_normalizer_centerOf U).trans ?_
  rw [hcen, centralizer_zpowers_eq]
  exact GoldCMax.normalizer_le_centralizer_of_two hz2

theorem c3Facts_of_borelData {X : Type} [Group X] [Finite X] {U : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) (hB : HasBorelData X U) (hC : Cent9Data X)
    (hout : ∀ α : MulAut X, (∃ a : ℕ, α ^ 2 ^ a = 1) → ∃ g : X, ∀ x, α x = g * x * g⁻¹)
    (hZ : ∀ g : X, (∀ x : X, x * g = g * x) → g = 1) :
    ∃ P : Subgroup X, C3Facts X U P := by
  obtain ⟨P₁, Q₁, hcov, hidx, h3, hmax, hF, hinv⟩ := hB
  have hUi : ¬ 2 ∣ U.index := by
    have h := hU.2.2
    rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at h
  obtain ⟨hc2, hc9⟩ := hC U hU.2.1 hUi
  have hcent := normalizer_le_centralizer_centerOf_of_card_two (U := U) hc2
  have hUP₁ : U ≤ P₁ := Subgroup.le_normalizer.trans hcov.le
  have hUP : U ≤ oPrimeResidualOf 2 P₁ := le_oPrime_two hU.2.1 hUP₁
  have hsup := oPrime_two_sup_eq hU hcov
  have hcard := card_oPrime_two hU hcov hidx h3
  have hsolv := isSolvable_oPrime_two hU hcov hidx h3
  have hQU : Q₁ ≤ U := by
    have h1 : Q₁ ≤ pCoreOf 2 P₁ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hF.le hF.normalizes hF.pGroup
    exact h1.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le hU hUP₁))
  have hP₁card : Nat.card ↥P₁ = Nat.card (Subgroup.normalizer (U : Set X)) * 3 := by
    have h := Subgroup.card_mul_index ((Subgroup.normalizer (U : Set X)).subgroupOf P₁)
    rw [show ((Subgroup.normalizer (U : Set X)).subgroupOf P₁).index = 3 from hidx,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcov.le).toEquiv] at h
    exact h.symm
  refine ⟨oPrimeResidualOf 2 P₁, ?_⟩
  exact
  { le := hUP
    card := hcard
    not_normal := not_oPrime_two_le hU hcov
    not_centralizes := by
      intro hPC
      have hP₁C : P₁ ≤ Subgroup.centralizer (centerOf U : Set X) := by
        rw [← hsup]
        exact sup_le hPC hcent
      have hCtop : Subgroup.centralizer (centerOf U : Set X) ≠ ⊤ := by
        intro htop
        obtain ⟨z, hz2, hzc⟩ := GoldCMax.exists_zpowers_of_card_two hc2
        have hzmem : z ∈ centerOf U := hzc ▸ Subgroup.mem_zpowers z
        have hz1 : z = 1 := hZ z fun x => by
          have hx : x ∈ Subgroup.centralizer (centerOf U : Set X) := htop ▸ Subgroup.mem_top x
          exact (Subgroup.mem_centralizer_iff.1 hx z hzmem).symm
        rw [hz1, orderOf_one] at hz2
        omega
      have hCeq : Subgroup.centralizer (centerOf U : Set X) = P₁ := by
        by_contra hne
        exact hCtop (hmax.2 _ (lt_of_le_of_ne hP₁C (Ne.symm hne)) le_top)
      rw [hCeq, hP₁card] at hc9
      omega
    maximal := by
      rw [hsup]
      exact hmax
    blockFree := Or.inl ⟨Q₁, ParabolicFacts.of_le_solvable hF oPrime_two_le (hQU.trans hUP) hsolv⟩
    inv := fun α hα => map_oPrime_two α (hinv α hα)
    cent := hcent
    norm := Or.inr ⟨hout, hZ⟩ }

end GoldC3

end CFSG.Quasithin
