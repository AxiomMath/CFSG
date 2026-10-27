module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreePackage
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeCalHZero
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeNormalizerW
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeDichotomy
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeRankBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeObstruction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeLStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeLStarClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
open CFSG.ComponentClassification.OutcomeLocal
open Module
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {Ch : Choice2011 G}

private theorem U0_le_U (c : Ctx23L D Ch) : c.U0 ≤ D.U := by
  rw [Ctx23L.U0]
  exact uc22p22v_conjClosure_le (inf_le_right.trans (le_normalizer_uCore D.M D.T)) (Data.Z_le_U D)

private theorem U0_lt_U (c : Ctx23L D Ch) (hne : c.U0 ≠ D.U) : c.U0 < D.U :=
  lt_of_le_of_ne (U0_le_U c) hne

private theorem exists_second_ctx (c : Ctx23L D Ch) (h205 : S20_5 D) (h208 : S20_8 D)
    (h1930 : H1930 D) (hL0W : c.L0 ≤ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)) :
    ∃ (L₁ L₂ : Subgroup G) (c₂ : Ctx23L D Ch),
      L₁ ∈ calLOf D.T D.M (Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)) ∧ c.L0 ≤ L₁ ∧
        L₁ ≤ L₂ ∧ L₂ ∈ calLStar D.T D.M ∧ c₂.L = L₂ ∧ c₂.L0 = c.L0 := by
  obtain ⟨L₁, hL₁, hL0L₁⟩ := exists_calLOf_le_normalizer_wClos c h205 h1930 hL0W
  obtain ⟨L₂, hL₂, hL₁L₂⟩ := exists_calLStar_of_calLOf hL₁
  let N₂ : Subgroup G :=
    Subgroup.normalizer (⨆ K ∈ calLOf D.T D.M (Subgroup.normalizer (L₂ : Set G)), K : Subgroup G)
  have hN : calMOf (L₂ ⊔ D.T) = {N₂} := h208 h1930 L₂ hL₂
  let c₂ : Ctx23L D Ch :=
    { c.toCtx23 with L := L₂, hL := hL₂, hL0L := hL0L₁.trans hL₁L₂, N := N₂, hN := hN }
  exact ⟨L₁, L₂, c₂, hL₁, hL0L₁, hL₁L₂, hL₂, rfl, rfl⟩

private theorem le_of_calMOf_eq_singleton {X N : Subgroup G} (h : calMOf X = {N}) : X ≤ N := by
  have hN : N ∈ calMOf X := h ▸ rfl
  exact hN.2

private theorem normalizer_U0_of_inf (c : Ctx23L D Ch) {L₁' : Subgroup G}
    (hU0 : D.U ⊓ conjClosure L₁' D.Z = c.U0) :
    L₁' ⊓ D.M ≤ Subgroup.normalizer (c.U0 : Set G) := by
  rw [← hU0]
  intro x hx
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨le_normalizer_uCore D.M D.T hx.2, uc22p22v_le_normalizer_conjClosure L₁' D.Z hx.1⟩

private theorem lt_rk_U (c : Ctx23L D Ch) {k : ℕ} (hcard : Nat.card c.U0 = 2 ^ k)
    (hlt : c.U0 < D.U) : k < rk ↥D.U := by
  have hU : IsPGroup 2 D.U :=
    uc22p22e_isPGroup_of_elem
      (uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).2
  obtain ⟨n, hn⟩ := hU.exists_card_eq
  have hrk : rk ↥D.U = n := by
    rw [show rk ↥D.U = padicValNat 2 (Nat.card D.U) from rfl, hn, padicValNat.prime_pow]
  have h1 : 2 ^ k < 2 ^ rk ↥D.U := by
    have h2 : Nat.card c.U0 < Nat.card D.U := Subgroup.card_lt_of_lt hlt
    rw [hcard, show Nat.card D.U = 2 ^ rk ↥D.U by rw [hrk, ← hn]] at h2
    exact h2
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1

private theorem factorization_of_eq_mul (c : Ctx23L D Ch)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z) (hlt : c.U0 < D.U)
    {H₁ H₂ : Subgroup G}
    (hH₁ : Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G) ≤ H₁)
    (hH₂ : Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) ≤ H₂)
    (hob : ¬ ∃ g : G, InCalO2 1 D.M ⊥ D.U g)
    {X : Subgroup G} (hTX : D.T ≤ X) (hXM : X ≤ D.M)
    (hF : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 X ∨ Group.IsSolvable ↥X) :
    (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G) := by
  rcases eq_mul_U_of_or c hU0 hlt hTX hXM hF with h | h
  · refine Set.Subset.antisymm ?_ ?_
    · rw [h]
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ⟨hH₁ ha.2, ha.1⟩, b, ⟨hH₂ hb.2, hb.1⟩, rfl⟩
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact X.mul_mem ha.2 hb.2
  · exact absurd h hob

private theorem center_wClos_le_cClos (c : Ctx23L D Ch) :
    E3.wClos D.U 1 D.T ⊓ Subgroup.centralizer (E3.wClos D.U 1 D.T : Set G) ≤
      E3.cClos D.U 1 D.T :=
  le_inf (inf_le_left.trans (E3.wClos_le 1 D.T)) inf_le_right

private theorem centralizer_cClos_le_normalizer_center (c : Ctx23L D Ch) :
    Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G) ≤
      Subgroup.normalizer (E3.wClos D.U 1 D.T ⊓
        Subgroup.centralizer (E3.wClos D.U 1 D.T : Set G) : Subgroup G) :=
  (Subgroup.centralizer_le (center_wClos_le_cClos c)).trans
    (Subgroup.centralizer_le_normalizer _)

private theorem exists_rank_data (c : Ctx23L D Ch) (h205 : S20_5 D) (h208 : S20_8 D)
    (h1930 : H1930 D) (hL0W0 : c.L0 ≤ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G))
    (hpk : H1930 D → ∀ c : Ctx23L D Ch, c.Conclusions23_2)
    {k : ℕ} (hcard : Nat.card c.U0 = 2 ^ k)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z) (hirr : IrrOn (c.L0 ⊓ D.M) c.U0)
    (hlt : c.U0 < D.U) :
    ∃ L₁ : Subgroup G,
      L₁ ∈ calLOf D.T D.M (Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)) ∧ c.L0 ≤ L₁ ∧
        L₁ ⊓ D.M ≤ Subgroup.normalizer (c.U0 : Set G) ∧ 2 * k ≤ rk ↥D.U := by
  obtain ⟨L₁, L₂, c₂, hL₁, hL0L₁, hL₁L₂, hL₂, hc₂L, hc₂L0⟩ :=
    exists_second_ctx c h205 h208 h1930 hL0W0
  obtain ⟨-, -, -, -, -, -, hU0₂, hUV₂, -, -, -⟩ := hpk h1930 c₂
  have hN₂ : L₂ ⊔ D.T ≤ c₂.N := le_of_calMOf_eq_singleton (hc₂L ▸ c₂.hN)
  have hUV₂' : D.U ⊓ conjClosure c₂.N D.Z = c.U0 := by
    change D.U ⊓ c₂.V = c.U0
    rw [hUV₂, hU0₂, hc₂L0, ← hU0]
  refine ⟨L₁, hL₁, hL0L₁, ?_, ?_⟩
  · exact normalizer_U0_of_inf c (Ctx23L.inf_conjClosure_eq_U0 c hL0L₁
      (hL₁L₂.trans (le_sup_left.trans hN₂)) hUV₂' hU0)
  · exact Ctx23L.two_mul_le_rk_U c hL₁ hL0L₁ (hL₁L₂.trans (le_sup_left.trans hN₂))
      ((inf_conjClosure_le_normalizer_of_calLOf hL₁).trans inf_le_right)
      (U_eq_conjClosure_normalizer_wClos c) hUV₂' hU0 hirr hcard hlt

theorem s23_3_of_conclusions (D : Data G) (Ch : Choice2011 G)
    (hpk : H1930 D → ∀ c : Ctx23L D Ch, c.Conclusions23_2)
    (h205 : S20_5 D) (h207 : S20_7 D) (h208 : S20_8 D) (h2010 : S20_10 D)
    (h861 : W3Lem86_1 G) (h2122 : S21_22Use D Ch)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G) :
    S23_3 D Ch := by
  intro h1930 c
  by_contra hne
  obtain ⟨hU, k, hk2, hNat, hcase, hcard, hU0, hUV, hirr, hW, ha⟩ := hpk h1930 c
  have hH0 : CFSG.LocalAnalysis.WeakClosure81.IsCalH0 D.U (c.L0 ⊔ D.T) :=
    Ctx23L.isCalH0_U c h861 hTim hcat h2010 h1930 hU0 (U0_lt_U c hne)
  have hL0W0 : c.L0 ⊔ D.T ≤ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) :=
    Ctx23L.L0T_le_normalizer_wClos_zero c h2010 h207 h1930 hH0 hW ha
      (lt_rk_U c hcard (U0_lt_U c hne))
  obtain ⟨L₁, hL₁, hL0L₁, hU0inv, h2k⟩ :=
    exists_rank_data c h205 h208 h1930 (le_sup_left.trans hL0W0) hpk hcard hU0 hirr (U0_lt_U c hne)
  have hL0W1 : c.L0 ⊔ D.T ≤ Subgroup.normalizer (E3.wClos D.U 1 D.T : Set G) :=
    Ctx23L.L0T_le_normalizer_wClos_one c h2010 h207 h1930 hH0 hW ha h2k hk2
  have hH₁ : Subgroup.normalizer (E3.wClos D.U 1 D.T ⊓
      Subgroup.centralizer (E3.wClos D.U 1 D.T : Set G) : Subgroup G) ∈ hSet D.T D.M :=
    normalizer_center_wClos_one_mem_hSet c (by omega) (le_sup_left.trans hL0W1)
  have hH₂ : Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) ∈ hSet D.T D.M :=
    normalizer_wClos_mem_hSet c (le_sup_left.trans hL0W0)
  have hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (CFSG.LocalAnalysis.WeakClosure81.InFSq 1 X ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((Subgroup.normalizer (E3.wClos D.U 1 D.T ⊓
          Subgroup.centralizer (E3.wClos D.U 1 D.T : Set G) : Subgroup G) ⊓ X :
            Subgroup G) : Set G) *
        ((Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) ⊓ X : Subgroup G) : Set G) :=
    fun X hXM hTX hF =>
      factorization_of_eq_mul c hU0 (U0_lt_U c hne) (centralizer_cClos_le_normalizer_center c)
        le_rfl (Ctx23L.not_exists_inCalO2_one c k hk2 hU0 hirr hcard (U0_lt_U c hne)
          (by omega) L₁ hL₁ hL0L₁ hU0inv) hTX hXM hF
  have hL012 : c.L0 ≤ Subgroup.normalizer (E3.wClos D.U 1 D.T ⊓
        Subgroup.centralizer (E3.wClos D.U 1 D.T : Set G) : Subgroup G) ⊓
      Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) :=
    le_inf ((le_sup_left.trans hL0W1).trans
      ((le_inf le_rfl
        (normalizer_le_normalizer_centralizer (E3.wClos D.U 1 D.T))).trans
          Subgroup.inf_normalizer_le_normalizer_inf)) (le_sup_left.trans hL0W0)
  exact Ctx23L.L0_not_le_M c (hL012.trans (h2122 h1930 c.toCtx21 _ hH₁ _ hH₂ hL012 hfX))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
