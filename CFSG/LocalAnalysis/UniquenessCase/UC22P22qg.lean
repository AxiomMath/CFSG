module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qy
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def Clause2Print (D : Data G) (p : ℕ) (P P₀ : Subgroup G) : Prop :=
  5 ≤ p ∧ Group.IsSolvable D.M ∧ IsWeaklyClosedIn P₀ P ∧
    (∃ (_ : Fact p.Prime) (n : ℕ), 2 ≤ n ∧
      Nonempty (rankThreeLayer (centralizer (P₀ : Set G)) ≃* PSL(2, GaloisField p n))) ∧
    ¬ rankThreeLayer (centralizer (P₀ : Set G)) ≤ D.M ∧
    CFSG.Open.uniqueFourIsFrobenius
      (CFSG.Open.uniqueFourPrimeCore p D.M ⊔
        centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G))
      (CFSG.Open.pCoreOf 2 D.M) (centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G)) ∧
    ∀ Y : Subgroup G, Y ≤ P → Nat.card Y = p → Y ≠ P₀ → normalizer (Y : Set G) ≤ D.M

@[expose] def R613Ident (D : Data G) : Prop :=
  ∀ (p : ℕ) (P P₀ : Subgroup G), Hyp612 D p P P₀ →
    inftyOf (centralizer (P₀ : Set G)) = rankThreeLayer (centralizer (P₀ : Set G))

@[expose] def R613Cent (D : Data G) : Prop :=
  ∀ (p : ℕ) (P P₀ : Subgroup G), Hyp612 D p P P₀ →
    P ≤ centralizer ((P ⊓ inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G)

@[expose] def R613DefAt (D : Data G) (p : ℕ) (P P₀ : Subgroup G) : Prop :=
  (3 < p ∧ Group.IsSolvable D.M ∧ IsWeaklyClosedIn P₀ P ∧
      rankThreeGamma 1 p (P ⊓ inftyOf (centralizer (P₀ : Set G))) ≤ D.M ∧
      (∃ n : ℕ, 1 < n ∧ LieModel (inftyOf (centralizer (P₀ : Set G))) .PSL 2 p n) ∧
      CFSG.Open.uniqueFourIsFrobenius
        (CFSG.Open.uniqueFourPrimeCore p D.M ⊔
          centralizer (inftyOf (centralizer (P₀ : Set G)) : Set G))
        (CFSG.Open.pCoreOf 2 D.M) (centralizer (inftyOf (centralizer (P₀ : Set G)) : Set G))) ∧
    P ≤ centralizer ((P ⊓ inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G)

end CFSG.LocalAnalysis.UniquenessCase.UC6

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.RankThreeCoreUniqueness.Helpers (gamma_le_iff)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def Sigma2Print (D : Data G) : Prop :=
  ∀ p ∈ D.sig2, ∃ P P₀ : Subgroup G, UC6.Hyp612 D p P P₀ ∧ UC6.Clause2Print D p P P₀

theorem uc22p22q_frobenius_of_product {W K V : Subgroup G} (h : rankThreeFrobeniusProduct W K V) :
    CFSG.Open.uniqueFourIsFrobenius (W ⊔ V) K V := by
  obtain ⟨X, hXW, hXK, hK, hV, hKX, hKn, hKV, hfpf⟩ := h
  have hWX : W ⊔ V = X := by
    apply le_antisymm
    · exact sup_le (fun a ha => (hXW a).2 ⟨a, ha, 1, V.one_mem, by simp⟩)
        (fun b hb => (hXW b).2 ⟨1, W.one_mem, b, hb, by simp⟩)
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (hXW x).1 hx
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  have hKVX : K ⊔ V = X := by
    apply le_antisymm
    · exact sup_le hKX (fun b hb => (hXK b).2 ⟨1, K.one_mem, b, hb, by simp⟩)
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (hXK x).1 hx
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  refine ⟨hK, hV, ?_, ?_, le_sup_right, hWX.trans hKVX.symm, hKV, hfpf⟩
  · rw [hWX]
    exact hKX
  · rw [hWX]
    exact hKn

theorem sigma2Print_ofSetup (hS : RankThreeUC.Standing G) (S : RankThreeUC.Setup G) :
    Sigma2Print (PartTwo.Three.dataOfSetup hS S) := fun p hp => by
  obtain ⟨hpA, Q, hw, hB⟩ := hp
  haveI : Fact p.Prime := ⟨(PartTwo.Three.prime_of_mem_rankThreeSigmaA hpA).1⟩
  have h3 : 3 ≤ CFSG.Open.pRank p (Q : Subgroup G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.selected_sylow_rank_at_least_three hS.rank p hpA Q
  have hQM : (Q : Subgroup G) ≤ S.M :=
    le_normalizer.trans
      ((CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 2 p (Q : Subgroup G) (Q : Subgroup G)
        le_rfl (by omega)).trans hw.u0)
  have hmem : p ∈ (PartTwo.Three.dataOfSetup hS S).sig2 := ⟨hpA, Q, hw, hB⟩
  obtain ⟨h5, hsolv, P₀, hP₀Q, hcard, hweak, hlayer, hnot, hfrob, hN⟩ := hB
  refine ⟨(Q : Subgroup G), P₀, ⟨hmem, uc22p22q_isSylowOf_of_sylow Q hQM, hP₀Q, hcard,
    fun hle => hnot ((uc22p22q_layer_le _).trans hle)⟩, h5, hsolv, fun g hg => hweak g hg, hlayer, hnot,
    uc22p22q_frobenius_of_product hfrob, hN⟩

theorem uc22p22q_normalizer_le_of_noncyclic (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {X : Subgroup G} (hXM : X ≤ D.M) (hXp : IsPGroup p X) (hXc : ¬ IsCyclic X) :
    normalizer (X : Set G) ≤ D.M := by
  intro g hg
  have hXg : X ≤ uniqueFourConj g D.M := by
    intro x hx
    rw [UC6.mem_uniqueFourConj_iff]
    exact hXM ((mem_normalizer_iff.1 hg x).1 hx)
  have hmem : uniqueFourConj g D.M ∈ calMOf X := ⟨UC6.isMaxTwoLocal_conj D.maxLocal g, hXg⟩
  rw [h61 p hp X hXM hXp hXc] at hmem
  have hconj : uniqueFourConj g D.M = D.M := Set.mem_singleton_iff.mp hmem
  have hgN : g ∈ normalizer (D.M : Set G) := UC6.uniqueFourConj_eq_self_iff.mp hconj
  rwa [UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal] at hgN

theorem uc22p22q_r613defAt_of (D : Data G) (hstd : Sigma23Std D) (h61 : UC6.R6_1 D) {p : ℕ} {P P₀ : Subgroup G}
    (hH : UC6.Hyp612 D p P P₀) (hc2 : UC6.Clause2Print D p P P₀)
    (hid : UC6.inftyOf (centralizer (P₀ : Set G)) = rankThreeLayer (centralizer (P₀ : Set G)))
    (hcent : P ≤ centralizer ((P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G)) :
    UC6.R613DefAt D p P P₀ := by
  obtain ⟨h5, hsolv, hwc, ⟨hfact, n, hn2, ⟨e⟩⟩, hnot, hfrob, hN⟩ := hc2
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  have hpP : p.Prime := hfact.out
  have hLie : LieModel (UC6.inftyOf (centralizer (P₀ : Set G))) .PSL 2 p n := by
    rw [hid]
    have h25 : 5 ≤ p ^ n := (by omega : 5 ≤ p).trans (Nat.le_self_pow (by omega) p)
    exact Or.inl ⟨by decide, CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv _ p n h25 e⟩
  have hL : ∃ n : ℕ, 1 < n ∧ LieModel (UC6.inftyOf (centralizer (P₀ : Set G))) .PSL 2 p n := ⟨n, hn2, hLie⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨m, hm, hel, -⟩ := uc22p22q_P1_elem D hstd hH hwc hL hp2
  refine ⟨⟨by omega, hsolv, hwc, ?_, hL, ?_⟩, hcent⟩
  · refine (gamma_le_iff 1 p _ D.M).2 fun X hXP₁ hX1 => ?_
    have hXne : X ≠ ⊥ := uc22p22qv_ne_bot_of_pRank hpP hX1
    have hXel : IsElemAbelian p X := uc22p22n_isElemAbelian_of_le hXP₁ hel
    have hXM : X ≤ D.M := (hXP₁.trans inf_le_left).trans hH.sylow.le
    by_cases hcyc : IsCyclic X
    · have hXcard : Nat.card X = p := by
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).1 (uc22p22e_isPGroup_of_elem hXel)
        have hk1 : k ≤ 1 :=
          (CFSG.SectionRank.le_pRank hpP.one_lt le_rfl hXel hk).trans
            (CFSG.SectionRank.pRank_le_one_of_isCyclic hpP hcyc)
        have hk0 : k ≠ 0 := by
          rintro rfl
          exact hXne (Subgroup.card_eq_one.1 (by simpa using hk))
        rw [hk, show k = 1 by omega, pow_one]
      refine hN X (hXP₁.trans inf_le_left) hXcard ?_
      rintro rfl
      have hP₀L : X ≤ rankThreeLayer (centralizer (X : Set G)) := hid ▸ (hXP₁.trans inf_le_right)
      have hLC : rankThreeLayer (centralizer (X : Set G)) ≤ centralizer (X : Set G) :=
        uc22p22q_layer_le _
      have hcard : Nat.card X = p := hXcard
      have hz : ∀ z ∈ X, z = 1 := by
        intro z hz
        have hLie' : LieModel ↥(rankThreeLayer (centralizer (X : Set G))) .PSL 2 p n := by
          rw [← hid]
          exact hLie
        have hconj := CFSG.ComponentClassification.CatFactsL4U4.Idx.conj_injective_of_lieModel hLie'
        have hzc : (⟨z, hP₀L hz⟩ : ↥(rankThreeLayer (centralizer (X : Set G)))) ∈
            Subgroup.center ↥(rankThreeLayer (centralizer (X : Set G))) := by
          rw [Subgroup.mem_center_iff]
          intro l
          apply Subtype.ext
          exact ((Subgroup.mem_centralizer_iff.1 (hLC l.2)) z hz).symm
        have h1 : (MulAut.conj (⟨z, hP₀L hz⟩ : ↥(rankThreeLayer (centralizer (X : Set G))))) =
            MulAut.conj 1 := by
          ext l
          have hl : (l : G) * z = z * (l : G) :=
            congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc l)
          simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, one_mul,
            inv_one, mul_one]
          rw [mul_inv_eq_iff_eq_mul]
          exact hl.symm
        have := hconj h1
        exact congrArg Subtype.val this
      have : X = ⊥ := (Subgroup.eq_bot_iff_forall X).2 hz
      exact hpP.one_lt.ne' (by rw [← hcard, this]; simp)
    · exact uc22p22q_normalizer_le_of_noncyclic D h61 hpσ hXM (hH.sylow.isPGroup.to_le (hXP₁.trans inf_le_left)) hcyc
  · rw [hid]
    exact hfrob

end CFSG.LocalAnalysis.UniquenessCase.UC22
