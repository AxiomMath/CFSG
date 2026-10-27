module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847Fields
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenB
public import CFSG.LocalAnalysis.UniquenessCase.UC6S898b
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar
public import CFSG.Adapters.LieModelOrders
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CStrongEmb
public import CFSG.GroupTheory.TwoResidualOddOrder
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3Borel
public import CFSG.LocalAnalysis.WeakClosure81.InFSqPrimeTwoGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
  CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def UC2_14_6 (D : Data G) : Prop :=
  ∀ (Y X : Subgroup G) (n q : ℕ),
    Y ∈ calC D.M → X ≤ Y → Nat.card X = q → IsSU3 (Bar2 Y) n →
    (n % 6 = 1 ∨ n % 6 = 5) → D.M ≤ normalizer (Y : Set G) →
    q.Prime → q ≠ 2 → 2 ^ n ≡ 1 [MOD q] →
    D.sig = {3} → evenRank G = 3 →
    ∀ r : ℕ, r.Prime → 3 < r → r ∣ 2 ^ n + 1 →
    ∀ A : Subgroup G, A ≤ Y → Nat.card A = r → Permutes A D.T →
      UniqueMax D.M (A ⊔ D.T)

theorem uc2_17_36b_isSU3_param_eq
    {X : Type} [Group X] [Finite X] {n n' : ℕ}
    (h : IsSU3 X n) (h' : IsSU3 X n') : n = n' := by
  have hq : Nat.card (X ⧸ Subgroup.center X) = ordTwistedA 2 (2 ^ n) := by
    have hc := CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h.2
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hc
  have hq' : Nat.card (X ⧸ Subgroup.center X) = ordTwistedA 2 (2 ^ n') := by
    have hc := CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h'.2
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hc
  have h1 := CFSG.RankThree.PartTwo.KFacts.padicValNat_ordTwistedA_two
    (m := n) (by have := s13_two_le_of_isU3 h.2; omega)
  have h2 := CFSG.RankThree.PartTwo.KFacts.padicValNat_ordTwistedA_two
    (m := n') (by have := s13_two_le_of_isU3 h'.2; omega)
  rw [← hq] at h1
  rw [← hq'] at h2
  omega

theorem uc2_17_36b_r847_second
    (D : Data G) (h847 : R847SU3G4 D) (hx : DataExt D)
    {V₀ V L X : Subgroup G} {n r : ℕ} (c : Ctx17_33 D V₀ V L n)
    (hML : D.M ≤ normalizer (L : Set G))
    (hXL : X ≤ L) (hXcard : Nat.card X = r) (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1)
    (hNle : ¬ normalizer (X : Set G) ≤ D.M) :
    (n % 6 = 1 ∨ n % 6 = 5) ∧ D.M ≤ normalizer (L : Set G) ∧ evenRank G = 3 ∧
      2 ^ n ≡ 1 [MOD r] ∧ ∀ p ∈ D.sig, p = 3 := by
  have hn2 : 2 ≤ n := s13_two_le_of_isU3 c.shape.2
  have hr2 : r ≠ 2 := uc22p20v_ne_two_of_dvd_sub_one (by omega) hr hrdvd
  have hmod : 2 ^ n ≡ 1 [MOD r] :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_two_pow (n := n))).2 hrdvd).symm
  have hLN : (L.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).2 hML
  have hdata : ∀ p ∈ D.sig, ((n % 6 = 1 ∨ n % 6 = 5) ∧ evenRank G = 3) ∧ p = 3 := by
    intro p hp
    rcases h847 L c.mem_calC hLN n c.shape X hXL r hr hr2 hrdvd hXcard p hp with
      h1 | ⟨hp3, hn6, he⟩
    · exact absurd h1 hNle
    · exact ⟨⟨hn6, he⟩, hp3⟩
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  obtain ⟨⟨hmod6, hrank3⟩, -⟩ := hdata p hp
  exact ⟨hmod6, hML, hrank3, hmod, fun q hq => (hdata q hq).2⟩

theorem uc2_17_36b_barSub_ne_bot (D : Data G) {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_33 D V₀ V L n) (h1735 : R17_35At D V₀ V) :
    barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥ := by
    intro hbot
    let W' : Subgroup (Vtil V₀ V c.hyp125.isElemAbelian) :=
      CFSG.Quasithin.commSub (⊤ : Subgroup (Vtil V₀ V c.hyp125.isElemAbelian))
        (barSub V₀ V c.hyp125.isElemAbelian L)
    have hWbot : W' = ⊥ := by
      dsimp [W']
      rw [hbot, CFSG.Quasithin.commSub_eq_bot_iff]
      intro v _
      simp [CFSG.Quasithin.fixV]
    obtain ⟨S⟩ := (h1735.1 L n c).1
    letI : Field S.K := S.fieldK
    letI : Finite S.K := S.finiteK
    have hn2 : 2 ≤ n := s13_two_le_of_isU3 c.shape.2
    haveI : Nontrivial S.K := by
      rw [← Finite.one_lt_card_iff_nontrivial, S.cardK]
      have h1 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    haveI : Nontrivial (Multiplicative (Fin 3 → S.K)) := inferInstance
    haveI : Nontrivial ↥W' := S.e.toEquiv.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot W').1 inferInstance hWbot

theorem uc2_17_35_v0_ne_bot_of_ne_two (D : Data G) {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_33 D V₀ V L n) (h1735 : R17_35At D V₀ V)
    (hn : n ≠ 2) : V₀ ≠ ⊥ := by
  intro h0
  have h4 := (h1735.2 L n c h0).2.2.1
  have h2n := (h1735.1 L n c).2
  exact hn (by omega)

theorem uc2_17_36b_twoResidual_not_le_conj (D : Data G) (h846 : F08.R846 D)
    {V₀ V L A : Subgroup G} {n q : ℕ} (c : Ctx17_33 D V₀ V L n)
    (hAL : A ≤ L) (hAcard : Nat.card A = q) (hq : q.Prime) (hq3 : 3 < q)
    (hqdiv : q ∣ 2 ^ n + 1) :
    ∀ g : G, g ∉ D.M →
      ¬ CFSG.Quasithin.twoResidual (A ⊔ D.T) ≤ CFSG.Quasithin.conjSubgroup D.M g := by
  intro g hg hle
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have hAle : A ≤ CFSG.Quasithin.twoResidual (A ⊔ D.T) :=
    CFSG.GroupTheory.le_twoResidual_of_odd_card le_sup_left (hAcard ▸ hqodd)
  have hsp := h846 L c.mem_calC n c.shape q hq hq3 hqdiv
  have hg' : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
  refine CFSG.RankThree.PartOne.IsStronglyPEmbedded.not_dvd_card_inf_conj hsp hg' ?_
  have hAinf : A ≤ D.M ⊓ CFSG.Quasithin.conjSubgroup D.M g :=
    le_inf (hAL.trans c.mem_calC.1.le) (hAle.trans hle)
  rw [← hAcard]
  exact Subgroup.card_dvd_of_le hAinf

theorem uc2_17_36b_exists_cartan
    (D : Data G)
    {V₀ V L : Subgroup G} {n q : ℕ} (c : Ctx17_33 D V₀ V L n)
    (hML : D.M ≤ Subgroup.normalizer (L : Set G))
    (hq : q.Prime) (hq3 : 3 < q) (hqdiv : q ∣ 2 ^ n + 1) :
    ∃ A : Subgroup G, A ≤ L ∧ Nat.card A = q ∧ Permutes A D.T := by
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hTL : D.T ≤ Subgroup.normalizer (L : Set G) := hTM.trans hML
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have hT : CFSG.Quasithin.IsSylowIn 2 D.T D.M :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := D.T) (K := D.M)).1 D.sylowM
  have hN : (L.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mpr hML
  have hSyl : CFSG.Quasithin.IsSylowIn 2 (D.T ⊓ L) L :=
    CFSG.Quasithin.IsSylowIn.inf_normal hT hLM hN
  obtain ⟨A, hAL, hAcard, -, hAperm⟩ :=
    exists_permutes_of_isSU3_bar2 hTL hSyl c.shape hq hq3 hqdiv
  exact ⟨A, hAL, hAcard, hAperm⟩

theorem seventeen_thirtysix_b
    (D : Data G) {V₀ V : Subgroup G}
    (h1735 : R17_35At D V₀ V) (h341 : R17_34_1At D V₀ V)
    (h36a : R17_36aAt D V₀ V) (h847 : R847SU3G4 D) (h846 : F08.R846 D) (hx : DataExt D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h146 : UC2_14_6 D)
    (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (h127 : R127 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h183 : W3Thm183 G) :
    R17_36bAt D V₀ V := by
  intro L n c r hr hrdvd X hXcard hXL
  by_contra hNle
  have hML0 : D.M ≤ normalizer (L : Set G) := by
    have h := TwelveTwentyThree.le_normalizer_conjClosure D.M L
    rwa [← h36a L n c] at h
  obtain ⟨hmod6, hML, hrank3, h2nr, hall⟩ :=
    uc2_17_36b_r847_second D h847 hx c hML0 hXL hXcard hr hrdvd hNle
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  have h3sig : 3 ∈ D.sig := by rw [← hall p hp]; exact hp
  have hsig3 : D.sig = {3} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨h3sig, hall⟩
  have hV0 : V₀ ≠ ⊥ := uc2_17_35_v0_ne_bot_of_ne_two D c h1735 (by
    intro h2
    subst h2
    norm_num at hmod6)
  have hk1 : D.k = 1 := s15_Thirteen_k_eq_one_of_three_mem D hSg h1219 h3sig
  have hn2 : 2 ≤ n := s13_two_le_of_isU3 c.shape.2
  have hn3 : n ≠ 3 := by
    intro h3
    subst h3
    norm_num at hmod6
  have hr2 : r ≠ 2 := uc22p20v_ne_two_of_dvd_sub_one (by omega) hr hrdvd
  have hL1 : barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥ :=
    uc2_17_36b_barSub_ne_bot D c h1735
  obtain ⟨q, hq, hq3, hqdiv⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S898.exists_prime_gt_three_dvd (n := n) hn2 hn3
  obtain ⟨A, hAL, hAcard, hAperm⟩ :=
    uc2_17_36b_exists_cartan D c hML hq hq3 hqdiv
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  let H : Subgroup G := A ⊔ D.T
  have hHinF : InFSq 1 H :=
    CFSG.LocalAnalysis.WeakClosure81.inFSq_one_of_prime_mul_two_group
      A D.T q hq hqodd hAcard D.sylowM.isPGroup hAperm
  let Δ : Finset (Subgroup G) := {H}
  have hsup : (⨆ K ∈ Δ, K) = H := by simp [Δ]
  have hΔU : UniqueMax D.M (⨆ K ∈ Δ, K) := by
    rw [hsup]
    exact h146 L X n r c.mem_calC hXL hXcard c.shape hmod6 hML hr hr2
      h2nr hsig3 hrank3 q hq hq3 hqdiv A hAL hAcard hAperm
  have hΔ : ∀ K ∈ Δ, D.T ≤ K ∧ K ≤ D.M := by
    intro K hK
    simp only [Δ, Finset.mem_singleton] at hK
    subst K
    exact ⟨le_sup_right, sup_le (hAL.trans c.mem_calC.1.le) D.sylowM.le⟩
  let ι : Subgroup G → ℕ := fun _ => 1
  have hι : ∀ K ∈ Δ, InFSq (ι K) K := by
    intro K hK
    simp only [Δ, Finset.mem_singleton] at hK
    subst K
    exact hHinF
  have hmax : Δ.sup ι = 1 := rfl
  have hO2 : ∀ K ∈ Δ, ∀ g : G, g ∉ D.M →
      ¬ CFSG.Quasithin.twoResidual K ≤ CFSG.Quasithin.conjSubgroup D.M g := by
    intro K hK g hg
    simp only [Δ, Finset.mem_singleton] at hK
    subst K
    exact uc2_17_36b_twoResidual_not_le_conj D h846 c hAL hAcard hq hq3 hqdiv g hg
  have hmbar : mBar D.M V₀ V c.hyp125.isElemAbelian = 2 * n := (h1735.1 L n c).2
  have hmk : D.k + 1 < mBar D.M V₀ V c.hyp125.isElemAbelian := by
    rw [hk1, hmbar]
    omega
  have hmain := twelve_twentyThree_three_two D hx h61 h66 h127 h1114 h162 hTor h1482 h183
    c.hyp125 hV0 c.mem_calC.1 c.shape.1 hL1 hΔ hΔU ι hι hO2 hmax hmk
  have hb := h341 L n c
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
