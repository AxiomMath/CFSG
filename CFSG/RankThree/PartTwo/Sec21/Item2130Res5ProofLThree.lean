module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res3ProofTypes
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem412

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

open Item211Proof

namespace Item2130Res5Proof

variable {G : Type} [Group G] [Finite G]

@[expose] def InducesTypeOnBarSL (L : Subgroup G) (x : G) (k : ℕ) : Prop :=
  ∃ (hx : x ∈ Subgroup.normalizer (L : Set G)) (π : Bool) (p f : ℕ) (K : Type) (_ : Field K)
    (_ : Sec4.PiField π p f K) (_ : Sec4.ModThree π (p ^ f))
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* Sec4.slPi π 3 (p ^ f) K)
    (y : GL (Fin 3) K), y ∈ Sec4.glPi π 3 (p ^ f) K ∧ Sec4.Type123 π (p ^ f) K y k ∧
      ∀ z : L ⧸ aschbacherSolvableCore 3 L,
        ((e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hx⟩) z) : GL (Fin 3) K)) =
          y * (e z : GL (Fin 3) K) * y⁻¹

variable {L A : Subgroup G}

theorem inducesTypeOn_of_lOne (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {Φ₀ : lBar L ≃* lOne L A}
    (hΦ₀ : ∀ l : L, (Φ₀ (l : lBar L) : QuotX L A) = piX L A ⟨l, Subgroup.mem_sup_left l.2⟩)
    {a : G} (haA : a ∈ A) {k : ℕ}
    (h : Sec4.InducesTypeOn (lOne L A) (piX L A ⟨a, Subgroup.mem_sup_right haA⟩) k) :
    Sec4.InducesTypeOn L a k := by
  obtain ⟨hx, π, p, f, K, _, hK, hq, e, y, hy, hyk, hey⟩ := h
  refine ⟨hAL haA, π, p, f, K, inferInstance, hK, hq, (lEquivTheta Φ₀).trans e, y, hy, hyk,
    fun z => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, lEquivTheta_conj hΦ₀ haA (hAL haA) hx z]
  exact hey _

omit [Finite G] in
theorem inducesTypeOnBarSL_of_lOne [Finite G] (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {Φ₀ : lBar L ≃* lOne L A}
    (hΦ₀ : ∀ l : L, (Φ₀ (l : lBar L) : QuotX L A) = piX L A ⟨l, Subgroup.mem_sup_left l.2⟩)
    {a : G} (haA : a ∈ A) {k : ℕ}
    (h : Sec4.InducesTypeOnSL (lOne L A) (piX L A ⟨a, Subgroup.mem_sup_right haA⟩) k) :
    InducesTypeOnBarSL L a k := by
  obtain ⟨hx, π, p, f, K, _, hK, hq, e, y, hy, hyk, hey⟩ := h
  refine ⟨hAL haA, π, p, f, K, inferInstance, hK, hq, Φ₀.trans e, y, hy, hyk, fun z => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, lEquiv_conj hΦ₀ haA (hAL haA) hx z]
  exact hey _

theorem le_sup_zpowers_of_sup_eq (hA : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {b : G} (hbA : b ∈ A)
    (h : aOne L A ⊔ lOne L A =
      Subgroup.zpowers (piX L A ⟨b, Subgroup.mem_sup_right hbA⟩) ⊔ lOne L A) :
    A ≤ L ⊔ Subgroup.zpowers b := by
  set b' : ↥(L ⊔ A) := ⟨b, Subgroup.mem_sup_right hbA⟩ with hb'
  set T : Subgroup ↥(L ⊔ A) := Subgroup.zpowers b' ⊔ L.subgroupOf (L ⊔ A) with hT
  have hmapT : T.map (piX L A) =
      Subgroup.zpowers (piX L A b') ⊔ lOne L A := by
    rw [hT, Subgroup.map_sup, MonoidHom.map_zpowers]
  have hθT : aschbacherSolvableCore 3 ↥(L ⊔ A) ≤ T :=
    (theta_le_subgroupOf hA hAL).trans le_sup_right
  intro a ha
  set a' : ↥(L ⊔ A) := ⟨a, Subgroup.mem_sup_right ha⟩ with ha'
  have h1 : piX L A a' ∈ aOne L A ⊔ lOne L A :=
    Subgroup.mem_sup_left ⟨a', Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  rw [h, ← hmapT] at h1
  have h2 : a' ∈ (T.map (piX L A)).comap (piX L A) := h1
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hθT] at h2
  have h3 : (a' : G) ∈ T.map (L ⊔ A).subtype := ⟨a', h2, rfl⟩
  have hTle : T.map (L ⊔ A).subtype ≤ L ⊔ Subgroup.zpowers b := by
    rw [hT, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [MonoidHom.map_zpowers]
      exact le_sup_right
    · rw [Subgroup.map_subgroupOf_eq_of_le le_sup_left]
      exact le_sup_left
  exact hTle h3

end Item2130Res5Proof

open Item2130Res5Proof

section Certs


@[expose] def Item2130CaseB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (b : G)
    (U₀ Y : Subgroup G),
    Config2130 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 9 → Choice2130 A E c L b U₀ Y →
      ¬ A ≤ Y ⊔ Subgroup.zpowers b → Sec4.IsSLThreePiTheta Y →
      ¬ Sec4.IsHeisCentral ↥(Sec13.lBarA b Y A) (lBar Y) →
      (∀ x ∈ A, ¬ KFacts.InducesStdKind Y x .field ∧ ¬ KFacts.InducesStdKind Y x .graphField) →
      (Sec4.IsTypeCOn A Y ∨ IsTypeCOnBarSL A Y) → c ∉ Y → False

@[expose] def Item2130CaseTypeThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (b : G)
    (U₀ Y : Subgroup G),
    Config2130 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 9 → Choice2130 A E c L b U₀ Y →
      ¬ A ≤ Y ⊔ Subgroup.zpowers b → Sec4.IsSLThreePiTheta Y →
      ¬ Sec4.IsHeisCentral ↥(Sec13.lBarA b Y A) (lBar Y) →
      (∀ x ∈ A, ¬ KFacts.InducesStdKind Y x .field ∧ ¬ KFacts.InducesStdKind Y x .graphField) →
      (∃ a ∈ A, Sec4.InducesTypeOn Y a 3 ∨ InducesTypeOnBarSL Y a 3) →
        c ∈ Y ∨ (c ∈ Y ⊔ Sec4.thetaQuotCentralizer Y ∧ ¬ A ≤ Y ⊔ Sec4.thetaQuotCentralizer Y)

theorem item2130TypesLThree_of (h41 : Sec4.Item4_1LargePrime) (hB : Item2130CaseB)
    (h3 : Item2130CaseTypeThree) : Item2130TypesLThree := by
  intro G _ _ A E U c L b U₀ Y hcfg h9 hC hAY hSL hH hNF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hA : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hA27 : Nat.card A = 27 := by rw [hcfg.card_eq, h9]
  have hbA : b ∈ A := hC.b_mem.1
  have hb1 : b ≠ 1 := hC.b_ne_one
  have hYb : Y ∈ thetaComponentsAt 3 b := lZeroStarAt_subset A b hC.y_mem
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYb
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩))
  have hAL : A ≤ Subgroup.normalizer (Y : Set G) := hC.three_norm A hA hAC
  have hq : IsQuasisimple (lBar Y) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYb
  have hCA : A ⊓ Sec4.thetaQuotCentralizer Y = Subgroup.zpowers b := by
    have hset := Sec13.sectionCentralizer_eq_inf hAL
    rw [hC.sec_cent] at hset
    exact SetLike.coe_injective hset.symm
  have hG4 := hcfg.pair.standing.toTheoremFourHyp
  have hΛ : SectionFourHyp ↥(Y ⊔ A) := hG4.sectionFourHyp
    (fun htop => centralizer_ne_top hG4 hb1 (eq_top_iff.mpr (htop ▸ sup_le hYC hAC)))
  obtain ⟨Φ₀, hΦ₀⟩ := exists_lEquiv hAL
  have hX : SectionFourHyp (QuotX Y A) := sectionFourHyp_quotX h41 hΛ hA hAL Φ₀ hq
  have hq₁ : IsQuasisimple (lOne Y A) := LocalCores.isQuasisimple_of_mulEquiv Φ₀ hq
  have hmax := maximal_aOne (L := Y) hAe hcfg.pair.mem_S.1.2.1
  have hcard₁ : Nat.card (aOne Y A) = 27 := by
    rw [← Nat.card_congr (aEquiv (L := Y) hA).toEquiv, hA27]
  have hb₁ : orderOf (piX Y A ⟨b, Subgroup.mem_sup_right hbA⟩) = 3 := by
    have h1 : (piX Y A ⟨b, Subgroup.mem_sup_right hbA⟩) =
        ((aEquiv (L := Y) hA ⟨b, hbA⟩ : aOne Y A) : QuotX Y A) := rfl
    rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hAe.2 b hbA) hb1
  have hCA₁ := aOne_inf_centralizer hA hAL hbA hCA
  have hTC : Sec4.IsTypeCOn A Y ∨ IsTypeCOnBarSL A Y →
      c ∈ Y ∨ (c ∈ Y ⊔ Sec4.thetaQuotCentralizer Y ∧ ¬ A ≤ Y ⊔ Sec4.thetaQuotCentralizer Y) :=
    fun h => by
      by_cases hcY : c ∈ Y
      · exact Or.inl hcY
      · exact (hB G A E U c L b U₀ Y hcfg h9 hC hAY hSL hH hNF h hcY).elim
  have hT3 : (∃ a ∈ A, Sec4.InducesTypeOn Y a 3 ∨ InducesTypeOnBarSL Y a 3) →
      c ∈ Y ∨ (c ∈ Y ⊔ Sec4.thetaQuotCentralizer Y ∧ ¬ A ≤ Y ⊔ Sec4.thetaQuotCentralizer Y) :=
    h3 G A E U c L b U₀ Y hcfg h9 hC hAY hSL hH hNF
  have hfield : ∀ σ ∈ aOne Y A, KFacts.InducesStdKind (lOne Y A) σ .field → False := by
    intro σ hσ hk
    obtain ⟨a, haA, rfl⟩ := exists_eq_piX_of_mem_aOne hσ
    exact (hNF a haA).1 (inducesStdKind_of_lOne hAL hΦ₀ haA hk)
  obtain ⟨p, e, hp, he, hSL' | hL'⟩ := hSL
  ·
    have hSL₁ : Sec4.IsSLThreePi (lOne Y A) := ⟨p ^ e, isSLThreePiAt_of_mulEquiv Φ₀ hSL'⟩
    rcases Sec4.rank3II_4_11 (QuotX Y A) hX (lOne Y A) (normal_lOne hAL) hSL₁ hq₁ (aOne Y A)
        hmax (by omega) _ hb₁ hCA₁ with
      ⟨-, -, hTC'⟩ | ⟨-, hH'⟩ | ⟨-, -, a, haA, ha3, -⟩ | ⟨-, σ, hσ, hσf, -⟩ | ⟨h81, -⟩ |
        ⟨-, σ, hσ, hσf, -⟩
    · exact hTC (Or.inr (isTypeCOnBarSL_of_lOne hAL hΦ₀ hTC'))
    · exfalso
      obtain ⟨eX⟩ := nonempty_quotX_equiv_lBarA hYb hAC hA hAL
      have eH : ↥(aOne Y A ⊔ lOne Y A) ≃* ↥(Sec13.lBarA b Y A) :=
        (MulEquiv.subgroupCongr aOne_sup_lOne).trans (Subgroup.topEquiv.trans eX)
      exact hH (Sec13.isHeisCentral_of_mulEquiv eH Φ₀.symm hH')
    · obtain ⟨a', ha'A, rfl⟩ := exists_eq_piX_of_mem_aOne haA
      exact hT3 ⟨a', ha'A, Or.inr (inducesTypeOnBarSL_of_lOne hAL hΦ₀ ha'A ha3)⟩
    · exact (hfield σ hσ hσf).elim
    · omega
    · exact (hfield σ hσ hσf).elim
  ·
    have hL₁ : ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi (lOne Y A) p e :=
      ⟨p, e, hp, he, isoLThreePi_of_mulEquiv Φ₀ hL'⟩
    rcases Sec4.rank3II_4_12 (QuotX Y A) hX (lOne Y A) (normal_lOne hAL) hL₁ hq₁ (aOne Y A)
        hmax (by omega) _ hb₁ hCA₁ with
      ⟨-, hsup, -⟩ | ⟨-, hTC'⟩ | ⟨-, ⟨a, haA, ha3⟩, -⟩ | ⟨h81, -⟩
    · exact (hAY (le_sup_zpowers_of_sup_eq hA hAL hbA hsup)).elim
    · exact hTC (Or.inl (isTypeCOn_of_lOne hAL hΦ₀ hTC'))
    · obtain ⟨a', ha'A, rfl⟩ := exists_eq_piX_of_mem_aOne haA
      exact hT3 ⟨a', ha'A, Or.inl (inducesTypeOn_of_lOne hAL hΦ₀ ha'A ha3)⟩
    · omega

end Certs

end CFSG.RankThree.PartTwo.Sec21
