module

public import CFSG.Quasithin.EmptyFaithful.S1565C
public import CFSG.Quasithin.EmptyFaithful.E22NW
public import CFSG.Quasithin.Background.F918P6
public import CFSG.Quasithin.EmptyFaithful.S1565B

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1565

structure Data15365C (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ H K : Subgroup G) (t : G) :
    Prop where
  ctx : Ctx153 G T Mc M V₁ V₂ t
  hstar : IsHStar T M H
  minPar : MinParabolic H T (H ⊓ M)
  sqtk : SQTKGroup ↥H
  three : IsThreePrimeGroup (M ⊓ H)
  H_eq : H = K ⊔ T
  hF : HypF918 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H K
  e22 : E2.E22CasesW H T (H ⊓ M) K
  n_gt : 1 < E1.nParam H
  n_odd : ∀ n : ℕ, 2 ≤ n → Shape15365 n (E2.star (H ⊓ M) H K) →
    E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)) → 3 ≤ n ∧ Odd n
  q_le : qInt (tildeOf (quasithinOmegaOneCenter T) H)
    (tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)) hF.isElemAbelian_tilde ≤ 2

section Inputs

attribute [local instance] commGroupOfFact

@[expose] def Input15365TypesFourC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ H K : Subgroup G) (t : G)
    (D : Data15365C G T Mc M V₁ V₂ H K t), conjClosure K T = K →
    ∀ I : Subgroup G, quasithinOmegaOneCenter T ≤ I → I ≤ conjClosure (ZS153 T M V₁) H →
    ∀ W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)),
      (∀ t ∈ autIH (quasithinOmegaOneCenter T) (ZS153 T M V₁) H T, ∀ w ∈ W, t w ∈ W) →
      IsIrrPlusTildeU D.hF I W → ChiefFreeBelow15365 D.hF M I

@[expose] def Input15365TypesFiveC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ H K : Subgroup G) (t : G)
    (D : Data15365C G T Mc M V₁ V₂ H K t), conjClosure K T ≠ K →
    ∀ I : Subgroup G, quasithinOmegaOneCenter T ≤ I → I ≤ conjClosure (ZS153 T M V₁) H →
    ∀ W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)),
      (∀ t ∈ autIH (quasithinOmegaOneCenter T) (ZS153 T M V₁) H T, ∀ w ∈ W, t w ∈ W) →
      IsIrrPlusTildeU D.hF I W → ChiefFreeBelow15365 D.hF M I

end Inputs

section Extract

variable {Γ : Type} [Group Γ]

theorem e22CasesW_one_data {H T M K : Subgroup Γ} (hE : E2.E22CasesW H T M K)
    (hn : 1 < E1.nParam H) (hK : conjClosure K T ≠ K) :
    kerIn M H = pCoreOf 2 H ∧ ∃ n : ℕ, 2 ≤ n ∧
      (IsPSL 2 2 n ↥(E2.star M H K) ∨ IsSz n ↥(E2.star M H K)) ∧
      E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) := by
  unfold E2.E22CasesW at hE
  simp only at hE
  rcases hE with ⟨hker, _, _, -, -, h⟩ | ⟨hTK, -, -⟩
  · refine ⟨hker, ?_⟩
    rcases h with ⟨n, hn2, hs, hB⟩ | ⟨p, -, -, -, -, -, hnH⟩
    · exact ⟨n, hn2, hs, hB⟩
    · rw [hnH] at hn
      exact absurd hn (lt_irrefl _)
  · exfalso
    apply hK
    apply le_antisymm
    · exact conjClosure_le fun t ht z hz => (Subgroup.mem_normalizer_iff.mp (hTK ht) z).mp hz
    · exact le_conjClosure K T

theorem e22CasesW_two_data {H T M K : Subgroup Γ} (hE : E2.E22CasesW H T M K)
    (hn : 1 < E1.nParam H) (hK0 : conjClosure K T = K) :
    (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
        ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) ∧
      E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) := by
  unfold E2.E22CasesW at hE
  simp only at hE
  rcases hE with ⟨-, t, htT, hcj, -, -⟩ | ⟨-, hker, h⟩
  · exfalso
    apply hcj
    have htN : t ∈ Subgroup.normalizer (K : Set Γ) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have := mem_conjClosure htT hx
        rwa [hK0] at this
      · intro hx
        have := mem_conjClosure (T.inv_mem htT) hx
        rw [hK0] at this
        simpa [mul_assoc] using this
    exact A38.map_conj_eq_iff.mpr htN
  · refine ⟨hker, ?_⟩
    rcases h with ⟨n, hB⟩ | ⟨n, -, -, -, hB, -⟩ | ⟨p, e, -, -, -, -, -, -, -, hnH⟩ |
      ⟨p, -, -, -, -, hnH⟩
    · exact hB.2
    · exact hB
    · rw [hnH] at hn
      exact absurd hn (lt_irrefl _)
    · rw [hnH] at hn
      exact absurd hn (lt_irrefl _)

theorem e22CasesW_two_shape_split {H T M K : Subgroup Γ} (hE : E2.E22CasesW H T M K)
    (hn : 1 < E1.nParam H) (hK0 : conjClosure K T = K) :
    ∃ n : ℕ, 2 ≤ n ∧ Shape15365 n (E2.star M H K) ∧
      ((IsPSL 2 2 n ↥(E2.star M H K) ∨ IsSz n ↥(E2.star M H K) ∨ IsPSU 3 2 n ↥(E2.star M H K)) ∨
        E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K))) := by
  unfold E2.E22CasesW at hE
  simp only at hE
  rcases hE with ⟨-, t, htT, hcj, -, -⟩ | ⟨-, hker, h⟩
  · exfalso
    apply hcj
    have htN : t ∈ Subgroup.normalizer (K : Set Γ) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have := mem_conjClosure htT hx
        rwa [hK0] at this
      · intro hx
        have := mem_conjClosure (T.inv_mem htT) hx
        rw [hK0] at this
        simpa [mul_assoc] using this
    exact A38.map_conj_eq_iff.mpr htN
  · rcases h with ⟨n, hBn⟩ | ⟨n, h1n, hsh, hD, -, hn1⟩ | ⟨p, e, -, -, -, -, -, -, -, hnH⟩ |
      ⟨p, -, -, -, -, hnH⟩
    · refine ⟨n, hBn.1.1, ?_, Or.inl hBn.1.2⟩
      rcases hBn.1.2 with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h1))
    · have hn2 : 2 ≤ n := by
        by_contra hlt
        have hn1' : n = 1 := by omega
        exact absurd (hn1 hn1') (not_le.mpr hn)
      refine ⟨n, hn2, ?_, Or.inr hD⟩
      rcases hsh with h1 | h1
      · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))
    · rw [hnH] at hn
      exact absurd hn (lt_irrefl _)
    · rw [hnH] at hn
      exact absurd hn (lt_irrefl _)

theorem e22CasesW_two_shape {H T M K : Subgroup Γ} (hE : E2.E22CasesW H T M K)
    (hn : 1 < E1.nParam H) (hK0 : conjClosure K T = K) :
    ∃ n : ℕ, 2 ≤ n ∧ Shape15365 n (E2.star M H K) := by
  obtain ⟨n, h2, hs, -⟩ := e22CasesW_two_shape_split hE hn hK0
  exact ⟨n, h2, hs⟩

end Extract

namespace S1565

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_e22_dataC (hE22 : E2.E22StatementW) (h11 : StageLemma14111)
    (c : Ctx153 G T Mc M V₁ V₂ t) {H : Subgroup G} (hH : IsHStar T M H) (hn : 1 < E1.nParam H) :
    ∃ K : Subgroup G, K ∈ cComp H ∧ H = K ⊔ T ∧
      CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) ∧ E2.E22CasesW H T (H ⊓ M) K := by
  have hmin : MinParabolic H T (H ⊓ M) := (c.hyp.lemma_15_3_2_six h11).2 H hH
  have hns : ¬ Group.IsSolvable ↥H := fun hs => absurd (E1.solvable_nParam_le_one hs) (not_le.mpr hn)
  obtain ⟨⟨K, hK, hHK, hq, hcases⟩, -⟩ :=
    hE22.exists_cases hmin (sqtkGroup_of_isHStar c hH) hns
  exact ⟨K, hK, hHK, hq, hcases⟩

theorem odd_of_inputsC (i1 : Input15365Odd) {H M K : Subgroup G}
    (hthree : IsThreePrimeGroup (M ⊓ H)) :
    ∀ n : ℕ, 2 ≤ n → Shape15365 n (E2.star (H ⊓ M) H K) →
      E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)) → 3 ≤ n ∧ Odd n := by
  intro n hn2 hshape hB
  have hodd : Odd n := by
    by_contra hev
    have hev' : Even n := Nat.not_odd_iff_even.mp hev
    have h3 := i1 (E2.StarQuot (H ⊓ M) H) (E2.star (H ⊓ M) H K)
      (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)) n hn2 hev' hshape hB
    have hXH : (H ⊓ M) ⊓ K ≤ H := inf_le_left.trans inf_le_left
    have h1 : Nat.card (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)) ∣
        Nat.card (((H ⊓ M) ⊓ K).subgroupOf H) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (((H ⊓ M) ⊓ K).subgroupOf H) = Nat.card ((H ⊓ M) ⊓ K : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
    have h4 : Nat.card ((H ⊓ M) ⊓ K : Subgroup G) ∣ Nat.card (M ⊓ H : Subgroup G) :=
      Subgroup.card_dvd_of_le fun x hx => ⟨hx.1.2, hx.1.1⟩
    exact hthree ((h3.trans h1).trans (h2 ▸ h4))
  have h3 : 3 ≤ n := by
    obtain ⟨k, hk⟩ := hodd
    omega
  exact ⟨h3, hodd⟩

end S1565

end CFSG.Quasithin
