module

public import CFSG.Quasithin.Vol2.Ch11SecE41Core
public import CFSG.Quasithin.Vol2.Ch11SecA02Recog
public import CFSG.Quasithin.Vol2.Ch11SecDK
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSp StatedScalars)
open scoped IsMulCommutative

theorem card_of_lieModel_G2 (hG2a : SecA.FactG2AdjointOrder) {X : Type} [Group X] {n : ℕ}
    (hn : 1 ≤ n) (hX : LieModel X .G2 0 2 n) : Nat.card X = 2 ^ (6 * n) * SecA.oG2 n := by
  rcases hX with ⟨h, -⟩ | ⟨-, -, -, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact absurd h (by decide)
  · rw [Nat.card_congr e.toEquiv, hG2a K n hn hK, SecA.oG2, ← pow_mul, ← pow_mul,
      mul_comm n 6, mul_comm n 2]
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem card_of_lieModel_PSp {X : Type} [Group X] {n : ℕ} (hX : LieModel X .PSp 2 2 n) :
    ∃ c : ℕ, c ∣ 2 ^ n - 1 ∧ c * Nat.card X = 2 ^ (4 * n) * SecA.oSp4 n := by
  rcases hX with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · refine ⟨Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)), ?_, ?_⟩
    · have := SecA.card_scalars_subgroupOf_dvd (K := K) (StatedSp 2 K)
      rwa [hK] at this
    · rw [Nat.card_congr e.toEquiv, SecA.card_statedProj_mul, SecA.card_Sp_four hK]
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem kindG2_of_lieModel (hG2a : SecA.FactG2AdjointOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n)
    (hX : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .G2 0 2 n) : KindG2 L (fsuV T I) n := by
  obtain ⟨_, -, -, ⟨e⟩, -⟩ := h1102 G T L I n h
  have hn := h.one_lt
  have hc : Nat.card (autOn L (fsuV T I)) = 2 ^ (6 * n) * SecA.oG2 n := by
    rw [← Nat.card_congr e.toEquiv, card_of_lieModel_G2 hG2a (by omega) hX]
  rcases SecA.kind_cases h1102 h with ⟨K, _, _, hK, ⟨e'⟩⟩ | ⟨K, _, _, hK, ⟨e'⟩⟩ | hk
  · obtain ⟨m, hm, hm'⟩ := SecA.card_SL3_eq (by omega) hK
    have h1 := (Nat.card_congr e'.toEquiv).symm.trans hc
    rw [hm'] at h1
    have := SecA.eq_of_two_pow_mul_odd hm (SecA.odd_oG2 (by omega)) h1
    omega
  · obtain ⟨m, hm, hm'⟩ := SecA.card_Sp4_eq (by omega) hK
    have h1 := (Nat.card_congr e'.toEquiv).symm.trans hc
    rw [hm'] at h1
    have := SecA.eq_of_two_pow_mul_odd hm (SecA.odd_oG2 (by omega)) h1
    omega
  · exact hk

theorem kindSp4_of_lieModel (hG2 : SecA.FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hX : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSp 2 2 n) :
    KindSp4 L (fsuV T I) n := by
  obtain ⟨_, -, -, ⟨e⟩, -⟩ := h1102 G T L I n h
  have hn := h.one_lt
  obtain ⟨c, hcd, hcX⟩ := card_of_lieModel_PSp hX
  have hcodd : Odd c := SecA.odd_of_dvd_two_pow_sub_one (by omega) hcd
  have hc : c * Nat.card (autOn L (fsuV T I)) = 2 ^ (4 * n) * SecA.oSp4 n := by
    rw [← Nat.card_congr e.toEquiv, hcX]
  rcases SecA.kind_cases h1102 h with ⟨K, _, _, hK, ⟨e'⟩⟩ | hk | ⟨K, _, _, hK, ⟨e'⟩⟩
  · obtain ⟨m, hm, hm'⟩ := SecA.card_SL3_eq (by omega) hK
    rw [Nat.card_congr e'.toEquiv, hm'] at hc
    have h1 : 2 ^ (3 * n) * (c * m) = 2 ^ (4 * n) * SecA.oSp4 n := by rw [← hc]; ring
    have := SecA.eq_of_two_pow_mul_odd (hcodd.mul hm) (SecA.odd_oSp4 (by omega)) h1
    omega
  · exact hk
  · obtain ⟨m, hm, hm'⟩ := SecA.card_G2_eq hG2 (by omega) hK
    rw [Nat.card_congr e'.toEquiv, hm'] at hc
    have h1 : 2 ^ (6 * n) * (c * m) = 2 ^ (4 * n) * SecA.oSp4 n := by rw [← hc]; ring
    have := SecA.eq_of_two_pow_mul_odd (hcodd.mul hm) (SecA.odd_oSp4 (by omega)) h1
    omega

omit [Finite G] in
theorem pCoreOf_ne_bot_of_faithful {J : Subgroup G} (hJ : quasithinIsFaithfulLocal T J) :
    pCoreOf 2 J ≠ ⊥ := by
  intro h0
  apply hJ.2.2.2
  have hcl : Subgroup.closure {z | z ∈ pCoreOf 2 J ⊓ Subgroup.centralizer (pCoreOf 2 J : Set G) ∧
      z ^ 2 = 1} = ⊥ := by
    rw [eq_bot_iff, Subgroup.closure_le]
    rintro z ⟨⟨hz, -⟩, -⟩
    rw [h0] at hz
    exact hz
  change ⁅Subgroup.closure {z | z ∈ pCoreOf 2 J ⊓ Subgroup.centralizer (pCoreOf 2 J : Set G) ∧
      z ^ 2 = 1}, J⁆ = ⊥
  rw [hcl, Subgroup.commutator_bot_left]

theorem not_case11_1_2Three (hF : SecA.NatFacts) (hR2 : SecB.FactR2Gen) (hSp : FactSp4R2Big)
    (hG2L : FactG2LongRoot) (hG2a : SecA.FactG2AdjointOrder) (hG2 : SecA.FactG2DerivedOrder)
    (h331 : Stmt3_3_1) (h3228 : Ch10.TmpL6_3_2_2_eight) (h1100 : Stmt11_0_0)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1110 : Stmt11_1_0) (h1122 : Stmt11_2_2)
    (h1132 : Stmt11_3_2) (h : Hyp11 G T L I n) {V₁ V₂ K X : Subgroup G}
    (hV₂ : IsVi T L I n 2 V₂) (hn2 : n = 2)
    (h3 : Case11_1_2Three T L K X (LOf L V₁) (LOf L V₂)) : False := by
  subst hn2
  obtain ⟨-, ⟨K₀, hK₀, hK₀K, hK₀ne, hK₀L₁⟩, hall⟩ := h3
  obtain ⟨hmax, hfaith, hK₀M, ⟨I', U, hfsu, hU, hLU⟩, hor⟩ := hall K₀ hK₀ hK₀K hK₀ne hK₀L₁
  have hshape : Shape11 (K₀ ⊔ LOf L V₂) 2 := by
    rcases hor with ⟨-, hJs⟩ | ⟨hJg, -⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨by decide, hJs⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hJg⟩))))
  have hJT : T ≤ Subgroup.normalizer ((K₀ ⊔ LOf L V₂ : Subgroup G) : Set G) :=
    h1100 G T _ 2 hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow hmax hfaith (by norm_num)
      hshape
  have hJ : Hyp11 G T (K₀ ⊔ LOf L V₂) I' 2 := ⟨hfsu, hJT, by norm_num, hshape⟩
  rcases hor with ⟨hLg, hJs⟩ | ⟨hJg, hLs⟩
  · exact false_of_g2_sp4 hF hR2 hSp hG2L h331 hG2 h3228 h1102 h1103 h1110 h1122 h1132 h hJ
      (kindG2_of_lieModel hG2a h1102 h (Or.inr (Or.inl ⟨rfl, by decide, hLg⟩)))
      (kindSp4_of_lieModel hG2 h1102 hJ (Or.inl ⟨by decide, hJs⟩)) hV₂ hU hLU.symm
      fun hle => hK₀M (le_sup_left.trans hle)
  · have hLJ : ¬ L ≤ Subgroup.normalizer ((K₀ ⊔ LOf L V₂ : Subgroup G) : Set G) := by
      intro hle
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hNO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K₀ ⊔ LOf L V₂)
      have hM := SecA.normalizer_le_of_isPGroup h331 h
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K₀ ⊔ LOf L V₂))
        (pCoreOf_ne_bot_of_faithful hfaith) (sup_le (hle.trans hNO) (hJT.trans hNO))
      exact hK₀M (le_sup_left.trans
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans hM))
    exact false_of_g2_sp4 hF hR2 hSp hG2L h331 hG2 h3228 h1102 h1103 h1110 h1122 h1132 hJ h
      (kindG2_of_lieModel hG2a h1102 hJ (Or.inr (Or.inl ⟨rfl, by decide, hJg⟩)))
      (kindSp4_of_lieModel hG2 h1102 h (Or.inl ⟨by decide, hLs⟩)) hU hV₂ hLU hLJ

theorem cComp_centralizer_eq_kOf (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2)
    (h : Hyp11 G T L I n) {V₁ K : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hK : quasithinIsCComponent K (Subgroup.centralizer (V₁ : Set G))) (hle : LOf L V₁ ≤ K) :
    K = KOf L V₁ V₁ := by
  obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n h).1 2 (by norm_num) (by norm_num)
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  obtain ⟨K₁, hLK₁, hK₁, hN, -, -⟩ :=
    h1112 G T L I n 1 V₁ V₁ V₂ X h (Or.inl rfl) hV₁ hV₁ hV₂ hX
  have hKN : quasithinIsCComponent K (Subgroup.normalizer (V₁ : Set G)) :=
    cComp_of_normal (Subgroup.centralizer_le_normalizer (V₁ : Set G))
      (fun t ht => SecA.mem_normalizer_centralizer ht) hK
  rw [SecD.kOf_eq_of_cComp hLK₁ hK₁ hN (SecD.lOf_ne_bot h1110 h hV₁)]
  exact cComp_eq_of_normal hKN hK₁ hN (SecD.lOf_ne_bot h1110 h hV₁) (perfectCore_perfect _) hle
    hLK₁

theorem cases_of_lt (hF : SecA.NatFacts) (hR2 : SecB.FactR2Gen) (hSp : FactSp4R2Big)
    (hG2L : FactG2LongRoot) (hG2a : SecA.FactG2AdjointOrder) (hG2 : SecA.FactG2DerivedOrder)
    (h331 : Stmt3_3_1) (h3228 : Ch10.TmpL6_3_2_2_eight) (h1100 : Stmt11_0_0)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2)
    (h1122 : Stmt11_2_2) (h1132 : Stmt11_3_2) (h : Hyp11 G T L I n) {V₁ K : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hK : quasithinIsCComponent K (Subgroup.centralizer (V₁ : Set G)))
    (hlt : LOf L V₁ < K) : n = 2 ∧ (Case11_1_2One K ∨ Case11_1_2Two L K) := by
  obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n h).1 2 (by norm_num) (by norm_num)
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  obtain ⟨K₁, hLK₁, hK₁, hN, -, hcase⟩ :=
    h1112 G T L I n 1 V₁ V₁ V₂ X h (Or.inl rfl) hV₁ hV₁ hV₂ hX
  have hKK₁ : K = K₁ := by
    rw [cComp_centralizer_eq_kOf h1110 h1112 h hV₁ hK hlt.le,
      SecD.kOf_eq_of_cComp hLK₁ hK₁ hN (SecD.lOf_ne_bot h1110 h hV₁)]
  subst hKK₁
  rcases hcase with heq | ⟨-, hn2, h1 | h2 | h3⟩
  · exact absurd heq (ne_of_lt hlt)
  · exact ⟨hn2, Or.inl h1⟩
  · exact ⟨hn2, Or.inr h2⟩
  · exact (not_case11_1_2Three hF hR2 hSp hG2L hG2a hG2 h331 h3228 h1100 h1102 h1103 h1110 h1122
      h1132 h hV₂ hn2 h3).elim

theorem stmt11_4_1_two (hF : SecA.NatFacts) (hR2 : SecB.FactR2Gen) (hSp : FactSp4R2Big)
    (hG2L : FactG2LongRoot) (hG2a : SecA.FactG2AdjointOrder) (hG2 : SecA.FactG2DerivedOrder)
    (h331 : Stmt3_3_1) (h3228 : Ch10.TmpL6_3_2_2_eight) (h1100 : Stmt11_0_0)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2)
    (h1122 : Stmt11_2_2) (h1132 : Stmt11_3_2) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) :
    ∀ K : Subgroup G, quasithinIsCComponent K (Subgroup.centralizer (V₁ : Set G)) →
      LOf L V₁ < K → Case11_1_2One K ∨ Case11_1_2Two L K := fun _ hK hlt =>
  (cases_of_lt hF hR2 hSp hG2L hG2a hG2 h331 h3228 h1100 h1102 h1103 h1110 h1112 h1122 h1132 h
    hV₁ hK hlt).2

end CFSG.Quasithin.Vol2.Ch11.SecE
