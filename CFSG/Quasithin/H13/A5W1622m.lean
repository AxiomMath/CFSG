module

public import CFSG.Quasithin.Background.C41PfCorr
public import CFSG.Quasithin.H13.A5W1622a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

@[expose] def z0Of {G : Type} [Group G] (v : G) (K₀ : Subgroup G) : Subgroup G :=
  Subgroup.closure
    {x | x ∈ pCoreOf 2 K₀ ∧ ∀ r ∈ pCoreOf 2 K₀, x * r * x⁻¹ * r⁻¹ ∈ Subgroup.zpowers v}

@[expose] def Lem13622Case4Z0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K₀ : Subgroup G, K₀ ≤ Subgroup.centralizer ({S.v12} : Set G) → K₀ ∈ lFamily S.Tv →
      S.Tv ≤ Subgroup.normalizer (K₀ : Set G) → ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G) →
      S.Lv ≤ K₀ →
      (∃ (F : Type) (_ : Field F) (_ : Fintype F)
        (α : ↥K₀ →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)), Fintype.card F = 2 ∧
          IsModO2Surj K₀ α) →
      C134CorrLocal.IsC134Case4Corr (K₀ ⊔ S.Tv) S.Tv K₀ → S.v12 ∈ c134CQ (K₀ ⊔ S.Tv) K₀ →
        ⁅z0Of S.v12 K₀, K₀⁆ = ⁅centerOf (pCoreOf 2 K₀), K₀⁆

theorem card_eq_two_of_not_dvd {G : Type} [Group G] {K₀ : Subgroup G} {F : Type} [Field F]
    [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {α : ↥K₀ →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    (hα : IsModO2Surj K₀ α) (h16 : ¬ 16 ∣ Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) :
    Fintype.card F = 2 := by
  have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) := by
    rw [Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv,
      ← hα.2, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα.1).toEquiv]
  have hU := Subgroup.card_subgroup_dvd_card
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 F)
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_unitriangular,
    Nat.card_eq_fintype_card (α := F), hF, h1] at hU
  rcases n with _ | _ | n
  · exfalso
    have := Fintype.one_lt_card (α := F)
    rw [hF] at this
    norm_num at this
  · rw [hF, pow_one]
  · exfalso
    apply h16
    refine dvd_trans ?_ hU
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ∣ 2 ^ ((n + 2) * 3) := pow_dvd_pow 2 (by omega)
      _ = (2 ^ (n + 2)) ^ (3 * (3 - 1) / 2) := by rw [← pow_mul]

theorem le_normalizer_closure {G : Type} [Group G] {K : Subgroup G} {s : Set G}
    (hs : ∀ g ∈ K, ∀ x ∈ s, g * x * g⁻¹ ∈ s) :
    K ≤ Subgroup.normalizer ((Subgroup.closure s : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hs g hg y hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have := hs g⁻¹ (K.inv_mem hg) x hx
      simpa using this
    · show g * (g⁻¹ * x * g) * g⁻¹ = x
      group

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem c134Q_facts (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G)) :
    c134Q (K₀ ⊔ S.Tv) K₀ ≤ pCoreOf 2 K₀ ∧ c134Q (K₀ ⊔ S.Tv) K₀ ≤ S.Tv ∧
      K₀ ≤ Subgroup.normalizer ((c134Q (K₀ ⊔ S.Tv) K₀ : Subgroup G) : Set G) ∧
      blockU K₀ ≤ c134Q (K₀ ⊔ S.Tv) K₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G₀ := K₀ ⊔ S.Tv with hG₀
  have hsyl : IsSylowTwoOf S.Tv G₀ :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv h1222 h517) le_sup_right (sup_le hK₀G S.Tv_le_Gv)
  have hOT : pCoreOf 2 G₀ ≤ S.Tv := pCoreOf_le_of_isSylowTwoOf hsyl
  have hG₀N : G₀ ≤ Subgroup.normalizer ((pCoreOf 2 G₀ : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₀
  have hK₀N : G₀ ≤ Subgroup.normalizer (K₀ : Set G) := sup_le Subgroup.le_normalizer hTK₀
  have hKQ : K₀ ≤ Subgroup.normalizer ((c134Q G₀ K₀ : Subgroup G) : Set G) :=
    le_normalizer_commutator (le_sup_left.trans hG₀N) Subgroup.le_normalizer
  have hQO : c134Q G₀ K₀ ≤ pCoreOf 2 G₀ := by
    rw [c134Q, Subgroup.commutator_le]
    intro r hr k hk
    have h1 : k * r⁻¹ * k⁻¹ ∈ pCoreOf 2 G₀ :=
      (Subgroup.mem_normalizer_iff.mp (hG₀N ((le_sup_left : K₀ ≤ G₀) hk)) _).mp
        ((pCoreOf 2 G₀).inv_mem hr)
    rw [commutatorElement_def]
    have e : r * k * r⁻¹ * k⁻¹ = r * (k * r⁻¹ * k⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 G₀).mul_mem hr h1
  have hQK : c134Q G₀ K₀ ≤ K₀ := by
    rw [c134Q, Subgroup.commutator_le]
    intro r hr k hk
    have h1 : r * k * r⁻¹ ∈ K₀ :=
      (Subgroup.mem_normalizer_iff.mp (hK₀N (hOT.trans le_sup_right hr)) _).mp hk
    rw [commutatorElement_def]
    exact K₀.mul_mem h1 (K₀.inv_mem hk)
  have hO2 : IsPGroup 2 ↥(pCoreOf 2 G₀) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₀
  have hQK₀ : c134Q G₀ K₀ ≤ pCoreOf 2 K₀ :=
    le_pCoreOf_of_normalizes hQK hKQ (hO2.to_le hQO)
  refine ⟨hQK₀, hQO.trans hOT, hKQ, ?_⟩
  have hnorm : (K₀.subgroupOf G₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hK₀N
  have hO : pCoreOf 2 K₀ ≤ pCoreOf 2 G₀ :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K₀ G₀ le_sup_left
      hnorm
  exact Subgroup.commutator_mono hO le_rfl

theorem comm_a_mem_center_of_not_mem (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀p : ⁅K₀, K₀⁆ = K₀) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hv : S.v12 ∉ c134Q (K₀ ⊔ S.Tv) K₀) :
    ∀ k ∈ K₀, k⁻¹ * S.a * k * S.a⁻¹ ∈ centerOf (c134Q (K₀ ⊔ S.Tv) K₀) := by
  obtain ⟨-, hQT, hKQ, hUQ⟩ := S.c134Q_facts h1222 h517 hK₀G hTK₀
  obtain ⟨hcommA, -⟩ := S.comm_mem_blockU h1222 h517 hK₀G hK₀p hTK₀ hchar
  set Q := c134Q (K₀ ⊔ S.Tv) K₀ with hQdef
  intro k hk
  have hxQ : k⁻¹ * S.a * k * S.a⁻¹ ∈ Q := hUQ (hcommA k hk)
  refine ⟨hxQ, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
  have hrT : r ∈ S.Tv := hQT hr
  have hkr : k * r * k⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hKQ hk) r).mp hr
  obtain ⟨m₁, hm₁⟩ := Subgroup.mem_zpowers_iff.mp (S.comm_a_Tv hrT)
  obtain ⟨m₂, hm₂⟩ := Subgroup.mem_zpowers_iff.mp (S.comm_a_Tv (hQT hkr))
  have hvc : ∀ g ∈ Subgroup.centralizer ({S.v12} : Set G), ∀ m : ℤ,
      g * S.v12 ^ m = S.v12 ^ m * g := fun g hg m =>
    ((Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hg) m)).eq
  have hkG : k ∈ Subgroup.centralizer ({S.v12} : Set G) := hK₀G hk
  have h1 : S.a * r * S.a⁻¹ = S.v12 ^ m₁ * r := by
    rw [hm₁]; group
  have h2 : S.a * (k * r * k⁻¹) * S.a⁻¹ = S.v12 ^ m₂ * (k * r * k⁻¹) := by
    rw [hm₂]; group
  have hx : (k⁻¹ * S.a * k * S.a⁻¹) * r * (k⁻¹ * S.a * k * S.a⁻¹)⁻¹ * r⁻¹ =
      S.v12 ^ (m₂ - m₁) := by
    have e1 : (k⁻¹ * S.a * k * S.a⁻¹) * r * (k⁻¹ * S.a * k * S.a⁻¹)⁻¹ =
        k⁻¹ * (S.a * (k * (S.a⁻¹ * r * S.a) * k⁻¹) * S.a⁻¹) * k := by group
    have h1' : S.a⁻¹ * r * S.a = S.v12 ^ (-m₁) * r := by
      have hva : S.a⁻¹ * S.v12 ^ m₁ = S.v12 ^ m₁ * S.a⁻¹ :=
        hvc _ (Subgroup.inv_mem _ S.a_mem_Gv) m₁
      have hr' : r = S.v12 ^ m₁ * (S.a⁻¹ * r * S.a) := by
        calc r = S.a⁻¹ * (S.a * r * S.a⁻¹) * S.a := by group
          _ = S.a⁻¹ * (S.v12 ^ m₁ * r) * S.a := by rw [h1]
          _ = (S.a⁻¹ * S.v12 ^ m₁) * r * S.a := by group
          _ = (S.v12 ^ m₁ * S.a⁻¹) * r * S.a := by rw [hva]
          _ = S.v12 ^ m₁ * (S.a⁻¹ * r * S.a) := by group
      calc S.a⁻¹ * r * S.a = S.v12 ^ (-m₁) * (S.v12 ^ m₁ * (S.a⁻¹ * r * S.a)) := by
            rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
        _ = S.v12 ^ (-m₁) * r := by rw [← hr']
    rw [e1, h1']
    have e2 : k * (S.v12 ^ (-m₁) * r) * k⁻¹ = S.v12 ^ (-m₁) * (k * r * k⁻¹) := by
      rw [← mul_assoc k, hvc k hkG (-m₁)]; group
    rw [e2]
    have e3 : S.a * (S.v12 ^ (-m₁) * (k * r * k⁻¹)) * S.a⁻¹ =
        S.v12 ^ (-m₁) * (S.a * (k * r * k⁻¹) * S.a⁻¹) := by
      rw [← mul_assoc S.a, hvc _ S.a_mem_Gv (-m₁)]; group
    rw [e3, h2]
    have e4 : k⁻¹ * (S.v12 ^ (-m₁) * (S.v12 ^ m₂ * (k * r * k⁻¹))) * k * r⁻¹ =
        (k⁻¹ * (S.v12 ^ (-m₁) * S.v12 ^ m₂) * k) * (k⁻¹ * (k * r * k⁻¹) * k) * r⁻¹ := by
      group
    rw [e4]
    have e5 : k⁻¹ * (S.v12 ^ (-m₁) * S.v12 ^ m₂) * k = S.v12 ^ (m₂ - m₁) := by
      rw [← zpow_add, show -m₁ + m₂ = m₂ - m₁ by ring, mul_assoc,
        ← hvc k hkG (m₂ - m₁)]
      group
    rw [e5]
    group
  have hxrQ : (k⁻¹ * S.a * k * S.a⁻¹) * r * (k⁻¹ * S.a * k * S.a⁻¹)⁻¹ * r⁻¹ ∈ Q :=
    Q.mul_mem (Q.mul_mem (Q.mul_mem hxQ hr) (Q.inv_mem hxQ)) (Q.inv_mem hr)
  rw [hx] at hxrQ
  have hvq : S.v12 ^ (m₂ - m₁) = 1 := by
    have hv2 : S.v12 ^ 2 = 1 := S.elemAbelian_V.2 _ S.v12_mem_V
    rcases Int.even_or_odd (m₂ - m₁) with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [hj, ← two_mul, zpow_mul, zpow_two, ← pow_two, hv2, one_zpow]
    · exfalso
      apply hv
      have : S.v12 ^ (m₂ - m₁) = S.v12 := by
        rw [hj, zpow_add, zpow_mul, zpow_two, ← pow_two, hv2, one_zpow, one_mul,
          zpow_one]
      rwa [this] at hxrQ
  rw [hvq] at hx
  calc r * (k⁻¹ * S.a * k * S.a⁻¹) =
      ((k⁻¹ * S.a * k * S.a⁻¹) * r * (k⁻¹ * S.a * k * S.a⁻¹)⁻¹ * r⁻¹)⁻¹ *
        (k⁻¹ * S.a * k * S.a⁻¹) * r := by group
    _ = (k⁻¹ * S.a * k * S.a⁻¹) * r := by rw [hx]; group

end Setting

end CFSG.Quasithin.H13.A5
