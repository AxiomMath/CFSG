module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XChief
public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddAbel

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13
open scoped commutatorElement

private theorem le_normalizer_commutator_L829N {G : Type} [Group G] {Λ A B : Subgroup G}
    (hA : Λ ≤ Subgroup.normalizer (A : Set G)) (hB : Λ ≤ Subgroup.normalizer (B : Set G)) :
    Λ ≤ Subgroup.normalizer (⁅A, B⁆ : Subgroup G) := by
  have key : ∀ y ∈ Λ, ∀ g ∈ (⁅A, B⁆ : Subgroup G), y * g * y⁻¹ ∈ (⁅A, B⁆ : Subgroup G) := by
    intro y hy
    have hle : (⁅A, B⁆ : Subgroup G) ≤
        (⁅A, B⁆ : Subgroup G).comap (MulAut.conj y).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_comap]
      show y * ⁅a, b⁆ * y⁻¹ ∈ (⁅A, B⁆ : Subgroup G)
      have e : y * ⁅a, b⁆ * y⁻¹ = ⁅y * a * y⁻¹, y * b * y⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.mp (hA hy) a).mp ha)
        ((Subgroup.mem_normalizer_iff.mp (hB hy) b).mp hb)
    exact fun g hg => hle hg
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact fun hg => key y hy g hg
  · intro hg
    have e : y⁻¹ * (y * g * y⁻¹) * y⁻¹⁻¹ = g := by group
    have := key y⁻¹ (Λ.inv_mem hy) _ hg
    rwa [e] at this

private theorem le_of_le_sup_commutator_nilpotent_L829N {Γ : Type} [Group Γ]
    [Group.IsNilpotent Γ] {N M : Subgroup Γ} [M.Normal] (h : N ≤ M ⊔ ⁅N, ⊤⁆) : N ≤ M := by
  have key : ∀ k : ℕ, N ≤ M ⊔ (⊤ : Subgroup Γ).lowerCentralSeries k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc : ⁅N, ⊤⁆ ≤ M ⊔ (⊤ : Subgroup Γ).lowerCentralSeries (k + 1) := by
        calc ⁅N, ⊤⁆ ≤ ⁅M ⊔ (⊤ : Subgroup Γ).lowerCentralSeries k, ⊤⁆ :=
              Subgroup.commutator_mono_left ih
          _ = ⁅M, ⊤⁆ ⊔ ⁅(⊤ : Subgroup Γ).lowerCentralSeries k, ⊤⁆ :=
              Subgroup.commutator_sup_right _ _ _
          _ ≤ M ⊔ (⊤ : Subgroup Γ).lowerCentralSeries (k + 1) := by
              rw [Subgroup.lowerCentralSeries_succ]
              exact sup_le_sup (Subgroup.commutator_le_left _ _) le_rfl
      exact h.trans (sup_le le_sup_left hc)
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries (⊤ : Subgroup Γ)).mp
    (Group.isNilpotent_top.mpr ‹Group.IsNilpotent Γ›)
  have := key n
  rw [hn, sup_bot_eq] at this
  exact this

private theorem le_of_le_sup_commutator_pGroup_L829N {G : Type} [Group G] [Finite G]
    {T M N : Subgroup G} (hT : IsPGroup 2 ↥T) (hMT : M ≤ T)
    (hTM : T ≤ Subgroup.normalizer (M : Set G)) (hNT : N ≤ T) (h : N ≤ M ⊔ ⁅N, T⁆) :
    N ≤ M := by
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  haveI : (M.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMT).mpr hTM
  have h' : N.subgroupOf T ≤ M.subgroupOf T ⊔ ⁅N.subgroupOf T, ⊤⁆ := by
    rw [← Subgroup.map_le_map_iff_of_injective (T.subtype_injective), Subgroup.map_sup,
      Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le hNT, Subgroup.map_subgroupOf_eq_of_le hMT]
    exact h
  have h'' := Subgroup.map_mono (f := T.subtype) (le_of_le_sup_commutator_nilpotent_L829N h')
  rwa [Subgroup.map_subgroupOf_eq_of_le hNT, Subgroup.map_subgroupOf_eq_of_le hMT] at h''

private theorem coatom_contains_sq_comm_L829N {P : Type} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {M : Subgroup P} (hM : IsCoatom M) : (∀ x : P, x * x ∈ M) ∧ (∀ x y : P, ⁅x, y⁆ ∈ M) := by
  haveI : Group.IsNilpotent P := hP.isNilpotent
  haveI : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M Group.normalizerCondition_of_isNilpotent hM
  have hidx : M.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hP).mp hM
  have hcard : Nat.card (P ⧸ M) = 2 := by rw [← Subgroup.index_eq_card, hidx]
  haveI : IsCyclic (P ⧸ M) := isCyclic_of_prime_card hcard
  haveI := IsCyclic.commutative (α := P ⧸ M)
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · have h := Subgroup.pow_index_mem M x
    rwa [hidx, pow_two] at h
  · have h1 : (QuotientGroup.mk' M) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact IsMulCommutative.is_comm.comm _ _
    exact (QuotientGroup.eq_one_iff _).mp h1

private theorem mem_frattini_of_coatom_L829N {P : Type} [Group P] (x : P)
    (h : ∀ M : Subgroup P, IsCoatom M → x ∈ M) : x ∈ frattini P := by
  simp only [frattini, Order.radical, Subgroup.mem_iInf, Set.mem_setOf_eq]
  exact fun M hM => h M hM

private theorem exists_odd_prime_orderOf_L829N {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hH : ¬ IsPGroup 2 ↥H) : ∃ y ∈ H, ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ orderOf y = q := by
  obtain ⟨q, hq, hqd, hq2⟩ : ∃ q : ℕ, q.Prime ∧ q ∣ Nat.card H ∧ q ≠ 2 := by
    by_contra hc
    simp only [not_exists, not_and, ne_eq, not_not] at hc
    exact hH (IsPGroup.iff_card.mpr ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd
      Nat.card_pos.ne' fun hd hdvd => hc _ hd hdvd⟩)
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hqd
  exact ⟨x, x.2, q, hq, hq2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem exists_chief_factor_odd {G : Type} [Group G] [Finite G] {Λ H : Subgroup G}
    (hHΛ : H ≤ Λ) (hchar : QuasithinUnique.CharTwo Λ) (hH : ¬ IsPGroup 2 ↥H) :
    ∃ y : G, ∃ W₀ W₁ : Subgroup G, y ∈ H ∧ Odd (orderOf y) ∧ W₀ < W₁ ∧ W₁ ≤ pCoreOf 2 Λ ∧
      Λ ≤ Subgroup.normalizer (W₀ : Set G) ∧ Λ ≤ Subgroup.normalizer (W₁ : Set G) ∧
      (∀ B : Subgroup G, W₀ ≤ B → B ≤ W₁ → Λ ≤ Subgroup.normalizer (B : Set G) →
        B = W₀ ∨ B = W₁) ∧
      ¬ ⁅W₁, Subgroup.zpowers y⁆ ≤ W₀ := by
  classical
  obtain ⟨y, hyH, q, hq, hq2, hyq⟩ := exists_odd_prime_orderOf_L829N H hH
  haveI : Fact q.Prime := ⟨hq⟩
  have hyΛ : y ∈ Λ := hHΛ hyH
  have hchar' : Λ ⊓ Subgroup.centralizer ((pCoreOf 2 Λ : Subgroup G) : Set G) ≤ pCoreOf 2 Λ :=
    hchar
  have hRp : IsPGroup 2 ↥(pCoreOf 2 Λ) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Λ
  have hRY : ¬ ⁅pCoreOf 2 Λ, Subgroup.zpowers y⁆ ≤ ⊥ := by
    intro hle
    have hcent : y ∈ Subgroup.centralizer ((pCoreOf 2 Λ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have h1 : ⁅r, y⁆ ∈ (⊥ : Subgroup G) :=
        hle (Subgroup.commutator_mem_commutator hr (Subgroup.mem_zpowers y))
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hyR : y ∈ pCoreOf 2 Λ := hchar' (Subgroup.mem_inf.mpr ⟨hyΛ, hcent⟩)
    obtain ⟨k, hk⟩ := hRp ⟨y, hyR⟩
    have hk' : y ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hdvd : q ∣ 2 ^ k := by
      rw [← hyq]
      exact orderOf_dvd_of_pow_eq_one hk'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd))
  have hZp : IsPGroup q ↥(Subgroup.zpowers y) :=
    IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, hyq, pow_one]⟩
  have hcop : ∀ A : Subgroup G, A ≤ pCoreOf 2 Λ → Subgroup.zpowers y ≤
      Subgroup.normalizer (A : Set G) →
      ⁅⁅A, Subgroup.zpowers y⁆, Subgroup.zpowers y⁆ = ⁅A, Subgroup.zpowers y⁆ := by
    intro A hA hYA
    have hAp : IsPGroup 2 ↥A := hRp.to_le hA
    exact coprime_commutator_commutator_eq hYA
      (IsPGroup.coprime_card_of_ne q 2 hq2 _ _ hZp hAp)
  have hΛR : Λ ≤ Subgroup.normalizer ((pCoreOf 2 Λ : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Λ
  have hΛU : Λ ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_of_normal
  obtain ⟨W₀, W₁, _, hW₀W₁, hW₁R, hΛW₀, hΛW₁, hchief, hW₁Y⟩ :=
    CFSG.Quasithin.H13.L827X.exists_chief_factor_comm hΛR hΛU bot_le
      (Subgroup.zpowers_le.mpr hyΛ) (Subgroup.commutator_bot_left _).le hRY hcop
  exact ⟨y, W₀, W₁, hyH, by rw [hyq]; exact hq.odd_of_ne_two hq2, hW₀W₁, hW₁R, hΛW₀, hΛW₁,
    hchief, hW₁Y⟩

theorem chief_section_elemAb {G : Type} [Group G] [Finite G] {Λ W₀ W₁ : Subgroup G}
    (hlt : W₀ < W₁) (hp : IsPGroup 2 ↥W₁) (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G))
    (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (hchief : ∀ B : Subgroup G, W₀ ≤ B → B ≤ W₁ → Λ ≤ Subgroup.normalizer (B : Set G) →
      B = W₀ ∨ B = W₁) :
    (∀ x ∈ W₁, ∀ y ∈ W₁, x * y * x⁻¹ * y⁻¹ ∈ W₀) ∧ (∀ x ∈ W₁, x * x ∈ W₀) := by
  classical
  have hΦΛ : Λ ≤ Subgroup.normalizer (((frattini ↥W₁).map W₁.subtype : Subgroup G) : Set G) :=
    h1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (frattini ↥W₁))
  have hCΛ : Λ ≤ Subgroup.normalizer
      ((((frattini ↥W₁).map W₁.subtype) ⊔ W₀ : Subgroup G) : Set G) :=
    (le_inf hΦΛ h0).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hCle : (frattini ↥W₁).map W₁.subtype ⊔ W₀ ≤ W₁ :=
    sup_le (Subgroup.map_subtype_le _) hlt.le
  have hfr : ∀ a b : ↥W₁, ⁅a, b⁆ ∈ frattini ↥W₁ ∧ a * a ∈ frattini ↥W₁ := by
    intro a b
    exact ⟨mem_frattini_of_coatom_L829N _ fun M hM => (coatom_contains_sq_comm_L829N hp hM).2 a b,
      mem_frattini_of_coatom_L829N _ fun M hM => (coatom_contains_sq_comm_L829N hp hM).1 a⟩
  have hne : (frattini ↥W₁).map W₁.subtype ⊔ W₀ ≠ W₁ := by
    intro heq
    have hW₀ne : W₀.subgroupOf W₁ ≠ ⊤ := by
      rw [Ne, Subgroup.subgroupOf_eq_top]
      exact not_le_of_gt hlt
    obtain ⟨M, hMc, hMW⟩ :=
      (eq_top_or_exists_le_coatom (W₀.subgroupOf W₁)).resolve_left hW₀ne
    have hΦM : frattini ↥W₁ ≤ M := frattini_le_coatom hMc
    have hle : (frattini ↥W₁).map W₁.subtype ⊔ W₀ ≤ M.map W₁.subtype := by
      refine sup_le (Subgroup.map_mono hΦM) ?_
      intro w hw
      exact Subgroup.mem_map.mpr ⟨⟨w, hlt.le hw⟩, hMW (Subgroup.mem_subgroupOf.mpr hw), rfl⟩
    rw [heq] at hle
    have hMtop : M = ⊤ := by
      rw [eq_top_iff]
      intro p _
      obtain ⟨m, hm, hmp⟩ := Subgroup.mem_map.mp (hle p.2)
      have hmp' : m = p := Subtype.ext hmp
      exact hmp' ▸ hm
    exact hMc.1 hMtop
  have hΦW₀ : (frattini ↥W₁).map W₁.subtype ≤ W₀ := by
    rcases hchief _ le_sup_right hCle hCΛ with h | h
    · exact le_sup_left.trans h.le
    · exact absurd h hne
  constructor
  · intro x hx y hy
    have hm := Subgroup.mem_map_of_mem W₁.subtype (hfr ⟨x, hx⟩ ⟨y, hy⟩).1
    have e : W₁.subtype ⁅(⟨x, hx⟩ : ↥W₁), ⟨y, hy⟩⁆ = x * y * x⁻¹ * y⁻¹ := by
      simp [commutatorElement_def]
    rw [e] at hm
    exact hΦW₀ hm
  · intro x hx
    have hm := Subgroup.mem_map_of_mem W₁.subtype (hfr ⟨x, hx⟩ ⟨x, hx⟩).2
    have e : W₁.subtype ((⟨x, hx⟩ : ↥W₁) * ⟨x, hx⟩) = x * x := by
      simp
    rw [e] at hm
    exact hΦW₀ hm

theorem chief_normal_two_trivial {G : Type} [Group G] [Finite G] {Λ W₀ W₁ Q : Subgroup G}
    (hlt : W₀ < W₁) (hp : IsPGroup 2 ↥W₁) (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G))
    (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (hchief : ∀ B : Subgroup G, W₀ ≤ B → B ≤ W₁ → Λ ≤ Subgroup.normalizer (B : Set G) →
      B = W₀ ∨ B = W₁)
    (hQΛ : Q ≤ Λ) (hQ2 : IsPGroup 2 ↥Q) (hQn : ∀ y ∈ Λ, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) :
    ∀ x ∈ W₁, ∀ q ∈ Q, q * x * q⁻¹ * x⁻¹ ∈ W₀ := by
  classical
  have hcomm := chief_section_elemAb hlt hp h0 h1 hchief
  have hQW₁ : Q ≤ Subgroup.normalizer (W₁ : Set G) := hQΛ.trans h1
  have hQW₀ : Q ≤ Subgroup.normalizer (W₀ : Set G) := hQΛ.trans h0
  have hΛQ : Λ ≤ Subgroup.normalizer (Q : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact fun hg => hQn y hy g hg
    · intro hg
      have e : y⁻¹ * (y * g * y⁻¹) * y⁻¹⁻¹ = g := by group
      have := hQn y⁻¹ (Λ.inv_mem hy) _ hg
      rwa [e] at this
  have hVΛ : Λ ≤ Subgroup.normalizer (⁅W₁, Q⁆ : Subgroup G) :=
    le_normalizer_commutator_L829N h1 hΛQ
  have hVW₁ : ⁅W₁, Q⁆ ≤ W₁ := Subgroup.le_normalizer_iff_commutator_le_left.mp hQW₁
  have hCΛ : Λ ≤ Subgroup.normalizer ((⁅W₁, Q⁆ ⊔ W₀ : Subgroup G) : Set G) :=
    (le_inf hVΛ h0).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hCle : ⁅W₁, Q⁆ ⊔ W₀ ≤ W₁ := sup_le hVW₁ hlt.le
  rcases hchief _ le_sup_right hCle hCΛ with hC | hC
  · intro x hx q hq
    have hV : ⁅x, q⁆ ∈ W₀ := le_sup_left.trans hC.le (Subgroup.commutator_mem_commutator hx hq)
    have e : (⁅x, q⁆ : G)⁻¹ = q * x * q⁻¹ * x⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [← e]
    exact W₀.inv_mem hV
  · exfalso
    have hW₁W₀ : W₁ ≤ Subgroup.normalizer (W₀ : Set G) := by
      refine Subgroup.le_normalizer_iff_commutator_le_right.mpr ?_
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact hcomm.1 a ha b (hlt.le hb)
    have hT : IsPGroup 2 ↥(W₁ ⊔ Q) := IsPGroup.to_sup_of_normal_left' hp hQ2 hQW₁
    have hTW₀ : W₁ ⊔ Q ≤ Subgroup.normalizer (W₀ : Set G) := sup_le hW₁W₀ hQW₀
    have hN : W₁ ≤ W₀ ⊔ ⁅W₁, W₁ ⊔ Q⁆ := by
      calc W₁ = ⁅W₁, Q⁆ ⊔ W₀ := hC.symm
        _ ≤ ⁅W₁, W₁ ⊔ Q⁆ ⊔ W₀ := sup_le_sup_right (Subgroup.commutator_mono_right le_sup_right) W₀
        _ = W₀ ⊔ ⁅W₁, W₁ ⊔ Q⁆ := sup_comm _ _
    exact not_le_of_gt hlt
      (le_of_le_sup_commutator_pGroup_L829N hT (le_sup_of_le_left hlt.le) hTW₀ le_sup_left hN)

end CFSG.Quasithin.H13.L829N
