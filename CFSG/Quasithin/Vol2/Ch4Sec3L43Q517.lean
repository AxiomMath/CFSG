module

public import CFSG.Quasithin.Vol2.Ch4Sec3L43L34
public import CFSG.Quasithin.Vol2.Ch4Sec4L446Nat
public import CFSG.Quasithin.Background.OperatorJordanHolderJH2

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank
open scoped Pointwise

theorem eig_count {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4) {ω₀ μ : F}
    (hω : ω₀ ≠ 1) (hω3 : ω₀ ^ 3 = 1) {j : ℕ} (hj : j = 1 ∨ j = 2)
    (h : ({μ ^ (j + 1), (μ ^ j)⁻¹, μ ^ j * μ⁻¹} : Multiset F) + {μ} =
      ({ω₀, ω₀⁻¹, ω₀⁻¹, 1} : Multiset F)) : j = 1 ∧ μ = ω₀ := by
  classical
  have hω0 : ω₀ ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hωinv : ω₀⁻¹ = ω₀ ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hω3)
  have hω2 : ω₀ ^ 2 ≠ ω₀ := by
    intro h2
    apply hω
    have : ω₀ * ω₀ = ω₀ * 1 := by rw [← pow_two, h2, mul_one]
    exact mul_left_cancel₀ hω0 this
  have hω21 : ω₀ ^ 2 ≠ 1 := by
    intro h2
    apply hω
    rw [← hω3, pow_succ, h2, one_mul]
  have hω4 : ω₀ ^ 4 = ω₀ := by rw [pow_succ, hω3, one_mul]
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    have := congrArg (Multiset.count 0) h
    have h1 : (0 : F) ≠ ω₀ := Ne.symm hω0
    have h2 : (0 : F) ≠ ω₀⁻¹ := by rw [hωinv]; exact (pow_ne_zero 2 hω0).symm
    simp [h1, h2] at this
  have hmem : μ = 1 ∨ μ = ω₀ ∨ μ = ω₀ ^ 2 := by
    have hcard : ({0, 1, ω₀, ω₀ ^ 2} : Finset F).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair (Ne.symm hω2)]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hω, Ne.symm hω21⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨zero_ne_one, Ne.symm hω0, (pow_ne_zero 2 hω0).symm⟩
    have huniv : ({0, 1, ω₀, ω₀ ^ 2} : Finset F) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hcard, hF])
    have : μ ∈ ({0, 1, ω₀, ω₀ ^ 2} : Finset F) := by
      rw [huniv]
      exact Finset.mem_univ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h0 | h1 | h2 | h3
    · exact absurd h0 hμ0
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)
  rw [hωinv] at h
  rcases hj with rfl | rfl
  · refine ⟨rfl, ?_⟩
    rcases hmem with h1 | h1 | h1
    · exfalso
      rw [h1] at h
      have := congrArg (Multiset.count 1) h
      simp [Ne.symm hω, Ne.symm hω21] at this
    · exact h1
    · exfalso
      rw [h1] at h
      have e1 : (ω₀ ^ 2) ^ (1 + 1) = ω₀ := by rw [← pow_mul, hω4]
      have e2 : ((ω₀ ^ 2) ^ 1)⁻¹ = ω₀ := by rw [pow_one, ← hωinv, inv_inv]
      have e3 : (ω₀ ^ 2) ^ 1 * (ω₀ ^ 2)⁻¹ = 1 := by
        rw [pow_one, mul_inv_cancel₀ (pow_ne_zero 2 hω0)]
      rw [e1, e2, e3] at h
      have := congrArg (Multiset.count ω₀) h
      simp [hω, Ne.symm hω2] at this
  · exfalso
    rcases hmem with h1 | h1 | h1
    · rw [h1] at h
      have := congrArg (Multiset.count 1) h
      simp [Ne.symm hω, Ne.symm hω21] at this
    · rw [h1] at h
      have e1 : ω₀ ^ (2 + 1) = 1 := hω3
      have e2 : (ω₀ ^ 2)⁻¹ = ω₀ := by rw [← hωinv, inv_inv]
      have e3 : ω₀ ^ 2 * ω₀⁻¹ = ω₀ := by
        rw [pow_two, mul_assoc, mul_inv_cancel₀ hω0, mul_one]
      rw [e1, e2, e3] at h
      have := congrArg (Multiset.count ω₀) h
      simp [hω, Ne.symm hω2] at this
    · rw [h1] at h
      have e1 : (ω₀ ^ 2) ^ (2 + 1) = 1 := by
        rw [← pow_mul, show 2 * (2 + 1) = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
      have e2 : ((ω₀ ^ 2) ^ 2)⁻¹ = ω₀ ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 4 by norm_num, hω4, hωinv]
      have e3 : (ω₀ ^ 2) ^ 2 * (ω₀ ^ 2)⁻¹ = ω₀ ^ 2 := by
        rw [pow_two (ω₀ ^ 2), mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hω0), mul_one]
      rw [e1, e2, e3] at h
      have := congrArg (Multiset.count (ω₀ ^ 2)) h
      simp [hω2, hω21] at this

variable {G : Type} [Group G]

theorem le_normalizer_bot' (H : Subgroup G) :
    H ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun x _ =>
  Subgroup.mem_normalizer_iff.mpr fun y => by
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl
      group
    · intro hy
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = 1 := by rw [hy]; group

theorem gap432L34Twisted_holds (hJH : OperatorJHNatEig) (hB414 : LemmaB414Corrected) :
    Gap432L34Twisted := by
  intro G _ _ T M L n I H K t F _ _ ZS K₂ R₂ X KZ Γ A B α P c k hk hTw
  have hK₂Γ : K₂ ≤ Γ := by
    rw [c.Γ_eq]
    exact c.K₂_le.trans le_sup_left
  have hXΓ : X ≤ Γ := by
    rw [c.Γ_eq]
    exact le_sup_right
  have hKZΓ : KZ ≤ Γ := by
    rw [c.Γ_eq]
    exact le_sup_left
  have hAΓ : A ≤ Γ := (c.A_le.trans (pCoreOf_le 2 KZ)).trans hKZΓ
  obtain ⟨-, hdata⟩ := hB414 G Γ A B K₂ X F c.card_F c.Γ_A c.Γ_B c.B_lt c.sq c.comm
    c.irred hK₂Γ hXΓ α c.α_surj c.α_ker P c.P_max c.P_K₂ c.P_X c.αX_card c.αX_cent c.star
  obtain ⟨-, hTwF, j, hj3, hj0, hj1, hlab⟩ := hdata k (by omega) hTw
  have hk0 : k ≠ 0 := by omega
  have hjne : j ≠ 0 := fun h => hk0 (hj0.mp h)
  obtain ⟨γx, hγxX, hγx1⟩ : ∃ γx : ↥Γ, (γx : G) ∈ X ∧ α γx ≠ 1 := by
    by_contra hall
    push Not at hall
    have h0 : (X.subgroupOf Γ).map α = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨γ, hγ, rfl⟩
      exact Subgroup.mem_bot.mpr (hall γ hγ)
    have h3 := c.αX_card
    rw [h0, Subgroup.card_bot] at h3
    omega
  obtain ⟨α₀', α₀, hα₀'s, hα₀'k, hα₀c, hcfg⟩ := c.labels
  obtain ⟨U, ω₀, μ', hω₀, hω₀3, hμ', ⟨lR, hlR, hlRm⟩, ⟨lB, hlB, hlB0⟩, ⟨lA, hlA, hlA0⟩,
    ⟨lO, hlO, hlOm⟩, hUfac, hUO2, hUcomm, hUab, hYU, hO2U⟩ := hcfg γx hγxX hγx1
  obtain ⟨μ, hμ, lW, hlW, hlWm⟩ := hlab α₀' hα₀'s hα₀'k α₀ hα₀c γx hγxX hγx1
  have hα₀s : Function.Surjective α₀ := by
    intro g
    obtain ⟨p, rfl⟩ := hα₀'s g
    have hp : (p : GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) ∈ (K₂.subgroupOf Γ).map α := by
      rw [c.P_K₂]
      exact p.2
    obtain ⟨γ, hγ, hγp⟩ := hp
    exact ⟨⟨γ, hγ⟩, hα₀c ⟨γ, hγ⟩ γ p rfl hγp.symm⟩
  have hPO2 : perfectCore P ≤
      Subgroup.normalizer ((pCoreOf 2 (perfectCore P) : Subgroup _) : Set _) :=
    le_normalizer_pCoreOf 2 _
  have hxN : α γx ∈ Subgroup.normalizer ((pCoreOf 2 (perfectCore P) : Subgroup _) : Set _) := by
    have hxP : α γx ∈ P := c.P_X ⟨γx, hγxX, rfl⟩
    exact normalizer_le_normalizer_pCoreOf 2 _
      (normalizer_le_normalizer_perfectCore P (Subgroup.le_normalizer hxP))
  have hμμ' : μ = μ' := hμ.eig_unique hμ' le_rfl hα₀'s hPO2 hxN
  set Y := K₂ ⊔ X with hY
  have hJ := hJH G Y K₂ (γx : G) 2 F α₀ le_sup_left (Subgroup.mem_sup_right hγxX) le_rfl hα₀s
  have hcat := ((hlB.append hlW).append hlA).append hlO
  have hm := (hJ ⊥ R₂ lR hlR).1 _ hcat
  rw [labMultiset_append, labMultiset_append, labMultiset_append,
    labMultiset_eq_zero_of_forall hlB0, labMultiset_eq_zero_of_forall hlA0, hlWm, hlOm, hlRm,
    ← hμμ', zero_add, add_zero] at hm
  obtain ⟨rfl, hμω⟩ := eig_count c.card_F hω₀ hω₀3 (by omega) hm
  subst hμω
  have hZSU : ZS ≤ U := hUfac.1.le
  have hYZS : Y ≤ Subgroup.normalizer (ZS : Set G) := hUfac.2.2.1
  have hUZS : U ≤ Subgroup.normalizer (ZS : Set G) := fun u hu =>
    A4.mem_normalizer_of_conj_mem fun z hz => by
      rw [hUab u hu z (hZSU hz), mul_inv_cancel_right]
      exact hz
  have hUnotO : ¬ U ≤ pCoreOf 2 KZ := by
    intro hUO
    obtain ⟨l₁, l₂, hl₁, -, hsum⟩ := (hJ ⊥ (pCoreOf 2 KZ) _ ((hlB.append hlW).append hlA)).2
      U bot_le hUO (le_normalizer_bot' U) hO2U hYU
    obtain ⟨l₃, l₄, -, hl₄, hsum2⟩ := (hJ ⊥ U l₁ hl₁).2 ZS bot_le hZSU (le_normalizer_bot' ZS)
      hUZS hYZS
    have h4 := (hJ ZS U _ (isLabSeries_singleton hUfac)).1 l₄ hl₄
    have hmem : μ ∈ labMultiset l₁ := by
      rw [← hsum2, h4]
      simp [labMultiset]
    have hmem2 : μ ∈ labMultiset ((lB ++ lW) ++ lA) := by
      rw [← hsum]
      exact Multiset.mem_add.mpr (Or.inl hmem)
    rw [labMultiset_append, labMultiset_append, labMultiset_eq_zero_of_forall hlB0,
      labMultiset_eq_zero_of_forall hlA0, hlWm] at hmem2
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      norm_num at hω₀3
    simp only [zero_add, add_zero, Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton, pow_one] at hmem2
    rcases hmem2 with h1 | h1 | h1
    · apply hω₀
      have : μ * μ = μ * 1 := by rw [mul_one, ← pow_two]; exact h1.symm
      exact mul_left_cancel₀ hμ0 this
    · apply hω₀
      have h2 : μ * μ = 1 := by
        calc μ * μ = μ * μ⁻¹ := by rw [← h1]
          _ = 1 := mul_inv_cancel₀ hμ0
      calc μ = μ * (μ * μ) := by rw [h2, mul_one]
        _ = μ ^ 3 := by ring
        _ = 1 := hω₀3
    · apply hω₀
      rw [mul_inv_cancel₀ hμ0] at h1
      exact h1
  have hUK₂ : U ≤ K₂ := hUO2.trans (pCoreOf_le 2 K₂)
  have hUΓ : U ≤ Γ := hUK₂.trans hK₂Γ
  set J := (U.subgroupOf Γ).map α with hJdef
  have hJP : J ≤ perfectCore P := by
    rw [← c.P_K₂]
    exact Subgroup.map_mono (fun γ hγ => hUK₂ hγ)
  have hPJ : perfectCore P ≤ Subgroup.normalizer (J : Set _) := fun p hp =>
    A4.mem_normalizer_of_conj_mem fun y hy => by
      have hp' : p ∈ (K₂.subgroupOf Γ).map α := by
        rw [c.P_K₂]
        exact hp
      obtain ⟨γ, hγ, rfl⟩ := hp'
      obtain ⟨u, hu, rfl⟩ := hy
      have hγu : (γ : G) * u * (γ : G)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hYU (Subgroup.mem_sup_left hγ)) _).mp hu
      refine ⟨γ * u * γ⁻¹, hγu, ?_⟩
      rw [map_mul, map_mul, map_inv]
  have hU2 : IsPGroup 2 U := (pCoreOf_isPGroup 2 K₂).to_le hUO2
  have hJ2 : IsPGroup 2 ↥J := (hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUΓ).symm).map α
  have hJO : J ≤ pCoreOf 2 (perfectCore P) := le_pCoreOf_of_le_normalizer 2 hJP hPJ hJ2
  rcases hμ'.eq_or_eq le_rfl hα₀'s hPO2 bot_le hJO hPJ with hJ0 | hJ1
  · apply hUnotO
    intro u hu
    have h1 : α ⟨u, hUΓ hu⟩ ∈ J := ⟨⟨u, hUΓ hu⟩, hu, rfl⟩
    rw [hJ0, Subgroup.mem_bot] at h1
    exact c.α_ker_le ⟨u, hUΓ hu⟩ h1
  have hγU : ∀ γ : ↥Γ, α γ ∈ pCoreOf 2 (perfectCore P) →
      ∃ u ∈ U, ∃ hu : u ∈ Γ, α ⟨u, hu⟩ = α γ := by
    intro γ hγ
    rw [← hJ1] at hγ
    obtain ⟨u, hu, hue⟩ := hγ
    exact ⟨u, hu, u.2, hue⟩
  have hΓZS : Γ ≤ Subgroup.normalizer (ZS : Set G) := by
    rw [c.Γ_eq]
    exact _root_.sup_le (fun g hg => Subgroup.centralizer_le_normalizer _ (c.KZ_cent hg)) c.X_ZS
  have hZSAB : ZS ⊓ A ≤ B := by
    have hZAN : ZS ⊓ A ≤ Subgroup.normalizer (B : Set G) := fun z hz => c.Γ_B (hAΓ hz.2)
    have hΓJ' : Γ ≤ Subgroup.normalizer ((ZS ⊓ A ⊔ B : Subgroup G) : Set G) :=
      le_normalizer_sup_of_le (fun g hg => A4.mem_normalizer_inf (hΓZS hg) (c.Γ_A hg)) c.Γ_B
    rcases c.irred (ZS ⊓ A ⊔ B) le_sup_right (_root_.sup_le inf_le_right c.B_lt.le) hΓJ' with
      h1 | h2
    · rw [← h1]
      exact le_sup_left
    · exfalso
      apply hUnotO
      intro u hu
      refine c.α_ker_le ⟨u, hUΓ hu⟩ ((c.α_ker _).mpr fun a ha => ?_)
      have ha' : a ∈ ((ZS ⊓ A : Subgroup G) : Set G) * (B : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZAN, h2]
        exact ha
      obtain ⟨z, hz, b, hb, rfl⟩ := ha'
      have huz : z * u = u * z :=
        Subgroup.mem_centralizer_iff.mp (c.KZ_cent (c.K₂_le (hUK₂ hu))) z hz.1
      have e : u * (z * b) * u⁻¹ * (z * b)⁻¹ = z * (u * b * u⁻¹ * b⁻¹) * z⁻¹ := by
        calc u * (z * b) * u⁻¹ * (z * b)⁻¹ = (u * z) * b * u⁻¹ * b⁻¹ * z⁻¹ := by group
          _ = (z * u) * b * u⁻¹ * b⁻¹ * z⁻¹ := by rw [huz]
          _ = z * (u * b * u⁻¹ * b⁻¹) * z⁻¹ := by group
      show u * (z * b) * u⁻¹ * (z * b)⁻¹ ∈ B
      rw [e]
      refine (Subgroup.mem_normalizer_iff.mp (c.Γ_B (hAΓ hz.2)) _).mp ?_
      exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (c.Γ_B (hUΓ hu)) b).mp hb) (B.inv_mem hb)
  set N' := α.ker.map Γ.subtype with hN'
  have hN'mem : ∀ g ∈ N', ∃ γ : ↥Γ, α γ = 1 ∧ (γ : G) = g := by
    intro g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨γ, hγ, rfl⟩
  have hN'act : ∀ g ∈ N', ∀ a ∈ A, g * a * g⁻¹ * a⁻¹ ∈ B := by
    intro g hg a ha
    obtain ⟨γ, hγ, rfl⟩ := hN'mem g hg
    exact (c.α_ker γ).mp hγ a ha
  have hN'2 : IsPGroup 2 N' := by
    refine (pCoreOf_isPGroup 2 KZ).to_le fun g hg => ?_
    obtain ⟨γ, hγ, rfl⟩ := hN'mem g hg
    exact c.α_ker_le γ hγ
  have hN'conj : ∀ γ ∈ Γ, ∀ g ∈ N', γ * g * γ⁻¹ ∈ N' := by
    intro γ hγ g hg
    obtain ⟨δ, hδ, rfl⟩ := hN'mem g hg
    refine Subgroup.mem_map.mpr ⟨⟨γ, hγ⟩ * δ * ⟨γ, hγ⟩⁻¹, ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_mul, map_mul, hδ, mul_one, map_inv, mul_inv_cancel]
  have hN'norm : Γ ≤ Subgroup.normalizer (N' : Set G) := by
    intro γ hγ
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hN'conj γ hγ g hg, fun hg => ?_⟩
    have := hN'conj γ⁻¹ (Γ.inv_mem hγ) _ hg
    simpa [mul_assoc] using this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX3 : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by rw [c.X_card, pow_one])
  have hB2 : IsPGroup 2 B :=
    (pCoreOf_isPGroup 2 KZ).to_le (c.B_lt.le.trans c.A_le)
  have hB3 : ¬ 3 ∣ Nat.card B := not_three_dvd_card_of_isPGroup hB2
  have hKN3 : ¬ 3 ∣ Nat.card ↥(K₂ ⊓ N') := not_three_dvd_card_of_isPGroup (hN'2.to_le inf_le_right)
  have hXB : X ≤ Subgroup.normalizer (B : Set G) := hXΓ.trans c.Γ_B
  have hXKN : X ≤ Subgroup.normalizer ((K₂ ⊓ N' : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf (c.X_K₂ hx) (hN'norm (hXΓ hx))
  have hdecL : ∀ l ∈ K₂, IsCentMod X N' l →
      ∃ m ∈ K₂ ⊓ N', l * m ∈ K₂ ⊓ Subgroup.centralizer (X : Set G) := by
    intro l hl hlX
    have ha : ∀ x ∈ X, l⁻¹ * (x * l * x⁻¹) ∈ K₂ ⊓ N' := by
      intro x hx
      refine ⟨K₂.mul_mem (K₂.inv_mem hl)
        ((Subgroup.mem_normalizer_iff.mp (c.X_K₂ hx) l).mp hl), ?_⟩
      have h1 : x * l * x⁻¹ * l⁻¹ ∈ N' := by
        have := N'.inv_mem (hlX x hx)
        simpa [mul_assoc] using this
      have h2 := hN'conj l⁻¹ (Γ.inv_mem (hK₂Γ hl)) _ h1
      have e : l⁻¹ * (x * l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (x * l * x⁻¹) := by group
      rwa [e] at h2
    obtain ⟨m, hm, hfix⟩ := exists_mul_fixed_of_isPGroup hX3 hKN3 hXKN ha
    refine ⟨m, hm, K₂.mul_mem hl hm.1, ?_⟩
    show l * m ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hfix x hx
    calc x * (l * m) = x * (l * m) * x⁻¹ * x := by group
      _ = l * m * x := by rw [this]
  have hdecV : ∀ v ∈ A, IsFixedMod X B v →
      ∃ b ∈ B, v * b ∈ A ⊓ Subgroup.centralizer (X : Set G) := by
    intro v hv hvX
    have ha : ∀ x ∈ X, v⁻¹ * (x * v * x⁻¹) ∈ B := by
      intro x hx
      have h2 := (Subgroup.mem_normalizer_iff.mp (c.Γ_B (Γ.inv_mem (hAΓ hv))) _).mp (hvX x hx)
      have e : v⁻¹ * (x * v * x⁻¹ * v⁻¹) * v⁻¹⁻¹ = v⁻¹ * (x * v * x⁻¹) := by group
      rwa [e] at h2
    obtain ⟨b, hb, hfix⟩ := exists_mul_fixed_of_isPGroup hX3 hB3 hXB ha
    refine ⟨b, hb, A.mul_mem hv (c.B_lt.le hb), ?_⟩
    show v * b ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hfix x hx
    calc x * (v * b) = x * (v * b) * x⁻¹ * x := by group
      _ = v * b * x := by rw [this]
  have hcommN : ∀ l ∈ Γ, ∀ m ∈ N', ∀ w ∈ A,
      (l * m) * w * (l * m)⁻¹ * w⁻¹ ∈ B ↔ l * w * l⁻¹ * w⁻¹ ∈ B := by
    intro l hl m hm w hw
    have e : (l * m) * w * (l * m)⁻¹ * w⁻¹ =
        (l * (m * w * m⁻¹ * w⁻¹) * l⁻¹) * (l * w * l⁻¹ * w⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem_cancel_left _
      ((Subgroup.mem_normalizer_iff.mp (c.Γ_B hl) _).mp (hN'act m hm w hw))
  have hcommB : ∀ l ∈ Γ, ∀ w ∈ A, ∀ b ∈ B,
      l * (w * b) * l⁻¹ * (w * b)⁻¹ ∈ B ↔ l * w * l⁻¹ * w⁻¹ ∈ B := by
    intro l hl w hw b hb
    have e : l * (w * b) * l⁻¹ * (w * b)⁻¹ =
        (l * w * l⁻¹ * w⁻¹) * (w * (l * b * l⁻¹ * b⁻¹) * w⁻¹) := by group
    rw [e]
    refine Subgroup.mul_mem_cancel_right _ ?_
    refine (Subgroup.mem_normalizer_iff.mp (c.Γ_B (hAΓ hw)) _).mp ?_
    exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (c.Γ_B hl) b).mp hb) (B.inv_mem hb)
  set A' := A ⊓ Subgroup.centralizer (X : Set G) with hA'
  set D := pCoreOf 2 K₂ ⊓ Subgroup.centralizer (X : Set G) with hD
  set CK := K₂ ⊓ Subgroup.centralizer (X : Set G) with hCK
  have hCKD : CK ≤ Subgroup.normalizer (D : Set G) := fun k hk =>
    mem_normalizer_inf (le_normalizer_pCoreOf 2 K₂ hk.1) (Subgroup.le_normalizer hk.2)
  have hCKA' : CK ≤ Subgroup.normalizer (A' : Set G) := fun k hk =>
    mem_normalizer_inf (c.Γ_A (hK₂Γ hk.1)) (Subgroup.le_normalizer hk.2)
  have hCKcent : ∀ k ∈ CK, IsCentMod X N' k := by
    intro k hk x hx
    have : k * x = x * k := (Subgroup.mem_centralizer_iff.mp hk.2 x hx).symm
    rw [this, mul_inv_cancel_right, mul_inv_cancel]
    exact N'.one_mem
  set J₀ := A' ⊓ D ⊔ B with hJ₀
  have hADB : A' ⊓ D ≤ Subgroup.normalizer (B : Set G) := fun d hd =>
    c.Γ_B (hAΓ hd.1.1)
  have hJ₀set : (J₀ : Set G) = ((A' ⊓ D : Subgroup G) : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right (A' ⊓ D) B hADB
  have hJ₀mem : ∀ j ∈ J₀, ∃ d ∈ A' ⊓ D, ∃ b ∈ B, j = d * b := by
    intro j hj
    have hj' : j ∈ ((A' ⊓ D : Subgroup G) : Set G) * (B : Set G) := by
      rw [← hJ₀set]
      exact hj
    obtain ⟨d, hd, b, hb, rfl⟩ := hj'
    exact ⟨d, hd, b, hb, rfl⟩
  have hsub : ∀ j ∈ J₀, j ∈ A ∧ IsFixedMod X B j := by
    intro j hj
    obtain ⟨d, hd, b, hb, rfl⟩ := hJ₀mem j hj
    refine ⟨A.mul_mem hd.1.1 (c.B_lt.le hb), fun x hx => ?_⟩
    have hdx : x * d * x⁻¹ = d := by
      have := Subgroup.mem_centralizer_iff.mp hd.1.2 x hx
      rw [this, mul_inv_cancel_right]
    have e : x * (d * b) * x⁻¹ * (d * b)⁻¹ = d * (x * b * x⁻¹ * b⁻¹) * d⁻¹ := by
      calc x * (d * b) * x⁻¹ * (d * b)⁻¹ = (x * d * x⁻¹) * (x * b * x⁻¹ * b⁻¹) * d⁻¹ := by
            group
        _ = d * (x * b * x⁻¹ * b⁻¹) * d⁻¹ := by rw [hdx]
    rw [e]
    refine (Subgroup.mem_normalizer_iff.mp (hADB hd) _).mp ?_
    exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXB hx) b).mp hb) (B.inv_mem hb)
  have hinv : ∀ l ∈ K₂, IsCentMod X N' l → ∀ j ∈ J₀, l * j * l⁻¹ ∈ J₀ := by
    intro l hl hlX j hj
    obtain ⟨m, hm, hlm⟩ := hdecL l hl hlX
    have hjA := (hsub j hj).1
    have h1 : m⁻¹ * j * m⁻¹⁻¹ * j⁻¹ ∈ B := hN'act m⁻¹ (N'.inv_mem hm.2) j hjA
    have h2 : m⁻¹ * j * m ∈ J₀ := by
      have e : m⁻¹ * j * m = (m⁻¹ * j * m⁻¹⁻¹ * j⁻¹) * j := by group
      rw [e]
      exact J₀.mul_mem ((le_sup_right : B ≤ A' ⊓ D ⊔ B) h1) hj
    obtain ⟨d, hd, b, hb, he⟩ := hJ₀mem _ h2
    have e : l * j * l⁻¹ = (l * m) * (m⁻¹ * j * m) * (l * m)⁻¹ := by group
    rw [e, he]
    have e2 : (l * m) * (d * b) * (l * m)⁻¹ =
        ((l * m) * d * (l * m)⁻¹) * ((l * m) * b * (l * m)⁻¹) := by group
    rw [e2]
    refine J₀.mul_mem ((le_sup_left : A' ⊓ D ≤ A' ⊓ D ⊔ B) ⟨?_, ?_⟩)
      ((le_sup_right : B ≤ A' ⊓ D ⊔ B) ?_)
    · exact (Subgroup.mem_normalizer_iff.mp (hCKA' hlm) d).mp hd.1
    · exact (Subgroup.mem_normalizer_iff.mp (hCKD hlm) d).mp hd.2
    · exact (Subgroup.mem_normalizer_iff.mp (c.Γ_B (hK₂Γ hlm.1)) b).mp hb
  obtain ⟨⟨v₀, hv₀A, hv₀X, hv₀B⟩, hTirr, hTfix⟩ := hTwF hk0
  have hJ₀ne : ¬ J₀ = B := by
    intro hJB
    apply hv₀B
    refine hTfix v₀ hv₀A hv₀X fun l hl hlX => ?_
    obtain ⟨m, hm, hlm⟩ := hdecL l hl hlX
    obtain ⟨b, hb, hvb⟩ := hdecV v₀ hv₀A hv₀X
    have h1 : (l * m) * (v₀ * b) * (l * m)⁻¹ * (v₀ * b)⁻¹ ∈ B := by
      have hmem : (l * m) * (v₀ * b) * (l * m)⁻¹ * (v₀ * b)⁻¹ ∈ A' ⊓ D := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp (c.Γ_A (hK₂Γ hlm.1)) _).mp hvb.1)
            (A.inv_mem hvb.1)
        · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hlm.2 hvb.2)
            (Subgroup.inv_mem _ hlm.2)) (Subgroup.inv_mem _ hvb.2)
        · exact c.D_comm _ ⟨c.O2KZ_le (c.A_le hvb.1), hvb.2⟩ _ hlm
      rw [← hJB]
      exact (le_sup_left : A' ⊓ D ≤ J₀) hmem
    exact (hcommN l (hK₂Γ hl) m hm.2 v₀ hv₀A).mp ((hcommB _ (hK₂Γ hlm.1) v₀ hv₀A b hb).mp h1)
  have hJ₀all : ∀ v ∈ A, IsFixedMod X B v → v ∈ J₀ := by
    rcases hTirr J₀ le_sup_right hsub hinv with h | h
    · exact absurd h hJ₀ne
    · exact h
  have hcent : ∀ v ∈ A, IsFixedMod X B v → ∀ γ : ↥Γ, α γ ∈ pCoreOf 2 (perfectCore P) →
      (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∈ B := by
    intro v hv hvX γ hγ
    obtain ⟨u, hu, huΓ, hue⟩ := hγU γ hγ
    set ν : ↥Γ := (⟨u, huΓ⟩ : ↥Γ)⁻¹ * γ with hν
    have hν1 : α ν = 1 := by rw [hν, map_mul, map_inv, hue, inv_mul_cancel]
    have hνN' : (ν : G) ∈ N' := ⟨ν, hν1, rfl⟩
    have hγe : (γ : G) = u * ν := by
      rw [hν]
      simp
    obtain ⟨d, hd, b, hb, rfl⟩ := hJ₀mem v (hJ₀all v hv hvX)
    rw [hγe]
    refine (hcommN u huΓ ν hνN' (d * b) hv).mpr ?_
    refine (hcommB u huΓ d hd.1.1 b hb).mpr ?_
    refine hZSAB ⟨hUcomm (Subgroup.commutator_mem_commutator hu hd.2.1), ?_⟩
    exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp (c.Γ_A huΓ) d).mp hd.1.1) (A.inv_mem hd.1.1)
  exact hv₀B (hj1 rfl v₀ hv₀A hv₀X (hcent v₀ hv₀A hv₀X))

theorem lemma43End_of_jh (hUpto : Lemma43Upto) (hB414 : LemmaB414Corrected)
    (hJH : OperatorJHNatEig) : Lemma43End :=
  lemma43End_of hUpto hB414 (gap432L34Twisted_holds hJH hB414)

theorem lemma43End_of_b414 (hUpto : Lemma43Upto) (hB414 : LemmaB414Corrected) : Lemma43End :=
  lemma43End_of_jh hUpto hB414 OperatorJH.operatorJHNatEig_holds

end CFSG.Quasithin.H13.Ch4
