module

public import CFSG.Quasithin.H13.A5S1327e
public import CFSG.Quasithin.Background.F6Cat
public import CFSG.Quasithin.H13.A5S1324b

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def kk3 : Fin 3 → Equiv.Perm (Fin 5) := ![pa, pb, pc]

@[expose] def idx3 (τ : Equiv.Perm (Fin 5)) : Fin 3 := if τ = pb then 1 else if τ = pc then 2 else 0

@[expose] def kappaFun (σ : Equiv.Perm (Fin 5)) (i : Fin 3) : Fin 3 := idx3 (σ * kk3 i * σ⁻¹)

theorem kappaFun_inv : ∀ σ : Equiv.Perm (Fin 5), σ 4 = 4 → ∀ i : Fin 3,
    kappaFun σ⁻¹ (kappaFun σ i) = i ∧ kappaFun σ (kappaFun σ⁻¹ i) = i := by
  decide +kernel

@[expose] def kappa (σ : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 3) :=
  if h : σ 4 = 4 then
    { toFun := kappaFun σ, invFun := kappaFun σ⁻¹
      left_inv := fun i => (kappaFun_inv σ h i).1
      right_inv := fun i => (kappaFun_inv σ h i).2 }
  else 1

theorem kappa_mul : ∀ σ τ : Equiv.Perm (Fin 5), σ 4 = 4 → τ 4 = 4 →
    kappa (σ * τ) = kappa σ * kappa τ := by
  decide +kernel

theorem kappa_eq_one_iff : ∀ σ : Equiv.Perm (Fin 5), σ 4 = 4 → (kappa σ = 1 ↔ InK4 σ) := by
  decide +kernel

theorem kappa_gen : ∀ π : Equiv.Perm (Fin 3), π = 1 ∨ π = kappa c3p ∨ π = kappa c3p ^ 2 ∨
    π = kappa (Equiv.swap 0 1) ∨ π = kappa (Equiv.swap 0 1) * kappa c3p ∨
    π = kappa (Equiv.swap 0 1) * kappa c3p ^ 2 := by
  decide +kernel

theorem perm3_sq_conj_eq_one : ∀ σ : Equiv.Perm (Fin 3), σ ^ 2 = 1 →
    (σ * ((Equiv.swap 0 1 * Equiv.swap 1 2) * σ * (Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹)) ^ 2 = 1 →
    σ = 1 := by
  decide +kernel

theorem eq_bot_of_normal_isPGroup_perm3 {K : Subgroup (Equiv.Perm (Fin 3))} (hKn : K.Normal)
    (hK2 : IsPGroup 2 K) : K = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  have h2 : ∀ τ ∈ K, τ ^ 2 = 1 := by
    intro τ hτ
    obtain ⟨k, hk⟩ := hK2 ⟨τ, hτ⟩
    exact perm3_sq_of_two_pow (k := k) (by simpa using congrArg Subtype.val hk)
  have hc : (Equiv.swap 0 1 * Equiv.swap 1 2) * σ * (Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹ ∈ K :=
    hKn.conj_mem σ hσ _
  exact Subgroup.mem_bot.mpr (perm3_sq_conj_eq_one σ (h2 σ hσ) (h2 _ (K.mul_mem hσ hc)))

theorem oTwoUpper_perm3 : ∀ σ ∈ oTwoUpper (⊤ : Subgroup (Equiv.Perm (Fin 3))), σ ^ 3 = 1 := by
  have hA3' : ∀ τ : Equiv.Perm (Fin 3), τ ^ 3 = 1 → Equiv.Perm.sign τ = 1 := by decide
  have hA3 : ∀ τ : Equiv.Perm (Fin 3), τ ^ 3 = 1 → τ ∈ alternatingGroup (Fin 3) :=
    fun τ hτ => Equiv.Perm.mem_alternatingGroup.mpr (hA3' τ hτ)
  have hA : oTwoUpper (⊤ : Subgroup (Equiv.Perm (Fin 3))) ≤ alternatingGroup (Fin 3) := by
    refine (Subgroup.closure_le _).mpr fun σ hσ => hA3 σ ?_
    refine eq_one_of_pow_coprime (m := 2) (n := orderOf σ) (perm3_cube_sq σ) ?_
      (Nat.coprime_two_left.mpr hσ.2)
    rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  intro σ hσ
  have h3 : ∀ τ : Equiv.Perm (Fin 3), Equiv.Perm.sign τ = 1 → τ ^ 3 = 1 := by decide
  exact h3 σ (Equiv.Perm.mem_alternatingGroup.mp (hA hσ))

theorem perm3_words : ∀ x π : Equiv.Perm (Fin 3), x ≠ 1 → x ≠ kappa (Equiv.swap 0 1) →
    π = 1 ∨ π = x ∨ π = x ^ 2 ∨ π = kappa (Equiv.swap 0 1) ∨
      π = kappa (Equiv.swap 0 1) * x ∨ π = kappa (Equiv.swap 0 1) * x ^ 2 ∨
      π = x * kappa (Equiv.swap 0 1) ∨ π = x * kappa (Equiv.swap 0 1) * x := by
  decide +kernel

theorem threeTop_of_pow_mem {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hpow : ∀ k ∈ oTwoUpper X, ∃ a : ℕ, k ^ 3 ^ a ∈ pCoreOf 2 X) : ThreeTop X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N3 := CFSG.pPrimeCore 3 ↥X with hN3
  set π := QuotientGroup.mk' N3 with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N3
  have hO2N3 : CFSG.Open.pCore 2 ↥X ≤ N3 := by
    refine le_sSup ⟨CFSG.LieType.BorelTits.pCore_normal 2, ?_⟩
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥X) 2).exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  intro q
  have hq : (q : ↥X ⧸ N3) ∈ (oTwoUpper (⊤ : Subgroup ↥X)).map π := by
    rw [← oTwoUpper_map, Subgroup.map_top_of_surjective π hπs]
    exact q.2
  obtain ⟨k, hk, hkq⟩ := hq
  have hkX : (k : G) ∈ oTwoUpper X := by
    have h1 : (k : G) ∈ (oTwoUpper (⊤ : Subgroup ↥X)).map X.subtype := ⟨k, hk, rfl⟩
    rwa [← oTwoUpper_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  obtain ⟨a, ha⟩ := hpow k hkX
  refine ⟨a, Subtype.ext ?_⟩
  obtain ⟨k', hk', hk'e⟩ := ha
  have e : k' = k ^ 3 ^ a := Subtype.ext (by rw [Subgroup.coe_pow]; exact hk'e)
  have h2 : π (k ^ 3 ^ a) = 1 := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← e]
    exact hO2N3 hk'
  simp only [Subgroup.coe_pow, Subgroup.coe_one, ← hkq, ← map_pow, h2]

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem thompsonJ_not_le_centralizer (h5172 : Stmt5_1_7_two)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) := by
  intro hJ
  have hZH' : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
    intro h
    apply hHZ
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h)
  obtain ⟨hLJ, -, -⟩ := h5172 G T _ L V H 2 S.hyp501 S.isCh5Module hH hZH'
  have hLC : L ≤ Subgroup.centralizer (V : Set G) := by
    rw [hLJ]
    refine Subgroup.commutator_le.mpr fun l hl j hj => ?_
    have hlN := S.frame.L_le hl
    have hjN := S.frame.T_le (thompsonJ_le_self T hj)
    have hcN : ⁅l, j⁆ ∈ Subgroup.normalizer (V : Set G) := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hjN)
        (Subgroup.inv_mem _ hlN)) (Subgroup.inv_mem _ hjN)
    refine S.frame.mem_centralizer_of_rho ⟨_, hcN⟩ ?_
    have e : (⟨⁅l, j⁆, hcN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨l, hlN⟩ * ⟨j, hjN⟩ * (⟨l, hlN⟩)⁻¹ * (⟨j, hjN⟩)⁻¹ := by
      apply Subtype.ext
      simp [commutatorElement_def]
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv,
      S.frame.rho_eq_one_of_mem ⟨j, hjN⟩ (hJ hj)]
    group
  obtain ⟨g, hgL, hg⟩ := (S.frame.image_L c3p).2 c3p_sign
  have h1 := S.frame.rho_eq_one_of_mem g (hLC hgL)
  rw [hg] at h1
  exact absurd h1 (by decide)

theorem L1T_le_NV : S.L1 ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
  sup_le (S.L1_le_L.trans S.frame.L_le) S.frame.T_le

theorem rho_four_of_mem_L1T {g : G} (hg : g ∈ S.L1 ⊔ T) :
    S.frame.ρ ⟨g, S.L1T_le_NV hg⟩ 4 = 4 :=
  S.rho_four_of_conj_z _ (S.conj_z_of_normalizes (S.L1T_le_NV1 hg))

@[expose] noncomputable def phiL1T : ↥(S.L1 ⊔ T) →* Equiv.Perm (Fin 3) where
  toFun g := kappa (S.frame.ρ ⟨g, S.L1T_le_NV g.2⟩)
  map_one' := by
    have e : (⟨((1 : ↥(S.L1 ⊔ T)) : G), S.L1T_le_NV (1 : ↥(S.L1 ⊔ T)).2⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = 1 := rfl
    rw [e, map_one]
    exact (kappa_eq_one_iff 1 rfl).2 (Or.inl rfl)
  map_mul' a b := by
    have e : (⟨((a * b : ↥(S.L1 ⊔ T)) : G), S.L1T_le_NV (a * b).2⟩ :
        ↥(Subgroup.normalizer (V : Set G))) =
        ⟨a, S.L1T_le_NV a.2⟩ * ⟨b, S.L1T_le_NV b.2⟩ := rfl
    rw [e, map_mul]
    exact kappa_mul _ _ (S.rho_four_of_mem_L1T a.2) (S.rho_four_of_mem_L1T b.2)

theorem phiL1T_apply (g : ↥(S.L1 ⊔ T)) :
    S.phiL1T g = kappa (S.frame.ρ ⟨g, S.L1T_le_NV g.2⟩) := rfl

theorem mem_T_of_phiL1T_eq_one (g : ↥(S.L1 ⊔ T)) (hg : S.phiL1T g = 1) : (g : G) ∈ T := by
  rw [phiL1T_apply, kappa_eq_one_iff _ (S.rho_four_of_mem_L1T g.2)] at hg
  exact S.mem_T_of_InK4 _ (sup_le (S.L1_le_L.trans le_sup_left) le_sup_right g.2) hg

theorem phiL1T_surjective {t : G} (ht : t ∈ T) (htN : t ∈ Subgroup.normalizer (V : Set G))
    (hts : S.frame.ρ ⟨t, htN⟩ = Equiv.swap 0 1) : Function.Surjective S.phiL1T := by
  obtain ⟨l, hlL1, hl⟩ := S.exists_L1_c3p
  set l' : ↥(S.L1 ⊔ T) := ⟨l, Subgroup.mem_sup_left hlL1⟩ with hl'
  set t' : ↥(S.L1 ⊔ T) := ⟨t, Subgroup.mem_sup_right ht⟩ with ht'
  have hφl : S.phiL1T l' = kappa c3p := by
    rw [phiL1T_apply, ← hl]
  have hφt : S.phiL1T t' = kappa (Equiv.swap 0 1) := by
    rw [phiL1T_apply, ← hts]
  intro π
  rcases kappa_gen π with h | h | h | h | h | h
  · exact ⟨1, by rw [h, map_one]⟩
  · exact ⟨l', by rw [h, hφl]⟩
  · exact ⟨l' ^ 2, by rw [h, map_pow, hφl]⟩
  · exact ⟨t', by rw [h, hφt]⟩
  · exact ⟨t' * l', by rw [h, map_mul, hφt, hφl]⟩
  · exact ⟨t' * l' ^ 2, by rw [h, map_mul, map_pow, hφt, hφl]⟩

theorem quotient_L1T_equiv_S3 {t : G} (ht : t ∈ T)
    (htN : t ∈ Subgroup.normalizer (V : Set G)) (hts : S.frame.ρ ⟨t, htN⟩ = Equiv.swap 0 1) :
    Nonempty (↥(S.L1 ⊔ T) ⧸ CFSG.Open.pCore 2 ↥(S.L1 ⊔ T) ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := S.phiL1T_surjective ht htN hts
  have hker : CFSG.Open.pCore 2 ↥(S.L1 ⊔ T) = S.phiL1T.ker := by
    apply le_antisymm
    · have hn : ((CFSG.Open.pCore 2 ↥(S.L1 ⊔ T)).map S.phiL1T).Normal :=
        Subgroup.Normal.map (CFSG.LieType.BorelTits.pCore_normal 2) _ hs
      have hp : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥(S.L1 ⊔ T)).map S.phiL1T) :=
        (CFSG.LieType.BorelTits.pCore_isPGroup 2).map _
      have hbot := eq_bot_of_normal_isPGroup_perm3 hn hp
      intro g hg
      have : S.phiL1T g ∈ (CFSG.Open.pCore 2 ↥(S.L1 ⊔ T)).map S.phiL1T :=
        Subgroup.mem_map_of_mem _ hg
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    · refine CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker _) fun g => ?_
      have hgT : ((g : ↥(S.L1 ⊔ T)) : G) ∈ T := S.mem_T_of_phiL1T_eq_one _ g.2
      obtain ⟨k, hk⟩ := S.isPGroup_T ⟨_, hgT⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      simpa using congrArg Subtype.val hk
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hs)⟩

theorem inf_L1T_eq_T {H : Subgroup G} (hTH : T ≤ H) {t : G} (ht : t ∈ T)
    (htN : t ∈ Subgroup.normalizer (V : Set G)) (hts : S.frame.ρ ⟨t, htN⟩ = Equiv.swap 0 1)
    (hpow3 : ∀ k ∈ oTwoUpper H, ∃ a : ℕ, k ^ 3 ^ a ∈ pCoreOf 2 H)
    (h3 : ¬ ThreeTop (S.H0 H)) : (S.L1 ⊔ T) ⊓ H = T := by
  refine le_antisymm (fun g hg => ?_) (le_inf le_sup_right hTH)
  by_contra hgT
  set Φ := S.phiL1T with hΦ
  set g' : ↥(S.L1 ⊔ T) := ⟨g, hg.1⟩ with hg'
  set t' : ↥(S.L1 ⊔ T) := ⟨t, Subgroup.mem_sup_right ht⟩ with ht'
  have hφt : Φ t' = kappa (Equiv.swap 0 1) := by rw [hΦ, phiL1T_apply, ← hts]
  have hker : ∀ x : ↥(S.L1 ⊔ T), Φ x = 1 → (x : G) ∈ T := S.mem_T_of_phiL1T_eq_one
  have hg1 : Φ g' ≠ 1 := fun h => hgT (hker g' h)
  have hgs : Φ g' ≠ kappa (Equiv.swap 0 1) := by
    intro h
    apply hgT
    have h1 : Φ (t'⁻¹ * g') = 1 := by rw [map_mul, map_inv, hφt, h, inv_mul_cancel]
    have h2 : t⁻¹ * g ∈ T := hker _ h1
    have e : g = t * (t⁻¹ * g) := by group
    rw [e]
    exact T.mul_mem ht h2
  have hall : S.L1 ⊔ T ≤ H := by
    intro x hx
    have hY : ∀ π : Equiv.Perm (Fin 3), ∃ y : ↥(S.L1 ⊔ T), (y : G) ∈ H ∧ Φ y = π := by
      intro π
      have htH := hTH ht
      rcases perm3_words (Φ g') π hg1 hgs with h | h | h | h | h | h | h | h
      · exact ⟨1, H.one_mem, by rw [h, map_one]⟩
      · exact ⟨g', hg.2, h.symm⟩
      · exact ⟨g' ^ 2, H.pow_mem hg.2 2, by rw [map_pow, h]⟩
      · exact ⟨t', htH, by rw [hφt, h]⟩
      · exact ⟨t' * g', H.mul_mem htH hg.2, by rw [map_mul, hφt, h]⟩
      · exact ⟨t' * g' ^ 2, H.mul_mem htH (H.pow_mem hg.2 2), by rw [map_mul, map_pow, hφt, h]⟩
      · exact ⟨g' * t', H.mul_mem hg.2 htH, by rw [map_mul, hφt, h]⟩
      · exact ⟨g' * t' * g', H.mul_mem (H.mul_mem hg.2 htH) hg.2,
          by rw [map_mul, map_mul, hφt, h]⟩
    obtain ⟨y, hyH, hy⟩ := hY (Φ ⟨x, hx⟩)
    have h1 : Φ (y⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hy, inv_mul_cancel]
    have h2 : (y : G)⁻¹ * x ∈ T := hker _ h1
    have e : x = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [e]
    exact H.mul_mem hyH (hTH h2)
  apply h3
  have hH0 : S.H0 H = H := le_antisymm (sup_le (S.borel_L_le.trans hall) le_rfl) le_sup_right
  rw [hH0]
  exact threeTop_of_pow_mem hpow3

theorem H0_eq_sup {H : Subgroup G} (hTH : T ≤ H) : S.H0 H = (S.L1 ⊔ T) ⊔ H := by
  apply le_antisymm
  · exact sup_le_sup_right S.borel_L_le H
  · exact sup_le (sup_le (S.L1_le_borel_L.trans le_sup_left) (hTH.trans le_sup_right))
      le_sup_right

theorem pow_three_pow_mem (h331 : Stmt3_3_1)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3))) :
    ∀ k ∈ oTwoUpper H, ∃ a : ℕ, k ^ 3 ^ a ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hMP, -⟩ := S.hyp501.minParabolic_of_isHStar h331 hH
  obtain ⟨p, hp, -, hpow⟩ := hMP.exists_prime_pow_mem_pCoreOf hsolv
  rw [twoResidual_eq_oTwoUpper'] at hpow
  obtain ⟨F, hF1, hFsurj, hFT, hFL⟩ := S.exists_F h331 hH hsolv hS3
  obtain ⟨y, hyL, -, hFy, -⟩ := S.exists_gen h331 hH hHZ hsolv hF1 hFsurj hFT hFL
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hH.1.1
  obtain ⟨hUO, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl (S.charTwo_of_inH hH.1) le_rfl
  have hO2U : pCoreOf 2 H ≤ Subgroup.centralizer (S.UH H : Set G) :=
    Subgroup.le_centralizer_iff.mp (hUO.trans inf_le_right)
  have hFy3 : orderOf (F ⟨y, oTwoUpper_le H hyL⟩) = 3 := orderOf_eq_prime (hFL y hyL) hFy
  have hp3 : p = 3 := by
    obtain ⟨a, ha⟩ := hpow y hyL
    have h1 : F ⟨y, oTwoUpper_le H hyL⟩ ^ p ^ a = 1 := by
      rw [← map_pow]
      exact (hF1 _).2 (hO2U ha)
    have h3 : 3 ∣ p ^ a := by
      rw [← hFy3]
      exact orderOf_dvd_of_pow_eq_one h1
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  rw [hp3] at hpow
  exact hpow

theorem triple_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h5172 : Stmt5_1_7_two) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (h3 : ¬ ThreeTop (S.H0 H)) : F6.IsGoldschmidtTripleIn (S.H0 H) (S.L1 ⊔ T) H := by
  have hTH : T ≤ H := hH.1.1
  obtain ⟨⟨j, hjJ, hjN, hj⟩, -⟩ :=
    S.lemma_13_2_4_two_b (S.thompsonJ_not_le_centralizer h5172 hH hHZ)
  have hjT : j ∈ T := thompsonJ_le_self T hjJ
  have hpow3 := S.pow_three_pow_mem h331 hH hHZ hsolv hS3
  refine ⟨(S.H0_eq_sup hTH).symm, S.quotient_L1T_equiv_S3 hjT hjN hj,
    S.quotient_pCore_equiv_S3 h331 h1222 hH hHZ hsolv hS3, ?_⟩
  rw [S.inf_L1T_eq_T hTH hjT hjN hj hpow3 h3]
  exact isSylowTwoOf_of_le S.h13.sylow (hTH.trans le_sup_right)

theorem f618_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h5172 : Stmt5_1_7_two) (hF618 : F6.TheoremF618Cat)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (hO2 : pCoreOf 2 (S.H0 H) ≠ ⊥) (h3 : ¬ ThreeTop (S.H0 H)) :
    IsGoldschmidtAmalgam
        (((S.L1 ⊔ T).subgroupOf (S.H0 H)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H))))
        ((H.subgroupOf (S.H0 H)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)))) ∧
      F6.F618ConclusionCat
        (((S.L1 ⊔ T).subgroupOf (S.H0 H)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H))))
        ((H.subgroupOf (S.H0 H)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)))) := by
  have htriple := S.triple_of h331 h1222 h5172 hH hHZ hsolv hS3 h3
  rcases htriple.goldschmidt_mod_pPrimeCore with ⟨-, hAm, -⟩ | ⟨-, -, ⟨e⟩, -, -⟩
  · have := S.h13.simple
    have hSQ : CFSG.SectionRank.IsSQTKCat ↥(S.H0 H) :=
      (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1 _ hO2
    exact ⟨hAm, hF618 _ _ _ hAm.toIsGoldschmidtTriple
      ⟨↥(S.H0 H), inferInstance, inferInstance, hSQ, ⟨MulEquiv.refl _⟩⟩⟩
  · exfalso
    apply h3
    intro q
    refine ⟨1, ?_⟩
    have hq : e q ∈ oTwoUpper (⊤ : Subgroup (Equiv.Perm (Fin 3))) := by
      rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective, oTwoUpper_map]
      exact ⟨q, q.2, rfl⟩
    have h1 : e ((q : _) ^ 3) = 1 := by rw [map_pow]; exact oTwoUpper_perm3 _ hq
    apply Subtype.ext
    simpa using (map_eq_one_iff e e.injective).mp h1

end Setting

end CFSG.Quasithin.H13.A5
