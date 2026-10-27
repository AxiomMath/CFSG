module

public import CFSG.Quasithin.H13.A7Rho

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped Pointwise commutatorElement

theorem s3_mem_alternating : ∀ a c : Perm (Fin 3), sign a = 1 → (∀ k, c k ≠ k) →
    a = 1 ∨ a = c ∨ a = c ^ 2 := by
  decide

theorem s3_decomp : ∀ τ c τ₀ : Perm (Fin 3), (∀ k, c k ≠ k) → sign τ₀ = -1 →
    ∃ m : Fin 3, ∃ δ : Fin 2, τ = c ^ (m : ℕ) * τ₀ ^ (δ : ℕ) := by
  decide

theorem s3_cycle_eq_pow : ∀ a c : Perm (Fin 3), (∀ k, a k ≠ k) → (∀ k, c k ≠ k) →
    a = c ∨ a = c ^ 2 := by
  decide

theorem res3_cyc016_even : ∀ i : Fin 3, ∀ k : Fin 3,
    r3fun (cyc016 ^ (i : ℕ)) (r3fun (cyc016 ^ (i : ℕ)) (r3fun (cyc016 ^ (i : ℕ)) k)) = k := by
  decide +kernel

theorem r3fun_swap01 : ∀ k : Fin 3, r3fun (swap 0 1) k = (swap 0 1 : Perm (Fin 3)) k := by
  decide +kernel

theorem r3fun_swap23 : ∀ k : Fin 3, r3fun (swap 2 3) k = k := by
  decide +kernel

theorem swap01_mem_stab016 : (swap 0 1 : Perm (Fin 7)) ∈ stab016 := q48_le_stab016 (by
  rw [mem_q48_iff]
  decide +kernel)

theorem swap23_mem_stab016 : (swap 2 3 : Perm (Fin 7)) ∈ stab016 := q48_le_stab016 (by
  rw [mem_q48_iff]
  decide +kernel)

theorem cyc016_pow_moves_vecTwo : ∀ i : Fin 3, i ≠ 0 →
    permAct7 (cyc016 ^ (i : ℕ)) vecTwo ≠ vecTwo := by
  decide +kernel

theorem s3_sign_of_cube : ∀ x : Perm (Fin 3), x ^ 3 = 1 → sign x = 1 := by
  decide

theorem s3_sign_swap01 : sign (swap 0 1 : Perm (Fin 3)) = -1 := by
  decide

section Main

variable {G : Type} [Group G]

theorem A7NatConfig.exists_rho (T : Sylow 2 G) {L V K D : Subgroup G}
    {ψ : V ≃* Multiplicative (evenWeight 7)} (h : A7NatConfig (T : Subgroup G) L V ψ)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hC2 : IsPGroup 2 (L ⊓ centralizer (V : Set G) : Subgroup G))
    (hTP : ∀ t ∈ (T : Subgroup G), ∃ u, IsCoordAct ψ t (sevenWord u))
    {e : V} (hTe : (T : Subgroup G) ≤ centralizer ({(e : G)} : Set G))
    (eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))
    (hCK : centralizer ({(e : G)} : Set G) ≤ normalizer (K : Set G))
    (hKZ : ¬ K ≤ centralizer (quasithinOmegaOneCenter (T : Subgroup G) : Set G))
    {e₂ : V} (he₂ : vec ψ e₂ = vecTwo)
    (he₂Z : (e₂ : G) ∈ quasithinOmegaOneCenter (T : Subgroup G))
    (hDL : D ≤ L) (hDe : D ≤ centralizer ({(e : G)} : Set G)) (hDK : D ≤ kerK eK)
    (hDN : D ≤ normalizer (V : Set G))
    (hDc : ∀ d ∈ D, ∃ σ ∈ zpowers cyc016, IsCoordAct ψ d σ)
    {d₀ : G} (hd₀ : d₀ ∈ D) {i₀ : Fin 3} (hi₀ : i₀ ≠ 0)
    (hd₀l : IsCoordAct ψ d₀ (cyc016 ^ (i₀ : ℕ)))
    {t₀ : G} (ht₀T : t₀ ∈ (T : Subgroup G)) (ht₀ : IsCoordAct ψ t₀ (swap 0 1))
    {t₂ : G} (ht₂T : t₂ ∈ (T : Subgroup G)) (ht₂ : IsCoordAct ψ t₂ (swap 2 3))
    (ht₂K : sign (kAct eK ⟨t₂, hCK (hTe ht₂T)⟩) = -1) :
    ∃ ρ : ↥((D ⊔ (T : Subgroup G)) ⊔ K) →* Perm (Fin 5) × Perm (Fin 3),
      Function.Surjective ρ ∧
      ρ.ker = (centralizer (VZ (T : Subgroup G) ((D ⊔ (T : Subgroup G)) ⊔ K) : Set G)).subgroupOf
        ((D ⊔ (T : Subgroup G)) ⊔ K) ∧
      (K.subgroupOf ((D ⊔ (T : Subgroup G)) ⊔ K)).map ρ = (alternatingGroup (Fin 5)).prod ⊥ ∧
      (D.subgroupOf ((D ⊔ (T : Subgroup G)) ⊔ K)).map ρ =
        (⊥ : Subgroup (Perm (Fin 5))).prod (alternatingGroup (Fin 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter (T : Subgroup G) with hZdef
  set W : Subgroup G := D ⊔ (T : Subgroup G) with hWdef
  set Y : Subgroup G := W ⊔ K with hYdef
  set N := normalizer (V : Set G) with hNdef
  have hTN : (T : Subgroup G) ≤ N := h.T_le
  have hWN : W ≤ N := sup_le hDN hTN
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) := hTe.trans hCK
  have hWK : W ≤ normalizer (K : Set G) := sup_le (hDe.trans hCK) hTK
  have hYK : Y ≤ normalizer (K : Set G) := sup_le hWK le_normalizer
  have hWLT : W ≤ L ⊔ (T : Subgroup G) := sup_le (hDL.trans le_sup_left) le_sup_right
  have hC2LT := isPGroup_sup_inf_centralizer hC2 T.isPGroup' hTL
  have hTZ : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    intro t ht
    rw [mem_centralizer_iff]
    intro z hz
    have hzC : z ∈ centralizer ((T : Subgroup G) : Set G) :=
      ((Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2) hz
    exact (mem_centralizer_iff.1 hzC t ht).symm
  have hWq : ∀ w (hw : w ∈ W), h.lamN ⟨w, hWN hw⟩ ∈ q48 := by
    set Qs : Subgroup G := (q48.comap h.lamN).map N.subtype with hQsdef
    have hWQ : W ≤ Qs := by
      refine sup_le (fun d hd => ?_) (fun t ht => ?_)
      · obtain ⟨σ, hσ, hdσ⟩ := hDc d hd
        refine ⟨⟨d, hDN hd⟩, ?_, rfl⟩
        show h.lamN ⟨d, hDN hd⟩ ∈ q48
        rw [h.lamN_eq _ hdσ]
        exact (zpowers_le.2 cyc016_mem_q48) hσ
      · obtain ⟨u, htu⟩ := hTP t ht
        refine ⟨⟨t, hTN ht⟩, ?_, rfl⟩
        show h.lamN ⟨t, hTN ht⟩ ∈ q48
        rw [h.lamN_eq _ htu]
        exact word_mem_q48 u
    intro w hw
    obtain ⟨⟨w', hw'N⟩, hw'q, hw'⟩ := hWQ hw
    have hww : w' = w := hw'
    subst hww
    exact hw'q
  set lam3 : W →* Perm (Fin 3) := res3.comp ((h.lamN.comp (inclusion hWN)).codRestrict stab016
    fun w => q48_le_stab016 (hWq w w.2)) with hlam3
  have hlam3_apply : ∀ (w : G) (hw : w ∈ W), lam3 ⟨w, hw⟩ =
      res3 ⟨h.lamN ⟨w, hWN hw⟩, q48_le_stab016 (hWq w hw)⟩ := fun _ _ => rfl
  have hd₀W : d₀ ∈ W := mem_sup_left hd₀
  have hkill : ∀ w (hw : w ∈ W), w ∈ K → lam3 ⟨w, hw⟩ = 1 := fun w hw hwK =>
    h.res3_eq_one_of_mem eK hWN hWK hWq hWLT hC2LT hd₀W (hDK hd₀) hi₀ hd₀l hwK hw
  obtain ⟨ρ₂, hρ₂W, hρ₂K⟩ := exists_rho2 hWK lam3 hkill
  set ρ₁ : Y →* Perm (Fin 5) := (kAct eK).comp (inclusion hYK) with hρ₁def
  have hρ₁_apply : ∀ (y : G) (hy : y ∈ Y), ρ₁ ⟨y, hy⟩ = kAct eK ⟨y, hYK hy⟩ := fun _ _ => rfl
  have hd₀Y : d₀ ∈ Y := mem_sup_left hd₀W
  have ht₀Y : t₀ ∈ Y := mem_sup_left (mem_sup_right ht₀T)
  have ht₂Y : t₂ ∈ Y := mem_sup_left (mem_sup_right ht₂T)
  have hρ₂d₀ : ∀ k, ρ₂ ⟨d₀, hd₀Y⟩ k ≠ k := by
    intro k
    rw [hρ₂W d₀ hd₀W, hlam3_apply, res3_apply]
    simp only
    rw [h.lamN_eq _ hd₀l]
    exact r3fun_cyc016_pow i₀ hi₀ k
  have hρ₂t₀ : ρ₂ ⟨t₀, ht₀Y⟩ = swap 0 1 := by
    rw [hρ₂W t₀ (mem_sup_right ht₀T), hlam3_apply]
    ext k
    rw [res3_apply]
    simp only
    rw [h.lamN_eq _ ht₀]
    exact congrArg Fin.val (r3fun_swap01 k)
  have hρ₂t₂ : ρ₂ ⟨t₂, ht₂Y⟩ = 1 := by
    rw [hρ₂W t₂ (mem_sup_right ht₂T), hlam3_apply]
    ext k
    rw [res3_apply]
    simp only
    rw [h.lamN_eq _ ht₂]
    exact congrArg Fin.val (r3fun_swap23 k)
  have hρ₁d : ∀ d (hd : d ∈ D), ρ₁ ⟨d, mem_sup_left (mem_sup_left hd)⟩ = 1 := by
    intro d hd
    obtain ⟨hdN, hd1⟩ := (mem_kerK eK).1 (hDK hd)
    exact hd1
  have hρ₁k : ∀ k (hk : k ∈ K), ρ₁ ⟨k, mem_sup_right hk⟩ = kBar eK ⟨k, hk⟩ := fun k hk =>
    kAct_of_mem eK hk
  have hρ₂k : ∀ k (hk : k ∈ K), ρ₂ ⟨k, mem_sup_right hk⟩ = 1 := hρ₂K
  have hker2 : ∀ y (hy : y ∈ Y), ρ₁ ⟨y, hy⟩ = 1 → ρ₂ ⟨y, hy⟩ = 1 → ∃ n, y ^ 2 ^ n = 1 := by
    intro y hy h1 h2
    have hy' : y ∈ ((W ⊔ K : Subgroup G) : Set G) := hy
    rw [coe_mul_of_left_le_normalizer_right W K hWK] at hy'
    obtain ⟨s, hs, k, hk, rfl⟩ := hy'
    have hsY : s ∈ Y := mem_sup_left hs
    have h3 : ρ₂ ⟨s, hsY⟩ = 1 := by
      have := h2
      rw [show (⟨s * k, hy⟩ : Y) = ⟨s, hsY⟩ * ⟨k, mem_sup_right hk⟩ from rfl, map_mul,
        hρ₂k k hk, mul_one] at this
      exact this
    rw [hρ₂W s hs, hlam3_apply] at h3
    obtain ⟨i, u, hiu⟩ := exists_fam48 (hWq s hs)
    have hr3 : ∀ k', r3fun (fam48 i u) k' = k' := by
      intro k'
      have := congrArg (fun f : Perm (Fin 3) => f k') h3
      simp only [res3_apply, Perm.one_apply] at this
      rwa [hiu] at this
    have h4 := fam48_pow_four_of_r3 i u hr3
    have hs4C : s ^ 4 ∈ centralizer (V : Set G) := by
      have h5 : h.lamN ⟨s ^ 4, hWN (pow_mem hs 4)⟩ = 1 := by
        rw [show (⟨s ^ 4, hWN (pow_mem hs 4)⟩ : N) = ⟨s, hWN hs⟩ ^ 4 from rfl, map_pow, hiu, h4]
      exact (h.lamN_eq_one_iff _).1 h5
    obtain ⟨a, ha⟩ := hC2LT ⟨s ^ 4, mem_inf.2 ⟨hWLT (pow_mem hs 4), hs4C⟩⟩
    have ha' : (s ^ 4) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hsN : s ∈ normalizer (K : Set G) := hWK hs
    have hk' : s * k * s⁻¹ ∈ K := (mem_normalizer_iff.1 hsN k).1 hk
    obtain ⟨k'', hk'', h6⟩ := exists_pow_eq_mul_pow (N := K) hk' hsN (4 * 2 ^ a)
    have h7 : (s * k) ^ (4 * 2 ^ a) = k'' := by
      rw [show s * k = s * k * s⁻¹ * s by group, h6, pow_mul, ha', mul_one]
    have h8 : ρ₁ ⟨k'', mem_sup_right hk''⟩ = 1 := by
      have : (⟨k'', mem_sup_right hk''⟩ : Y) = ⟨s * k, hy⟩ ^ (4 * 2 ^ a) :=
        Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h7.symm)
      rw [this, map_pow, h1, one_pow]
    rw [hρ₁k k'' hk''] at h8
    rw [kBar_eq_one_iff] at h8
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)) ⟨⟨k'', hk''⟩, h8⟩
    have hb' : k'' ^ 2 ^ b = 1 := by
      have h9 := congrArg (fun x : ↥(CFSG.pCore 2 ↥K) => ((x : K) : G)) hb
      simpa using h9
    refine ⟨2 + a + b, ?_⟩
    rw [show 2 + a + b = (2 + a) + b by ring, pow_add, pow_mul, show 2 ^ (2 + a) = 4 * 2 ^ a by
      rw [pow_add]; norm_num, h7, hb']
  set R : Subgroup G := (ρ₁.prod ρ₂).ker.map Y.subtype with hRdef
  have hmemR : ∀ y (hy : y ∈ Y), y ∈ R ↔ ρ₁ ⟨y, hy⟩ = 1 ∧ ρ₂ ⟨y, hy⟩ = 1 := by
    intro y hy
    constructor
    · rintro ⟨⟨y', hy'⟩, hker, hyy⟩
      have hyy' : y' = y := hyy
      subst hyy'
      have hker' : (ρ₁.prod ρ₂) ⟨y', hy'⟩ = 1 := hker
      rw [MonoidHom.prod_apply, Prod.mk_eq_one] at hker'
      exact hker'
    · rintro ⟨h1, h2⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      show (ρ₁.prod ρ₂) ⟨y, hy⟩ = 1
      rw [MonoidHom.prod_apply, Prod.mk_eq_one]
      exact ⟨h1, h2⟩
  have hRY : R ≤ Y := map_subtype_le _
  have hR2 : IsPGroup 2 R := by
    rintro ⟨y, hyR⟩
    obtain ⟨h1, h2⟩ := (hmemR y (hRY hyR)).1 hyR
    obtain ⟨n, hn⟩ := hker2 y (hRY hyR) h1 h2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hYR : Y ≤ normalizer (R : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    have key : ∀ g' (hg' : g' ∈ Y) y, y ∈ R → g' * y * g'⁻¹ ∈ R := by
      intro g' hg' y hyR
      have hyY := hRY hyR
      obtain ⟨h1, h2⟩ := (hmemR y hyY).1 hyR
      have hcY : g' * y * g'⁻¹ ∈ Y := mul_mem (mul_mem hg' hyY) (inv_mem hg')
      refine (hmemR _ hcY).2 ⟨?_, ?_⟩
      · rw [show (⟨g' * y * g'⁻¹, hcY⟩ : Y) = ⟨g', hg'⟩ * ⟨y, hyY⟩ * ⟨g', hg'⟩⁻¹ from rfl,
          map_mul, map_mul, map_inv, h1, mul_one, mul_inv_cancel]
      · rw [show (⟨g' * y * g'⁻¹, hcY⟩ : Y) = ⟨g', hg'⟩ * ⟨y, hyY⟩ * ⟨g', hg'⟩⁻¹ from rfl,
          map_mul, map_mul, map_inv, h2, mul_one, mul_inv_cancel]
    intro y
    constructor
    · exact key g hg y
    · intro hy
      have := key g⁻¹ (inv_mem hg) _ hy
      rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this
  have hTY : (T : Subgroup G) ≤ Y := le_sup_right.trans le_sup_left
  have hRT : R ≤ T := by
    have h1 := T.3 (hR2.to_sup_of_normal_left' T.isPGroup' (hTY.trans hYR)) le_sup_right
    rw [← h1]
    exact le_sup_left
  set U := VZ (T : Subgroup G) Y with hUdef
  have hZU : Z ≤ U := le_conjClosure _ _
  have hYU : Y ≤ normalizer (U : Set G) := le_normalizer_conjClosure _ _
  have hRU : R ≤ centralizer (U : Set G) := by
    intro r hr
    have hrY := hRY hr
    rw [hUdef, VZ, conjClosure, Subgroup.centralizer_closure]
    rw [mem_centralizer_iff]
    rintro _ ⟨g, hg, z, hz, rfl⟩
    have h1 : g⁻¹ * r * g ∈ R := by
      have := (mem_normalizer_iff.1 (hYR (inv_mem hg)) r).1 hr
      rwa [inv_inv] at this
    have h2 : g⁻¹ * r * g * z = z * (g⁻¹ * r * g) :=
      (mem_centralizer_iff.1 (hTZ (hRT h1)) z hz).symm
    calc g * z * g⁻¹ * r = g * (z * (g⁻¹ * r * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * r * g * z) * g⁻¹ := by rw [h2]
      _ = r * (g * z * g⁻¹) := by group
  have hKCU : ∀ g ∈ K, g ∈ centralizer (U : Set G) → g ∈ pCoreOf 2 K := by
    set N₁ : Subgroup K := (centralizer (U : Set G)).subgroupOf K with hN₁
    have hN₁n : N₁.Normal := by
      constructor
      intro n hn g
      rw [hN₁, mem_subgroupOf] at hn ⊢
      exact conj_mem_centralizer_of_mem_normalizer (hYU (mem_sup_right g.2)) hn
    have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hmapn : (N₁.map (kHom eK)).Normal := hN₁n.map _ (kHom_surjective eK)
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple (N₁.map (kHom eK)) hmapn with
      hbot | htop
    · intro g hgK hgC
      have h1 : kHom eK ⟨g, hgK⟩ = 1 := by
        have : kHom eK ⟨g, hgK⟩ ∈ N₁.map (kHom eK) := mem_map_of_mem _ (mem_subgroupOf.2 hgC)
        rw [hbot, mem_bot] at this
        exact this
      have h2 : kBar eK ⟨g, hgK⟩ = 1 := by
        show ((kHom eK ⟨g, hgK⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) = 1
        rw [h1]
        rfl
      rw [kBar_eq_one_iff] at h2
      rw [pCoreOf_eq_map_cfsgPCore]
      exact ⟨_, h2, rfl⟩
    · exfalso
      apply hKZ
      intro k hk
      obtain ⟨c, hcN, hck⟩ := (htop ▸ mem_top (kHom eK ⟨k, hk⟩) :
        kHom eK ⟨k, hk⟩ ∈ N₁.map (kHom eK))
      have h1 : kBar eK (c⁻¹ * ⟨k, hk⟩) = 1 := by
        rw [map_mul, map_inv]
        show ((kHom eK c : Perm (Fin 5)))⁻¹ * (kHom eK ⟨k, hk⟩ : Perm (Fin 5)) = 1
        rw [hck]
        simp
      rw [kBar_eq_one_iff] at h1
      have h2 : ((c⁻¹ * ⟨k, hk⟩ : K) : G) ∈ pCoreOf 2 K := by
        rw [pCoreOf_eq_map_cfsgPCore]
        exact ⟨_, h1, rfl⟩
      have h3 : ((c⁻¹ * ⟨k, hk⟩ : K) : G) ∈ centralizer (Z : Set G) :=
        hTZ (pCoreOf_le_of_le_normalizer T hTK h2)
      have h4 : (c : G) ∈ centralizer (Z : Set G) :=
        centralizer_le hZU (mem_subgroupOf.1 hcN)
      have h5 := mul_mem h4 h3
      simpa using h5
  refine ⟨ρ₁.prod ρ₂, ?_, ?_, ?_, ?_⟩
  ·
    rintro ⟨σ, τ⟩
    obtain ⟨m, δ, hτ⟩ := s3_decomp τ (ρ₂ ⟨d₀, hd₀Y⟩) (ρ₂ ⟨t₀, ht₀Y⟩) hρ₂d₀
      (by rw [hρ₂t₀]; exact s3_sign_swap01)
    set α₀ := ρ₁ ⟨t₀, ht₀Y⟩ with hα₀
    set β := ρ₁ ⟨t₂, ht₂Y⟩ with hβ
    have hβs : sign β = -1 := ht₂K
    set σ' := σ * (α₀ ^ (δ : ℕ))⁻¹ with hσ'
    obtain ⟨ε, hε⟩ : ∃ ε : ℕ, sign (σ' * (β ^ ε)⁻¹) = 1 := by
      by_cases hs : sign σ' = 1
      · exact ⟨0, by simpa using hs⟩
      · refine ⟨1, ?_⟩
        rw [map_mul, map_inv, pow_one, hβs, (Int.units_eq_one_or _).resolve_left hs]
        rfl
    obtain ⟨k, hk⟩ := kHom_surjective eK ⟨σ' * (β ^ ε)⁻¹, mem_alternatingGroup.2 hε⟩
    have hkbar : kBar eK k = σ' * (β ^ ε)⁻¹ := congrArg Subtype.val hk
    refine ⟨⟨k, mem_sup_right k.2⟩ * ⟨d₀, hd₀Y⟩ ^ (m : ℕ) * ⟨t₂, ht₂Y⟩ ^ ε *
      ⟨t₀, ht₀Y⟩ ^ (δ : ℕ), ?_⟩
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, MonoidHom.prod_apply,
      MonoidHom.prod_apply, MonoidHom.prod_apply, MonoidHom.prod_apply]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, Prod.pow_fst]
      rw [show (⟨(k : G), mem_sup_right k.2⟩ : Y) = ⟨(k : G), mem_sup_right k.2⟩ from rfl,
        hρ₁k _ k.2, show (⟨(k : G), k.2⟩ : K) = k from rfl, hkbar,
        hρ₁d d₀ hd₀, one_pow, mul_one, ← hβ, ← hα₀, hσ']
      group
    · simp only [Prod.snd_mul, Prod.pow_snd]
      rw [hρ₂k _ k.2, one_mul, hρ₂t₂, one_pow, mul_one]
      exact hτ.symm
  ·
    ext ⟨y, hy⟩
    rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.prod_apply, Prod.mk_eq_one]
    constructor
    · rintro ⟨h1, h2⟩
      exact hRU ((hmemR y hy).2 ⟨h1, h2⟩)
    · intro hyC
      have h1 : ρ₁ ⟨y, hy⟩ = 1 := by
        rw [hρ₁_apply]
        refine kAct_eq_one_of_comm eK (hYK hy) fun k hk => hKCU _ ?_ ?_
        · exact mul_mem ((mem_normalizer_iff.1 (hYK hy) k).1 hk) (inv_mem hk)
        · have h2 : k * y⁻¹ * k⁻¹ ∈ centralizer (U : Set G) :=
            conj_mem_centralizer_of_mem_normalizer (hYU (mem_sup_right hk)) (inv_mem hyC)
          have h3 := mul_mem hyC h2
          rwa [show y * (k * y⁻¹ * k⁻¹) = y * k * y⁻¹ * k⁻¹ by group] at h3
      refine ⟨h1, ?_⟩
      by_contra hne
      obtain ⟨c, hcY, hcC, hc1, hc3⟩ : ∃ (c : G) (hcY : c ∈ Y), c ∈ centralizer (U : Set G) ∧
          ρ₁ ⟨c, hcY⟩ = 1 ∧ ∀ k, ρ₂ ⟨c, hcY⟩ k ≠ k := by
        by_cases hs : sign (ρ₂ ⟨y, hy⟩) = 1
        · exact ⟨y, hy, hyC, h1, s3_even_no_fix _ hs hne⟩
        · have hs' : sign (ρ₂ ⟨y, hy⟩) = -1 := (Int.units_eq_one_or _).resolve_left hs
          have hcY : ⁅y, d₀⁆ ∈ Y := by
            rw [commutatorElement_def]
            exact mul_mem (mul_mem (mul_mem hy hd₀Y) (inv_mem hy)) (inv_mem hd₀Y)
          refine ⟨⁅y, d₀⁆, hcY, ?_, ?_, ?_⟩
          · rw [commutatorElement_def]
            have h2 : d₀ * y⁻¹ * d₀⁻¹ ∈ centralizer (U : Set G) :=
              conj_mem_centralizer_of_mem_normalizer (hYU hd₀Y) (inv_mem hyC)
            have h3 := mul_mem hyC h2
            rwa [show y * (d₀ * y⁻¹ * d₀⁻¹) = y * d₀ * y⁻¹ * d₀⁻¹ by group] at h3
          · rw [show (⟨⁅y, d₀⁆, hcY⟩ : Y) = ⁅(⟨y, hy⟩ : Y), ⟨d₀, hd₀Y⟩⁆ from rfl,
              map_commutatorElement, h1, hρ₁d d₀ hd₀]
            simp
          · rw [show (⟨⁅y, d₀⁆, hcY⟩ : Y) = ⁅(⟨y, hy⟩ : Y), ⟨d₀, hd₀Y⟩⁆ from rfl,
              map_commutatorElement]
            exact s3_comm_cycle _ _ hs' hρ₂d₀
      obtain ⟨m, hm12, hm⟩ : ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ ρ₂ ⟨c, hcY⟩ = ρ₂ ⟨d₀, hd₀Y⟩ ^ m := by
        rcases s3_cycle_eq_pow _ _ hc3 hρ₂d₀ with h2 | h2
        · exact ⟨1, Or.inl rfl, by rw [pow_one, h2]⟩
        · exact ⟨2, Or.inr rfl, h2⟩
      have hgY : c * (d₀ ^ m)⁻¹ ∈ Y := mul_mem hcY (inv_mem (pow_mem hd₀Y m))
      have hgR : c * (d₀ ^ m)⁻¹ ∈ R := by
        refine (hmemR _ hgY).2 ⟨?_, ?_⟩
        · rw [show (⟨c * (d₀ ^ m)⁻¹, hgY⟩ : Y) = ⟨c, hcY⟩ * (⟨d₀, hd₀Y⟩ ^ m)⁻¹ from rfl, map_mul,
            map_inv, map_pow, hc1, hρ₁d d₀ hd₀, one_pow, inv_one, one_mul]
        · rw [show (⟨c * (d₀ ^ m)⁻¹, hgY⟩ : Y) = ⟨c, hcY⟩ * (⟨d₀, hd₀Y⟩ ^ m)⁻¹ from rfl, map_mul,
            map_inv, map_pow, hm, mul_inv_cancel]
      have hdC : d₀ ^ m ∈ centralizer (U : Set G) := by
        have h2 := mul_mem (inv_mem (hRU hgR)) hcC
        rwa [show (c * (d₀ ^ m)⁻¹)⁻¹ * c = d₀ ^ m by group] at h2
      have hd₀mN : d₀ ^ m ∈ N := pow_mem (hDN hd₀) m
      have hlam : h.lamN ⟨d₀ ^ m, hd₀mN⟩ = (cyc016 ^ (i₀ : ℕ)) ^ m := by
        rw [show (⟨d₀ ^ m, hd₀mN⟩ : N) = ⟨d₀, hDN hd₀⟩ ^ m from rfl, map_pow, h.lamN_eq _ hd₀l]
      set j : Fin 3 := ⟨((i₀ : ℕ) * m) % 3, Nat.mod_lt _ (by norm_num)⟩ with hjdef
      have hlam' : h.lamN ⟨d₀ ^ m, hd₀mN⟩ = cyc016 ^ (j : ℕ) := by
        rw [hlam, ← pow_mul, cyc016_pow_mod]
      have hj : j ≠ 0 := by
        intro hj0
        have h2 : ((i₀ : ℕ) * m) % 3 = 0 := by
          have := congrArg Fin.val hj0
          simpa [hjdef] using this
        have hi3 : (i₀ : ℕ) < 3 := i₀.2
        have hi0 : (i₀ : ℕ) ≠ 0 := fun h0 => hi₀ (Fin.ext h0)
        rcases hm12 with rfl | rfl <;> omega
      have hfix := h.lamN_spec ⟨d₀ ^ m, hd₀mN⟩ e₂ e₂ (by
        show (e₂ : G) = d₀ ^ m * e₂ * (d₀ ^ m)⁻¹
        rw [← mem_centralizer_iff.1 hdC e₂ (hZU he₂Z), mul_inv_cancel_right])
      rw [hlam', he₂] at hfix
      exact cyc016_pow_moves_vecTwo j hj hfix.symm
  ·
    ext ⟨α, β⟩
    constructor
    · rintro ⟨⟨y, hy⟩, hyK, hyρ⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at hyK
      rw [MonoidHom.prod_apply] at hyρ
      rw [← hyρ, mem_prod]
      refine ⟨?_, ?_⟩
      · rw [show (⟨y, hy⟩ : Y) = ⟨y, mem_sup_right hyK⟩ from rfl, hρ₁k y hyK]
        exact kBar_mem eK _
      · rw [show (⟨y, hy⟩ : Y) = ⟨y, mem_sup_right hyK⟩ from rfl, hρ₂k y hyK]
        exact one_mem _
    · intro hab
      have hα : α ∈ alternatingGroup (Fin 5) := (mem_prod.1 hab).1
      have hβ : β = 1 := by simpa using (mem_prod.1 hab).2
      obtain ⟨k, hk⟩ := kHom_surjective eK ⟨α, hα⟩
      refine ⟨⟨k, mem_sup_right k.2⟩, mem_subgroupOf.2 k.2, ?_⟩
      rw [MonoidHom.prod_apply, hρ₁k _ k.2, hρ₂k _ k.2, hβ]
      exact Prod.ext (congrArg Subtype.val hk) rfl
  ·
    ext ⟨α, β⟩
    constructor
    · rintro ⟨⟨y, hy⟩, hyD, hyρ⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at hyD
      rw [MonoidHom.prod_apply] at hyρ
      rw [← hyρ, mem_prod]
      refine ⟨?_, ?_⟩
      · rw [show (⟨y, hy⟩ : Y) = ⟨y, mem_sup_left (mem_sup_left hyD)⟩ from rfl, hρ₁d y hyD]
        exact one_mem _
      · rw [show (⟨y, hy⟩ : Y) = ⟨y, mem_sup_left (mem_sup_left hyD)⟩ from rfl,
          hρ₂W y (mem_sup_left hyD), hlam3_apply, mem_alternatingGroup]
        obtain ⟨σ, hσ, hyσ⟩ := hDc y hyD
        obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hσ
        apply s3_sign_of_cube
        rw [← map_pow]
        have h3 : (⟨h.lamN ⟨y, hWN (mem_sup_left hyD)⟩,
            q48_le_stab016 (hWq y (mem_sup_left hyD))⟩ : stab016) ^ 3 = 1 := by
          apply Subtype.ext
          show h.lamN ⟨y, hWN (mem_sup_left hyD)⟩ ^ 3 = 1
          rw [h.lamN_eq _ hyσ, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
            zpow_natCast, cyc016_pow_three, one_zpow]
        rw [h3, map_one]
    · intro hab
      have hα : α = 1 := by simpa using (mem_prod.1 hab).1
      have hβ : β ∈ alternatingGroup (Fin 3) := (mem_prod.1 hab).2
      rcases s3_mem_alternating β _ (mem_alternatingGroup.1 hβ) hρ₂d₀ with h2 | h2 | h2
      · exact ⟨1, one_mem _, by rw [map_one, hα, h2]; rfl⟩
      · refine ⟨⟨d₀, hd₀Y⟩, mem_subgroupOf.2 hd₀, ?_⟩
        rw [MonoidHom.prod_apply, hρ₁d d₀ hd₀, hα, h2]
      · refine ⟨⟨d₀, hd₀Y⟩ ^ 2, mem_subgroupOf.2 (pow_mem hd₀ 2), ?_⟩
        rw [map_pow, MonoidHom.prod_apply, hρ₁d d₀ hd₀, hα, h2, Prod.pow_mk, one_pow]

end Main

end CFSG.Quasithin.H13.A7
