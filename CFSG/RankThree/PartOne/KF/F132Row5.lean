module

public import CFSG.RankThree.PartOne.KF.F132Core
public import CFSG.RankThree.PartOne.KF.F132D8
public import CFSG.RankThree.PartOne.KF.F132Sl2
public import CFSG.RankThree.PartOne.KF.R5Levi2
public import CFSG.RankThree.PartOne.KF.R56Final
public import CFSG.RankThree.PartOne.KFOUT3.KtySUCtx
public import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx
public import CFSG.RankThree.PartOne.KF.F132AtEx
public import CFSG.RankThree.PartOne.KF.F132Center
public import CFSG.RankThree.PartOne.KFOUT3.KtyCore

public section

namespace CFSG.RankThree.PartOne.KF132

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

theorem rowSU_S {n : ℕ} [NeZero n] (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (hc2 : D8Comb2 hc)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) {G : Type} [Group G] {L F : Subgroup G}
    (ε : ↥L →* StatedProj (StatedSU n (2 ^ f) K)) (hε : IsCentralPQuot p ε) (hFL : F ≤ L)
    (hFexp : ∀ f ∈ F, f ^ p = 1)
    (hFT₁ : ∀ t ∈ (d8Tor p K n).subgroupOf (SU (unitaryInvolution K 2 f) n), ∃ x : F,
      ε (Subgroup.inclusion hFL x) = suQ n hK t)
    (hFT₂ : ∀ x : F, ∃ t ∈ (d8Tor p K n).subgroupOf (SU (unitaryInvolution K 2 f) n),
      ε (Subgroup.inclusion hFL x) = suQ n hK t) :
    ∃ S : D8Ctx p K L F, ∀ (d : D8Mod p K) (m : ↥(SU (unitaryInvolution K 2 f) n)),
      (m : GL (Fin n) K) = diagU (d8Vec n d) →
        ε (Subgroup.inclusion hFL (S.tor d)) = suQ n hK m := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  set σ : K ≃+* K := unitaryInvolution K 2 f with hσdef
  have hσ : ∀ c : K, σ c = c ^ 2 ^ f := fun c => unitaryInvolution_apply K 2 f c
  have hσfix : ∀ u : rootsOfUnity p K, σ ((u : Kˣ) : K) = (u : Kˣ) := by
    intro u
    have h1 : (u : Kˣ) ^ p = 1 := (mem_rootsOfUnity p _).mp u.2
    have h2 : (u : Kˣ) ^ (2 ^ f - 1) = 1 := by
      obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, h1, one_pow]
    rw [hσ, ← Units.val_pow_eq_pow_val]
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have : (u : Kˣ) ^ 2 ^ f = (u : Kˣ) := by
      calc (u : Kˣ) ^ 2 ^ f = (u : Kˣ) ^ (2 ^ f - 1) * (u : Kˣ) := by
            rw [← pow_succ, Nat.sub_add_cancel hq1]
        _ = (u : Kˣ) := by rw [h2, one_mul]
    rw [this]
  have hT : ∀ v : D8Mod p K, (diagU (d8Vec n v) : GL (Fin n) K) ∈ SU σ n :=
    fun v => d8Vec_mem_SU hn hc σ hσfix v
  have hP : ∀ τ : Equiv.Perm (Fin n), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
      (permGL τ : GL (Fin n) K) ∈ SU σ n := fun τ hτ => permGL_mem_SU σ τ hτ
  obtain ⟨SM, hSM⟩ := KFOUT3.exists_d8ctx_tor hc hc2 hp hp2 hζ (SU σ n) hT hP
  have hq : IsCentralPQuot p (suQ n hK) := isCentralPQuot_suQ hp hp2 hn1 hpq hf1 hK
  have hVexp : ∀ d : D8Mod p K, d ^ p = 1 := fun d =>
    Prod.ext (Subtype.ext ((mem_rootsOfUnity p _).mp d.1.2))
      (Subtype.ext ((mem_rootsOfUnity p _).mp d.2.2))
  obtain ⟨S, hS⟩ := KFOUT3.wctx_ofCentralQuot' hVexp SM (suQ n hK) hq ε hε hFL hFexp hFT₁ hFT₂
  refine ⟨S, fun d m hm => ?_⟩
  rw [hS d]
  congr 1
  apply Subtype.ext
  rw [hSM d, hm]

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

theorem row5_class0 (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hEA : E = A) (hcL : c ∉ L)
    (hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L)) (hf3 : 3 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hFq : Nat.card (fixF σ) = 2 ^ f) {ζ' : (fixF σ)ˣ} (hζ' : IsPrimitiveRoot ζ' p)
    {P : Type} [Group P] [Finite P] (ε : ↥L →* P) (q : ↥(SU σ 4) →* P)
    (hε : IsCentralPQuot p ε) (hq : IsCentralPQuot p q)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (torus5 σ p).map q)
    {x : G} (hxA : x ∈ A) (hxL : x ∈ L)
    (hb : q (b5 σ (upU σ ζ') (σ_upU σ ζ')) = ε ⟨x, hxL⟩) :
    ∃ t : MulAut E, t ∈ torusImage E L ∧ IsAutReflection p E t ∧
      (∀ hxE : x ∈ E, ((t ⟨x, hxE⟩ : E) : G) = x) ∧ KFAt p E f t ∧
      ((kZero p E t).subgroupOf L).map ε = (suBlock σ).range.map q := by
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hK4 : 4 ≤ Nat.card (fixF σ) := by
    rw [hFq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  set ζ : Kˣ := upU σ ζ' with hζdef
  have hσζ : σ (ζ : K) = ζ := σ_upU σ ζ'
  have hζp' : ζ' ^ p = 1 := hζ'.pow_eq_one
  have hζ'1 : ζ' ≠ 1 := hζ'.ne_one (by omega)
  have hζp : ζ ^ p = 1 := by rw [hζdef, ← map_pow, hζp', map_one]
  have hζ1 : ζ ≠ 1 := fun h1 => hζ'1 (upU_injective σ (by rw [map_one]; exact h1))
  have hζ2' : ζ' ^ 2 ≠ 1 := hζ'.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)
  have hζ2 : ζ ^ 2 ≠ 1 := fun h2 =>
    hζ2' (upU_injective σ (by rw [map_pow, map_one]; exact h2))
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : q (b5 σ ζ hσζ) = q 1 := by
      rw [hb, map_one]
      have : (⟨x, hxL⟩ : ↥L) = 1 := Subtype.ext h1
      rw [this, map_one]
    have hbMne : b5 σ ζ hσζ ≠ 1 := by
      intro h1'
      have := congrArg (fun x : ↥(SU σ 4) => gu x 1 1) h1'
      simp only [gu_one, Matrix.one_apply_eq] at this
      have h11 : gu (b5 σ ζ hσζ) 1 1 = (ζ : K) := by
        show ((diagU (dvec4 1 ζ) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 1 = _
        simp [diagU_val, dvec4]
      exact hζ1 (Units.ext (by rw [← h11]; exact this))
    exact hbMne (hq.eq_of_map_eq (torus5_pow_eq_one (b5_mem_torus5 hσζ hζp)) (one_pow p) h2)
  have hKM := perfectResidual_centralizer_b5 σ hK4 hσζ hζ1 hζ2
  obtain ⟨K₀, hd, hmod, hmap⟩ := layerCore_of_sl2_cover hp hp2 (IsPGroup.of_card h.A_card)
    h.A_elem h.L_le_centralizer hA ε q hε hq hxA hxL hx1
    (torus5_pow_eq_one (b5_mem_torus5 hσζ hζp)) hb.symm (fun t ht => torus5_pow_eq_one ht) hAT
    hFq (by omega) (suBlock σ) (suBlock_injective σ) hKM (card_torus5_inf_range hp.pos ⟨ζ', hζ'⟩)
    rootU5_le_range isPGroup_rootU5 torus5_le_normalizer_rootU5
    ⟨suBlock σ (tr2 1), suBlock_tr2_mem_rootU5 1, rho5 σ ζ', rho5_mem_torus5 hζp',
      suBlock_tr2_one_not_commute_rho5 hζ'1⟩
  obtain ⟨t, htL, hr, hfix, hKF, hKz⟩ := exists_reflection_of_core hGA h hEA hcL hd hf3 hmod
  refine ⟨t, htL, hr, hfix, hKF, ?_⟩
  rw [hKz, hd.K_eq, hmap]

theorem row5_class1 (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hEA : E = A) (hcL : c ∉ L)
    (hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L)) (hf3 : 3 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσσ : ∀ x, σ (σ x) = x)
    (hK : Nat.card K = 2 ^ (2 * f)) (hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ p) {P : Type} [Group P] [Finite P] (ε : ↥L →* P)
    (q : ↥(SU σ 4) →* P) (hε : IsCentralPQuot p ε) (hq : IsCentralPQuot p q)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (torus5 σ p).map q)
    {x : G} (hxA : x ∈ A) (hxL : x ∈ L)
    (hb : q (bB σ ζ (hfix ζ hζ.pow_eq_one)) = ε ⟨x, hxL⟩) :
    ∃ t : MulAut E, t ∈ torusImage E L ∧ IsAutReflection p E t ∧
      (∀ hxE : x ∈ E, ((t ⟨x, hxE⟩ : E) : G) = x) ∧ KFAt p E (2 * f) t ∧
      ((kZero p E t).subgroupOf L).map ε = (suBlockB σ hσσ).range.map q := by
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hσζ : σ (ζ : K) = ζ := hfix ζ hζp
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hζ2 : ζ ^ 2 ≠ 1 := by
    apply hζ.pow_ne_one_of_pos_of_lt (by norm_num)
    omega
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨ζ, hζ⟩
  have hbmem : bB σ ζ hσζ ∈ torus5 σ p := mem_torus5_iff.2 ⟨ζ, ζ, hζp, hζp, rfl⟩
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : q (bB σ ζ hσζ) = q 1 := by
      rw [hb, map_one]
      have : (⟨x, hxL⟩ : ↥L) = 1 := Subtype.ext h1
      rw [this, map_one]
    have hbMne : bB σ ζ hσζ ≠ 1 := by
      intro h1'
      have := congrArg (fun x : ↥(SU σ 4) => gu x 0 0) h1'
      simp only [gu_one, Matrix.one_apply_eq] at this
      have h00 : gu (bB σ ζ hσζ) 0 0 = (ζ : K) := by
        show ((diagU (dvec4 ζ ζ) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 = _
        simp [diagU_val, dvec4]
      exact hζ1 (Units.ext (by rw [← h00]; exact this))
    exact hbMne (hq.eq_of_map_eq (torus5_pow_eq_one hbmem) (one_pow p) h2)
  have hKM := perfectResidual_centralizer_bB σ hσσ hK4 hσζ hζ2
  obtain ⟨K₀, hd, hmod, hmap⟩ := layerCore_of_sl2_cover hp hp2 (IsPGroup.of_card h.A_card)
    h.A_elem h.L_le_centralizer hA ε q hε hq hxA hxL hx1 (torus5_pow_eq_one hbmem) hb.symm
    (fun t ht => torus5_pow_eq_one ht) hAT hK (by omega) (suBlockB σ hσσ) (suBlockB_injective σ hσσ)
    hKM (card_torus5_inf_rangeB hσσ hp.pos hfix hζex) (rootUB_le_range hσσ) (isPGroup_rootUB hσσ)
    (torus5_le_normalizer_rootUB hσσ)
    ⟨suBlockB σ hσσ (tr2 1), suBlockB_tr2_mem_rootUB hσσ 1, rhoB σ hσσ ζ,
      rhoB_mem_torus5 hσσ hζp hσζ, suBlockB_tr2_one_not_commute_rhoB hσσ hζ1⟩
  obtain ⟨t, htL, hr, hfix', hKF, hKz⟩ := exists_reflection_of_core hGA h hEA hcL hd (by omega) hmod
  refine ⟨t, htL, hr, hfix', hKF, ?_⟩
  rw [hKz, hd.K_eq, hmap]

theorem row5_main (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hEA : E = A)
    (hG : Sec12TwoGeneric p c L E) (hf3 : 3 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)
    (hfix : ∀ u : Kˣ, u ^ p = 1 → unitaryInvolution K 2 f (u : K) = u)
    {ζ' : (fixF (unitaryInvolution K 2 f))ˣ} (hζ' : IsPrimitiveRoot ζ' p)
    (ε : ↥L →* StatedProj (StatedSU 4 (2 ^ f) K)) (hε : IsCentralPQuot p ε)
    (hq : IsCentralPQuot p (suQ 4 hK))
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (torus5 (unitaryInvolution K 2 f) p).map (suQ 4 hK))
    (S : D8Ctx p K L (E ⊓ L))
    (hS : ∀ (d : D8Mod p K) (m : ↥(SU (unitaryInvolution K 2 f) 4)),
      (m : GL (Fin 4) K) = diagU (d8Vec 4 d) →
        ε (Subgroup.inclusion (inf_le_right : E ⊓ L ≤ L) (S.tor d)) = suQ 4 hK m) :
    (∀ s ∈ reflectionSet p E, s ∈ torusImage E L → KFAt p E f s ∨ KFAt p E (2 * f) s) ∧
      ∃ r₀ r₁ : MulAut E, r₀ ∈ reflectionSet p E ∧ r₀ ∈ torusImage E L ∧ r₁ ∈ reflectionSet p E ∧
        r₁ ∈ torusImage E L ∧ orderOf (r₀ * r₁) = 4 ∧ KFAt p E f r₀ ∧ KFAt p E (2 * f) r₁ ∧
        ((kZero p E r₀).subgroupOf L).map ε =
          (suBlock (unitaryInvolution K 2 f)).range.map (suQ 4 hK) ∧
        ((kZero p E r₁).subgroupOf L).map ε =
          (suBlockB (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK)).range.map
            (suQ 4 hK) ∧
        ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ s' ∈ reflectionSet p E,
          s' ∈ torusImage E L → orderOf (s * s') = 4 →
            ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G)),
              (s = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹ ∧
                s' = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹) ∨
              (s = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹ ∧
                s' = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹) := by
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have R : Sec12Three.Restr c L E (E ⊓ L) := h.restr_of_generic hG
  let σ : K ≃+* K := unitaryInvolution K 2 f
  have hσσ : ∀ x, σ (σ x) = x := unitaryInvolution_involutive hK
  have hFq : Nat.card (fixF σ) = 2 ^ f := card_fixedSubfield hK
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hζ : IsPrimitiveRoot (upU σ ζ') p := hζ'.map_of_injective (upU_injective σ)
  set ζ : Kˣ := upU σ ζ' with hζdef
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hσζ : σ (ζ : K) = ζ := σ_upU σ ζ'
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨ζ, hζ⟩
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
    calc A = E := hEA.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := hG.E_eq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  set z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p _).mpr hζp⟩ with hz
  have hz1 : z ≠ 1 := fun h1 => hζ1 (congrArg Subtype.val h1)
  have hz2 : z ^ 2 ≠ 1 := fun h1 => hz1 (eq_one_of_sq_eq_one_of_odd (hp.odd_of_ne_two hp2) h1)
  set d₀ : D8Mod p K := ((1 : rootsOfUnity p K), z) with hd₀
  set d₁ : D8Mod p K := (z, z) with hd₁
  set x₀ : G := ((S.tor d₀ : ↥(E ⊓ L)) : G) with hx₀
  set x₁ : G := ((S.tor d₁ : ↥(E ⊓ L)) : G) with hx₁
  have hx₀E : x₀ ∈ E := (S.tor d₀).2.1
  have hx₀L : x₀ ∈ L := (S.tor d₀).2.2
  have hx₁E : x₁ ∈ E := (S.tor d₁).2.1
  have hx₁L : x₁ ∈ L := (S.tor d₁).2.2
  have hm₀ : ((b5 σ ζ hσζ : ↥(SU σ 4)) : GL (Fin 4) K) = diagU (d8Vec 4 d₀) := by
    rw [d8Vec_four]
    rfl
  have hm₁ : ((bB σ ζ hσζ : ↥(SU σ 4)) : GL (Fin 4) K) = diagU (d8Vec 4 d₁) := by
    rw [d8Vec_four]
    rfl
  have hb₀ : suQ 4 hK (b5 σ ζ hσζ) = ε ⟨x₀, hx₀L⟩ := (hS d₀ _ hm₀).symm
  have hb₁ : suQ 4 hK (bB σ ζ hσζ) = ε ⟨x₁, hx₁L⟩ := (hS d₁ _ hm₁).symm
  obtain ⟨t₀, ht₀L, hr₀, hfix₀, hKF₀, hmap₀⟩ := row5_class0 hGA h hEA hcL hA hf3 σ hFq hζ' ε
    (suQ 4 hK) hε hq hAT (hEA ▸ hx₀E) hx₀L hb₀
  obtain ⟨t₁, ht₁L, hr₁, hfix₁, hKF₁, hmap₁⟩ := row5_class1 hGA h hEA hcL hA hf3 σ hσσ hK' hfix
    hζ ε (suQ 4 hK) hε hq hAT (hEA ▸ hx₁E) hx₁L hb₁
  have hζexp := hζex
  have hW₀ : weylE S R hp hp2 hζex ⟨t₀, ht₀L⟩ = DihedralGroup.sr 0 :=
    weylE_eq_of_fix S R hp hp2 hζex ht₀L hr₀ (d := d₀) (i₀ := 0) (hfix₀ hx₀E)
      (fun i hi => eq_zero_of_sr_fix_one hz1 hz2 hi)
  have hW₁ : weylE S R hp hp2 hζex ⟨t₁, ht₁L⟩ = DihedralGroup.sr 3 :=
    weylE_eq_of_fix S R hp hp2 hζex ht₁L hr₁ (d := d₁) (i₀ := 3) (hfix₁ hx₁E)
      (fun i hi => eq_three_of_sr_fix_same hz2 hi)
  have hrs₀ : t₀ ∈ reflectionSet p E := ⟨hr₀, L, hF13.inZeroStar, ht₀L⟩
  have hrs₁ : t₁ ∈ reflectionSet p E := ⟨hr₁, L, hF13.inZeroStar, ht₁L⟩
  have hv0 : (0 : ZMod 4).val = 0 := rfl
  have hv3 : (3 : ZMod 4).val = 3 := rfl
  have hall : ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → KFAt p E f s ∨ KFAt p E (2 * f) s := by
    intro s hs hsL
    obtain ⟨i, hi⟩ := (isAutReflection_weylE_iff S R hp hp2 hζex ⟨s, hsL⟩).1 hs.1
    have hpar : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
    rcases hpar with hpar | hpar
    · exact Or.inl (kfAt_of_parity S R hp hp2 hζex hW₀ hi (by rw [hv0]; omega) hKF₀)
    · exact Or.inr (kfAt_of_parity S R hp hp2 hζex hW₁ hi (by rw [hv3]; omega) hKF₁)
  refine ⟨hall, t₀, t₁, hrs₀, ht₀L, hrs₁, ht₁L, ?_, hKF₀, hKF₁, hmap₀, hmap₁, ?_⟩
  · have h1 : orderOf ((⟨t₀, ht₀L⟩ : ↥(torusImage E L)) * ⟨t₁, ht₁L⟩) = orderOf (t₀ * t₁) := by
      rw [← Subgroup.orderOf_coe]
      rfl
    rw [← h1, ← MulEquiv.orderOf_eq (weylE S R hp hp2 hζex), map_mul, hW₀, hW₁,
      DihedralGroup.sr_mul_sr, DihedralGroup.orderOf_r]
    decide
  · intro s hs hsL s' hs' hs'L hord
    obtain ⟨i, hi⟩ := (isAutReflection_weylE_iff S R hp hp2 hζex ⟨s, hsL⟩).1 hs.1
    obtain ⟨j, hj⟩ := (isAutReflection_weylE_iff S R hp hp2 hζex ⟨s', hs'L⟩).1 hs'.1
    have hne := parity_ne_of_pair S R hp hp2 hζex hi hj hord
    have hpar : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
    rcases hpar with hpar | hpar
    · obtain ⟨x, hxL, hxE, h1, h2⟩ := exists_conj_pair S R hp hp2 hζex hW₀ hW₁ hi hj
        (by rw [hv0]; omega) (by rw [hv3]; omega) hne
      exact ⟨x, hxL, hxE, Or.inl ⟨h1, h2⟩⟩
    · obtain ⟨x, hxL, hxE, h1, h2⟩ := exists_conj_pair S R hp hp2 hζex hW₁ hW₀ hi hj
        (by rw [hv3]; omega) (by rw [hv0]; omega) hne
      exact ⟨x, hxL, hxE, Or.inr ⟨h1, h2⟩⟩

theorem kf132Row5_frame (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hEA : E = A) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 2 f) :
    Subgroup.center L = ⊥ ∧
      (∀ s ∈ reflectionSet p E, s ∈ torusImage E L → KFAt p E f s ∨ KFAt p E (2 * f) s) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (hK : Nat.card K = (2 ^ f) ^ 2)
        (ε : ↥L →* StatedProj (StatedSU 4 (2 ^ f) K)), IsCentralPQuot p ε ∧
        ∃ r₀ r₁ : MulAut E, r₀ ∈ reflectionSet p E ∧ r₀ ∈ torusImage E L ∧ r₁ ∈ reflectionSet p E ∧
          r₁ ∈ torusImage E L ∧ orderOf (r₀ * r₁) = 4 ∧ KFAt p E f r₀ ∧ KFAt p E (2 * f) r₁ ∧
          ((kZero p E r₀).subgroupOf L).map ε =
            (suBlock (unitaryInvolution K 2 f)).range.map (suQ 4 hK) ∧
          ((kZero p E r₁).subgroupOf L).map ε =
            (suBlockB (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK)).range.map
              (suQ 4 hK) ∧
          ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ s' ∈ reflectionSet p E,
            s' ∈ torusImage E L → orderOf (s * s') = 4 →
              ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G)),
                (s = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹ ∧
                  s' = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹) ∨
                (s = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹ ∧
                  s' = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹) := by
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hf3 := three_le_of_dvd h5 hf1 hpq
  have hZL : Subgroup.center L = ⊥ :=
    psuFourEvenCenterTrivial_of_multipliers hGA L f (by omega) hF.isQuasisimple_L hmod
  have hG : Sec12TwoGeneric p c L E := sec12TwoGeneric_of_center_bot hF hZL
  have hcore : Table123Core p L (A ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h hG
  obtain ⟨K, hKf, hKfin, hchar, hK, ⟨ζ₀, hζ₀⟩, ε, hε, hFT₁, hFT₂⟩ :=
    exists_runitary_frame_of (n := 4) (Or.inl rfl) d8Comb_four hcore hf1 hpq hmod
  let σ : K ≃+* K := unitaryInvolution K 2 f
  have hFq : Nat.card (fixF σ) = 2 ^ f := card_fixedSubfield hK
  have hq : IsCentralPQuot p (suQ 4 hK) := isCentralPQuot_suQ hp hp2 (by norm_num) hpq hf1 hK
  have hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u := by
    intro u hu
    have h2 : u ^ (2 ^ f - 1) = 1 := by
      obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, hu, one_pow]
    show unitaryInvolution K 2 f (u : K) = u
    rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val]
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have : u ^ 2 ^ f = u := by
      calc u ^ 2 ^ f = u ^ (2 ^ f - 1) * u := by rw [← pow_succ, Nat.sub_add_cancel hq1]
        _ = u := by rw [h2, one_mul]
    rw [this]
  obtain ⟨ζ', hζ'⟩ : ∃ ζ : (fixF σ)ˣ, IsPrimitiveRoot ζ p := by
    have hdvd : p ∣ Nat.card (fixF σ)ˣ := by
      rw [Nat.card_units, hFq]
      exact hpq
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    refine ⟨z, ?_⟩
    have := IsPrimitiveRoot.orderOf z
    rwa [hz] at this
  have hAT : ((A ⊓ L).subgroupOf L).map ε = (torus5 σ p).map (suQ 4 hK) := by
    have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
    rw [hAL]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  obtain ⟨S, hS⟩ := rowSU_S (n := 4) (Or.inl rfl) d8Comb_four d8Comb2_four hp hp2 hK hf1 hpq
    ⟨ζ₀, hζ₀⟩ ε hε hcore.F_le hcore.F_exp hFT₁ hFT₂
  obtain ⟨hall, hrest⟩ := row5_main hGA h hF13 hEA hG hf3 hK hfix hζ' ε hε hq hAT S hS
  exact ⟨hZL, hall, K, hKf, hKfin, hchar, hK, ε, hε, hrest⟩

theorem kf132Row5_dichotomy (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hEA : E = A) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 2 f)
    {s s' : MulAut E} (hs : s ∈ reflectionSet p E) (hsL : s ∈ torusImage E L)
    (hs' : s' ∈ reflectionSet p E) (hs'L : s' ∈ torusImage E L) (hord : orderOf (s * s') = 4) :
    (KFAt p E f s ∧ KFAt p E (2 * f) s') ∨ (KFAt p E (2 * f) s ∧ KFAt p E f s') := by
  obtain ⟨-, -, K, -, -, -, hK, ε, hε, r₀, r₁, -, -, -, -, -, hK₀, hK₁, -, -, hpairs⟩ :=
    kf132Row5_frame hGA h hF hF13 hEA hf1 hpq hmod
  obtain ⟨x, hxL, hxE, hx⟩ := hpairs s hs hsL s' hs' hs'L hord
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1 ▸ hK₀.conj hxE, h2 ▸ hK₁.conj hxE⟩
  · exact Or.inr ⟨h1 ▸ hK₁.conj hxE, h2 ▸ hK₀.conj hxE⟩

end CFSG.RankThree.PartOne.KF132

namespace CFSG.RankThree.PartOne.S13K

theorem kf132At_row5 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132At 5 := by
  intro G _ _ p A c L E h hF hF13 hT hr4 hrow hrA hr9 t ht htL
  have hEA : E = A := hrA (by norm_num)
  obtain ⟨f, hf1, hpq, hmod⟩ := hrow
  obtain ⟨-, hall, -⟩ := CFSG.RankThree.PartOne.KF132.kf132Row5_frame hGA h hF hF13 hEA hf1 hpq hmod
  rcases hall t ht htL with hK | hK
  · exact ⟨f, f, ⟨hf1, hpq, hmod⟩, Or.inl rfl, hK⟩
  · exact ⟨f, 2 * f, ⟨hf1, hpq, hmod⟩, Or.inr rfl, hK⟩

theorem kf132Types_row5 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132Types 5 :=
  kf132Types_of_at (by norm_num) (by norm_num) (by norm_num) (kf132At_row5 hGA)

theorem kf132AtEx_row5 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132AtEx 5 := by
  intro G _ _ p A c L E h hF hF13 hT hr4 hrow hrA hr9
  have hEA : E = A := hrA (by norm_num)
  obtain ⟨f, hf1, hpq, hmod⟩ := hrow
  obtain ⟨-, -, K, -, -, -, hK, ε, hε, r₀, r₁, hr₀, hr₀L, -, -, -, hK₀, -⟩ :=
    CFSG.RankThree.PartOne.KF132.kf132Row5_frame hGA h hF hF13 hEA hf1 hpq hmod
  exact ⟨r₀, hr₀, hr₀L, f, f, ⟨hf1, hpq, hmod⟩, Or.inl rfl, hK₀⟩

end CFSG.RankThree.PartOne.S13K
