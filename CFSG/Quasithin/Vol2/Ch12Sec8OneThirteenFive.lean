module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneThirteenFiveStmt
public import CFSG.Quasithin.Vol2.Ch12Sec8OneSix
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4E9
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep7
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bFinal
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Rank
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch10SecDClB
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.A3Structure318Quot
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1542
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Quasithin.Background.ConjClosureSup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

private theorem card_closure_pair_of_three {M : Type*} [Group M] [Finite M] {x y : M}
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy1 : x ≠ y) (hxy2 : x ^ 2 ≠ y) :
    Nat.card (Subgroup.closure ({x, y} : Set M)) = 9 := by
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hA : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxord]
  have hB : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hyord]
  have hcommxy : Commute x y := hxy
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (hcommxy.zpow_zpow m n).eq
  have hyA : y ∉ Subgroup.zpowers x := by
    intro hyA
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hyA
    have hm' : x ^ (m % (orderOf x : ℤ)) = y := by
      rw [zpow_mod_orderOf]
      exact hm
    rw [hxord] at hm'
    have hm'' : x ^ (m % (3 : ℤ)) = y := by simpa using hm'
    have hr0 : 0 ≤ m % 3 := Int.emod_nonneg m (by norm_num)
    have hr3 : m % 3 < 3 := Int.emod_lt_of_pos m (by norm_num)
    rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h | h | h <;> rw [h] at hm''
    · rw [zpow_zero] at hm''
      exact hy1 hm''.symm
    · rw [zpow_one] at hm''
      exact hxy1 hm''
    · rw [zpow_two, ← pow_two] at hm''
      exact hxy2 hm''
  have hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    by_contra hz1
    have hdvd : orderOf z ∣ 3 := by
      rw [← hyord]
      exact orderOf_dvd_of_mem_zpowers hz.2
    have hoz : orderOf z = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hz1
      · exact h
    have hBz : Subgroup.zpowers z = Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz.2)
        (by rw [Nat.card_zpowers y, Nat.card_zpowers z, hoz, hyord])
    have hyB : y ∈ Subgroup.zpowers z := by
      rw [hBz]
      exact Subgroup.mem_zpowers y
    exact hyA ((Subgroup.zpowers_le.mpr hz.1) hyB)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers x) (Subgroup.zpowers y) hcomm).1
  rw [hdisj, Subgroup.card_bot, mul_one, hA, hB] at hcard
  have hclosure : Subgroup.closure ({x, y} : Set M) =
      Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).2 ?_
      rintro z (hx | hy)
      · rw [hx]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
      · rw [hy]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    · exact sup_le
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp : x ∈ ({x, y} : Set M))))
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp : y ∈ ({x, y} : Set M))))
  rw [hclosure]
  omega

namespace L128P

theorem false_of_two_e9_in_img_centralizerMod {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (hs : Setting1282One G T L V n V₁ V₂) (D : HatModelU (u128 V V₁)) {C : Subgroup G}
    (hC : C = centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂)
    (hCN : C ≤ Subgroup.normalizer (u128 V V₁ : Set G))
    {x y : D.V ≃ₗ[ZMod 2] D.V} (hxC : x ∈ D.img C) (hyC : y ∈ D.img C)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy1 : x ≠ y) (hxy2 : x ^ 2 ≠ y) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpr : 2 ≤ CFSG.Open.pRank 3 (D.img C) := by
    rw [← pRank_top_subtype (p := 3)]
    refine Rank8.two_le_pRank_three_of (x := ⟨x, hxC⟩) (y := ⟨y, hyC⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact Subtype.ext (by simpa using hx3)
    · exact Subtype.ext (by simpa using hy3)
    · exact Subtype.ext (by simpa using hxy)
    · exact fun h => hx1 (by simpa using congrArg Subtype.val h)
    · exact fun h => hy1 (by simpa using congrArg Subtype.val h)
    · exact fun h => hxy1 (by simpa using congrArg Subtype.val h)
    · exact fun h => hxy2 (by simpa using congrArg Subtype.val h)
  rw [L1294.img_eq_range D hCN, ← pRank_top_subtype (p := 3)] at hpr
  have h2 := two_le_pRank_of_surjective' Nat.prime_three (by norm_num)
    (D.ρ.comp (Subgroup.inclusion hCN)).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _) hpr
  rw [pRank_top_subtype (p := 3)] at h2
  have h3 : CFSG.Open.pRank 3 C ≤ 1 := by
    rw [hC]
    exact thirteen_eight h1222 h12213 hs
  omega

private theorem mem_img_centralizerMod_of_comm {G : Type} [Group G] [Finite G]
    {T L V : Subgroup G} {V₁ V₂ K₁ : Subgroup G} (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (hs : Setting1282One G T L V 4 V₁ V₂)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (D : HatModelU (u128 V V₁)) {a : G} (ha : a ∈ V₂) (haV₁ : a ∉ V₁)
    (hKC : K₁ ≤ Subgroup.centralizer (zU128 V V₁ : Set G))
    (hker : ∀ k : G, ∀ hk : k ∈ K₁,
      D.ρ ⟨k, C1294.K₁_le_normalizer_u128 (V := V) hK hk⟩ = 1 ↔ k ∈ pCoreOf 2 K₁)
    {γ : D.V ≃ₗ[ZMod 2] D.V} (hγ : γ ∈ D.img K₁) (hγ3 : γ ^ 3 = 1)
    (hγa : γ (D.π a) = D.π a) :
    γ ∈ D.img (centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂) := by
  classical
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨z, hz, hz1, -, -, -⟩ := L128P.exists_gens hV₁2 hV₂4
  have haU : a ∈ u128 V V₁ := le_conjClosure V _ (hs.v2.1 ha)
  obtain ⟨k, hkK, hkU, hkγ⟩ := (L128A.HatU.mem_img D).1 hγ
  set kU : Subgroup.normalizer (u128 V V₁ : Set G) :=
    ⟨k, C1294.K₁_le_normalizer_u128 (V := V) hK hkK⟩ with hkUdef
  have hργ : D.ρ kU = γ := by
    simpa [kU] using hkγ
  have hk3P : k ^ 3 ∈ pCoreOf 2 K₁ := by
    have h1 : D.ρ (kU ^ 3) = 1 := by rw [map_pow, hργ, hγ3]
    have h2 : D.ρ ⟨k ^ 3, C1294.K₁_le_normalizer_u128 (V := V) hK
        (K₁.pow_mem hkK 3)⟩ = 1 := by
      simpa [kU] using h1
    exact (hker (k ^ 3) (K₁.pow_mem hkK 3)).1 h2
  obtain ⟨e, he⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (G := G) 2 K₁
    ⟨k ^ 3, hk3P⟩
  have he' : (k ^ 3) ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  set k' : G := k ^ 2 ^ e with hk'def
  have hk'K : k' ∈ K₁ := K₁.pow_mem hkK _
  have hk'3 : k' ^ 3 = 1 := by
    rw [hk'def, ← pow_mul, mul_comm, pow_mul]
    exact he'
  have hρk' : D.ρ ⟨k', C1294.K₁_le_normalizer_u128 (V := V) hK hk'K⟩ = γ ^ 2 ^ e := by
    have hpow : (kU ^ 2 ^ e) =
        (⟨k', C1294.K₁_le_normalizer_u128 (V := V) hK hk'K⟩ :
          Subgroup.normalizer (u128 V V₁ : Set G)) := by
      apply Subtype.ext
      change k ^ 2 ^ e = k'
      rw [hk'def]
    have hmap : D.ρ (kU ^ 2 ^ e) = γ ^ 2 ^ e := by
      rw [map_pow, hργ]
    rwa [hpow] at hmap
  have hfix : D.ρ ⟨k', C1294.K₁_le_normalizer_u128 (V := V) hK hk'K⟩ (D.π a) = D.π a := by
    rw [hρk']
    have hpowfix : ∀ m : ℕ, (γ ^ m) (D.π a) = D.π a := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [pow_succ']
        change γ ((γ ^ m) (D.π a)) = D.π a
        rw [ih, hγa]
    exact hpowfix _
  set c : G := (k' * a * k'⁻¹)⁻¹ * a with hcdef
  have hconjU : k' * a * k'⁻¹ ∈ u128 V V₁ :=
    L128A.HatU.conj_mem (C1294.K₁_le_normalizer_u128 (V := V) hK hk'K) haU
  have hcZ : c ∈ zU128 V V₁ := by
    have hπeq : D.π (k' * a * k'⁻¹) = D.π a := by
      rw [← D.ρ_π ⟨k', C1294.K₁_le_normalizer_u128 (V := V) hK hk'K⟩ a haU]
      exact hfix
    exact (D.π_eq_iff _ hconjU a haU).1 hπeq
  have hka : k' * a * k'⁻¹ = a * c⁻¹ := by
    rw [hcdef]
    group
  have hcommc : Commute k' c := by
    exact (Subgroup.mem_centralizer_iff.mp (hKC hk'K) c hcZ).symm
  have hpow : ∀ m : ℕ, k' ^ m * a * (k' ^ m)⁻¹ = a * (c⁻¹) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hc' : Commute k' (c⁻¹) := hcommc.inv_right
      calc k' ^ (m + 1) * a * (k' ^ (m + 1))⁻¹
          = k' * (k' ^ m * a * (k' ^ m)⁻¹) * k'⁻¹ := by rw [pow_succ']; group
        _ = k' * (a * (c⁻¹) ^ m) * k'⁻¹ := by rw [ih]
        _ = (k' * a * k'⁻¹) * (c⁻¹) ^ m := by
            calc k' * (a * (c⁻¹) ^ m) * k'⁻¹
                = (k' * a) * ((c⁻¹) ^ m * k'⁻¹) := by group
              _ = (k' * a) * (k'⁻¹ * (c⁻¹) ^ m) := by
                  rw [← (hc'.inv_left.pow_right m)]
              _ = (k' * a * k'⁻¹) * (c⁻¹) ^ m := by group
        _ = (a * c⁻¹) * (c⁻¹) ^ m := by rw [hka]
        _ = a * (c⁻¹) ^ (m + 1) := by rw [pow_succ']; group
  have hc3 : c ^ 3 = 1 := by
    have h3 := hpow 3
    rw [hk'3, one_mul, inv_one, mul_one] at h3
    have hinv : (c⁻¹) ^ 3 = 1 := by
      have h4 : a * (c⁻¹) ^ 3 = a * 1 := by rw [← h3, mul_one]
      exact mul_left_cancel h4
    have : (c ^ 3)⁻¹ = 1 := by simpa [inv_pow] using hinv
    exact inv_eq_one.mp this
  have hc1 : c = 1 := by
    have hUT : u128 V V₁ ≤ T := (hs.almostSpecial h1222 h12213).G22_three.1
    have hcT : c ∈ T := hUT hcZ.1
    obtain ⟨j, hj⟩ := hs.hyp.hyp.sylow.1 ⟨c, hcT⟩
    have hc2 : c ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hdvd3 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    have hodd : Odd (orderOf c) := Odd.of_dvd_nat (by decide : Odd 3) hdvd3
    have hcop : Nat.Coprime (orderOf c) (2 ^ j) :=
      Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hc2))
  have hk'a : k' * a * k'⁻¹ = a := by
    rw [hka, hc1, inv_one, mul_one]
  have hk'z : k' * z * k'⁻¹ = z :=
    L1297.conj_eq_of_mem_normalizer hV₁2 hz (C1294.K₁_le_normalizer hK hk'K)
  have hk'C₂ : k' ∈ Subgroup.centralizer (V₂ : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    rcases L128P.eq_of_mem_four hs.le hV₁2 hV₂4 hz hz1 haV₁ ha hv with h | h | h | h <;>
      rw [h]
    · simp
    · calc z * k' = (k' * z * k'⁻¹) * k' := by rw [hk'z]
        _ = k' * z := by group
    · calc a * k' = (k' * a * k'⁻¹) * k' := by rw [hk'a]
        _ = k' * a := by group
    · calc (z * a) * k' = (k' * z * k'⁻¹) * (k' * a * k'⁻¹) * k' := by rw [hk'z, hk'a]
        _ = k' * (z * a) := by group
  have hk'C : k' ∈ centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂ := by
    refine ⟨C1294.K₁_le_normalizer hK hk'K, C1294.K₁_le_normalizer hK hk'K, fun v hv => ?_⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hk'C₂ v hv
    have h1 : k' * v * k'⁻¹ * v⁻¹ = 1 := by
      calc k' * v * k'⁻¹ * v⁻¹ = (v * k') * k'⁻¹ * v⁻¹ := by rw [← hcomm]
        _ = 1 := by group
    rw [h1]
    exact V₁.one_mem
  have hmemPow : γ ^ 2 ^ e ∈
      D.img (centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂) :=
    (L128A.HatU.mem_img D).2
      ⟨k', hk'C, C1294.K₁_le_normalizer_u128 (V := V) hK hk'K, hρk'⟩
  have hγeq : γ = (γ ^ 2 ^ e) ^ 2 ^ e := by
    rw [← pow_mul]
    have h4 : 2 ^ e * 2 ^ e = 4 ^ e := by rw [← mul_pow]; norm_num
    rw [h4]
    have hmod : ∀ n : ℕ, 4 ^ n % 3 = 1 := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih => simp [pow_succ, Nat.mul_mod, ih]
    rw [Rank8.pow_eq_pow_mod_three hγ3 (4 ^ e), hmod e, pow_one]
  rw [hγeq]
  exact (D.img _).pow_mem hmemPow (2 ^ e)

theorem commutator_zU_K₁_ne_bot {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    {V₁ V₂ K₁ : Subgroup G} (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (hs : Setting1282One G T L V 4 V₁ V₂)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hK4 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (D : HatModelU (u128 V V₁)) (h5 : G112Concl5 D.B (D.img (Subgroup.normalizer (V₁ : Set G))))
    (himg : (D.img K₁).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) ≤ 2)
    (hker : ∀ k : G, ∀ hk : k ∈ K₁,
      D.ρ ⟨k, C1294.K₁_le_normalizer_u128 (V := V) hK hk⟩ = 1 ↔ k ∈ pCoreOf 2 K₁) :
    ⁅zU128 V V₁, K₁⁆ ≠ ⊥ := by
  classical
  intro hbot
  have hKC : K₁ ≤ Subgroup.centralizer (zU128 V V₁ : Set G) := by
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    rw [Subgroup.le_centralizer_iff] at this
    exact this
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨-, -, -, a, haV₂, haV₁⟩ := L128P.exists_gens hV₁2 hV₂4
  have haV := hs.v2.1 haV₂
  have haU : a ∈ u128 V V₁ := le_conjClosure V _ haV
  have hπa : D.π a ≠ 0 := by
    intro h0
    rw [L128A.HatU.π_eq_zero_iff D haU] at h0
    have h1 : a ∈ V ⊓ zU128 V V₁ := ⟨haV, h0⟩
    rw [lemma12_8_8_three h1222 h12213 hs] at h1
    exact haV₁ h1
  obtain ⟨x, hxΓ, y, hyΓ, hx3, hy3, hxy, hx1, hy1, hxy1, hxy2, hxa, hya⟩ :=
    L1294E.exists_e9 (L128A.HatU.B_nondegenerate D) h5 hπa
  have hxK : x ∈ D.img K₁ := L1294E.mem_of_relIndex_le_two himg hxΓ hx3
  have hyK : y ∈ D.img K₁ := L1294E.mem_of_relIndex_le_two himg hyΓ hy3
  have hxC : x ∈ D.img (centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂) :=
    mem_img_centralizerMod_of_comm h1222 h12213 hs hK D haV₂ haV₁ hKC hker hxK hx3 hxa
  have hyC : y ∈ D.img (centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂) :=
    mem_img_centralizerMod_of_comm h1222 h12213 hs hK D haV₂ haV₁ hKC hker hyK hy3 hya
  have hCN : centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂ ≤
      Subgroup.normalizer (u128 V V₁ : Set G) := fun g hg =>
    le_normalizer_conjClosure V _ hg.1
  exact L128P.false_of_two_e9_in_img_centralizerMod h1222 h12213 hs D rfl hCN
    hxC hyC hx3 hy3 hxy hx1 hy1 hxy1 hxy2

theorem K₁_eq_commutator_zU_g {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    {V₁ V₂ K₁ : Subgroup G} {g : G} (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h12813 : Lemma12_8_13) (hs : Setting1282One G T L V 4 V₁ V₂)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hK4 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hgP : g ∈ p128 T L V) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G))
    (D : HatModelU (u128 V V₁)) (h5 : G112Concl5 D.B (D.img (Subgroup.normalizer (V₁ : Set G))))
    (himg : (D.img K₁).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) ≤ 2)
    (hker : ∀ k : G, ∀ hk : k ∈ K₁,
      D.ρ ⟨k, C1294.K₁_le_normalizer_u128 (V := V) hK hk⟩ = 1 ↔ k ∈ pCoreOf 2 K₁)
    (hcardK : Nat.card (D.img K₁) = 20160)
    (hKn : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hKcomm : ⁅zU128 V V₁, K₁⁆ ≠ ⊥)
    (hDgcomm : ¬ CFSG.conjugate (zU128 V V₁) g ≤
      centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁)) :
    K₁ = ⁅K₁, CFSG.conjugate (zU128 V V₁) g⁆ := by
  classical
  set H := Subgroup.normalizer (V₁ : Set G) with hHdef
  set Dg := CFSG.conjugate (zU128 V V₁) g with hDgdef
  set N := ⁅K₁, Dg⁆ with hNdef
  have hDgH : Dg ≤ H := fun d hd => (C1294.Dg_mem_normalizers h12813 hs hgP hgN hd).1
  have hDgU : Dg ≤ Subgroup.normalizer (u128 V V₁ : Set G) := fun d hd =>
    (C1294.Dg_mem_normalizers h12813 hs hgP hgN hd).2
  have hNle : N ≤ K₁ := by
    refine Subgroup.commutator_le.2 ?_
    intro k hk d hd
    rw [commutatorElement_def]
    have hd' : d * k⁻¹ * d⁻¹ ∈ K₁ :=
      (Subgroup.mem_normalizer_iff.mp (hKn (hDgH hd)) k⁻¹).mp (K₁.inv_mem hk)
    have e : k * d * k⁻¹ * d⁻¹ = k * (d * k⁻¹ * d⁻¹) := by group
    rw [e]
    exact K₁.mul_mem hk hd'
  have hNnormalSup : (N.subgroupOf (K₁ ⊔ Dg)).Normal := CFSG.commutator_normal_in_sup K₁ Dg
  have hSupN : K₁ ⊔ Dg ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hNle.trans le_sup_left)).1 hNnormalSup
  have hNnormal : (N.subgroupOf K₁).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_trans le_sup_left hSupN)
  set q := QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) with hqdef
  have hmapNormal : ((N.subgroupOf K₁).map q).Normal :=
    Subgroup.Normal.map hNnormal q (QuotientGroup.mk'_surjective _)
  haveI := C1294.isSimpleGroup_quot hK4
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf K₁).map q) with hbot | htop
  ·
    have hNP : N ≤ pCoreOf 2 K₁ := by
      intro n hn
      have hmem : q ⟨n, hNle hn⟩ = 1 := by
        have h1 : q ⟨n, hNle hn⟩ ∈ (N.subgroupOf K₁).map q :=
          Subgroup.mem_map_of_mem q (show (⟨n, hNle hn⟩ : ↥K₁) ∈ N.subgroupOf K₁ from hn)
        rwa [hbot, Subgroup.mem_bot] at h1
      have hnP : (⟨n, hNle hn⟩ : ↥K₁) ∈ CFSG.pCore 2 ↥K₁ :=
        (QuotientGroup.eq_one_iff _).1 hmem
      exact Subgroup.mem_map_of_mem K₁.subtype hnP
    obtain ⟨hdim, q5, hpolar5, -, ⟨S, hS3, hSq⟩, hΓO, -⟩ := h5
    have hnd : ∀ v, (∀ w, D.B v w = 0) → v = 0 := L128A.HatU.B_nondegenerate D
    obtain ⟨hcardO, hno2, -⟩ :=
      C1294.factF4_holds D.V q5 D.B hdim hpolar5 hnd ⟨S, hS3, hSq⟩
    have hKdotO : D.img K₁ ≤ orthogonalSubgroupOf q5 :=
      (L1294.img_mono D (C1294.K₁_le_normalizer hK)).trans hΓO
    have hrelO : (D.img K₁).relIndex (orthogonalSubgroupOf q5) = 2 := by
      have h := Subgroup.relIndex_mul_card (H := D.img K₁) (K := orthogonalSubgroupOf q5)
      rw [inf_eq_left.2 hKdotO, hcardK, hcardO] at h
      have h2 : (D.img K₁).relIndex (orthogonalSubgroupOf q5) * 20160 = 2 * 20160 := by
        simpa using h
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
    have hKdotNormal : ((D.img K₁).subgroupOf (orthogonalSubgroupOf q5)).Normal :=
      Subgroup.normal_of_index_eq_two hrelO
    have hO_NK : orthogonalSubgroupOf q5 ≤ Subgroup.normalizer (D.img K₁ : Set _) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKdotO).1 hKdotNormal
    set Cen : Subgroup (D.V ≃ₗ[ZMod 2] D.V) :=
      orthogonalSubgroupOf q5 ⊓ Subgroup.centralizer (D.img K₁ : Set _) with hCendef
    have hCenO : Cen ≤ orthogonalSubgroupOf q5 := inf_le_left
    have hCenNorm : ∀ γ ∈ orthogonalSubgroupOf q5, ∀ n ∈ Cen, γ * n * γ⁻¹ ∈ Cen := by
      intro γ hγ n hn
      refine ⟨(orthogonalSubgroupOf q5).mul_mem
        ((orthogonalSubgroupOf q5).mul_mem hγ hn.1) ((orthogonalSubgroupOf q5).inv_mem hγ), ?_⟩
      have hnC : n ∈ Subgroup.centralizer (D.img K₁ : Set _) := hn.2
      rw [Subgroup.mem_centralizer_iff] at hnC
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro k hk
      have hk' : γ⁻¹ * k * γ ∈ D.img K₁ :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hO_NK hγ)) k).1 hk
      have hcomm := hnC _ hk'
      calc k * (γ * n * γ⁻¹) = γ * ((γ⁻¹ * k * γ) * n) * γ⁻¹ := by group
        _ = γ * (n * (γ⁻¹ * k * γ)) * γ⁻¹ := by rw [hcomm]
        _ = (γ * n * γ⁻¹) * k := by group
    haveI hKdotSimple : IsSimpleGroup ↥(D.img K₁) := by
      let ρK : ↥K₁ →* (D.V ≃ₗ[ZMod 2] D.V) :=
        D.ρ.comp (Subgroup.inclusion (C1294.K₁_le_normalizer_u128 (V := V) hK))
      have hker_eq : ρK.ker = CFSG.pCore 2 ↥K₁ := by
        ext k
        rw [MonoidHom.mem_ker]
        change D.ρ ⟨k, C1294.K₁_le_normalizer_u128 (V := V) hK k.2⟩ = 1 ↔
          k ∈ CFSG.pCore 2 ↥K₁
        rw [hker k k.2]
        constructor
        · intro hk
          rw [show pCoreOf 2 K₁ = (CFSG.pCore 2 ↥K₁).map K₁.subtype from rfl] at hk
          obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.1 hk
          have hxeq : x = k := Subtype.ext hxk
          rwa [hxeq] at hx
        · intro hk
          exact Subgroup.mem_map_of_mem K₁.subtype hk
      have hrange : ρK.range = D.img K₁ := (L1294.img_eq_range D _).symm
      have e1 : (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* ρK.range :=
        (QuotientGroup.quotientMulEquivOfEq hker_eq.symm).trans
          (QuotientGroup.quotientKerEquivRange ρK)
      have e2 : ρK.range ≃* ↥(D.img K₁) := MulEquiv.subgroupCongr hrange
      let e : ↥(D.img K₁) ≃* (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := (e1.trans e2).symm
      exact @MulEquiv.isSimpleGroup ↥(D.img K₁) _ (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) _
        (C1294.isSimpleGroup_quot hK4) e
    have hcenter : Subgroup.center ↥(D.img K₁) = ⊥ := by
      have hna : ∃ a b : ↥(D.img K₁), a * b ≠ b * a := by
        by_contra hnab
        push Not at hnab
        letI : CommGroup ↥(D.img K₁) :=
          { toGroup := inferInstance, mul_comm := fun a b => hnab a b }
        have hp := IsSimpleGroup.prime_card (α := ↥(D.img K₁))
        rw [hcardK] at hp
        norm_num at hp
      exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).2
    have hCenK : Cen ⊓ D.img K₁ = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxCen, hxK⟩
      rw [Subgroup.mem_bot]
      have hxZ : (⟨x, hxK⟩ : ↥(D.img K₁)) ∈ Subgroup.center ↥(D.img K₁) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have hcomm := Subgroup.mem_centralizer_iff.mp hxCen.2 y y.2
        exact Subtype.ext hcomm
      rw [hcenter] at hxZ
      exact Subtype.ext_iff.mp (Subgroup.mem_bot.1 hxZ)
    have hCenCardLe : Nat.card Cen ≤ 2 := by
      have hdisj : Disjoint (D.img K₁) Cen := by
        rw [disjoint_iff_inf_le, inf_comm, hCenK]
      have hCenN : Cen ≤ Subgroup.normalizer (D.img K₁ : Set _) := hCenO.trans hO_NK
      have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (D.img K₁) Cen hCenN hdisj
      have hle : D.img K₁ ⊔ Cen ≤ orthogonalSubgroupOf q5 := sup_le hKdotO hCenO
      have hcardLe := Subgroup.card_le_of_le hle
      rw [hcard, hcardK, hcardO] at hcardLe
      omega
    have hCenBot : Cen = ⊥ := by
      have hne := hno2 Cen hCenO hCenNorm
      have hpos : 0 < Nat.card Cen := Nat.card_pos
      have hcard1 : Nat.card Cen = 1 := by omega
      exact (Subgroup.card_eq_one).1 hcard1
    have hρd1 : ∀ d ∈ Dg, ∀ hdU : d ∈ Subgroup.normalizer (u128 V V₁ : Set G),
        D.ρ ⟨d, hdU⟩ = 1 := by
      intro d hd hdU
      have hρdO : D.ρ ⟨d, hdU⟩ ∈ orthogonalSubgroupOf q5 :=
        hΓO (L128A.HatU.rho_mem_img D (hDgH hd) hdU)
      have hρdC : D.ρ ⟨d, hdU⟩ ∈ Subgroup.centralizer (D.img K₁ : Set _) := by
        rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
        intro γ hγ
        obtain ⟨k, hkK, hkU, rfl⟩ := (L128A.HatU.mem_img D).1 hγ
        have hkU' := C1294.K₁_le_normalizer_u128 (V := V) hK hkK
        have hmemN : k * d * k⁻¹ * d⁻¹ ∈ N := Subgroup.commutator_mem_commutator hkK hd
        have hmemP : k * d * k⁻¹ * d⁻¹ ∈ pCoreOf 2 K₁ := hNP hmemN
        have hρ1 : D.ρ ⟨k * d * k⁻¹ * d⁻¹,
            C1294.K₁_le_normalizer_u128 (V := V) hK (hNle hmemN)⟩ = 1 :=
          (hker (k * d * k⁻¹ * d⁻¹) (hNle hmemN)).2 hmemP
        have hsub : (⟨k * d * k⁻¹ * d⁻¹,
              C1294.K₁_le_normalizer_u128 (V := V) hK (hNle hmemN)⟩ :
              Subgroup.normalizer (u128 V V₁ : Set G)) =
            (⟨k, hkU'⟩ : Subgroup.normalizer (u128 V V₁ : Set G)) *
              (⟨d, hdU⟩ : Subgroup.normalizer (u128 V V₁ : Set G)) *
              (⟨k, hkU'⟩ : Subgroup.normalizer (u128 V V₁ : Set G))⁻¹ *
              (⟨d, hdU⟩ : Subgroup.normalizer (u128 V V₁ : Set G))⁻¹ :=
          Subtype.ext (by simp [commutatorElement_def])
        rw [hsub, map_mul, map_mul, map_mul, map_inv, map_inv] at hρ1
        rw [commutatorElement_def]
        exact hρ1
      have hρdCen : D.ρ ⟨d, hdU⟩ ∈ Cen := ⟨hρdO, hρdC⟩
      rw [hCenBot, Subgroup.mem_bot] at hρdCen
      exact hρdCen
    exfalso
    exact hDgcomm fun d hd =>
      (mem_centralizerMod).2
        ⟨hDgH hd, CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (u128 V V₁) (hDgU hd),
          fun u hu => (L128A.HatU.rho_eq_one_iff D ⟨d, hDgU hd⟩).1
            (hρd1 d hd (hDgU hd)) u hu⟩
  ·
    have hKnN : K₁ ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).1 hNnormal
    have hpow : ∀ x ∈ K₁, ∃ k : ℕ, x ^ 2 ^ k ∈ N := by
      intro x hx
      refine L128P.exists_two_pow_mem_of_le_sup (N := N) (P := pCoreOf 2 K₁) (X := K₁)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₁).trans hKnN) ?_ hx
      intro y hy
      have hyq : q ⟨y, hy⟩ ∈ (N.subgroupOf K₁).map q := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnq⟩ := Subgroup.mem_map.1 hyq
      have hnp : ((n : ↥K₁)⁻¹ * ⟨y, hy⟩) ∈ CFSG.pCore 2 ↥K₁ := by
        have h1 : q ((n : ↥K₁)⁻¹ * ⟨y, hy⟩) = 1 := by
          rw [map_mul, map_inv, hnq]
          simp
        exact (QuotientGroup.eq_one_iff _).1 h1
      have hnp' : ((n : G)⁻¹ * y) ∈ pCoreOf 2 K₁ :=
        Subgroup.mem_map_of_mem K₁.subtype hnp
      have hyeq : y = (n : G) * ((n : G)⁻¹ * y) := by group
      rw [hyeq]
      exact Subgroup.mul_mem_sup hn hnp'
    have hNK : N = K₁ := CFSG.Quasithin.C2Nine.eq_of_perfect_of_pow_mem hK.2.1 hNle hNnormal hpow
    exact hNK.symm

theorem zD_ne {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    {V₁ V₂ K₁ : Subgroup G} {g : G} (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) (hs : Setting1282One G T L V 4 V₁ V₂)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hgP : g ∈ p128 T L V) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G))
    (hKcomm : ⁅zU128 V V₁, K₁⁆ ≠ ⊥)
    (hcommK : K₁ = ⁅K₁, CFSG.conjugate (zU128 V V₁) g⁆) :
    quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁) ≠ ⊥ := by
  classical
  set H := Subgroup.normalizer (V₁ : Set G) with hHdef
  set Dg := CFSG.conjugate (zU128 V V₁) g with hDgdef
  have hDgH : Dg ≤ H := fun d hd => (C1294.Dg_mem_normalizers h12813 hs hgP hgN hd).1
  have hDgU : Dg ≤ Subgroup.normalizer (u128 V V₁ : Set G) := fun d hd =>
    (C1294.Dg_mem_normalizers h12813 hs hgP hgN hd).2
  have hDgZ : Dg ≤ Subgroup.normalizer (zU128 V V₁ : Set G) := hDgU.trans
    (CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (u128 V V₁))
  have hcommDg : ⁅zU128 V V₁, Dg⁆ ≠ ⊥ := by
    intro hbot
    have hDgC : Dg ≤ Subgroup.centralizer (zU128 V V₁ : Set G) := by
      have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      rw [Subgroup.le_centralizer_iff] at h1
      exact h1
    have hK₁C : K₁ ≤ Subgroup.centralizer (zU128 V V₁ : Set G) := by
      have hK₁N : K₁ ≤ Subgroup.normalizer
          (Subgroup.centralizer (zU128 V V₁ : Set G) : Set G) :=
        (C1294.K₁_le_normalizer_u128 (V := V) hK).trans
          ((CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (u128 V V₁)).trans
            (normalizer_le_normalizer_centralizer'' (zU128 V V₁)))
      have hNle := Subgroup.commutator_le.2 (fun k hk d hd => by
        have hdC : d ∈ Subgroup.centralizer (zU128 V V₁ : Set G) := hDgC hd
        have hkC : k * d * k⁻¹ ∈ Subgroup.centralizer (zU128 V V₁ : Set G) :=
          (Subgroup.mem_normalizer_iff.mp (hK₁N hk) d).1 hdC
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ hkC ((Subgroup.centralizer (zU128 V V₁ : Set G)).inv_mem hdC))
      rw [← hcommK] at hNle
      exact hNle
    exact hKcomm ((Subgroup.commutator_eq_bot_iff_le_centralizer).2
      ((Subgroup.le_centralizer_iff).mp hK₁C))
  have hex : ∃ z ∈ zU128 V V₁, ∃ d ∈ Dg, z * d * z⁻¹ * d⁻¹ ≠ 1 := by
    by_contra h
    push Not at h
    apply hcommDg
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz d hd
    have h1 : ⁅z, d⁆ = 1 := by
      rw [commutatorElement_def]
      exact h z hz d hd
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  obtain ⟨z, hz, d, hd, hcne⟩ := hex
  have hgP' : g⁻¹ ∈ p128 T L V := (p128 T L V).inv_mem hgP
  have hgN' : g⁻¹ ∉ Subgroup.normalizer (V₁ : Set G) := fun h =>
    hgN (by simpa using (Subgroup.normalizer (V₁ : Set G)).inv_mem h)
  have hzgN : g * z * g⁻¹ ∈ Subgroup.normalizer (u128 V V₁ : Set G) := by
    have hd' : g * z * g⁻¹ ∈ CFSG.conjugate (zU128 V V₁) g⁻¹ := by
      rw [C1294.mem_conj']
      simpa [mul_assoc] using hz
    exact (C1294.Dg_mem_normalizers h12813 hs hgP' hgN' hd').2
  have hzgZ : g * z * g⁻¹ ∈ Subgroup.normalizer (zU128 V V₁ : Set G) :=
    (CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (u128 V V₁)) hzgN
  have hzDg : z ∈ Subgroup.normalizer (Dg : Set G) :=
    CFSG.Quasithin.mem_normalizer_of_conj_mem_of_finite fun d' hd' => by
      rw [C1294.mem_conj']
      have hd'Z : g * d' * g⁻¹ ∈ zU128 V V₁ := C1294.mem_conj'.1 hd'
      have h1 := (Subgroup.mem_normalizer_iff.mp hzgZ (g * d' * g⁻¹)).1 hd'Z
      convert h1 using 1 <;> group
  set c : G := z * d * z⁻¹ * d⁻¹ with hcdef
  have hcZ : c ∈ zU128 V V₁ := by
    change z * d * z⁻¹ * d⁻¹ ∈ zU128 V V₁
    have hdz : d * z⁻¹ * d⁻¹ ∈ zU128 V V₁ := by
      have h := (zU128 V V₁).inv_mem ((Subgroup.mem_normalizer_iff.mp (hDgZ hd) z).1 hz)
      simpa [mul_inv_rev, mul_assoc] using h
    have e : z * d * z⁻¹ * d⁻¹ = z * (d * z⁻¹ * d⁻¹) := by group
    rw [e]
    exact (zU128 V V₁).mul_mem hz hdz
  have hcDg : c ∈ Dg := by
    change z * d * z⁻¹ * d⁻¹ ∈ Dg
    have h1 : z * d * z⁻¹ ∈ Dg := (Subgroup.mem_normalizer_iff.mp hzDg d).1 hd
    have e : z * d * z⁻¹ * d⁻¹ = (z * d * z⁻¹) * d⁻¹ := by group
    rw [e]
    exact Dg.mul_mem h1 (Dg.inv_mem hd)
  have hZI2eq : zU128 V V₁ ⊓ Dg = centerOf (i128 T L V V₁) :=
    (h12810 G T L V 4 V₁ V₂ hs g hgP hgN).2.1
  have hZI2ne : centerOf (i128 T L V V₁) ≠ ⊥ := by
    intro hbot
    apply hcne
    have hmem : c ∈ zU128 V V₁ ⊓ Dg := ⟨hcZ, hcDg⟩
    rw [hZI2eq, hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hZI2notle : ¬ centerOf (i128 T L V V₁) ≤ V₁ := by
    intro hle
    have hcardZ : Nat.card (centerOf (i128 T L V V₁)) = 2 := by
      have hle2 : Nat.card (centerOf (i128 T L V V₁)) ≤ 2 := by
        calc Nat.card (centerOf (i128 T L V V₁)) ≤ Nat.card V₁ := Subgroup.card_le_of_le hle
          _ = 2 := hV₁2
      have hpos : 1 < Nat.card (centerOf (i128 T L V V₁)) :=
        (Subgroup.one_lt_card_iff_ne_bot _).2 hZI2ne
      omega
    have hEq : centerOf (i128 T L V V₁) = V₁ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardZ, hV₁2])
    have hgNi : g ∈ Subgroup.normalizer (i128 T L V V₁ : Set G) :=
      le_normalizer_conjClosure (u128 V V₁) (p128 T L V) hgP
    have hgNz : g ∈ Subgroup.normalizer (centerOf (i128 T L V V₁) : Set G) :=
      (CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (i128 T L V V₁)) hgNi
    rw [hEq] at hgNz
    exact hgN hgNz
  obtain ⟨x, hxZ, hxV₁⟩ := Set.not_subset.1 hZI2notle
  have hxZinf : x ∈ zU128 V V₁ ⊓ Dg := by
    rw [← hZI2eq] at hxZ
    exact hxZ
  have hxDg : x ∈ Dg := (Subgroup.mem_inf.1 hxZinf).2
  have hxZ_U : x ∈ zU128 V V₁ := (Subgroup.mem_inf.1 hxZinf).1
  have hA := (h12810 G T L V 4 V₁ V₂ hs g hgP hgN).1
  have hlt : V₁ < zU128 V V₁ ⊓ CFSG.conjugate (u128 V V₁) g := by
    rw [hA]
    refine lt_of_le_of_ne le_sup_right ?_
    intro hEq
    apply hxV₁
    have hxSup : x ∈ (zU128 V V₁ ⊓ Dg) ⊔ V₁ := Subgroup.mem_sup_left ⟨hxZ_U, hxDg⟩
    rw [← hEq] at hxSup
    exact hxSup
  exact (h12810 G T L V 4 V₁ V₂ hs g hgP hgN).2.2.1 hlt

theorem commutator_zD_K₁_ne_bot {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    {V₁ V₂ K₁ : Subgroup G} (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h1228 : Stmt12_2_8) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hs : Setting1282One G T L V 4 V₁ V₂)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hK4 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hLK : lOne L V₁ ≤ K₁)
    (hKn : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hZD : quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁) ≠ ⊥) :
    ⁅quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁), K₁⁆ ≠ ⊥ := by
  classical
  intro hbot
  set H := Subgroup.normalizer (V₁ : Set G) with hHdef
  set ZD := quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁) with hZDdef
  have hZDT : ZD ≤ T :=
    (inf_le_left : ZD ≤ quasithinOmegaOneCenter T).trans
      ((CFSG.Quasithin.B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_left)
  have hZD2 : IsPGroup 2 ZD := hs.hyp.hyp.sylow.1.to_le hZDT
  have hZC : K₁ ≤ Subgroup.centralizer (ZD : Set G) := by
    exact (Subgroup.le_centralizer_iff).mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot)
  have hTC : T ≤ Subgroup.centralizer (ZD : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzT : z ∈ Subgroup.centralizer (T : Set G) :=
      (CFSG.Quasithin.B2F.omegaOneCenter_le_inf_centralizer T hz.1).2
    exact (Subgroup.mem_centralizer_iff.mp hzT t ht).symm
  have hL₁C : lOne L V₁ ≤ Subgroup.centralizer (ZD : Set G) := hLK.trans hZC
  have hI2C : i128 T L V V₁ ≤ Subgroup.centralizer (ZD : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzI : z ∈ Subgroup.centralizer (i128 T L V V₁ : Set G) := hz.2.2
    exact (Subgroup.mem_centralizer_iff.mp hzI x hx).symm
  have hO2PC : oTwoUpper (p128 T L V) ≤ Subgroup.centralizer (ZD : Set G) := by
    refine (le_trans ?_ hI2C)
    rw [L128P.i128_eq_sup h1222 h12213 hs]
    exact le_sup_left
  have hXC : (oTwoUpper (p128 T L V) ⊔ lOne L V₁ ⊔ T : Subgroup G) ≤
      Subgroup.centralizer (ZD : Set G) := by
    refine sup_le (sup_le hO2PC hL₁C) hTC
  have hPle : p128 T L V ≤ L ⊔ T := inf_le_left
  have hXLT : (oTwoUpper (p128 T L V) ⊔ lOne L V₁ ⊔ T : Subgroup G) ≤ L ⊔ T := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact ((oTwoUpper_le (p128 T L V)).trans hPle)
    · exact (oTwoUpper_le (L ⊓ H)).trans (inf_le_left.trans (le_sup_left : L ≤ L ⊔ T))
    · exact le_sup_right
  obtain ⟨k, hk, hkN⟩ := L128P.exists_not_mem_normalizer h1222 hs
  have hXN : ¬ (oTwoUpper (p128 T L V) ⊔ lOne L V₁ ⊔ T : Subgroup G) ≤
      Subgroup.normalizer (V₁ : Set G) := fun hle =>
    hkN (hle (Subgroup.mem_sup_left (Subgroup.mem_sup_left hk)))
  have hL₁X : lOne L V₁ ⊔ T ≤ (oTwoUpper (p128 T L V) ⊔ lOne L V₁ ⊔ T : Subgroup G) :=
    sup_le_sup_right le_sup_right T
  have hLTX : L ⊔ T ≤ (oTwoUpper (p128 T L V) ⊔ lOne L V₁ ⊔ T : Subgroup G) :=
    L1297.sup_le_of_not_le_normalizer h1222 hs.hyp hs.v1
      (X := oTwoUpper (p128 T L V) ⊔ lOne L V₁ ⊔ T) hL₁X hXLT hXN
  have hLTC : L ⊔ T ≤ Subgroup.centralizer (ZD : Set G) := hLTX.trans hXC
  have hNJ : Subgroup.normalizer (ZD : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    L1297.normalizer_le_of_sup_le h37 h38 h39 hs.hyp.hyp hZD hZD2
      (hLTC.trans (Subgroup.centralizer_le_normalizer _))
  have hK₁L : K₁ ≤ Subgroup.normalizer (L : Set G) :=
    (hZC.trans (Subgroup.centralizer_le_normalizer _)).trans hNJ
  have h3dvd : 3 ∣ Nat.card ↥K₁ := by
    have h := Subgroup.card_mul_index (CFSG.pCore 2 ↥K₁)
    rw [C1294.index_pCore_eq hK4] at h
    rw [← h]
    exact Dvd.dvd.mul_left (by norm_num) _
  have hgen := C1294.closure_three_eq_top (CFSG.pCore 2 ↥K₁) CFSG.pCore_isPGroup
    (C1294.isSimpleGroup_quot hK4) (C1294.perfect_top_of_cComp hK) h3dvd
  have hK₁H : K₁ ≤ H := le_of_mem_cComp (show K₁ ∈ cComp H from hK)
  have hK₁L₁ : K₁ ≤ lOne L V₁ := by
    have hle : (⊤ : Subgroup ↥K₁) ≤ (lOne L V₁).subgroupOf K₁ := by
      rw [← hgen]
      refine (Subgroup.closure_le _).2 ?_
      rintro x hx
      obtain ⟨j, hxord⟩ := hx
      have hxpow' : x ^ 3 ^ j = 1 := by
        have := pow_orderOf_eq_one x
        rwa [hxord] at this
      have hxpow : (x : G) ^ 3 ^ j = 1 := by
        simpa using congrArg (fun y : ↥K₁ => (y : G)) hxpow'
      have hxL : (x : G) ∈ L :=
        L128P.mem_of_pow_three_pow_eq_one h1228 hs.hyp (by norm_num) (hK₁L x.2) hxpow
      have hxH : (x : G) ∈ H := hK₁H x.2
      have hodd : Odd (orderOf (x : G)) := by
        rw [Subgroup.orderOf_coe, hxord]
        exact Odd.pow (by decide)
      exact mem_oTwoUpper_of_odd ⟨hxL, hxH⟩ hodd
    intro k hk
    have := hle (Subgroup.mem_top (⟨k, hk⟩ : ↥K₁))
    simpa [Subgroup.mem_subgroupOf] using this
  have hKL₁ : K₁ = lOne L V₁ := le_antisymm hK₁L₁ hLK
  have hKidx : (CFSG.pCore 2 ↥K₁).index = 20160 := C1294.index_pCore_eq hK4
  have hLidx : (CFSG.pCore 2 ↥(lOne L V₁)).index = 168 := by
    obtain ⟨e⟩ := lOne_quotient_mulEquiv h1222 hs.hyp (by norm_num : 4 ≠ 3) hs.v1
    rw [Subgroup.index, Nat.card_congr e.toEquiv, Matrix.card_SL_field, ZMod.card]
    norm_num [Fin.prod_univ_succ]
  rw [hKL₁] at hKidx
  omega

theorem normalizer_le_normalizer_of_cComponent {G : Type} [Group G] [Finite G]
    {T L V : Subgroup G} {V₁ V₂ K₁ : Subgroup G} (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hs : Setting1282One G T L V 4 V₁ V₂)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hK4 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) :
    Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G) := by
  classical
  set H := Subgroup.normalizer (V₁ : Set G) with hHdef
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₁ne : V₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hV₁2
    norm_num at hV₁2
  have hV₁2p : IsPGroup 2 V₁ := IsPGroup.of_card (n := 1) (by simpa using hs.v1.2.1)
  have hHcore : pCoreOf 2 H ≠ ⊥ := by
    intro hb
    have hle := CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 V₁ hV₁2p
    rw [hb, le_bot_iff] at hle
    exact hV₁ne hle
  have hInH : InH T H := ⟨hs.v1.2.2, hHcore⟩
  have hSQ : SQTKGroup ↥H :=
    CFSG.Quasithin.sqtkGroup_of_pCoreOf_ne_bot hs.hyp.hyp.qtke hs.hyp.hyp.simple
      hs.hyp.hyp.nonabelian hHcore
  have hK₁H : K₁ ≤ H := le_of_mem_cComp (show K₁ ∈ cComp H from hK)
  have hrank : 1 < CFSG.Open.pRank 3 (K₁.subgroupOf H) := by
    rw [CFSG.Quasithin.Vol2.Ch11.SecA.pRank_subgroupOf_eq hK₁H Nat.prime_three (by norm_num)]
    obtain ⟨e⟩ := hK4
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    exact lt_of_lt_of_le (by norm_num : 1 < 2) Rank8.two_le_pRank_sl_four
  have hL : K₁.subgroupOf H ∈ cComp (⊤ : Subgroup ↥H) :=
    CFSG.Quasithin.subgroupOf_mem_cComp (show K₁ ∈ cComp H from hK)
  have hNormal : (K₁.subgroupOf H).Normal :=
    CFSG.Quasithin.A318.normal_of_pRank_gt_one hSQ
      (h38 (↥H ⧸ CFSG.pCore 2 ↥H) (SQTKHyp.of_sqtkGroup ↥H hSQ)) hL Nat.prime_three
      (by norm_num) hrank
  intro h hh
  refine CFSG.Quasithin.mem_normalizer_of_conj_mem_of_finite fun k hk => ?_
  have hmem := Subgroup.mem_subgroupOf.1
    (hNormal.conj_mem (⟨k, hK₁H hk⟩ : ↥H) hk (⟨h, hh⟩ : ↥H))
  simpa using hmem

theorem lt_zU_of_e9 {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (hs : Setting1282One G T L V n V₁ V₂) (D : HatModelU (u128 V V₁)) {a : G}
    (ha : a ∈ V₂) (haV₁ : a ∉ V₁) {x y : D.V ≃ₗ[ZMod 2] D.V}
    (hxΓ : x ∈ D.img (Subgroup.normalizer (V₁ : Set G)))
    (hyΓ : y ∈ D.img (Subgroup.normalizer (V₁ : Set G)))
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy1 : x ≠ y) (hxy2 : x ^ 2 ≠ y) (hxa : x (D.π a) = D.π a)
    (hya : y (D.π a) = D.π a) : V₁ < zU128 V V₁ := by
  set Y : Subgroup (D.V ≃ₗ[ZMod 2] D.V) := Subgroup.closure ({x, y} : Set _) with hYdef
  have hYΓ : Y ≤ D.img (Subgroup.normalizer (V₁ : Set G)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro z (hx | hy)
    · rwa [hx]
    · rwa [hy]
  have hYv : ∀ z ∈ Y, z (D.π a) = D.π a := by
    have hxStab : x ∈ MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a) :=
      MulAction.mem_stabilizer_iff.2 hxa
    have hyStab : y ∈ MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a) :=
      MulAction.mem_stabilizer_iff.2 hya
    have hYle : Y ≤ MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro z (hx | hy)
      · rwa [hx]
      · rwa [hy]
    intro z hz
    exact MulAction.mem_stabilizer_iff.1 (hYle hz)
  have hY3 : IsElemAbelian 3 Y := by
    refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
    · intro a₁ ha₁ a₂ ha₂
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha₁ ha₂
      rcases ha₁ with rfl | rfl <;> rcases ha₂ with rfl | rfl <;> simp [hxy]
    · intro a₁ ha₁
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha₁
      rcases ha₁ with rfl | rfl
      · exact hx3
      · exact hy3
  have hY9 : Nat.card Y = 9 := card_closure_pair_of_three hx3 hy3 hxy hx1 hy1 hxy1 hxy2
  exact L128P.lt_zU_of_elemAbelian h1222 h12213 hs D ha haV₁ hYΓ hYv hY3 hY9

end L128P

theorem lemma12_8_13_five_of (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h1228 : Stmt12_2_8)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h12810 : Lemma12_8_10)
    (h12813 : Lemma12_8_13) : Lemma12_8_13_five := by
  intro G _ _ T L V V₁ V₂ K₁ hs hLK hK hK4 g hgP hgN D h5 himg
  classical
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨-, -, -, a, haV₂, haV₁⟩ := L128P.exists_gens hV₁2 hV₂4
  have haV := hs.v2.1 haV₂
  have haU : a ∈ u128 V V₁ := le_conjClosure V _ haV
  have hπa : D.π a ≠ 0 := by
    intro h0
    rw [L128A.HatU.π_eq_zero_iff D haU] at h0
    have h1 : a ∈ V ⊓ zU128 V V₁ := ⟨haV, h0⟩
    rw [lemma12_8_8_three h1222 h12213 hs] at h1
    exact haV₁ h1
  obtain ⟨x, hxΓ, y, hyΓ, hx3, hy3, hxy, hx1, hy1, hxy1, hxy2, hxa, hya⟩ :=
    L1294E.exists_e9 (L128A.HatU.B_nondegenerate D) h5 hπa
  have hxK : x ∈ D.img K₁ := L1294E.mem_of_relIndex_le_two himg hxΓ hx3
  have hyK : y ∈ D.img K₁ := L1294E.mem_of_relIndex_le_two himg hyΓ hy3
  have hZlt : V₁ < zU128 V V₁ :=
    L128P.lt_zU_of_e9 h1222 h12213 hs D haV₂ haV₁ hxΓ hyΓ hx3 hy3 hxy hx1 hy1 hxy1 hxy2
      hxa hya
  have hKn : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G) :=
    L128P.normalizer_le_normalizer_of_cComponent h1222 h12213 h37 h38 h39 hs hK hK4
  obtain ⟨q, hpolar, hrel, hcardK, hker⟩ :=
    C1294.step2_main hK hK4 D h5 himg C1294.factF4_holds
  have hKcomm : ⁅zU128 V V₁, K₁⁆ ≠ ⊥ :=
    L128P.commutator_zU_K₁_ne_bot h1222 h12213 hs hK hK4 D h5 himg hker
  have hDgcomm : ¬ CFSG.conjugate (zU128 V V₁) g ≤
      centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) :=
    (h12813 G T L V 4 V₁ V₂ hs g hgP hgN).2.2.1 hZlt
  have hcommK : K₁ = ⁅K₁, CFSG.conjugate (zU128 V V₁) g⁆ :=
    L128P.K₁_eq_commutator_zU_g h1222 h12213 h12813 hs hK hK4 hgP hgN D h5 himg hker hcardK hKn
      hKcomm hDgcomm
  have hZD : quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁) ≠ ⊥ :=
    L128P.zD_ne h1222 h12213 h12810 h12813 hs hK hgP hgN hKcomm hcommK
  have hZDcomm : ⁅quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁), K₁⁆ ≠ ⊥ :=
    L128P.commutator_zD_K₁_ne_bot h1222 h12213 h1228 h37 h38 h39 hs hK hK4 hLK hKn hZD
  have hVDle : conjClosure (quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁)) K₁ ≤
      zU128 V V₁ := by
    refine conjClosure_le fun k hk z hz => ?_
    have hkZ : k ∈ Subgroup.normalizer (zU128 V V₁ : Set G) :=
      (CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (u128 V V₁))
        (C1294.K₁_le_normalizer_u128 (V := V) hK hk)
    have hzZ : z ∈ zU128 V V₁ :=
      C1294.centerOf_I2_le_zU h12810 hs hgP hgN hz.2
    exact (Subgroup.mem_normalizer_iff.mp hkZ z).1 hzZ
  have hred : CFSG.Quasithin.IsTwoReducedIn (K₁ ⊔ T)
      (conjClosure (quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁)) K₁) := by
    set ZD := quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁) with hZDdef
    have hT' : QuasithinUnique.IsSylowTwoOf T (K₁ ⊔ T) :=
      isSylowTwoOf_of_quasithinIsSylowTwo hs.hyp.hyp.sylow le_sup_right
    have hZT : ZD ≤ quasithinOmegaOneCenter T := inf_le_left
    have hZDT' : ZD ≤ T :=
      (inf_le_left : ZD ≤ quasithinOmegaOneCenter T).trans
        ((CFSG.Quasithin.B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_left)
    have hUT : u128 V V₁ ≤ T := (hs.almostSpecial h1222 h12213).G22_three.1
    have hZT' : T ≤ Subgroup.normalizer (V₁ : Set G) := hs.v1.2.2
    have hK₁H : K₁ ≤ Subgroup.normalizer (V₁ : Set G) := C1294.K₁_le_normalizer hK
    have hKT_U : K₁ ⊔ T ≤ Subgroup.normalizer (u128 V V₁ : Set G) :=
      sup_le (C1294.K₁_le_normalizer_u128 (V := V) hK)
        (hZT'.trans (le_normalizer_conjClosure V (Subgroup.normalizer (V₁ : Set G))))
    have hNnorm : K₁ ⊔ T ≤ Subgroup.normalizer
        ((u128 V V₁ ⊓ (K₁ ⊔ T) : Subgroup G) : Set G) := fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hKT_U hx, Subgroup.le_normalizer hx⟩
    have hZDU : ZD ≤ u128 V V₁ := fun z hz =>
      (C1294.centerOf_I2_le_zU h12810 hs hgP hgN hz.2).1
    have hZN : ZD ≤ u128 V V₁ ⊓ (K₁ ⊔ T) := by
      intro z hz
      exact ⟨hZDU hz, hZDT'.trans (le_sup_right : T ≤ K₁ ⊔ T) hz⟩
    have hNleT : (u128 V V₁ ⊓ (K₁ ⊔ T) : Subgroup G) ≤ T :=
      (inf_le_left : (u128 V V₁ ⊓ (K₁ ⊔ T) : Subgroup G) ≤ u128 V V₁).trans hUT
    have hN2 : IsPGroup 2 ↥(u128 V V₁ ⊓ (K₁ ⊔ T)) := hs.hyp.hyp.sylow.1.to_le hNleT
    have hNp : u128 V V₁ ⊓ (K₁ ⊔ T) ≤ pCoreOf 2 (K₁ ⊔ T) :=
      @CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer G _ 2
        (u128 V V₁ ⊓ (K₁ ⊔ T)) (K₁ ⊔ T) inf_le_right hNnorm hN2
    have hZO : ZD ≤ pCoreOf 2 (K₁ ⊔ T) := hZN.trans hNp
    have hconj := CFSG.Quasithin.B2_13_conjClosure hT' hZT hZO
    have hTZD : T ≤ Subgroup.centralizer (ZD : Set G) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzT : z ∈ Subgroup.centralizer (T : Set G) :=
        (CFSG.Quasithin.B2F.omegaOneCenter_le_inf_centralizer T hz.1).2
      exact (Subgroup.mem_centralizer_iff.mp hzT t ht).symm
    have hTK : T ≤ Subgroup.normalizer (K₁ : Set G) := hZT'.trans hKn
    rwa [conjClosure_sup_eq_of_le_normalizer hTK hTZD] at hconj
  have hfaith : quasithinIsFaithfulLocal T K₁ := by
    have hHcore : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≠ ⊥ := by
      intro hb
      have hV₁2p : IsPGroup 2 V₁ := IsPGroup.of_card (n := 1) (by simpa using hs.v1.2.1)
      have hle := CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 V₁ hV₁2p
      rw [hb, le_bot_iff] at hle
      have hne : V₁ ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hV₁2
        norm_num at hV₁2
      exact hne hle
    obtain ⟨S, hS⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hs.hyp.hyp.sylow
    have hSH : (S : Subgroup G) ≤ Subgroup.normalizer (V₁ : Set G) := by
      rw [hS]
      exact hs.v1.2.2
    have hInH : InH (S : Subgroup G) (Subgroup.normalizer (V₁ : Set G)) :=
      ⟨hSH, hHcore⟩
    have hKlocS := CFSG.Quasithin.EmptyFaithfulMultiple.quasithinIsLocal_of_mem_cComp S
      hInH (show K₁ ∈ cComp (Subgroup.normalizer (V₁ : Set G)) from hK)
    have hKloc : quasithinIsLocal T K₁ := by
      rwa [hS] at hKlocS
    have hKc : K₁ ∈ cComp (K₁ ⊔ T) :=
      cComp_mem_of_le (show K₁ ∈ cComp (Subgroup.normalizer (V₁ : Set G)) from hK)
        le_sup_left (sup_le (le_of_mem_cComp (show K₁ ∈ cComp
          (Subgroup.normalizer (V₁ : Set G)) from hK)) hs.v1.2.2)
    have hSH' : (S : Subgroup G) ≤ K₁ ⊔ T := by
      rw [hS]
      exact le_sup_right
    have hchar : CharTwo (K₁ ⊔ T) :=
      CFSG.Quasithin.charTwo_of_inH hs.hyp.hyp.qtke.2.1 S ⟨hSH', hKloc.2.2.2⟩
    have hVDK : ⁅conjClosure (quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁)) K₁,
        K₁⁆ ≠ ⊥ := by
      intro hbot
      apply hZDcomm
      refine eq_bot_iff.mpr ?_
      rw [← hbot]
      exact Subgroup.commutator_mono (le_conjClosure _ _) le_rfl
    exact CFSG.Quasithin.Vol2.Ch10.SecD.quasithinIsFaithfulLocal_of_isTwoReducedIn
      hKloc hKc hchar hred hVDK
  exact ⟨hKn, hZD, hVDle, hred, hZDcomm, hcommK, hfaith⟩

end CFSG.Quasithin.H13
