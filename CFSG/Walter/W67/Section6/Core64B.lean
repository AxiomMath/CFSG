module

public import CFSG.Walter.W67.Section6.Std62
public import CFSG.Walter.W67.Section6.Core64A
public import CFSG.Walter.W67.Section4.Prop41C
public import CFSG.Walter.W67.Section6.JRSylow

public section

namespace CFSG.Walter.W67

namespace Sec6

variable {G : Type} [Group G] [Finite G] (s : Std G)

theorem lemma_6_4_i
    (h56 : S_prop_5_6) (h57 : S_lemma_5_7) (hR : RFacts) {X : Subgroup G}
    (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥)
    (hsol : Group.IsSolvable (Subgroup.normalizer (X : Set G))) :
    X = s.fr.E ∧ Nat.card X = 7 ∧ Nat.card (s.L X) = 168 ∧ s.p = 3 := by
  have hLN := L_le_normalizer s hXE hX
  have hLsol : Group.IsSolvable (s.L X) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLN)
  obtain ⟨hXeq, hprime⟩ := h57 G s hR hXE hX hLsol
  obtain ⟨-, -, -, hL, hLp, hLf, -, -⟩ := exists_jrGroup s hXE hX
  have hq := jrGroup_q s hL hLp hLf
  have hq3 : ¬ 3 < hL.q := fun h => not_isSolvable_of_three_lt hL h hLsol
  have hpos := f_div_pos s hXE hX
  have hq5 : hL.q ≠ 5 := by omega
  obtain ⟨-, -, -, hsolv⟩ := (hR _ hL hq5).1
  obtain ⟨hq3', hLc, -⟩ := hsolv hLsol
  have hp3 : s.p = 3 := by
    rw [hq] at hq3'
    have hdvd : s.p ∣ 3 := hq3' ▸ dvd_pow_self s.p hpos.ne'
    exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp hdvd
  have h3 : ¬ 3 ∣ Nat.card s.fr.E := h56 G s hp3 hR
  have hLE := L_inf_E_of_not_three_dvd s hXE hX h3
  subst hXeq
  set ℓ := Nat.card s.fr.E with hℓ
  have : Fact ℓ.Prime := ⟨hprime⟩
  have hNcard : Nat.card (Subgroup.normalizer (s.fr.E : Set G)) = 168 * ℓ := by
    rw [normalizer_eq s hXE hX, sup_comm]
    have h := Sec52.card_sup_mul_card_inf (E_le_normalizer_L s hXE hX)
    rw [hLE, Subgroup.card_bot, mul_one, hLc] at h
    exact h
  have hℓ168 : ℓ ∣ 168 := by
    by_contra hdvd
    have hcopr : Nat.Coprime ℓ 168 := (Nat.Prime.coprime_iff_not_dvd hprime).mpr hdvd
    have hEc : Nat.card s.fr.E = ℓ ^ (Nat.card G).factorization ℓ := by
      have hEr : IsPGroup ℓ s.fr.E := IsPGroup.of_card (n := 1) (by rw [pow_one])
      rw [card_eq_of_normalizer hEr fun Q hQ hEQ hQN => ?_]
      have hQc := Subgroup.card_dvd_of_le hQN
      rw [hNcard] at hQc
      obtain ⟨k, hk⟩ := hQ.exists_card_eq
      rw [hk] at hQc
      have hk1 : k ≤ 1 := by
        by_contra hk1
        have h1 : ℓ ^ 2 ∣ 168 * ℓ := (pow_dvd_pow ℓ (by omega)).trans hQc
        rw [pow_two] at h1
        exact hdvd (Nat.dvd_of_mul_dvd_mul_right hprime.pos h1)
      have hcard : Nat.card Q ≤ Nat.card s.fr.E := by
        rw [hk, ← hℓ]
        calc ℓ ^ k ≤ ℓ ^ 1 := Nat.pow_le_pow_right hprime.pos hk1
          _ = ℓ := pow_one ℓ
      exact (Subgroup.eq_of_le_of_card_ge hEQ hcard).symm.le
    set P : Sylow ℓ G := Sylow.ofCard s.fr.E hEc with hP
    have hPE : (P : Subgroup G) = s.fr.E := Sylow.coe_ofCard _ _
    have hℓ2 : ℓ ≠ 2 := by
      intro h2
      exact (Nat.not_even_iff_odd.mpr s.fr.odd_card_E) (by rw [← hℓ, h2]; exact even_two)
    refine false_of_perfect_of_le_centralizer s.perfect hℓ2 P (by rw [hPE]; exact s.E_ne_bot) ?_
    rw [hPE, normalizer_eq s hXE hX]
    refine sup_le (L_le_centralizer s hXE hX) ?_
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro e' he'
    exact E_comm s e' he' e he
  have hℓ7 : ℓ = 7 := by
    have h168 : (168 : ℕ) = 2 ^ 3 * 3 * 7 := by norm_num
    rw [h168] at hℓ168
    rcases (Nat.Prime.dvd_mul hprime).mp hℓ168 with h | h
    · rcases (Nat.Prime.dvd_mul hprime).mp h with h' | h'
      · have h2 := (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp
          (hprime.dvd_of_dvd_pow h')
        exact absurd (show Even ℓ by rw [h2]; exact even_two)
          (Nat.not_even_iff_odd.mpr s.fr.odd_card_E)
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_three).mp h' ▸
          dvd_rfl) h3
    · exact (Nat.prime_dvd_prime_iff_eq hprime (by norm_num)).mp h
  exact ⟨rfl, hℓ7, hLc, hp3⟩

structure Sol (s : Std G) where
  p3 : s.p = 3
  f7 : s.f = 7
  E7 : Nat.card s.fr.E = 7
  S : Subgroup G
  L168 : Sec64.L168 (s.L s.fr.E) S

theorem nonempty_sol
    (h56 : S_prop_5_6) (h57 : S_lemma_5_7) (hR : RFacts) {X : Subgroup G}
    (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥)
    (hsol : Group.IsSolvable (Subgroup.normalizer (X : Set G))) :
    X = s.fr.E ∧ Nonempty (Sol s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hXeq, hX7, hL168, hp3⟩ := lemma_6_4_i s h56 h57 hR hXE hX hsol
  subst hXeq
  refine ⟨rfl, ?_⟩
  have hLN := L_le_normalizer s hXE hX
  have hLsol : Group.IsSolvable (s.L s.fr.E) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLN)
  obtain ⟨-, -, -, hL, hLp, hLf, -, -⟩ := exists_jrGroup s hXE hX
  have hq := jrGroup_q s hL hLp hLf
  have hq3 : ¬ 3 < hL.q := fun h => not_isSolvable_of_three_lt hL h hLsol
  have hpos := f_div_pos s hXE hX
  have hq5 : hL.q ≠ 5 := by omega
  obtain ⟨-, -, -, hsolv⟩ := (hR _ hL hq5).1
  obtain ⟨hq3', -, hSyl⟩ := hsolv hLsol
  have hf7 : s.f = 7 := by
    rw [hq, hp3, hX7] at hq3'
    have h1 : s.f / 7 = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 3)
      (show 3 ^ (s.f / 7) = 3 ^ 1 by rw [hq3', pow_one])
    obtain ⟨c, hc⟩ := card_dvd_f s hXE hX
    rw [hX7] at hc
    rw [hc, Nat.mul_div_cancel_left _ (by norm_num)] at h1
    rw [hc, h1]
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 (s.L s.fr.E)) := inferInstance
  obtain ⟨hS₀n, hS₀c⟩ := hSyl S₀
  refine ⟨⟨hp3, hf7, hX7, (S₀ : Subgroup (s.L s.fr.E)).map (s.L s.fr.E).subtype, ?_, ?_,
    hL168, ?_, ?_⟩⟩
  · exact Subgroup.map_subtype_le _
  · rw [Subgroup.card_map_of_injective (s.L s.fr.E).subtype_injective]
    exact hL.card_sylow S₀
  · intro l hl
    apply Sec53.mem_normalizer_of_conj_le
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨l, hl⟩ * y * ⟨l, hl⟩⁻¹, hS₀n.conj_mem y hy ⟨l, hl⟩, rfl⟩
  · rintro l ⟨hl, hlC⟩
    have hlC' : (⟨l, hl⟩ : s.L s.fr.E) ∈
        Subgroup.centralizer ((S₀ : Subgroup (s.L s.fr.E)) : Set (s.L s.fr.E)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hlC y ⟨y, hy, rfl⟩
    rw [hS₀c] at hlC'
    exact ⟨⟨l, hl⟩, hlC', rfl⟩

namespace Sol

variable {s} (σ : Sol s)
include σ

theorem not_three_dvd_E : ¬ 3 ∣ Nat.card s.fr.E := by
  rw [σ.E7]
  norm_num

theorem L_inf_E : s.L s.fr.E ⊓ s.fr.E = ⊥ :=
  L_inf_E_of_not_three_dvd s le_rfl s.E_ne_bot σ.not_three_dvd_E

omit σ in
theorem normalizer_eq_centralizer :
    Subgroup.normalizer (s.fr.E : Set G) = Subgroup.centralizer (s.fr.E : Set G) := by
  refine le_antisymm ?_ (Subgroup.centralizer_le_normalizer _)
  rw [normalizer_eq s le_rfl s.E_ne_bot]
  exact sup_le (L_le_centralizer s le_rfl s.E_ne_bot) (E_le_centralizer s le_rfl)

theorem card_normalizer_E :
    Nat.card (Subgroup.normalizer (s.fr.E : Set G)) = 168 * 7 := by
  rw [normalizer_eq s le_rfl s.E_ne_bot, sup_comm]
  have h := Sec52.card_sup_mul_card_inf (E_le_normalizer_L s le_rfl s.E_ne_bot)
  rw [σ.L_inf_E, Subgroup.card_bot, mul_one, σ.L168.card_L, σ.E7] at h
  exact h

theorem exists_gen :
    ∃ g ∈ s.fr.E, Subgroup.zpowers g = s.fr.E ∧ orderOf g = 7 := by
  obtain ⟨g, hg, hgen⟩ := exists_generator s
  refine ⟨g, hg, hgen, ?_⟩
  rw [← Nat.card_zpowers, hgen, σ.E7]

omit σ in
theorem decomp
    {x : G} (hx : x ∈ Subgroup.normalizer (s.fr.E : Set G)) :
    ∃ l ∈ s.L s.fr.E, ∃ e ∈ s.fr.E, l * e = x ∧ l * e = e * l := by
  rw [normalizer_eq s le_rfl s.E_ne_bot] at hx
  obtain ⟨l, hl, e, he, rfl⟩ :=
    (mem_sup_iff_of_le_normalizer (E_le_normalizer_L s le_rfl s.E_ne_bot)).mp hx
  exact ⟨l, hl, e, he, rfl,
    (Subgroup.mem_centralizer_iff.mp (L_le_centralizer s le_rfl s.E_ne_bot hl) e he).symm⟩

theorem pow_eq_one_of_decomp
    {l e : G} (hl : l ∈ s.L s.fr.E) (he : e ∈ s.fr.E)
    (hle : l * e = e * l) {n : ℕ} (hn : (l * e) ^ n = 1) : l ^ n = 1 ∧ e ^ n = 1 := by
  have h1 : (l * e) ^ n = l ^ n * e ^ n := (Commute.mul_pow hle n)
  rw [h1] at hn
  have hle' : l ^ n = (e ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hn
  have hmem : l ^ n ∈ s.L s.fr.E ⊓ s.fr.E :=
    Subgroup.mem_inf.mpr ⟨(s.L s.fr.E).pow_mem hl n,
      hle' ▸ s.fr.E.inv_mem (s.fr.E.pow_mem he n)⟩
  rw [σ.L_inf_E, Subgroup.mem_bot] at hmem
  refine ⟨hmem, ?_⟩
  rw [hmem] at hle'
  exact inv_eq_one.mp hle'.symm

theorem mem_L_of_coprime
    {x : G} (hx : x ∈ Subgroup.normalizer (s.fr.E : Set G))
    (hco : Nat.Coprime (orderOf x) 7) : x ∈ s.L s.fr.E := by
  obtain ⟨l, hl, e, he, rfl, hle⟩ := decomp hx
  obtain ⟨-, he1⟩ := σ.pow_eq_one_of_decomp hl he hle (pow_orderOf_eq_one (l * e))
  have he7 : e ^ 7 = 1 := by
    have := Subgroup.orderOf_dvd_natCard _ he
    rw [σ.E7] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have he' : e = 1 := by
    have := pow_gcd_eq_one.mpr ⟨he1, he7⟩
    rwa [hco.gcd_eq_one, pow_one] at this
  rw [he', mul_one]
  exact hl

theorem decomp_seven
    {y : G} (hy : y ∈ Subgroup.normalizer (s.fr.E : Set G))
    (hy7 : y ^ 7 = 1) : ∃ l ∈ s.L s.fr.E, ∃ e ∈ s.fr.E, l * e = y ∧ l * e = e * l ∧ l ^ 7 = 1 := by
  obtain ⟨l, hl, e, he, rfl, hle⟩ := decomp hy
  exact ⟨l, hl, e, he, rfl, hle, (σ.pow_eq_one_of_decomp hl he hle hy7).1⟩

theorem q_eq : s.q = 3 ^ 7 := by rw [Hyp.q, σ.p3, σ.f7]

theorem not_seven_dvd_K : ¬ 7 ∣ Nat.card s.K := by
  intro h7
  have h := h7.trans (card_K_dvd s)
  rw [σ.q_eq] at h
  norm_num at h

theorem factorization_H :
    (Nat.card s.H).factorization 7 = 1 := by
  have h := s.factorization_card_H (by norm_num : Nat.Prime 7) (by norm_num)
  rw [Nat.factorization_eq_zero_of_not_dvd σ.not_seven_dvd_K, zero_add, σ.E7,
    Nat.Prime.factorization_self (by norm_num)] at h
  exact h

omit σ in
theorem no_real_seven
    (hK : ¬ 7 ∣ Nat.card s.K) (u x t : G) (hu : orderOf u = 2)
    (hx : x ∈ Subgroup.centralizer ({u} : Set G)) (ht : t ∈ Subgroup.centralizer ({u} : Set G))
    (ht2 : t * t = 1) (htx : t * x * t⁻¹ = x⁻¹) (hxr : IsPGroup 7 (Subgroup.zpowers x)) :
    x = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_J s hu)
  have hconj : ∀ y ∈ Subgroup.centralizer ({u} : Set G),
      g * y * g⁻¹ ∈ Subgroup.centralizer ({s.J} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← hg]
    calc g * y * g⁻¹ * (g * u * g⁻¹) = g * (y * u) * g⁻¹ := by group
      _ = g * (u * y) * g⁻¹ := by rw [hy]
      _ = g * u * g⁻¹ * (g * y * g⁻¹) := by group
  have hx' := hconj x hx
  have ht' := hconj t ht
  have hIDP := s.fr.isInternalDirectProduct_H
  have hKE : s.K ⊔ s.fr.E ≤ Subgroup.centralizer ({s.J} : Set G) := sup_le s.K_le_H s.fr.E_le_H
  have hJKE : s.J ∉ s.K ⊔ s.fr.E := by
    intro hJ'
    have h1 := Subgroup.disjoint_def.mp hIDP.2.1 (Subgroup.mem_zpowers s.J) hJ'
    have h2 := s.orderOf_J
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hJC : s.J ∈ Subgroup.centralizer ((s.K ⊔ s.fr.E : Subgroup G) : Set G) :=
    hIDP.2.2 (Subgroup.mem_zpowers s.J)
  have hJN : Subgroup.zpowers s.J ≤ Subgroup.normalizer ((s.K ⊔ s.fr.E : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hJC)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hxr) ⟨x, Subgroup.mem_zpowers x⟩
  rw [Subgroup.orderOf_mk] at hk
  have hodd : Odd (orderOf (g * x * g⁻¹)) := by
    rw [orderOf_conj_mul, hk]; exact (by decide : Odd 7).pow
  have hx'H : g * x * g⁻¹ ∈ Subgroup.zpowers s.J ⊔ (s.K ⊔ s.fr.E) := by rw [hIDP.1]; exact hx'
  have hx'KE := mem_of_odd_of_mem_zpowers_sup' s.orderOf_J hKE hJKE hx'H hodd
  have ht'H : g * t * g⁻¹ ∈ (s.K ⊔ s.fr.E) ⊔ Subgroup.zpowers s.J := by
    rw [sup_comm, hIDP.1]; exact ht'
  obtain ⟨k₀, hk₀, j, hj, hk₀j⟩ := (mem_sup_iff_of_le_normalizer hJN).mp ht'H
  have hjc : ∀ y ∈ s.K ⊔ s.fr.E, j * y = y * j := fun y hy => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hj
    exact (Commute.zpow_left ((Subgroup.mem_centralizer_iff.mp hJC y hy).symm) i).eq
  have hj2 : j * j = 1 := by
    have h1 := Subgroup.orderOf_dvd_natCard _ hj
    rw [s.card_zpowers_J] at h1
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one]
    exact h1
  have ht'2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hk₀2 : k₀ * k₀ = 1 := by
    rw [← hk₀j] at ht'2
    calc k₀ * k₀ = k₀ * (k₀ * j) * j⁻¹ := by group
      _ = k₀ * (j * k₀) * j⁻¹ := by rw [hjc k₀ hk₀]
      _ = (k₀ * j) * (k₀ * j) * (j * j)⁻¹ := by group
      _ = 1 := by rw [ht'2, hj2]; group
  obtain ⟨k₁, hk₁, e₁, he₁, rfl⟩ := mem_KE s hk₀
  have he₁1 : e₁ = 1 := by
    refine eq_one_of_sq_mem_K s he₁ ?_
    have e1 : e₁ * e₁ = (k₁ * (e₁ * k₁ * e₁⁻¹))⁻¹ * ((k₁ * e₁) * (k₁ * e₁)) := by group
    rw [e1, hk₀2, mul_one]
    exact s.K.inv_mem (s.K.mul_mem hk₁
      ((Subgroup.mem_normalizer_iff.mp (E_le_normalizer_K s he₁) k₁).mp hk₁))
  rw [he₁1, mul_one] at hk₀j
  obtain ⟨k₂, hk₂, e₂, he₂, hx'eq⟩ := mem_KE s hx'KE
  have hrel : (k₁ * j) * (k₂ * e₂) * (k₁ * j)⁻¹ = (k₂ * e₂)⁻¹ := by
    rw [hk₀j, hx'eq]
    calc g * t * g⁻¹ * (g * x * g⁻¹) * (g * t * g⁻¹)⁻¹ = g * (t * x * t⁻¹) * g⁻¹ := by group
      _ = (g * x * g⁻¹)⁻¹ := by rw [htx]; group
  have hrel' : k₁ * (k₂ * e₂) * k₁⁻¹ = (k₂ * e₂)⁻¹ := by
    have hjke := hjc (k₂ * e₂) (hx'eq ▸ hx'KE)
    calc k₁ * (k₂ * e₂) * k₁⁻¹ = k₁ * ((k₂ * e₂) * j * j⁻¹) * k₁⁻¹ := by group
      _ = k₁ * (j * (k₂ * e₂) * j⁻¹) * k₁⁻¹ := by rw [← hjke]
      _ = (k₁ * j) * (k₂ * e₂) * (k₁ * j)⁻¹ := by group
      _ = (k₂ * e₂)⁻¹ := hrel
  have he₂1 : e₂ = 1 := by
    refine eq_one_of_sq_mem_K s he₂ ?_
    have e2 : e₂ * e₂ = (e₂ * (k₁ * k₂) * e₂⁻¹)⁻¹ * (k₂⁻¹ * k₁) := by
      have : e₂ * (k₁ * k₂) * e₂ = k₂⁻¹ * k₁ := by
        have h3 : (k₂ * e₂) * (k₁ * (k₂ * e₂) * k₁⁻¹) = 1 := by rw [hrel', mul_inv_cancel]
        calc e₂ * (k₁ * k₂) * e₂ = k₂⁻¹ * ((k₂ * e₂) * (k₁ * (k₂ * e₂) * k₁⁻¹)) * k₁ := by group
          _ = k₂⁻¹ * k₁ := by rw [h3]; group
      calc e₂ * e₂ = (e₂ * (k₁ * k₂) * e₂⁻¹)⁻¹ * (e₂ * (k₁ * k₂) * e₂) := by group
        _ = _ := by rw [this]
    rw [e2]
    exact s.K.mul_mem (s.K.inv_mem ((Subgroup.mem_normalizer_iff.mp (E_le_normalizer_K s he₂)
      _).mp (s.K.mul_mem hk₁ hk₂))) (s.K.mul_mem (s.K.inv_mem hk₂) hk₁)
  rw [he₂1, mul_one] at hx'eq
  have hdvd : orderOf x ∣ Nat.card s.K := by
    rw [← orderOf_conj_mul g x, ← hx'eq]
    exact Subgroup.orderOf_dvd_natCard _ hk₂
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk] at hdvd
    exact hK ((dvd_pow_self 7 hk0).trans hdvd)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  exact hk

theorem invFacts : Sec64.InvFacts G 7 where
  two_comm := fun _ hT _ ha _ hb => (two_facts s hT ha hb).1
  two_sq := fun _ hT _ ha => (two_facts s hT ha ha).2
  no_real := no_real_seven σ.not_seven_dvd_K

end Sol

end Sec6

end CFSG.Walter.W67
