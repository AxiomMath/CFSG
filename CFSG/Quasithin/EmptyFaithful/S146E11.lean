module

public import CFSG.Quasithin.EmptyFaithful.S146E9
public import CFSG.Quasithin.EmptyFaithful.S146G2
public import CFSG.Quasithin.EmptyFaithful.S146E1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section Cosets

theorem mem_of_pow_mem_of_pow_three {Y : Type*} [Group Y] {p : Y} (hp3 : p ^ 3 = 1) {A : Subgroup Y}
    {k : ℕ} (hk : ¬ 3 ∣ k) (h : p ^ k ∈ A) : p ∈ A := by
  have hk' : k % 3 = 1 ∨ k % 3 = 2 := by omega
  have e : p ^ k = p ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hp3, one_pow, one_mul]
  rw [e] at h
  rcases hk' with h1 | h1
  · rwa [h1, pow_one] at h
  · rw [h1] at h
    have : p = (p ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hp3, one_mul, pow_one]
    rw [this]
    exact A.pow_mem h 2

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem FCtx.relIndex_tZero (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u)
    (e : OTwoQuot (centralizerMod Zz (mcOf T) (Subgroup.zpowers u)) ≃* Equiv.Perm (Fin 3)) :
    (tZero T u).relIndex (centralizerMod Zz (mcOf T) (Subgroup.zpowers u)) = 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := centralizerMod Zz (mcOf T) (Subgroup.zpowers u) with hX
  set T₀ := tZero T u with hT₀
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  have hT₀X : T₀ ≤ X := centralizerMod_mono_left _ hTH
  have hT₀T : T₀ ≤ T := centralizerMod_le_left _ _ _
  have hT₀p : IsPGroup 2 T₀ := S.hyp.sylow.1.to_le hT₀T
  have hXT : X ⊓ T ≤ T₀ := fun x hx => ⟨hx.2, hx.1.2.1, hx.1.2.2⟩
  have hnorm : Subgroup.normalizer (T₀ : Set G) ⊓ mcOf T ≤ T := c.hinv.normalizer_eq.le
  have hXH : X ≤ mcOf T := centralizerMod_le_left _ _ _
  have hQT : pCoreOf 2 X ≤ T₀ := by
    by_contra hQT
    set P : Subgroup G := pCoreOf 2 X ⊔ T₀ with hP
    have hPX : P ≤ X := sup_le (pCoreOf_le 2 X) hT₀X
    have hPp : IsPGroup 2 P := by
      intro x
      obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup_two hT₀p
        (fun t ht => le_normalizer_pCoreOf 2 X (hT₀X ht)) x.2
      obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 X) ⟨_, hk⟩
      refine ⟨k + m, ?_⟩
      apply Subtype.ext
      have := congrArg Subtype.val hm
      simpa [pow_add, pow_mul] using this
    have : Group.IsNilpotent ↥P := hPp.isNilpotent
    have hlt : T₀.subgroupOf P < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      apply hQT
      exact le_sup_left.trans (Subgroup.subgroupOf_eq_top.mp h)
    obtain ⟨n, hn, hnT⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    have hT₀P : T₀ ≤ P := le_sup_right
    have hfwd : ∀ (m : ↥P), m ∈ Subgroup.normalizer ((T₀.subgroupOf P : Subgroup ↥P) : Set ↥P) →
        ∀ t ∈ T₀, (m : G) * t * (m : G)⁻¹ ∈ T₀ := by
      intro m hm t ht
      have h1 : (⟨t, hT₀P ht⟩ : ↥P) ∈ T₀.subgroupOf P := ht
      have h2 := (Subgroup.mem_normalizer_iff.mp hm ⟨t, hT₀P ht⟩).mp h1
      exact h2
    have hnN : (n : G) ∈ Subgroup.normalizer (T₀ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => hfwd n hn x hx, fun hx => ?_⟩
      have h3 := hfwd n⁻¹ (Subgroup.inv_mem _ hn) _ hx
      have e3 : ((n⁻¹ : ↥P) : G) * ((n : G) * x * (n : G)⁻¹) * ((n⁻¹ : ↥P) : G)⁻¹ = x := by
        simp only [Subgroup.coe_inv, inv_inv]
        group
      rwa [e3] at h3
    have hnT' : (n : G) ∈ T := hnorm ⟨hnN, hXH (hPX n.2)⟩
    exact hnT (hXT ⟨hPX n.2, hnT'⟩)
  set Q : Subgroup ↥X := CFSG.Open.pCore 2 ↥X with hQ
  set T₀' : Subgroup ↥X := T₀.subgroupOf X with hT₀'
  have hQT' : Q ≤ T₀' := fun x hx => Subgroup.mem_subgroupOf.mpr
    (hQT (mem_pCoreOf_of_mem_pCore (by exact hx)))
  have hQidx : Q.index = 6 := by
    have h1 : Nat.card (↥X ⧸ Q) = Nat.card (Equiv.Perm (Fin 3)) := Nat.card_congr e.toEquiv
    rw [CFSG.Quasithin.gold_card_perm_fin_three] at h1
    exact h1
  have hmul := Subgroup.relIndex_mul_index hQT'
  rw [hQidx] at hmul
  have hmul := Subgroup.relIndex_mul_index hQT'
  rw [hQidx] at hmul
  have hT₀'p : IsPGroup 2 ↥T₀' := hT₀p.comap_subtype (K := X)
  obtain ⟨n, hn⟩ := hT₀'p.index (Q.subgroupOf T₀')
  have hrel : Q.relIndex T₀' = 2 ^ n := hn
  rw [hrel] at hmul
  have hn1 : n ≤ 1 := by
    by_contra h
    push Not at h
    have h4 : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 h
    have : 4 ∣ 6 := by
      rw [← hmul]
      exact Dvd.dvd.mul_right h4 _
    omega
  show T₀'.index = 3
  interval_cases n
  ·
    exfalso
    have h1 : Q.relIndex T₀' = 1 := by rw [hrel]; rfl
    have hT₀Q : T₀' ≤ Q := Subgroup.relIndex_eq_one.mp h1
    have hfwd : ∀ g ∈ X, ∀ t ∈ T₀, g * t * g⁻¹ ∈ T₀ := by
      intro g hg t ht
      have h2 : (⟨t, hT₀X ht⟩ : ↥X) ∈ Q := hT₀Q (Subgroup.mem_subgroupOf.mpr ht)
      have h3 : (⟨g, hg⟩ : ↥X) * ⟨t, hT₀X ht⟩ * (⟨g, hg⟩ : ↥X)⁻¹ ∈ Q :=
        (CFSG.LieType.BorelTits.pCore_normal 2).conj_mem _ h2 _
      have h4 := hQT' h3
      exact Subgroup.mem_subgroupOf.mp h4
    have hXN : X ≤ Subgroup.normalizer (T₀ : Set G) := by
      refine le_normalizer_of_forall_conjSub_le fun g hg y hy => ?_
      have h5 := hfwd g hg _ (mem_conjSub.mp hy)
      have e5 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rwa [e5] at h5
    have hXT' : X ≤ T₀ := fun x hx => hXT ⟨hx, hnorm ⟨hXN hx, hXH hx⟩⟩
    have h6 : T₀' = ⊤ := Subgroup.subgroupOf_eq_top.mpr hXT'
    rw [h6, Subgroup.index_top] at hmul
    omega
  · omega

theorem FCtx.exists_coset_rep (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u)
    (e : OTwoQuot (centralizerMod Zz (mcOf T) (Subgroup.zpowers u)) ≃* Equiv.Perm (Fin 3)) :
    ∃ p ∈ centralizerMod Zz (mcOf T) (Subgroup.zpowers u), orderOf p = 3 ∧
      ∀ x ∈ centralizerMod Zz (mcOf T) (Subgroup.zpowers u), ∃ n : ℕ, n < 3 ∧
        (p ^ n)⁻¹ * x ∈ tZero T u := by
  classical
  set X := centralizerMod Zz (mcOf T) (Subgroup.zpowers u) with hX
  set T₀ := tZero T u with hT₀
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  have hT₀X : T₀ ≤ X := centralizerMod_mono_left _ hTH
  have hT₀T : T₀ ≤ T := centralizerMod_le_left _ _ _
  have hT₀p : IsPGroup 2 T₀ := S.hyp.sylow.1.to_le hT₀T
  have hidx : (T₀.subgroupOf X).index = 3 := c.relIndex_tZero S e
  set T₀' : Subgroup ↥X := T₀.subgroupOf X with hT₀'
  have hdvd : 3 ∣ Nat.card ↥X := by
    have := Subgroup.card_mul_index T₀'
    rw [hidx] at this
    exact ⟨Nat.card T₀', by rw [← this]; ring⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨p', hp'⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 hdvd
  have hp3 : p' ^ 3 = 1 := by rw [← hp']; exact pow_orderOf_eq_one p'
  have hpT₀ : p' ∉ T₀' := by
    intro h
    obtain ⟨k, hk⟩ := (hT₀p.comap_subtype (K := X)) ⟨p', h⟩
    have h1 : p' ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : 3 ∣ 2 ^ k := hp' ▸ orderOf_dvd_of_pow_eq_one h1
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    omega
  let f : Fin 3 → ↥X ⧸ T₀' := fun i => (QuotientGroup.mk (p' ^ (i : ℕ)) : ↥X ⧸ T₀')
  have hlt : ∀ i j : Fin 3, (i : ℕ) < j → f i ≠ f j := by
    intro i j hij hEq
    have hm : (p' ^ (i : ℕ))⁻¹ * p' ^ (j : ℕ) ∈ T₀' := QuotientGroup.eq.mp hEq
    have e : (p' ^ (i : ℕ))⁻¹ * p' ^ (j : ℕ) = p' ^ ((j : ℕ) - i) := by
      have : (j : ℕ) = i + ((j : ℕ) - i) := by omega
      conv_lhs => rw [this, pow_add]
      group
    rw [e] at hm
    refine hpT₀ (mem_of_pow_mem_of_pow_three hp3 (k := (j : ℕ) - i) ?_ hm)
    have := i.2
    have := j.2
    omega
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
    · exact hlt i j h hij
    · exact hlt j i h hij.symm
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (by
    rw [Nat.card_fin]
    exact le_of_eq hidx)
  refine ⟨p', p'.2, ?_, fun x hx => ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hp'
  · obtain ⟨i, hi⟩ := hbij.2 (QuotientGroup.mk ⟨x, hx⟩)
    have h5 : (p' ^ (i : ℕ))⁻¹ * ⟨x, hx⟩ ∈ T₀' := QuotientGroup.eq.mp hi
    refine ⟨i, i.2, ?_⟩
    have h6 := Subgroup.mem_subgroupOf.mp h5
    simpa using h6

end Cosets

end CFSG.Quasithin
