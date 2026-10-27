module

public import CFSG.Quasithin.Background.SmithB42G2Rank
public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.Quasithin.Vol2.Ch11G2Q8InvField
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.Quasithin.B42G2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8

variable {K : Type} [Field K] [CharP K 2]
variable {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem coord_injective (hf : IsCoord (lmG K) H ⊥ π f) : Function.Injective f := by
  intro u v h
  have h1 := (hf.eq_iff u v).mp h
  rw [Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact h1

theorem card_W [Finite K] (hf : IsCoord (lmG K) H ⊥ π f) : Nat.card W = Nat.card K ^ 6 := by
  rw [← card_Q]
  exact Nat.card_congr (Equiv.ofBijective f ⟨coord_injective hf, hf.surj⟩)

section Inner

variable {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
include hc0 hc1

theorem mem_fixV_iff_fixSub (hf : IsCoord (lmG K) H ⊥ π f) {A : Subgroup (MulAut W)}
    (hAH : A ≤ H) (w : W) :
    w ∈ fixV A ↔ f w ∈ fixSub ((A.subgroupOf H).comap (rhoG hc0 hc1 π)) := by
  constructor
  · intro hw γ hγ
    rw [← IsCoord.actG hf hc0 hc1]
    exact congrArg f (hw _ hγ)
  · intro hw a ha
    obtain ⟨γ, hγ⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨a, hAH ha⟩
    have hγA : γ ∈ (A.subgroupOf H).comap (rhoG hc0 hc1 π) := by
      rw [Subgroup.mem_comap, hγ, Subgroup.mem_subgroupOf]
      exact ha
    apply coord_injective hf
    have h1 := IsCoord.actG hf hc0 hc1 γ w
    rw [hγ] at h1
    rw [h1]
    exact hw γ hγA

theorem card_fixV_eq_fixSub (hf : IsCoord (lmG K) H ⊥ π f) {A : Subgroup (MulAut W)}
    (hAH : A ≤ H) :
    Nat.card (fixV A) = Nat.card (fixSub ((A.subgroupOf H).comap (rhoG hc0 hc1 π))) := by
  refine Nat.card_congr (Equiv.ofBijective (fun w : fixV A =>
    (⟨f w.1, (mem_fixV_iff_fixSub hc0 hc1 hf hAH w.1).mp w.2⟩ :
      fixSub ((A.subgroupOf H).comap (rhoG hc0 hc1 π)))) ⟨?_, ?_⟩)
  · rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
    exact Subtype.ext (coord_injective hf (congrArg Subtype.val h))
  · rintro ⟨x, hx⟩
    obtain ⟨w, rfl⟩ := hf.surj x
    exact ⟨⟨w, (mem_fixV_iff_fixSub hc0 hc1 hf hAH w).mpr hx⟩, rfl⟩

theorem card_comap_rhoG (hf : IsCoord (lmG K) H ⊥ π f) {A : Subgroup (MulAut W)}
    (hAH : A ≤ H) :
    Nat.card ((A.subgroupOf H).comap (rhoG hc0 hc1 π)) = Nat.card A := by
  obtain ⟨hinj, hsurj⟩ := rhoG_bijective hf hc0 hc1
  rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self_of_surjective hsurj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv

theorem comap_rhoG_mul_self (hf : IsCoord (lmG K) H ⊥ π f) {A : Subgroup (MulAut W)}
    (hA : IsElemAbelian2 A) :
    ∀ γ ∈ (A.subgroupOf H).comap (rhoG hc0 hc1 π), γ * γ = 1 := by
  intro γ hγ
  apply (rhoG_bijective hf hc0 hc1).1
  rw [map_mul, map_one]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one, ← sq]
  exact hA.2 _ hγ

theorem comap_rhoG_comm (hf : IsCoord (lmG K) H ⊥ π f) {A : Subgroup (MulAut W)}
    (hA : IsElemAbelian2 A) :
    ∀ γ ∈ (A.subgroupOf H).comap (rhoG hc0 hc1 π),
      ∀ δ ∈ (A.subgroupOf H).comap (rhoG hc0 hc1 π), γ * δ = δ * γ := by
  intro γ hγ δ hδ
  apply (rhoG_bijective hf hc0 hc1).1
  rw [map_mul, map_mul]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact hA.1 _ hγ _ hδ

end Inner

theorem card_mul_card_fixV_inner [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hf : IsCoord (lmG K) H ⊥ π f) {A : Subgroup (MulAut W)} (hAH : A ≤ H)
    (hA : IsElemAbelian2 A) :
    Nat.card A ≤ Nat.card K ^ 3 ∧ Nat.card A * Nat.card (fixV A) ≤ Nat.card K ^ 6 ∧
      (A ≠ ⊥ → Nat.card K ^ 6 ≤ Nat.card A * Nat.card (fixV A) →
        Nat.card A = Nat.card K ^ 3 ∧ Nat.card (fixV A) = Nat.card K ^ 3) := by
  have h4 : 2 < Nat.card K := by
    rw [hK]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one h4
  have hn1 : 1 ≤ n := by omega
  have h1 := comap_rhoG_mul_self hc0 hc1 hf hA
  have hc := comap_rhoG_comm hc0 hc1 hf hA
  have hcard := card_comap_rhoG hc0 hc1 hf hAH
  have hfix := card_fixV_eq_fixSub hc0 hc1 hf hAH
  obtain ⟨hle, heq⟩ := card_mul_card_fixSub hK hn1 h1 hc
  rw [hcard, ← hfix] at hle heq
  refine ⟨hcard ▸ card_le_cube hK hn1 h1 hc, hle, fun hne hge => heq ?_ hge⟩
  intro hbot
  apply hne
  have h0 : Nat.card A = 1 := by
    rw [← hcard, hbot, Subgroup.card_bot]
  exact Subgroup.eq_bot_of_card_eq A h0

@[expose] def semiMap (c : K) (γ : ↥(cayleyGroup K)) (σ : K ≃+* K) : (Ix3 → K) →+ (Ix3 → K) where
  toFun x := c • g2Act γ (frobQ (σ : K →+* K) x)
  map_zero' := by
    have h0 : frobQ (σ : K →+* K) 0 = 0 := funext fun j => map_zero σ
    rw [h0, map_zero, smul_zero]
  map_add' x y := by
    have h0 : frobQ (σ : K →+* K) (x + y) = frobQ (σ : K →+* K) x + frobQ (σ : K →+* K) y :=
      funext fun j => map_add σ (x j) (y j)
    rw [h0, map_add, smul_add]

theorem semiMap_apply (c : K) (γ : ↥(cayleyGroup K)) (σ : K ≃+* K) (x : Ix3 → K) :
    semiMap c γ σ x = c • g2Act γ (frobQ (σ : K →+* K) x) := rfl

theorem semiMap_smul (c : K) (γ : ↥(cayleyGroup K)) (σ : K ≃+* K) (k : K) (x : Ix3 → K) :
    semiMap c γ σ (k • x) = σ k • semiMap c γ σ x := by
  rw [semiMap_apply, semiMap_apply, frobQ_smul, JonesParshall.g2Act_smul, smul_comm]
  rfl

theorem semiMap_eu_ne_zero {c : K} (hc : c ≠ 0) (γ : ↥(cayleyGroup K)) (σ : K ≃+* K) :
    semiMap c γ σ (eu 0 1) ≠ 0 := by
  intro h
  rw [semiMap_apply] at h
  have h1 := (smul_eq_zero.mp h).resolve_left hc
  have h2 := congrArg (g2Act γ⁻¹) h1
  rw [g2Act_inv_apply, map_zero] at h2
  have h3 := congrFun h2 (.inl 0)
  simp [frobQ] at h3

omit [CharP K 2] in
theorem eq_of_semilinear {T : (Ix3 → K) → (Ix3 → K)} {σ σ' : K → K} {x₀ : Ix3 → K}
    (hx₀ : T x₀ ≠ 0) (h1 : ∀ k x, T (k • x) = σ k • T x) (h2 : ∀ k x, T (k • x) = σ' k • T x)
    (k : K) : σ k = σ' k := by
  have h3 : (σ k - σ' k) • T x₀ = 0 := by rw [sub_smul, ← h1, ← h2, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hx₀)

omit [Field K] [CharP K 2] in
theorem two_lt_card {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) : 2 < Nat.card K := by
  rw [hK]
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

omit [Field K] [CharP K 2] in
theorem mul_self_of_elemAbelian {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A) {a : MulAut W}
    (ha : a ∈ A) : a * a = 1 := by
  rw [← sq]
  exact hA.2 a ha

theorem semiMap_semiMap_of_sq (hf : IsCoord (lmG K) H ⊥ π f) {τ : MulAut W}
    (hτ2 : τ * τ = 1) {c : K} {γ : ↥(cayleyGroup K)} {σ : K ≃+* K}
    (hrep : ∀ w, f (τ w) = semiMap c γ σ (f w)) (x : Ix3 → K) :
    semiMap c γ σ (semiMap c γ σ x) = x := by
  obtain ⟨w, rfl⟩ := hf.surj x
  rw [← hrep, ← hrep, ← MulAut.mul_apply, hτ2, MulAut.one_apply]

theorem sigma_involutive (hf : IsCoord (lmG K) H ⊥ π f) {τ : MulAut W} (hτ2 : τ * τ = 1)
    {c : K} {γ : ↥(cayleyGroup K)} {σ : K ≃+* K}
    (hrep : ∀ w, f (τ w) = semiMap c γ σ (f w)) (k : K) : σ (σ k) = k := by
  have hTT := semiMap_semiMap_of_sq hf hτ2 hrep
  refine eq_of_semilinear (T := fun x => semiMap c γ σ (semiMap c γ σ x)) (x₀ := eu 0 1)
    (σ := fun k => σ (σ k)) (σ' := fun k => k) ?_ (fun k x => ?_) (fun k x => ?_) k
  · rw [hTT]
    intro h0
    have h1 := congrFun h0 (.inl 0)
    simp at h1
  · rw [semiMap_smul, semiMap_smul]
  · rw [hTT, hTT]

section Normalizer

variable [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
include hK hn

omit [CharP K 2] [Finite K] in
theorem ringEquiv_involution_unique {σ₁ σ₂ : K ≃+* K} (h1 : ∀ k, σ₁ (σ₁ k) = k)
    (h2 : ∀ k, σ₂ (σ₂ k) = k) (h1' : ∃ k, σ₁ k ≠ k) (h2' : ∃ k, σ₂ k ≠ k) : σ₁ = σ₂ := by
  classical
  obtain ⟨σ, -, -, hgen, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ n) hK
  have : IsCyclic (K ≃+* K) := ⟨σ, fun x => by
    have h : x ∈ Subgroup.zpowers σ := by
      rw [hgen]
      exact Subgroup.mem_top x
    exact h⟩
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have : Fintype (K ≃+* K) := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := K ≃+* K) (n := 2) (by norm_num)
  by_contra hne
  have hσ1 : σ₁ ≠ 1 := by
    rintro rfl
    obtain ⟨k, hk⟩ := h1'
    exact hk rfl
  have hσ2 : σ₂ ≠ 1 := by
    rintro rfl
    obtain ⟨k, hk⟩ := h2'
    exact hk rfl
  have hsq : ∀ τ : K ≃+* K, (∀ k, τ (τ k) = k) → τ ^ 2 = 1 := fun τ hτ =>
    RingEquiv.ext fun k => by
      rw [sq]
      exact hτ k
  have hsub : ({1, σ₁, σ₂} : Finset (K ≃+* K)) ⊆
      Finset.univ.filter (fun a : K ≃+* K => a ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact hsq _ h1
    · exact hsq _ h2
  have h3 : ({1, σ₁, σ₂} : Finset (K ≃+* K)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hσ1.symm, hσ2.symm⟩
  have h4 := Finset.card_le_card hsub
  omega

theorem exists_semiMap (hf : IsCoord (lmG K) H ⊥ π f) {τ : MulAut W}
    (hτ : τ ∈ Subgroup.normalizer (H : Set (MulAut W))) :
    ∃ (c : K) (γ : ↥(cayleyGroup K)) (σ : K ≃+* K), c ≠ 0 ∧
      ∀ w, f (τ w) = semiMap c γ σ (f w) := by
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one (two_lt_card hK hn)
  have hτ' : τ⁻¹ ∈ Subgroup.normalizer (H : Set (MulAut W)) := Subgroup.inv_mem _ hτ
  obtain ⟨c, γ, σ, hc, h⟩ := exists_smul_frob_of_normalizes hf hc0 hc1 hK hn τ
    (fun z hz => by rw [Subgroup.mem_bot.mp hz, map_one]; exact Subgroup.one_mem _)
    (fun z hz => by rw [Subgroup.mem_bot.mp hz, map_one]; exact Subgroup.one_mem _)
    (fun h hh => (Subgroup.mem_normalizer_iff.mp hτ h).mp hh)
    (fun h hh => by
      have h1 := (Subgroup.mem_normalizer_iff.mp hτ' h).mp hh
      rwa [inv_inv] at h1)
  exact ⟨c, γ, σ, hc, fun w => h w⟩

theorem mem_of_semiMap_trivial (hf : IsCoord (lmG K) H ⊥ π f) {τ : MulAut W}
    (hτ2 : τ * τ = 1) {c : K} {γ : ↥(cayleyGroup K)} {σ : K ≃+* K}
    (hrep : ∀ w, f (τ w) = semiMap c γ σ (f w)) (hσ : ∀ k, σ k = k) : τ ∈ H := by
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one (two_lt_card hK hn)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hfrob : ∀ x, frobQ (σ : K →+* K) x = x := fun x => funext fun j => hσ (x j)
  have hT : ∀ x, semiMap c γ σ x = c • g2Act γ x := fun x => by rw [semiMap_apply, hfrob]
  have hTT := semiMap_semiMap_of_sq hf hτ2 hrep
  have hpol : ∀ x y, polarQ (semiMap c γ σ x) (semiMap c γ σ y) = c * c * polarQ x y := by
    intro x y
    rw [hT, hT, polarQ_smul_left, polarQ_smul_right, polarQ_g2Act]
    ring
  have h4 : c * c * (c * c) = 1 := by
    have h1 := hpol (semiMap c γ σ (eu 0 1)) (semiMap c γ σ (q6 0 0 0 1 0 0))
    rw [hTT, hTT, hpol] at h1
    have h0 : polarQ (eu 0 (1 : K)) (q6 0 0 0 1 0 0) = 1 := by
      rw [polarQ_eu0]
      rfl
    rw [h0] at h1
    linear_combination -h1
  have hc : c = 1 := by
    have h5 : (c + 1) ^ 4 = 0 := by
      linear_combination h4 + (2 * c ^ 3 + 3 * c ^ 2 + 2 * c + 1) * h2
    have h6 : c + 1 = 0 := pow_eq_zero_iff (by norm_num) |>.mp h5
    linear_combination h6 - h2
  have hτeq : τ = ((rhoG hc0 hc1 π γ : ↥H) : MulAut W) := by
    ext w
    apply coord_injective hf
    rw [hrep, hT, hc, one_smul, IsCoord.actG hf hc0 hc1]
  rw [hτeq]
  exact (rhoG hc0 hc1 π γ).2

theorem exists_sigma_ne (hf : IsCoord (lmG K) H ⊥ π f) {τ : MulAut W} (hτ2 : τ * τ = 1)
    (hτH : τ ∉ H) {c : K} {γ : ↥(cayleyGroup K)} {σ : K ≃+* K}
    (hrep : ∀ w, f (τ w) = semiMap c γ σ (f w)) : ∃ k, σ k ≠ k := by
  by_contra h
  push Not at h
  exact hτH (mem_of_semiMap_trivial hK hn hf hτ2 hrep h)

theorem mul_mem_of_not_mem (hf : IsCoord (lmG K) H ⊥ π f) {A : Subgroup (MulAut W)}
    (hAN : A ≤ Subgroup.normalizer (H : Set (MulAut W))) (hA : IsElemAbelian2 A)
    {a b : MulAut W} (ha : a ∈ A) (hb : b ∈ A) (haH : a ∉ H) (hbH : b ∉ H) : a * b ∈ H := by
  obtain ⟨ca, γa, σa, hca, hra⟩ := exists_semiMap hK hn hf (hAN ha)
  obtain ⟨cb, γb, σb, hcb, hrb⟩ := exists_semiMap hK hn hf (hAN hb)
  have ha2 := mul_self_of_elemAbelian hA ha
  have hb2 := mul_self_of_elemAbelian hA hb
  have hσ : σa = σb := ringEquiv_involution_unique hK hn
    (sigma_involutive hf ha2 hra) (sigma_involutive hf hb2 hrb)
    (exists_sigma_ne hK hn hf ha2 haH hra) (exists_sigma_ne hK hn hf hb2 hbH hrb)
  obtain ⟨c, γ, σ, hc, hr⟩ := exists_semiMap hK hn hf (Subgroup.mul_mem _ (hAN ha) (hAN hb))
  have hab2 : a * b * (a * b) = 1 := by
    rw [show a * b * (a * b) = a * (b * a) * b by group, ← hA.1 a ha b hb,
      show a * (a * b) * b = (a * a) * (b * b) by group, ha2, hb2, one_mul]
  have hTab : ∀ x, semiMap c γ σ x = semiMap ca γa σa (semiMap cb γb σb x) := by
    intro x
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [← hr, ← hrb, ← hra, MulAut.mul_apply]
  have hlin : ∀ k, σ k = k := by
    intro k
    refine eq_of_semilinear (T := semiMap c γ σ) (x₀ := eu 0 1)
      (σ := fun k => σ k) (σ' := fun k => k) (semiMap_eu_ne_zero hc γ σ)
      (fun k x => semiMap_smul c γ σ k x) (fun k x => ?_) k
    rw [hTab, hTab, semiMap_smul, semiMap_smul, hσ, sigma_involutive hf hb2 hrb]
  exact mem_of_semiMap_trivial hK hn hf hab2 hr hlin

theorem card_le_two_mul_card_inf [Finite W] (hf : IsCoord (lmG K) H ⊥ π f)
    {A : Subgroup (MulAut W)}
    (hAN : A ≤ Subgroup.normalizer (H : Set (MulAut W))) (hA : IsElemAbelian2 A) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ H) := by
  classical
  have : Finite (MulAut W) := Finite.of_injective (fun e : MulAut W => (e : W → W))
    (fun e e' h => MulEquiv.ext (congrFun h))
  by_cases hAH : A ≤ H
  · rw [inf_eq_left.mpr hAH]
    omega
  · obtain ⟨a, ha, haH⟩ := IsConcreteLE.not_le_iff_exists.mp hAH
    let φ : A → Bool × ↥(A ⊓ H) := fun b =>
      if hb : (b : MulAut W) ∈ H then (true, ⟨b, b.2, hb⟩)
      else (false, ⟨a * b, A.mul_mem ha b.2, mul_mem_of_not_mem hK hn hf hAN hA ha b.2 haH hb⟩)
    have hφ : Function.Injective φ := by
      intro b b' h
      by_cases hb : (b : MulAut W) ∈ H <;> by_cases hb' : (b' : MulAut W) ∈ H <;>
        simp only [φ, hb, hb', dite_true, dite_false, Prod.mk.injEq, Bool.true_eq_false,
          Bool.false_eq_true, false_and, true_and] at h
      · exact Subtype.ext (congrArg (fun x : ↥(A ⊓ H) => (x : MulAut W)) h)
      · exact Subtype.ext (mul_left_cancel (congrArg (fun x : ↥(A ⊓ H) => (x : MulAut W)) h))
    have h1 := Nat.card_le_card_of_injective φ hφ
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1

theorem card_fixV_sq_le [Finite W] (hf : IsCoord (lmG K) H ⊥ π f) {A : Subgroup (MulAut W)}
    (hAN : A ≤ Subgroup.normalizer (H : Set (MulAut W))) (hA : IsElemAbelian2 A)
    {a : MulAut W} (ha : a ∈ A) (haH : a ∉ H) :
    Nat.card (fixV A) ^ 2 ≤ Nat.card (fixV (A ⊓ H)) := by
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one (two_lt_card hK hn)
  obtain ⟨c, γ, σ, hc, hr⟩ := exists_semiMap hK hn hf (hAN ha)
  have ha2 := mul_self_of_elemAbelian hA ha
  obtain ⟨θ, hθ⟩ := exists_sigma_ne hK hn hf ha2 haH hr
  have hAH0 : A ⊓ H ≤ H := inf_le_right
  set M := fixSub (((A ⊓ H).subgroupOf H).comap (rhoG hc0 hc1 π)) with hM
  have hTM : ∀ x ∈ M, semiMap c γ σ x ∈ M := by
    intro x hx
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [← hr, ← mem_fixV_iff_fixSub hc0 hc1 hf hAH0]
    have hw := (mem_fixV_iff_fixSub hc0 hc1 hf hAH0 w).mpr hx
    intro b hb
    rw [← MulAut.mul_apply, hA.1 b (Subgroup.mem_inf.mp hb).1 a ha, MulAut.mul_apply, hw b hb]
  let T' : M →+ M :=
    { toFun := fun x => ⟨semiMap c γ σ x, hTM x x.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  have hT' : ∀ (k : K) (x : M), T' (k • x) = σ k • T' x := fun k x =>
    Subtype.ext (semiMap_smul c γ σ k x)
  have h1 := card_fix_sq_le T' (σ : K →+* K) hθ hT'
  have hmem : ∀ w ∈ fixV A, f w ∈ M := fun w hw =>
    (mem_fixV_iff_fixSub hc0 hc1 hf hAH0 w).mp fun b hb => hw b (Subgroup.mem_inf.mp hb).1
  have hinj : Function.Injective (fun w : fixV A =>
      (⟨⟨f w.1, hmem w.1 w.2⟩, Subtype.ext (by
        change semiMap c γ σ (f w.1) = f w.1
        rw [← hr, w.2 a ha])⟩ : {x : M // T' x = x})) := by
    rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
    exact Subtype.ext (coord_injective hf
      (congrArg (fun x : {x : M // T' x = x} => ((x : M) : Ix3 → K)) h))
  calc Nat.card (fixV A) ^ 2 ≤ Nat.card {x : M // T' x = x} ^ 2 :=
        Nat.pow_le_pow_left (Nat.card_le_card_of_injective _ hinj) 2
    _ ≤ Nat.card M := h1
    _ = Nat.card (fixV (A ⊓ H)) := (card_fixV_eq_fixSub hc0 hc1 hf hAH0).symm

theorem card_mul_card_fixV_lt [Finite W] (hf : IsCoord (lmG K) H ⊥ π f)
    {A : Subgroup (MulAut W)} (hAN : A ≤ Subgroup.normalizer (H : Set (MulAut W)))
    (hA : IsElemAbelian2 A) (hAH : ¬ A ≤ H) :
    Nat.card A * Nat.card (fixV A) < Nat.card K ^ 6 := by
  obtain ⟨a, ha, haH⟩ := IsConcreteLE.not_le_iff_exists.mp hAH
  have hA0 : IsElemAbelian2 (A ⊓ H) :=
    ⟨fun x hx y hy => hA.1 x (Subgroup.mem_inf.mp hx).1 y (Subgroup.mem_inf.mp hy).1,
      fun x hx => hA.2 x (Subgroup.mem_inf.mp hx).1⟩
  obtain ⟨h3, h6, -⟩ := card_mul_card_fixV_inner hK hn hf inf_le_right hA0
  have h2 := card_le_two_mul_card_inf hK hn hf hAN hA
  have hsq := card_fixV_sq_le hK hn hf hAN hA ha haH
  have hq4 : 4 < Nat.card K ^ 3 := by
    have := two_lt_card hK hn
    calc 4 < 3 ^ 3 := by norm_num
      _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have key : (Nat.card A * Nat.card (fixV A)) ^ 2 < (Nat.card K ^ 6) ^ 2 := by
    calc (Nat.card A * Nat.card (fixV A)) ^ 2 = Nat.card A ^ 2 * Nat.card (fixV A) ^ 2 := by
          ring
      _ ≤ (2 * Nat.card ↥(A ⊓ H)) ^ 2 * Nat.card (fixV (A ⊓ H)) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left h2 2) hsq
      _ = 4 * Nat.card ↥(A ⊓ H) * (Nat.card ↥(A ⊓ H) * Nat.card (fixV (A ⊓ H))) := by ring
      _ ≤ 4 * Nat.card K ^ 3 * Nat.card K ^ 6 := Nat.mul_le_mul (Nat.mul_le_mul_left 4 h3) h6
      _ < Nat.card K ^ 3 * Nat.card K ^ 3 * Nat.card K ^ 6 := by
          have hpos : 0 < Nat.card K ^ 3 * Nat.card K ^ 6 := by
            have := two_lt_card hK hn
            positivity
          nlinarith
      _ = (Nat.card K ^ 6) ^ 2 := by ring
  exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp key

theorem offender_facts [Finite W] (hf : IsCoord (lmG K) H ⊥ π f) {A : Subgroup (MulAut W)}
    (hAN : A ≤ Subgroup.normalizer (H : Set (MulAut W))) (hA : IsElemAbelian2 A) :
    Nat.card A * Nat.card (fixV A) ≤ Nat.card W ∧
      (A ≠ ⊥ → Nat.card W ≤ Nat.card A * Nat.card (fixV A) →
        A ≤ H ∧ Nat.card A = Nat.card K ^ 3 ∧ Nat.card (fixV A) = Nat.card K ^ 3) := by
  rw [card_W hf]
  by_cases hAH : A ≤ H
  · obtain ⟨-, h6, heq⟩ := card_mul_card_fixV_inner hK hn hf hAH hA
    exact ⟨h6, fun hne hge => ⟨hAH, heq hne hge⟩⟩
  · have hlt := card_mul_card_fixV_lt hK hn hf hAN hA hAH
    exact ⟨hlt.le, fun _ hge => absurd hge (not_le.mpr hlt)⟩

end Normalizer

end CFSG.Quasithin.B42G2
