module

public import CFSG.Walter.J1.Exclude

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem oddPart_eq_of_good {A : Subgroup G} (habel : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y)
    (hA : Nat.card A = 27) {X : Subgroup G} (hXA : X ≤ A) (hX3 : Nat.card X = 3) {x : G}
    (hx : orderOf x = 2) (hXx : X ≤ Subgroup.centralizer ({x} : Set G)) :
    A ≤ Subgroup.centralizer (X : Set G) ∧
      (∀ y ∈ Subgroup.centralizer (X : Set G), Odd (orderOf y) → y ∈ A) ∧
      A ⊓ Subgroup.centralizer ({x} : Set G) = X ∧
      Nat.card (Subgroup.centralizer (X : Set G)) = 54 := by
  obtain ⟨-, AX, -, -, -, -, -, hAXx, hAXcard, hAXodd, -, hAXc⟩ :=
    h.oddPart_classify_of_centralizer (Or.inl rfl) hX3 hx hXx
  have hAC : A ≤ Subgroup.centralizer (X : Set G) := fun y hy =>
    Subgroup.mem_centralizer_iff.mpr fun z hz => habel z (hXA hz) y hy
  have hAAX : A ≤ AX := fun y hy =>
    hAXodd y (hAC hy) (odd_orderOf_of_mem (by rw [hA]; decide) hy)
  have hAXeq : AX = A := by
    refine (Subgroup.eq_of_le_of_card_ge hAAX ?_).symm
    have := Subgroup.card_dvd_of_le hAAX
    rw [hA] at this ⊢
    rcases hAXc with h0 | h0 | h0 | h0 | h0 <;> rw [h0] at this ⊢ <;> omega
  subst hAXeq
  refine ⟨hAC, hAXodd, hAXx, ?_⟩
  rw [← hAXcard, hA]

omit [Finite G] in
theorem conj_mul_mem_eq {A : Subgroup G} (habel : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y) {s c z : G}
    (hc : c ∈ A) (hz : z ∈ A) : s * c * z * (s * c)⁻¹ = s * z * s⁻¹ := by
  rw [show s * c * z * (s * c)⁻¹ = s * (c * z * c⁻¹) * s⁻¹ by group, habel c hc z hz,
    mul_inv_cancel_right]

omit [Finite G] in
theorem inf_centralizer_mul_eq {A : Subgroup G} (habel : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y)
    {s c : G} (hc : c ∈ A) :
    A ⊓ Subgroup.centralizer ({s * c} : Set G) = A ⊓ Subgroup.centralizer ({s} : Set G) := by
  ext z
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hz, hzc⟩
    refine ⟨hz, ?_⟩
    have h1 : s * c * z * (s * c)⁻¹ = z := by rw [hzc.symm]; group
    rw [conj_mul_mem_eq habel hc hz] at h1
    calc z * s = (s * z * s⁻¹) * s := by rw [h1]
      _ = s * z := by group
  · rintro ⟨hz, hzs⟩
    refine ⟨hz, ?_⟩
    have h1 : s * z * s⁻¹ = z := by rw [← hzs]; group
    rw [← conj_mul_mem_eq habel hc hz (s := s)] at h1
    calc z * (s * c) = (s * c * z * (s * c)⁻¹) * (s * c) := by rw [h1]
      _ = s * c * z := by group

include h in
theorem exists_commute_of_mem_normalizer {A : Subgroup G}
    (habel : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y) (hA : Nat.card A = 27) {a : G}
    (ha : a * a = 1) (haA : a ∈ Subgroup.normalizer (A : Set G)) {X : Subgroup G}
    (hXA : X ≤ A) (hX3 : Nat.card X = 3) {x : G} (hx : orderOf x = 2)
    (hXx : X ≤ Subgroup.centralizer ({x} : Set G))
    (haX : a ∈ Subgroup.normalizer (X : Set G)) :
    ∃ w ∈ Subgroup.normalizer (A : Set G), w * a = a * w ∧
      A ⊓ Subgroup.centralizer ({w} : Set G) = X := by
  obtain ⟨hAC, hodd, hAx, hC54⟩ := h.oddPart_eq_of_good habel hA hXA hX3 hx hXx
  set C := Subgroup.centralizer (X : Set G)
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hxC : x ∈ C := Subgroup.mem_centralizer_iff.mpr fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hXx hy))
  have hCN : ∀ y ∈ C, y ∈ Subgroup.normalizer (A : Set G) := by
    intro y hy
    refine mem_normalizer_of_conj_mem fun z hz => hodd _ (C.mul_mem (C.mul_mem hy (hAC hz))
      (C.inv_mem hy)) ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact odd_orderOf_of_mem (by rw [hA]; decide) hz
  have haC : ∀ y ∈ C, a * y * a⁻¹ ∈ C := by
    intro y hy
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hz' : a⁻¹ * z * a ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haX) z).mp hz
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hy _ hz'
    calc z * (a * y * a⁻¹) = a * ((a⁻¹ * z * a) * y) * a⁻¹ := by group
      _ = a * (y * (a⁻¹ * z * a)) * a⁻¹ := by rw [this]
      _ = a * y * a⁻¹ * z := by group
  have hidx : (A.subgroupOf C).index = 2 := by
    have := (A.subgroupOf C).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, hA, hC54] at this
    omega
  have hxA : x ∉ A := fun hxA => by
    have := odd_orderOf_of_mem (by rw [hA]; decide) hxA
    rw [hx] at this
    exact absurd this (by decide)
  have haxA : a * x * a⁻¹ ∉ A := fun h1 => hxA (by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haA) _).mp h1
    simpa [mul_assoc] using this)
  set b₀ := a * x * a⁻¹ * x⁻¹
  have hb₀A : b₀ ∈ A := by
    have key := (Subgroup.index_eq_two_iff.mp hidx)
    obtain ⟨k, hk⟩ := key
    have h1 := hk ⟨a * x * a⁻¹, haC x hxC⟩
    have h2 := hk ⟨x, hxC⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at h1 h2
    have hn1 : (a * x * a⁻¹ : G) ∉ A := haxA
    have hk1 : (a * x * a⁻¹) * k ∈ A := by
      rcases h1 with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hn1
    have hk2 : x * k ∈ A := by
      rcases h2 with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hxA
    have := A.mul_mem hk1 (A.inv_mem hk2)
    simpa [b₀, mul_assoc] using this
  have hab₀ : a * b₀ * a⁻¹ = b₀⁻¹ := by
    simp only [b₀]
    rw [hainv]
    have hx2 : x⁻¹ = x := inv_eq_of_mul_eq_one_right ((orderOf_eq_two_iff).mp hx).1
    rw [hx2]
    calc a * (a * x * a * x) * a = (a * a) * x * a * x * a := by group
      _ = x * a * x * a := by rw [ha, one_mul]
      _ = (a * x * a * x)⁻¹ := by
        rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hx2, hainv]
        group
  have hb₀odd : Odd (orderOf b₀) := odd_orderOf_of_mem (by rw [hA]; decide) hb₀A
  obtain ⟨k, hk⟩ := hb₀odd
  set c := b₀ ^ (k + 1)
  have hcA : c ∈ A := A.pow_mem hb₀A _
  have hc2 : c * c = b₀ := by
    rw [← pow_two, ← pow_mul, show (k + 1) * 2 = 2 * k + 1 + 1 by ring, pow_succ, ← hk,
      pow_orderOf_eq_one, one_mul]
  have hac : a * c * a⁻¹ = c⁻¹ := by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hab₀, inv_pow]
  refine ⟨c * x, Subgroup.mul_mem _ (Subgroup.le_normalizer hcA) (hCN x hxC), ?_, ?_⟩
  · have : a * (c * x) * a⁻¹ = c * x := by
      calc a * (c * x) * a⁻¹ = (a * c * a⁻¹) * (a * x * a⁻¹) := by group
        _ = c⁻¹ * (b₀ * x) := by rw [hac]; simp [b₀]
        _ = c * x := by rw [← hc2]; group
    calc c * x * a = (a * (c * x) * a⁻¹)⁻¹⁻¹ * a := by rw [this, inv_inv]
      _ = a * (c * x) := by group
  ·
    rw [← hAx]
    ext z
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hz, hzc⟩
      refine ⟨hz, ?_⟩
      have hxz : x * z * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hCN x hxC) z).mp hz
      have h1 : c * x * z * (c * x)⁻¹ = z := by rw [hzc.symm]; group
      rw [show c * x * z * (c * x)⁻¹ = c * (x * z * x⁻¹) * c⁻¹ by group,
        habel c hcA _ hxz, mul_inv_cancel_right] at h1
      calc z * x = (x * z * x⁻¹) * x := by rw [h1]
        _ = x * z := by group
    · rintro ⟨hz, hzx⟩
      refine ⟨hz, ?_⟩
      calc z * (c * x) = c * (z * x) := by rw [← mul_assoc, habel z hz c hcA, mul_assoc]
        _ = c * (x * z) := by rw [hzx]
        _ = c * x * z := by group

include h in
theorem exists_four_of_commute {a b : G} (hT : IsFour a b) {A : Subgroup G} (hM : IsMaxInv a b A)
    (habel : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y)
    (ha : Nat.card (A ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = 3) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwa : w * a = a * w) :
    ∃ s : G, (s = 1 ∨ s = a ∨ s = b ∨ s = a * b) ∧
      A ⊓ Subgroup.centralizer ({w} : Set G) = A ⊓ Subgroup.centralizer ({s} : Set G) := by
  obtain ⟨g, hg⟩ := h.exists_conj_t_eq hT.1
  set h' := h.conj g
  set Aa := A ⊓ Subgroup.centralizer ({a} : Set G)
  have hAaF : Aa ≤ h'.F := h'.le_F_of_odd (by rw [hg]; exact inf_le_right)
    (by rw [ha]; decide)
  obtain ⟨c, hcAa, hc1, hAac, hc3⟩ := exists_gen (Or.inl rfl) ha
  have hcF := hAaF hcAa
  have hfour := h.inf_centralizer_four_eq_bot hT hM.1.1
  have hbC : b ∈ Subgroup.centralizer ({h'.t} : Set G) := by
    rw [hg, Subgroup.mem_centralizer_singleton_iff]; exact hT.2.2.2.symm
  obtain ⟨f, hfF, hf⟩ : ∃ f ∈ h'.F, f = b ∨ f = a * b := by
    rcases h'.mem_centralizer_t.mp hbC with hb | hb
    · exact ⟨b, hb, Or.inl rfl⟩
    · rw [hg] at hb
      exact ⟨a * b, hb, Or.inr rfl⟩
  have hf2 : f * f = 1 := by rcases hf with rfl | rfl; exacts [hT.mul_self_b, hT.mul_self_mul]
  have hf1 : f ≠ 1 := by rcases hf with rfl | rfl; exacts [hT.b_ne_one, hT.mul_ne_one]
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
  have hfa : f * a = a * f := by
    rcases hf with rfl | rfl
    · exact hT.2.2.2.symm
    · rw [mul_assoc, ← hT.2.2.2, ← mul_assoc]
  have hfN : f ∈ Subgroup.normalizer (Aa : Set G) :=
    mem_normalizer_inf_centralizer (by rcases hf with rfl | rfl; exacts [hM.1.2.2, hM.1.mul_mem])
      hfa.symm
  have hfc : f * c * f⁻¹ = c⁻¹ := by
    have hmem : f * c * f⁻¹ ∈ Subgroup.zpowers c := by
      rw [← hAac]; exact (Subgroup.mem_normalizer_iff.mp hfN c).mp hcAa
    have hc1' : f * c * f⁻¹ ≠ 1 := by
      intro h1; apply hc1; have := congrArg (fun z => f⁻¹ * z * f) h1; simpa [mul_assoc] using this
    have hcc : f * c * f⁻¹ ≠ c := by
      intro h1
      have hfc' : c * f = f * c := by
        calc c * f = (f * c * f⁻¹) * f := by rw [h1]
          _ = f * c := by group
      have hcb : c * b = b * c := by
        rcases hf with rfl | rfl
        · exact hfc'
        · have hca : c * a = a * c := Subgroup.mem_centralizer_singleton_iff.mp hcAa.2
          calc c * b = c * (a * (a * b)) := by rw [hT.a_mul_mul]
            _ = a * (c * (a * b)) := by rw [← mul_assoc, hca, mul_assoc]
            _ = a * ((a * b) * c) := by rw [hfc']
            _ = b * c := by rw [← mul_assoc, ← mul_assoc, hT.mul_self_a, one_mul]
      have : c ∈ A ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) :=
        ⟨hcAa, Subgroup.mem_centralizer_singleton_iff.mpr hcb⟩
      rw [hfour] at this
      exact hc1 this
    obtain ⟨k, hk⟩ := hmem
    have hk' : c ^ k = f * c * f⁻¹ := hk
    have h3 : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc3
    rw [zpow_eq_zpow_emod k h3] at hk'
    have hnn : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
    have hlt : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k % 3 = n := ⟨(k % 3).toNat, (Int.toNat_of_nonneg hnn).symm⟩
    rw [hn, zpow_natCast] at hk'
    have hn3 : n < 3 := by omega
    interval_cases n
    · exact absurd hk'.symm (by rw [pow_zero]; exact hc1')
    · exact absurd hk'.symm (by rw [pow_one]; exact hcc)
    · rw [← hk', eq_inv_iff_mul_eq_one, ← pow_succ, hc3]
  have hwC : w ∈ Subgroup.centralizer ({h'.t} : Set G) := by
    rw [hg, Subgroup.mem_centralizer_singleton_iff]; exact hwa
  have hwN : w ∈ Subgroup.normalizer (Aa : Set G) := mem_normalizer_inf_centralizer hwA hwa.symm
  have haN : a ∈ Subgroup.normalizer (Aa : Set G) := mem_normalizer_inf_centralizer hM.1.2.1 rfl
  obtain ⟨g', hg'F, hg'⟩ : ∃ g' ∈ h'.F, w = g' ∨ w = a * g' := by
    rcases h'.mem_centralizer_t.mp hwC with hw | hw
    · exact ⟨w, hw, Or.inl rfl⟩
    · rw [hg] at hw
      refine ⟨a * w, hw, Or.inr ?_⟩
      rw [← mul_assoc, hT.mul_self_a, one_mul]
  have hg'N : g' ∈ Subgroup.normalizer (Aa : Set G) := by
    rcases hg' with rfl | rfl
    · exact hwN
    · rw [show g' = a * (a * g') by rw [← mul_assoc, hT.mul_self_a, one_mul]]
      exact Subgroup.mul_mem _ haN hwN
  have hg'c : g' * c * g'⁻¹ = c ∨ g' * c * g'⁻¹ = c ^ 2 := by
    have hmem : g' * c * g'⁻¹ ∈ Subgroup.zpowers c := by
      rw [← hAac]; exact (Subgroup.mem_normalizer_iff.mp hg'N c).mp hcAa
    have hc1' : g' * c * g'⁻¹ ≠ 1 := by
      intro h1; apply hc1; have := congrArg (fun z => g'⁻¹ * z * g') h1
      simpa [mul_assoc] using this
    obtain ⟨k, hk⟩ := hmem
    have hk' : c ^ k = g' * c * g'⁻¹ := hk
    have h3 : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc3
    rw [zpow_eq_zpow_emod k h3] at hk'
    have hnn : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
    have hlt : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k % 3 = n := ⟨(k % 3).toNat, (Int.toNat_of_nonneg hnn).symm⟩
    rw [hn, zpow_natCast] at hk'
    have hn3 : n < 3 := by omega
    interval_cases n
    · exact absurd hk'.symm (by rw [pow_zero]; exact hc1')
    · left; rw [← hk', pow_one]
    · right; rw [← hk']
  have hcases := A5Sub.mem_normalizer_three h'.iso hcF hfF hg'F hc3 hc1 (by rw [pow_two]; exact hf2)
    hf1 hfc hg'c
  have hcfi : ∀ i : ℕ, c ^ i * f = f * (c ^ i)⁻¹ := by
    intro i
    have : f * c ^ i * f⁻¹ = (c ^ i)⁻¹ := by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hfc, inv_pow]
    calc c ^ i * f = f * (f⁻¹ * c ^ i * f) := by group
      _ = f * (f * c ^ i * f⁻¹) := by rw [hfinv]
      _ = f * (c ^ i)⁻¹ := by rw [this]
  have hcpow : ∀ i : ℕ, c ^ i ∈ A := fun i => A.pow_mem hcAa.1 i
  have hcpowinv : ∀ i : ℕ, (c ^ i)⁻¹ ∈ A := fun i => A.inv_mem (hcpow i)
  have hsets : ∀ s c' : G, c' ∈ A → (s = 1 ∨ s = a ∨ s = b ∨ s = a * b) → w = s * c' →
      ∃ s : G, (s = 1 ∨ s = a ∨ s = b ∨ s = a * b) ∧
        A ⊓ Subgroup.centralizer ({w} : Set G) = A ⊓ Subgroup.centralizer ({s} : Set G) :=
    fun s c' hc' hs hw => ⟨s, hs, by rw [hw, inf_centralizer_mul_eq habel hc']⟩
  have hfT : f = b ∨ f = a * b := hf
  have hafT : a * f = b ∨ a * f = a * b := by
    rcases hf with rfl | rfl
    · right; rfl
    · left; exact hT.a_mul_mul
  have hs1 : (1 : G) = 1 ∨ (1 : G) = a ∨ (1 : G) = b ∨ (1 : G) = a * b := Or.inl rfl
  have hsa : a = 1 ∨ a = a ∨ a = b ∨ a = a * b := Or.inr (Or.inl rfl)
  have hsf : f = 1 ∨ f = a ∨ f = b ∨ f = a * b := Or.inr (Or.inr hfT)
  have hsaf : a * f = 1 ∨ a * f = a ∨ a * f = b ∨ a * f = a * b := by
    rcases hafT with h | h <;> simp [h]
  have hpow : ∃ s c' : G, c' ∈ A ∧ (s = 1 ∨ s = a ∨ s = b ∨ s = a * b) ∧ (w = s * c') := by
    rcases hg' with hw | hw <;> rcases hcases with h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1] at hw
    · exact ⟨1, 1, A.one_mem, hs1, by rw [hw]; group⟩
    · exact ⟨1, c, hcAa.1, hs1, by rw [hw]; group⟩
    · exact ⟨1, c ^ 2, hcpow 2, hs1, by rw [hw]; group⟩
    · exact ⟨f, 1, A.one_mem, hsf, by rw [hw]; group⟩
    · exact ⟨f, (c ^ 1)⁻¹, hcpowinv 1, hsf, by rw [hw, ← hcfi 1, pow_one]⟩
    · exact ⟨f, (c ^ 2)⁻¹, hcpowinv 2, hsf, by rw [hw, ← hcfi 2]⟩
    · exact ⟨a, 1, A.one_mem, hsa, by rw [hw]⟩
    · exact ⟨a, c, hcAa.1, hsa, hw⟩
    · exact ⟨a, c ^ 2, hcpow 2, hsa, hw⟩
    · exact ⟨a * f, 1, A.one_mem, hsaf, by rw [hw]; group⟩
    · exact ⟨a * f, (c ^ 1)⁻¹, hcpowinv 1, hsaf, by rw [hw, mul_assoc, ← hcfi 1, pow_one]⟩
    · exact ⟨a * f, (c ^ 2)⁻¹, hcpowinv 2, hsaf, by rw [hw, mul_assoc, ← hcfi 2]⟩
  obtain ⟨s, c', hc', hs, hw⟩ := hpow
  exact hsets s c' hc' hs hw

include h in
theorem eq_coord_of_mem_normalizer {a b : G} (hT : IsFour a b) {A : Subgroup G}
    (hM : IsMaxInv a b A) (habel : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y) (hA : Nat.card A = 27)
    (ha : Nat.card (A ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = 3) {X : Subgroup G}
    (hXA : X ≤ A) (hX3 : Nat.card X = 3) {x : G} (hx : orderOf x = 2)
    (hXx : X ≤ Subgroup.centralizer ({x} : Set G))
    (haX : a ∈ Subgroup.normalizer (X : Set G)) :
    X = A ⊓ Subgroup.centralizer ({a} : Set G) ∨ X = A ⊓ Subgroup.centralizer ({b} : Set G) ∨
      X = A ⊓ Subgroup.centralizer ({a * b} : Set G) := by
  obtain ⟨w, hwA, hwa, hwX⟩ := h.exists_commute_of_mem_normalizer habel hA hT.mul_self_a
    hM.1.2.1 hXA hX3 hx hXx haX
  obtain ⟨s, hs, hws⟩ := h.exists_four_of_commute hT hM habel ha hwA hwa
  rw [hws] at hwX
  rcases hs with rfl | rfl | rfl | rfl
  · exfalso
    have : A ⊓ Subgroup.centralizer ({(1 : G)} : Set G) = A := by
      rw [inf_eq_left]
      intro z _
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp
    rw [this] at hwX
    rw [← hwX, hA] at hX3
    omega
  · exact Or.inl hwX.symm
  · exact Or.inr (Or.inl hwX.symm)
  · exact Or.inr (Or.inr hwX.symm)

include h in
theorem mem_of_normalizer_of_orderOf_three {A : Subgroup G}
    (habel : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y) (hA : Nat.card A = 27) {X : Subgroup G}
    (hXA : X ≤ A) (hX3 : Nat.card X = 3) {x : G} (hx : orderOf x = 2)
    (hXx : X ≤ Subgroup.centralizer ({x} : Set G)) {ν : G} (hν3 : orderOf ν = 3)
    (hνX : ν ∈ Subgroup.normalizer (X : Set G)) : ν ∈ A := by
  obtain ⟨hAC, hodd, -, -⟩ := h.oddPart_eq_of_good habel hA hXA hX3 hx hXx
  obtain ⟨v, hvX, hv1, hXv, hv3⟩ := exists_gen (Or.inl rfl) hX3
  have hν3' : ν ^ 3 = 1 := by rw [← hν3, pow_orderOf_eq_one]
  have hνv : ν * v * ν⁻¹ = v := by
    have hmem : ν * v * ν⁻¹ ∈ Subgroup.zpowers v := by
      rw [← hXv]; exact (Subgroup.mem_normalizer_iff.mp hνX v).mp hvX
    obtain ⟨k, hk⟩ := hmem
    have hk' : v ^ k = ν * v * ν⁻¹ := hk
    have h3 : v ^ (3 : ℤ) = 1 := by exact_mod_cast hv3
    rw [zpow_eq_zpow_emod k h3] at hk'
    have hnn : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
    have hlt : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k % 3 = n := ⟨(k % 3).toNat, (Int.toNat_of_nonneg hnn).symm⟩
    rw [hn, zpow_natCast] at hk'
    have hn3 : n < 3 := by omega
    interval_cases n
    · exfalso; apply hv1
      have := congrArg (fun z => ν⁻¹ * z * ν) hk'
      simpa [mul_assoc] using this.symm
    · rw [← hk', pow_one]
    · exfalso
      have e1 : ν ^ 3 * v * (ν ^ 3)⁻¹ = v ^ 2 := by
        have e2 : ∀ j : ℕ, ν ^ j * v * (ν ^ j)⁻¹ = v ^ (2 ^ j) := by
          intro j
          induction j with
          | zero => simp
          | succ j ih =>
            rw [pow_succ, show ν ^ j * ν * v * (ν ^ j * ν)⁻¹ = ν ^ j * (ν * v * ν⁻¹) * (ν ^ j)⁻¹
              by group, ← hk', ← MulAut.conj_apply, map_pow, MulAut.conj_apply, ih, ← pow_mul,
              pow_succ]
        rw [e2 3]
        have : v ^ (2 ^ 3) = v ^ 2 := by
          rw [show (2 : ℕ) ^ 3 = 3 * 2 + 2 by norm_num, pow_add, pow_mul, hv3, one_pow, one_mul]
        exact this
      rw [hν3', one_mul, inv_one, mul_one] at e1
      apply hv1
      have : v * v = v * 1 := by rw [mul_one, ← pow_two, ← e1]
      exact mul_left_cancel this
  have hνC : ν ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff, hXv]
    rintro _ ⟨k, rfl⟩
    have : v * ν = ν * v := by
      calc v * ν = (ν * v * ν⁻¹) * ν := by rw [hνv]
        _ = ν * v := by group
    exact (Commute.zpow_left this k).eq
  exact hodd ν hνC (by rw [hν3]; decide)

end JankoHyp


end CFSG.Walter.J1
