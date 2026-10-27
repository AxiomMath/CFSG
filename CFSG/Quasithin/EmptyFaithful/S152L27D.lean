module

public import CFSG.Quasithin.EmptyFaithful.S152L27A
public import CFSG.Quasithin.EmptyFaithful.S152L27C

public section

namespace CFSG.Quasithin

section Quotient

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
private theorem exists_three_lift152 {Q : Subgroup Y} [Q.Normal] (hQ : IsPGroup 2 Q) (x : Y) (k : ℕ)
    (hk : orderOf (QuotientGroup.mk' Q x) = 3 ^ k) :
    ∃ x₃ : Y, QuotientGroup.mk' Q x₃ = QuotientGroup.mk' Q x ∧ ∃ i : ℕ, orderOf x₃ = 3 ^ i := by
  set π := QuotientGroup.mk' Q with hπ
  have hπk : π x ^ 3 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
  have hxk : x ^ 3 ^ k ∈ Q := by
    have h : π (x ^ 3 ^ k) = 1 := by rw [map_pow]; exact hπk
    exact (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨j, hj⟩ := hQ ⟨x ^ 3 ^ k, hxk⟩
  have hx1 : x ^ (3 ^ k * 2 ^ j) = 1 := by
    have := congrArg (fun y : Q => (y : Y)) hj
    simpa [pow_mul] using this
  have hcop : IsCoprime ((3 ^ k : ℕ) : ℤ) ((2 ^ j : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow k j (by norm_num))
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : x = x ^ (u * ((3 ^ k : ℕ) : ℤ)) * x ^ (v * ((2 ^ j : ℕ) : ℤ)) := by
    rw [← zpow_add, huv, zpow_one]
  refine ⟨x ^ (v * ((2 ^ j : ℕ) : ℤ)), ?_, ?_⟩
  · have e1 : π (x ^ (u * ((3 ^ k : ℕ) : ℤ))) = 1 := by
      rw [map_zpow, zpow_mul', zpow_natCast, hπk, one_zpow]
    calc π (x ^ (v * ((2 ^ j : ℕ) : ℤ))) = 1 * π (x ^ (v * ((2 ^ j : ℕ) : ℤ))) := by rw [one_mul]
      _ = π (x ^ (u * ((3 ^ k : ℕ) : ℤ))) * π (x ^ (v * ((2 ^ j : ℕ) : ℤ))) := by rw [e1]
      _ = π x := by rw [← map_mul, ← h1]
  · have h3 : (x ^ (v * ((2 ^ j : ℕ) : ℤ))) ^ 3 ^ k = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have : v * ((2 ^ j : ℕ) : ℤ) * ((3 ^ k : ℕ) : ℤ) = ((3 ^ k * 2 ^ j : ℕ) : ℤ) * v := by
        push_cast; ring
      rw [this, zpow_mul, zpow_natCast, hx1, one_zpow]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3)
    exact ⟨i, hi⟩

theorem le_pCore_of_commutes_mod_pCore152 {K N V : Subgroup Y} (hK : K.Normal)
    (h3 : ∀ x : Y, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ K)
    (hO3 : ∀ W : Subgroup Y, W.Normal → ¬ 3 ∣ Nat.card W → W ≤ N)
    (hV2 : IsPGroup 2 V) (hVN : ∀ n ∈ N, ∀ v ∈ V, n * v * n⁻¹ ∈ V)
    (hcomm : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ * v⁻¹ ∈ CFSG.pCore 2 Y) :
    V ≤ CFSG.pCore 2 Y := by
  set Q := CFSG.pCore 2 Y with hQdef
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have : Q.Normal := CFSG.pCore_normal
  let π : Y →* Y ⧸ Q := QuotientGroup.mk' Q
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hker : π.ker = Q := QuotientGroup.ker_mk' Q
  have hY2 : ∀ W : Subgroup (Y ⧸ Q), W.Normal → IsPGroup 2 W → W = ⊥ := by
    intro W hW hW2
    have hc2 : IsPGroup 2 (W.comap π) := hW2.comap_of_ker_isPGroup π (by rw [hker]; exact hQ2)
    have hcn : (W.comap π).Normal := hW.comap π
    have hle : W.comap π ≤ Q := le_sSup ⟨hcn, hc2⟩
    rw [← Subgroup.map_comap_eq_self_of_surjective hπ W, eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff y).mpr (hle hy)
  have hKn : (K.map π).Normal := hK.map π hπ
  have h3' : ∀ x : Y ⧸ Q, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ K.map π := by
    rintro x ⟨k, hk⟩
    obtain ⟨y, rfl⟩ := hπ x
    obtain ⟨x₃, hx₃, i, hi⟩ := exists_three_lift152 hQ2 y k hk
    exact ⟨x₃, h3 x₃ ⟨i, hi⟩, hx₃⟩
  have hA : ∀ W : Subgroup (Y ⧸ Q), W.Normal → ¬ 3 ∣ Nat.card W → W ≤ N.map π := by
    intro W hW hnd
    have hcn : (W.comap π).Normal := hW.comap π
    have hnd' : ¬ 3 ∣ Nat.card (W.comap π) := by
      intro hd
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(W.comap π)) 3 hd
      have hyW : π (y : Y) ∈ W := y.2
      have hord : orderOf (π (y : Y)) ∣ 3 := by
        rw [← hy, ← Subgroup.orderOf_coe]
        exact orderOf_map_dvd π _
      have hy1 : π (y : Y) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
        · exact orderOf_eq_one_iff.mp h
        · exfalso
          apply hnd
          have := Subgroup.orderOf_dvd_natCard W hyW
          rw [h] at this
          exact this
      have hyQ : (y : Y) ∈ Q := (QuotientGroup.eq_one_iff _).mp hy1
      have hy3 : orderOf (y : Y) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
      have := eq_one_of_odd_of_mem_pGroup hQ2 hyQ (by rw [hy3]; decide)
      rw [this, orderOf_one] at hy3
      omega
    have := hO3 _ hcn hnd'
    rw [← Subgroup.map_comap_eq_self_of_surjective hπ W]
    exact Subgroup.map_mono this
  have hV2' : IsPGroup 2 (V.map π) := hV2.map π
  have hVA : ∀ a ∈ N.map π, ∀ v ∈ V.map π, a * v * a⁻¹ ∈ V.map π := by
    rintro _ ⟨n, hn, rfl⟩ _ ⟨v, hv, rfl⟩
    exact ⟨n * v * n⁻¹, hVN n hn v hv, by simp⟩
  have hKV : ∀ k ∈ K.map π, ∀ v ∈ V.map π, k * v = v * k := by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨v, hv, rfl⟩
    have h := (QuotientGroup.eq_one_iff _).mpr (hcomm k hk v hv)
    have h' : π (k * v * k⁻¹ * v⁻¹) = 1 := h
    simp only [map_mul, map_inv] at h'
    calc π k * π v = (π k * π v * (π k)⁻¹ * (π v)⁻¹) * (π v * π k) := by group
      _ = π v * π k := by rw [h']; simp
  have hbot := eq_bot_of_normalizes_of_centralizes152 hY2 hKn h3' hA hV2' hVA hKV
  intro v hv
  have : π v ∈ V.map π := ⟨v, hv, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff v).mp this

end Quotient

section Ambient

variable {G : Type*} [Group G] [Finite G]

theorem le_pCoreOf_of_commutes152 {Mc Kc N V : Subgroup G} (hKcMc : Kc ≤ Mc)
    (hKcn : Mc ≤ Subgroup.normalizer (Kc : Set G))
    (h3 : ∀ x ∈ Mc, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ Kc)
    (hO3 : ∀ W : Subgroup G, W ≤ Mc → Mc ≤ Subgroup.normalizer (W : Set G) → ¬ 3 ∣ Nat.card W →
      W ≤ N)
    (hVMc : V ≤ Mc) (hV2 : IsPGroup 2 V) (hVN : ∀ n ∈ N, ∀ v ∈ V, n * v * n⁻¹ ∈ V)
    (hcomm : ∀ k ∈ Kc, ∀ v ∈ V, k * v * k⁻¹ * v⁻¹ ∈ CFSG.Open.pCoreOf 2 Mc) :
    V ≤ CFSG.Open.pCoreOf 2 Mc := by
  have hpc : ∀ y : ↥Mc, y ∈ CFSG.pCore 2 ↥Mc ↔ (y : G) ∈ CFSG.Open.pCoreOf 2 Mc := by
    intro y
    unfold CFSG.Open.pCoreOf
    constructor
    · intro hy; exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have : z = y := Subtype.ext hzy
      exact this ▸ hz
  have key := le_pCore_of_commutes_mod_pCore152 (Y := ↥Mc) (K := Kc.subgroupOf Mc)
    (N := N.subgroupOf Mc) (V := V.subgroupOf Mc)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKcMc).mpr hKcn)
    (fun x ⟨k, hk⟩ => Subgroup.mem_subgroupOf.mpr
      (h3 x x.2 ⟨k, by rw [Subgroup.orderOf_coe]; exact hk⟩))
    (fun W' hW' hnd => by
      have hWMc : W'.map Mc.subtype ≤ Mc := Subgroup.map_subtype_le W'
      have hWn : Mc ≤ Subgroup.normalizer ((W'.map Mc.subtype : Subgroup G) : Set G) := by
        intro g hg
        rw [Subgroup.mem_normalizer_iff]
        have key : ∀ g ∈ Mc, ∀ w ∈ W'.map Mc.subtype, g * w * g⁻¹ ∈ W'.map Mc.subtype := by
          rintro g hg _ ⟨w, hw, rfl⟩
          exact ⟨⟨g, hg⟩ * w * ⟨g, hg⟩⁻¹, hW'.conj_mem w hw ⟨g, hg⟩, by simp⟩
        intro w
        refine ⟨key g hg w, fun hw => ?_⟩
        have := key g⁻¹ (Mc.inv_mem hg) _ hw
        simpa [mul_assoc] using this
      have hcard : Nat.card (W'.map Mc.subtype) = Nat.card W' :=
        Subgroup.card_map_of_injective Mc.subtype_injective
      have hle := hO3 _ hWMc hWn (by rw [hcard]; exact hnd)
      intro w hw
      exact Subgroup.mem_subgroupOf.mpr (hle ⟨w, hw, rfl⟩))
    (hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVMc).symm)
    (by
      intro n hn v hv
      exact Subgroup.mem_subgroupOf.mpr (hVN n (Subgroup.mem_subgroupOf.mp hn) v
        (Subgroup.mem_subgroupOf.mp hv)))
    (by
      intro k hk v hv
      exact (hpc _).mpr (hcomm k (Subgroup.mem_subgroupOf.mp hk) v (Subgroup.mem_subgroupOf.mp hv)))
  intro v hv
  exact (hpc ⟨v, hVMc hv⟩).mp (key (Subgroup.mem_subgroupOf.mpr hv))

end Ambient

end CFSG.Quasithin
