module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructTags
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSUBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Generic

variable {G : Type} [Group G]

theorem ggRCST_eq_one_of_pow {H : Type*} [Group H] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : H}
    {k : ℕ} (h2 : x ^ 2 ^ k = 1) (hpx : x ^ p = 1) : x = 1 := by
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have h1 : orderOf x ∣ Nat.gcd (2 ^ k) p :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hpx)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem ggRCST_le_normalizer_map_ker {H : Subgroup G} {M : Type*} [MulOneClass M] (f : H →* M) :
    H ≤ Subgroup.normalizer ((f.ker.map H.subtype : Subgroup G) : Set G) := by
  have key : ∀ c (hc : c ∈ H) x, x ∈ f.ker.map H.subtype → c * x * c⁻¹ ∈ f.ker.map H.subtype := by
    rintro c hc _ ⟨y, hy, rfl⟩
    refine ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, ?_, rfl⟩
    have hy' : f y = 1 := hy
    change f (⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹) = 1
    rw [map_mul, map_mul, hy', mul_one, ← map_mul, mul_inv_cancel, map_one]
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key c hc x, fun h => ?_⟩
  have := key c⁻¹ (H.inv_mem hc) (c * x * c⁻¹) h
  rwa [inv_inv, show c⁻¹ * (c * x * c⁻¹) * c = x by group] at this

theorem ggRCST_exists_of_mem_sup {A Y : Subgroup G} (hA : A ≤ Subgroup.normalizer (Y : Set G))
    {y : G} (hy : y ∈ A ⊔ Y) : ∃ a ∈ A, ∃ w ∈ Y, y = a * w := by
  have hy' : y ∈ (↑(A ⊔ Y) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A Y hA] at hy'
  obtain ⟨a, ha, w, hw, rfl⟩ := hy'
  exact ⟨a, ha, w, hw, rfl⟩

theorem ggRCST_mem_of_mem_sup_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A Y : Subgroup G}
    (hA2 : IsPGroup 2 A) (hA : A ≤ Subgroup.normalizer (Y : Set G)) {y : G} (hy : y ∈ A ⊔ Y)
    (hyp : y ^ p = 1) : y ∈ Y := by
  obtain ⟨a, ha, w, hw, rfl⟩ := ggRCST_exists_of_mem_sup hA hy
  have hYN : Y ≤ A ⊔ Y := le_sup_right
  have hAN : A ≤ A ⊔ Y := le_sup_left
  have hYn : (Y.subgroupOf (A ⊔ Y)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYN]
    exact sup_le hA Subgroup.le_normalizer
  have haN : a ∈ A ⊔ Y := hAN ha
  have hwN : w ∈ A ⊔ Y := hYN hw
  have hφw : QuotientGroup.mk' (Y.subgroupOf (A ⊔ Y)) ⟨w, hwN⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hw
  obtain ⟨k, hk⟩ := hA2 ⟨a, ha⟩
  have hak : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set z : ↥(A ⊔ Y) := ⟨a * w, (A ⊔ Y).mul_mem haN hwN⟩ with hz
  have hz' : z = ⟨a, haN⟩ * ⟨w, hwN⟩ := rfl
  have hφz : QuotientGroup.mk' (Y.subgroupOf (A ⊔ Y)) z =
      QuotientGroup.mk' (Y.subgroupOf (A ⊔ Y)) ⟨a, haN⟩ := by
    rw [hz', map_mul, hφw, mul_one]
  have h1 : (QuotientGroup.mk' (Y.subgroupOf (A ⊔ Y)) z) ^ 2 ^ k = 1 := by
    rw [hφz, ← map_pow]
    have : (⟨a, haN⟩ : ↥(A ⊔ Y)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hak)
    rw [this, map_one]
  have h2 : (QuotientGroup.mk' (Y.subgroupOf (A ⊔ Y)) z) ^ p = 1 := by
    rw [← map_pow]
    have : z ^ p = 1 := Subtype.ext (by simpa [hz] using hyp)
    rw [this, map_one]
  have h3 := ggRCST_eq_one_of_pow hp hp2 h1 h2
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
  exact h3

theorem ggRCST_mem_of_mem_sup_coprime [Finite G] {p : ℕ} (hp : p.Prime) {A Y : Subgroup G}
    (hpA : ¬ p ∣ Nat.card A) (hA : A ≤ Subgroup.normalizer (Y : Set G)) {y : G}
    (hy : y ∈ A ⊔ Y) (hyp : y ^ p = 1) : y ∈ Y := by
  obtain ⟨a, ha, w, hw, rfl⟩ := ggRCST_exists_of_mem_sup hA hy
  have hYN : Y ≤ A ⊔ Y := le_sup_right
  have hAN : A ≤ A ⊔ Y := le_sup_left
  have hYn : (Y.subgroupOf (A ⊔ Y)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYN]
    exact sup_le hA Subgroup.le_normalizer
  have haN : a ∈ A ⊔ Y := hAN ha
  have hwN : w ∈ A ⊔ Y := hYN hw
  have hφw : QuotientGroup.mk' (Y.subgroupOf (A ⊔ Y)) ⟨w, hwN⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hw
  have hak : a ^ Nat.card A = 1 := by
    have h := pow_card_eq_one' (G := ↥A) (x := ⟨a, ha⟩)
    have h' := congrArg Subtype.val h
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h'
  set z : ↥(A ⊔ Y) := ⟨a * w, (A ⊔ Y).mul_mem haN hwN⟩ with hz
  have hz' : z = ⟨a, haN⟩ * ⟨w, hwN⟩ := rfl
  have hφz : QuotientGroup.mk' (Y.subgroupOf (A ⊔ Y)) z =
      QuotientGroup.mk' (Y.subgroupOf (A ⊔ Y)) ⟨a, haN⟩ := by
    rw [hz', map_mul, hφw, mul_one]
  have h1 : (QuotientGroup.mk' (Y.subgroupOf (A ⊔ Y)) z) ^ Nat.card A = 1 := by
    rw [hφz, ← map_pow]
    have : (⟨a, haN⟩ : ↥(A ⊔ Y)) ^ Nat.card A = 1 := Subtype.ext (by simpa using hak)
    rw [this, map_one]
  have h2 : (QuotientGroup.mk' (Y.subgroupOf (A ⊔ Y)) z) ^ p = 1 := by
    rw [← map_pow]
    have : z ^ p = 1 := Subtype.ext (by simpa [hz] using hyp)
    rw [this, map_one]
  have hcop : Nat.Coprime p (Nat.card A) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpA
  have h3 : orderOf (QuotientGroup.mk' (Y.subgroupOf (A ⊔ Y)) z) ∣ Nat.gcd p (Nat.card A) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h3
  exact h3

theorem ggRCST_mem_normalizer_sup {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem ggRCST_pCoreOf_eq {X Q M : Subgroup G} (hX : X = Q ⊔ M) (hQ2 : IsPGroup 2 Q)
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hM : ∀ N : Subgroup G, N ≤ M → IsPGroup 2 N → M ≤ Subgroup.normalizer (N : Set G) → N = ⊥) :
    CFSG.Assembly.pCoreOf 2 X = Q := by
  have hQX : Q ≤ X := hX ▸ le_sup_left
  have hMX : M ≤ X := hX ▸ le_sup_right
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := hX ▸ sup_le Subgroup.le_normalizer hMQ
  have hXP : X ≤ Subgroup.normalizer (CFSG.Assembly.pCoreOf 2 X : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hQP : Q ≤ CFSG.Assembly.pCoreOf 2 X := by
    have hQn : (Q.subgroupOf X).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQX]
      exact hXQ
    have hQ2X : IsPGroup 2 (Q.subgroupOf X) := hQ2.comap_of_injective X.subtype X.subtype_injective
    have h1 := Dichotomy.CentralizerContainment.le_pCore_assembly hQn hQ2X
    intro q hq
    exact ⟨⟨q, hQX hq⟩, h1 (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  refine le_antisymm (fun x hx => ?_) hQP
  have hxX : x ∈ Q ⊔ M := hX ▸ (Subgroup.map_subtype_le _ hx)
  obtain ⟨m, hm, q, hq, rfl⟩ := ggRCST_exists_of_mem_sup hMQ (by rwa [sup_comm] at hxX)
  have hmP : m ∈ CFSG.Assembly.pCoreOf 2 X := by
    have := (CFSG.Assembly.pCoreOf 2 X).mul_mem hx ((CFSG.Assembly.pCoreOf 2 X).inv_mem (hQP hq))
    simpa using this
  have hN := hM (CFSG.Assembly.pCoreOf 2 X ⊓ M) inf_le_right
    ((ggIsPGroup_pCoreOf 2 X).to_le inf_le_left)
    (le_trans (le_inf (hMX.trans hXP) Subgroup.le_normalizer)
      Subgroup.inf_normalizer_le_normalizer_inf)
  have hm1 : m = 1 := by
    have : m ∈ CFSG.Assembly.pCoreOf 2 X ⊓ M := ⟨hmP, hm⟩
    rw [hN] at this
    exact this
  rw [hm1, one_mul]
  exact hq

theorem ggRCST_not_dvd_card_sup [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q L : Subgroup G} (hQ2 : IsPGroup 2 Q) (hL : L ≤ Subgroup.normalizer (Q : Set G))
    (hpL : ¬ p ∣ Nat.card L) : ¬ p ∣ Nat.card ↥(Q ⊔ L) := by
  have hQN : Q ≤ Q ⊔ L := le_sup_left
  have hLN : L ≤ Q ⊔ L := le_sup_right
  have hQn : (Q.subgroupOf (Q ⊔ L)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQN]
    exact sup_le Subgroup.le_normalizer hL
  set f : ↥L →* ↥(Q ⊔ L) ⧸ Q.subgroupOf (Q ⊔ L) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hLN) with hf
  have hfs : Function.Surjective f := by
    intro z
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective _ z
    have hx' : x ∈ L ⊔ Q := by rwa [sup_comm] at hx
    obtain ⟨l, hl, q, hq, rfl⟩ := ggRCST_exists_of_mem_sup hL hx'
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hq
  have hdvd : Nat.card (↥(Q ⊔ L) ⧸ Q.subgroupOf (Q ⊔ L)) ∣ Nat.card L :=
    Subgroup.card_dvd_of_surjective hfs
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf (Q ⊔ L))
  have hQc : Nat.card (Q.subgroupOf (Q ⊔ L)) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv
  intro hpN
  rw [hcard, hQc] at hpN
  rcases (Nat.Prime.dvd_mul hp).mp hpN with h | h
  · exact hpL (h.trans hdvd)
  · exact ggNot_dvd_card_of_isPGroup_two hp hp2 hQ2 h

theorem ggRCST_isQuasisimple_quot [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q L Y Q₁ : Subgroup G} (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hLY : L ≤ Y)
    (hY : Y ≤ Q ⊔ L) (hQ₁2 : IsPGroup 2 Q₁) (hYQ : Y ⊓ Q ≤ Q₁)
    (hL : CFSG.IsQuasisimple L) (hpL : p ∣ Nat.card L) [(Q₁.subgroupOf Y).Normal] :
    CFSG.IsQuasisimple (↥Y ⧸ Q₁.subgroupOf Y) := by
  set f : ↥L →* ↥Y ⧸ Q₁.subgroupOf Y := (QuotientGroup.mk' _).comp (Subgroup.inclusion hLY)
    with hf
  have hfs : Function.Surjective f := by
    intro z
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective _ z
    have hy' : y ∈ L ⊔ Q := by
      have := hY hy
      rwa [sup_comm] at this
    obtain ⟨l, hl, q, hq, rfl⟩ := ggRCST_exists_of_mem_sup hLQ hy'
    have hqY : q ∈ Y := by
      have := Y.mul_mem (Y.inv_mem (hLY hl)) hy
      simpa using this
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : (l : G)⁻¹ * (l * q) = q := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    rw [this]
    exact hYQ ⟨hqY, hq⟩
  have hker : IsPGroup 2 f.ker := by
    rintro ⟨l, hl⟩
    have h1 : (Subgroup.inclusion hLY l : ↥Y) ∈ Q₁.subgroupOf Y := by
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hl
      exact hl
    rw [Subgroup.mem_subgroupOf] at h1
    obtain ⟨k, hk⟩ := hQ₁2 ⟨_, h1⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  exact ggRCSS_isQuasisimple_of_surjective hp hp2 hL hpL f hfs hker

theorem ggRCST_map_le_normalizer {U : Type*} [Group U] (ψ : U →* G) {A B : Subgroup U}
    (h : A ≤ Subgroup.normalizer (B : Set U)) :
    A.map ψ ≤ Subgroup.normalizer ((B.map ψ : Subgroup G) : Set G) := by
  have key : ∀ a ∈ A, ∀ x ∈ B.map ψ, ψ a * x * (ψ a)⁻¹ ∈ B.map ψ := by
    rintro a ha _ ⟨b, hb, rfl⟩
    exact ⟨a * b * a⁻¹, (Subgroup.mem_normalizer_iff.mp (h ha) b).mp hb, by simp⟩
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key a ha x, fun hx => ?_⟩
  have := key a⁻¹ (A.inv_mem ha) _ hx
  rwa [map_inv, inv_inv, show (ψ a)⁻¹ * (ψ a * x * (ψ a)⁻¹) * ψ a = x by group] at this

theorem ggRCST_mem_centralizer_of_map {U : Type*} [Group U] {ψ : U →* G}
    (hker : ψ.ker ≤ Subgroup.center U) (hZ : ∀ z ∈ Subgroup.center U, z ^ 2 = 1 → z = 1)
    {T B : U} (hT : T * T = 1) (h : ψ B ∈ Subgroup.centralizer {ψ T}) :
    B ∈ Subgroup.centralizer {T} := by
  rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
  set c := B * T * B⁻¹ with hc
  set z := c * T⁻¹ with hz
  have h1 : ψ c = ψ T := by
    rw [hc, map_mul, map_mul, map_inv, h, mul_inv_cancel_right]
  have hzc : z ∈ Subgroup.center U :=
    hker (by rw [MonoidHom.mem_ker, hz, map_mul, h1, map_inv, mul_inv_cancel])
  have hc2 : c * c = 1 := by
    rw [hc, show B * T * B⁻¹ * (B * T * B⁻¹) = B * (T * T) * B⁻¹ by group, hT, mul_one,
      mul_inv_cancel]
  have hcz : c = z * T := by rw [hz, inv_mul_cancel_right]
  have hz2 : z ^ 2 = 1 := by
    have hzT : T * z = z * T := Subgroup.mem_center_iff.mp hzc T
    calc z ^ 2 = z * z * (T * T) := by rw [hT, mul_one, pow_two]
      _ = z * (T * z) * T := by rw [hzT]; group
      _ = c * c := by rw [hcz]; group
      _ = 1 := hc2
  have hz1 : z = 1 := hZ z hzc hz2
  have hcT : c = T := by rw [hcz, hz1, one_mul]
  calc B * T = (B * T * B⁻¹) * B := by group
    _ = T * B := by rw [← hc, hcT]

theorem ggRCST_range_inf_centralizer {U : Type*} [Group U] {ψ : U →* G}
    (hker : ψ.ker ≤ Subgroup.center U) (hZ : ∀ z ∈ Subgroup.center U, z ^ 2 = 1 → z = 1)
    {T : U} (hT : T * T = 1) :
    ψ.range ⊓ Subgroup.centralizer {ψ T} = (Subgroup.centralizer {T}).map ψ := by
  apply le_antisymm
  · rintro _ ⟨⟨B, rfl⟩, hB⟩
    exact ⟨B, ggRCST_mem_centralizer_of_map hker hZ hT hB, rfl⟩
  · rintro _ ⟨B, hB, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨⟨B, rfl⟩, ?_⟩
    have hB' : B * T = T * B := Subgroup.mem_centralizer_singleton_iff.mp hB
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, hB', map_mul]

theorem ggRCST_ggRCSX_le_map {U : Type*} [Group U] {ψ : U →* G}
    (hker : ψ.ker ≤ Subgroup.center U) (hZ : ∀ z ∈ Subgroup.center U, z ^ 2 = 1 → z = 1)
    {T : U} (hT : T * T = 1) {K : Subgroup U} {m : ℕ} (hm : Odd m)
    (hK : ∀ c ∈ Subgroup.centralizer {T}, c ^ m ∈ K) : ggRCSX ψ.range (ψ T) ≤ K.map ψ := by
  rw [ggRCSX, ggOTwoPrime, Subgroup.closure_le]
  rintro y ⟨hy, j, hj⟩
  rw [ggRCST_range_inf_centralizer hker hZ hT] at hy
  obtain ⟨c, hc, rfl⟩ := hy
  have hcop : m.Coprime (orderOf (ψ c)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hj)
      (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hm))
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  rw [SetLike.mem_coe, ← hu, ← map_pow, ← map_pow]
  exact ⟨_, pow_mem (hK c hc) u, rfl⟩

theorem ggRCST_map_le_ggRCSX_of_isPGroup {U : Type*} [Group U] (ψ : U →* G) {T : U}
    {P : Subgroup U} (hPC : P ≤ Subgroup.centralizer {T}) (hP : IsPGroup 2 P) :
    P.map ψ ≤ ggRCSX ψ.range (ψ T) := by
  refine OTwoGen.le_ggOTwoPrime_of_isPGroup ?_ (hP.map ψ)
  rintro _ ⟨x, hx, rfl⟩
  refine Subgroup.mem_inf.mpr ⟨⟨x, rfl⟩, ?_⟩
  have := hPC hx
  rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
  rw [← map_mul, this, map_mul]

theorem ggRCST_range_le_ggRCSX {U M : Type*} [Group U] [Group M] (ψ : U →* G) {T : U}
    (φ : M →* U) (hφ : φ.range ≤ Subgroup.centralizer {T})
    (hM : (⊤ : Subgroup M) ≤ Subgroup.closure {x : M | ∃ k : ℕ, x ^ (2 ^ k) = 1}) :
    (ψ.comp φ).range ≤ ggRCSX ψ.range (ψ T) := by
  refine OTwoGen.range_le_ggOTwoPrime (ψ.comp φ) ?_ hM
  rintro _ ⟨x, rfl⟩
  refine Subgroup.mem_inf.mpr ⟨⟨φ x, rfl⟩, ?_⟩
  have := hφ ⟨x, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
  rw [MonoidHom.comp_apply, ← map_mul, this, map_mul]

theorem ggRCST_ggRCSX_le_normalizer {U : Type*} [Group U] {ψ : U →* G}
    (hker : ψ.ker ≤ Subgroup.center U) (hZ : ∀ z ∈ Subgroup.center U, z ^ 2 = 1 → z = 1)
    {T : U} (hT : T * T = 1) {P : Subgroup U}
    (hP : Subgroup.centralizer {T} ≤ Subgroup.normalizer (P : Set U)) :
    ggRCSX ψ.range (ψ T) ≤ Subgroup.normalizer ((P.map ψ : Subgroup G) : Set G) := by
  refine (ggOTwoPrime_le _).trans ?_
  rw [ggRCST_range_inf_centralizer hker hZ hT]
  exact ggRCST_map_le_normalizer ψ hP

theorem ggRCST_isQuasisimple_range {M : Type*} [Group M] (φ : M →* G)
    (hM : CFSG.IsQuasisimple M) (hker : φ.ker ≤ Subgroup.center M) :
    CFSG.IsQuasisimple φ.range := by
  refine CFSG.LocalCores.isQuasisimple_of_surjective hM φ.rangeRestrict φ.rangeRestrict_surjective
    ?_
  rw [MonoidHom.ker_rangeRestrict]
  exact hker

end Generic

section Derived

variable {G : Type} [Group G] [Finite G]

theorem ggRootCentDerivedAt_of_not_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G₀ : Subgroup G}
    {r : G} {Q L₀ : Subgroup G} (hQ2 : IsPGroup 2 Q) (hL₀Q : L₀ ≤ Subgroup.normalizer (Q : Set G))
    (hX : ggRCSX G₀ r ≤ Q ⊔ L₀) (hpL : ¬ p ∣ Nat.card L₀) : GGRootCentDerivedAt p G₀ r :=
  Or.inl fun _ hy hyp =>
    ggRCS_eq_one_of_not_dvd hp (ggRCST_not_dvd_card_sup hp hp2 hQ2 hL₀Q hpL) (hX hy) hyp

theorem ggRootCentDerivedAt_of_quasisimple {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G₀ : Subgroup G} {r : G} {Q L₀ : Subgroup G} (hQX : Q ≤ ggRCSX G₀ r) (hQ2 : IsPGroup 2 Q)
    (hXQ : ggRCSX G₀ r ≤ Subgroup.normalizer (Q : Set G)) (hL₀X : L₀ ≤ ggRCSX G₀ r)
    (hL₀ : CFSG.IsQuasisimple L₀) (hY : ggRCSXd G₀ r ≤ Q ⊔ L₀)
    (hcov : ∀ y ∈ ggRCSX G₀ r, y ^ p = 1 → y ∈ Q ⊔ L₀) : GGRootCentDerivedAt p G₀ r := by
  have hL₀Q : L₀ ≤ Subgroup.normalizer (Q : Set G) := hL₀X.trans hXQ
  by_cases hpL : p ∣ Nat.card L₀
  swap
  · exact Or.inl fun y hy hyp =>
      ggRCS_eq_one_of_not_dvd hp (ggRCST_not_dvd_card_sup hp hp2 hQ2 hL₀Q hpL) (hcov y hy hyp) hyp
  have hperf : ⁅L₀, L₀⁆ = L₀ := Subgroup.isPerfect_iff.mp hL₀.1
  have hL₀Y : L₀ ≤ ggRCSXd G₀ r := CFSG.Quasithin.le_perfectCore_of_perfect hL₀X hperf
  have hYX : ggRCSXd G₀ r ≤ ggRCSX G₀ r := CFSG.Quasithin.perfectCore_le _
  have hXY : ggRCSX G₀ r ≤ Subgroup.normalizer (ggRCSXd G₀ r : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _)
  have hQ₁2 : IsPGroup 2 ↥(ggRCSXd G₀ r ⊓ Q) := hQ2.to_le inf_le_right
  have hQ₁n : ((ggRCSXd G₀ r ⊓ Q).subgroupOf (ggRCSXd G₀ r)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact le_trans (le_inf Subgroup.le_normalizer (hYX.trans hXQ))
      (Subgroup.inf_normalizer_le_normalizer_inf)
  refine Or.inr (Or.inl ⟨dvd_trans hpL (Subgroup.card_dvd_of_le hL₀Y),
    ⟨ggRCSXd G₀ r ⊓ Q, inf_le_left, hQ₁2, hQ₁n, ?_⟩, fun y hy hyp => ?_⟩)
  · intro _
    exact ggRCST_isQuasisimple_quot hp hp2 hL₀Q hL₀Y hY hQ₁2 le_rfl hL₀ hpL
  · have hy' : y ∈ Q ⊔ ggRCSXd G₀ r := (sup_le_sup_left hL₀Y Q) (hcov y hy hyp)
    exact ggRCST_mem_of_mem_sup_two hp hp2 hQ2 (hQX.trans hXY) hy' hyp

theorem ggRCSLayer_of_two_summands {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G₀ M : Subgroup G}
    (hG₀M : G₀ ≤ M) (hM : M ≤ Subgroup.normalizer (G₀ : Set G)) {r : G} {Q L₁ L₂ : Subgroup G}
    (hQ2 : IsPGroup 2 Q) (hO2 : CFSG.Assembly.pCoreOf 2 (ggRCSX G₀ r) = Q)
    (hX : ggRCSX G₀ r = Q ⊔ L₁ ⊔ L₂) (hL₁Q : L₁ ≤ Subgroup.normalizer (Q : Set G))
    (hL₂Q : L₂ ≤ Subgroup.normalizer (Q : Set G))
    (hcomm : L₁ ≤ Subgroup.centralizer (L₂ : Set G)) (hL₁ : CFSG.IsQuasisimple L₁)
    (hL₂ : CFSG.IsQuasisimple L₂) (hQ₁ : Q ≤ ⁅Q ⊔ L₁, Q ⊔ L₁⁆) (hQ₂ : Q ≤ ⁅Q ⊔ L₂, Q ⊔ L₂⁆) :
    GGRCSLayer p G₀ M r := by
  set X := ggRCSX G₀ r with hXdef
  set V := M ⊓ Subgroup.centralizer ({r} : Set G) with hV
  have hXV : X ≤ V := (ggOTwoPrime_le _).trans (inf_le_inf_right _ hG₀M)
  have hVX : V ≤ Subgroup.normalizer (X : Set G) := fun c hc =>
    ggMem_normalizer_oTwoPrime_inf_centralizer (hM hc.1) hc.2
  have hVQ : V ≤ Subgroup.normalizer (Q : Set G) := by
    rw [← hO2]
    exact hVX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hQX : Q ≤ X := by rw [hX]; exact le_sup_left.trans le_sup_left
  have hL₁X : L₁ ≤ X := by rw [hX]; exact le_sup_right.trans le_sup_left
  have hL₂X : L₂ ≤ X := by rw [hX]; exact le_sup_right
  have hXsn : IsSubnormal X V :=
    ggIsSubnormal_of_normal hXV ((Subgroup.normal_subgroupOf_iff_le_normalizer hXV).mpr hVX)
  have hcomm' : L₂ ≤ Subgroup.centralizer (L₁ : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact ((Subgroup.mem_centralizer_iff.mp (hcomm ha)) b hb).symm
  have piece : ∀ L L' : Subgroup G, L ≤ Subgroup.normalizer (Q : Set G) →
      L' ≤ Subgroup.normalizer (Q : Set G) → L' ≤ Subgroup.centralizer (L : Set G) →
      L ≤ X → CFSG.IsQuasisimple L → Q ≤ ⁅Q ⊔ L, Q ⊔ L⁆ → X ≤ Q ⊔ L ⊔ L' → p ∣ Nat.card L →
      GGRCSLayerPiece p V (Q ⊔ L) := by
    intro L L' hLQ hL'Q hL'L hLX hLq hQL hXL hpL
    have hYX : Q ⊔ L ≤ X := sup_le hQX hLX
    have hXN : X ≤ Subgroup.normalizer ((Q ⊔ L : Subgroup G) : Set G) := by
      refine hXL.trans (sup_le (sup_le ?_ ?_) ?_)
      · exact le_sup_left.trans Subgroup.le_normalizer
      · exact le_sup_right.trans Subgroup.le_normalizer
      · intro g hg
        exact ggRCST_mem_normalizer_sup (hL'Q hg)
          (Subgroup.centralizer_le_normalizer _ (hL'L hg))
    have hperfL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLq.1
    refine Or.inl ⟨Q, hYX.trans hXV, ?_, ?_, ?_, le_sup_left, hQ2, hVQ, ?_⟩
    · exact ggIsSubnormal_trans
        (ggIsSubnormal_of_normal hYX ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hXN))
        hXsn
    · refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le hQL ?_)
      calc L = ⁅L, L⁆ := hperfL.symm
        _ ≤ ⁅Q ⊔ L, Q ⊔ L⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
    · exact dvd_trans hpL (Subgroup.card_dvd_of_le le_sup_right)
    · intro _
      exact ggRCST_isQuasisimple_quot hp hp2 hLQ le_sup_right le_rfl hQ2 inf_le_right hLq hpL
  have hX₁ : X ≤ Q ⊔ L₁ ⊔ L₂ := hX.le
  have hX₂ : X ≤ Q ⊔ L₂ ⊔ L₁ := by rw [hX, sup_right_comm]
  refine ⟨{Y | (Y = Q ⊔ L₁ ∧ p ∣ Nat.card L₁) ∨ (Y = Q ⊔ L₂ ∧ p ∣ Nat.card L₂)}, ?_, ?_⟩
  · rintro Y (⟨rfl, hp1⟩ | ⟨rfl, hp1⟩)
    · exact piece L₁ L₂ hL₁Q hL₂Q hcomm' hL₁X hL₁ hQ₁ hX₁ hp1
    · exact piece L₂ L₁ hL₂Q hL₁Q hcomm hL₂X hL₂ hQ₂ hX₂ hp1
  · intro y hy hyp
    have hmem₁ : p ∣ Nat.card L₁ → Q ⊔ L₁ ≤ sSup {Y | (Y = Q ⊔ L₁ ∧ p ∣ Nat.card L₁) ∨
        (Y = Q ⊔ L₂ ∧ p ∣ Nat.card L₂)} := fun h => le_sSup (Or.inl ⟨rfl, h⟩)
    have hmem₂ : p ∣ Nat.card L₂ → Q ⊔ L₂ ≤ sSup {Y | (Y = Q ⊔ L₁ ∧ p ∣ Nat.card L₁) ∨
        (Y = Q ⊔ L₂ ∧ p ∣ Nat.card L₂)} := fun h => le_sSup (Or.inr ⟨rfl, h⟩)
    have hN₁ : L₂ ≤ Subgroup.normalizer ((Q ⊔ L₁ : Subgroup G) : Set G) := fun g hg =>
      ggRCST_mem_normalizer_sup (hL₂Q hg) (Subgroup.centralizer_le_normalizer _ (hcomm' hg))
    have hN₂ : L₁ ≤ Subgroup.normalizer ((Q ⊔ L₂ : Subgroup G) : Set G) := fun g hg =>
      ggRCST_mem_normalizer_sup (hL₁Q hg) (Subgroup.centralizer_le_normalizer _ (hcomm hg))
    have hy₁ : y ∈ L₂ ⊔ (Q ⊔ L₁) := by rw [sup_comm]; exact hX₁ hy
    have hy₂ : y ∈ L₁ ⊔ (Q ⊔ L₂) := by rw [sup_comm]; exact hX₂ hy
    by_cases hp1 : p ∣ Nat.card L₁ <;> by_cases hp2' : p ∣ Nat.card L₂
    · exact sup_le (sup_le ((hmem₁ hp1).trans' le_sup_left) ((hmem₁ hp1).trans' le_sup_right))
        ((hmem₂ hp2').trans' le_sup_right) (hX₁ hy)
    · exact hmem₁ hp1 (ggRCST_mem_of_mem_sup_coprime hp hp2' hN₁ hy₁ hyp)
    · exact hmem₂ hp2' (ggRCST_mem_of_mem_sup_coprime hp hp1 hN₂ hy₂ hyp)
    · have h1 := ggRCST_mem_of_mem_sup_coprime hp hp2' hN₁ hy₁ hyp
      rw [ggRCS_eq_one_of_not_dvd hp (ggRCST_not_dvd_card_sup hp hp2 hQ2 hL₁Q hp1) h1 hyp]
      exact one_mem _

omit [Finite G] in
theorem ggRootCentDerivedAt_of_sThree {p : ℕ} {G₀ : Subgroup G} {r : G} {Q : Subgroup G}
    {M : Type*} [Group M] (φ : M →* G) (e : M ≃* Equiv.Perm (Fin 3))
    (hQX : Q ≤ ggRCSX G₀ r) (hQ2 : IsPGroup 2 Q)
    (hXQ : ggRCSX G₀ r ≤ Subgroup.normalizer (Q : Set G)) (hφX : φ.range ≤ ggRCSX G₀ r)
    (hX : ggRCSX G₀ r ≤ Q ⊔ φ.range) (hφQ : ∀ m, φ m ∈ Q → ∃ j : ℕ, m ^ 2 ^ j = 1) :
    GGRootCentDerivedAt p G₀ r := by
  set X := ggRCSX G₀ r with hXdef
  have hQn : (Q.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQX]
    exact hXQ
  refine Or.inr (Or.inr ⟨Q, hQX, hQ2, hQn, ?_⟩)
  intro _
  have hmem : ∀ m, φ m ∈ X := fun m => hφX ⟨m, rfl⟩
  set f : M →* ↥X ⧸ Q.subgroupOf X := (QuotientGroup.mk' _).comp (φ.codRestrict X hmem) with hf
  have hfs : Function.Surjective f := by
    intro z
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective _ z
    have hx' : x ∈ φ.range ⊔ Q := by
      have := hX hx
      rwa [sup_comm] at this
    obtain ⟨_, ⟨m, rfl⟩, q, hq, rfl⟩ := ggRCST_exists_of_mem_sup (hφX.trans hXQ) hx'
    refine ⟨m, ?_⟩
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hq
  have hker2 : IsPGroup 2 f.ker := by
    rintro ⟨m, hm⟩
    have h1 : φ m ∈ Q := by
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hm
      exact hm
    obtain ⟨j, hj⟩ := hφQ m h1
    exact ⟨j, Subtype.ext (by simpa using hj)⟩
  have hbot : f.ker.map e.toMonoidHom = ⊥ :=
    ggRCSS_perm_three_normal_two _ ((MonoidHom.normal_ker f).map e.toMonoidHom e.surjective)
      (hker2.map _)
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hbot
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hfs⟩).symm.trans e⟩

end Derived

end CFSG.StandardType
