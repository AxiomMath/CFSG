module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.A10

open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem card_modEq_card_inf_centralizer [Finite G] {p : ℕ} [Fact p.Prime] {B : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (B : Set G)) (hp : IsPGroup p (Subgroup.zpowers g)) :
    Nat.card B ≡ Nat.card ↥(B ⊓ Subgroup.centralizer ({g} : Set G)) [MOD p] := by
  set g' : Subgroup.normalizer (B : Set G) := ⟨g, hg⟩ with hg'
  have hP : IsPGroup p (Subgroup.zpowers g') := by
    intro x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 x.2
    have hx : (g ^ n : G) ∈ Subgroup.zpowers g := Subgroup.zpow_mem_zpowers g n
    obtain ⟨k, hk⟩ := hp ⟨g ^ n, hx⟩
    refine ⟨k, ?_⟩
    have hk' : (g ^ n) ^ p ^ k = 1 := congrArg Subtype.val hk
    apply Subtype.ext
    apply Subtype.ext
    have h1 : ((x : Subgroup.normalizer (B : Set G)) : G) = g ^ n := by
      rw [← hn]; rfl
    show ((x : Subgroup.normalizer (B : Set G)) : G) ^ p ^ k = 1
    rw [h1]; exact hk'
  have hmod := hP.card_modEq_card_fixedPoints B
  have key : ∀ b : B, b ∈ MulAction.fixedPoints (Subgroup.zpowers g') B ↔
      g * (b : G) = (b : G) * g := by
    intro b
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      have h1 := h ⟨g', Subgroup.mem_zpowers g'⟩
      have h2 : ((⟨g', Subgroup.mem_zpowers g'⟩ : Subgroup.zpowers g') • b : B) = b := h1
      have h3 : (((⟨g', Subgroup.mem_zpowers g'⟩ : Subgroup.zpowers g') • b : B) : G) = (b : G) :=
        congrArg Subtype.val h2
      have h4 : (((⟨g', Subgroup.mem_zpowers g'⟩ : Subgroup.zpowers g') • b : B) : G) =
          g * (b : G) * g⁻¹ := rfl
      rw [h4] at h3
      calc g * (b : G) = g * (b : G) * g⁻¹ * g := by group
        _ = (b : G) * g := by rw [h3]
    · intro h x
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 x.2
      apply Subtype.ext
      have h4 : (((x : Subgroup.zpowers g') • b : B) : G) =
          ((x : Subgroup.normalizer (B : Set G)) : G) * (b : G) *
            ((x : Subgroup.normalizer (B : Set G)) : G)⁻¹ := rfl
      have h1 : ((x : Subgroup.normalizer (B : Set G)) : G) = g ^ n := by
        rw [← hn]; rfl
      rw [h4, h1]
      have hc : (g ^ n) * (b : G) = (b : G) * (g ^ n) :=
        ((Commute.zpow_left (show Commute g (b : G) from h) n)).eq
      calc g ^ n * (b : G) * (g ^ n)⁻¹ = (b : G) * g ^ n * (g ^ n)⁻¹ := by rw [hc]
        _ = (b : G) := by group
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g') B) =
      Nat.card ↥(B ⊓ Subgroup.centralizer ({g} : Set G)) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun b => ⟨(b.1 : G), b.1.2, ?_⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
        left_inv := fun b => rfl
        right_inv := fun x => rfl }
    · show (b.1 : G) ∈ Subgroup.centralizer ({g} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (key b.1).1 b.2
    · rw [key]
      exact Subgroup.mem_centralizer_iff.mp x.2.2 g rfl
  rw [hfix] at hmod
  exact hmod

theorem ncard_conjClass_mul_card [Finite G] (K : Subgroup G) (x : G) :
    {y | ∃ g ∈ K, g⁻¹ * x * g = y}.ncard * Nat.card ↥(K ⊓ Subgroup.centralizer ({x} : Set G)) =
      Nat.card K := by
  let _ : MulAction K G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp K.subtype)
  have hsmul : ∀ (k : K) (y : G), k • y = (k : G) * y * (k : G)⁻¹ := fun k y => rfl
  have h1 := MulAction.index_stabilizer K x
  have hstab : MulAction.stabilizer K x =
      (K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K := by
    ext k
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨k.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h' hh'
      rw [Set.mem_singleton_iff] at hh'
      subst hh'
      calc h' * (k : G) = ((k : G) * h' * (k : G)⁻¹) * (k : G) := by rw [h]
        _ = (k : G) * h' := by group
    · rintro ⟨-, hk⟩
      have := Subgroup.mem_centralizer_iff.mp hk x rfl
      calc (k : G) * x * (k : G)⁻¹ = x * (k : G) * (k : G)⁻¹ := by rw [this]
        _ = x := by group
  have horb : MulAction.orbit K x = {y | ∃ g ∈ K, g⁻¹ * x * g = y} := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨(k : G)⁻¹, K.inv_mem k.2, by simp [hsmul]⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g⁻¹, K.inv_mem hg⟩, by simp [hsmul]⟩
  rw [hstab, horb] at h1
  have h2 := Subgroup.card_mul_index ((K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K)
  rw [h1] at h2
  have h3 : Nat.card ↥((K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K) =
      Nat.card ↥(K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h3] at h2
  rw [mul_comm]
  exact h2

theorem mem_normalizer_of_normal {K : Type*} [Group K] (B : Subgroup K) [B.Normal] (g : K) :
    g ∈ Subgroup.normalizer (B : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact Subgroup.Normal.conj_mem ‹B.Normal› x hx g
  · intro hx
    have := Subgroup.Normal.conj_mem ‹B.Normal› _ hx g⁻¹
    simpa [mul_assoc] using this

theorem mem_normalizer_inf_centralizer {K : Type*} [Group K] (B : Subgroup K) [B.Normal] {g u : K}
    (hgu : g * u = u * g) :
    g ∈ Subgroup.normalizer ((B ⊓ Subgroup.centralizer ({u} : Set K) : Subgroup K) : Set K) := by
  have key : ∀ g : K, Commute g u → ∀ x : K, x ∈ Subgroup.centralizer ({u} : Set K) →
      g * x * g⁻¹ ∈ Subgroup.centralizer ({u} : Set K) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hxc : Commute x u := hx
    exact ((hg.mul_left hxc).mul_left hg.inv_left).eq
  have hc : Commute g u := hgu
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxB, hxC⟩
    exact ⟨Subgroup.Normal.conj_mem ‹B.Normal› x hxB g, key g hc x hxC⟩
  · rintro ⟨hxB, hxC⟩
    have h1 := key g⁻¹ hc.inv_left _ hxC
    have h2 := Subgroup.Normal.conj_mem ‹B.Normal› _ hxB g⁻¹
    refine ⟨?_, ?_⟩
    · simpa [mul_assoc] using h2
    · simpa [mul_assoc] using h1

theorem card_zpowers_of_orderOf {K : Type*} [Group K] {g : K} {n : ℕ} (hg : orderOf g = n) :
    Nat.card (Subgroup.zpowers g) = n := by
  rw [Nat.card_zpowers, hg]

theorem card_normalizer_sylow_five {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 640)
    (P : Sylow 5 K) [Fact (Nat.Prime 5)] :
    Nat.card (Subgroup.normalizer (P : Set K)) = 640 ∨
      Nat.card (Subgroup.normalizer (P : Set K)) = 40 := by
  have hPcard : Nat.card (P : Subgroup K) = 5 := by
    rw [Sylow.card_eq_multiplicity, hK]
    have : (640 : ℕ).factorization 5 = 1 := by
      have h640 : (640 : ℕ) = 5 * 128 := by norm_num
      rw [h640, Nat.factorization_mul (by norm_num) (by norm_num)]
      simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 5),
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 128)]
    rw [this]; norm_num
  have hidx : (P : Subgroup K).index = 128 := by
    have := Subgroup.card_mul_index (P : Subgroup K)
    rw [hK, hPcard] at this
    omega
  have hdvd := Sylow.card_dvd_index P
  have hmod := card_sylow_modEq_one 5 K
  rw [hidx] at hdvd
  have hn := Sylow.card_eq_index_normalizer P
  have hN := Subgroup.card_mul_index (Subgroup.normalizer (P : Set K))
  rw [hK, ← hn] at hN
  have h128 : Nat.card (Sylow 5 K) ∣ 2 ^ 7 := by simpa using hdvd
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h128
  rw [hi'] at hmod hN
  unfold Nat.ModEq at hmod
  interval_cases i <;> omega

theorem false_of_card_640 {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 640)
    {B : Subgroup K} [B.Normal] (hB : Nat.card B = 16) {z : K} (hzB : z ∈ B)
    (hCz : ∀ g : K, g * z = z * g → ∃ n : ℕ, g ^ 2 ^ n = 1)
    (hCB : ∀ g : K, (∀ b ∈ B, g * b = b * g) → g ∈ B) : False := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5 (by rw [hK]; norm_num : 5 ∣ Nat.card K)
  have hcard5 : Nat.card (Subgroup.zpowers g) = 5 := card_zpowers_of_orderOf hg
  have hp5 : IsPGroup 5 (Subgroup.zpowers g) := IsPGroup.of_card (n := 1) (by rw [hcard5]; norm_num)
  have hgN : g ∈ Subgroup.normalizer (B : Set K) := mem_normalizer_of_normal B g
  have hdvd16 : ∀ D : Subgroup K, D ≤ B → Nat.card D ∣ 2 ^ 4 := fun D hD => by
    have := Subgroup.card_dvd_of_le hD
    rw [hB] at this
    simpa using this
  have hCg : B ⊓ Subgroup.centralizer ({g} : Set K) = ⊥ := by
    have hmod := card_modEq_card_inf_centralizer (p := 5) hgN hp5
    rw [hB] at hmod
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hdvd16 _ inf_le_left)
    rw [hi'] at hmod
    unfold Nat.ModEq at hmod
    have hi01 : i = 0 ∨ i = 4 := by
      interval_cases i <;> omega
    rcases hi01 with rfl | rfl
    · have : Nat.card ↥(B ⊓ Subgroup.centralizer ({g} : Set K)) = 1 := by rw [hi']; norm_num
      exact Subgroup.eq_bot_of_card_eq _ this
    · exfalso
      have hle : B ⊓ Subgroup.centralizer ({g} : Set K) = B := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
        rw [hi', hB]
        norm_num
      have hzC : z ∈ B ⊓ Subgroup.centralizer ({g} : Set K) := by rw [hle]; exact hzB
      have hzg : g * z = z * g := Subgroup.mem_centralizer_iff.mp hzC.2 g rfl
      obtain ⟨n, hn⟩ := hCz g hzg
      have := orderOf_dvd_of_pow_eq_one hn
      rw [hg] at this
      have h52 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) this
      omega
  have hidx : (Subgroup.zpowers g).index = 128 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers g)
    rw [hK, hcard5] at this
    omega
  let P : Sylow 5 K := hp5.toSylow (by rw [hidx]; norm_num)
  have hPeq : (P : Subgroup K) = Subgroup.zpowers g := rfl
  set N : Subgroup K := Subgroup.normalizer (P : Set K) with hN
  have hNcard : Nat.card N = 640 ∨ Nat.card N = 40 := card_normalizer_sylow_five hK P
  have hgNN : g ∈ N := by
    show g ∈ Subgroup.normalizer (P : Set K)
    exact Subgroup.le_normalizer (hPeq ▸ Subgroup.mem_zpowers g)
  have hS := ncard_conjClass_mul_card N g
  set S : Set K := {y | ∃ x ∈ N, x⁻¹ * g * x = y} with hSdef
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg
    omega
  have hSsub : S ⊆ ((P : Subgroup K) : Set K) \ {1} := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · have hx' : x⁻¹ ∈ Subgroup.normalizer (P : Set K) := N.inv_mem hx
      have := (Subgroup.mem_normalizer_iff.mp hx' g).mp (hPeq ▸ Subgroup.mem_zpowers g)
      show x⁻¹ * g * x ∈ (P : Subgroup K)
      simpa [mul_assoc] using this
    · intro h
      rw [Set.mem_singleton_iff] at h
      apply hg1
      have : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
      rw [← this, h]
      group
  have hScard : S.ncard ≤ 4 := by
    have h1 : (((P : Subgroup K) : Set K) \ {1}).ncard = 4 := by
      rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _)]
      have h5' : (((P : Subgroup K) : Set K)).ncard = 5 := by
        rw [← Nat.card_coe_set_eq]
        show Nat.card (P : Subgroup K) = 5
        rw [hPeq, hcard5]
      rw [h5']
    rw [← h1]
    exact Set.ncard_le_ncard hSsub (Set.toFinite _)
  set C₀ : Subgroup K := N ⊓ Subgroup.centralizer ({g} : Set K) with hC₀
  have hC₀ge : 10 ≤ Nat.card C₀ := by
    have hpos : 0 < S.ncard := by
      rw [Set.ncard_pos (Set.toFinite _)]
      exact ⟨g, 1, N.one_mem, by simp⟩
    rcases hNcard with h | h <;> rw [h] at hS <;>
      · generalize S.ncard = s at hS hScard hpos
        generalize Nat.card C₀ = c at hS ⊢
        interval_cases s <;> omega
  have hC₀dvd : Nat.card C₀ ∣ 640 := hK ▸ Subgroup.card_subgroup_dvd_card C₀
  have hgC₀ : g ∈ C₀ := ⟨hgNN, Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh]⟩
  have h5C₀ : 5 ∣ Nat.card C₀ := hg ▸ Subgroup.orderOf_dvd_natCard C₀ hgC₀
  have h2C₀ : 2 ∣ Nat.card C₀ := by
    obtain ⟨m, hm⟩ := h5C₀
    rw [hm] at hC₀dvd hC₀ge
    have hm128 : m ∣ 2 ^ 7 := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 5)).1 (by simpa using hC₀dvd)
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hm128
    rw [hm, hj']
    interval_cases j <;> omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := C₀) 2 h2C₀
  have hu' : orderOf (u : K) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have huC : (u : K) * g = g * (u : K) :=
    (Subgroup.mem_centralizer_iff.mp u.2.2 g rfl).symm
  have hu2 : Nat.card (Subgroup.zpowers (u : K)) = 2 := card_zpowers_of_orderOf hu'
  have hup : IsPGroup 2 (Subgroup.zpowers (u : K)) := IsPGroup.of_card (n := 1) (by rw [hu2]; norm_num)
  set D : Subgroup K := B ⊓ Subgroup.centralizer ({(u : K)} : Set K) with hD
  have hDle : D ≤ B := inf_le_left
  have hDeven : 2 ∣ Nat.card D := by
    have hmod : Nat.card B ≡ Nat.card D [MOD 2] :=
      card_modEq_card_inf_centralizer (p := 2) (mem_normalizer_of_normal B (u : K)) hup
    rw [hB] at hmod
    unfold Nat.ModEq at hmod
    omega
  have hgD : g ∈ Subgroup.normalizer (D : Set K) :=
    mem_normalizer_inf_centralizer B (g := g) (u := (u : K)) huC.symm
  have hDmod := card_modEq_card_inf_centralizer (p := 5) hgD hp5
  have hDg : D ⊓ Subgroup.centralizer ({g} : Set K) = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hCg]
    exact inf_le_inf_right _ hDle
  rw [hDg, Subgroup.card_bot] at hDmod
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hdvd16 D hDle)
  rw [hi'] at hDmod hDeven
  unfold Nat.ModEq at hDmod
  have hi4 : i = 4 := by
    interval_cases i <;> omega
  have hDB : D = B := by
    refine Subgroup.eq_of_le_of_card_ge hDle ?_
    rw [hi', hi4, hB]
    norm_num
  have hucB : ∀ b ∈ B, (u : K) * b = b * (u : K) := by
    intro b hb
    have : b ∈ D := by rw [hDB]; exact hb
    exact Subgroup.mem_centralizer_iff.mp this.2 (u : K) rfl
  have huB : (u : K) ∈ B := hCB (u : K) hucB
  have huCg : (u : K) ∈ B ⊓ Subgroup.centralizer ({g} : Set K) :=
    ⟨huB, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh; rw [hh]; exact huC.symm⟩
  rw [hCg, Subgroup.mem_bot] at huCg
  rw [huCg, orderOf_one] at hu'
  omega

open scoped IsMulCommutative

theorem exists_normal_pow_two_not_mem_of_transfer {X : Type*} [Group X] [Finite X]
    {H K : Subgroup X} (hH : IsPGroup 2 H) (hindex : ¬ 2 ∣ H.index)
    (hKn : (K.subgroupOf H).Normal) (habel : ⁅H, H⁆ ≤ K) {g : X} (hg : g ∈ H) (hgK : g ∉ K)
    (h : ∀ (m : ℤ) (a : X), a⁻¹ * g ^ m * a ∈ H → (g ^ m)⁻¹ * (a⁻¹ * g ^ m * a) ∈ K) :
    ∃ N : Subgroup X, N.Normal ∧ (∀ x : X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) ∧ g ∉ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : IsMulCommutative (H ⧸ K.subgroupOf H) := by
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, commutator_def,
      Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf]
    exact habel (Subgroup.commutator_mem_commutator x.2 y.2)
  let ϕ : H →* H ⧸ K.subgroupOf H := QuotientGroup.mk' (K.subgroupOf H)
  have hV := transfer_eq_pow_of_forall ϕ hg (by
    intro k a ha
    rw [eq_comm, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have := h k a (by simpa using ha)
    simpa using this)
  have hq : IsPGroup 2 (H ⧸ K.subgroupOf H) := hH.to_quotient _
  obtain ⟨a, ha⟩ := hq.exists_card_eq
  refine ⟨(MonoidHom.transfer ϕ).ker, inferInstance, fun x => ⟨a, ?_⟩, ?_⟩
  · rw [MonoidHom.mem_ker, map_pow]
    have := pow_card_eq_one' (G := H ⧸ K.subgroupOf H) (x := MonoidHom.transfer ϕ x)
    rwa [ha] at this
  · intro hgker
    rw [MonoidHom.mem_ker, hV] at hgker
    obtain ⟨n, hn⟩ := hq (ϕ ⟨g, hg⟩)
    have hcop : Nat.Coprime (2 ^ n) H.index :=
      Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hindex)
    have hz2 : ϕ ⟨g, hg⟩ = 1 := by
      have := pow_gcd_eq_one.2 ⟨hn, hgker⟩
      rwa [hcop, pow_one] at this
    apply hgK
    have := (QuotientGroup.eq_one_iff (⟨g, hg⟩ : H)).1 hz2
    exact Subgroup.mem_subgroupOf.1 this

theorem not_mem_oTwoUpper_of_transfer [Finite G] {X H K : Subgroup G} (hHX : H ≤ X)
    (hH : IsPGroup 2 H) (hindex : ¬ 2 ∣ H.relIndex X) (hKH : K ≤ H)
    (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (habel : ⁅H, H⁆ ≤ K) {g : G} (hg : g ∈ H)
    (hgK : g ∉ K)
    (h : ∀ (m : ℤ) (a : G), a ∈ X → a⁻¹ * g ^ m * a ∈ H → (g ^ m)⁻¹ * (a⁻¹ * g ^ m * a) ∈ K) :
    g ∉ oTwoUpper X := by
  have hK' : K.subgroupOf X ≤ H.subgroupOf X := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hKH (Subgroup.mem_subgroupOf.1 hx))
  have hKnormal : ((K.subgroupOf X).subgroupOf (H.subgroupOf X)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hK']
    intro k a hk ha
    exact Subgroup.mem_subgroupOf.2 (hKn a (Subgroup.mem_subgroupOf.1 ha) k
      (Subgroup.mem_subgroupOf.1 hk))
  have habel' : ⁅H.subgroupOf X, H.subgroupOf X⁆ ≤ K.subgroupOf X := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact Subgroup.mem_subgroupOf.2 (habel (Subgroup.commutator_mem_commutator
      (Subgroup.mem_subgroupOf.1 ha) (Subgroup.mem_subgroupOf.1 hb)))
  have hH' : IsPGroup 2 (H.subgroupOf X) :=
    hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHX).symm
  obtain ⟨N, hNn, hNpow, hgN⟩ := exists_normal_pow_two_not_mem_of_transfer (X := X)
    (H := H.subgroupOf X) (K := K.subgroupOf X) hH' hindex hKnormal habel'
    (g := ⟨g, hHX hg⟩) (Subgroup.mem_subgroupOf.2 hg)
    (fun hmem => hgK (Subgroup.mem_subgroupOf.1 hmem))
    (by
      intro m a ha
      have := h m a a.2 (Subgroup.mem_subgroupOf.1 ha)
      exact Subgroup.mem_subgroupOf.2 (by simpa using this))
  intro hgO
  have hle : oTwoUpper X ≤ N.map X.subtype := by
    refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    obtain ⟨k, hk⟩ := hNpow ⟨x, hx⟩
    exact ⟨k, ⟨_, hk, by simp⟩⟩
  obtain ⟨n, hn, hng⟩ := hle hgO
  have : n = ⟨g, hHX hg⟩ := Subtype.ext hng
  exact hgN (this ▸ hn)

theorem oTwoUpper_oTwoUpper (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X := by
  refine le_antisymm (oTwoUpper_le _) ?_
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  exact mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd hx.1 hx.2) hx.2

end CFSG.Quasithin.A10
