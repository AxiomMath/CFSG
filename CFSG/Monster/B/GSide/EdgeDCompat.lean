module

public import CFSG.Monster.B.GSide.EdgeHom

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
open scoped Pointwise

section Counting

variable {G : Type*} [Group G]

theorem card_fixed_perm_modEq {α : Type*} [Finite α] (σ : Equiv.Perm α) {p : ℕ} [Fact p.Prime]
    (hσ : σ ^ p = 1) : Nat.card {x // σ x = x} ≡ Nat.card α [MOD p] := by
  classical
  have := Fintype.ofFinite α
  have h := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) (σ := σ)
    (by rw [pow_one]; exact hσ)
  rw [Nat.card_eq_fintype_card (α := α)]
  refine Eq.trans ?_ h
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not])

theorem exists_dvd_two_pow_sub_one [Finite G] {Y : Subgroup G} {k : ℕ} (hY : Nat.card Y = 2 ^ k)
    {g : G} (hgY : ∀ y : G, y ∈ Y ↔ g * y * g⁻¹ ∈ Y) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hgp : g ^ p = 1) {z : G} (hzY : z ∈ Y) (hz1 : z ≠ 1) (hgz : g * z = z * g)
    (hgc : ¬ ∀ y ∈ Y, g * y = y * g) : ∃ j < k, 1 ≤ j ∧ p ∣ 2 ^ j - 1 := by
  set σ : Equiv.Perm G := MulAction.toPermHom (ConjAct G) G (ConjAct.toConjAct g) with hσdef
  have hσ : ∀ x, σ x = g * x * g⁻¹ := fun x => by
    rw [hσdef, MulAction.toPermHom_apply, MulAction.toPerm_apply, ConjAct.toConjAct_smul]
  have hmem : ∀ x : G, σ x ∈ Y ↔ x ∈ Y := fun x => by rw [hσ]; exact (hgY x).symm
  have hσp : σ ^ p = 1 := by
    rw [hσdef, ← map_pow, ← map_pow, hgp, map_one, map_one]
  have hτp : (σ.subtypePerm hmem) ^ p = 1 := by
    rw [Equiv.Perm.subtypePerm_pow]
    ext y
    show ((σ ^ p) (y : G)) = y
    rw [hσp, Equiv.Perm.one_apply]
  have hfix := card_fixed_perm_modEq (σ.subtypePerm hmem) hτp
  set C := Y ⊓ Subgroup.centralizer {g} with hC
  have hcardC : Nat.card {y // σ.subtypePerm hmem y = y} = Nat.card C := by
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, y.1.2, ?_⟩
        invFun := fun c => ⟨⟨c.1, c.2.1⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have h : σ (y.1 : G) = y.1 := congrArg Subtype.val y.2
      rw [hσ] at h
      show (y.1 : G) ∈ Subgroup.centralizer {g}
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y.1 : G) * g = g * y.1 * g⁻¹ * g := by rw [h]
        _ = g * y.1 := by group
    · apply Subtype.ext
      show σ (c : G) = c
      rw [hσ]
      have h := Subgroup.mem_centralizer_singleton_iff.1 c.2.2
      calc g * (c : G) * g⁻¹ = c * g * g⁻¹ := by rw [h]
        _ = c := by group
  rw [hcardC, hY] at hfix
  obtain ⟨m, hm, hmC⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hY ▸ Subgroup.card_dvd_of_le (inf_le_left : C ≤ Y))
  have hm1 : 1 ≤ m := by
    by_contra h0
    have h00 : m = 0 := by omega
    have hC1 : Nat.card C = 1 := by rw [hmC, h00, pow_zero]
    have hCb : C = ⊥ := Subgroup.card_eq_one.1 hC1
    have hz : z ∈ C := ⟨hzY, Subgroup.mem_centralizer_singleton_iff.2 hgz.symm⟩
    have hz' : z ∈ (⊥ : Subgroup G) := hCb ▸ hz
    exact hz1 ((Subgroup.mem_bot).1 hz')
  have hmk : m < k := by
    rcases (lt_or_eq_of_le hm) with h | h
    · exact h
    · exfalso
      apply hgc
      have hCY : C = Y := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hY, hmC, h])
      intro y hy
      have hy' : y ∈ C := hCY ▸ hy
      exact (Subgroup.mem_centralizer_singleton_iff.1 hy'.2).symm
  rw [hmC] at hfix
  have hdvd : p ∣ 2 ^ k - 2 ^ m :=
    (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right two_pos hm)).1 hfix
  have hsplit : 2 ^ k - 2 ^ m = 2 ^ m * (2 ^ (k - m) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hm]
  rw [hsplit] at hdvd
  have hcop : Nat.Coprime p (2 ^ m) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)
  exact ⟨k - m, by omega, by omega, hcop.dvd_of_dvd_mul_left hdvd⟩

theorem le_of_normal_of_odd_index [Finite G] {K H : Subgroup G} [hK : K.Normal]
    (hK2 : IsPGroup 2 K) (hH : ¬ 2 ∣ H.index) : K ≤ H := by
  have hfix := hK2.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ H) (by
    rw [← Subgroup.index]
    exact hH)
  obtain ⟨q, hq⟩ := hfix
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hconj : ∀ k ∈ K, x⁻¹ * k * x ∈ H := by
    intro k hk
    have h1 : (⟨k⁻¹, K.inv_mem hk⟩ : K) • (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk x :=
      hq ⟨k⁻¹, K.inv_mem hk⟩
    rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, QuotientGroup.eq] at h1
    simpa using h1
  intro k hk
  have h := hconj _ (hK.conj_mem k hk x)
  rwa [show x⁻¹ * (x * k * x⁻¹) * x = k by group] at h

theorem exists_two_pow_of_prime_dvd_normalizer [Finite G] {Y : Subgroup G} {k : ℕ}
    (hY : Nat.card Y = 2 ^ k) {z : G} (hzY : z ∈ Y) (hz1 : z ≠ 1)
    (hZ : ∀ y ∈ Y, (∀ y' ∈ Y, y * y' = y' * y) ↔ y = 1 ∨ y = z)
    (hC : ∀ g : G, (∀ y ∈ Y, g * y = y * g) → g * g = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpN : p ∣ Nat.card (Subgroup.normalizer (Y : Set G))) :
    ∃ j < k, 1 ≤ j ∧ p ∣ 2 ^ j - 1 := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hex := exists_prime_orderOf_dvd_card' p hpN
  obtain ⟨g, hg⟩ := hex
  have hgY : ∀ y : G, y ∈ Y ↔ (g : G) * y * (g : G)⁻¹ ∈ Y := Subgroup.mem_normalizer_iff.1 g.2
  have hgo : orderOf (g : G) = p := (Subgroup.orderOf_coe g).trans hg
  have hgp : (g : G) ^ p = 1 := by
    rw [← hgo]
    exact pow_orderOf_eq_one _
  have hzc : ∀ y' ∈ Y, z * y' = y' * z := (hZ z hzY).2 (Or.inr rfl)
  have hgz : (g : G) * z = z * g := by
    have hmem : (g : G) * z * (g : G)⁻¹ ∈ Y := (hgY z).1 hzY
    have hcen : ∀ y' ∈ Y, (g : G) * z * (g : G)⁻¹ * y' = y' * ((g : G) * z * (g : G)⁻¹) := by
      intro y' hy'
      have hw : (g : G)⁻¹ * y' * g ∈ Y := (hgY _).2 (by
        rw [show (g : G) * ((g : G)⁻¹ * y' * g) * (g : G)⁻¹ = y' by group]
        exact hy')
      have h1 := hzc _ hw
      calc (g : G) * z * (g : G)⁻¹ * y' = g * (z * ((g : G)⁻¹ * y' * g)) * (g : G)⁻¹ := by
            group
        _ = g * (((g : G)⁻¹ * y' * g) * z) * (g : G)⁻¹ := by rw [h1]
        _ = y' * ((g : G) * z * (g : G)⁻¹) := by group
    rcases (hZ _ hmem).1 hcen with h | h
    · exfalso
      apply hz1
      calc z = (g : G)⁻¹ * ((g : G) * z * (g : G)⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · calc (g : G) * z = (g : G) * z * (g : G)⁻¹ * g := by group
        _ = z * g := by rw [h]
  have hgc : ¬ ∀ y ∈ Y, (g : G) * y = y * g := fun h => by
    have h2 := hC _ h
    have hdvd : orderOf (g : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [hgo] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd)
  exact exists_dvd_two_pow_sub_one hY hgY hp2 hgp hzY hz1 hgz hgc

theorem ncard_conj_dvd [Finite G] (N : Subgroup G) {d : G} (hd : d ∈ N) :
    {x : G | ∃ n ∈ N, n * d * n⁻¹ = x}.ncard ∣ Nat.card N := by
  have e : {x : G | ∃ n ∈ N, n * d * n⁻¹ = x} = Subtype.val '' conjugatesOf (⟨d, hd⟩ : N) := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩ * ⟨d, hd⟩ * ⟨n, hn⟩⁻¹, isConj_iff.2 ⟨⟨n, hn⟩, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, hc⟩ := isConj_iff.1 hy
      exact ⟨c, c.2, by rw [← hc]; rfl⟩
  rw [e, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq,
    natCard_conjugatesOf]
  exact Subgroup.index_dvd_card _

theorem mul_self_of_isConj {d x : G} (hd2 : d * d = 1) (h : IsConj d x) : x * x = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  calc c * d * c⁻¹ * (c * d * c⁻¹) = c * (d * d) * c⁻¹ := by group
    _ = 1 := by rw [hd2]; group

theorem map_mem_normalizer {B : Type*} [Group B] (φ : B →* G) {Q : Subgroup B} (hQn : Q.Normal)
    (b : B) : φ b ∈ Subgroup.normalizer ((Q.map φ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨b * q * b⁻¹, hQn.conj_mem q hq b, ?_⟩
    simp only [map_mul, map_inv]
  · intro hy
    obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨b⁻¹ * q * b, by simpa using hQn.conj_mem q hq b⁻¹, ?_⟩
    simp only [map_mul, map_inv, hqy]
    group

theorem map_comm_iff {B : Type*} [Group B] {φ : B →* G} (hφ : Function.Injective φ)
    {Q : Subgroup B} {x : B} (hZQ : ∀ q ∈ Q, (∀ q' ∈ Q, q * q' = q' * q) ↔ q = 1 ∨ q = x) :
    ∀ y ∈ Q.map φ, (∀ y' ∈ Q.map φ, y * y' = y' * y) ↔ y = 1 ∨ y = φ x := by
  intro y hy
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hy
  constructor
  · intro h
    have hc : ∀ q' ∈ Q, q * q' = q' * q := fun q' hq' => hφ (by
      rw [map_mul, map_mul]
      exact h _ (Subgroup.mem_map_of_mem φ hq'))
    rcases (hZQ q hq).1 hc with rfl | rfl
    · exact Or.inl (map_one φ)
    · exact Or.inr rfl
  · intro h y' hy'
    obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.1 hy'
    have hq1 : q = 1 ∨ q = x := by
      rcases h with h | h
      · exact Or.inl (hφ (h.trans (map_one φ).symm))
      · exact Or.inr (hφ h)
    have h1 := congrArg φ ((hZQ q hq).2 hq1 q' hq')
    simpa only [map_mul] using h1

theorem mem_normalizer_of_unique {B : Type*} [Group B] [Finite B] {φ : B →* G}
    (hφ : Function.Injective φ) {Q : Subgroup B} (hQn : Q.Normal) {n : ℕ}
    (hQcard : Nat.card Q = 2 ^ n) {x : B}
    (hZQ : ∀ q ∈ Q, (∀ q' ∈ Q, q * q' = q' * q) ↔ q = 1 ∨ q = x) {MB : Subgroup B}
    (hMB : ¬ 2 ∣ MB.index)
    (hQ4 : ∀ K : Subgroup B, K ≤ MB → (∀ m ∈ MB, ∀ k ∈ K, m * k * m⁻¹ ∈ K) →
      Nat.card K = 2 ^ n → (∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) ↔ k = 1 ∨ k = x) → K = Q)
    {s : G} (hMs : ∀ m ∈ MB, ∃ b, s * φ b * s⁻¹ = φ m) (hsx : s * φ x * s⁻¹ = φ x) :
    s ∈ Subgroup.normalizer ((Q.map φ : Subgroup G) : Set G) := by
  set φ' : B →* G := (MulAut.conj s).toMonoidHom.comp φ with hφ'
  have hφ'a : ∀ b, φ' b = s * φ b * s⁻¹ := fun b => rfl
  have hφ'inj : Function.Injective φ' := fun a b h => by
    rw [hφ'a, hφ'a] at h
    exact hφ (mul_left_cancel (mul_right_cancel h))
  have hMr : MB.map φ ≤ φ'.range := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨b, hb⟩ := hMs m hm
    exact ⟨b, hb⟩
  have hcard' : Nat.card ((MB.map φ).comap φ') = Nat.card MB := by
    rw [← Subgroup.card_map_of_injective hφ'inj, Subgroup.map_comap_eq_self hMr,
      Subgroup.card_map_of_injective hφ]
  have hidx' : ((MB.map φ).comap φ').index = MB.index := by
    have h1 := ((MB.map φ).comap φ').card_mul_index
    have h2 := MB.card_mul_index
    rw [hcard'] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  have hQM : Q ≤ (MB.map φ).comap φ' :=
    le_of_normal_of_odd_index (hK := hQn) (IsPGroup.of_card hQcard) (by rw [hidx']; exact hMB)
  have hY'M : Q.map φ' ≤ MB.map φ := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hy
    exact hQM hq
  have hY'r : Q.map φ' ≤ φ.range := hY'M.trans (Subgroup.map_le_range φ MB)
  have hKMB : (Q.map φ').comap φ ≤ MB := by
    intro b hb
    obtain ⟨m, hm, hmb⟩ := Subgroup.mem_map.1 (hY'M (Subgroup.mem_comap.1 hb))
    rw [← hφ hmb]
    exact hm
  have hKn : ∀ m ∈ MB, ∀ k ∈ (Q.map φ').comap φ, m * k * m⁻¹ ∈ (Q.map φ').comap φ := by
    intro m hm k hk
    obtain ⟨c, hc⟩ := hMs m hm
    obtain ⟨q, hq, hqk⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hk)
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨c * q * c⁻¹, hQn.conj_mem q hq c, ?_⟩)
    simp only [map_mul, map_inv]
    rw [hqk, hφ'a c, hc]
  have hKcard : Nat.card ((Q.map φ').comap φ) = 2 ^ n := by
    rw [← Subgroup.card_map_of_injective hφ, Subgroup.map_comap_eq_self hY'r,
      Subgroup.card_map_of_injective hφ'inj, hQcard]
  have hKZ : ∀ k ∈ (Q.map φ').comap φ,
      (∀ k' ∈ (Q.map φ').comap φ, k * k' = k' * k) ↔ k = 1 ∨ k = x := by
    intro k hk
    obtain ⟨q, hq, hqk⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hk)
    constructor
    · intro hcen
      have hqc : ∀ q' ∈ Q, q * q' = q' * q := by
        intro q' hq'
        obtain ⟨k', hk'⟩ := MonoidHom.mem_range.1 (hY'r (Subgroup.mem_map_of_mem φ' hq'))
        have hk'K : k' ∈ (Q.map φ').comap φ := by
          rw [Subgroup.mem_comap, hk']
          exact Subgroup.mem_map_of_mem φ' hq'
        apply hφ'inj
        simp only [map_mul]
        rw [hqk, ← hk']
        have h1 := congrArg φ (hcen k' hk'K)
        simpa only [map_mul] using h1
      rcases (hZQ q hq).1 hqc with rfl | rfl
      · left
        apply hφ
        rw [← hqk, map_one, map_one]
      · right
        apply hφ
        rw [← hqk]
        exact hsx
    · rintro (h | h) k' hk'
      · rw [h, one_mul, mul_one]
      · rw [h]
        have hsx' : φ' x = φ x := hsx
        have hqx : q = x := hφ'inj (hqk.trans (by rw [h, hsx']))
        obtain ⟨q', hq', hqk'⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hk')
        have hxQ : x ∈ Q := hqx ▸ hq
        have hxc := (hZQ x hxQ).2 (Or.inr rfl) q' hq'
        apply hφ
        have h1 := congrArg φ' hxc
        simp only [map_mul] at h1 ⊢
        rw [← hqk', ← hsx']
        exact h1
  have hKQ := hQ4 _ hKMB hKn hKcard hKZ
  have hY' : Q.map φ' = Q.map φ := by
    rw [← Subgroup.map_comap_eq_self hY'r, hKQ]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← hY']
    exact Subgroup.mem_map_of_mem φ' hq
  · intro hy
    rw [← hY'] at hy
    obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.1 hy
    have hqy' : s * φ q * s⁻¹ = s * y * s⁻¹ := hqy
    exact Subgroup.mem_map.2 ⟨q, hq, mul_left_cancel (mul_right_cancel hqy')⟩

theorem fix_or_swap_of_mem {m a b x : G} (hm : m * a * m⁻¹ ∈ ({a, b} : Set G))
    (hmx : m * x = x * m) (hx2 : x * x = 1) (hb : b = a * x) :
    (m * a * m⁻¹ = a ∧ m * b * m⁻¹ = b) ∨ (m * a * m⁻¹ = b ∧ m * b * m⁻¹ = a) := by
  have hbx : m * b * m⁻¹ = m * a * m⁻¹ * x := by
    rw [hb]
    calc m * (a * x) * m⁻¹ = m * a * m⁻¹ * (m * x * m⁻¹) := by group
      _ = m * a * m⁻¹ * x := by rw [hmx, mul_inv_cancel_right]
  rcases hm with h | h
  · exact Or.inl ⟨h, by rw [hbx, h, hb]⟩
  · have h' : m * a * m⁻¹ = b := h
    refine Or.inr ⟨h', ?_⟩
    rw [hbx, h', hb, mul_assoc, hx2, mul_one]

theorem fix_or_swap_map {B : Type*} [Group B] (φ : B →* G) {m a b : B} {d e s : G}
    (hs1 : s * d * s⁻¹ = φ a) (hs2 : s * e * s⁻¹ = φ b)
    (h : (m * a * m⁻¹ = a ∧ m * b * m⁻¹ = b) ∨ (m * a * m⁻¹ = b ∧ m * b * m⁻¹ = a)) :
    (s⁻¹ * φ m * s * d * (s⁻¹ * φ m * s)⁻¹ = d ∧ s⁻¹ * φ m * s * e * (s⁻¹ * φ m * s)⁻¹ = e) ∨
      (s⁻¹ * φ m * s * d * (s⁻¹ * φ m * s)⁻¹ = e ∧
        s⁻¹ * φ m * s * e * (s⁻¹ * φ m * s)⁻¹ = d) := by
  have hconj : ∀ {x y : B} {x' y' : G}, s * x' * s⁻¹ = φ x → s * y' * s⁻¹ = φ y →
      m * x * m⁻¹ = y → s⁻¹ * φ m * s * x' * (s⁻¹ * φ m * s)⁻¹ = y' := by
    intro x y x' y' hx hy hxy
    have h1 : φ m * φ x * (φ m)⁻¹ = φ y := by
      rw [← hxy]
      simp only [map_mul, map_inv]
    calc s⁻¹ * φ m * s * x' * (s⁻¹ * φ m * s)⁻¹ = s⁻¹ * (φ m * (s * x' * s⁻¹) * (φ m)⁻¹) * s := by
          group
      _ = s⁻¹ * (s * y' * s⁻¹) * s := by rw [hx, h1, hy]
      _ = y' := by group
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hconj hs1 hs1 h1, hconj hs2 hs2 h2⟩
  · exact Or.inr ⟨hconj hs1 hs2 h1, hconj hs2 hs1 h2⟩

theorem conjugatesOf_map_eq {A B : Type*} [Group A] [Group B] (i : A →* B)
    (hidx : i.range.index = 2) {L : Set A} {u : A} (hLcls : ∀ b, b ∈ L ↔ IsConj u b) {t : B}
    (htR : t ∉ i.range) (htu : t * i u = i u * t) : conjugatesOf (i u) = i '' L := by
  have key : ∀ c ∈ i.range, c * i u * c⁻¹ ∈ i '' L := by
    intro c hc
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.1 hc
    exact ⟨k * u * k⁻¹, (hLcls _).2 (isConj_iff.2 ⟨k, rfl⟩), by simp only [map_mul, map_inv]⟩
  ext x
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hx
    by_cases hc : c ∈ i.range
    · exact key c hc
    · have hct : c * t⁻¹ ∈ i.range := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        exact iff_of_false hc (fun h => htR (by simpa using i.range.inv_mem h))
      have htu' : t⁻¹ * i u * t = i u := by rw [mul_assoc, ← htu, inv_mul_cancel_left]
      have e : c * i u * c⁻¹ = c * t⁻¹ * i u * (c * t⁻¹)⁻¹ := by
        calc c * i u * c⁻¹ = c * (t⁻¹ * i u * t) * c⁻¹ := by rw [htu']
          _ = c * t⁻¹ * i u * (c * t⁻¹)⁻¹ := by group
      rw [e]
      exact key _ hct
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨k, rfl⟩ := isConj_iff.1 ((hLcls a).1 ha)
    exact isConj_iff.2 ⟨i k, by simp only [map_mul, map_inv]⟩

theorem card_dvd_inf_centralizer_map {B : Type*} [Group B] {φ : B →* G}
    (hφ : Function.Injective φ) (C : Subgroup B) {a b : B} {a' b' : G} (ha' : φ a = a')
    (hb' : φ b = b') (ha : ∀ c ∈ C, c * a = a * c) (hb : ∀ c ∈ C, c * b = b * c) :
    Nat.card C ∣ Nat.card ↥(Subgroup.centralizer {a'} ⊓ Subgroup.centralizer {b'}) := by
  subst ha' hb'
  rw [← Subgroup.card_map_of_injective (K := C) hφ]
  apply Subgroup.card_dvd_of_le
  intro y hy
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hy
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
    Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  · rw [← map_mul, ← map_mul, ha c hc]
  · rw [← map_mul, ← map_mul, hb c hc]

theorem map_mul_mul_inv {B : Type*} [Group B] (φ : B →* G) (a b : B) :
    φ (a * b * a⁻¹) = φ a * φ b * (φ a)⁻¹ := by
  simp only [map_mul, map_inv]

theorem mul_mul_cancel_of_mul_self {u x : G} (hu : u * u = 1) : u * (u * x) = x := by
  rw [← mul_assoc, hu, one_mul]

theorem mul_mul_eq_of_comm {u x : G} (hu : u * u = 1) (hc : u * x = x * u) : u * x * u = x := by
  rw [mul_assoc, ← hc, ← mul_assoc, hu, one_mul]

theorem commute_map_mul {A : Type*} [Group A] (i : A →* G) {c : G} {a x : A}
    (ha : c * i a = i a * c) (hx : c * i x = i x * c) : c * i (a * x) = i (a * x) * c := by
  rw [map_mul]
  exact (Commute.mul_right ha hx).eq

theorem mem_of_conj_eq {H : Subgroup G} (hH : H.Normal) {t a b : G} (h : t * a * t⁻¹ = b)
    (ha : a ∈ H) : b ∈ H := by
  rw [← h]
  exact hH.conj_mem a ha t

theorem map_mul_mem {A : Type*} [Group A] (i : A →* G) {H : Subgroup G} {a b : A}
    (ha : i a ∈ H) (hb : i b ∈ H) : i (a * b) ∈ H := by
  rw [map_mul]
  exact H.mul_mem ha hb

omit [Group G] in
theorem mem_pair_congr {x a b b' : G} (h : b = b') :
    x ∈ ({a, b} : Set G) ↔ x ∈ ({a, b'} : Set G) := by
  rw [h]

theorem mul_self_eq_one_of_map {A : Type*} [Group A] {θ : A →* G} (hθ : Function.Injective θ)
    {u : A} (h : θ u * θ u = 1) : u * u = 1 :=
  hθ (by rw [map_mul, map_one]; exact h)

theorem mulEquiv_comm {K H : Type*} [Group K] [Group H] (ψ : K ≃* H) (k : K) (y : H)
    (h : k * ψ.symm y = ψ.symm y * k) : ψ k * y = y * ψ k := by
  have h1 := congrArg ψ h
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1

theorem natCard_centralizer_mulEquiv {K H : Type*} [Group K] [Group H] (φ : K ≃* H) (k : K) :
    Nat.card (Subgroup.centralizer {φ k}) = Nat.card (Subgroup.centralizer {k}) :=
  Nat.card_congr
    { toFun := fun x => ⟨φ.symm x, Subgroup.mem_centralizer_singleton_iff.2 (by
        have h := congrArg φ.symm (Subgroup.mem_centralizer_singleton_iff.1 x.2)
        rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at h)⟩
      invFun := fun x => ⟨φ x, Subgroup.mem_centralizer_singleton_iff.2 (by
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 x.2])⟩
      left_inv := fun x => Subtype.ext (MulEquiv.apply_symm_apply φ x)
      right_inv := fun x => Subtype.ext (MulEquiv.symm_apply_apply φ x) }

theorem natCard_centralizer_centralizer {a b : G} (hb : b ∈ Subgroup.centralizer {a}) :
    Nat.card (Subgroup.centralizer {(⟨b, hb⟩ : Subgroup.centralizer {a})}) =
      Nat.card ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}) :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2,
        Subgroup.mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 x.2))⟩⟩
      invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩,
        Subgroup.mem_centralizer_singleton_iff.2
          (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem mul_mul_self_of_comm {a b : G} (hab : a * b = b * a) (ha : a * a = 1) (hb : b * b = 1) :
    a * b * (a * b) = 1 := by
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← hab]
    _ = a * a * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

theorem exists_conj_of_mem_orbit {A : Type*} [Group A] (i : A →* G) {O : Set G} {x₀ : G}
    (hO : O = {y | ∃ a : A, y = i a * x₀ * (i a)⁻¹}) :
    ∀ x ∈ O, ∀ y ∈ O, ∃ a : A, i a * x * (i a)⁻¹ = y := by
  subst hO
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  refine ⟨b * a⁻¹, ?_⟩
  simp only [map_mul, map_inv]
  group

theorem mem_iff_isConj_of_orbit {L : Set G} (hL : ∃ u ∈ L, L = {b | ∃ a : G, b = a * u * a⁻¹}) :
    ∀ a ∈ L, ∀ b, b ∈ L ↔ IsConj a b := by
  obtain ⟨u, -, rfl⟩ := hL
  intro a ha b
  have hua : IsConj u a := by
    obtain ⟨k, rfl⟩ := ha
    exact isConj_iff.2 ⟨k, rfl⟩
  constructor
  · rintro ⟨c, rfl⟩
    exact hua.symm.trans (isConj_iff.2 ⟨c, rfl⟩)
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.1 (hua.trans h)
    exact ⟨c, hc.symm⟩

end Counting

section Parts

theorem ncard_eq_sum_of_parts {α ι : Type*} [Finite α] [Fintype ι] {T : Set α}
    {P : ι → Set α} (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (hcov : T ⊆ ⋃ i, P i)
    (ε : ι → Bool) (hε1 : ∀ i, ε i = true → P i ⊆ T)
    (hε0 : ∀ i, ε i = false → Disjoint (P i) T) :
    T.ncard = ∑ i, cond (ε i) (P i).ncard 0 := by
  classical
  have := Fintype.ofFinite α
  have hT : T.toFinset = (Finset.univ.filter fun i => ε i = true).biUnion
      fun i => (P i).toFinset := by
    ext x
    simp only [Set.mem_toFinset, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hx)
      refine ⟨i, ?_, hi⟩
      cases h : ε i
      · exact absurd hx (Set.disjoint_left.1 (hε0 i h) hi)
      · rfl
    · rintro ⟨i, hi, hx⟩
      exact hε1 i hi hx
  rw [Set.ncard_eq_toFinset_card', hT, Finset.card_biUnion, Finset.sum_filter]
  · refine Finset.sum_congr rfl fun i _ => ?_
    cases h : ε i
    · rfl
    · simp only [ite_true, Bool.cond_true]
      exact (Set.ncard_eq_toFinset_card' _).symm
  · intro i _ j _ hij
    exact Set.disjoint_toFinset.2 (hdisj i j hij)

theorem false_of_cert {n : ℕ}
    (h : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ n → ∃ j < 23, 1 ≤ j ∧ q ∣ 2 ^ j - 1) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ n) (hord : ∀ j < 23, 1 ≤ j → ¬ p ∣ 2 ^ j - 1) :
    False := by
  obtain ⟨j, hj, h1, hd⟩ := h p hp hp2 hpn
  exact hord j hj h1 hd

theorem subsetSum_cases (a b c d e : Bool) {n : ℕ}
    (hn : n = 2 + (cond a 1782 0 + cond b 2816 0 + cond c 456192 0 + cond d 1596672 0 +
      cond e 41472 0))
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n → ∃ j < 23, 1 ≤ j ∧ p ∣ 2 ^ j - 1) :
    (a = false ∧ b = false ∧ c = false ∧ d = false ∧ e = false) ∨
      (a = true ∧ b = true ∧ c = false ∧ d = false ∧ e = false) := by
  subst hn
  cases a <;> cases b <;> cases c <;> cases d <;> cases e
  · exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact (false_of_cert h 233 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 311 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 819073 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 228097 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 19141 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 47 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 173 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 1409 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 103 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 59 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 820481 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 197 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 29 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 1027841 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 61681 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 223 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 5407 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 199807 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 10789 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 131 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 149 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 256831 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 29 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact (false_of_cert h 443 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 200159 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 47 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 239 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 8969 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 5981 (by norm_num) (by decide) (by decide) (by decide)).elim
  · exact (false_of_cert h 37 (by norm_num) (by decide) (by decide) (by decide)).elim

theorem parts_subset_of_count {α : Type*} [Finite α] {S : Set α} {d e : α} (hde : d ≠ e)
    (hdS : d ∈ S) (heS : e ∈ S) {Lg : Set α} (hLS : Lg ⊆ S) (hLd : d ∉ Lg) (hLe : e ∉ Lg)
    (hLcard : Lg.ncard = 1782) (P : Fin 4 → Set α)
    (hPdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (hPd : ∀ i, d ∉ P i) (hPe : ∀ i, e ∉ P i)
    (hPL : ∀ i, Disjoint (P i) Lg)
    (hPcard : ∀ i, (P i).ncard = ![2816, 456192, 1596672, 41472] i)
    (hcov : S ⊆ {d, e} ∪ Lg ∪ ⋃ i, P i) (hdich : ∀ i, P i ⊆ S ∨ Disjoint (P i) S)
    (hprime : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ S.ncard → ∃ j < 23, 1 ≤ j ∧ p ∣ 2 ^ j - 1) :
    P 0 ⊆ S := by
  classical
  have hdeL : Disjoint ({d, e} : Set α) Lg := by
    rw [Set.disjoint_left]
    rintro x (rfl | rfl) hx
    · exact hLd hx
    · exact hLe hx
  have hBS : {d, e} ∪ Lg ⊆ S :=
    Set.union_subset (Set.insert_subset hdS (Set.singleton_subset_iff.2 heS)) hLS
  have hBcard : ({d, e} ∪ Lg).ncard = 1784 := by
    rw [Set.ncard_union_eq hdeL, Set.ncard_pair hde, hLcard]
  have hPB : ∀ i, Disjoint (P i) ({d, e} ∪ Lg) := fun i => by
    rw [Set.disjoint_union_right]
    refine ⟨?_, hPL i⟩
    rw [Set.disjoint_right]
    rintro x (rfl | rfl)
    · exact hPd i
    · exact hPe i
  have hST : (S \ ({d, e} ∪ Lg)).ncard + 1784 = S.ncard := by
    rw [← hBcard]
    exact Set.ncard_sdiff_add_ncard_of_subset hBS
  have hTcov : S \ ({d, e} ∪ Lg) ⊆ ⋃ i, P i := by
    rintro x ⟨hxS, hxB⟩
    rcases hcov hxS with h | h
    · exact absurd h hxB
    · exact h
  set ε : Fin 4 → Bool := fun i => decide (P i ⊆ S) with hε
  have hε1 : ∀ i, ε i = true → P i ⊆ S \ ({d, e} ∪ Lg) := fun i h x hx =>
    ⟨of_decide_eq_true h hx, Set.disjoint_left.1 (hPB i) hx⟩
  have hε0 : ∀ i, ε i = false → Disjoint (P i) (S \ ({d, e} ∪ Lg)) := fun i h => by
    have h' : ¬ P i ⊆ S := of_decide_eq_false h
    rcases hdich i with h1 | h1
    · exact absurd h1 h'
    · exact Set.disjoint_of_subset_right Set.sdiff_subset h1
  have hsum := ncard_eq_sum_of_parts hPdisj hTcov ε hε1 hε0
  have h0 : (P 0).ncard = 2816 := hPcard 0
  have h1 : (P 1).ncard = 456192 := hPcard 1
  have h2 : (P 2).ncard = 1596672 := hPcard 2
  have h3 : (P 3).ncard = 41472 := hPcard 3
  rw [Fin.sum_univ_four, h0, h1, h2, h3] at hsum
  have hn : S.ncard = 2 + (cond true 1782 0 + cond (ε 0) 2816 0 + cond (ε 1) 456192 0 +
      cond (ε 2) 1596672 0 + cond (ε 3) 41472 0) := by
    rw [Bool.cond_true]
    omega
  rcases subsetSum_cases true (ε 0) (ε 1) (ε 2) (ε 3) hn hprime with ⟨h, -⟩ | ⟨-, h, -⟩
  · exact absurd h (by decide)
  · exact of_decide_eq_true h

end Parts

section Adjacency

variable {G : Type*} [Group G] {d : G}

theorem gAdj_of_two_part
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (hd : orderOf d = 2) {a b : G}
    (ha : IsConj d a) (hb : IsConj d b) (hab : a * b = b * a) (hne : b ≠ a)
    (h2 : 2 ^ 38 ∣ Nat.card ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b})) :
    gAdj ψ a b := by
  have hbC : b ∈ Subgroup.centralizer {a} := Subgroup.mem_centralizer_singleton_iff.2 hab.symm
  have hy : psiAt ψ ha ⟨b, hbC⟩ ∈ dH ψ := (psiAt_mem_dH_iff ψ ha ⟨b, hbC⟩).2 hb
  have hd1 : d ≠ 1 := fun h => by
    rw [h, orderOf_one] at hd
    exact absurd hd (by norm_num)
  have hyc : psiAt ψ ha ⟨b, hbC⟩ ≠ cV0 := fun h =>
    hne (congrArg Subtype.val ((psiAt ψ ha).injective (h.trans (psiAt_self hd1 ψ ha).symm)))
  have hcard : Nat.card (Subgroup.centralizer {psiAt ψ ha ⟨b, hbC⟩}) =
      Nat.card ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}) :=
    (natCard_centralizer_mulEquiv (psiAt ψ ha) _).trans (natCard_centralizer_centralizer hbC)
  have h2' : 2 ^ 38 ∣ Nat.card (Subgroup.centralizer {psiAt ψ ha ⟨b, hbC⟩}) := by
    rw [hcard]
    exact h2
  rcases mem_RA_or_RB_of_two_part (orderOf_of_mem_dH ψ hd hy) hyc h2' with h | h
  · exact ⟨ha, hbC, h⟩
  · exact absurd hy (not_mem_dH_of_mem_RB' ψ hψ h)

end Adjacency

theorem commute_cEdgeIncl_xhat
    (b : cEdgeStab) :
    b * cEdgeIncl (lamV0 * lamW0) = cEdgeIncl (lamV0 * lamW0) * b := by
  apply Subtype.ext
  show (b : Shat) * (clabelS cv0 * clabelS cw0) = clabelS cv0 * clabelS cw0 * b
  have hc : clabelS cv0 * clabelS cw0 = clabelS cw0 * clabelS cv0 :=
    congrArg Subtype.val lamV0_mul_comm
  rcases (mem_cvSetStab_pair cgraph_adj_cv0_cw0.ne).1 b.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have c0 : Commute (b : Shat) (clabelS cv0) := (commute_clabelS_iff_mem cv0 b).2 h0
    have c1 : Commute (b : Shat) (clabelS cw0) := (commute_clabelS_iff_mem cw0 b).2 h1
    exact (c0.mul_right c1).eq
  · have e0 := GSide.clabelS_cvMul cv0 (b : Shat)
    have e1 := GSide.clabelS_cvMul cw0 (b : Shat)
    rw [h0] at e0
    rw [h1] at e1
    calc (b : Shat) * (clabelS cv0 * clabelS cw0) = (b : Shat) *
        (((b : Shat)⁻¹ * clabelS cw0 * b) * ((b : Shat)⁻¹ * clabelS cv0 * b)) := by
          rw [← e0, ← e1]
      _ = clabelS cw0 * clabelS cv0 * b := by group
      _ = clabelS cv0 * clabelS cw0 * b := by rw [hc]

theorem natCard_cEdgeFix_eq :
    Nat.card cEdgeFix = 77148607752437760 := by
  have e : Nat.card cEdgeFix = Nat.card (Subgroup.centralizer {lamW0H}) :=
    Nat.card_congr
      { toFun := fun a => ⟨cEdgeFixToH a, Subgroup.mem_centralizer_singleton_iff.2
          (Subtype.ext ((commute_clabelS_iff_mem cw0 a).2 a.2.2))⟩
        invFun := fun h => ⟨h.1.1, h.1.2, (commute_clabelS_iff_mem cw0 _).1
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 h.2))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [e]
  exact natCard_centralizer_of_mem_RA_or_RB (Or.inl lamW0H_mem_RA)

theorem two_pow_dvd_natCard_centralizer
    {L : Set cEdgeFix} {u : cEdgeFix}
    (hLcls : ∀ b, b ∈ L ↔ IsConj u b) (hLcard : L.ncard = 1782) {t : cEdgeStab}
    (htA : (t : Shat) ∉ cEdgeFix) (htu : t * cEdgeIncl u = cEdgeIncl u * t) :
    2 ^ 38 ∣ Nat.card (Subgroup.centralizer {cEdgeIncl u}) := by
  have htR : t ∉ cEdgeIncl.range := by
    rw [cEdgeIncl_range, Subgroup.mem_subgroupOf]
    exact htA
  have hconj := conjugatesOf_map_eq cEdgeIncl index_range_cEdgeIncl hLcls htR htu
  have hidx : (Subgroup.centralizer {cEdgeIncl u}).index = 1782 := by
    rw [← natCard_conjugatesOf, hconj, Nat.card_coe_set_eq,
      Set.ncard_image_of_injective _ cEdgeIncl_injective, hLcard]
  have hE : Nat.card cEdgeStab = 2 * 77148607752437760 := by
    have h1 := cEdgeIncl.range.index_mul_card
    rw [index_range_cEdgeIncl, ← Nat.card_congr (MonoidHom.ofInjective cEdgeIncl_injective).toEquiv,
      natCard_cEdgeFix_eq] at h1
    exact h1.symm
  have h := (Subgroup.centralizer {cEdgeIncl u}).card_mul_index
  rw [hidx, hE] at h
  have hc : Nat.card (Subgroup.centralizer {cEdgeIncl u}) = 86586540687360 := by omega
  rw [hc]
  exact ⟨315, by norm_num⟩

section Edge

variable {G : Type*} [Group G] {d : G}

theorem mem_range_of_fix_or_swap
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (φe : cEdgeStab →* G) (hφA : ∀ a : cEdgeFix, φe (cEdgeIncl a) = edgeTheta ψ a)
    {t : G} (ht : t ∈ φe.range)
    (ht1 : t * d * t⁻¹ = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G))
    (ht2 : t * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * t⁻¹ = d) {x : G}
    (hx : (x * d * x⁻¹ = d ∧ x * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * x⁻¹ =
        ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G)) ∨
      (x * d * x⁻¹ = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) ∧
        x * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * x⁻¹ = d)) :
    x ∈ φe.range := by
  set e : G := ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) with he
  have fix : ∀ y : G, y * d * y⁻¹ = d → y * e * y⁻¹ = e → y ∈ φe.range := by
    intro y h1 h2
    have hyd : y ∈ Subgroup.centralizer {d} := Subgroup.mem_centralizer_singleton_iff.2 (by
      calc y * d = y * d * y⁻¹ * y := by group
        _ = d * y := by rw [h1])
    have hye : y * e = e * y := by
      calc y * e = y * e * y⁻¹ * y := by group
        _ = e * y := by rw [h2]
    obtain ⟨a, ha⟩ := (mem_range_edgeTheta ψ).2 ⟨hyd, hye⟩
    exact ⟨cEdgeIncl a, by rw [hφA, ha]⟩
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact fix x h1 h2
  · have hy := fix (t⁻¹ * x)
      (by calc t⁻¹ * x * d * (t⁻¹ * x)⁻¹ = t⁻¹ * (x * d * x⁻¹) * t := by group
          _ = t⁻¹ * (t * d * t⁻¹) * t := by rw [h1, ht1]
          _ = d := by group)
      (by calc t⁻¹ * x * e * (t⁻¹ * x)⁻¹ = t⁻¹ * (x * e * x⁻¹) * t := by group
          _ = t⁻¹ * (t * e * t⁻¹) * t := by rw [h2, ht2]
          _ = e := by group)
    have h := φe.range.mul_mem ht hy
    rwa [mul_inv_cancel_left] at h

theorem mem_parts_of_mem_map
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (hd2 : d * d = 1)
    (φe : cEdgeStab →* G) (hinj : Function.Injective φe)
    (hφA : ∀ a : cEdgeFix, φe (cEdgeIncl a) = edgeTheta ψ a) {Q : Subgroup cEdgeStab}
    {O : Fin 4 → Set cEdgeStab}
    (hOcov : ∀ x ∈ Q, (x : Shat) ∉ cEdgeFix → x * x = 1 → ∃ i, x ∈ O i) {L : Set cEdgeFix}
    (hN1D : ∀ a : cEdgeFix, cEdgeIncl a ∈ Q → cEdgeFixToH a ∈ dH ψ →
      a = lamV0 ∨ a = lamW0 ∨ a ∈ L) {x : G} (hxY : x ∈ Q.map φe) (hxD : IsConj d x) :
    x ∈ ({d, ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G)} : Set G) ∪ edgeTheta ψ '' L ∪
      ⋃ i, φe '' O i := by
  have hxq := Subgroup.mem_map.1 hxY
  obtain ⟨q, hq, rfl⟩ := hxq
  by_cases hqA : (q : Shat) ∈ cEdgeFix
  · have hex : ∃ a : cEdgeFix, cEdgeIncl a = q := ⟨⟨q, hqA⟩, rfl⟩
    obtain ⟨a, rfl⟩ := hex
    rw [hφA] at hxD ⊢
    have haD : cEdgeFixToH a ∈ dH ψ := hxD
    rcases hN1D a hq haD with rfl | rfl | haL
    · refine Set.mem_union_left _ (Set.mem_union_left _ ?_)
      rw [edgeTheta_lamV0 ψ hψ]
      exact Set.mem_insert _ _
    · refine Set.mem_union_left _ (Set.mem_union_left _ ?_)
      rw [edgeTheta_lamW0]
      exact Set.mem_insert_of_mem _ rfl
    · exact Set.mem_union_left _ (Set.mem_union_right _ ⟨a, haL, rfl⟩)
  · have hq2 : q * q = 1 := mul_self_eq_one_of_map hinj (mul_self_of_isConj hd2 hxD)
    have hex := hOcov q hq hqA hq2
    obtain ⟨i, hi⟩ := hex
    exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨i, q, hi, rfl⟩)

theorem mul_self_of_centralizes
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) {Y : Subgroup G}
    (hdY : d ∈ Y) {P : cEdgeFix → Prop} (hθY : ∀ a, P a → edgeTheta ψ a ∈ Y)
    (hQ1 : ∀ h : vStab cv0, (∀ a : cEdgeFix, P a → h * cEdgeFixToH a = cEdgeFixToH a * h) →
      h * h = 1)
    (g : G) (hg : ∀ y ∈ Y, g * y = y * g) : g * g = 1 := by
  have hgd : g ∈ Subgroup.centralizer {d} := Subgroup.mem_centralizer_singleton_iff.2 (hg d hdY)
  have hh := hQ1 (ψ ⟨g, hgd⟩) (fun a ha =>
    mulEquiv_comm ψ ⟨g, hgd⟩ (cEdgeFixToH a) (Subtype.ext (hg _ (hθY a ha))))
  exact congrArg Subtype.val (mul_self_eq_one_of_map (θ := ψ.toMonoidHom) ψ.injective hh)

theorem exists_mem_normalizer_conj
    [Finite G] (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (hd : orderOf d = 2)
    (hidx : 2 ∣ (Subgroup.centralizer {d}).index) (φe : cEdgeStab →* G)
    (hinj : Function.Injective φe) (hφA : ∀ a : cEdgeFix, φe (cEdgeIncl a) = edgeTheta ψ a)
    {t : cEdgeStab} (htA : (t : Shat) ∉ cEdgeFix)
    (ht1 : φe t * d * (φe t)⁻¹ = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G))
    (ht2 : φe t * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * (φe t)⁻¹ = d)
    {Q : Subgroup cEdgeStab} (hQn : Q.Normal) (hQcard : Nat.card Q = 2 ^ 23)
    (hZQ : ∀ q ∈ Q, (∀ q' ∈ Q, q * q' = q' * q) ↔ q = 1 ∨ q = cEdgeIncl (lamV0 * lamW0))
    {L : Set cEdgeFix} (hLcard : L.ncard = 1782) (hLRA : ∀ a ∈ L, cEdgeFixToH a ∈ RA)
    {u g : cEdgeFix} (hu : u ∈ L) (hLcls : ∀ b, b ∈ L ↔ IsConj u b) (hgL : g ∈ L)
    (hgu : g = u * (lamV0 * lamW0)) (htu : t * cEdgeIncl u = cEdgeIncl u * t)
    {MB : Subgroup cEdgeStab}
    (hMB : ∀ b ∈ MB, b * cEdgeIncl u * b⁻¹ ∈ ({cEdgeIncl u, cEdgeIncl g} : Set cEdgeStab))
    (hMBidx : ¬ 2 ∣ MB.index)
    (hQ4 : ∀ K : Subgroup cEdgeStab, K ≤ MB → (∀ m ∈ MB, ∀ k ∈ K, m * k * m⁻¹ ∈ K) →
      Nat.card K = 2 ^ 23 → (∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) ↔
        k = 1 ∨ k = cEdgeIncl (lamV0 * lamW0)) → K = Q) :
    ∃ s ∈ Subgroup.normalizer ((Q.map φe : Subgroup G) : Set G),
      s * d * s⁻¹ = edgeTheta ψ u := by
  subst hgu
  let e : G := ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G)
  have hθV : edgeTheta ψ lamV0 = d := edgeTheta_lamV0 ψ hψ
  have hθW : edgeTheta ψ lamW0 = e := edgeTheta_lamW0 ψ
  have hd2 : d * d = 1 := by rw [← pow_two, ← hd, pow_orderOf_eq_one]
  have hRA := RA_subset_dH ψ hψ hd hidx
  have hfD : IsConj d (edgeTheta ψ u) := hRA (hLRA u hu)
  have hgD : IsConj d (edgeTheta ψ (u * (lamV0 * lamW0))) := hRA (hLRA _ hgL)
  have hu2 : u * u = 1 :=
    mul_self_eq_one_of_map (edgeTheta_injective ψ) (mul_self_of_isConj hd2 hfD)
  have hxc : u * (lamV0 * lamW0) = lamV0 * lamW0 * u :=
    Subgroup.mem_center_iff.1 (Subgroup.mul_mem _ lamV0_mem_center lamW0_mem_center) u
  have hug : u * (u * (lamV0 * lamW0)) = lamV0 * lamW0 := mul_mul_cancel_of_mul_self hu2
  have hgu' : u * (lamV0 * lamW0) * u = lamV0 * lamW0 := mul_mul_eq_of_comm hu2 hxc
  have hcomm : edgeTheta ψ u * edgeTheta ψ (u * (lamV0 * lamW0)) =
      edgeTheta ψ (u * (lamV0 * lamW0)) * edgeTheta ψ u :=
    (map_mul _ _ _).symm.trans ((congrArg (edgeTheta ψ) (hug.trans hgu'.symm)).trans
      (map_mul _ _ _))
  have hx2 : lamV0 * lamW0 * (lamV0 * lamW0) = 1 :=
    mul_mul_self_of_comm lamV0_mul_comm lamV0_mul_self lamW0_mul_self
  have hx1 : lamV0 * lamW0 ≠ 1 := fun h =>
    lamV0_ne_lamW0 ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right lamW0_mul_self))
  have hne : edgeTheta ψ (u * (lamV0 * lamW0)) ≠ edgeTheta ψ u := fun h =>
    hx1 (mul_left_cancel ((edgeTheta_injective ψ h).trans (mul_one u).symm))
  have hxE2 : cEdgeIncl (lamV0 * lamW0) * cEdgeIncl (lamV0 * lamW0) = 1 :=
    (map_mul _ _ _).symm.trans ((congrArg cEdgeIncl hx2).trans (map_one _))
  have hĝ : cEdgeIncl (u * (lamV0 * lamW0)) = cEdgeIncl u * cEdgeIncl (lamV0 * lamW0) :=
    map_mul _ _ _
  have hC := two_pow_dvd_natCard_centralizer hLcls hLcard htA htu
  have h38' := card_dvd_inf_centralizer_map hinj (Subgroup.centralizer {cEdgeIncl u})
    (hφA u) (hφA (u * (lamV0 * lamW0)))
    (fun c hc => Subgroup.mem_centralizer_singleton_iff.1 hc)
    (fun c hc => commute_map_mul cEdgeIncl (Subgroup.mem_centralizer_singleton_iff.1 hc)
      (commute_cEdgeIncl_xhat c))
  have hfg : gAdj ψ (edgeTheta ψ u) (edgeTheta ψ (u * (lamV0 * lamW0))) :=
    gAdj_of_two_part ψ hψ hd hfD hgD hcomm hne (hC.trans h38')
  have hs := exists_conj_pair_of_gAdj ψ (gAdj_edge ψ) hfg
  obtain ⟨s, hs1, hs2⟩ := hs
  have hz : φe (cEdgeIncl (lamV0 * lamW0)) = d * e :=
    (hφA _).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) hθV hθW))
  have hθug : edgeTheta ψ (u * (u * (lamV0 * lamW0))) = d * e :=
    (congrArg (edgeTheta ψ) hug).trans ((hφA _).symm.trans hz)
  have hsde : s * (d * e) * s⁻¹ = d * e :=
    calc s * (d * e) * s⁻¹ = (s * d * s⁻¹) * (s * e * s⁻¹) := by group
      _ = edgeTheta ψ u * edgeTheta ψ (u * (lamV0 * lamW0)) := congrArg₂ (· * ·) hs1 hs2
      _ = edgeTheta ψ (u * (u * (lamV0 * lamW0))) := (map_mul _ _ _).symm
      _ = d * e := hθug
  refine ⟨s, mem_normalizer_of_unique hinj hQn hQcard hZQ hMBidx hQ4 ?_
    ((congrArg (fun y => s * y * s⁻¹) hz).trans (hsde.trans hz.symm)), hs1⟩
  intro m hm
  have hfs := fix_or_swap_of_mem (hMB m hm) (commute_cEdgeIncl_xhat m) hxE2 hĝ
  have hfs' := fix_or_swap_map φe (hs1.trans (hφA u).symm) (hs2.trans (hφA _).symm) hfs
  have hr := mem_range_of_fix_or_swap ψ φe hφA (MonoidHom.mem_range.2 ⟨t, rfl⟩) ht1 ht2 hfs'
  obtain ⟨b, hb⟩ := hr
  exact ⟨b, by rw [hb]; group⟩

theorem edge_dCompat
    [Finite G] (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (hd : orderOf d = 2)
    (hidx : 2 ∣ (Subgroup.centralizer {d}).index) (φe : cEdgeStab →* G)
    (hinj : Function.Injective φe) (hφA : ∀ a : cEdgeFix, φe (cEdgeIncl a) = edgeTheta ψ a)
    (hφsw : ∀ b : cEdgeStab, (b : Shat) ∉ cEdgeFix →
      φe b * d * (φe b)⁻¹ = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) ∧
      φe b * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * (φe b)⁻¹ = d)
    (Q : Subgroup cEdgeStab) (hQn : Q.Normal) (hQcard : Nat.card Q = 2 ^ 23)
    (hcQ : cEdgeIncl lamV0 ∈ Q)
    (hZQ : ∀ q ∈ Q, (∀ q' ∈ Q, q * q' = q' * q) ↔ q = 1 ∨ q = cEdgeIncl (lamV0 * lamW0))
    (hQ1 : ∀ h : vStab cv0, (∀ a : cEdgeFix, cEdgeIncl a ∈ Q →
      h * cEdgeFixToH a = cEdgeFixToH a * h) → h * h = 1)
    (O : Fin 4 → Set cEdgeStab) (hOA : ∀ i x, x ∈ O i → (x : Shat) ∉ cEdgeFix)
    (hOcov : ∀ x ∈ Q, (x : Shat) ∉ cEdgeFix → x * x = 1 → ∃ i, x ∈ O i)
    (hOorb : ∀ i, ∀ x ∈ O i, ∀ y ∈ O i, ∃ a : cEdgeFix, cEdgeIncl a * x * (cEdgeIncl a)⁻¹ = y)
    (hOdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    (hOcard : ∀ i, (O i).ncard = ![2816, 456192, 1596672, 41472] i)
    (L : Set cEdgeFix) (hLcls : ∀ a ∈ L, ∀ b, b ∈ L ↔ IsConj a b) (hLcard : L.ncard = 1782)
    (hLRA : ∀ a ∈ L, cEdgeFixToH a ∈ RA) (hLcw : lamV0 ∉ L ∧ lamW0 ∉ L)
    (hN1D : ∀ a : cEdgeFix, cEdgeIncl a ∈ Q → cEdgeFixToH a ∈ dH ψ →
      a = lamV0 ∨ a = lamW0 ∨ a ∈ L)
    (u g : cEdgeFix) (hu : u ∈ L) (hgL : g ∈ L) (hgu : g = u * (lamV0 * lamW0))
    (hBu : ∃ b : cEdgeStab, (b : Shat) ∉ cEdgeFix ∧ b * cEdgeIncl u = cEdgeIncl u * b)
    (MB : Subgroup cEdgeStab)
    (hMB : ∀ b, b ∈ MB ↔ b * cEdgeIncl u * b⁻¹ ∈ ({cEdgeIncl u, cEdgeIncl g} : Set cEdgeStab))
    (hMBidx : MB.index = 891)
    (hQ4 : ∀ K : Subgroup cEdgeStab, K ≤ MB → (∀ m ∈ MB, ∀ k ∈ K, m * k * m⁻¹ ∈ K) →
      Nat.card K = 2 ^ 23 → (∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) ↔
        k = 1 ∨ k = cEdgeIncl (lamV0 * lamW0)) → K = Q) :
    ∀ x ∈ O 0, IsConj d (φe x) := by
  let e : G := ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G)
  have hθV : edgeTheta ψ lamV0 = d := edgeTheta_lamV0 ψ hψ
  have hθW : edgeTheta ψ lamW0 = e := edgeTheta_lamW0 ψ
  have hd2 : d * d = 1 := by rw [← pow_two, ← hd, pow_orderOf_eq_one]
  have hde : d ≠ e := fun h =>
    lamV0_ne_lamW0 (edgeTheta_injective ψ (hθV.trans (h.trans hθW.symm)))
  have htex := hBu
  obtain ⟨t, htA, htu⟩ := htex
  have ht := hφsw t htA
  have hdY : d ∈ Q.map φe := Subgroup.mem_map.2 ⟨cEdgeIncl lamV0, hcQ, (hφA lamV0).trans hθV⟩
  have hW : t * cEdgeIncl lamV0 * t⁻¹ = cEdgeIncl lamW0 := hinj ((map_mul_mul_inv φe t _).trans
    (((congrArg (fun y => φe t * y * (φe t)⁻¹) ((hφA lamV0).trans hθV)).trans ht.1).trans
      ((hφA lamW0).trans hθW).symm))
  have hxQ : cEdgeIncl (lamV0 * lamW0) ∈ Q := map_mul_mem cEdgeIncl hcQ (mem_of_conj_eq hQn hW hcQ)
  have hz : φe (cEdgeIncl (lamV0 * lamW0)) = d * e :=
    (hφA _).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) hθV hθW))
  have hz1 : φe (cEdgeIncl (lamV0 * lamW0)) ≠ 1 := fun h =>
    hde ((eq_inv_of_mul_eq_one_right (hz.symm.trans h)).trans
      (inv_eq_of_mul_eq_one_right hd2)).symm
  have hZY := map_comm_iff hinj hZQ
  have hCY : ∀ g' : G, (∀ y ∈ Q.map φe, g' * y = y * g') → g' * g' = 1 :=
    mul_self_of_centralizes ψ hdY (P := fun a => cEdgeIncl a ∈ Q)
      (fun a ha => Subgroup.mem_map.2 ⟨cEdgeIncl a, ha, hφA a⟩) hQ1
  have hYcard : Nat.card (Q.map φe) = 2 ^ 23 :=
    (Subgroup.card_map_of_injective hinj).trans hQcard
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G, N = Subgroup.normalizer ((Q.map φe : Subgroup G) : Set G) :=
    ⟨_, rfl⟩
  have hBN : ∀ b, φe b ∈ N := fun b => hN ▸ map_mem_normalizer φe hQn b
  have hdN : d ∈ N := hN ▸ Subgroup.le_normalizer hdY
  have hNY : ∀ n ∈ N, ∀ y, y ∈ Q.map φe ↔ n * y * n⁻¹ ∈ Q.map φe := fun n hn =>
    Subgroup.mem_normalizer_iff.1 (hN ▸ hn)
  obtain ⟨S, hS⟩ : ∃ S : Set G, S = {x | ∃ n ∈ N, n * d * n⁻¹ = x} := ⟨_, rfl⟩
  have hmemS : ∀ x, x ∈ S ↔ ∃ n ∈ N, n * d * n⁻¹ = x := fun x => by rw [hS]; rfl
  have hprime : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ S.ncard → ∃ j < 23, 1 ≤ j ∧ p ∣ 2 ^ j - 1 := by
    intro p hp hp2 hpS
    have hpN : p ∣ Nat.card N := hpS.trans (hS ▸ ncard_conj_dvd N hdN)
    rw [hN] at hpN
    exact exists_two_pow_of_prime_dvd_normalizer hYcard (Subgroup.mem_map_of_mem φe hxQ) hz1 hZY
      hCY hp hp2 hpN
  have hSN : ∀ n ∈ N, ∀ x ∈ S, n * x * n⁻¹ ∈ S := by
    intro n hn x hx
    obtain ⟨n', hn', rfl⟩ := (hmemS x).1 hx
    exact (hmemS _).2 ⟨n * n', N.mul_mem hn hn', by group⟩
  have hSD : ∀ x ∈ S, IsConj d x ∧ x ∈ Q.map φe := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := (hmemS x).1 hx
    exact ⟨isConj_iff.2 ⟨n, rfl⟩, (hNY n hn d).1 hdY⟩
  have hdS : d ∈ S := (hmemS d).2 ⟨1, N.one_mem, by group⟩
  have heS : e ∈ S := (hmemS e).2 ⟨φe t, hBN t, ht.1⟩
  have hopp := exists_mem_normalizer_conj ψ hψ hd hidx φe hinj hφA htA ht.1 ht.2 hQn hQcard
    hZQ hLcard hLRA hu (hLcls u hu) hgL hgu htu (fun b hb => (hMB b).1 hb)
    (by rw [hMBidx]; decide) hQ4
  obtain ⟨s, hsN, hs⟩ := hopp
  have hfS : edgeTheta ψ u ∈ S := (hmemS _).2 ⟨s, hN ▸ hsN, hs⟩
  have hLS : edgeTheta ψ '' L ⊆ S := by
    rintro _ ⟨b, hb, rfl⟩
    have hk := isConj_iff.1 ((hLcls u hu b).1 hb)
    obtain ⟨k, rfl⟩ := hk
    have e1 : edgeTheta ψ (k * u * k⁻¹) =
        φe (cEdgeIncl k) * edgeTheta ψ u * (φe (cEdgeIncl k))⁻¹ :=
      (map_mul_mul_inv _ k u).trans
        (congrArg (fun y => y * edgeTheta ψ u * y⁻¹) (hφA k).symm)
    exact e1 ▸ hSN _ (hBN _) _ hfS
  have hAimg : ∀ i, ∀ a : cEdgeFix, edgeTheta ψ a ∉ φe '' O i := by
    rintro i a ⟨x, hx, hxa⟩
    have hxa' : x = cEdgeIncl a := hinj (hxa.trans (hφA a).symm)
    exact hOA i (cEdgeIncl a) (hxa' ▸ hx) a.2
  have hdich : ∀ i, φe '' O i ⊆ S ∨ Disjoint (φe '' O i) S := by
    intro i
    by_cases h : ∃ x₀ ∈ O i, φe x₀ ∈ S
    · left
      obtain ⟨x₀, hx₀, hx₀S⟩ := h
      rintro _ ⟨y, hy, rfl⟩
      have ha := hOorb i x₀ hx₀ y hy
      obtain ⟨a, ha⟩ := ha
      have e2 : φe y = φe (cEdgeIncl a) * φe x₀ * (φe (cEdgeIncl a))⁻¹ :=
        (congrArg φe ha.symm).trans (map_mul_mul_inv _ _ _)
      exact e2 ▸ hSN _ (hBN _) _ hx₀S
    · right
      rw [Set.disjoint_left]
      rintro _ ⟨y, hy, rfl⟩ hyS
      exact h ⟨y, hy, hyS⟩
  have hcov : S ⊆ {d, e} ∪ edgeTheta ψ '' L ∪ ⋃ i, φe '' O i := fun x hx =>
    mem_parts_of_mem_map ψ hψ hd2 φe hinj hφA hOcov hN1D (hSD x hx).2 (hSD x hx).1
  have hLd : d ∉ edgeTheta ψ '' L := by
    rintro ⟨a, ha, h⟩
    exact hLcw.1 ((edgeTheta_injective ψ (h.trans hθV.symm)) ▸ ha)
  have hLe : e ∉ edgeTheta ψ '' L := by
    rintro ⟨a, ha, h⟩
    exact hLcw.2 ((edgeTheta_injective ψ (h.trans hθW.symm)) ▸ ha)
  have hLcard' : (edgeTheta ψ '' L).ncard = 1782 :=
    (Set.ncard_image_of_injective _ (edgeTheta_injective ψ)).trans hLcard
  have hPdisj : ∀ i j, i ≠ j → Disjoint (φe '' O i) (φe '' O j) := fun i j hij =>
    (Set.disjoint_image_iff hinj).2 (hOdisj i j hij)
  have hPd : ∀ i, d ∉ φe '' O i := fun i => hθV ▸ hAimg i lamV0
  have hPe : ∀ i, e ∉ φe '' O i := fun i => hθW ▸ hAimg i lamW0
  have hPL : ∀ i, Disjoint (φe '' O i) (edgeTheta ψ '' L) := fun i =>
    Set.disjoint_right.2 (by
      rintro _ ⟨a, _, rfl⟩
      exact hAimg i a)
  have hPcard : ∀ i, (φe '' O i).ncard = ![2816, 456192, 1596672, 41472] i := fun i =>
    (Set.ncard_image_of_injective _ hinj).trans (hOcard i)
  have hsub := parts_subset_of_count hde hdS heS hLS hLd hLe hLcard' (fun i => φe '' O i)
    hPdisj hPd hPe hPL hPcard hcov hdich hprime
  intro x hx
  exact (hSD _ (hsub ⟨x, hx, rfl⟩)).1

theorem edge_dCompat_label
    [Finite G] (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (hd : orderOf d = 2)
    (hidx : 2 ∣ (Subgroup.centralizer {d}).index) (φe : cEdgeStab →* G)
    (hinj : Function.Injective φe) (hφA : ∀ a : cEdgeFix, φe (cEdgeIncl a) = edgeTheta ψ a)
    (hφsw : ∀ b : cEdgeStab, (b : Shat) ∉ cEdgeFix →
      φe b * d * (φe b)⁻¹ = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) ∧
      φe b * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * (φe b)⁻¹ = d)
    (Q : Subgroup cEdgeStab) (hQn : Q.Normal) (hQcard : Nat.card Q = 2 ^ 23)
    (hcQ : cEdgeIncl lamV0 ∈ Q)
    (hZQ : ∀ q ∈ Q, (∀ q' ∈ Q, q * q' = q' * q) ↔ q = 1 ∨ q = cEdgeIncl (lamV0 * lamW0))
    (hQ1 : ∀ h : vStab cv0, (∀ a : cEdgeFix, cEdgeIncl a ∈ Q →
      h * cEdgeFixToH a = cEdgeFixToH a * h) → h * h = 1)
    (O : Fin 4 → Set cEdgeStab)
    (hOunion : ⋃ i, O i = {x | x ∈ Q ∧ x * x = 1 ∧ (x : Shat) ∉ cEdgeFix})
    (hOorb : ∀ i, ∃ x ∈ O i, O i = {y | ∃ a : cEdgeFix, y = cEdgeIncl a * x * (cEdgeIncl a)⁻¹})
    (hOdisj : Pairwise (Function.onFun Disjoint O))
    (hOcard : ∀ i, (O i).ncard = ![2816, 456192, 1596672, 41472] i)
    (hOlab : ∀ x ∈ Q, (x : Shat) ∉ cEdgeFix → (∃ v, (x : Shat) = clabelS v) → x ∈ O 0)
    (L : Set cEdgeFix) (hLorb : ∃ u ∈ L, L = {b | ∃ a : cEdgeFix, b = a * u * a⁻¹})
    (hLcard : L.ncard = 1782) (hLRA : ∀ a ∈ L, cEdgeFixToH a ∈ RA)
    (hLx : ∀ a ∈ L, a * (lamV0 * lamW0) ∈ L) (hLcw : lamV0 ∉ L ∧ lamW0 ∉ L)
    (hN1D : ∀ a : cEdgeFix, cEdgeIncl a ∈ Q → cEdgeFixToH a ∈ dH ψ →
      a = lamV0 ∨ a = lamW0 ∨ a ∈ L)
    (u : cEdgeFix) (hu : u ∈ L)
    (hBu : ∃ b : cEdgeStab, (b : Shat) ∉ cEdgeFix ∧ b * cEdgeIncl u = cEdgeIncl u * b)
    (MB : Subgroup cEdgeStab)
    (hMB : ∀ b, b ∈ MB ↔ b * cEdgeIncl u * b⁻¹ ∈
      ({cEdgeIncl u, cEdgeIncl u * cEdgeIncl (lamV0 * lamW0)} : Set cEdgeStab))
    (hMBidx : MB.index = 891)
    (hQ4 : ∀ K : Subgroup cEdgeStab, K ≤ MB → (∀ m ∈ MB, ∀ k ∈ K, m * k * m⁻¹ ∈ K) →
      Nat.card K = 2 ^ 23 → (∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) ↔
        k = 1 ∨ k = cEdgeIncl (lamV0 * lamW0)) → K = Q) :
    ∀ s (hs : s ∈ cvSetStab {cv0, cw0}), (⟨s, hs⟩ : cEdgeStab) ∈ Q → s ∉ cEdgeFix →
      (∃ v, s = clabelS v) → IsConj d (φe ⟨s, hs⟩) := by
  have hOA : ∀ i x, x ∈ O i → (x : Shat) ∉ cEdgeFix := fun i x hx =>
    ((Set.ext_iff.1 hOunion x).1 (Set.mem_iUnion.2 ⟨i, hx⟩)).2.2
  have hOcov : ∀ x ∈ Q, (x : Shat) ∉ cEdgeFix → x * x = 1 → ∃ i, x ∈ O i :=
    fun x hx hA h2 => Set.mem_iUnion.1 ((Set.ext_iff.1 hOunion x).2 ⟨hx, h2, hA⟩)
  have hOorb' : ∀ i, ∀ x ∈ O i, ∀ y ∈ O i,
      ∃ a : cEdgeFix, cEdgeIncl a * x * (cEdgeIncl a)⁻¹ = y := fun i => by
    have h := hOorb i
    obtain ⟨x₀, -, hO⟩ := h
    exact exists_conj_of_mem_orbit cEdgeIncl hO
  have hMB' : ∀ b, b ∈ MB ↔ b * cEdgeIncl u * b⁻¹ ∈
      ({cEdgeIncl u, cEdgeIncl (u * (lamV0 * lamW0))} : Set cEdgeStab) := fun b =>
    (hMB b).trans (mem_pair_congr (map_mul _ _ _).symm)
  intro s hs hsQ hsA hlab
  exact edge_dCompat ψ hψ hd hidx φe hinj hφA hφsw Q hQn hQcard hcQ hZQ hQ1 O hOA hOcov hOorb'
    (fun i j hij => hOdisj hij) hOcard L (mem_iff_isConj_of_orbit hLorb) hLcard hLRA hLcw hN1D
    u _ hu (hLx u hu) rfl hBu MB hMB' hMBidx hQ4 _ (hOlab _ hsQ hsA hlab)

theorem hve_of_edge_hom
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (φe : cEdgeStab →* G)
    (hφA : ∀ a : cEdgeFix,
      φe (cEdgeIncl a) = ((ψ.symm (cEdgeFixToH a) : Subgroup.centralizer {d}) : G)) :
    ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}),
      ((ψ.symm ⟨a, ha⟩ : Subgroup.centralizer {d}) : G) = φe ⟨a, hb⟩ := by
  intro a ha hb
  have hw : a ∈ vStab cw0 := by
    rcases (mem_cvSetStab_pair cgraph_adj_cv0_cw0.ne).1 hb with ⟨_, h1⟩ | ⟨h0, _⟩
    · exact h1
    · exact absurd ((mem_vStab.1 ha).symm.trans h0) cgraph_adj_cv0_cw0.ne
  exact (hφA ⟨a, ha, hw⟩).symm

end Edge

end CFSG.Monster.B.GSide
