module

public import CFSG.Quasithin.H13.A6S13816c
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Background.F1Cartan
public import CFSG.Quasithin.Background.A3Structure38Basic

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.QuasithinUnique CFSG.Quasithin

namespace L2Comm

variable {Q : Type} [Group Q] [Finite Q]

theorem le_of_isSylowTwoOf {U S K : Subgroup Q} (hU : IsSylowTwoOf U K) (hUS : U ≤ S)
    (hSK : S ≤ K) (hS : IsPGroup 2 S) : S ≤ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : U.relIndex S * S.relIndex K = U.relIndex K :=
    Subgroup.relIndex_mul_relIndex U S K hUS hSK
  have h2 : ¬ 2 ∣ U.relIndex S := fun h => hU.2.2 (h.trans ⟨_, h1.symm⟩)
  obtain ⟨m, hm⟩ := hS.exists_card_eq
  have h3 : U.relIndex S ∣ 2 ^ m := by
    rw [← hm]
    exact (U.subgroupOf S).index_dvd_card
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h3
  rcases i with _ | i
  · rw [pow_zero] at hi
    exact Subgroup.relIndex_eq_one.mp hi
  · exact absurd (hi ▸ dvd_pow_self 2 (Nat.succ_ne_zero i)) h2

omit [Finite Q] in
theorem mem_normalizer_of_comm {K K' A : Subgroup Q} (hcomm : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x)
    (hAK : A ≤ K) {g : Q} (hg : g ∈ K') : g ∈ Subgroup.normalizer (A : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : g * h * g⁻¹ = h := by rw [← hcomm h (hAK hh) g hg, mul_inv_cancel_right]
    rwa [e]
  · intro hh
    have hk := hcomm _ (hAK hh) g⁻¹ (K'.inv_mem hg)
    have e : h = g * h * g⁻¹ := by
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = (g * h * g⁻¹) * g⁻¹ * g := by rw [← hk]
        _ = g * h * g⁻¹ := by group
    rw [e]
    exact hh

omit [Finite Q] in
theorem pair_split {K₁ X N : Subgroup Q} {t c : Q}
    (hcomm' : ⁅K₁, K₁.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hinf : K₁ ⊓ K₁.map (MulAut.conj t).toMonoidHom = ⊥)
    (hX' : X ≤ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom)
    (htX : t ∈ Subgroup.normalizer (X : Set Q))
    (hXN : X ≤ Subgroup.normalizer (N : Set Q)) (hN : IsPGroup 2 N)
    (hc : c ∈ X) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hdec : ∀ x ∈ X, x ∈ N ∨ c * c * x ∈ N ∨ c * x ∈ N) :
    (∀ y ∈ X, y ∈ K₁ → ∃ k : ℕ, y ^ (2 ^ k) = 1) ∧
      (∀ y ∈ X, y ∈ K₁.map (MulAut.conj t).toMonoidHom → ∃ k : ℕ, y ^ (2 ^ k) = 1) ∧
      ∃ a ∈ K₁, ∃ b ∈ K₁.map (MulAut.conj t).toMonoidHom,
        c = a * b ∧ a ^ 3 = 1 ∧ a ≠ 1 ∧ b ^ 3 = 1 ∧ b ≠ 1 := by
  set K₂ := K₁.map (MulAut.conj t).toMonoidHom with hK₂
  have hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a :=
    L32Comm.mul_comm_of_commutator_eq_bot hcomm'
  have hint : ∀ y, y ∈ K₁ → y ∈ K₂ → y = 1 := fun y h1 h2 => by
    have : y ∈ K₁ ⊓ K₂ := ⟨h1, h2⟩
    rw [hinf] at this
    exact this
  have hN1 : ∀ n ∈ N, n ^ 3 = 1 → n = 1 := fun n hn h3 => by
    obtain ⟨k, hk⟩ := L32Comm.exists_pow_of_isPGroup hN hn
    exact L32Comm.eq_one_of_pow_of_cube hk h3
  have hconjN : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.mp (hXN hg) n).mp hn
  have hE9 : ∀ y ∈ X, y ∈ K₁ → y ^ 3 = 1 → y = 1 := by
    intro y hyX hyK hy3
    by_contra hy1
    set y' := t * y * t⁻¹ with hy'
    have hy'X : y' ∈ X := (Subgroup.mem_normalizer_iff.mp htX y).mp hyX
    have hy'K : y' ∈ K₂ := ⟨y, hyK, by simp [MulAut.conj_apply, hy']⟩
    have hy'3 : y' ^ 3 = 1 := by rw [hy', conj_pow, hy3, mul_one, mul_inv_cancel]
    have hy'1 : y' ≠ 1 := fun h => hy1 (by
      have e1 : y = t⁻¹ * y' * t := by rw [hy']; group
      rw [e1, h]
      group)
    have hcm : Commute y y' := hcomm y hyK y' hy'K
    have hA : y⁻¹ * y' ∈ N → False := fun h => by
      have h3 : (y⁻¹ * y') ^ 3 = 1 := by
        rw [hcm.inv_left.mul_pow, inv_pow, hy3, hy'3, inv_one, one_mul]
      have h4 := hN1 _ h h3
      have hyy : y = y' := by
        calc y = y * (y⁻¹ * y') := by rw [h4, mul_one]
          _ = y' := by group
      exact hy1 (hint y hyK (hyy ▸ hy'K))
    have hB : y * y' ∈ N → False := fun h => by
      have h3 : (y * y') ^ 3 = 1 := by rw [hcm.mul_pow, hy3, hy'3, one_mul]
      have h4 := hN1 _ h h3
      have hyy : y = y'⁻¹ := eq_inv_of_mul_eq_one_left h4
      exact hy1 (hint y hyK (hyy ▸ K₂.inv_mem hy'K))
    rcases hdec y hyX with h | h | h
    · exact hy1 (hN1 y h hy3)
    · rcases hdec y' hy'X with h' | h' | h'
      · exact hy'1 (hN1 y' h' hy'3)
      · apply hA
        have := N.mul_mem (N.inv_mem h) h'
        have e1 : (c * c * y)⁻¹ * (c * c * y') = y⁻¹ * y' := by group
        rwa [e1] at this
      · apply hB
        have h1 := hconjN _ (X.inv_mem (X.mul_mem hc hc)) _ h
        have := N.mul_mem h1 h'
        have e1 : (c * c)⁻¹ * (c * c * y) * (c * c)⁻¹⁻¹ * (c * y') =
            y * c ^ 3 * y' := by group
        rwa [e1, hc3, mul_one] at this
    · rcases hdec y' hy'X with h' | h' | h'
      · exact hy'1 (hN1 y' h' hy'3)
      · apply hB
        have h1 := hconjN _ (X.inv_mem hc) _ h
        have := N.mul_mem h1 h'
        have e1 : c⁻¹ * (c * y) * c⁻¹⁻¹ * (c * c * y') = y * c ^ 3 * y' := by
          rw [pow_three']
          group
        rwa [e1, hc3, mul_one] at this
      · apply hA
        have := N.mul_mem (N.inv_mem h) h'
        have e1 : (c * y)⁻¹ * (c * y') = y⁻¹ * y' := by group
        rwa [e1] at this
  have hE9' : ∀ y ∈ X, y ∈ K₂ → y ^ 3 = 1 → y = 1 := by
    intro y hyX hyK hy3
    obtain ⟨k, hk, rfl⟩ := hyK
    have hk' : (MulAut.conj t).toMonoidHom k = t * k * t⁻¹ := rfl
    rw [hk'] at hyX hy3 ⊢
    have hkX : k ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htX) _).mp hyX
      have e1 : t⁻¹ * (t * k * t⁻¹) * t⁻¹⁻¹ = k := by group
      rwa [e1] at this
    have hk3 : k ^ 3 = 1 := by
      have e1 : k ^ 3 = t⁻¹ * (t * k * t⁻¹) ^ 3 * t⁻¹⁻¹ := by
        rw [conj_pow]
        group
      rw [e1, hy3, mul_one, mul_inv_cancel]
    rw [hE9 k hkX hk hk3, mul_one, mul_inv_cancel]
  have hcube : ∀ x ∈ X, x ^ 3 ∈ N := by
    intro x hx
    rcases hdec x hx with h | h | h
    · exact N.pow_mem h 3
    · have e1 : x = (c * c)⁻¹ * (c * c * x) := by group
      rw [e1]
      refine L32Comm.cube_mem_of_conj hXN (X.inv_mem (X.mul_mem hc hc)) ?_ h
      have e2 : (c * c)⁻¹ ^ 3 = (c ^ 3 * c ^ 3)⁻¹ := by group
      rw [e2, hc3, mul_one, inv_one]
    · have e1 : x = c⁻¹ * (c * x) := by group
      rw [e1]
      refine L32Comm.cube_mem_of_conj hXN (X.inv_mem hc) ?_ h
      rw [inv_pow, hc3, inv_one]
  have htwo : ∀ y ∈ X, y ∈ K₁ → ∃ k : ℕ, y ^ (2 ^ k) = 1 := by
    intro y hyX hyK
    obtain ⟨k, hk⟩ := L32Comm.exists_pow_of_isPGroup hN (hcube y hyX)
    refine ⟨k, hE9 _ (X.pow_mem hyX _) (K₁.pow_mem hyK _) ?_⟩
    rw [← pow_mul, mul_comm, pow_mul, hk]
  have htwo' : ∀ y ∈ X, y ∈ K₂ → ∃ k : ℕ, y ^ (2 ^ k) = 1 := by
    intro y hyX hyK
    obtain ⟨k, hk⟩ := L32Comm.exists_pow_of_isPGroup hN (hcube y hyX)
    refine ⟨k, hE9' _ (X.pow_mem hyX _) (K₂.pow_mem hyK _) ?_⟩
    rw [← pow_mul, mul_comm, pow_mul, hk]
  refine ⟨htwo, htwo', ?_⟩
  obtain ⟨a, haK, b, hbK, hcab⟩ := L32Comm.exists_mul_of_mem_sup hcomm (hX' hc)
  have hab : Commute a b := hcomm a haK b hbK
  have h1 : a ^ 3 * b ^ 3 = 1 := by rw [← hab.mul_pow, ← hcab, hc3]
  have ha3 : a ^ 3 = 1 := by
    have h2 : a ^ 3 = (b ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
    exact hint _ (K₁.pow_mem haK 3) (h2 ▸ K₂.inv_mem (K₂.pow_mem hbK 3))
  have hb3 : b ^ 3 = 1 := by rw [ha3, one_mul] at h1; exact h1
  refine ⟨a, haK, b, hbK, hcab, ha3, fun ha => ?_, hb3, fun hb => ?_⟩
  · rw [ha, one_mul] at hcab
    exact hc1 (hE9' c hc (hcab ▸ hbK) hc3)
  · rw [hb, mul_one] at hcab
    exact hc1 (hE9 c hc (hcab ▸ haK) hc3)

theorem mem_normalizer_of_pair {K K' X U : Subgroup Q} {a b c : Q}
    (hcomm : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x)
    (htwo : ∀ y ∈ X, y ∈ K → ∃ k : ℕ, y ^ (2 ^ k) = 1) (hU : IsSylowTwoOf U K)
    (hUX : U ≤ Subgroup.normalizer (X : Set Q)) (hc : c ∈ X) (ha : a ∈ K) (hb : b ∈ K')
    (hcab : c = a * b) (ha3 : a ^ 3 = 1) : a ∈ Subgroup.normalizer (U : Set Q) := by
  have hQ2 : IsPGroup 2 ↥(X ⊓ K) := fun y => by
    obtain ⟨k, hk⟩ := htwo y y.2.1 y.2.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hUQ : U ≤ Subgroup.normalizer ((X ⊓ K : Subgroup Q) : Set Q) :=
    F7.le_normalizer_inf hUX (hU.1.trans Subgroup.le_normalizer)
  have hsup : IsPGroup 2 ↥(U ⊔ (X ⊓ K)) := hU.2.1.to_sup_of_normal_right' hQ2 hUQ
  have hle : X ⊓ K ≤ U :=
    le_sup_right.trans (le_of_isSylowTwoOf hU le_sup_left (sup_le hU.1 inf_le_right) hsup)
  have key : ∀ u ∈ U, a * u * a⁻¹ ∈ U := by
    intro u hu
    have hp : u⁻¹ ∈ U := U.inv_mem hu
    have hbu : b * u = u * b := (hcomm u (hU.1 hu) b hb).symm
    have hw : u⁻¹ * c * u⁻¹⁻¹ * c⁻¹ = u⁻¹ * a * u * a⁻¹ := by
      rw [hcab]
      calc u⁻¹ * (a * b) * u⁻¹⁻¹ * (a * b)⁻¹ = u⁻¹ * a * (b * u) * b⁻¹ * a⁻¹ := by group
        _ = u⁻¹ * a * (u * b) * b⁻¹ * a⁻¹ := by rw [hbu]
        _ = u⁻¹ * a * u * a⁻¹ := by group
    have hwX : u⁻¹ * c * u⁻¹⁻¹ * c⁻¹ ∈ X :=
      X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hUX hp) c).mp hc) (X.inv_mem hc)
    rw [hw] at hwX
    have hwK : u⁻¹ * a * u * a⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem (hU.1 hu)) ha) (hU.1 hu)) (K.inv_mem ha)
    have hwU : u⁻¹ * a * u * a⁻¹ ∈ U := hle ⟨hwX, hwK⟩
    have e : a * u * a⁻¹ = u * (u⁻¹ * a * u * a⁻¹) := by group
    rw [e]
    exact U.mul_mem hu hwU
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key h, fun h' => ?_⟩
  have h2 := key _ (key _ h')
  have e : a * (a * (a * h * a⁻¹) * a⁻¹) * a⁻¹ = a ^ 3 * h * (a ^ 3)⁻¹ := by
    rw [pow_three']
    group
  rwa [e, ha3, one_mul, inv_one, mul_one] at h2

theorem mem_sup_of_two_elt {K₁ K₂ U₁ U₂ : Subgroup Q}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinf : K₁ ⊓ K₂ = ⊥)
    (hU₁ : IsSylowTwoOf U₁ K₁) (hU₂ : IsSylowTwoOf U₂ K₂) {s : Q} (hs : s ∈ K₁ ⊔ K₂)
    (hs₁ : s ∈ Subgroup.normalizer (U₁ : Set Q)) (hs₂ : s ∈ Subgroup.normalizer (U₂ : Set Q))
    {k : ℕ} (hk : s ^ (2 ^ k) = 1) : s ∈ U₁ ⊔ U₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm' : ∀ x ∈ K₂, ∀ y ∈ K₁, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  obtain ⟨s₁, h₁, s₂, h₂, rfl⟩ := L32Comm.exists_mul_of_mem_sup hcomm hs
  have hc : Commute s₁ s₂ := hcomm s₁ h₁ s₂ h₂
  have hk₁ : s₁ ^ (2 ^ k) = 1 := by
    have h1 : s₁ ^ (2 ^ k) * s₂ ^ (2 ^ k) = 1 := by rw [← hc.mul_pow, hk]
    have h2 : s₁ ^ (2 ^ k) = (s₂ ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : s₁ ^ (2 ^ k) ∈ K₁ ⊓ K₂ :=
      ⟨K₁.pow_mem h₁ _, h2 ▸ K₂.inv_mem (K₂.pow_mem h₂ _)⟩
    rw [hinf] at h3
    exact h3
  have hk₂ : s₂ ^ (2 ^ k) = 1 := by
    rw [hc.mul_pow, hk₁, one_mul] at hk
    exact hk
  have hmem : ∀ {K U : Subgroup Q}, IsSylowTwoOf U K → ∀ {g : Q}, g ∈ K →
      g ∈ Subgroup.normalizer (U : Set Q) → g ^ (2 ^ k) = 1 → g ∈ U := by
    intro K U hU g hgK hgN hg
    have hz : IsPGroup 2 ↥(Subgroup.zpowers g) := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hg)
      exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
    have hzN : Subgroup.zpowers g ≤ Subgroup.normalizer (U : Set Q) :=
      (Subgroup.zpowers_le).mpr hgN
    have hsup : IsPGroup 2 ↥(U ⊔ Subgroup.zpowers g) := hU.2.1.to_sup_of_normal_left' hz hzN
    have hle := le_of_isSylowTwoOf hU le_sup_left
      (sup_le hU.1 ((Subgroup.zpowers_le).mpr hgK)) hsup
    exact hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  have hs₁' : s₁ ∈ Subgroup.normalizer (U₁ : Set Q) := by
    have h1 : s₂⁻¹ ∈ Subgroup.normalizer (U₁ : Set Q) :=
      mem_normalizer_of_comm hcomm hU₁.1 (K₂.inv_mem h₂)
    have := Subgroup.mul_mem _ hs₁ h1
    rwa [mul_inv_cancel_right] at this
  have hs₂' : s₂ ∈ Subgroup.normalizer (U₂ : Set Q) := by
    have h1 : s₁⁻¹ ∈ Subgroup.normalizer (U₂ : Set Q) :=
      mem_normalizer_of_comm hcomm' hU₂.1 (K₁.inv_mem h₁)
    have := Subgroup.mul_mem _ h1 hs₂
    rwa [inv_mul_cancel_left] at this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hmem hU₁ h₁ hs₁' hk₁))
    (Subgroup.mem_sup_right (hmem hU₂ h₂ hs₂' hk₂))

theorem isSolvable_borel {K₁ K₂ U₁ U₂ : Subgroup Q}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinf : K₁ ⊓ K₂ = ⊥)
    (hU₁ : IsSylowTwoOf U₁ K₁) (hU₂ : IsSylowTwoOf U₂ K₂) :
    Group.IsSolvable ↥((K₁ ⊔ K₂) ⊓ Subgroup.normalizer (U₁ : Set Q) ⊓
      Subgroup.normalizer (U₂ : Set Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := (K₁ ⊔ K₂) ⊓ Subgroup.normalizer (U₁ : Set Q) ⊓ Subgroup.normalizer (U₂ : Set Q)
    with hB
  set W := U₁ ⊔ U₂ with hW
  have hU₁U₂ : U₁ ≤ Subgroup.normalizer (U₂ : Set Q) := fun x hx =>
    mem_normalizer_of_comm (fun x hx y hy => (hcomm y hy x hx).symm) hU₂.1 (hU₁.1 hx)
  have hU₂U₁ : U₂ ≤ Subgroup.normalizer (U₁ : Set Q) := fun x hx =>
    mem_normalizer_of_comm hcomm hU₁.1 (hU₂.1 hx)
  have hWB : W ≤ B := sup_le
    (le_inf (le_inf (hU₁.1.trans le_sup_left) Subgroup.le_normalizer) hU₁U₂)
    (le_inf (le_inf (hU₂.1.trans le_sup_right) hU₂U₁) Subgroup.le_normalizer)
  have hW2 : IsPGroup 2 ↥W := hU₁.2.1.to_sup_of_normal_right' hU₂.2.1 hU₁U₂
  have hBW : B ≤ Subgroup.normalizer (W : Set Q) := by
    intro g hg
    rw [← A38.map_conj_eq_iff, hW, Subgroup.map_sup, A38.map_conj_eq_iff.mpr hg.1.2,
      A38.map_conj_eq_iff.mpr hg.2]
  have hWn : (W.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWB).mpr hBW
  have hodd : Odd (Nat.card (↥B ⧸ W.subgroupOf B)) := by
    rw [Nat.odd_iff]
    by_contra h
    have h2 : 2 ∣ Nat.card (↥B ⧸ W.subgroupOf B) := by omega
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥B ⧸ W.subgroupOf B) 2 h2
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    have hs2 : (s : ↥B) ^ 2 ∈ W.subgroupOf B := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
    obtain ⟨j, hj⟩ := L32Comm.exists_pow_of_isPGroup hW2 (Subgroup.mem_subgroupOf.mp hs2)
    have hsk : (s : Q) ^ (2 ^ (j + 1)) = 1 := by
      rw [pow_succ', pow_mul, ← Subgroup.coe_pow, hj]
    have hsW := mem_sup_of_two_elt hcomm hinf hU₁ hU₂ s.2.1.1 s.2.1.2 s.2.2 hsk
    have h1 : (QuotientGroup.mk s : ↥B ⧸ W.subgroupOf B) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hsW)
    rw [h1, orderOf_one] at hq
    exact absurd hq (by norm_num)
  have hq : Group.IsSolvable (↥B ⧸ W.subgroupOf B) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact F1.isSolvable_of_normal_subgroupOf hWB (F1.isSolvable_of_isPGroup_two hW2) hq

omit [Finite Q] in
theorem nine_dvd_card {K₁ K₂ B : Subgroup Q} (hinf : K₁ ⊓ K₂ = ⊥)
    (hBK : B ≤ Subgroup.normalizer (K₁ : Set Q)) {a b : Q} (haB : a ∈ B) (haK : a ∈ K₁)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hbB : b ∈ B) (hbK : b ∈ K₂) (hb3 : b ^ 3 = 1)
    (hb1 : b ≠ 1) : 9 ∣ Nat.card B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := (B ⊓ K₁).subgroupOf B with hA
  have hAn : A.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    (F7.le_normalizer_inf Subgroup.le_normalizer hBK)
  have h1 : 3 ∣ Nat.card A := by
    have ha : (⟨⟨a, haB⟩, Subgroup.mem_subgroupOf.mpr ⟨haB, haK⟩⟩ : A) ^ 3 = 1 :=
      Subtype.ext (Subtype.ext (by simp [ha3]))
    have ha' : (⟨⟨a, haB⟩, Subgroup.mem_subgroupOf.mpr ⟨haB, haK⟩⟩ : A) ≠ 1 := fun h =>
      ha1 (by simpa using congrArg (fun x : A => ((x : ↥B) : Q)) h)
    rw [← orderOf_eq_prime ha ha']
    exact orderOf_dvd_natCard _
  have h2 : 3 ∣ A.index := by
    rw [Subgroup.index_eq_card]
    have hb : (QuotientGroup.mk (⟨b, hbB⟩ : ↥B) : ↥B ⧸ A) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨b, hbB⟩ : ↥B) ^ 3 = 1 := Subtype.ext (by simp [hb3])
      rw [this, QuotientGroup.mk_one]
    have hb' : (QuotientGroup.mk (⟨b, hbB⟩ : ↥B) : ↥B ⧸ A) ≠ 1 := by
      intro h
      have h3 := (QuotientGroup.eq_one_iff _).mp h
      rw [hA, Subgroup.mem_subgroupOf] at h3
      have h4 : b ∈ K₁ ⊓ K₂ := ⟨h3.2, hbK⟩
      rw [hinf] at h4
      exact hb1 h4
    rw [← orderOf_eq_prime hb hb']
    exact orderOf_dvd_natCard _
  rw [← A.card_mul_index]
  exact Nat.mul_dvd_mul h1 h2

end L2Comm

end CFSG.Quasithin.H13.A6

