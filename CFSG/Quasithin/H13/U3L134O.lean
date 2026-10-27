module

public import CFSG.Quasithin.H13.U3U33Fixed
public import CFSG.Quasithin.H13.L32NNotation
public import CFSG.Quasithin.H13.U3L15Core
public import CFSG.Quasithin.Recognition.HSTypeModels

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

@[expose] def SylOvergroupProp (Q : Type) [Group Q] [Finite Q] : Prop :=
  ∀ H : Subgroup Q, (∃ S : Sylow 2 Q, (S : Subgroup Q) ≤ H) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → (∃ y ∈ H, orderOf y = p) → H = ⊤

theorem SylOvergroupProp.of_mulEquiv {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂] [Finite Q₁]
    [Finite Q₂] (e : Q₁ ≃* Q₂) (h : SylOvergroupProp Q₂) : SylOvergroupProp Q₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro H ⟨S, hS⟩ p hp hp2 hp3 ⟨y, hyH, hy⟩
  have hH := h (H.map e.toMonoidHom) ⟨S.mapSurjective e.surjective, by
      rw [Sylow.coe_mapSurjective]
      exact Subgroup.map_mono hS⟩ p hp hp2 hp3
    ⟨e y, ⟨y, hyH, rfl⟩, by rw [MulEquiv.orderOf_eq, hy]⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨x', hx', hxx'⟩ := hH ▸ mem_top (e x)
  rwa [e.injective hxx'] at hx'

theorem index_ne_three {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q] (h6 : 6 < Nat.card Q)
    (H : Subgroup Q) : H.index ≠ 3 := by
  intro h3
  have hdvd := H.index_normalCore_dvd_factorial_index
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
  · rw [h, index_bot, h3] at hdvd
    have := Nat.le_of_dvd (by decide) hdvd
    simp only [Nat.factorial] at this
    omega
  · have hH : H = ⊤ := eq_top_iff.2 (h ▸ H.normalCore_le)
    rw [hH, index_top] at h3
    omega

theorem card_sylow_two_eq {Q : Type} [Group Q] [Finite Q] (S : Sylow 2 Q) {a m : ℕ}
    (hQ : Nat.card Q = 2 ^ a * m) (hm : ¬ 2 ∣ m) : Nat.card S = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [S.card_eq_multiplicity, hQ]
  congr 1
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem orderOf_dvd_card_of_mem {Q : Type} [Group Q] [Finite Q] {H : Subgroup Q} {y : Q}
    (hy : y ∈ H) : orderOf y ∣ Nat.card H := by
  have := orderOf_dvd_natCard (⟨y, hy⟩ : H)
  rwa [Subgroup.orderOf_mk] at this

theorem eq_of_prime_dvd {p a b r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hr : r.Prime)
    (h : p ∣ 2 ^ a * (3 ^ b * r)) : p = r := by
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)) hp2
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h2)) hp3
    · exact (Nat.prime_dvd_prime_iff_eq hp hr).1 h2

theorem sylOvergroupProp_of_simple {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q] {a r : ℕ}
    (hQ : Nat.card Q = 2 ^ a * (3 * r)) (hr : r.Prime) (hr2 : r ≠ 2) (h6 : 6 < Nat.card Q) :
    SylOvergroupProp Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro H ⟨S, hS⟩ p hp hp2 hp3 ⟨y, hyH, hy⟩
  have hpr : p = r := by
    have h := hy ▸ orderOf_dvd_natCard y
    rw [hQ] at h
    exact eq_of_prime_dvd (b := 1) hp hp2 hp3 hr (by simpa using h)
  subst hpr
  have hm : ¬ 2 ∣ 3 * p := by
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
    · exact absurd h (by decide)
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).1 h).symm
  have h1 : 2 ^ a ∣ Nat.card H := card_sylow_two_eq S hQ hm ▸ card_dvd_of_le hS
  have h2 : p ∣ Nat.card H := hy ▸ orderOf_dvd_card_of_mem hyH
  have hcop : Nat.Coprime (2 ^ a) p :=
    Nat.Coprime.pow_left a ((Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2))
  obtain ⟨c, hc⟩ := hcop.mul_dvd_of_dvd_of_dvd h1 h2
  have hidx := card_mul_index H
  rw [hc, hQ] at hidx
  have hpos : 0 < 2 ^ a * p := Nat.mul_pos (pow_pos (by norm_num) a) hr.pos
  have h3 : c * H.index = 3 := by
    have : 2 ^ a * p * (c * H.index) = 2 ^ a * p * 3 := by
      calc 2 ^ a * p * (c * H.index) = 2 ^ a * p * c * H.index := by ring
        _ = 2 ^ a * (3 * p) := hidx
        _ = 2 ^ a * p * 3 := by ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hi : H.index ∣ 3 := ⟨c, by rw [← h3, mul_comm]⟩
  rcases (Nat.dvd_prime Nat.prime_three).1 hi with h | h
  · exact index_eq_one.1 h
  · exact absurd h (index_ne_three h6 H)

abbrev Alt6G : Type := ↥(alternatingGroup (Fin 6))

@[expose] def c5 : Perm (Fin 6) := swap 0 4 * swap 0 3 * swap 0 2 * swap 0 1

@[expose] def u4 : Perm (Fin 6) := swap 1 3 * swap 1 4 * swap 1 2

@[expose] def n20 : List (Perm (Fin 6)) :=
  (List.range 5).flatMap fun i => (List.range 4).map fun j => c5 ^ i * u4 ^ j

theorem c5_codes : Perm.sign c5 = 1 ∧ c5 ^ 5 = 1 ∧ c5 ≠ 1 := by
  decide +kernel

theorem normalizer_c5_codes : ∀ σ : Perm (Fin 6), σ * c5 * σ⁻¹ ∈ [c5, c5 ^ 2, c5 ^ 3, c5 ^ 4] →
    σ ∈ n20 := by
  decide +kernel

theorem n20_length : n20.length = 20 := by
  decide

theorem card_alt6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

@[expose] def c5A : ↥(alternatingGroup (Fin 6)) := ⟨c5, Perm.mem_alternatingGroup.2 c5_codes.1⟩

theorem orderOf_c5A : orderOf c5A = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime (Subtype.ext ?_) fun h => c5_codes.2.2 (congrArg Subtype.val h)
  rw [Subgroup.coe_pow]
  exact c5_codes.2.1

theorem card_normalizer_c5_le :
    Nat.card (normalizer ((zpowers c5A : Subgroup Alt6G) : Set Alt6G)) ≤ 20 := by
  classical
  set N := normalizer ((zpowers c5A : Subgroup Alt6G) : Set Alt6G)
  have hmem : ∀ σ : N, ((σ : Alt6G) : Perm (Fin 6)) ∈ n20 := by
    intro σ
    apply normalizer_c5_codes
    have h1 : (σ : Alt6G) * c5A * (σ : Alt6G)⁻¹ ∈ zpowers c5A :=
      (mem_normalizer_iff.1 σ.2 c5A).1 (mem_zpowers c5A)
    rw [mem_zpowers_iff_mem_range_orderOf, orderOf_c5A, Finset.mem_image] at h1
    obtain ⟨k, hk, hkc⟩ := h1
    have hk' : ((σ : Alt6G) : Perm (Fin 6)) * c5 * ((σ : Alt6G) : Perm (Fin 6))⁻¹ = c5 ^ k := by
      have := congrArg Subtype.val hkc
      simpa [c5A] using this.symm
    rw [hk']
    rw [Finset.mem_range] at hk
    interval_cases k
    · exfalso
      apply c5_codes.2.2
      have h2 : c5 = ((σ : Alt6G) : Perm (Fin 6))⁻¹ *
          (((σ : Alt6G) : Perm (Fin 6)) * c5 * ((σ : Alt6G) : Perm (Fin 6))⁻¹) *
          ((σ : Alt6G) : Perm (Fin 6)) := by group
      rw [h2, hk', pow_zero]
      group
    · simp
    · simp
    · simp
    · simp
  have hinj : Function.Injective fun σ : N => ((σ : Alt6G) : Perm (Fin 6)) :=
    fun a b h => Subtype.ext (Subtype.ext h)
  calc Nat.card N = Fintype.card N := Nat.card_eq_fintype_card
    _ ≤ n20.toFinset.card := by
        refine Finset.card_le_card_of_injOn (fun σ : N => ((σ : Alt6G) : Perm (Fin 6)))
          (fun σ _ => List.mem_toFinset.2 (hmem σ)) (fun a _ b _ h => hinj h)
    _ ≤ n20.length := List.toFinset_card_le _
    _ = 20 := n20_length

theorem le_normalizer_zpowers_of_card_forty {K : Type} [Group K] [Finite K] {H : Subgroup K}
    (hH : Nat.card H = 40) {y : K} (hyH : y ∈ H) (hy : orderOf y = 5) :
    H ≤ normalizer ((zpowers y : Subgroup K) : Set K) := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set P : Subgroup ↥H := zpowers (⟨y, hyH⟩ : ↥H) with hPdef
  have hPc : Nat.card P = 5 := by
    rw [hPdef, Nat.card_zpowers, Subgroup.orderOf_mk, hy]
  have hP5 : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by rw [hPc, pow_one])
  have hPi : P.index = 8 := by
    have h := card_mul_index P
    rw [hPc, hH] at h
    omega
  let PS : Sylow 5 ↥H := hP5.toSylow (by rw [hPi]; decide)
  have hn : Nat.card (Sylow 5 ↥H) = 1 := by
    have h1 := card_sylow_modEq_one 5 ↥H
    have h2 : Nat.card (Sylow 5 ↥H) ∣ 2 ^ 3 := by
      have := Sylow.card_dvd_index PS
      exact this.trans (by rw [show (PS : Subgroup ↥H) = P from rfl, hPi]; norm_num)
    obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    unfold Nat.ModEq at h1
    rw [hie] at h1 ⊢
    interval_cases i <;> simp_all
  have : Subsingleton (Sylow 5 ↥H) := (Nat.card_eq_one_iff_unique.1 hn).1
  have hnorm : (PS : Subgroup ↥H).Normal := Sylow.normal_of_subsingleton PS
  have key : ∀ t ∈ H, ∀ x ∈ zpowers y, t * x * t⁻¹ ∈ zpowers y := by
    intro t ht x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    have hx' : (⟨y, hyH⟩ : ↥H) ^ k ∈ (PS : Subgroup ↥H) := zpow_mem (mem_zpowers _) k
    have h1 := hnorm.conj_mem _ hx' ⟨t, ht⟩
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h1
    refine mem_zpowers_iff.2 ⟨j, ?_⟩
    have := congrArg Subtype.val hj
    simpa using this
  intro s hs
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key s hs x, fun hx => ?_⟩
  have := key s⁻¹ (inv_mem hs) _ hx
  rwa [show s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x by group] at this

theorem false_of_le_normalizer_zpowers {S : Subgroup Alt6G} (hS : Nat.card S = 8) {y : Alt6G}
    (hy : orderOf y = 5) (hSN : S ≤ normalizer ((zpowers y : Subgroup Alt6G) : Set Alt6G)) :
    False := by
  classical
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hA := card_alt6
  have hy5 : IsPGroup 5 (zpowers y) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hy, pow_one])
  have hyi : (zpowers y).index = 72 := by
    have h := card_mul_index (zpowers y)
    rw [Nat.card_zpowers, hy, hA] at h
    omega
  have hc5 : IsPGroup 5 (zpowers c5A) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_c5A, pow_one])
  have hci : (zpowers c5A).index = 72 := by
    have h := card_mul_index (zpowers c5A)
    rw [Nat.card_zpowers, orderOf_c5A, hA] at h
    omega
  let Sy : Sylow 5 Alt6G := hy5.toSylow (by rw [hyi]; decide)
  let Sc : Sylow 5 Alt6G := hc5.toSylow (by rw [hci]; decide)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Alt6G Sy Sc
  have hsm : ∀ x : Alt6G, (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := fun x => by
    simp [MulAut.smul_def, mul_assoc]
  have hconj : ∀ x, x ∈ zpowers y → g * x * g⁻¹ ∈ zpowers c5A := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ ((g • Sy : Sylow 5 Alt6G) : Subgroup Alt6G) := by
      rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, hsm,
        show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      exact hx
    rw [hg] at h1
    exact h1
  have hconj' : ∀ x, x ∈ zpowers c5A → g⁻¹ * x * g ∈ zpowers y := by
    intro x hx
    have h1 : x ∈ ((g • Sy : Sylow 5 Alt6G) : Subgroup Alt6G) := by
      rw [hg]
      exact hx
    rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, hsm] at h1
    exact h1
  set S' := S.map (MulAut.conj g).toMonoidHom with hS'
  have hS'N : S' ≤ normalizer ((zpowers c5A : Subgroup Alt6G) : Set Alt6G) := by
    rintro _ ⟨s, hs, rfl⟩
    have hsN := hSN hs
    rw [mem_normalizer_iff] at hsN ⊢
    intro x
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro hx
      have h1 := (hsN (g⁻¹ * x * g)).1 (hconj' x hx)
      have h2 := hconj _ h1
      rwa [show g * (s * (g⁻¹ * x * g) * s⁻¹) * g⁻¹ = g * s * g⁻¹ * x * (g * s * g⁻¹)⁻¹ by
        group] at h2
    · intro hx
      have h1 := hconj' _ hx
      rw [show g⁻¹ * (g * s * g⁻¹ * x * (g * s * g⁻¹)⁻¹) * g = s * (g⁻¹ * x * g) * s⁻¹ by
        group] at h1
      have h2 := (hsN (g⁻¹ * x * g)).2 h1
      have h3 := hconj _ h2
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h3
  have hS'c : Nat.card S' = 8 := by
    rw [hS', Subgroup.card_map_of_injective (MulAut.conj g).injective, hS]
  have h8 : 8 ∣ Nat.card (normalizer ((zpowers c5A : Subgroup Alt6G) : Set Alt6G)) :=
    hS'c ▸ card_dvd_of_le hS'N
  have h5' : 5 ∣ Nat.card (normalizer ((zpowers c5A : Subgroup Alt6G) : Set Alt6G)) := by
    have := card_dvd_of_le (le_normalizer (H := zpowers c5A))
    rwa [Nat.card_zpowers, orderOf_c5A] at this
  have h40 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 5) h8 h5'
  have hle := card_normalizer_c5_le
  have := Nat.le_of_dvd Nat.card_pos h40
  omega

theorem sylOvergroupProp_alt6 : SylOvergroupProp ↥(alternatingGroup (Fin 6)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rintro H ⟨S, hS⟩ p hp hp2 hp3 ⟨y, hyH, hy⟩
  have hA := card_alt6
  have hp5 : p = 5 := by
    have h := hy ▸ orderOf_dvd_natCard y
    rw [hA] at h
    exact eq_of_prime_dvd (a := 3) (b := 2) hp hp2 hp3 (by norm_num) (by simpa using h)
  subst hp5
  have hS8 : Nat.card S = 8 :=
    card_sylow_two_eq S (a := 3) (m := 45) (by rw [hA]; norm_num) (by decide)
  have h1 : 8 ∣ Nat.card H := hS8 ▸ card_dvd_of_le hS
  have h2 : 5 ∣ Nat.card H := hy ▸ orderOf_dvd_card_of_mem hyH
  obtain ⟨c, hc⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 5) h1 h2
  have hidx := card_mul_index H
  rw [hc, hA] at hidx
  have h9 : c * H.index = 9 := by
    have : 40 * (c * H.index) = 40 * 9 := by
      calc 40 * (c * H.index) = 8 * 5 * c * H.index := by ring
        _ = 360 := hidx
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hi : H.index ∣ 9 := ⟨c, by rw [← h9, mul_comm]⟩
  have hi' : H.index = 1 ∨ H.index = 3 ∨ H.index = 9 := by
    have : H.index ≤ 9 := Nat.le_of_dvd (by norm_num) hi
    interval_cases hH : H.index <;> simp_all
  rcases hi' with h | h | h
  · exact index_eq_one.1 h
  · exact absurd h (index_ne_three (by rw [hA]; norm_num) H)
  · exfalso
    have hc1 : c = 1 := by rw [h] at h9; omega
    rw [hc1, mul_one] at hc
    exact false_of_le_normalizer_zpowers hS8 hy
      (hS.trans (le_normalizer_zpowers_of_card_forty (by rw [hc]) hyH hy))

theorem SylOvergroupProp.of_center {Q : Type} [Group Q] [Finite Q] (hperf : Group.IsPerfect Q)
    (hZ : Nat.card (center Q) = 3) (h : SylOvergroupProp (Q ⧸ center Q)) : SylOvergroupProp Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro H ⟨S, hS⟩ p hp hp2 hp3 ⟨y, hyH, hy⟩
  set π := QuotientGroup.mk' (center Q) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hyZ : y ∉ center Q := by
    intro hyZ
    have h1 := orderOf_dvd_card_of_mem hyZ
    rw [hZ, hy] at h1
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1)
  have hy' : orderOf (π y) = p := by
    have : Fact p.Prime := ⟨hp⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
    · intro h1
      apply hyZ
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hHb := h (H.map π) ⟨S.mapSurjective hπs, by
      rw [Sylow.coe_mapSurjective]
      exact Subgroup.map_mono hS⟩ p hp hp2 hp3 ⟨π y, ⟨y, hyH, rfl⟩, hy'⟩
  have hdec : ∀ q : Q, ∃ x ∈ H, ∃ z ∈ center Q, q = x * z := by
    intro q
    obtain ⟨x, hx, hxq⟩ := hHb ▸ mem_top (π q)
    refine ⟨x, hx, x⁻¹ * q, ?_, by group⟩
    have : π (x⁻¹ * q) = 1 := by rw [map_mul, map_inv, hxq, inv_mul_cancel]
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  have key1 : ∀ a b z : Q, z ∈ center Q → ⁅a * z, b⁆ = ⁅a, b⁆ := by
    intro a b z hz
    have h1 : b * z = z * b := mem_center_iff.1 hz b
    rw [commutatorElement_def, commutatorElement_def]
    calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
      _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [h1]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  have key2 : ∀ a b z : Q, z ∈ center Q → ⁅a, b * z⁆ = ⁅a, b⁆ := by
    intro a b z hz
    have h1 : a⁻¹ * z = z * a⁻¹ := mem_center_iff.1 hz a⁻¹
    rw [commutatorElement_def, commutatorElement_def]
    calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [h1]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  have hcomm : commutator Q ≤ H := by
    rw [commutator_def, commutator_le]
    intro a _ b _
    obtain ⟨x₁, hx₁, z₁, hz₁, rfl⟩ := hdec a
    obtain ⟨x₂, hx₂, z₂, hz₂, rfl⟩ := hdec b
    rw [key1 _ _ _ hz₁, key2 _ _ _ hz₂, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx₁ hx₂) (inv_mem hx₁)) (inv_mem hx₂)
  rw [eq_top_iff, ← hperf.commutator_eq_top]
  exact hcomm

theorem prime_dvd_two_three {p b : ℕ} (hp : p.Prime) (h : p ∣ 2 ^ 5 * 3 ^ b) : p = 2 ∨ p = 3 := by
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h1))

theorem sylOvergroupProp_u33 :
    SylOvergroupProp U33G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro H ⟨S, hS⟩ p hp hp2 hp3 ⟨y, hyH, hy⟩
  let T₀ : Sylow 2 U33G := u33_syl.1.toSylow u33_syl.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq U33G S T₀
  set H' := H.map (MulAut.conj g).toMonoidHom with hH'
  have hTH' : u33Data.T ≤ H' := by
    intro t ht
    have ht' : t ∈ ((g • S : Sylow 2 U33G) : Subgroup U33G) := by
      rw [hg]
      exact ht
    rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at ht'
    refine ⟨g⁻¹ * t * g, hS (by simpa [MulAut.smul_def, mul_assoc] using ht'), ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hpH' : p ∣ Nat.card H' := by
    have h1 : (MulAut.conj g) y ∈ H' := ⟨y, hyH, rfl⟩
    have h2 := orderOf_dvd_card_of_mem h1
    rwa [MulEquiv.orderOf_eq, hy] at h2
  rcases u33Data.lattice H' hTH' with h | h | h | h
  · rw [h, u33_card_T] at hpH'
    rcases prime_dvd_two_three (b := 0) hp (by simpa using hpH') with h1 | h1
    · exact absurd h1 hp2
    · exact absurd h1 hp3
  · rw [h, card_u33_A] at hpH'
    rcases prime_dvd_two_three (b := 1) hp (by simpa using hpH') with h1 | h1
    · exact absurd h1 hp2
    · exact absurd h1 hp3
  · rw [h, card_u33_B] at hpH'
    rcases prime_dvd_two_three (b := 1) hp (by simpa using hpH') with h1 | h1
    · exact absurd h1 hp2
    · exact absurd h1 hp3
  · rw [eq_top_iff]
    intro x _
    obtain ⟨x', hx', hxx'⟩ := h ▸ mem_top ((MulAut.conj g) x)
    rwa [(MulAut.conj g).injective hxx'] at hx'

theorem sylOvergroupProp_of_qt13Five
    {Q : Type} [Group Q] [Finite Q] (h : QT13Five Q) :
    SylOvergroupProp Q := by
  rcases h with ⟨⟨e⟩⟩ | h | ⟨⟨e⟩⟩ | ⟨hperf, hZ, ⟨e⟩⟩ | h
  · have hs : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have hc : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    exact SylOvergroupProp.of_mulEquiv e (sylOvergroupProp_of_simple (a := 2) (r := 5)
      (by rw [hc]; norm_num) (by norm_num) (by norm_num) (by rw [hc]; norm_num))
  · obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel h
    have hs := HSType.isSimpleGroup_SL_three_two
    have hc := HSType.card_SL_three_two
    exact SylOvergroupProp.of_mulEquiv e (sylOvergroupProp_of_simple (a := 3) (r := 7)
      (by rw [hc]; norm_num) (by norm_num) (by norm_num) (by rw [hc]; norm_num))
  · exact SylOvergroupProp.of_mulEquiv e sylOvergroupProp_alt6
  · exact SylOvergroupProp.of_center hperf hZ (SylOvergroupProp.of_mulEquiv e sylOvergroupProp_alt6)
  · obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel h
    obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
    exact SylOvergroupProp.of_mulEquiv (e1.trans e2.symm) sylOvergroupProp_u33

variable {G : Type} [Group G]

theorem isTwoThreeGroup_of_overgroup [Finite G] {T L X : Subgroup G} (hT : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G)) (hsyl : IsSylowTwoOf (T ⊓ L) L) (hOT : pCoreOf 2 L ≤ T)
    (hprop : SylOvergroupProp (↥L ⧸ CFSG.pCore 2 ↥L)) (hTX : T ≤ X) (hX : X < L ⊔ T) :
    A6.IsTwoThreeGroup X := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro p hp hpX
  by_contra hne
  push Not at hne
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) p hpX
  have hxo : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L T hTL
  obtain ⟨l, hl, t, ht, hxlt⟩ : (x : G) ∈ (L : Set G) * (T : Set G) := by
    rw [← hmul]
    exact hX.le x.2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by
    rw [← Subgroup.orderOf_coe] at hk
    rw [← hk]
    exact pow_orderOf_eq_one t
  obtain ⟨l', hl', he⟩ := pow_mem_mul_of_normalizes' hl (hTL ht) (2 ^ k)
  have hxk : (x : G) ^ 2 ^ k ∈ L := by
    rw [← hxlt, he, htk, mul_one]
    exact hl'
  have hodd : Odd p := hp.odd_of_ne_two hne.1
  have hxL : (x : G) ∈ L :=
    mem_of_pow_two_pow_mem hxk hodd (by rw [← hxo]; exact pow_orderOf_eq_one _)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  set H : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := (X.subgroupOf L).map π with hHdef
  have hP : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
    hsyl.2.1.of_equiv (subgroupOfEquivOfLe hsyl.1).symm
  let P : Sylow 2 ↥L := hP.toSylow hsyl.2.2
  have hSH : ((P.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)) :
      Sylow 2 _) : Subgroup _) ≤ H := by
    rw [Sylow.coe_mapSurjective]
    refine map_mono fun z hz => mem_subgroupOf.2 (hTX ?_)
    exact (mem_inf.1 (mem_subgroupOf.1 (show z ∈ (T ⊓ L).subgroupOf L from hz))).1
  have hyH : π ⟨x, hxL⟩ ∈ H := ⟨⟨x, hxL⟩, mem_subgroupOf.2 x.2, rfl⟩
  have hyo : orderOf (π ⟨x, hxL⟩) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have : (⟨x, hxL⟩ : ↥L) ^ p = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxo]
        exact pow_orderOf_eq_one _)
      rw [this, map_one]
    · intro h1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, h1⟩
      have hj' : (x : G) ^ 2 ^ j = 1 := by
        have := congrArg (fun w => ((w : ↥L) : G)) (congrArg Subtype.val hj)
        simpa using this
      have h3 := orderOf_dvd_of_pow_eq_one hj'
      rw [hxo] at h3
      exact hne.1 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3))
  have hHt := hprop H ⟨_, hSH⟩ p hp hne.1 hne.2 ⟨_, hyH, hyo⟩
  have hLX : L ≤ X := by
    intro l hl
    obtain ⟨y, hy, hyl⟩ := hHt ▸ mem_top (π ⟨l, hl⟩)
    have h1 : y⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hyl
      exact QuotientGroup.eq.1 hyl
    have h3 : ((y⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ X := hTX (hOT (coe_mem_pCoreOf_iff.2 h1))
    have h4 : (y : G) ∈ X := mem_subgroupOf.1 hy
    have e : l = (y : G) * ((y⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [e]
    exact mul_mem h4 h3
  exact hX.ne (le_antisymm hX.le (sup_le hLX hTX))

end CFSG.Quasithin.H13.U3
