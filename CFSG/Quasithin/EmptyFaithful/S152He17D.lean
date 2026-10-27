module

public import CFSG.Quasithin.EmptyFaithful.S152He17C

public section

namespace CFSG.Quasithin.He17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
  CFSG.Quasithin.He16
open scoped commutatorElement Pointwise

theorem swap_comm_identity {α : Type*} [DecidableEq α] (u0 u1 u2 u3 : α)
    (h01 : u0 ≠ u1) (h02 : u0 ≠ u2) (h03 : u0 ≠ u3) (h12 : u1 ≠ u2) (h13 : u1 ≠ u3)
    (h23 : u2 ≠ u3) :
    Equiv.swap u1 u2 * Equiv.swap u1 u3 * Equiv.swap u0 u2 * Equiv.swap u0 u1 =
      Equiv.swap u0 u2 * Equiv.swap u0 u3 := by
  ext z
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem swap_comm_of_fixed {α : Type*} [DecidableEq α] {σ : Equiv.Perm α} {x y : α}
    (hx : σ x = x) (hy : σ y = y) : σ * Equiv.swap x y = Equiv.swap x y * σ := by
  have h := Equiv.swap_apply_apply σ x y
  rw [hx, hy, eq_comm, mul_inv_eq_iff_eq_mul] at h
  exact h

theorem orbit_distinct {α : Type*} (a : Equiv.Perm α) (ha5 : a ^ 5 = 1) {x : α} (hx : a x ≠ x) :
    Set.InjOn (fun i => (⇑a)^[i] x) (Set.Iio 5) := by
  have hper : Function.IsPeriodicPt (⇑a) 5 x := by
    show (⇑a)^[5] x = x
    rw [Equiv.Perm.iterate_eq_pow, ha5]; rfl
  rcases (Nat.dvd_prime Nat.prime_five).mp hper.minimalPeriod_dvd with h1 | h5
  · exact absurd (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h1) hx
  · have := (Function.iterate_injOn_Iio_minimalPeriod (f := ⇑a) (x := x))
    rwa [h5] at this

theorem exists_three_dvd_orderOf {α : Type*} [DecidableEq α] [Fintype α] {Y : Subgroup (Equiv.Perm α)}
    {a σ : Equiv.Perm α} {p q : α} (hpq : p ≠ q) (hσ : σ = Equiv.swap p q) (ha5 : orderOf a = 5)
    (haY : a ∈ Y) (hac : σ * a = a * σ)
    (hN : ∀ τ : Equiv.Perm α, τ.IsThreeCycle → σ * τ = τ * σ → ∀ y ∈ Y, τ * y * τ⁻¹ ∈ Y) :
    ∃ g ∈ Y, 3 ∣ orderOf g := by
  have ha5' : a ^ 5 = 1 := ha5 ▸ pow_orderOf_eq_one a
  have hane : a ≠ 1 := by
    rintro rfl
    simp at ha5
  have hfix : a p = p ∧ a q = q := by
    have h1 : Equiv.swap (a p) (a q) = Equiv.swap p q := by
      rw [Equiv.swap_apply_apply, ← hσ, ← hac]; group
    have h2 : Equiv.swap (a p) (a q) p = Equiv.swap p q p := by rw [h1]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_def] at h2
    split_ifs at h2 with hp hq
    · exact ⟨hp.symm, h2⟩
    · exfalso
      have hap2 : a (a p) = p := by rw [h2, ← hq]
      have h22 : (a ^ 2) p = p := by rw [pow_two, Equiv.Perm.mul_apply, hap2]
      have h4 : (a ^ 4) p = p := by
        rw [show a ^ 4 = a ^ 2 * a ^ 2 by rw [← pow_add], Equiv.Perm.mul_apply, h22, h22]
      have h5 : (a ^ 5) p = a p := by
        rw [show a ^ 5 = a * a ^ 4 by rw [← pow_succ'], Equiv.Perm.mul_apply, h4]
      rw [ha5', Equiv.Perm.one_apply, h2] at h5
      exact hpq h5
    · exact absurd h2 hpq
  obtain ⟨x, hx⟩ : ∃ x, a x ≠ x := by
    by_contra h
    push Not at h
    exact hane (Equiv.ext h)
  have hnot : ∀ r, a r = r → ∀ k, (⇑a)^[k] x ≠ r := by
    intro r hr k hk
    have h1 : (⇑a)^[k] r = r := Function.iterate_fixed hr k
    have h2 : x = r := (Function.Injective.iterate a.injective k) (hk.trans h1.symm)
    exact hx (by rw [h2, hr])
  have hinj := orbit_distinct a ha5' hx
  have h01 : x ≠ a x := hx.symm
  have h02 : x ≠ a (a x) := fun h =>
    absurd (hinj (show 0 ∈ Set.Iio 5 by simp) (show 2 ∈ Set.Iio 5 by simp) h) (by norm_num)
  have h03 : x ≠ a (a (a x)) := fun h =>
    absurd (hinj (show 0 ∈ Set.Iio 5 by simp) (show 3 ∈ Set.Iio 5 by simp) h) (by norm_num)
  have h12 : a x ≠ a (a x) := fun h =>
    absurd (hinj (show 1 ∈ Set.Iio 5 by simp) (show 2 ∈ Set.Iio 5 by simp) h) (by norm_num)
  have h13 : a x ≠ a (a (a x)) := fun h =>
    absurd (hinj (show 1 ∈ Set.Iio 5 by simp) (show 3 ∈ Set.Iio 5 by simp) h) (by norm_num)
  have h23 : a (a x) ≠ a (a (a x)) := fun h =>
    absurd (hinj (show 2 ∈ Set.Iio 5 by simp) (show 3 ∈ Set.Iio 5 by simp) h) (by norm_num)
  have hσ0 : σ x = x := by
    rw [hσ]; exact Equiv.swap_apply_of_ne_of_ne (hnot p hfix.1 0) (hnot q hfix.2 0)
  have hσ1 : σ (a x) = a x := by
    rw [hσ]; exact Equiv.swap_apply_of_ne_of_ne (hnot p hfix.1 1) (hnot q hfix.2 1)
  have hσ2 : σ (a (a x)) = a (a x) := by
    rw [hσ]; exact Equiv.swap_apply_of_ne_of_ne (hnot p hfix.1 2) (hnot q hfix.2 2)
  set τ : Equiv.Perm α := Equiv.swap x (a x) * Equiv.swap x (a (a x)) with hτ
  have hτ3 : τ.IsThreeCycle := Equiv.Perm.isThreeCycle_swap_mul_swap_same h01 h02 h12
  have hστ : σ * τ = τ * σ := by
    rw [hτ, ← mul_assoc, swap_comm_of_fixed hσ0 hσ1, mul_assoc, swap_comm_of_fixed hσ0 hσ2,
      ← mul_assoc]
  have hg := Y.mul_mem haY (hN τ hτ3 hστ a⁻¹ (Y.inv_mem haY))
  refine ⟨_, hg, ?_⟩
  have hconj : ∀ u v : α, a * Equiv.swap u v * a⁻¹ = Equiv.swap (a u) (a v) := fun u v =>
    (Equiv.swap_apply_apply a u v).symm
  have hEq : a * (τ * a⁻¹ * τ⁻¹) = Equiv.swap x (a (a x)) * Equiv.swap x (a (a (a x))) := by
    have e1 : a * (τ * a⁻¹ * τ⁻¹) =
        ((a * Equiv.swap x (a x) * a⁻¹) * (a * Equiv.swap x (a (a x)) * a⁻¹)) * τ⁻¹ := by
      rw [hτ]; group
    rw [e1, hconj, hconj, hτ, mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]
    rw [← swap_comm_identity x (a x) (a (a x)) (a (a (a x))) h01 h02 h03 h12 h13 h23]
    group
  rw [hEq, (Equiv.Perm.isThreeCycle_swap_mul_swap_same h02 h03 h23).orderOf]

section A6

open Equiv Equiv.Perm

theorem fix_card {τ : Perm (Fin 6)} (h : orderOf τ = 5) :
    Fintype.card (Function.fixedPoints τ) = 1 := by
  have hne : τ ≠ 1 := by rintro rfl; simp at h
  have hall : ∀ n ∈ τ.cycleType, n = 5 := by
    intro n hn
    have h1 : n ∣ 5 := h ▸ Equiv.Perm.dvd_of_mem_cycleType hn
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
    rcases (Nat.dvd_prime Nat.prime_five).mp h1 with h3 | h3
    · omega
    · exact h3
  have hrep : τ.cycleType = Multiset.replicate (Multiset.card τ.cycleType) 5 :=
    Multiset.eq_replicate_card.mpr hall
  have hsum : τ.cycleType.sum = 5 * Multiset.card τ.cycleType := by
    conv_lhs => rw [hrep]
    rw [Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hpos : Multiset.card τ.cycleType ≠ 0 := by
    intro h0
    exact hne (Equiv.Perm.cycleType_eq_zero.mp (Multiset.card_eq_zero.mp h0))
  have hle : τ.cycleType.sum ≤ 6 := by
    rw [Equiv.Perm.sum_cycleType]
    simpa using Finset.card_le_univ τ.support
  have hcard := Equiv.Perm.card_fixedPoints τ
  rw [hcard, Fintype.card_fin]
  omega

theorem stab_card (z : Fin 6) :
    Nat.card (MulAction.stabilizer (alternatingGroup (Fin 6)) z) = 60 := by
  have hpt : MulAction.IsPretransitive (alternatingGroup (Fin 6)) (Fin 6) := by
    refine ⟨fun x y => ?_⟩
    by_cases hxy : x = y
    · exact ⟨1, by simp [hxy]⟩
    · obtain ⟨u, hux, huy⟩ := (by decide : ∀ x y : Fin 6, ∃ u : Fin 6, u ≠ x ∧ u ≠ y) x y
      refine ⟨⟨swap x u * swap x y, ?_⟩, ?_⟩
      · rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hux.symm, Perm.sign_swap hxy]; decide
      · show (swap x u * swap x y) x = y
        rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hxy) huy.symm]
  have h1 := MulAction.index_stabilizer_of_transitive (alternatingGroup (Fin 6)) z
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer (alternatingGroup (Fin 6)) z)
  have hX : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]; simp [Nat.factorial]
  rw [h1, hX, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin] at h2
  omega

theorem mem_zpowers_of_order_five {Q : Type*} [Group Q] [Finite Q] {b : ℕ} (hb : b ≤ 3)
    (hQ : Nat.card Q = 5 * 2 ^ b) {a x : Q} (ha : orderOf a = 5) (hx : orderOf x = 5) :
    x ∈ Subgroup.zpowers a := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hpg : ∀ g : Q, orderOf g = 5 → IsPGroup 5 (Subgroup.zpowers g) := fun g hg =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg]; norm_num)
  obtain ⟨P, hPa⟩ := (hpg a ha).exists_le_sylow
  obtain ⟨P', hPx⟩ := (hpg x hx).exists_le_sylow
  have hPcard : Nat.card (P : Subgroup Q) = 5 := by
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 P.isPGroup'
    have hdvd : Nat.card (P : Subgroup Q) ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card _
    have h5 : 5 ∣ Nat.card (P : Subgroup Q) := by
      have := Subgroup.card_dvd_of_le hPa
      rwa [Nat.card_zpowers, ha] at this
    rw [hj] at hdvd h5 ⊢
    rw [hQ] at hdvd
    rcases Nat.lt_trichotomy j 1 with h | h | h
    · interval_cases j; simp at h5
    · rw [h]; norm_num
    · exfalso
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
      have h25 : 25 ∣ 5 ^ (m + 2) := ⟨5 ^ m, by ring⟩
      have h25' : 25 ∣ 5 * 2 ^ b := h25.trans hdvd
      have : 5 ∣ 2 ^ b := by omega
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five this) (by norm_num)
  have hsub : Subsingleton (Sylow 5 Q) := by
    have hmod := card_sylow_modEq_one 5 Q
    have hdvd := P.card_dvd_index
    have hidx : (P : Subgroup Q).index = 2 ^ b := by
      have := Subgroup.card_mul_index (P : Subgroup Q)
      rw [hPcard, hQ] at this
      omega
    rw [hidx] at hdvd
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hi3 : i ≤ 3 := hi.trans hb
    have hn1 : Nat.card (Sylow 5 Q) = 1 := by
      rw [hi'] at hmod ⊢
      unfold Nat.ModEq at hmod
      interval_cases i <;> simp_all
    exact (Nat.card_eq_one_iff_unique.mp hn1).1
  have hPP : P = P' := Subsingleton.elim P P'
  have hzP : Subgroup.zpowers a = (P : Subgroup Q) := by
    refine Subgroup.eq_of_le_of_card_ge hPa ?_
    rw [Nat.card_zpowers, ha, hPcard]
  rw [hzP]
  exact hPP ▸ hPx (Subgroup.mem_zpowers x)

theorem false_of_a6 {S Y : Subgroup (alternatingGroup (Fin 6))} {a : alternatingGroup (Fin 6)}
    (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (haY : a ∈ Y) (ha5 : orderOf a = 5)
    (hY5 : ∃ b : ℕ, Nat.card Y = 5 * 2 ^ b)
    (hSY : S ≤ Subgroup.normalizer (Y : Set (alternatingGroup (Fin 6)))) : False := by
  have hX : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]; simp [Nat.factorial]
  have hS8 : Nat.card S = 8 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS2
    have h1 := Subgroup.card_mul_index S
    rw [hk, hX] at h1
    have hk3 : k = 3 := by
      rcases Nat.lt_or_ge k 4 with hk4 | hk4
      · interval_cases k <;> first | rfl | (norm_num at h1; omega)
      · exfalso
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
        have : 2 ^ (m + 4) * S.index = 16 * (2 ^ m * S.index) := by ring
        omega
    rw [hk, hk3]; norm_num
  obtain ⟨b, hb⟩ := hY5
  have hb3 : b ≤ 3 := by
    have hdvd : Nat.card Y ∣ 360 := hX ▸ Subgroup.card_subgroup_dvd_card Y
    rw [hb] at hdvd
    by_contra hcon
    obtain ⟨m, rfl⟩ : ∃ m, b = m + 4 := ⟨b - 4, by omega⟩
    have h80 : 5 * 2 ^ (m + 4) = 80 * 2 ^ m := by ring
    rw [h80] at hdvd
    have := (dvd_mul_right 80 (2 ^ m)).trans hdvd
    omega
  set σ : Perm (Fin 6) := (a : Perm (Fin 6)) with hσ
  have hσ5 : orderOf σ = 5 := by rw [hσ, Subgroup.orderOf_coe, ha5]
  obtain ⟨z, hz⟩ := Fintype.card_eq_one_iff.mp (fix_card hσ5)
  have hσz : σ z.1 = z.1 := z.2
  have hsfix : ∀ s ∈ S, (s : Perm (Fin 6)) z.1 = z.1 := by
    intro s hs
    have hsN := hSY hs
    have ha' : s * a * s⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hsN a).mp haY
    have hQ : Nat.card Y = 5 * 2 ^ b := hb
    have hord : orderOf (⟨s * a * s⁻¹, ha'⟩ : Y) = 5 := by
      rw [Subgroup.orderOf_mk]
      have := MulEquiv.orderOf_eq (MulAut.conj s) a
      rw [MulAut.conj_apply] at this
      rw [this, ha5]
    have haY5 : orderOf (⟨a, haY⟩ : Y) = 5 := by rw [Subgroup.orderOf_mk, ha5]
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_order_five hb3 hb haY5 hord)
    have hi' : s * a * s⁻¹ = a ^ i := by
      have := congrArg (fun x : Y => (x : alternatingGroup (Fin 6))) hi
      simpa using this.symm
    set τ : Perm (Fin 6) := (s : Perm (Fin 6)) * σ * (s : Perm (Fin 6))⁻¹ with hτ
    have hτ5 : orderOf τ = 5 := by
      have := MulEquiv.orderOf_eq (MulAut.conj (s : Perm (Fin 6))) σ
      rw [MulAut.conj_apply] at this
      rw [hτ, this, hσ5]
    have hτa : τ = ((a ^ i : alternatingGroup (Fin 6)) : Perm (Fin 6)) := by
      rw [hτ, hσ]
      exact congrArg (fun x : alternatingGroup (Fin 6) => (x : Perm (Fin 6))) hi'
    have hτz : τ z.1 = z.1 := by
      rw [hτa]
      have : ((a ^ i : alternatingGroup (Fin 6)) : Perm (Fin 6)) = σ ^ i := by
        rw [hσ]; simp
      rw [this]
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hσz i
    have hτsz : τ ((s : Perm (Fin 6)) z.1) = (s : Perm (Fin 6)) z.1 := by
      rw [hτ]; simp [Perm.mul_apply, hσz]
    have h1 := fix_card hτ5
    have := Fintype.card_le_one_iff.mp h1.le ⟨_, hτsz⟩ ⟨_, hτz⟩
    exact congrArg Subtype.val this
  have hSst : S ≤ MulAction.stabilizer (alternatingGroup (Fin 6)) z.1 := fun s hs =>
    MulAction.mem_stabilizer_iff.mpr (hsfix s hs)
  have := Subgroup.card_dvd_of_le hSst
  rw [hS8, stab_card] at this
  omega

theorem false_of_a6_equiv {L : Type*} [Group L] (e : L ≃* alternatingGroup (Fin 6)) {S Y : Subgroup L}
    {a : L} (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (haY : a ∈ Y) (ha5 : orderOf a = 5)
    (hY5 : ∃ b : ℕ, Nat.card Y = 5 * 2 ^ b) (hSY : S ≤ Subgroup.normalizer (Y : Set L)) :
    False := by
  refine false_of_a6 (S := S.map (e : L →* alternatingGroup (Fin 6)))
    (Y := Y.map (e : L →* alternatingGroup (Fin 6))) (a := e a)
    (hS2.map _) ?_ (Subgroup.mem_map_of_mem _ haY) (by rw [MulEquiv.orderOf_eq, ha5]) ?_ ?_
  · rw [Subgroup.index_map_equiv]; exact hSi
  · obtain ⟨b, hb⟩ := hY5
    exact ⟨b, by rw [Subgroup.card_map_of_injective e.injective, hb]⟩
  · exact (Subgroup.map_mono hSY).trans (Subgroup.map_equiv_normalizer_eq Y e).le

end A6

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_pCoreOf {G₀ K R V : Subgroup G} (hKG : K ≤ G₀) (hsub : IsSubnormal K G₀)
    (hRG : R ≤ G₀) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (h12 : (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K) {g ℓ : G}
    (hg : g ∈ K) (hgV : g ∈ Subgroup.centralizer (V : Set G)) (hℓ : ℓ ∈ K) :
    g * ℓ * g⁻¹ * ℓ⁻¹ ∈ pCoreOf 2 K := by
  have hY : K ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K :=
    fun x hx => h12 ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
  have h1 := commutator_le_of_le_O2_oTwoZ hKG hsub hRG hRK hY
  have hmem : ⁅g, ℓ⁆ ∈ ⁅K ⊓ Subgroup.centralizer (V : Set G), K⁆ :=
    Subgroup.commutator_mem_commutator ⟨hg, hgV⟩ hℓ
  have h2 : ⁅g, ℓ⁆ ∈ pCoreOf 2 G₀ := h1 hmem
  have hGN : G₀ ≤ Subgroup.normalizer (pCoreOf 2 G₀ : Set G) := le_normalizer_pCoreOf 2 G₀
  have hKN : K ≤ Subgroup.normalizer ((pCoreOf 2 G₀ ⊓ K : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hGN (hKG hx), Subgroup.le_normalizer hx⟩
  have hle : pCoreOf 2 G₀ ⊓ K ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer inf_le_right hKN ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
  have h3 : ⁅g, ℓ⁆ ∈ K := by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hg hℓ) (K.inv_mem hg)) (K.inv_mem hℓ)
  rw [← commutatorElement_def]
  exact hle ⟨h2, h3⟩

omit [Finite G] in
theorem commute_conjAct_iff {V : Subgroup G} {t k : G} (ht : t ∈ Subgroup.normalizer (V : Set G))
    (hk : k ∈ Subgroup.normalizer (V : Set G)) :
    Commute (conjAct V ⟨t, ht⟩) (conjAct V ⟨k, hk⟩) ↔
      t * k * t⁻¹ * k⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have hmem : t * k * t⁻¹ * k⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).mul_mem ht hk) ((Subgroup.normalizer (V : Set G)).inv_mem ht))
      ((Subgroup.normalizer (V : Set G)).inv_mem hk)
  have h1 : conjAct V ⟨t * k * t⁻¹ * k⁻¹, hmem⟩ = 1 ↔
      t * k * t⁻¹ * k⁻¹ ∈ Subgroup.centralizer (V : Set G) := A4.conjAct_eq_one_iff
  have e : (⟨t * k * t⁻¹ * k⁻¹, hmem⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      ⟨t, ht⟩ * ⟨k, hk⟩ * ⟨t, ht⟩⁻¹ * ⟨k, hk⟩⁻¹ := Subtype.ext rfl
  rw [← h1, e]
  simp only [map_mul, map_inv]
  rw [commute_iff_eq, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

theorem alt_kernel_facts {G₀ K R V : Subgroup G} (hKG : K ≤ G₀) (hsub : IsSubnormal K G₀)
    (hRG : R ≤ G₀) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (h11 : pCoreOf 2 (K ⊔ R) ≤ (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G))
    (h12 : (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K)
    {n : ℕ} (hn : 5 ≤ n) {α : ↥K →* alternatingGroup (Fin n)} (hα : IsAltBlockTypeWith K n α) :
    (∀ x : ↥K, α x = 1 ↔ (x : G) ∈ pCoreOf 2 K) ∧
      pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) ∧
      ∀ x : ↥K, (x : G) ∈ Subgroup.centralizer (V : Set G) → α x = 1 := by
  classical
  have hOC : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) := by
    have hle : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) :=
      le_pCoreOf_of_le_normalizer ((pCoreOf_le 2 K).trans le_sup_left)
        (sup_le (le_normalizer_pCoreOf 2 K) (hRK.trans (normalizer_le_normalizer_pCoreOf 2 K)))
        (pCoreOf_isPGroup 2 K)
    exact fun x hx => (h11 (hle hx)).2
  have hker : ∀ x : ↥K, α x = 1 ↔ (x : G) ∈ pCoreOf 2 K := by
    intro x
    have : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
    rw [← mk_eq_one_iff_mem_pCoreOf' x, QuotientGroup.eq_one_iff, ← hα.2.1, MonoidHom.mem_ker]
  have hn4 : 4 ≤ Nat.card (Fin n) := by simp; omega
  have hcenter : Subgroup.center ↥(alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot hn4
  have hα1 : ∀ x : ↥K, (x : G) ∈ Subgroup.centralizer (V : Set G) → α x = 1 := by
    intro x hx
    have hz : α x ∈ Subgroup.center ↥(alternatingGroup (Fin n)) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨ℓ, rfl⟩ := hα.1 s
      have h1 : (x : G) * ℓ * (x : G)⁻¹ * (ℓ : G)⁻¹ ∈ pCoreOf 2 K :=
        commutator_mem_pCoreOf hKG hsub hRG hRK h12 x.2 hx ℓ.2
      have h2 : α (x * ℓ * x⁻¹ * ℓ⁻¹) = 1 := (hker _).mpr h1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    rw [hcenter] at hz
    exact hz
  exact ⟨hker, hOC, hα1⟩

theorem false_of_altBlock {G₀ K R M₁ Y V : Subgroup G} (hKG : K ≤ G₀) (hsub : IsSubnormal K G₀)
    (hRG : R ≤ G₀) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hVN : K ⊔ R ≤ Subgroup.normalizer (V : Set G))
    (h11 : pCoreOf 2 (K ⊔ R) ≤ (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G))
    (h12 : (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K)
    (hYK : Y ≤ M₁ ⊓ K) (hYM : ∀ m ∈ M₁, ∀ y ∈ Y, m * y * m⁻¹ ∈ Y)
    (hYcard : ∃ e : ℕ, Nat.card Y = 5 * 2 ^ e) {y : G} (hyY : y ∈ Y)
    (hyN : y ∈ Subgroup.normalizer (V : Set G)) (hy5 : orderOf (conjAct V ⟨y, hyN⟩) = 5)
    {n : ℕ} (hn : 5 ≤ n) {α : ↥K →* alternatingGroup (Fin n)} (hα : IsAltBlockTypeWith K n α)
    {t : G} (htR : t ∈ R) (htV : t ∈ Subgroup.normalizer (V : Set G))
    (hRt : autOn R V = Subgroup.zpowers (conjAct V ⟨t, htV⟩)) {σ : Equiv.Perm (Fin n)}
    (hσ : σ.IsSwap)
    (hconj : ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹)
    (hMK : autOn (M₁ ⊓ K) V = autOn K V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V))) :
    False := by
  classical
  have hKN : ∀ k ∈ K, k ∈ Subgroup.normalizer (V : Set G) := fun k hk =>
    hVN (Subgroup.mem_sup_left hk)
  have htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp (hRK htR) k).mp hk
  obtain ⟨hker, hOC, hα1⟩ := alt_kernel_facts hKG hsub hRG hRK h11 h12 hn hα
  have hkey : ∀ x : ↥K, t * (x : G) * t⁻¹ * (x : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) ↔
      σ * ((α x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * σ⁻¹ =
        ((α x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
    intro x
    set x' : ↥K := ⟨t * x * t⁻¹, htK x x.2⟩ with hx'
    have hc : t * (x : G) * t⁻¹ * (x : G)⁻¹ = ((x' * x⁻¹ : ↥K) : G) := rfl
    have hconj' : ((α x' : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * ((α x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * σ⁻¹ := by
      have := hconj x x.2 (htK x x.2)
      rwa [Subtype.coe_eta] at this
    rw [hc]
    constructor
    · intro hV
      have h1 : α (x' * x⁻¹) = 1 := hα1 _ hV
      rw [map_mul, map_inv, mul_inv_eq_one] at h1
      rw [← hconj', h1]
    · intro h
      have h1 : α (x' * x⁻¹) = 1 := by
        rw [map_mul, map_inv, mul_inv_eq_one]
        exact Subtype.ext (by rw [hconj', h])
      exact hOC ((hker _).mp h1)
  have hyK : y ∈ K := (hYK hyY).2
  have hyM : y ∈ M₁ := (hYK hyY).1
  set yK : ↥K := ⟨y, hyK⟩ with hyK'
  have hcomm_y : Commute (conjAct V ⟨t, htV⟩) (conjAct V ⟨y, hyN⟩) := by
    have hmem : conjAct V ⟨y, hyN⟩ ∈ autOn (M₁ ⊓ K) V :=
      mem_autOn_iff_exists.mpr ⟨y, hyN, ⟨hyM, hyK⟩, rfl⟩
    rw [hMK] at hmem
    have htmem : conjAct V ⟨t, htV⟩ ∈ autOn R V :=
      mem_autOn_iff_exists.mpr ⟨t, htV, htR, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hmem.2 _ htmem
  have hσy : σ * ((α yK : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * σ⁻¹ =
      ((α yK : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) :=
    (hkey yK).mp ((commute_conjAct_iff htV hyN).mp hcomm_y)
  set a : Equiv.Perm (Fin n) := ((α yK : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) with ha
  have hy5C : y ^ 5 ∈ Subgroup.centralizer (V : Set G) := by
    have h1 : conjAct V ⟨y, hyN⟩ ^ 5 = 1 := hy5 ▸ pow_orderOf_eq_one _
    rw [← map_pow] at h1
    exact A4.conjAct_eq_one_iff.mp h1
  have ha5 : a ^ 5 = 1 := by
    have h1 : α (yK ^ 5) = 1 := hα1 _ hy5C
    rw [map_pow] at h1
    have := congrArg Subtype.val h1
    simpa [ha] using this
  have hane : a ≠ 1 := by
    intro h1
    have h2 : α yK = 1 := Subtype.ext h1
    have h3 : y ∈ Subgroup.centralizer (V : Set G) := hOC ((hker yK).mp h2)
    have h4 : conjAct V ⟨y, hyN⟩ = 1 := A4.conjAct_eq_one_iff.mpr h3
    rw [h4, orderOf_one] at hy5
    omega
  have ha5' : orderOf a = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one ha5) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hane
    · exact h
  have hlift : ∀ s : alternatingGroup (Fin n),
      σ * (s : Equiv.Perm (Fin n)) * σ⁻¹ = (s : Equiv.Perm (Fin n)) →
      ∃ m : G, m ∈ M₁ ∧ ∃ hm : m ∈ K, α ⟨m, hm⟩ = s := by
    intro s hs
    obtain ⟨k, rfl⟩ := hα.1 s
    have hk1 : t * (k : G) * t⁻¹ * (k : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
      (hkey k).mpr hs
    have hcomm : Commute (conjAct V ⟨t, htV⟩) (conjAct V ⟨(k : G), hKN k k.2⟩) :=
      (commute_conjAct_iff htV (hKN k k.2)).mpr hk1
    have hmem1 : conjAct V ⟨(k : G), hKN k k.2⟩ ∈ autOn K V :=
      mem_autOn_iff_exists.mpr ⟨k, hKN k k.2, k.2, rfl⟩
    have hmem2 : conjAct V ⟨(k : G), hKN k k.2⟩ ∈
        Subgroup.centralizer (autOn R V : Set (MulAut ↥V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [hRt] at hh
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (hcomm.zpow_left j)
    have hmem3 : conjAct V ⟨(k : G), hKN k k.2⟩ ∈ autOn (M₁ ⊓ K) V := by
      rw [hMK]; exact ⟨hmem1, hmem2⟩
    obtain ⟨m, hmN, ⟨hmM, hmK⟩, hmeq⟩ := mem_autOn_iff_exists.mp hmem3
    refine ⟨m, hmM, hmK, ?_⟩
    have hkm : (k : G)⁻¹ * m ∈ Subgroup.centralizer (V : Set G) := by
      have hmem : (k : G)⁻¹ * m ∈ Subgroup.normalizer (V : Set G) :=
        (Subgroup.normalizer (V : Set G)).mul_mem
          ((Subgroup.normalizer (V : Set G)).inv_mem (hKN k k.2)) hmN
      have e : (⟨(k : G)⁻¹ * m, hmem⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨(k : G), hKN k k.2⟩⁻¹ * ⟨m, hmN⟩ := Subtype.ext rfl
      have h1 : conjAct V ⟨(k : G)⁻¹ * m, hmem⟩ = 1 := by
        rw [e, map_mul, map_inv, hmeq, inv_mul_cancel]
      exact A4.conjAct_eq_one_iff.mp h1
    have h2 : α ((k⁻¹ : ↥K) * ⟨m, hmK⟩) = 1 := hα1 _ hkm
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2.symm
  let ψ : ↥K →* Equiv.Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp α
  let Yp : Subgroup (Equiv.Perm (Fin n)) := (Y.subgroupOf K).map ψ
  have hYp : ∀ g, g ∈ Yp ↔ ∃ z : ↥K, (z : G) ∈ Y ∧ ψ z = g := by
    intro g
    simp only [Yp, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  have haYp : a ∈ Yp := (hYp a).mpr ⟨yK, hyY, rfl⟩
  have hN : ∀ τ : Equiv.Perm (Fin n), τ.IsThreeCycle → σ * τ = τ * σ →
      ∀ y₀ ∈ Yp, τ * y₀ * τ⁻¹ ∈ Yp := by
    intro τ hτ hστ y₀ hy₀
    obtain ⟨z, hzY, rfl⟩ := (hYp y₀).mp hy₀
    have hs : σ * (((⟨τ, hτ.mem_alternatingGroup⟩ : alternatingGroup (Fin n))) :
        Equiv.Perm (Fin n)) * σ⁻¹ = τ := by
      show σ * τ * σ⁻¹ = τ
      rw [hστ]; group
    obtain ⟨m, hmM, hmK, hmα⟩ := hlift ⟨τ, hτ.mem_alternatingGroup⟩ hs
    refine (hYp _).mpr ⟨(⟨m, hmK⟩ : ↥K) * z * (⟨m, hmK⟩ : ↥K)⁻¹, hYM m hmM z hzY, ?_⟩
    have hψm : ψ ⟨m, hmK⟩ = τ := congrArg Subtype.val hmα
    simp only [map_mul, map_inv, hψm]
  have h3 : ∀ g ∈ Yp, ¬ 3 ∣ orderOf g := by
    intro g hg h3g
    obtain ⟨z, hzY, rfl⟩ := (hYp g).mp hg
    have h1 : orderOf (ψ z) ∣ orderOf z := orderOf_map_dvd ψ z
    have h2 : orderOf z ∣ Nat.card Y := by
      rw [← Subgroup.orderOf_coe]
      exact Subgroup.orderOf_dvd_natCard Y hzY
    obtain ⟨e, he⟩ := hYcard
    have h4 : 3 ∣ 5 * 2 ^ e := he ▸ h3g.trans (h1.trans h2)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h4 with h5 | h5
    · omega
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h5
      omega
  obtain ⟨p, q, hpq, hσpq⟩ := hσ
  obtain ⟨g, hg, hg3⟩ := exists_three_dvd_orderOf (Y := Yp) hpq hσpq ha5' haYp
    (mul_inv_eq_iff_eq_mul.mp hσy) hN
  exact h3 g hg hg3

omit [Finite G] in
theorem exists_autOn_equiv {K V : Subgroup G} (hKN : K ≤ Subgroup.normalizer (V : Set G)) {n : ℕ}
    {α : ↥K →* alternatingGroup (Fin n)} (hαs : Function.Surjective α)
    (hα1 : ∀ x : ↥K, α x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G)) :
    ∃ (ρ : ↥K →* ↥(autOn K V)) (_ : ↥(autOn K V) ≃* alternatingGroup (Fin n)),
      ∀ k : ↥K, ((ρ k : ↥(autOn K V)) : MulAut ↥V) = conjAct V ⟨(k : G), hKN k.2⟩ := by
  let ρ : ↥K →* ↥(autOn K V) :=
    ((conjAct V).comp (Subgroup.inclusion hKN)).codRestrict (autOn K V)
      (fun k => mem_autOn_iff_exists.mpr ⟨k, hKN k.2, k.2, rfl⟩)
  have hρs : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hxN, hxK, rfl⟩ := mem_autOn_iff_exists.mp hy
    exact ⟨⟨x, hxK⟩, rfl⟩
  have hker : ρ.ker = α.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hα1]
    constructor
    · intro h
      exact A4.conjAct_eq_one_iff.mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext (A4.conjAct_eq_one_iff.mpr h)
  exact ⟨ρ, (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)), fun k => rfl⟩

theorem false_of_a6Block {G₀ K R M₁ Y V : Subgroup G} (hKG : K ≤ G₀) (hsub : IsSubnormal K G₀)
    (hRG : R ≤ G₀) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hVN : K ⊔ R ≤ Subgroup.normalizer (V : Set G))
    (h11 : pCoreOf 2 (K ⊔ R) ≤ (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G))
    (h12 : (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K)
    (hYK : Y ≤ M₁ ⊓ K) (hYM : ∀ m ∈ M₁, ∀ y ∈ Y, m * y * m⁻¹ ∈ Y)
    (hYcard : ∃ e : ℕ, Nat.card Y = 5 * 2 ^ e) {y : G} (hyY : y ∈ Y)
    (hyN : y ∈ Subgroup.normalizer (V : Set G)) (hy5 : orderOf (conjAct V ⟨y, hyN⟩) = 5)
    {α : ↥K →* alternatingGroup (Fin 6)} (hα : IsAltBlockTypeWith K 6 α)
    (hpar : IsParabolic2 (autOn K V) (autOn (M₁ ⊓ K) V)) : False := by
  classical
  obtain ⟨hker, hOC, hα1⟩ := alt_kernel_facts hKG hsub hRG hRK h11 h12 (by norm_num) hα
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := fun k hk => hVN (Subgroup.mem_sup_left hk)
  obtain ⟨ρ, θ, hρ⟩ := exists_autOn_equiv hKN hα.1
    (fun x => ⟨fun h => hOC ((hker x).mp h), hα1 x⟩)
  obtain ⟨-, S, hsyl, hSN⟩ := hpar
  have hSP : S ≤ autOn (M₁ ⊓ K) V := fun s hs => hSN ⟨hsyl.1 hs, Subgroup.le_normalizer hs⟩
  have hyK : y ∈ K := (hYK hyY).2
  set yK : ↥K := ⟨y, hyK⟩ with hyK'
  let Y₁ : Subgroup ↥(autOn K V) := (Y.subgroupOf K).map ρ
  let S₁ : Subgroup ↥(autOn K V) := S.subgroupOf (autOn K V)
  have hmemY₁ : ∀ x, x ∈ Y₁ ↔ ∃ z : ↥K, (z : G) ∈ Y ∧ ρ z = x := by
    intro x
    simp only [Y₁, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  have hconjY : ∀ s ∈ S₁, ∀ h ∈ Y₁, s * h * s⁻¹ ∈ Y₁ := by
    intro s hs h hh
    obtain ⟨z, hzY, rfl⟩ := (hmemY₁ h).mp hh
    have hsS : (s : MulAut ↥V) ∈ S := hs
    obtain ⟨m, hmN, ⟨hmM, hmK⟩, hmeq⟩ := mem_autOn_iff_exists.mp (hSP hsS)
    have hsρ : s = ρ ⟨m, hmK⟩ := Subtype.ext (by rw [hρ]; exact hmeq.symm)
    refine (hmemY₁ _).mpr ⟨⟨m, hmK⟩ * z * ⟨m, hmK⟩⁻¹, hYM m hmM z hzY, ?_⟩
    rw [hsρ]
    simp only [map_mul, map_inv]
  have hnormS : S₁ ≤ Subgroup.normalizer (Y₁ : Set ↥(autOn K V)) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconjY s hs h hh, fun hh => ?_⟩
    have := hconjY s⁻¹ (S₁.inv_mem hs) _ hh
    have e : s⁻¹ * (s * h * s⁻¹) * s⁻¹⁻¹ = h := by group
    rwa [e] at this
  have haY₁ : ρ yK ∈ Y₁ := (hmemY₁ _).mpr ⟨yK, hyY, rfl⟩
  have ha5 : orderOf (ρ yK) = 5 := by
    rw [← Subgroup.orderOf_coe, hρ]
    exact hy5
  have hY₁card : ∃ b : ℕ, Nat.card Y₁ = 5 * 2 ^ b := by
    obtain ⟨e, he⟩ := hYcard
    have hdvd : Nat.card Y₁ ∣ 5 * 2 ^ e := by
      have h1 : Nat.card Y₁ ∣ Nat.card (Y.subgroupOf K) := Subgroup.card_map_dvd (Y.subgroupOf K) ρ
      have h2 : Nat.card (Y.subgroupOf K) = Nat.card Y :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun x hx => (hYK hx).2)).toEquiv
      rw [h2, he] at h1
      exact h1
    have h5 : 5 ∣ Nat.card Y₁ := by
      have := orderOf_dvd_natCard (⟨ρ yK, haY₁⟩ : ↥Y₁)
      rwa [Subgroup.orderOf_mk, ha5] at this
    obtain ⟨d, hd⟩ := h5
    have hdd : d ∣ 2 ^ e := by
      rw [hd] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdd
    exact ⟨b, by rw [hd, hb]⟩
  exact false_of_a6_equiv θ (S := S₁) (Y := Y₁) (a := ρ yK)
    (hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm) hsyl.2.2 haY₁ ha5 hY₁card
    hnormS

omit [Finite G] in
theorem false_of_g2 {K R V : Subgroup G} {y : G} (hyK : y ∈ K)
    (hyN : y ∈ Subgroup.normalizer (V : Set G)) (hy5 : orderOf (conjAct V ⟨y, hyN⟩) = 5)
    (hg2 : IsG2Two ↥(autOn (K ⊔ R) V)) : False := by
  have hmem : conjAct V ⟨y, hyN⟩ ∈ autOn (K ⊔ R) V :=
    mem_autOn_iff_exists.mpr ⟨y, hyN, Subgroup.mem_sup_left hyK, rfl⟩
  have h1 : orderOf (⟨conjAct V ⟨y, hyN⟩, hmem⟩ : ↥(autOn (K ⊔ R) V)) = 5 := by
    rw [Subgroup.orderOf_mk, hy5]
  have h2 := orderOf_dvd_natCard (⟨conjAct V ⟨y, hyN⟩, hmem⟩ : ↥(autOn (K ⊔ R) V))
  rw [h1, hg2.1] at h2
  omega

theorem card_Y {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π) :
    ∃ e : ℕ, Nat.card (yOf152 T Mc M) = 5 * 2 ^ e := by
  have hmul := Subgroup.relIndex_mul_card (H := pCoreOf 2 (yOf152 T Mc M)) (K := yOf152 T Mc M)
  rw [c.y.relIndex_five, inf_eq_left.mpr (pCoreOf_le 2 _)] at hmul
  obtain ⟨e, he⟩ := (IsPGroup.iff_card).1 (pCoreOf_isPGroup 2 (yOf152 T Mc M))
  exact ⟨e, by rw [← hmul, he]⟩

@[expose] def C27Rest3 (R M K V : Subgroup G) : Prop :=
  (IsSp4Block K ∧ IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V)) ∨
  ((∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 ≤ n ∧ Fintype.card F = 2 ^ n ∧
      Nonempty (↥(autOn K V) ≃* ↥(StatedSL 3 F))) ∧
    IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V) ∧ IsMSPair (K ⊔ R) R) ∨
  ((Nonempty (↥(autOn K V) ≃* ↥(StatedSL 4 (ZMod 2))) ∨
      Nonempty (↥(autOn K V) ≃* ↥(StatedSL 5 (ZMod 2)))) ∧
    IsParabolic2 (autOn K V) (autOn (M ⊓ K) V) ∧ ¬ IsBorelIn (autOn K V) (autOn (M ⊓ K) V))

@[expose] def Input15204QuasiRest3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M H K₁ K₂ : Subgroup G) (π : ↥H →* W5)
    (c : Ctx15204 T Mc M H K₁ K₂ π) (Lc : Subgroup G), Tail15204 c Lc →
    yOf152 T Mc M ≤ Lc → ¬ IsSylowTwoOf (rOf T Mc M K₁) (rOf T Mc M K₁ ⊔ Lc) →
    CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc) →
    C27Rest3 (rOf T Mc M K₁) (M ⊓ g0Of T Mc M K₁) Lc
      (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁))) → False

theorem input15204QuasiRest2_of_rest3
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) (h : Input15204QuasiRest3) :
    Input15204QuasiRest2 := by
  intro G _ _ T Mc M H K₁ K₂ π c Lc tail hYL hnot hq hrest
  obtain ⟨y, hyY, hyN, hy5⟩ := exists_five_element (hC27 G) c tail hYL hq
  set R := rOf T Mc M K₁ with hR
  set V := omegaOneCenterOf (pCoreOf 2 (Lc ⊔ R)) with hV
  have hLG : Lc ≤ g0Of T Mc M K₁ := le_of_mem_cComp tail.comp
  have hNG : g0Of T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).1 tail.normal
  have hRG : R ≤ g0Of T Mc M K₁ := tail.hyp.radical.1
  have hRN : R ≤ Subgroup.normalizer (Lc : Set G) := hRG.trans hNG
  obtain ⟨⟨h11, h12, -⟩, -, -⟩ := hC27 G (g0Of T Mc M K₁) R (M ⊓ g0Of T Mc M K₁) Lc V tail.hyp
    tail.comp (isQuasisimple_quot tail.comp hq)
    (CFSG.Quasithin.CT.CharTwo.of_normal tail.charTwo hLG tail.normal) tail.not_le hRN rfl
  have hVN : Lc ⊔ R ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
    A4.normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 (Lc ⊔ R))
      (le_normalizer_pCoreOf 2 (Lc ⊔ R) hg)
  have hYM : ∀ m ∈ M ⊓ g0Of T Mc M K₁, ∀ z ∈ yOf152 T Mc M, m * z * m⁻¹ ∈ yOf152 T Mc M :=
    fun m hm z hz => (Subgroup.mem_normalizer_iff.mp (c.y.normal hm.1) z).mp hz
  have hrest' := h G T Mc M H K₁ K₂ π c Lc tail hYL hnot hq
  rcases hrest with ⟨⟨n, α, hn5, -, -, hα, t, htR, htV, hRt, -, σ, hσ, hconj⟩, hMK⟩ | he | hf | hg | hh
  · exact false_of_altBlock hLG (subnormal_of_mem_cComp tail.comp) hRG hRN hVN h11 h12
      (Y_le_inf c hYL) hYM (card_Y c) hyY hyN hy5 hn5 hα htR htV hRt hσ hconj hMK
  · rcases he with ⟨⟨-, α, hα⟩ | hsp, hmax⟩
    · exact false_of_a6Block hLG (subnormal_of_mem_cComp tail.comp) hRG hRN hVN h11 h12
        (Y_le_inf c hYL) hYM (card_Y c) hyY hyN hy5 hα hmax.1
    · exact hrest' (Or.inl ⟨hsp, hmax⟩)
  · exact false_of_g2 (hYL hyY) hyN hy5 hf.2.1
  · exact hrest' (Or.inr (Or.inl hg))
  · exact hrest' (Or.inr (Or.inr hh))

theorem input15204BranchBQuasi_of_rest3
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) (h : Input15204QuasiRest3) :
    Input15204BranchBQuasi :=
  input15204BranchBQuasi_of_rest2 hC27 (input15204QuasiRest2_of_rest3 hC27 h)

end CFSG.Quasithin.He17
