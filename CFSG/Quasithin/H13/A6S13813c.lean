module

public import CFSG.Quasithin.Background.C2Six
public import CFSG.Quasithin.Background.B1Transvection
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace A6P

section Fit

variable {G : Type} [Group G] [Finite G] {H : Subgroup G}

theorem mem_oTwoFIn_of_mem_pCoreOf {M : Type*} [Group M] [Finite M] (φ : ↥H →* M)
    (hker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) {p : ℕ} [hp : Fact p.Prime] {x : ↥H}
    (hx : φ x ∈ pCoreOf p φ.range) : (x : G) ∈ oTwoFIn H := by
  rw [C2Six.mem_oTwoFIn_iff]
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hkerπ : ∀ y : ↥H, π y = 1 ↔ φ y = 1 := by
    intro y
    rw [hker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have : z = y := Subtype.ext hzy
      exact this ▸ hz
  set N : Subgroup ↥H := (pCoreOf p φ.range).comap φ with hN
  have hNrange : ∀ y : ↥H, φ y ∈ φ.range := fun y => ⟨y, rfl⟩
  have hNnorm : (N.map π).Normal := by
    refine Subgroup.Normal.map ⟨fun n hn g => ?_⟩ π (QuotientGroup.mk'_surjective _)
    rw [hN, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have hgN : φ g ∈ Subgroup.normalizer (pCoreOf p φ.range : Set M) :=
      le_normalizer_pCoreOf p φ.range (hNrange g)
    exact (Subgroup.mem_normalizer_iff.mp hgN _).mp hn
  have hNp : IsPGroup p ↥(N.map π) := by
    rintro ⟨z, n, hn, rfl⟩
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup p φ.range) ⟨φ n, hn⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : φ (n ^ p ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    show π n ^ p ^ k = 1
    rw [← map_pow]
    exact (hkerπ _).2 h1
  have hle : N.map π ≤ CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
    le_sSup ⟨hNnorm, hNp.isNilpotent⟩
  exact hle ⟨x, hx, rfl⟩

theorem exists_odd_lift {M : Type*} [Group M] (φ : ↥H →* M) {K : Subgroup G} {x : ↥H}
    (hxK : (x : G) ∈ K) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    (hxn : φ x ^ p ^ n = 1) : ∃ x' : ↥H, (x' : G) ∈ oTwoRes K ∧ φ x' = φ x := by
  obtain ⟨a, m, hm, hmo⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, Subgroup.subset_closure ⟨K.one_mem, 1, odd_one, by simp⟩, ?_⟩
    rw [pow_zero, pow_one] at hxn
    rw [map_one, hxn]
  have hcop : Nat.Coprime (2 ^ a) (p ^ n) := Nat.Coprime.pow a n
    ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2))
  have hpn : 1 < p ^ n := Nat.one_lt_pow hn.ne' hp.out.one_lt
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hpn
  refine ⟨x ^ (2 ^ a * k), Subgroup.subset_closure ⟨?_, m, hm, ?_⟩, ?_⟩
  · simpa using K.pow_mem hxK _
  · have h1 : (x ^ (2 ^ a * k)) ^ m = (x ^ (2 ^ a * m)) ^ k := by
      rw [← pow_mul, ← pow_mul]
      ring_nf
    have h2 : x ^ (2 ^ a * m) = 1 := by rw [← hmo, pow_orderOf_eq_one]
    have h3 := congrArg Subtype.val (h1.trans (by rw [h2, one_pow]))
    simpa using h3
  · rw [map_pow, ← Nat.div_add_mod (2 ^ a * k) (p ^ n), hk, pow_add, pow_mul, hxn, one_pow,
      one_mul, pow_one]

end Fit

section Klein

variable {V : Type*} [CommGroup V] [Finite V]

theorem eq_bot_of_normal_two (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V} (hcard : Nat.card W = 4)
    {R : Subgroup (MulAut ↥W)} (hR2 : IsPGroup 2 R) {c : MulAut ↥W}
    (hcR : ∀ r ∈ R, c * r * c⁻¹ ∈ R) (hfix : ∀ w, c w = w → w = 1) : R = ⊥ := by
  classical
  by_contra hne
  have hW : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  have h6 : Nat.card (MulAut ↥W) = 6 := B1.card_mulAut_of_card_four hV hcard
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hdvd : Nat.card R ∣ 6 := h6 ▸ Subgroup.card_subgroup_dvd_card R
  have hk1 : k = 1 := by
    rcases k with _ | _ | k
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hk)) hne
    · rfl
    · rw [hk] at hdvd
      have h4 : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 (by omega : 2 ≤ k + 2)).trans hdvd
      norm_num at h4
  rw [hk1, pow_one] at hk
  obtain ⟨⟨r, hrR⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hcr : c * r * c⁻¹ = r := by
    have hmem := hcR r hrR
    by_contra hneq
    have h3 : ({1, r, c * r * c⁻¹} : Finset (MulAut ↥W)).card ≤ Nat.card R := by
      have : Fintype R := Fintype.ofFinite R
      rw [Nat.card_eq_fintype_card]
      have hsub : ({1, r, c * r * c⁻¹} : Finset (MulAut ↥W)) ⊆ (R : Set (MulAut ↥W)).toFinset := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rw [Set.mem_toFinset]
        rcases hy with rfl | rfl | rfl
        · exact R.one_mem
        · exact hrR
        · exact hmem
      calc ({1, r, c * r * c⁻¹} : Finset (MulAut ↥W)).card ≤ (R : Set (MulAut ↥W)).toFinset.card :=
            Finset.card_le_card hsub
        _ = Fintype.card R := by simp
    have hc1 : c * r * c⁻¹ ≠ 1 := fun h => hr1' (by
      calc r = c⁻¹ * (c * r * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group)
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hr1'.symm, hc1.symm⟩), Finset.card_pair (Ne.symm hneq), hk] at h3
    omega
  obtain ⟨w, hw⟩ : ∃ w : ↥W, r w ≠ w := by
    by_contra hall
    push Not at hall
    exact hr1' (MulEquiv.ext hall)
  have hr2 : r * r = 1 := by
    have h1 : orderOf (⟨r, hrR⟩ : R) ∣ 2 := hk ▸ orderOf_dvd_natCard _
    have h2 : (⟨r, hrR⟩ : R) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
    have := congrArg Subtype.val h2
    simpa [sq] using this
  set w₀ := r w * w⁻¹ with hw₀
  have hw₀1 : w₀ ≠ 1 := fun h => hw (mul_inv_eq_one.1 h)
  have hrw₀ : r w₀ = w₀ := by
    have e1 : r (r w) = w := by
      rw [← MulAut.mul_apply, hr2, MulAut.one_apply]
    rw [hw₀, map_mul, map_inv, e1]
    have : (r w)⁻¹ = r w := by
      rw [inv_eq_iff_mul_eq_one, ← sq, hW]
    rw [this, mul_comm]
    have : w = w⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← sq, hW]
    rw [← this]
  have hfixr : ∀ v, r v = v → v = 1 ∨ v = w₀ := by
    intro v hv
    by_contra hcon
    push Not at hcon
    obtain ⟨hv1, hvw⟩ := hcon
    apply hr1'
    have : Fintype ↥W := Fintype.ofFinite ↥W
    have hcardW : (Finset.univ : Finset ↥W).card = 4 := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
    have hvw' : v * w₀ ≠ 1 := fun h => hvw (by
      have : v = w₀⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this, inv_eq_iff_mul_eq_one, ← sq, hW])
    have hvw1 : v * w₀ ≠ v := fun h => hw₀1 (mul_eq_left.1 h)
    have hvw2 : v * w₀ ≠ w₀ := fun h => hv1 (mul_eq_right.1 h)
    have huniv : (Finset.univ : Finset ↥W) = {1, w₀, v, v * w₀} := by
      apply (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) _).symm
      rw [hcardW, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair hvw1.symm]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hvw.symm, hvw2.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hw₀1.symm, hv1.symm, hvw'.symm⟩
    refine MulEquiv.ext fun u => ?_
    have hu : u ∈ ({1, w₀, v, v * w₀} : Finset W) := huniv ▸ Finset.mem_univ u
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · simp
    · exact hrw₀
    · exact hv
    · rw [map_mul, hv, hrw₀]; rfl
  have hcw₀ : r (c w₀) = c w₀ := by
    have : r = c * r * c⁻¹ := hcr.symm
    calc r (c w₀) = (c * r * c⁻¹) (c w₀) := by rw [← this]
      _ = c (r w₀) := by simp [MulAut.mul_apply]
      _ = c w₀ := by rw [hrw₀]
  rcases hfixr _ hcw₀ with h | h
  · exact hw₀1 (c.injective (by rw [h, map_one]))
  · exact hw₀1 (hfix w₀ h)

end Klein

end A6P

end CFSG.Quasithin.H13.A6

