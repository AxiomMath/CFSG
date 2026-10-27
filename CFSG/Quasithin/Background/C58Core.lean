module

public import CFSG.Quasithin.Background.C58Pairs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Commutation
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Natural

public section

namespace CFSG.Quasithin.C58

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.DoubleA3 Subgroup

variable {G : Type} [Group G]

theorem exists_fixed_of_sq_eq_one {U : Subgroup G} (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hUab : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {a : G} (ha2 : a ^ 2 = 1)
    (haU : a ∈ normalizer (U : Set G)) (hna : a ∉ centralizer (U : Set G)) :
    ∃ w ∈ U, w ≠ 1 ∧ a * w * a⁻¹ = w := by
  rw [mem_centralizer_iff] at hna
  push Not at hna
  obtain ⟨v, hv, hva⟩ := hna
  have hav : a * v * a⁻¹ ∈ U := (mem_normalizer_iff.mp haU v).mp hv
  have hainv : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ha2]
  refine ⟨v * (a * v * a⁻¹), mul_mem hv hav, ?_, ?_⟩
  · intro h1
    apply hva
    have h2 : a * v * a⁻¹ = v⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hv2 : v⁻¹ = v := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hU2 v hv]
    rw [hv2] at h2
    calc v * a = a * v * a⁻¹ * a := by rw [h2]
      _ = a * v := by group
  · have e : a * (v * (a * v * a⁻¹)) * a⁻¹ = (a * v * a⁻¹) * (a * a * v * a⁻¹ * a⁻¹) := by group
    rw [e]
    have : a * a * v * a⁻¹ * a⁻¹ = v := by
      rw [hainv]
      have h3 : a * a = 1 := by rw [← pow_two, ha2]
      calc a * a * v * a * a = (a * a) * v * (a * a) := by group
        _ = v := by rw [h3]; group
    rw [this]
    exact hUab _ hav _ hv

theorem IsA4Block.mul_conj_mem [Finite G] {L U : Subgroup G} (h : IsA4Block L U) {a : G}
    (ha2 : a ^ 2 = 1) (haL : a ∈ normalizer (L : Set G)) (haU : a ∈ normalizer (U : Set G))
    (hna : a ∉ centralizer (U : Set G)) {k : G} (hk : k ∈ L) : a * k * a⁻¹ * k ∈ U := by
  obtain ⟨c, hcL, hc3, hcN, hcfp, hLc⟩ := h.exists_c
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hUL : U ≤ L := h.le
  have hUn : U ≤ normalizer (U : Set G) := Subgroup.le_normalizer
  have hcU : zpowers c ≤ normalizer (U : Set G) := zpowers_le.mpr hcN
  have hform : ∀ l ∈ L, ∃ j : ℤ, ∃ u ∈ U, l = c ^ j * u := by
    intro l hl
    have hl' : l ∈ ((zpowers c ⊔ U : Subgroup G) : Set G) := by
      rw [sup_comm, ← hLc]; exact hl
    rw [coe_mul_of_left_le_normalizer_right (zpowers c) U hcU] at hl'
    obtain ⟨p, hp, u, hu, rfl⟩ := hl'
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hp
    exact ⟨j, u, hu, rfl⟩
  have hmod : ∀ j : ℤ, c ^ j = c ^ (j % 3) := fun j => by
    have := zpow_mod_orderOf c j
    rw [hc3] at this
    simpa using this.symm
  have hac : a * c * a⁻¹ ∈ L := (mem_normalizer_iff.mp haL c).mp hcL
  obtain ⟨j, u, hu, hj⟩ := hform _ hac
  have hc_notU : c ∉ U := by
    intro hcu
    have := h.sq_U c hcu
    have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one this
    rw [hc3] at h2
    norm_num at h2
  have key : a * c * a⁻¹ * c ∈ U := by
    rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h0 | h0 | h0
    · exfalso
      rw [hmod, h0, zpow_zero, one_mul] at hj
      apply hc_notU
      have : c = a⁻¹ * u * a := by rw [← hj]; group
      rw [this]
      have := (mem_normalizer_iff.mp (inv_mem haU) u).mp hu
      simpa using this
    · exfalso
      rw [hmod, h0, zpow_one] at hj
      have hj' : a * c⁻¹ * a⁻¹ = u⁻¹ * c⁻¹ := by
        have : a * c⁻¹ * a⁻¹ = (a * c * a⁻¹)⁻¹ := by group
        rw [this, hj]; group
      have hcomm : ∀ v ∈ U, a * (c⁻¹ * v * c) * a⁻¹ = c⁻¹ * (a * v * a⁻¹) * c := by
        intro v hv
        have hav : a * v * a⁻¹ ∈ U := (mem_normalizer_iff.mp haU v).mp hv
        have hcv : c⁻¹ * (a * v * a⁻¹) * c ∈ U := by
          have := (mem_normalizer_iff.mp (inv_mem hcN) (a * v * a⁻¹)).mp hav
          simpa using this
        have hcu := h.comm_U u hu _ hcv
        calc a * (c⁻¹ * v * c) * a⁻¹ = (a * c⁻¹ * a⁻¹) * (a * v * a⁻¹) * (a * c * a⁻¹) := by
              group
          _ = u⁻¹ * (c⁻¹ * (a * v * a⁻¹) * c) * u := by rw [hj', hj]; group
          _ = u⁻¹ * (u * (c⁻¹ * (a * v * a⁻¹) * c)) := by rw [hcu]; group
          _ = c⁻¹ * (a * v * a⁻¹) * c := by group
      obtain ⟨w, hw, hw1, haw⟩ := exists_fixed_of_sq_eq_one h.sq_U h.comm_U ha2 haU hna
      have hpowfix : ∀ n : ℕ, (c ^ n)⁻¹ * w * c ^ n ∈ U ∧
          a * ((c ^ n)⁻¹ * w * c ^ n) * a⁻¹ = (c ^ n)⁻¹ * w * c ^ n := by
        intro n
        induction n with
        | zero => simpa using ⟨hw, haw⟩
        | succ n ih =>
          obtain ⟨ihU, ihfix⟩ := ih
          have e : (c ^ (n + 1))⁻¹ * w * c ^ (n + 1) = c⁻¹ * ((c ^ n)⁻¹ * w * c ^ n) * c := by
            rw [pow_succ]; group
          rw [e]
          refine ⟨?_, ?_⟩
          · have := (mem_normalizer_iff.mp (inv_mem hcN) _).mp ihU
            simpa using this
          · rw [hcomm _ ihU, ihfix]
      apply hna
      rw [mem_centralizer_iff]
      intro v hv
      by_cases hv1 : v = 1
      · rw [hv1]; group
      obtain ⟨n, rfl⟩ := klein_conj_transitive h.card_U hc3' hcN hcfp hw hv hw1 hv1
      have := (hpowfix n).2
      calc (c ^ n)⁻¹ * w * c ^ n * a = a * ((c ^ n)⁻¹ * w * c ^ n) * a⁻¹ * a := by rw [this]
        _ = a * ((c ^ n)⁻¹ * w * c ^ n) := by group
    · rw [hmod, h0] at hj
      have : a * c * a⁻¹ * c = c ^ (2 : ℤ) * u * c := by rw [hj]
      rw [this]
      have e : c ^ (2 : ℤ) * u * c = c ^ (2 : ℤ) * u * (c ^ (2 : ℤ))⁻¹ * c ^ (3 : ℤ) := by group
      rw [e]
      have h3 : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc3'
      rw [h3, mul_one]
      have := (mem_normalizer_iff.mp (zpow_mem hcN 2) u).mp hu
      exact this
  obtain ⟨i, v, hv, rfl⟩ := hform k hk
  have hav : a * v * a⁻¹ ∈ U := (mem_normalizer_iff.mp haU v).mp hv
  have hpow : ∀ n : ℕ, a * c ^ n * a⁻¹ * c ^ n ∈ U := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hw := key
      set w := a * c * a⁻¹ * c with hw'
      set w' := a * c ^ n * a⁻¹ * c ^ n with hw''
      have e : a * c ^ (n + 1) * a⁻¹ * c ^ (n + 1) =
          (a * c ^ n * a⁻¹) * w * (a * c ^ n * a⁻¹)⁻¹ * w' := by
        rw [hw', hw'']; group
      rw [e]
      have hmemL : a * c ^ n * a⁻¹ ∈ L := (mem_normalizer_iff.mp haL _).mp (pow_mem hcL n)
      have hN : a * c ^ n * a⁻¹ ∈ normalizer (U : Set G) := by
        have h1 : L ≤ normalizer (U : Set G) := by
          rw [hLc]; exact sup_le hUn hcU
        exact h1 hmemL
      exact mul_mem ((mem_normalizer_iff.mp hN w).mp hw) ih
  have hzpow : ∀ z : ℤ, a * c ^ z * a⁻¹ * c ^ z ∈ U := by
    intro z
    obtain ⟨n, hn⟩ : ∃ n : ℕ, z % 3 = n :=
      ⟨(z % 3).toNat, (Int.toNat_of_nonneg (Int.emod_nonneg z (by norm_num))).symm⟩
    have hz : c ^ z = c ^ n := by rw [hmod z, hn, zpow_natCast]
    rw [hz]; exact hpow _
  have e : a * (c ^ i * v) * a⁻¹ * (c ^ i * v) =
      (a * c ^ i * a⁻¹ * c ^ i) * (c ^ i)⁻¹ * (a * v * a⁻¹) * (c ^ i) * v := by group
  rw [e]
  have hcvi : (c ^ i)⁻¹ * (a * v * a⁻¹) * (c ^ i) ∈ U := by
    have := (mem_normalizer_iff.mp (zpow_mem hcN (-i)) (a * v * a⁻¹)).mp hav
    simpa [zpow_neg, mul_assoc] using this
  have := mul_mem (mul_mem (hzpow i) hcvi) hv
  simpa [mul_assoc] using this

theorem IsA4Block.le_normalizer_U {L U : Subgroup G} (h : IsA4Block L U) :
    L ≤ normalizer (U : Set G) := by
  obtain ⟨c, -, -, hcN, -, hLc⟩ := h.exists_c
  rw [hLc]
  exact sup_le Subgroup.le_normalizer (zpowers_le.mpr hcN)

theorem IsA4Block.isPGroup_U [Finite G] {L U : Subgroup G} (h : IsA4Block L U) :
    IsPGroup 2 U := by
  refine IsPGroup.of_card (n := 2) ?_
  rw [h.card_U]; norm_num

theorem IsA4Block.le_U_of_isPGroup [Finite G] {L U X : Subgroup G} (h : IsA4Block L U)
    (hXL : X ≤ L) (hX2 : IsPGroup 2 X) : X ≤ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXN : X ≤ normalizer (U : Set G) := hXL.trans (IsA4Block.le_normalizer_U h)
  have hXU2 : IsPGroup 2 ↥(X ⊔ U) := hX2.to_sup_of_normal_right' (IsA4Block.isPGroup_U h) hXN
  have hle : X ⊔ U ≤ L := sup_le hXL h.le
  obtain ⟨n, hn⟩ := hXU2.exists_card_eq
  have hdvd : Nat.card ↥(X ⊔ U) ∣ 12 := by
    rw [← h.card_L]; exact Subgroup.card_dvd_of_le hle
  have hU4 : 4 ∣ Nat.card ↥(X ⊔ U) := by
    rw [← h.card_U]; exact Subgroup.card_dvd_of_le le_sup_right
  rw [hn] at hdvd hU4
  have hn2 : n ≤ 2 := by
    by_contra hcon
    have h8 : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := h8.trans hdvd
    norm_num at this
  have hcard : Nat.card ↥(X ⊔ U) ≤ Nat.card U := by
    rw [hn, h.card_U]
    calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
      _ = 4 := by norm_num
  have heq : U = X ⊔ U := Subgroup.eq_of_le_of_card_ge le_sup_right hcard
  rw [heq]; exact le_sup_left

theorem IsA4Block.normalizer_le [Finite G] {L U : Subgroup G} (h : IsA4Block L U) :
    normalizer (L : Set G) ≤ normalizer (U : Set G) := by
  intro g hg
  have hle : conjSubgroup U g ≤ L := by
    have := conjSubgroup_mono h.le g
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hg] at this
  have h2 : IsPGroup 2 ↥(conjSubgroup U g) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [card_conjSubgroup, h.card_U]; norm_num
  have hle' := IsA4Block.le_U_of_isPGroup h hle h2
  have heq : conjSubgroup U g = U :=
    Subgroup.eq_of_le_of_card_ge hle' (by rw [card_conjSubgroup])
  exact conjSubgroup_eq_iff_mem_normalizer.mp heq

theorem IsA4Block.inf_centralizer_eq_bot {L U : Subgroup G} (h : IsA4Block L U) :
    U ⊓ centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨huU, huC⟩
  rw [mem_bot]
  refine h.center_L u (h.le huU) fun l hl => ?_
  exact ((mem_centralizer_iff.mp huC) l hl).symm

theorem IsA4Block.le_normalizer_inf [Finite G] {L U B : Subgroup G} (h : IsA4Block L U)
    (hUB : U ≤ B) (hBL : B ≤ normalizer (L : Set G)) :
    L ≤ normalizer ((B ⊓ centralizer (U : Set G) : Subgroup G) : Set G) := by
  have hLU := IsA4Block.le_normalizer_U h
  have key : ∀ k ∈ L, ∀ q ∈ B ⊓ centralizer (U : Set G),
      k * q * k⁻¹ ∈ B ⊓ centralizer (U : Set G) := by
    intro k hk q hq
    obtain ⟨hqB, hqC⟩ := Subgroup.mem_inf.mp hq
    obtain ⟨u, hu, hinner⟩ := h.exists_inner (hBL hqB) (fun v hv =>
      ((mem_centralizer_iff.mp hqC) v hv).symm)
    have h1 : q * k⁻¹ * q⁻¹ = u * k⁻¹ * u⁻¹ := hinner _ (inv_mem hk)
    have hkuk : k * u * k⁻¹ ∈ U := (mem_normalizer_iff.mp (hLU hk) u).mp hu
    have e : k * q * k⁻¹ = (k * u * k⁻¹) * u⁻¹ * q := by
      calc k * q * k⁻¹ = k * (q * k⁻¹ * q⁻¹) * q := by group
        _ = k * (u * k⁻¹ * u⁻¹) * q := by rw [h1]
        _ = (k * u * k⁻¹) * u⁻¹ * q := by group
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [e]; exact mul_mem (mul_mem (hUB hkuk) (inv_mem (hUB hu))) hqB
    · rw [mem_centralizer_iff]
      intro v hv
      have hv' : k⁻¹ * v * k ∈ U := by
        have := (mem_normalizer_iff.mp (hLU (inv_mem hk)) v).mp hv
        simpa using this
      have hc := (mem_centralizer_iff.mp hqC) _ hv'
      calc v * (k * q * k⁻¹) = k * ((k⁻¹ * v * k) * q) * k⁻¹ := by group
        _ = k * (q * (k⁻¹ * v * k)) * k⁻¹ := by rw [hc]
        _ = k * q * k⁻¹ * v := by group
  intro k hk
  rw [mem_normalizer_iff]
  intro q
  constructor
  · exact key k hk q
  · intro hq
    have := key k⁻¹ (inv_mem hk) _ hq
    simpa [mul_assoc] using this

theorem IsA4Block.le_sup_conj [Finite G] {L U B : Subgroup G} (h : IsA4Block L U)
    (hs : IsShort2 L) (hB2 : IsPGroup 2 B) (hUB : U ≤ B) (hBL : B ≤ normalizer (L : Set G))
    {y : G} (hy : y ∈ normalizer (B : Set G))
    (hyU : ¬ conjSubgroup U y ≤ centralizer (U : Set G)) :
    ∃ c ∈ L, L ≤ conjSubgroup U y ⊔ conjSubgroup (conjSubgroup U y) c := by
  obtain ⟨c, hcL, hc3o, hcN, -, hLc⟩ := h.exists_c
  have hc3 : c ^ 3 = 1 := by rw [← hc3o]; exact pow_orderOf_eq_one c
  refine ⟨c, hcL, ?_⟩
  have hBU : B ≤ normalizer (U : Set G) := hBL.trans (IsA4Block.normalizer_le h)
  set Q := B ⊓ centralizer (U : Set G) with hQ
  set Λ := conjSubgroup U y ⊔ conjSubgroup (conjSubgroup U y) c with hΛ
  have hUyB : conjSubgroup U y ≤ B := by
    have := conjSubgroup_mono hUB y
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hy] at this
  have hBUy : B ≤ normalizer ((conjSubgroup U y : Subgroup G) : Set G) := by
    have := conjSubgroup_mono hBU y
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hy, C5.conjSubgroup_normalizer] at this
  have hLQ := IsA4Block.le_normalizer_inf h hUB hBL
  have hQc : conjSubgroup Q c = Q := conjSubgroup_eq_iff_mem_normalizer.mpr (hLQ hcL)
  have hQΛ : Q ≤ normalizer (Λ : Set G) := by
    intro q hq
    refine C1.mem_normalizer_sup ?_ ?_
    · exact hBUy hq.1
    · have h1 : Q ≤ normalizer ((conjSubgroup U y : Subgroup G) : Set G) :=
        inf_le_left.trans hBUy
      have h2 := conjSubgroup_mono h1 c
      rw [hQc, C5.conjSubgroup_normalizer] at h2
      exact h2 hq
  have hUQ : U ≤ Q := le_inf hUB (fun u hu => mem_centralizer_iff.mpr fun v hv =>
    (h.comm_U u hu v hv).symm)
  obtain ⟨a, haUy, hna⟩ := IsConcreteLE.not_le_iff_exists.mp hyU
  have haB : a ∈ B := hUyB haUy
  have ha2 : a ^ 2 = 1 := by
    rw [mem_conjSubgroup_iff] at haUy
    have h1 := h.sq_U _ haUy
    have h2 : y * a ^ 2 * y⁻¹ = (y * a * y⁻¹) ^ 2 := by simp [pow_two, mul_assoc]
    have h3 : y * a ^ 2 * y⁻¹ = 1 := by rw [h2, h1]
    calc a ^ 2 = y⁻¹ * (y * a ^ 2 * y⁻¹) * y := by group
      _ = 1 := by rw [h3]; group
  have hw := IsA4Block.mul_conj_mem h ha2 (hBL haB) (hBU haB) hna hcL
  set w := a * c * a⁻¹ * c with hwdef
  have hainv : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ha2]
  have hp : a * (c⁻¹ * a * c) ∈ Λ := by
    refine mul_mem (mem_sup_left haUy) (mem_sup_right ?_)
    rw [mem_conjSubgroup_iff]
    simpa [mul_assoc] using haUy
  have ep : a * (c⁻¹ * a * c) = c * w⁻¹ * c := by
    rw [hwdef]
    calc a * (c⁻¹ * a * c) = a * c⁻¹ * a⁻¹ * c := by rw [hainv]; group
      _ = c * (a * c * a⁻¹ * c)⁻¹ * c := by group
  have hc2 : c ^ 2 ∈ Λ ⊔ Q := by
    have e : c ^ 2 = (c * w⁻¹ * c) * (c⁻¹ * w * c) := by simp [pow_two]; group
    rw [e]
    refine mul_mem (mem_sup_left (ep ▸ hp)) (mem_sup_right (hUQ ?_))
    have := (mem_normalizer_iff.mp (inv_mem (IsA4Block.le_normalizer_U h hcL)) w).mp hw
    simpa using this
  have hc : c ∈ Λ ⊔ Q := by
    have e : c = (c ^ 2) * (c ^ 2) := by
      calc c = c * c ^ 3 := by rw [hc3, mul_one]
        _ = c ^ 2 * c ^ 2 := by group
    rw [e]; exact mul_mem hc2 hc2
  have hLΛQ : L ≤ Λ ⊔ Q := by
    rw [hLc]
    exact sup_le (hUQ.trans le_sup_right) (zpowers_le.mpr hc)
  exact C56.le_of_le_sup_isPGroup hs (hB2.to_le inf_le_left) hQΛ hLΛQ

theorem pairData_of_block [Finite G] {L U B : Subgroup G} (h : IsA4Block L U) (hs : IsShort2 L)
    (hB2 : IsPGroup 2 B) (hUB : U ≤ B) (hBL : B ≤ normalizer (L : Set G))
    (hnt : ¬ B ≤ centralizer (U : Set G)) {y : G} (hy : y ∈ normalizer (B : Set G))
    (hyU : ¬ conjSubgroup U y ≤ centralizer (U : Set G)) :
    ∃ W : Subgroup G, PairData B (B ⊓ centralizer (U : Set G)) U W
      ((B ⊓ centralizer (U : Set G)) ⊓ centralizer (L : Set G)) y := by
  have hBU : B ≤ normalizer (U : Set G) := hBL.trans (IsA4Block.normalizer_le h)
  obtain ⟨z, -, -, -, hR⟩ := rank1_of_klein h.card_U h.sq_U h.comm_U hUB hBU hB2 hnt
  have hx1 : ¬ conjSubgroup U y ≤ B ⊓ centralizer (U : Set G) := fun hle =>
    hyU (hle.trans inf_le_right)
  have hx2 : ¬ conjSubgroup U y⁻¹ ≤ B ⊓ centralizer (U : Set G) := fun hle =>
    not_conj_inv_le_centralizer hyU (hle.trans inf_le_right)
  have hZ : (U ⊓ centralizer (L : Set G)).relIndex U = 2 ^ 2 := by
    rw [IsA4Block.inf_centralizer_eq_bot h, Subgroup.relIndex_bot_left, h.card_U]; norm_num
  obtain ⟨hQ, hDx⟩ := hR.Q_eq_sup_centralizer hy hx1 h.le (IsA4Block.le_normalizer_inf h hUB hBL)
    hZ (IsA4Block.le_sup_conj h hs hB2 hUB hBL hy hyU)
  refine ⟨zpowers z, ⟨hR, h.sq_U, hy, hx1, hx2, hQ, ?_, ?_, ?_⟩⟩
  · intro u hu d hd
    exact (mem_centralizer_iff.mp hd.1.2) u hu
  · intro u hu d hd
    have hd' := hDx hd
    rw [conjSubgroup_inf, conjSubgroup_eq_iff_mem_normalizer.mpr hy,
      C5.conjSubgroup_centralizer] at hd'
    exact (mem_centralizer_iff.mp hd'.2) u hu
  · rw [eq_bot_iff, ← IsA4Block.inf_centralizer_eq_bot h]
    exact inf_le_inf_left _ inf_le_right

end CFSG.Quasithin.C58
