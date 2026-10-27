module

public import CFSG.RankThree.PartTwo.Sec17.Item174StarU3Even

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof174Host.U3

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Matrix

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

@[expose] abbrev suMat (g : hypSU h 1 1) : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K)

theorem exists_eq_tau (n : hypSU h 1 1) (hoff : ∀ i j, i ≠ j → suMat n i j = 0) :
    ∃ x : Kˣ, n = tau h x := by
  set M := ((n : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) with hM
  replace hoff : ∀ i j, i ≠ j → M i j = 0 := hoff
  have hiso := hypForm_smul_smul h n (Pi.single ie (1 : K)) (Pi.single jf 1)
  rw [hypForm_eq, hypForm_eq, smul_single_apply, smul_single_apply, smul_single_apply,
    smul_single_apply, smul_single_apply, smul_single_apply, ← hM] at hiso
  rw [hoff iw ie (by simp), hoff jf ie (by simp), hoff ie jf (by simp)] at hiso
  simp only [map_zero, zero_mul, add_zero, Pi.single_eq_same, ne_eq, reduceCtorEq,
    not_false_eq_true, Pi.single_eq_of_ne, mul_zero, map_one, one_mul] at hiso
  have hdet : M.det = 1 := n.2.2
  rw [det_hyp3, hoff ie iw (by simp), hoff ie jf (by simp), hoff iw ie (by simp),
    hoff iw jf (by simp), hoff jf ie (by simp), hoff jf iw (by simp)] at hdet
  simp only [mul_zero, zero_mul, sub_zero, add_zero] at hdet
  have ha : M ie ie ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hiso
    exact zero_ne_one hiso
  refine ⟨Units.mk0 _ ha, Subtype.ext (Units.ext ?_)⟩
  change M = tauMat h (Units.mk0 _ ha)
  have hb0 : h.bar (M ie ie) ≠ 0 := (map_ne_zero h.bar).mpr ha
  have hd : M jf jf = (h.bar (M ie ie))⁻¹ := eq_inv_of_mul_eq_one_right hiso
  have hb : M iw iw = h.bar (M ie ie) * (M ie ie)⁻¹ := by
    rw [hd] at hdet
    have e2 : M ie ie * M iw iw = h.bar (M ie ie) := by
      have := congrArg (· * h.bar (M ie ie)) hdet
      simpa [mul_assoc, inv_mul_cancel₀ hb0] using this
    rw [eq_mul_inv_iff_mul_eq₀ ha, mul_comm]
    exact e2
  refine mat_ext fun i j hi hj => ?_
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    simp [tauMat, hoff, hb, hd]

theorem offdiag_eq_zero_of_comm {n g : hypSU h 1 1} {a b d : K} (hg : suMat g = dg a b d)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (hc : n * g = g * n) :
    ∀ i j, i ≠ j → suMat n i j = 0 := by
  have hm : suMat n * dg a b d = dg a b d * suMat n := by
    rw [← hg]
    exact congrArg (fun k : hypSU h 1 1 => suMat k) hc
  have key : ∀ i j, suMat n i j * Sum.elim (fun _ => a) (Sum.elim (fun _ => b) (fun _ => d)) j =
      Sum.elim (fun _ => a) (Sum.elim (fun _ => b) (fun _ => d)) i * suMat n i j := by
    intro i j
    have := congrFun (congrFun hm i) j
    rwa [dg, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  intro i j hij
  have hk := key i j
  have hne : Sum.elim (fun _ => a) (Sum.elim (fun _ => b) (fun _ => d)) j ≠
      Sum.elim (fun _ => a) (Sum.elim (fun _ => b) (fun _ => d)) i := by
    rcases idx_cases i with rfl | rfl | rfl <;> rcases idx_cases j with rfl | rfl | rfl <;>
      simp_all [eq_comm]
  have : (Sum.elim (fun _ => a) (Sum.elim (fun _ => b) (fun _ => d)) j -
      Sum.elim (fun _ => a) (Sum.elim (fun _ => b) (fun _ => d)) i) * suMat n i j = 0 := by
    linear_combination hk
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

theorem eq_omega_or_sq {ω : Kˣ} (hω : orderOf ω = 3) {x : K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    x = ω ∨ x = (ω : K) ^ 2 := by
  have hs := omega_sq_add (K := K) hω
  have h3 : (ω : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, omega_pow_three hω, Units.val_one]
  have hxs : x ^ 2 + x + 1 = 0 := by
    have : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination hx3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hx1)
  have : (x - ω) * (x - (ω : K) ^ 2) = 0 := by
    linear_combination hxs - x * hs + h3
  rcases mul_eq_zero.mp this with h0 | h0
  · exact Or.inl (sub_eq_zero.mp h0)
  · exact Or.inr (sub_eq_zero.mp h0)

theorem mem_normalizer_sup {G : Type} [Group G] {H L : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hL : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hL ⊢
  rw [Subgroup.map_sup, hH, hL]

theorem comm_of_odd (h : UnitaryFieldData p f K) (hp : p ≠ 2) {ω : Kˣ} (hω : orderOf ω = 3)
    (hωb : h.bar (ω : K) = ω) {D : Subgroup (hypSU h 1 1)} (hD : IsPGroup 2 D)
    (hT : ∀ x : Kˣ, tau h x ∈ Subgroup.normalizer (D : Set (hypSU h 1 1))) :
    ∀ d ∈ D, d * tau h ω = tau h ω * d := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpp := h.prime
  set Q := p ^ f with hQ
  have hQodd : Odd Q := (hpp.odd_of_ne_two hp).pow
  have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hQodd.pos)
  have hcard : Nat.card Kˣ = (Q - 1) * (Q + 1) := by
    rw [Nat.card_units, h.card, pow_mul', ← hQ]
    obtain ⟨Q', hQ'⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
    rw [hQ']
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have hcard0 : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
  obtain ⟨v, m, hm, hvm⟩ := Nat.exists_eq_two_pow_mul_odd hcard0
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hog : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  set η := g ^ m with hη
  have hη2 : η ^ 2 ^ v = 1 := by
    rw [hη, ← pow_mul, mul_comm, ← hvm, ← hog, pow_orderOf_eq_one]
  have hηq : η ^ (Q + 1) ≠ 1 := by
    intro h1
    rw [hη, ← pow_mul] at h1
    have hd := orderOf_dvd_of_pow_eq_one h1
    rw [hog, hcard] at hd
    have hd' : Q - 1 ∣ m := Nat.dvd_of_mul_dvd_mul_right (by omega) hd
    have h2 : 2 ∣ Q - 1 := by
      obtain ⟨k, hk⟩ := hQodd
      exact ⟨k, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr (h2.trans hd'))
  have h2η : 2 ∣ orderOf η := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hη2)
    rcases j with _ | j
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hηq (by rw [hj, one_pow])
    · rw [hj]
      exact dvd_pow_self 2 (Nat.succ_ne_zero j)
  have hbar : ∀ x : Kˣ, h.bar (x : K) = ((x ^ Q : Kˣ) : K) := fun x => by
    rw [h.bar_apply, Units.val_pow_eq_pow_val]
  have hmodQ : ∀ {a b : ℕ}, η ^ a = η ^ b → a % 2 = b % 2 := by
    intro a b hab
    exact Nat.ModEq.of_dvd h2η (pow_eq_pow_iff_modEq.mp hab)
  have hη0 : (η : K) ≠ 0 := η.ne_zero
  have hy1 : (η : K) ≠ h.bar η * (η : K)⁻¹ := by
    intro he
    have : η ^ 2 = η ^ Q := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ← hbar, pow_two]
      field_simp at he
      linear_combination he
    have := hmodQ this
    rw [Nat.odd_iff.mp hQodd] at this
    simp at this
  have hy2 : (η : K) ≠ (h.bar η)⁻¹ := by
    intro he
    apply hηq
    apply Units.ext
    rw [pow_succ, Units.val_mul, ← hbar, Units.val_one]
    calc h.bar (η : K) * η = h.bar (η : K) * (h.bar (η : K))⁻¹ := congrArg (h.bar (η : K) * ·) he
      _ = 1 := mul_inv_cancel₀ ((map_ne_zero h.bar).mpr hη0)
  have hy3 : h.bar η * (η : K)⁻¹ ≠ (h.bar η)⁻¹ := by
    intro he
    have : η ^ (2 * Q) = η ^ 1 := by
      apply Units.ext
      rw [pow_mul', Units.val_pow_eq_pow_val, ← hbar, pow_one]
      have hb0 := (map_ne_zero h.bar).mpr hη0
      field_simp at he
      linear_combination he
    have := hmodQ this
    simp [Nat.mul_mod_right] at this
  have hω1 : (ω : K) ≠ 1 := by
    intro h1
    have : ω = 1 := Units.ext h1
    rw [this, orderOf_one] at hω
    exact absurd hω (by norm_num)
  have hω2 : (1 : K) ≠ (ω : K) ^ 2 := by
    intro h1
    have h3 : (ω : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, omega_pow_three hω, Units.val_one]
    apply hω1
    calc (ω : K) = (ω : K) ^ 3 * ((ω : K) ^ 2)⁻¹ := by
          rw [pow_succ', mul_inv_cancel_right₀ (pow_ne_zero 2 ω.ne_zero)]
      _ = 1 := by rw [h3, ← h1, inv_one, one_mul]
  have hω3 : (ω : K) ≠ (ω : K) ^ 2 := by
    intro h1
    apply hω1
    have : (ω : K) * (ω : K) = (ω : K) * 1 := by rw [mul_one, ← pow_two, ← h1]
    exact mul_left_cancel₀ ω.ne_zero this
  set c := tau h ω with hc
  have hCc : ∀ n : hypSU h 1 1, n * c = c * n → ∃ x, n = tau h x := fun n hn =>
    exists_eq_tau n (offdiag_eq_zero_of_comm (coe_tau_omega h hω hωb) hω1 hω3 hω2 hn)
  have hCy : ∀ n : hypSU h 1 1, n * tau h η = tau h η * n → ∃ x, n = tau h x := fun n hn =>
    exists_eq_tau n (offdiag_eq_zero_of_comm (coe_tau h η) hy1 hy2 hy3 hn)
  set Y : Subgroup (hypSU h 1 1) := (powMonoidHom (2 ^ v) : Kˣ →* Kˣ).ker.map (tau h) with hY
  have hYp : IsPGroup 2 Y := by
    rintro ⟨_, x, hx, rfl⟩
    refine ⟨v, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, ← map_pow, OneMemClass.coe_one]
    rw [show x ^ 2 ^ v = 1 from hx, map_one]
  have hyY : tau h η ∈ Y := ⟨η, hη2, rfl⟩
  have hYT : ∀ z ∈ Y, ∃ x, z = tau h x := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hYD : Y ≤ Subgroup.normalizer (D : Set (hypSU h 1 1)) := by
    rintro _ ⟨x, -, rfl⟩
    exact hT x
  set P := Y ⊔ D with hP
  have hPp : IsPGroup 2 P := hYp.to_sup_of_normal_right' hD hYD
  have hcY : c ∈ Subgroup.normalizer (Y : Set (hypSU h 1 1)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hc, tau_comm, mul_inv_cancel_right]
      exact ⟨x, hx, rfl⟩
    · intro hz
      obtain ⟨x, hx, hxz⟩ := hz
      have : z = tau h x := by
        calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
          _ = tau h x := by
            rw [← hxz, hc, mul_assoc, tau_comm h x ω, inv_mul_cancel_left]
      rw [this]
      exact ⟨x, hx, rfl⟩
  have hcP : c ∈ Subgroup.normalizer (P : Set (hypSU h 1 1)) := mem_normalizer_sup hcY (hT ω)
  have hTY : ∀ x : Kˣ, tau h x ∈ P → tau h x ∈ Y := by
    intro x hx
    obtain ⟨k, hk⟩ := hPp ⟨_, hx⟩
    have hk' : x ^ 2 ^ k = 1 := tau_injective h (by
      have := congrArg Subtype.val hk
      simpa [← map_pow] using this)
    have hd1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hd2 : orderOf x ∣ 2 ^ v * m := hvm ▸ orderOf_dvd_natCard x
    have hcop : Nat.Coprime (orderOf x) m :=
      Nat.Coprime.coprime_dvd_left hd1 (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm))
    have hd3 : orderOf x ∣ 2 ^ v := hcop.dvd_of_dvd_mul_right hd2
    exact ⟨x, by
      change x ^ 2 ^ v = 1
      exact orderOf_dvd_iff_pow_eq_one.mp hd3, rfl⟩
  have hPY : P ≤ Y := by
    by_contra hne
    have hlt : Y.subgroupOf P < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hne ?_
      intro z hz
      have : (⟨z, hz⟩ : P) ∈ Y.subgroupOf P := htop ▸ Subgroup.mem_top _
      exact this
    have : Group.IsNilpotent P := hPp.isNilpotent
    obtain ⟨n', hn'N, hn'Y⟩ := SetLike.exists_of_lt
      (normalizerCondition_of_isNilpotent (G := P) _ hlt)
    set n : hypSU h 1 1 := n'.1 with hn
    have hnP : n ∈ P := n'.2
    have hnY : n ∉ Y := hn'Y
    have hnN : ∀ z ∈ Y, n⁻¹ * z * n ∈ Y := by
      intro z hz
      have hzP : z ∈ P := le_sup_left (a := Y) hz
      have hiff := (Subgroup.mem_normalizer_iff.mp hn'N) (n'⁻¹ * ⟨z, hzP⟩ * n')
      have : (n'⁻¹ * ⟨z, hzP⟩ * n' : P) ∈ Y.subgroupOf P := by
        refine hiff.mpr ?_
        rw [show n' * (n'⁻¹ * ⟨z, hzP⟩ * n') * n'⁻¹ = ⟨z, hzP⟩ by group]
        exact hz
      exact this
    obtain ⟨x₁, hx₁⟩ : ∃ x₁, n * c * n⁻¹ = tau h x₁ := by
      apply hCy
      obtain ⟨x', hx'⟩ := hYT _ (hnN _ hyY)
      have hy : tau h η = n * tau h x' * n⁻¹ := by
        rw [← hx']
        group
      rw [hy, hc]
      calc n * tau h ω * n⁻¹ * (n * tau h x' * n⁻¹) = n * (tau h ω * tau h x') * n⁻¹ := by group
        _ = n * (tau h x' * tau h ω) * n⁻¹ := by rw [tau_comm]
        _ = n * tau h x' * n⁻¹ * (n * tau h ω * n⁻¹) := by group
    have hox : orderOf x₁ = 3 := by
      rw [← orderOf_injective (tau h) (tau_injective h), ← hx₁, ← MulAut.conj_apply,
        MulEquiv.orderOf_eq, hc,
        orderOf_tau_omega h hω hωb]
    have hx3 : (x₁ : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hox, pow_orderOf_eq_one, Units.val_one]
    have hx1 : (x₁ : K) ≠ 1 := by
      intro h1
      have : x₁ = 1 := Units.ext h1
      rw [this, orderOf_one] at hox
      exact absurd hox (by norm_num)
    rcases eq_omega_or_sq hω hx3 hx1 with he | he
    ·
      have hx : x₁ = ω := Units.ext he
      have hnc : n * c = c * n := by
        have : n * c * n⁻¹ = c := by rw [hx₁, hx]
        calc n * c = n * c * n⁻¹ * n := by group
          _ = c * n := by rw [this]
      obtain ⟨x, hx⟩ := hCc n hnc
      rw [hx] at hnP hnY
      exact hnY (hTY x hnP)
    ·
      have hx : x₁ = ω ^ 2 := Units.ext (by rw [he, Units.val_pow_eq_pow_val])
      have hcm : n * c * n⁻¹ * c⁻¹ = c := by
        rw [hx₁, hx, map_pow, hc]
        group
      have hmem : n * c * n⁻¹ * c⁻¹ ∈ P := by
        have h1 : c * n⁻¹ * c⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hcP _).mp (inv_mem hnP)
        have := mul_mem hnP h1
        rwa [show n * (c * n⁻¹ * c⁻¹) = n * c * n⁻¹ * c⁻¹ by group] at this
      rw [hcm] at hmem
      obtain ⟨k, hk⟩ := hPp ⟨c, hmem⟩
      have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h3 : 3 ∣ 2 ^ k := by
        rw [← orderOf_tau_omega h hω hωb]
        exact orderOf_dvd_of_pow_eq_one hk'
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  intro d hd
  obtain ⟨x, rfl⟩ := hYT d (hPY (le_sup_right (a := Y) hd))
  exact tau_comm h x ω

end CFSG.RankThree.PartTwo.Sec17.Proof174Host.U3
