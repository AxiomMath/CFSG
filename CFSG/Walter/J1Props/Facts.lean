module

public import CFSG.Walter.J1Props.Hyp
public import CFSG.Walter.J1Props.NormQuot
public import CFSG.Walter.J1.Local

public section

namespace CFSG.Walter.J1Props

open CFSG.Walter.J1Recog CFSG.Open Word
open scoped Pointwise

theorem prime_dvd_card {p : ℕ} (hp : p.Prime) (hd : p ∣ 175560) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 := by
  have h : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq h =>
    (Nat.prime_dvd_prime_iff_eq hp hq).mp h
  rw [show (175560 : ℕ) = 2 ^ 3 * (3 * (5 * (7 * (11 * 19)))) by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hp).mp hd with h2 | hd
  · exact Or.inl (h 2 Nat.prime_two (hp.dvd_of_dvd_pow h2))
  rcases (Nat.Prime.dvd_mul hp).mp hd with h3 | hd
  · exact Or.inr (Or.inl (h 3 (by norm_num) h3))
  rcases (Nat.Prime.dvd_mul hp).mp hd with h5 | hd
  · exact Or.inr (Or.inr (Or.inl (h 5 (by norm_num) h5)))
  rcases (Nat.Prime.dvd_mul hp).mp hd with h7 | hd
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h 7 (by norm_num) h7))))
  rcases (Nat.Prime.dvd_mul hp).mp hd with h11 | h19
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h 11 (by norm_num) h11)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h 19 (by norm_num) h19)))))

theorem sylow_eq_bot_of_not_dvd {p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ 175560)
    (P : Sylow p walterJ1) : (P : Subgroup walterJ1) = ⊥ := by
  rw [← Subgroup.card_eq_one, Sylow.card_eq_multiplicity, card_walterJ1,
    Nat.factorization_eq_zero_of_not_dvd hp, pow_zero]

theorem not_dvd_index_of_card {p : ℕ} (hp : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19)
    {P : Subgroup walterJ1} (hP : Nat.card P = p) : ¬ p ∣ P.index := by
  have h := P.card_mul_index
  rw [hP, card_walterJ1] at h
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> omega

@[expose] def wy11 : Word 5 := wn ++ Word.pow (wt ++ ws) 2

@[expose] def wy19 : Word 5 := Word.pow wn 3 ++ wt ++ ws

@[expose] def wi11 : Word 5 := wn ++ ws

@[expose] def wi19 : Word 5 := ws ++ wt ++ ws

@[expose] def wr7 : Word 5 := ws ++ wm

@[expose] def wr11 : Word 5 := wn ++ wt ++ wu ++ Word.inv wn ++ Word.inv wm

@[expose] def wr19 : Word 5 := wt ++ Word.inv wn ++ ws ++ wt ++ wn ++ Word.inv wm ++ wu

@[expose] noncomputable def yJ : ℕ → walterJ1
  | 3 => mJ
  | 5 => uJ * xJ
  | 7 => nJ
  | 11 => elt wy11
  | _ => elt wy19

@[expose] noncomputable def iJ : ℕ → walterJ1
  | 3 => uJ
  | 5 => xJ
  | 7 => sJ
  | 11 => elt wi11
  | _ => elt wi19

theorem orders_yJ : mJ ^ 3 = 1 ∧ mJ ≠ 1 ∧ nJ ^ 7 = 1 ∧ nJ ≠ 1 ∧
    elt wy11 ^ 11 = 1 ∧ elt wy11 ≠ 1 ∧ elt wy19 ^ 19 = 1 ∧ elt wy19 ≠ 1 := by
  simp only [ne_eq, ← elt_pow, elt_eq_one_iff]
  decide +kernel

theorem inv_yJ : uJ * uJ = 1 ∧ uJ ≠ 1 ∧ uJ * mJ * uJ⁻¹ = mJ⁻¹ ∧
    sJ * sJ = 1 ∧ sJ ≠ 1 ∧ sJ * nJ * sJ⁻¹ = nJ⁻¹ ∧
    elt wi11 * elt wi11 = 1 ∧ elt wi11 ≠ 1 ∧ elt wi11 * elt wy11 * (elt wi11)⁻¹ = (elt wy11)⁻¹ ∧
    elt wi19 * elt wi19 = 1 ∧ elt wi19 ≠ 1 ∧
      elt wi19 * elt wy19 * (elt wi19)⁻¹ = (elt wy19)⁻¹ := by
  simp only [ne_eq, ← elt_inv, ← elt_append, elt_eq_one_iff, elt_eq_elt_iff]
  decide +kernel

theorem orderOf_yJ {p : ℕ} (hp : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19) :
    orderOf (yJ p) = p := by
  obtain ⟨h3, n3, h7, n7, h11, n11, h19, n19⟩ := orders_yJ
  obtain ⟨-, -, -, -, h5, -, -⟩ := rels_F
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact orderOf_eq_prime (p := 3) (hp := ⟨by norm_num⟩) h3 n3
  · exact orderOf_eq_prime (p := 5) (hp := ⟨by norm_num⟩) h5 ne_one_F.2.2.2.1
  · exact orderOf_eq_prime (p := 7) (hp := ⟨by norm_num⟩) h7 n7
  · exact orderOf_eq_prime (p := 11) (hp := ⟨by norm_num⟩) h11 n11
  · exact orderOf_eq_prime (p := 19) (hp := ⟨by norm_num⟩) h19 n19

theorem iJ_inv {p : ℕ} (hp : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19) :
    orderOf (iJ p) = 2 ∧ iJ p * yJ p * (iJ p)⁻¹ = (yJ p)⁻¹ := by
  obtain ⟨u2, u1, um, s2, s1, sn, i2, i1, iy, j2, j1, jy⟩ := inv_yJ
  obtain ⟨x2, -, -, -, -, -, -⟩ := rels_F
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ⟨J1.orderOf_eq_two_iff.mpr ⟨u2, u1⟩, um⟩
  · refine ⟨J1.orderOf_eq_two_iff.mpr ⟨x2, ne_one_F.1⟩, ?_⟩
    change xJ * (uJ * xJ) * xJ⁻¹ = (uJ * xJ)⁻¹
    have hx : xJ⁻¹ = xJ := inv_eq_of_mul_eq_one_right x2
    have hu : uJ⁻¹ = uJ := uJ_inv
    rw [hx, mul_inv_rev, hx, hu, mul_assoc, mul_assoc, x2, mul_one]
  · exact ⟨J1.orderOf_eq_two_iff.mpr ⟨s2, s1⟩, sn⟩
  · exact ⟨J1.orderOf_eq_two_iff.mpr ⟨i2, i1⟩, iy⟩
  · exact ⟨J1.orderOf_eq_two_iff.mpr ⟨j2, j1⟩, jy⟩

@[expose] noncomputable def sylowJ {p : ℕ} [Fact p.Prime]
    (hp : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19) : Sylow p walterJ1 :=
  (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_yJ hp, pow_one]) :
    IsPGroup p (Subgroup.zpowers (yJ p))).toSylow
    (not_dvd_index_of_card hp (by rw [Nat.card_zpowers, orderOf_yJ hp]))

theorem coe_sylowJ {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19) :
    (sylowJ hp : Subgroup walterJ1) = Subgroup.zpowers (yJ p) := rfl

theorem J1_simple : IsSimpleGroup walterJ1 := isSimpleGroup_walterJ1

theorem J1_card : Nat.card walterJ1 = 2 ^ 3 * 3 * 5 * 7 * 11 * 19 := by
  rw [card_walterJ1]
  norm_num

theorem J1_isConj_involutions
    {x y : walterJ1} (hx : orderOf x = 2) (hy : orderOf y = 2) :
    IsConj x y :=
  jankoHyp.isConj_involutions hx hy

theorem J2_inverted {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (P : Sylow p walterJ1) :
    ∃ x : walterJ1, orderOf x = 2 ∧ ∀ z ∈ (P : Subgroup walterJ1), x * z * x⁻¹ = z⁻¹ := by
  by_cases hd : p ∣ 175560
  · have hp : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 := by
      rcases prime_dvd_card (Fact.out : p.Prime) hd with h | h
      · exact absurd h hp2
      · exact h
    obtain ⟨hi, hiy⟩ := iJ_inv hp
    exact exists_inv_of_sylow hi hiy (sylowJ hp) (coe_sylowJ hp) P
  · refine ⟨tJ, orderOf_tJ, fun z hz => ?_⟩
    rw [sylow_eq_bot_of_not_dvd hd P, Subgroup.mem_bot] at hz
    rw [hz, mul_one, mul_inv_cancel, inv_one]

theorem card_centralizer_of_orderOf_eq_two
    {x : walterJ1} (hx : orderOf x = 2) :
    Nat.card (Subgroup.centralizer ({x} : Set walterJ1)) = 120 := by
  obtain ⟨g, hg⟩ := jankoHyp.exists_conj_eq_t hx
  have : (jankoHyp.conj g⁻¹).t = x := by
    rw [J1.JankoHyp.conj_t, ← hg]
    group
  rw [← this]
  exact (jankoHyp.conj g⁻¹).card_centralizer

theorem J2_centralizer
    {x : walterJ1} (hx : orderOf x = 2) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Sylow p walterJ1) (hP : (P : Subgroup walterJ1) ≠ ⊥)
    (hPx : (P : Subgroup walterJ1) ≤ Subgroup.centralizer ({x} : Set walterJ1)) :
    p = 3 ∨ p = 5 := by
  obtain ⟨⟨z, hzP⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  obtain ⟨k, hk⟩ := (P.isPGroup' ⟨z, hzP⟩)
  have hpz : p ∣ orderOf z := by
    rw [← Subgroup.orderOf_mk z hzP]
    have := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp this
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hz1 (congrArg Subtype.val hj)
    rw [hj]
    exact dvd_pow_self p hj0
  have h120 : p ∣ 120 := by
    rw [← card_centralizer_of_orderOf_eq_two hx]
    exact hpz.trans (Subgroup.orderOf_dvd_natCard _ (hPx hzP))
  have hp : p.Prime := Fact.out
  rw [show (120 : ℕ) = 2 ^ 3 * (3 * 5) by norm_num] at h120
  rcases (Nat.Prime.dvd_mul hp).mp h120 with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)) hp2
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)

theorem smul_zpowers (g y : walterJ1) :
    MulAut.conj g • Subgroup.zpowers y = Subgroup.zpowers (g * y * g⁻¹) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
    Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [conj_zpow, hk]; group⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk, conj_zpow]; group⟩

theorem exists_eq_zpowers_conj {p : ℕ} [Fact p.Prime]
    (hp : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19) (P : Sylow p walterJ1) :
    ∃ g : walterJ1, (P : Subgroup walterJ1) = Subgroup.zpowers (g * yJ p * g⁻¹) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq walterJ1 (sylowJ hp) P
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, coe_sylowJ, smul_zpowers]

theorem dvd_card_normQuot_conj {y r : walterJ1} {k e : ℕ} (hr : r * y * r⁻¹ = y ^ k) (he0 : 0 < e)
    (he : r ^ e = 1) (hq : ∀ q : ℕ, q.Prime → q ∣ e → r ^ (e / q) * y ≠ y * r ^ (e / q))
    (g : walterJ1) : e ∣ Nat.card (normQuot (Subgroup.zpowers (g * y * g⁻¹))) := by
  have hc : ∀ j : ℕ, (g * r * g⁻¹) ^ j = g * r ^ j * g⁻¹ := fun j => conj_pow
  apply dvd_card_normQuot _ he0
  · rw [hc, he, mul_one, mul_inv_cancel, one_mul, mul_one]
  · intro q hq' hqe h
    rw [hc] at h
    apply hq q hq' hqe
    calc r ^ (e / q) * y = g⁻¹ * (g * r ^ (e / q) * g⁻¹ * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * (g * r ^ (e / q) * g⁻¹)) * g := by rw [h]
      _ = y * r ^ (e / q) := by group
  · have h1 : g * r * g⁻¹ * (g * y * g⁻¹) * (g * r * g⁻¹)⁻¹ = (g * y * g⁻¹) ^ k := by
      rw [show g * r * g⁻¹ * (g * y * g⁻¹) * (g * r * g⁻¹)⁻¹ = g * (r * y * r⁻¹) * g⁻¹ by group,
        hr, conj_pow]
    refine J1.mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨j, rfl⟩ := hz
    refine ⟨k * j, ?_⟩
    change (g * y * g⁻¹) ^ ((k : ℤ) * j) = g * r * g⁻¹ * (g * y * g⁻¹) ^ j * (g * r * g⁻¹)⁻¹
    rw [← conj_zpow, h1, ← zpow_natCast, ← zpow_mul]

theorem rels_r : elt wr7 * nJ * (elt wr7)⁻¹ = nJ ^ 3 ∧ elt wr7 ^ 6 = 1 ∧
    elt wr7 ^ 3 * nJ ≠ nJ * elt wr7 ^ 3 ∧ elt wr7 ^ 2 * nJ ≠ nJ * elt wr7 ^ 2 ∧
    elt wr11 * elt wy11 * (elt wr11)⁻¹ = elt wy11 ^ 2 ∧ elt wr11 ^ 10 = 1 ∧
    elt wr11 ^ 5 * elt wy11 ≠ elt wy11 * elt wr11 ^ 5 ∧
    elt wr11 ^ 2 * elt wy11 ≠ elt wy11 * elt wr11 ^ 2 := by
  simp only [ne_eq, ← elt_inv, ← elt_pow, ← elt_append, elt_eq_one_iff, elt_eq_elt_iff]
  decide +kernel

theorem rels_r19 : elt wr19 * elt wy19 * (elt wr19)⁻¹ = elt wy19 ^ 8 ∧ elt wr19 ^ 6 = 1 ∧
    elt wr19 ^ 3 * elt wy19 ≠ elt wy19 * elt wr19 ^ 3 ∧
    elt wr19 ^ 2 * elt wy19 ≠ elt wy19 * elt wr19 ^ 2 := by
  simp only [ne_eq, ← elt_inv, ← elt_pow, ← elt_append, elt_eq_one_iff, elt_eq_elt_iff]
  decide +kernel

theorem prime_dvd_six {q : ℕ} (hq : q.Prime) (h : q ∣ 6) : q = 2 ∨ q = 3 := by
  have := Nat.le_of_dvd (by norm_num) h
  interval_cases q <;> simp_all <;> norm_num at hq

theorem prime_dvd_ten {q : ℕ} (hq : q.Prime) (h : q ∣ 10) : q = 2 ∨ q = 5 := by
  have := Nat.le_of_dvd (by norm_num) h
  interval_cases q <;> simp_all <;> norm_num at hq

theorem J2_seven (P : Sylow 7 walterJ1) :
    IsCyclic (normQuot (P : Subgroup walterJ1)) ∧
      Nat.card (normQuot (P : Subgroup walterJ1)) = 6 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨r1, r2, r3, r4, -, -, -, -⟩ := rels_r
  obtain ⟨g, hg⟩ := exists_eq_zpowers_conj (by norm_num) P
  have hcard : Nat.card (Subgroup.zpowers (g * yJ 7 * g⁻¹)) = 7 := by
    rw [Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_yJ (by norm_num)]
  obtain ⟨hcyc, hdvd, -⟩ := isCyclic_normQuot (p := 7) _ hcard
  have h6 := dvd_card_normQuot_conj (y := nJ) r1 (by norm_num) r2 (fun q hq hq6 => by
    rcases prime_dvd_six hq hq6 with rfl | rfl
    · exact r3
    · exact r4) g
  rw [hg]
  exact ⟨hcyc, Nat.dvd_antisymm hdvd h6⟩

theorem J2_eleven (P : Sylow 11 walterJ1) :
    IsCyclic (normQuot (P : Subgroup walterJ1)) ∧
      Nat.card (normQuot (P : Subgroup walterJ1)) = 10 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨-, -, -, -, r1, r2, r3, r4⟩ := rels_r
  obtain ⟨g, hg⟩ := exists_eq_zpowers_conj (by norm_num) P
  have hcard : Nat.card (Subgroup.zpowers (g * yJ 11 * g⁻¹)) = 11 := by
    rw [Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_yJ (by norm_num)]
  obtain ⟨hcyc, hdvd, -⟩ := isCyclic_normQuot (p := 11) _ hcard
  have h10 := dvd_card_normQuot_conj (y := elt wy11) r1 (by norm_num) r2 (fun q hq hq10 => by
    rcases prime_dvd_ten hq hq10 with rfl | rfl
    · exact r3
    · exact r4) g
  rw [hg]
  exact ⟨hcyc, Nat.dvd_antisymm hdvd h10⟩

theorem J2_nineteen (P : Sylow 19 walterJ1) :
    IsCyclic (normQuot (P : Subgroup walterJ1)) ∧
      Nat.card (normQuot (P : Subgroup walterJ1)) = 6 := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  obtain ⟨r1, r2, r3, r4⟩ := rels_r19
  obtain ⟨g, hg⟩ := exists_eq_zpowers_conj (by norm_num) P
  have hcard : Nat.card (Subgroup.zpowers (g * yJ 19 * g⁻¹)) = 19 := by
    rw [Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_yJ (by norm_num)]
  obtain ⟨hcyc, hdvd, hdvdL⟩ := isCyclic_normQuot (p := 19) _ hcard
  have h6 := dvd_card_normQuot_conj (y := elt wy19) r1 (by norm_num) r2 (fun q hq hq6 => by
    rcases prime_dvd_six hq hq6 with rfl | rfl
    · exact r3
    · exact r4) g
  rw [card_walterJ1] at hdvdL
  have hd6 : Nat.card (normQuot (Subgroup.zpowers (g * yJ 19 * g⁻¹))) ∣ 6 := by
    have := Nat.dvd_gcd hdvd hdvdL
    rwa [show Nat.gcd (19 - 1) 175560 = 6 by norm_num] at this
  rw [hg]
  exact ⟨hcyc, Nat.dvd_antisymm hd6 h6⟩

theorem not_eight_dvd_card_normalizer
    {P : Subgroup walterJ1} {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hP : Nat.card P = p) :
    ¬ 8 ∣ Nat.card (Subgroup.normalizer (P : Set walterJ1)) := by
  intro h8
  set N := Subgroup.normalizer (P : Set walterJ1)
  obtain ⟨S₀, hS₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := N) 2 (n := 3)
    (by norm_num; exact h8)
  set S' := S₀.map N.subtype
  have hS'card : Nat.card S' = 8 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, hS₀]
    norm_num
  have hS'N : S' ≤ N := Subgroup.map_subtype_le S₀
  have hS'2 : IsPGroup 2 S' := IsPGroup.of_card (n := 3) (by rw [hS'card]; norm_num)
  have hidx : ¬ 2 ∣ S'.index := by
    have := S'.card_mul_index
    rw [hS'card, card_walterJ1] at this
    omega
  obtain ⟨-, hsq, hcomm, -⟩ := jankoHyp.sylow_structure (hS'2.toSylow hidx)
  let ψ : S' →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hS'N)
  have hPc : IsCyclic P := isCyclic_of_prime_card hP
  have hA : IsCyclic (MulAut P) := by
    have : IsCyclic (ZMod (Nat.card P))ˣ := by
      rw [hP]
      exact ZMod.isCyclic_units_prime hp.out
    exact isCyclic_of_surjective (IsCyclic.mulAutMulEquiv P).symm
      (IsCyclic.mulAutMulEquiv P).symm.surjective
  have hrange : Nat.card ψ.range ≤ 2 := by
    have hRc : IsCyclic ψ.range := Subgroup.isCyclic _
    obtain ⟨⟨_, s, rfl⟩, ha⟩ := hRc.exists_generator
    have ha2 : (⟨ψ s, s, rfl⟩ : ψ.range) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, pow_two]
      have : s * s = 1 := Subtype.ext (hsq _ s.2)
      rw [this, map_one]
    rw [← orderOf_eq_card_of_forall_mem_zpowers ha]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ha2)
  have hker : 4 ≤ Nat.card ψ.ker := by
    have h := ψ.ker.card_mul_index
    rw [Subgroup.index_ker, hS'card] at h
    have hpos : 0 < Nat.card ψ.range := Nat.card_pos
    by_contra hlt
    have : Nat.card ψ.ker * Nat.card ψ.range ≤ 3 * 2 := Nat.mul_le_mul (by omega) hrange
    omega
  classical
  have : Fintype ψ.ker := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hker
  obtain ⟨v₁, -, hv₁⟩ := Finset.exists_mem_ne (s := (Finset.univ : Finset ψ.ker))
    (by rw [Finset.card_univ]; omega) 1
  obtain ⟨v₂, hv₂m, hv₂⟩ := Finset.exists_mem_ne (s := (Finset.univ : Finset ψ.ker).erase 1)
    (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega) v₁
  have hv₂1 : v₂ ≠ 1 := Finset.ne_of_mem_erase hv₂m
  set w₁ : walterJ1 := ((v₁ : S') : walterJ1)
  set w₂ : walterJ1 := ((v₂ : S') : walterJ1)
  have hw₁ : w₁ * w₁ = 1 := hsq _ (v₁ : S').2
  have hw₂ : w₂ * w₂ = 1 := hsq _ (v₂ : S').2
  have hw₁₂ : w₁ * w₂ = w₂ * w₁ := hcomm _ (v₁ : S').2 _ (v₂ : S').2
  have hw₁1 : w₁ ≠ 1 := fun h => hv₁ (Subtype.ext (Subtype.ext h))
  have hw₂1 : w₂ ≠ 1 := fun h => hv₂1 (Subtype.ext (Subtype.ext h))
  have hw₁₂' : w₁ ≠ w₂ := fun h => hv₂ (Subtype.ext (Subtype.ext h.symm))
  have hcent : ∀ v : ψ.ker, ∀ z ∈ P, ((v : S') : walterJ1) * z = z * (v : S') := by
    intro v z hz
    have h := congrArg (fun f : MulAut P => ((f ⟨z, hz⟩ : P) : walterJ1)) v.2
    change ((v : S') : walterJ1) * z * ((v : S') : walterJ1)⁻¹ = z at h
    calc ((v : S') : walterJ1) * z
        = ((v : S') : walterJ1) * z * ((v : S') : walterJ1)⁻¹ * (v : S') := by group
      _ = z * (v : S') := by rw [h]
  have : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by rw [hP]; exact hp.out.one_lt)
  obtain ⟨⟨y, hyP⟩, hy1'⟩ := exists_ne (1 : P)
  have hy1 : y ≠ 1 := fun h => hy1' (Subtype.ext h)
  have hyodd : Odd (orderOf y) := by
    have h := Subgroup.orderOf_dvd_natCard P hyP
    rw [hP] at h
    exact Odd.of_dvd_nat (hp.out.odd_of_ne_two hp2) h
  obtain ⟨g, hg⟩ := jankoHyp.exists_conj_eq_t (J1.orderOf_eq_two_iff.mpr ⟨hw₁, hw₁1⟩)
  set h₁ := jankoHyp.conj g⁻¹
  have ht₁ : h₁.t = w₁ := by
    rw [J1.JankoHyp.conj_t, ← hg]
    group
  have hyC : y ∈ Subgroup.centralizer ({h₁.t} : Set walterJ1) := by
    rw [ht₁, Subgroup.mem_centralizer_singleton_iff]
    exact (hcent v₁ y hyP).symm
  have hyF := h₁.mem_F_of_odd hyC hyodd
  have hw₂C : w₂ ∈ Subgroup.centralizer ({h₁.t} : Set walterJ1) := by
    rw [ht₁, Subgroup.mem_centralizer_singleton_iff]
    exact hw₁₂.symm
  have key : ∀ f ∈ h₁.F, f * f = 1 → f ≠ 1 → f * y = y * f → False := by
    intro f hf hf2 hf1 hfy
    have := J1.A5Sub.sq_eq_one_of_commute h₁.iso hf hyF (by rw [pow_two]; exact hf2) hf1 hfy
    have hd := orderOf_dvd_of_pow_eq_one this
    have h2 : orderOf y ∣ Nat.gcd (orderOf y) 2 := Nat.dvd_gcd dvd_rfl hd
    rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr hyodd), Nat.dvd_one,
      orderOf_eq_one_iff] at h2
    exact hy1 h2
  rcases h₁.mem_centralizer_t.mp hw₂C with hF | hF
  · exact key w₂ hF hw₂ hw₂1 (hcent v₂ y hyP)
  · rw [ht₁] at hF
    refine key (w₁ * w₂) hF ?_ ?_ ?_
    · calc w₁ * w₂ * (w₁ * w₂) = w₁ * (w₂ * w₁) * w₂ := by group
        _ = 1 := by rw [← hw₁₂, ← mul_assoc, hw₁, one_mul, hw₂]
    · intro h
      apply hw₁₂'
      calc w₁ = w₁ * (w₂ * w₂) := by rw [hw₂, mul_one]
        _ = (w₁ * w₂) * w₂ := by group
        _ = w₂ := by rw [h, one_mul]
    · calc w₁ * w₂ * y = w₁ * (w₂ * y) := by group
        _ = w₁ * (y * w₂) := by rw [hcent v₂ y hyP]
        _ = (w₁ * y) * w₂ := by group
        _ = (y * w₁) * w₂ := by rw [hcent v₁ y hyP]
        _ = y * (w₁ * w₂) := by group

theorem four_dvd_card_normalizer {t i y : walterJ1} (ht : t * t = 1) (hi : i * i = 1)
    (ht1 : t ≠ 1) (hi1 : i ≠ 1) (hti : t ≠ i) (hcomm : t * i = i * t) (hty : t * y = y * t)
    (hiy : i * y * i⁻¹ = y⁻¹) (g : walterJ1) :
    4 ∣ Nat.card (Subgroup.normalizer
      ((Subgroup.zpowers (g * y * g⁻¹) : Subgroup walterJ1) : Set walterJ1)) := by
  have hc : ∀ a b : walterJ1, (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := fun a b => by
    group
  have ht' : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by rw [hc, ht, mul_one, mul_inv_cancel]
  have hi' : (g * i * g⁻¹) * (g * i * g⁻¹) = 1 := by rw [hc, hi, mul_one, mul_inv_cancel]
  have hc' : Commute (g * t * g⁻¹) (g * i * g⁻¹) := by
    change (g * t * g⁻¹) * (g * i * g⁻¹) = (g * i * g⁻¹) * (g * t * g⁻¹)
    rw [hc, hc, hcomm]
  have hne : ∀ a b : walterJ1, a ≠ b → g * a * g⁻¹ ≠ g * b * g⁻¹ := fun a b hab h =>
    hab (by simpa [mul_assoc] using h)
  have h1 : ∀ a : walterJ1, a ≠ 1 → g * a * g⁻¹ ≠ 1 := fun a ha h =>
    hne a 1 ha (by rw [h, mul_one, mul_inv_cancel])
  have hV : Nat.card (GorensteinWalter.kleinFourOfCommutingInvolutions _ _ ht' hi' hc') = 4 :=
    (GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions _ _ ht' hi' (h1 t ht1)
      (h1 i hi1) (hne t i hti) hc').card_four
  rw [← hV]
  apply Subgroup.card_dvd_of_le
  have hy' : (g * t * g⁻¹) * (g * y * g⁻¹) * (g * t * g⁻¹)⁻¹ = g * y * g⁻¹ := by
    rw [show (g * t * g⁻¹) * (g * y * g⁻¹) * (g * t * g⁻¹)⁻¹ = g * (t * y * t⁻¹) * g⁻¹ by
      group, hty, mul_inv_cancel_right]
  have hiy' : (g * i * g⁻¹) * (g * y * g⁻¹) * (g * i * g⁻¹)⁻¹ = (g * y * g⁻¹)⁻¹ := by
    rw [show (g * i * g⁻¹) * (g * y * g⁻¹) * (g * i * g⁻¹)⁻¹ = g * (i * y * i⁻¹) * g⁻¹ by
      group, hiy]
    group
  have hnorm : ∀ x : walterJ1, (x * (g * y * g⁻¹) * x⁻¹ = g * y * g⁻¹ ∨
      x * (g * y * g⁻¹) * x⁻¹ = (g * y * g⁻¹)⁻¹) →
      x ∈ Subgroup.normalizer ((Subgroup.zpowers (g * y * g⁻¹) : Subgroup walterJ1) :
        Set walterJ1) := by
    intro x hx
    refine J1.mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨j, rfl⟩ := hz
    change x * (g * y * g⁻¹) ^ j * x⁻¹ ∈ Subgroup.zpowers (g * y * g⁻¹)
    rw [← conj_zpow]
    rcases hx with hx | hx <;> rw [hx]
    · exact Subgroup.zpow_mem_zpowers _ _
    · exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) _
  intro x hx
  change x ∈ ({(g * t * g⁻¹) * (g * i * g⁻¹), g * t * g⁻¹, g * i * g⁻¹, 1} :
    Set walterJ1) at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Subgroup.mul_mem _ (hnorm _ (Or.inl hy')) (hnorm _ (Or.inr hiy'))
  · exact hnorm _ (Or.inl hy')
  · exact hnorm _ (Or.inr hiy')
  · exact Subgroup.one_mem _

theorem four_data : tJ * uJ = uJ * tJ ∧ tJ * mJ = mJ * tJ ∧ tJ ≠ uJ ∧ tJ ≠ xJ := by
  simp only [ne_eq, ← elt_append, elt_eq_elt_iff]
  decide +kernel

theorem J2_normalizer_two_part
    {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 5) (P : Sylow p walterJ1) :
    (Nat.card (Subgroup.normalizer ((P : Subgroup walterJ1) : Set walterJ1))).factorization 2 =
      2 := by
  have hp' : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 := by
    rcases hp with rfl | rfl <;> simp
  obtain ⟨g, hg⟩ := exists_eq_zpowers_conj hp' P
  have hcard : Nat.card (P : Subgroup walterJ1) = p := by
    rw [hg, Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_yJ hp']
  have h8 := not_eight_dvd_card_normalizer (by rcases hp with rfl | rfl <;> norm_num) hcard
  obtain ⟨ht2, -⟩ := J1.orderOf_eq_two_iff.mp orderOf_tJ
  obtain ⟨htu, htm, htu', htx⟩ := four_data
  obtain ⟨x2, -, u2, -, -, -, -⟩ := rels_F
  have h4 : 4 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup walterJ1) : Set walterJ1)) := by
    rw [hg]
    rcases hp with rfl | rfl
    · obtain ⟨u2', u1, um, -⟩ := inv_yJ
      exact four_dvd_card_normalizer ht2 u2' ne_one_F.2.2.2.2.2 u1 htu' htu htm um g
    · obtain ⟨hi2, hiy⟩ := iJ_inv (p := 5) (by norm_num)
      refine four_dvd_card_normalizer ht2 x2 ne_one_F.2.2.2.2.2 ne_one_F.1 htx
        commute_tJ.1.symm ?_ hiy g
      change tJ * (uJ * xJ) = uJ * xJ * tJ
      rw [mul_assoc, commute_tJ.1, ← mul_assoc, ← commute_tJ.2.2, mul_assoc]
  have hn0 : Nat.card (Subgroup.normalizer ((P : Subgroup walterJ1) : Set walterJ1)) ≠ 0 :=
    Nat.card_pos.ne'
  have h2 := (Nat.Prime.pow_dvd_iff_le_factorization (k := 2) Nat.prime_two hn0).mp h4
  have h3 : ¬ 3 ≤ _ := fun h3 =>
    h8 ((Nat.Prime.pow_dvd_iff_le_factorization (k := 3) Nat.prime_two hn0).mpr h3)
  omega

end CFSG.Walter.J1Props
