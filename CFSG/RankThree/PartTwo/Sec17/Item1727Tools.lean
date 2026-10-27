module

public import CFSG.RankThree.PartTwo.Sec17.Item17ParaTools
public import CFSG.RankThree.PartTwo.Sec17.Item17TailEnd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G]

theorem zpow_eq_zpow_emod_three {e : G} (he : e ^ 3 = 1) (k : ℤ) : e ^ k = e ^ (k % 3) := by
  conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
  rw [zpow_add, zpow_mul, show e ^ (3 : ℤ) = 1 by exact_mod_cast he, one_zpow, mul_one]

theorem inf_centralizer_mul_of_mem {V : Subgroup G} {x y : G}
    (hy : y ∈ Subgroup.centralizer (V : Set G)) :
    V ⊓ Subgroup.centralizer ({x * y} : Set G) = V ⊓ Subgroup.centralizer ({x} : Set G) := by
  ext v
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hv, h⟩
    refine ⟨hv, ?_⟩
    have hyv : v * y = y * v := (Subgroup.mem_centralizer_iff.mp hy v hv)
    have h' : v * x * y = x * v * y := by rw [mul_assoc, h, mul_assoc x, ← hyv, ← mul_assoc]
    exact mul_right_cancel h'
  · rintro ⟨hv, h⟩
    refine ⟨hv, ?_⟩
    have hyv : v * y = y * v := (Subgroup.mem_centralizer_iff.mp hy v hv)
    rw [← mul_assoc, h, mul_assoc, hyv, ← mul_assoc]

theorem conj_mem_centralizer_of_mem_normalizer {V : Subgroup G} {g y : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hy : y ∈ Subgroup.centralizer (V : Set G)) :
    g * y * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have hCV : g ∈ Subgroup.normalizer ((Subgroup.centralizer (V : Set G) : Subgroup G) :
      Set G) := by
    refine mem_normalizer_of_map_conj_eq' ?_
    rw [Sec14.map_conj_centralizer, Late.map_conj_eq_of_mem_normalizer hg]
  exact (Subgroup.mem_normalizer_iff.mp hCV y).mp hy

theorem inf_centralizer_inv (V : Subgroup G) (x : G) :
    V ⊓ Subgroup.centralizer ({x⁻¹} : Set G) = V ⊓ Subgroup.centralizer ({x} : Set G) := by
  ext v
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨hv, (Commute.inv_right_iff.mp (show Commute v x⁻¹ from h))⟩
  · rintro ⟨hv, h⟩
    exact ⟨hv, (Commute.inv_right (show Commute v x from h))⟩

theorem mem_normalizer_inf_centralizer_of_eq {V : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G))
    (h : V ⊓ Subgroup.centralizer ({g * x * g⁻¹} : Set G) =
      V ⊓ Subgroup.centralizer ({x} : Set G)) :
    g ∈ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  exact mem_normalizer_of_map_conj_eq' ((map_conj_inf_centralizer hg x).trans h)

section Finite

variable [Finite G]

theorem mem_centralizer_of_inverts {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≠ 3) {V : Subgroup G}
    (hVe : CFSG.Assembly.IsElemAbelian p V) (hV : Nat.card V = p ^ 2) {c e s t : G}
    (hc3 : c ^ 3 = 1) (he3 : e ^ 3 = 1) (hce : c * e = e * c)
    (hcV : c ∈ Subgroup.normalizer (V : Set G)) (heV : e ∈ Subgroup.normalizer (V : Set G))
    (hsV : s ∈ Subgroup.normalizer (V : Set G)) (htV : t ∈ Subgroup.normalizer (V : Set G))
    (hfix : V ⊓ Subgroup.centralizer ({c} : Set G) = ⊥) (hsc : s * c * s⁻¹ = c⁻¹)
    (htc : t * c * t⁻¹ = c)
    (hse : ∃ k : ℤ, ∃ y ∈ Subgroup.centralizer (V : Set G), s * e * s⁻¹ = e ^ k * y)
    (hte : ∃ y ∈ Subgroup.centralizer (V : Set G), t * e * t⁻¹ = e⁻¹ * y) :
    e ∈ Subgroup.centralizer (V : Set G) := by
  by_contra he
  have hVab : IsMulCommutative V := hVe.1
  have hcop : Nat.Coprime 3 (Nat.card V) := by
    rw [hV]
    exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes Nat.prime_three hp.out).mpr
      (Ne.symm hp3))
  have hCe : V ⊓ Subgroup.centralizer ({e} : Set G) ≠ V := by
    intro h
    apply he
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : v ∈ V ⊓ Subgroup.centralizer ({e} : Set G) := by rw [h]; exact hv
    exact Subgroup.mem_centralizer_singleton_iff.mp hv'.2
  obtain ⟨k, y, hyC, hsek⟩ := hse
  obtain ⟨y', hy'C, htey⟩ := hte
  have hk : k % 3 = 1 ∨ k % 3 = 2 := by
    have hlt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    have hge : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h0 | h1 | h2
    · exfalso
      apply he
      rw [zpow_eq_zpow_emod_three he3, h0, zpow_zero, one_mul] at hsek
      have hCV : s⁻¹ ∈ Subgroup.normalizer ((Subgroup.centralizer (V : Set G) : Subgroup G) :
          Set G) := by
        refine inv_mem (mem_normalizer_of_map_conj_eq' ?_)
        rw [Sec14.map_conj_centralizer, Late.map_conj_eq_of_mem_normalizer hsV]
      have := (Subgroup.mem_normalizer_iff.mp hCV y).mp hyC
      rwa [← hsek, show s⁻¹ * (s * e * s⁻¹) * s⁻¹⁻¹ = e by group] at this
    · exact Or.inl h1
    · exact Or.inr h2
  have hsek' : V ⊓ Subgroup.centralizer ({s * e * s⁻¹} : Set G) =
      V ⊓ Subgroup.centralizer ({e} : Set G) := by
    rw [hsek, inf_centralizer_mul_of_mem hyC, zpow_eq_zpow_emod_three he3]
    rcases hk with h1 | h2
    · rw [h1, zpow_one]
    · rw [h2, show (2 : ℤ) = -1 + 3 by norm_num, zpow_add, show e ^ (3 : ℤ) = 1 by
        exact_mod_cast he3, mul_one, zpow_neg_one, inf_centralizer_inv]
  have hcCe : c ∈ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) :
      Set G) := mem_normalizer_inf_centralizer hcV hce
  by_cases hCe1 : V ⊓ Subgroup.centralizer ({e} : Set G) = ⊥
  ·
    obtain ⟨hVeq, hdisj⟩ := eq_sup_inf_centralizer_mul hVab hcop hce hc3 he3 hcV heV hfix hCe1
    set ℓ₁ := V ⊓ Subgroup.centralizer ({c * e} : Set G) with hℓ₁
    set ℓ₂ := V ⊓ Subgroup.centralizer ({c * e⁻¹} : Set G) with hℓ₂
    have ht12 : ℓ₁.map (MulAut.conj t).toMonoidHom = ℓ₂ := by
      rw [hℓ₁, map_conj_inf_centralizer htV,
        show t * (c * e) * t⁻¹ = (t * c * t⁻¹) * (t * e * t⁻¹) by group, htc, htey,
        ← mul_assoc, inf_centralizer_mul_of_mem hy'C]
    have hcard12 : Nat.card ℓ₁ = Nat.card ℓ₂ := by
      rw [← ht12, Subgroup.card_map_of_injective (MulAut.conj t).injective]
    have hnorm : ℓ₂ ≤ Subgroup.normalizer (ℓ₁ : Set G) := by
      intro x hx
      refine Subgroup.mem_normalizer_fintype fun v hv => ?_
      have hc : x * v = v * x :=
        congrArg Subtype.val (hVab.is_comm.comm ⟨x, hx.1⟩ ⟨v, hv.1⟩)
      rw [hc, mul_inv_cancel_right]
      exact hv
    have hcardV : Nat.card V = Nat.card ℓ₁ ^ 2 := by
      conv_lhs => rw [hVeq]
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm
        (disjoint_iff.mpr hdisj), ← hcard12, sq]
    have hℓ₁p : Nat.card ℓ₁ = p := by
      rw [hV] at hcardV
      exact (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hcardV).symm
    have hℓ₁e : CFSG.Assembly.IsElemAbelian p ℓ₁ := ⟨⟨⟨fun a b => Subtype.ext
      (show (a : G) * b = b * a from congrArg Subtype.val
        (hVab.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩))⟩⟩, fun x hx => hVe.2 x hx.1⟩
    have hℓ₁1 : ℓ₁ ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hℓ₁p
      exact hp.out.one_lt.ne hℓ₁p
    have hcℓ₁ : c ∈ Subgroup.normalizer (ℓ₁ : Set G) :=
      mem_normalizer_inf_centralizer hcV (by rw [mul_assoc c e c, ← hce])
    have hℓfix : ℓ₁ ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_right _ inf_le_left).trans hfix.le)
    have hsce : V ⊓ Subgroup.centralizer ({s * (c * e) * s⁻¹} : Set G) =
        V ⊓ Subgroup.centralizer ({c⁻¹ * (s * e * s⁻¹)} : Set G) := by
      rw [show s * (c * e) * s⁻¹ = (s * c * s⁻¹) * (s * e * s⁻¹) by group, hsc]
    rcases hk with h1 | h2
    ·
      have hs21 : ℓ₂.map (MulAut.conj s).toMonoidHom = ℓ₁ := by
        rw [hℓ₂, map_conj_inf_centralizer hsV,
          show s * (c * e⁻¹) * s⁻¹ = (s * c * s⁻¹) * (s * e * s⁻¹)⁻¹ by group, hsc, hsek,
          zpow_eq_zpow_emod_three he3, h1, zpow_one,
          show c⁻¹ * (e * y)⁻¹ = (c⁻¹ * e⁻¹) * (e * y⁻¹ * e⁻¹) by group,
          inf_centralizer_mul_of_mem (conj_mem_centralizer_of_mem_normalizer heV (inv_mem hyC)),
          ← mul_inv_rev, inf_centralizer_inv, show e * c = c * e from hce.symm]
      have hst : s * t ∈ Subgroup.normalizer (ℓ₁ : Set G) := by
        refine mem_normalizer_of_map_conj_eq' ?_
        rw [map_conj_mul, ht12, hs21]
      have hstc : s * t * c * (s * t)⁻¹ = c⁻¹ := by
        calc s * t * c * (s * t)⁻¹ = s * (t * c * t⁻¹) * s⁻¹ := by group
          _ = c⁻¹ := by rw [htc, hsc]
      exact card_ne_of_inverts hℓ₁e hℓ₁1 hc3 hcℓ₁ hℓfix hst hstc hℓ₁p
    ·
      have hs11 : ℓ₁.map (MulAut.conj s).toMonoidHom = ℓ₁ := by
        rw [hℓ₁, map_conj_inf_centralizer hsV, hsce, hsek, zpow_eq_zpow_emod_three he3, h2,
          show (2 : ℤ) = -1 + 3 by norm_num, zpow_add, show e ^ (3 : ℤ) = 1 by
            exact_mod_cast he3, mul_one, zpow_neg_one, ← mul_assoc,
          inf_centralizer_mul_of_mem hyC, ← mul_inv_rev, inf_centralizer_inv,
          show e * c = c * e from hce.symm]
      exact card_ne_of_inverts hℓ₁e hℓ₁1 hc3 hcℓ₁ hℓfix
        (mem_normalizer_of_map_conj_eq' hs11) hsc hℓ₁p
  ·
    set ℓ := V ⊓ Subgroup.centralizer ({e} : Set G) with hℓ
    have hdvd : Nat.card ℓ ∣ p ^ 2 := hV ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨m, hm, hmc⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    have hm1 : m = 1 := by
      rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with h0 | h1 | h2
      · exfalso
        rw [h0, pow_zero] at hmc
        exact hCe1 (Subgroup.card_eq_one.mp hmc)
      · exact h1
      · exfalso
        rw [h2, ← hV] at hmc
        exact hCe (Subgroup.eq_of_le_of_card_ge inf_le_left hmc.ge)
    rw [hm1, pow_one] at hmc
    have hℓe : CFSG.Assembly.IsElemAbelian p ℓ := ⟨⟨⟨fun a b => Subtype.ext
      (show (a : G) * b = b * a from congrArg Subtype.val
        (hVab.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩))⟩⟩, fun x hx => hVe.2 x hx.1⟩
    have hℓfix : ℓ ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_right _ inf_le_left).trans hfix.le)
    exact card_ne_of_inverts hℓe hCe1 hc3 hcCe hℓfix
      (mem_normalizer_inf_centralizer_of_eq hsV hsek') hsc hmc

end Finite

theorem conj_eq_mul_zpow_of_pow_three {d e w : G} (he3 : e ^ 3 = 1) (hde : d * e = e * d)
    (hed : e ∉ Subgroup.zpowers d) (hw3 : w ^ 3 = 1) (hwd : w * d = d * w) {j i : ℤ}
    (hwe : w * e * w⁻¹ = e ^ j * d ^ i) : w * e * w⁻¹ = e * d ^ i := by
  have hwdk : ∀ b : ℤ, w * d ^ b * w⁻¹ = d ^ b := fun b => by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hwd, mul_inv_cancel_right]
  have hde' : ∀ b : ℤ, d ^ b * e = e * d ^ b := fun b =>
    (Commute.zpow_left (show Commute d e from hde) b).eq
  have he3' : e ^ (3 : ℤ) = 1 := by exact_mod_cast he3
  have hj : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rw [zpow_eq_zpow_emod_three he3] at hwe
  rcases hj with h0 | h1 | h2
  · exfalso
    rw [h0, zpow_zero, one_mul] at hwe
    apply hed
    have he : e = w⁻¹ * (w * e * w⁻¹) * w := by group
    rw [he, hwe]
    have hwd' : w⁻¹ * d ^ i * w = d ^ i := by
      have hc := (Commute.zpow_right (show Commute w d from hwd) i).eq
      rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hwd']
    exact Subgroup.zpow_mem_zpowers d i
  · rwa [h1, zpow_one] at hwe
  · exfalso
    rw [h2, show (2 : ℤ) = -1 + 3 by norm_num, zpow_add, he3', mul_one, zpow_neg_one] at hwe
    have hw2 : w * w * e * (w * w)⁻¹ = e := by
      calc w * w * e * (w * w)⁻¹ = w * (w * e * w⁻¹) * w⁻¹ := by group
        _ = w * (e⁻¹ * d ^ i) * w⁻¹ := by rw [hwe]
        _ = (w * e * w⁻¹)⁻¹ * (w * d ^ i * w⁻¹) := by group
        _ = (e⁻¹ * d ^ i)⁻¹ * d ^ i := by rw [hwe, hwdk]
        _ = d ^ (-i) * e * d ^ i := by group
        _ = e := by rw [hde' (-i), mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    have hwww : w * w * w = 1 := by rw [← hw3, pow_three, mul_assoc]
    have hw3e : e = e⁻¹ * d ^ i := by
      calc e = (w * w * w) * e * (w * w * w)⁻¹ := by rw [hwww]; group
        _ = w * (w * w * e * (w * w)⁻¹) * w⁻¹ := by group
        _ = e⁻¹ * d ^ i := by rw [hw2, hwe]
    apply hed
    have he2 : e * e = d ^ i := by
      calc e * e = e * (e⁻¹ * d ^ i) := by rw [← hw3e]
        _ = d ^ i := by group
    have he4 : e = (e * e) * (e * e) := by
      calc e = e * e ^ 3 := by rw [he3, mul_one]
        _ = (e * e) * (e * e) := by rw [pow_three]; group
    rw [he4, he2]
    exact mul_mem (Subgroup.zpow_mem_zpowers d i) (Subgroup.zpow_mem_zpowers d i)

section Thompson

@[expose, reducible] def conjActOn (B K : Subgroup G)
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) : MulDistribMulAction B K where
  smul v k := ⟨v * k * (v : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hBK v.2) k).mp k.2⟩
  one_smul k := Subtype.ext (by
    change ((1 : B) : G) * k * ((1 : B) : G)⁻¹ = k
    simp)
  mul_smul a b k := Subtype.ext (by
    change ((a : G) * b) * k * ((a : G) * b)⁻¹ = a * (b * k * (b : G)⁻¹) * (a : G)⁻¹
    group)
  smul_mul a x y := Subtype.ext (by
    change (a : G) * (x * y) * (a : G)⁻¹ = (a * x * (a : G)⁻¹) * (a * y * (a : G)⁻¹)
    group)
  smul_one a := Subtype.ext (by
    change (a : G) * 1 * (a : G)⁻¹ = 1
    group)

theorem le_centralizer_of_forall_pow_eq_one' [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {K B : Subgroup G} (hK : IsPGroup p K)
    (hB : Nat.Coprime (Nat.card B) (Nat.card K))
    (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hfix : ∀ y ∈ B, ∀ x ∈ K, x ^ p = 1 → y * x = x * y) :
    B ≤ Subgroup.centralizer (K : Set G) := by
  let := conjActOn B K hBK
  have : Fact (IsPGroup p K) := ⟨hK⟩
  have hΩ : ActsTriviallyOnSubgroup (A := B) (G := K) (omega₁ (G := K) (p := p)) := by
    intro a x hx
    have hle : omega₁ (G := K) (p := p) ≤ fixedPointSubgroup (Subgroup.zpowers a) K := by
      rw [omega₁, omega, Subgroup.closure_le]
      intro z hz
      rw [SetLike.mem_coe, FixedPoints.mem_subgroup]
      rintro ⟨b, hb⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hz' : (z : G) ^ p = 1 := by
        have : z ^ (p ^ 1) = 1 := hz
        rw [pow_one] at this
        simpa using congrArg Subtype.val this
      apply Subtype.ext
      change ((a ^ k : B) : G) * z * ((a ^ k : B) : G)⁻¹ = z
      have hc : ((a ^ k : B) : G) * z = z * ((a ^ k : B) : G) :=
        hfix _ (a ^ k).2 z z.2 hz'
      rw [hc, mul_inv_cancel_right]
    have := hle hx
    rw [FixedPoints.mem_subgroup] at this
    exact this ⟨a, Subgroup.mem_zpowers a⟩
  have htriv := theorem_1_11 (G := K) (A := B) hp2 hB hΩ
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have := congrArg Subtype.val (htriv ⟨y, hy⟩ ⟨x, hx⟩)
  change y * x * y⁻¹ = x at this
  calc x * y = (y * x * y⁻¹) * y := by rw [this]
    _ = y * x := by group

end Thompson

end CFSG.RankThree.PartTwo.Sec17
