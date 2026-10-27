module

public import CFSG.Quasithin.Vol2.Ch10SecKL7g
public import CFSG.Quasithin.Vol2.Ch10SecKL7f

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W]

abbrev CM (Mb L₁ L₂ : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  Mb ⊓ Subgroup.centralizer ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W))

theorem CM_comm (Mb L₁ L₂ : Subgroup (MulAut W)) : CM Mb L₂ L₁ = CM Mb L₁ L₂ := by
  rw [CM, CM, sup_comm]

structure RHyp (Mb L₁ L₂ R : Subgroup (MulAut W)) : Prop where
  le : R ≤ CM Mb L₁ L₂
  normal : ∀ g ∈ Mb, ∀ r ∈ R, g * r * g⁻¹ ∈ R
  odd : ∀ c ∈ CM Mb L₁ L₂, Odd (orderOf c) → c ∈ R
  card : Nat.card R = 5 ∨ Nat.card R = 25
  pow5 : ∀ r ∈ R, r ^ 5 = 1
  comm : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r

theorem RHyp.swap {Mb L₁ L₂ R : Subgroup (MulAut W)} (hR : RHyp Mb L₁ L₂ R) :
    RHyp Mb L₂ L₁ R where
  le := (CM_comm Mb L₁ L₂) ▸ hR.le
  normal := hR.normal
  odd := (CM_comm Mb L₁ L₂) ▸ hR.odd
  card := hR.card
  pow5 := hR.pow5
  comm := hR.comm

theorem mem_normalizer_CM {Mb L₁ L₂ : Subgroup (MulAut W)}
    (hnorm : Mb ≤ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)))
    {g : MulAut W} (hg : g ∈ Mb) : g ∈ Subgroup.normalizer (CM Mb L₁ L₂ : Set (MulAut W)) := by
  have key : ∀ g ∈ Mb, ∀ c ∈ CM Mb L₁ L₂, g * c * g⁻¹ ∈ CM Mb L₁ L₂ := by
    intro g hg c hc
    refine ⟨mul_mem (mul_mem hg hc.1) (Mb.inv_mem hg),
      Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ L₁ ⊔ L₂ :=
      (Subgroup.mem_normalizer_iff.1 (hnorm (Mb.inv_mem hg)) y).1 hy
    have h1 := Subgroup.mem_centralizer_iff.1 hc.2 _ hy'
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g⁻¹⁻¹) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * y := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (Mb.inv_mem hg) _ hc
  simpa [mul_assoc] using this

theorem pow5_of_equiv {R : Subgroup (MulAut W)} {A : Type} [AddCommGroup A]
    (hA : ∀ a : A, 5 • a = 0) (e : ↥R ≃* Multiplicative A) (r : MulAut W) (hr : r ∈ R) :
    r ^ 5 = 1 := by
  have h1 : e ((⟨r, hr⟩ : ↥R) ^ 5) = 1 := by
    rw [map_pow, ← ofAdd_toAdd (e _), ← ofAdd_nsmul, hA, ofAdd_zero]
  rw [map_eq_one_iff _ e.injective] at h1
  exact congrArg Subtype.val h1

theorem comm_of_equiv {R : Subgroup (MulAut W)} {A : Type} [AddCommGroup A]
    (e : ↥R ≃* Multiplicative A) (r : MulAut W) (hr : r ∈ R) (s : MulAut W) (hs : s ∈ R) :
    r * s = s * r := by
  have h1 : e (⟨r, hr⟩ * ⟨s, hs⟩) = e (⟨s, hs⟩ * ⟨r, hr⟩) := by
    rw [map_mul, map_mul, mul_comm]
  exact congrArg Subtype.val (e.injective h1)

theorem rHyp_of {Mb L₁ L₂ : Subgroup (MulAut W)}
    (hnorm : Mb ≤ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)))
    (hR : Nonempty (↥(twoResidual (CM Mb L₁ L₂)) ≃* Multiplicative (ZMod 5)) ∨
      Nonempty (↥(twoResidual (CM Mb L₁ L₂)) ≃* Multiplicative (ZMod 5 × ZMod 5))) :
    RHyp Mb L₁ L₂ (twoResidual (CM Mb L₁ L₂)) where
  le := twoResidual_le _
  normal g hg r hr := conj_mem_twoResidual (mem_normalizer_CM hnorm hg) hr
  odd c hc hodd := mem_twoResidual_of_odd hc hodd
  card := by
    rcases hR with h1 | h1
    · obtain ⟨e⟩ := h1
      left
      rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    · obtain ⟨e⟩ := h1
      right
      rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_prod,
        Nat.card_zmod]
  pow5 r hr := by
    have h5 : ((5 : ℕ) : ZMod 5) = 0 := ZMod.natCast_self 5
    rcases hR with h1 | h1
    · obtain ⟨e⟩ := h1
      exact pow5_of_equiv (fun a => by rw [nsmul_eq_mul, h5, zero_mul]) e r hr
    · obtain ⟨e⟩ := h1
      refine pow5_of_equiv (fun a => ?_) e r hr
      ext
      · rw [Prod.smul_fst, Prod.fst_zero, nsmul_eq_mul, h5, zero_mul]
      · rw [Prod.smul_snd, Prod.snd_zero, nsmul_eq_mul, h5, zero_mul]
  comm r hr s hs := by
    rcases hR with h1 | h1
    · obtain ⟨e⟩ := h1
      exact comm_of_equiv e r hr s hs
    · obtain ⟨e⟩ := h1
      exact comm_of_equiv e r hr s hs

namespace RHyp

variable {Mb L₁ L₂ R : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {τ : MulAut W}

theorem C_map_mem_W₁ (h : Hyp Mb L₁ L₂ W₁ W₂ τ) {c : MulAut W} (hc : c ∈ CM Mb L₁ L₂) {w : W}
    (hw : w ∈ W₁) : c w ∈ W₁ := by
  rw [h.mem_W₁_iff] at hw ⊢
  intro l hl
  have hcl := (Hyp.mem_C_iff.1 hc).2.2 l hl
  calc l (c w) = (l * c) w := rfl
    _ = (c * l) w := by rw [hcl]
    _ = c w := by rw [MulAut.mul_apply, hw l hl]

theorem exists_card_fix (h : Hyp Mb L₁ L₂ W₁ W₂ τ) {x : MulAut W} (hx : x ∈ CM Mb L₁ L₂) :
    ∃ k ≤ 4, Nat.card ↥(W₁ ⊓ fixV (Subgroup.zpowers x)) = 8 ^ k := by
  obtain ⟨c⟩ := h.coord
  have : Finite W := h.finite_W
  obtain ⟨k, hk⟩ := c.card_invariant (V := W₁ ⊓ fixV (Subgroup.zpowers x)) inf_le_left
    fun l hl v hv => by
      refine ⟨c.map_mem hl hv.1, mem_fixV_zp.2 ?_⟩
      have hxl := (Hyp.mem_C_iff.1 hx).2.1 l hl
      calc x (l v) = (x * l) v := rfl
        _ = (l * x) v := by rw [hxl]
        _ = l v := by rw [MulAut.mul_apply, mem_fixV_zp.1 hv.2]
  refine ⟨k, ?_, hk⟩
  have hle := Subgroup.card_le_of_le (inf_le_left : W₁ ⊓ fixV (Subgroup.zpowers x) ≤ W₁)
  rw [hk, h.card_W₁] at hle
  by_contra hk4
  have : 8 ^ 5 ≤ 8 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem inf_W₁ (h : Hyp Mb L₁ L₂ W₁ W₂ τ) {y : MulAut W} (hy : y ∈ CM Mb L₁ L₂)
    (hy5 : y ^ 5 = 1) :
    W₁ ⊓ fixV (Subgroup.zpowers y) = ⊥ ∨ W₁ ≤ fixV (Subgroup.zpowers y) := by
  have : Finite W := h.finite_W
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk4, hk⟩ := exists_card_fix h hy
  have hmod := card_modEq_fixV (p := 5) (k := 1) y (by simpa using hy5) W₁
    fun w hw => C_map_mem_W₁ h hy hw
  rw [hk, h.card_W₁] at hmod
  have hk' : k = 0 ∨ k = 4 := by
    interval_cases k <;> simp_all [Nat.ModEq]
  rcases hk' with rfl | rfl
  · left
    exact Subgroup.card_eq_one.1 (by rw [hk, pow_zero])
  · right
    have := Subgroup.eq_of_le_of_card_ge (inf_le_left : W₁ ⊓ fixV (Subgroup.zpowers y) ≤ W₁)
      (by rw [hk, h.card_W₁]; norm_num)
    exact this ▸ inf_le_right

theorem le_rkIdx (h : Hyp Mb L₁ L₂ W₁ W₂ τ) (hR : RHyp Mb L₁ L₂ R) {y : MulAut W} (hy : y ∈ R)
    (hy1 : y ≠ 1) : 12 ≤ rkIdx (fixV (Subgroup.zpowers y)) := by
  have hyC := hR.le hy
  rcases inf_W₁ h hyC (hR.pow5 y hy) with h1 | h1
  · exact h.le_rkIdx_of_inf (by rw [inf_comm]; exact h1)
  · rcases inf_W₁ h.swap (by rw [CM_comm]; exact hyC) (hR.pow5 y hy) with h2 | h2
    · exact h.swap.le_rkIdx_of_inf (by rw [inf_comm]; exact h2)
    · exact absurd (h.eq_one_of_fix (fun w hw => mem_fixV_zp.1 (h1 hw))
        (fun w hw => mem_fixV_zp.1 (h2 hw))) hy1

theorem exists_W₁ (h : Hyp Mb L₁ L₂ W₁ W₂ τ) (hR : RHyp Mb L₁ L₂ R) :
    ∃ y ∈ R, W₁ ⊓ fixV (Subgroup.zpowers y) = ⊥ := by
  obtain ⟨y, hyR, hy1⟩ : ∃ y ∈ R, y ≠ 1 := by
    by_contra hall
    have hbot : R = ⊥ := eq_bot_iff.2 fun y hy => by
      by_contra hy1
      exact hall ⟨y, hy, hy1⟩
    have hc := hR.card
    rw [hbot, Subgroup.card_bot] at hc
    omega
  have hyC := hR.le hyR
  rcases inf_W₁ h hyC (hR.pow5 y hyR) with h1 | h1
  · exact ⟨y, hyR, h1⟩
  have h2 : W₂ ⊓ fixV (Subgroup.zpowers y) = ⊥ := by
    rcases inf_W₁ h.swap (by rw [CM_comm]; exact hyC) (hR.pow5 y hyR) with h2 | h2
    · exact h2
    · exact absurd (h.eq_one_of_fix (fun w hw => mem_fixV_zp.1 (h1 hw))
        (fun w hw => mem_fixV_zp.1 (h2 hw))) hy1
  refine ⟨τ⁻¹ * y * τ, ?_, ?_⟩
  · have := hR.normal τ⁻¹ (Mb.inv_mem h.memτ) y hyR
    rwa [inv_inv] at this
  · refine eq_bot_iff.2 fun w hw => ?_
    obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.1 hw
    rw [mem_fixV_zp] at hw2
    have hτw : τ w ∈ W₂ := h.mapW ▸ ⟨w, hw1, rfl⟩
    have hyτ : y (τ w) = τ w := by
      have := congrArg τ hw2
      simpa [MulAut.mul_apply] using this
    have hmem : τ w ∈ W₂ ⊓ fixV (Subgroup.zpowers y) := ⟨hτw, mem_fixV_zp.2 hyτ⟩
    rw [h2, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact (map_eq_one_iff τ τ.injective).1 hmem

theorem fix_W₁_of (h : Hyp Mb L₁ L₂ W₁ W₂ τ) (hR : RHyp Mb L₁ L₂ R) {c : MulAut W}
    (hc : c ∈ CM Mb L₁ L₂) {k : ℕ} (hck : c ^ 2 ^ k = 1) (hcR : ∀ r ∈ R, c * r = r * c) :
    W₁ ≤ fixV (Subgroup.zpowers c) := by
  have : Finite W := h.finite_W
  obtain ⟨j, hj4, hj⟩ := exists_card_fix h hc
  obtain ⟨y, hyR, hy⟩ := exists_W₁ h hR
  have hyC := hR.le hyR
  set V := W₁ ⊓ fixV (Subgroup.zpowers c) with hV
  have hyV : ∀ v ∈ V, y v ∈ V := fun v hv => by
    refine ⟨C_map_mem_W₁ h hyC hv.1, mem_fixV_zp.2 ?_⟩
    calc c (y v) = (c * y) v := rfl
      _ = (y * c) v := by rw [hcR y hyR]
      _ = y v := by rw [MulAut.mul_apply, mem_fixV_zp.1 hv.2]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 := card_modEq_fixV (p := 5) (k := 1) y (by simpa using hR.pow5 y hyR) V hyV
  have hVy : V ⊓ fixV (Subgroup.zpowers y) = ⊥ :=
    eq_bot_iff.2 fun v hv => hy ▸ (⟨hv.1.1, hv.2⟩ : v ∈ W₁ ⊓ fixV (Subgroup.zpowers y))
  rw [hVy, Subgroup.card_bot, hj] at h5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := card_modEq_fixV (p := 2) (k := k) c hck W₁ fun w hw => C_map_mem_W₁ h hc hw
  rw [← hV, hj, h.card_W₁] at h2
  have hj' : j = 4 := by
    interval_cases j <;> simp_all [Nat.ModEq]
  subst hj'
  have := Subgroup.eq_of_le_of_card_ge (inf_le_left : V ≤ W₁) (by rw [hj, h.card_W₁]; norm_num)
  exact this ▸ inf_le_right

theorem eq_one (h : Hyp Mb L₁ L₂ W₁ W₂ τ) (hR : RHyp Mb L₁ L₂ R) {c : MulAut W}
    (hc : c ∈ CM Mb L₁ L₂) {k : ℕ} (hck : c ^ 2 ^ k = 1) (hcR : ∀ r ∈ R, c * r = r * c) :
    c = 1 :=
  h.eq_one_of_fix (fun w hw => mem_fixV_zp.1 (fix_W₁_of h hR hc hck hcR hw))
    (fun w hw => mem_fixV_zp.1 (fix_W₁_of h.swap hR.swap (by rw [CM_comm]; exact hc) hck hcR hw))

end RHyp

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
