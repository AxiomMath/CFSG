module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5AutDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem zmod5_eq_one_of_odd_pow151b {x : ZMod 5} {n : ℕ} (hn : Odd n) (h : x ^ n = 1) :
    x = 1 := by
  have key : ∀ y : ZMod 5, y ≠ 0 → y ^ 3 = 1 → y = 1 := by decide
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨m, rfl⟩ := hn
  rcases eq_or_ne x 0 with rfl | hx
  · simp at h
  · have h4 : x ^ 4 = 1 := by simpa using ZMod.pow_card_sub_one_eq_one hx
    have h1 : x ^ (2 * m + 1) = x ^ (2 * (m % 2) + 1) := by
      conv_lhs => rw [← Nat.div_add_mod m 2]
      rw [show 2 * (2 * (m / 2) + m % 2) + 1 = 4 * (m / 2) + (2 * (m % 2) + 1) by ring, pow_add,
        pow_mul, h4, one_pow, one_mul]
    rw [h1] at h
    rcases Nat.mod_two_eq_zero_or_one m with h2 | h2
    · simpa [h2] using h
    · rw [h2] at h
      exact key x hx h

theorem commute_of_conj_odd_five151b {Γ : Type*} [Group Γ] {a g : Γ} (ha : orderOf a = 5)
    (h : g * a * g⁻¹ ∈ Subgroup.zpowers a) (hodd : Odd (orderOf g)) : g * a = a * g := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have hpow : ∀ m : ℕ, g ^ m * a * (g ^ m)⁻¹ = a ^ (k ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e : g ^ (m + 1) * a * (g ^ (m + 1))⁻¹ = g * (g ^ m * a * (g ^ m)⁻¹) * g⁻¹ := by group
      rw [e, ih, ← conj_zpow, ← hk, ← zpow_mul, pow_succ']
  have h1 : a ^ (1 : ℤ) = a ^ (k ^ orderOf g) := by
    rw [← hpow, pow_orderOf_eq_one, one_mul, inv_one, mul_one, zpow_one]
  have h2 : (1 : ℤ) ≡ k ^ orderOf g [ZMOD (orderOf a : ℤ)] := zpow_eq_zpow_iff_modEq.mp h1
  rw [ha] at h2
  have h3 : (1 : ZMod 5) = (k : ZMod 5) ^ orderOf g := by
    have := (ZMod.intCast_eq_intCast_iff 1 (k ^ orderOf g) 5).mpr h2
    simpa using this
  have h4 : (k : ZMod 5) = 1 := zmod5_eq_one_of_odd_pow151b hodd h3.symm
  have h5 : a ^ k = a ^ (1 : ℤ) := by
    refine zpow_eq_zpow_iff_modEq.mpr ?_
    rw [ha]
    exact (ZMod.intCast_eq_intCast_iff k 1 5).mp (by simpa using h4)
  rw [zpow_one] at h5
  have h6 : g * a * g⁻¹ = a := by rw [← hk]; exact h5
  exact mul_inv_eq_iff_eq_mul.mp h6

theorem exists_elemAbelian_nine_of_commute151b {Γ : Type*} [Group Γ] {Mb : Subgroup Γ} {c d : Γ}
    (hc : c ∈ Mb) (hd : d ∈ Mb) (hcd : c * d = d * c) (hc3 : orderOf c = 3) (hd3 : orderOf d = 3)
    (hinf : ∀ x ∈ Subgroup.zpowers c, x ∈ Subgroup.zpowers d → x = 1) :
    ∃ E : Subgroup Γ, E ≤ Mb ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Subgroup.zpowers d, Commute x y := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_zpow (show Commute c d from hcd) m n
  have hcc : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Subgroup.zpowers c, Commute x y := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_zpow_self c m n
  have hdd : ∀ x ∈ Subgroup.zpowers d, ∀ y ∈ Subgroup.zpowers d, Commute x y := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_zpow_self d m n
  have hc3' : ∀ x ∈ Subgroup.zpowers c, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [← hc3, pow_orderOf_eq_one]
  have hd3' : ∀ x ∈ Subgroup.zpowers d, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [← hd3, pow_orderOf_eq_one]
  let μ : Subgroup.zpowers c × Subgroup.zpowers d →* Γ :=
    MonoidHom.noncommCoprod (Subgroup.zpowers c).subtype (Subgroup.zpowers d).subtype
      fun x y => hcomm x x.2 y y.2
  have hμ : ∀ p : Subgroup.zpowers c × Subgroup.zpowers d, μ p = (p.1 : Γ) * p.2 := fun _ => rfl
  have hinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    rw [hμ, mul_eq_one_iff_eq_inv] at hp
    have h1 : (p.1 : Γ) = 1 := hinf _ p.1.2 (by rw [hp]; exact Subgroup.inv_mem _ p.2.2)
    have h2 : (p.2 : Γ) = 1 := by
      rw [h1] at hp
      exact inv_eq_one.mp hp.symm
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  refine ⟨μ.range, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩, ?_⟩
  · rintro _ ⟨p, rfl⟩
    rw [hμ]
    exact Mb.mul_mem (Subgroup.zpowers_le.mpr hc p.1.2) (Subgroup.zpowers_le.mpr hd p.2.2)
  · obtain ⟨p, hp⟩ := a.2
    obtain ⟨q, hq⟩ := b.2
    apply Subtype.ext
    show (a : Γ) * b = b * a
    rw [← hp, ← hq, hμ, hμ]
    exact (((hcc _ p.1.2 _ q.1.2).mul_right (hcomm _ p.1.2 _ q.2.2)).mul_left
      ((hcomm _ q.1.2 _ p.2.2).symm.mul_right (hdd _ p.2.2 _ q.2.2))).eq
  · obtain ⟨p, hp⟩ := ha
    rw [← hp, hμ, (hcomm _ p.1.2 _ p.2.2).mul_pow, hc3' _ p.1.2, hd3' _ p.2.2, one_mul]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod,
      Nat.card_zpowers, Nat.card_zpowers, hc3, hd3]

namespace SixData151b

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

theorem exists_fixed_W₁ (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {P : Subgroup (MulAut W)} (hP : IsPGroup 2 P) (hPs : ∀ g ∈ P, S.Stab₁ g) :
    ∃ z ∈ S.W₁, z ≠ 1 ∧ ∀ g ∈ P, g z = z := by
  have _ := hW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := card_modEq_card_inf_fixV151b (U := S.W₁) hP fun g hg u hu => (hPs g hg u).1 hu
  rw [S.card_W₁ hcard] at hmod
  have hne : S.W₁ ⊓ fixV P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hmod
    exact absurd hmod (by decide)
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨z, hz.1, fun e => hz1 (Subtype.ext e), fun g hg => hz.2 g hg⟩

theorem fix_W₁_of_commute (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256) {g : MulAut W}
    (hg : g * S.a₁ = S.a₁ * g) {z : W} (hz : z ∈ S.W₁) (hz1 : z ≠ 1) (hfix : g z = z) :
    ∀ w ∈ S.W₁, g w = w := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨s11, -, -, -⟩ := six_module151b S.comm S.winf
  set U : Subgroup W := S.W₁ ⊓ fixV (Subgroup.zpowers g) with hU
  have hzU : z ∈ U := ⟨hz, mem_fixV_zpowers_iff.mpr hfix⟩
  have hUinv : ∀ u ∈ U, S.a₁ u ∈ U := by
    intro u hu
    refine ⟨s11 _ S.a₁_mem u hu.1, mem_fixV_zpowers_iff.mpr ?_⟩
    have hgu : g u = u := mem_fixV_zpowers_iff.mp hu.2
    calc g (S.a₁ u) = (g * S.a₁) u := rfl
      _ = (S.a₁ * g) u := by rw [hg]
      _ = S.a₁ (g u) := rfl
      _ = S.a₁ u := by rw [hgu]
  have hmod := card_modEq_card_inf_fixV151b (U := U)
    (isPGroup_zpowers_of_pow_eq_one151b (S.a₁_pow (Or.inr rfl))) (invariant_zpowers151b hUinv)
  have h1 : Nat.card ↥(U ⊓ fixV (Subgroup.zpowers S.a₁)) = 1 := by
    refine Subgroup.card_eq_one.mpr (eq_bot_iff.mpr fun x hx => ?_)
    have : x ∈ S.W₁ ⊓ fixV (Subgroup.zpowers S.a₁) := ⟨hx.1.1, hx.2⟩
    rw [S.fixV_inf_a₁ (Or.inr rfl) hW] at this
    exact this
  rw [h1] at hmod
  have hUle : U ≤ S.W₁ := inf_le_left
  have hdvd : Nat.card U ∣ 16 := S.card_W₁ hcard ▸ Subgroup.card_dvd_of_le hUle
  have hne : Nat.card U ≠ 1 := by
    intro h
    have := Subgroup.card_eq_one.mp h
    exact hz1 (Subgroup.mem_bot.mp (this ▸ hzU))
  have h16 : Nat.card U = 16 := by
    have hle : Nat.card U ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card U = n at hmod hdvd hne hle
    interval_cases n <;> simp_all [Nat.ModEq]
  have hUW : U = S.W₁ := Subgroup.eq_of_le_of_card_ge hUle (by rw [h16, S.card_W₁ hcard])
  intro w hw
  exact mem_fixV_zpowers_iff.mp (hUW ▸ hw : w ∈ U).2

omit [Finite W] in
theorem swap_inv_mem_W₂ {g : MulAut W} (hg : S.Swap₁₂ g) {w : W} (hw : w ∈ S.W₂) :
    g⁻¹ w ∈ S.W₁ := by
  have hx : g⁻¹ w ∈ S.W₁ ⊔ S.W₂ := by rw [S.wsup]; exact Subgroup.mem_top _
  obtain ⟨u, hu, v, hv, huv⟩ := Subgroup.mem_sup.mp hx
  have h1 : g u * g v = w := by
    rw [← map_mul, huv]; exact MulAut.apply_inv_self W g w
  have h2 : g v ∈ S.W₁ ⊓ S.W₂ := by
    refine ⟨hg.2 v hv, ?_⟩
    have : g v = (g u)⁻¹ * w := by rw [← h1]; group
    rw [this]
    exact S.W₂.mul_mem (S.W₂.inv_mem (hg.1 u hu)) hw
  rw [S.winf, Subgroup.mem_bot] at h2
  have hv1 : v = 1 := g.injective (h2.trans (map_one g).symm)
  rw [← huv, hv1, mul_one]
  exact hu

omit [Finite W] in
theorem eq_one_of_fix_W₁_W₂ {x : MulAut W} (h₁ : ∀ w ∈ S.W₁, x w = w)
    (h₂ : ∀ w ∈ S.W₂, x w = w) : x = 1 := by
  refine MulEquiv.ext fun w => ?_
  have hw : w ∈ S.W₁ ⊔ S.W₂ := by rw [S.wsup]; exact Subgroup.mem_top _
  obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.mp hw
  show x (u * v) = u * v
  rw [map_mul, h₁ u hu, h₂ v hv]

omit [Finite W] in
theorem commute_of_fix_W₁_W₂ {x y : MulAut W} (hx₁ : ∀ w ∈ S.W₁, x w = w)
    (hx₂ : ∀ w ∈ S.W₂, x w ∈ S.W₂) (hy₂ : ∀ w ∈ S.W₂, y w = w)
    (hy₁ : ∀ w ∈ S.W₁, y w ∈ S.W₁) : x * y = y * x := by
  refine MulEquiv.ext fun w => ?_
  have hw : w ∈ S.W₁ ⊔ S.W₂ := by rw [S.wsup]; exact Subgroup.mem_top _
  obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.mp hw
  show x (y (u * v)) = y (x (u * v))
  rw [map_mul, map_mul, map_mul, map_mul, hx₁ u hu, hy₂ v hv, hx₁ _ (hy₁ u hu), hy₂ _ (hx₂ v hv)]

end SixData151b

end CFSG.Quasithin
