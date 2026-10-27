module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.EmptyFaithful.S153Q4Aa

public section

namespace CFSG.Quasithin.H13.L32A.HeisMod

open CFSG.Quasithin CFSG.Quasithin.S153Q CFSG.Quasithin.S153Q.Q4A

variable {W : Type} [CommGroup W]

section Weights

@[expose] def wt (a c : MulAut W) (j : ℕ) : Subgroup W where
  carrier := {w | a w = (c ^ j) w}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_mul, map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [map_inv, map_inv, hx]

theorem mem_wt {a c : MulAut W} {j : ℕ} {w : W} : w ∈ wt a c j ↔ a w = (c ^ j) w := Iff.rfl

theorem pow_mod_three {c : MulAut W} (hc3 : c ^ 3 = 1) (n : ℕ) : c ^ n = c ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hc3, one_pow, one_mul]

theorem wt_mod {a c : MulAut W} (hc3 : c ^ 3 = 1) (j : ℕ) : wt a c j = wt a c (j % 3) := by
  ext w
  rw [mem_wt, mem_wt, pow_mod_three hc3 j]

theorem pow_apply_comm {a c : MulAut W} (hac : a * c = c * a) (n : ℕ) (w : W) :
    a ((c ^ n) w) = (c ^ n) (a w) := by
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, (Commute.pow_right (show Commute a c from hac) n).eq]

theorem orbit_prod {c : MulAut W} (hc3 : c ^ 3 = 1) (hfpf : ∀ w : W, c w = w → w = 1) (w : W) :
    w * c w * c (c w) = 1 := by
  apply hfpf
  rw [map_mul, map_mul, z_cube_apply hc3 w]
  rw [mul_comm (c w * c (c w)) w, mul_assoc]

@[expose] def proj (a c : MulAut W) (j : ℕ) (w : W) : W :=
  w * (c ^ (2 * j)) (a w) * (c ^ j) (a (a w))

theorem proj_mul (a c : MulAut W) (j : ℕ) (x y : W) :
    proj a c j (x * y) = proj a c j x * proj a c j y := by
  simp only [proj, map_mul]
  ac_rfl

theorem pow_pow_apply (c : MulAut W) (m n : ℕ) (w : W) :
    (c ^ m) ((c ^ n) w) = (c ^ (m + n)) w := by
  rw [← MulAut.mul_apply, ← pow_add]

theorem comm_apply {f g : MulAut W} (h : f * g = g * f) (w : W) : f (g w) = g (f w) := by
  rw [← MulAut.mul_apply, h, MulAut.mul_apply]

theorem apply_apply_eq {f u : MulAut W} (h : f * f = u) (w : W) : f (f w) = u w := by
  rw [← MulAut.mul_apply, h]

theorem proj_mem {a c : MulAut W} (hc3 : c ^ 3 = 1) (ha3 : a ^ 3 = 1) (hac : a * c = c * a)
    (j : ℕ) (w : W) : proj a c j w ∈ wt a c j := by
  rw [mem_wt, proj, map_mul, map_mul, map_mul, map_mul, pow_apply_comm hac, pow_apply_comm hac,
    z_cube_apply ha3, pow_pow_apply, pow_pow_apply, show j + 2 * j = 3 * j by ring,
    pow_mul c 3 j, hc3, one_pow, MulAut.one_apply, show j + j = 2 * j by ring]
  ac_rfl

theorem proj_prod (hW2 : ∀ w : W, w * w = 1) {a c : MulAut W} (hc3 : c ^ 3 = 1)
    (hfpf : ∀ w : W, c w = w → w = 1) (w : W) :
    proj a c 0 w * proj a c 1 w * proj a c 2 w = w := by
  have h1 := orbit_prod hc3 hfpf (a w)
  have h2 := orbit_prod hc3 hfpf (a (a w))
  have e4 : (c ^ 4) (a w) = c (a w) := by
    rw [pow_mod_three hc3 4]
    simp
  simp only [proj, Nat.mul_zero, pow_zero, MulAut.one_apply, Nat.mul_one, pow_one,
    show 2 * 2 = 4 by norm_num, e4, sq, MulAut.mul_apply]
  calc w * a w * a (a w) * (w * c (c (a w)) * c (a (a w))) * (w * c (a w) * c (c (a (a w))))
      = w * (w * w) * (a w * c (a w) * c (c (a w))) *
          (a (a w) * c (a (a w)) * c (c (a (a w)))) := by ac_rfl
    _ = w := by rw [h1, h2, hW2, mul_one, mul_one, mul_one]

theorem proj_self {a c : MulAut W} (hW2 : ∀ w : W, w * w = 1) (hc3 : c ^ 3 = 1)
    (hac : a * c = c * a) {j : ℕ} {w : W} (hw : w ∈ wt a c j) : proj a c j w = w := by
  rw [mem_wt] at hw
  have haw : a (a w) = (c ^ (2 * j)) w := by
    rw [hw, pow_apply_comm hac, hw, pow_pow_apply, show j + j = 2 * j by ring]
  rw [proj, haw, hw, pow_pow_apply, pow_pow_apply,
    show 2 * j + j = 3 * j by ring, show j + 2 * j = 3 * j by ring, pow_mul c 3 j, hc3, one_pow,
    MulAut.one_apply, hW2, one_mul]

theorem proj_other {a c : MulAut W} (hc3 : c ^ 3 = 1) (hfpf : ∀ w : W, c w = w → w = 1)
    (hac : a * c = c * a) {j k : ℕ} (hj : j < 3) (hk : k < 3) (hjk : j ≠ k) {w : W}
    (hw : w ∈ wt a c j) : proj a c k w = 1 := by
  rw [mem_wt] at hw
  have haw : a (a w) = (c ^ (2 * j)) w := by
    rw [hw, pow_apply_comm hac, hw, pow_pow_apply, show j + j = 2 * j by ring]
  rw [proj, haw, hw, pow_pow_apply, pow_pow_apply,
    pow_mod_three hc3 (2 * k + j), pow_mod_three hc3 (k + 2 * j)]
  have h1 := orbit_prod hc3 hfpf w
  interval_cases j <;> interval_cases k <;> simp_all [sq, MulAut.mul_apply, mul_comm, mul_left_comm]

theorem wt_inf_eq_bot {a c : MulAut W} (hc3 : c ^ 3 = 1) (hfpf : ∀ w : W, c w = w → w = 1)
    {j k : ℕ} (hj : j < 3) (hk : k < 3) (hjk : j ≠ k) : wt a c j ⊓ wt a c k = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun w hw => ?_
  rw [Subgroup.mem_inf, mem_wt, mem_wt] at hw
  have he : (c ^ j) w = (c ^ k) w := hw.1.symm.trans hw.2
  by_contra hw1
  rcases Nat.lt_or_gt_of_ne hjk with hlt | hlt
  · have e : (c ^ (k - j)) w = w := by
      apply (c ^ j).injective
      rw [pow_pow_apply, show j + (k - j) = k by omega, he]
    have := three_dvd_of_zpow hc3 hfpf hw1 e
    omega
  · have e : (c ^ (j - k)) w = w := by
      apply (c ^ k).injective
      rw [pow_pow_apply, show k + (j - k) = j by omega, he]
    have := three_dvd_of_zpow hc3 hfpf hw1 e
    omega

theorem card_eq_prod (hW2 : ∀ w : W, w * w = 1) {a c : MulAut W} (hc3 : c ^ 3 = 1)
    (hfpf : ∀ w : W, c w = w → w = 1) (ha3 : a ^ 3 = 1) (hac : a * c = c * a) :
    Nat.card W = Nat.card (wt a c 0) * Nat.card (wt a c 1) * Nat.card (wt a c 2) := by
  let f : (wt a c 0 × wt a c 1) × wt a c 2 → W := fun p => p.1.1.1 * p.1.2.1 * p.2.1
  have hinj : Function.Injective f := by
    rintro ⟨⟨⟨x₀, hx₀⟩, ⟨x₁, hx₁⟩⟩, ⟨x₂, hx₂⟩⟩ ⟨⟨⟨y₀, hy₀⟩, ⟨y₁, hy₁⟩⟩, ⟨y₂, hy₂⟩⟩ hxy
    simp only [f] at hxy
    have key : ∀ k : ℕ, k < 3 → proj a c k (x₀ * x₁ * x₂) = proj a c k (y₀ * y₁ * y₂) :=
      fun k _ => by rw [hxy]
    have p00 := proj_self hW2 hc3 hac hx₀
    have p11 := proj_self hW2 hc3 hac hx₁
    have p22 := proj_self hW2 hc3 hac hx₂
    have q00 := proj_self hW2 hc3 hac hy₀
    have q11 := proj_self hW2 hc3 hac hy₁
    have q22 := proj_self hW2 hc3 hac hy₂
    have k0 := key 0 (by norm_num)
    have k1 := key 1 (by norm_num)
    have k2 := key 2 (by norm_num)
    simp only [proj_mul] at k0 k1 k2
    rw [p00, proj_other hc3 hfpf hac (by norm_num) (by norm_num) (by norm_num) hx₁,
      proj_other hc3 hfpf hac (by norm_num) (by norm_num) (by norm_num) hx₂, q00,
      proj_other hc3 hfpf hac (by norm_num) (by norm_num) (by norm_num) hy₁,
      proj_other hc3 hfpf hac (by norm_num) (by norm_num) (by norm_num) hy₂] at k0
    rw [p11, proj_other hc3 hfpf hac (by norm_num) (by norm_num) (by norm_num) hx₀,
      proj_other hc3 hfpf hac (by norm_num) (by norm_num) (by norm_num) hx₂, q11,
      proj_other hc3 hfpf hac (by norm_num) (by norm_num) (by norm_num) hy₀,
      proj_other hc3 hfpf hac (by norm_num) (by norm_num) (by norm_num) hy₂] at k1
    rw [p22, proj_other hc3 hfpf hac (by norm_num) (by norm_num) (by norm_num) hx₀,
      proj_other hc3 hfpf hac (by norm_num) (by norm_num) (by norm_num) hx₁, q22,
      proj_other hc3 hfpf hac (by norm_num) (by norm_num) (by norm_num) hy₀,
      proj_other hc3 hfpf hac (by norm_num) (by norm_num) (by norm_num) hy₁] at k2
    simp only [mul_one, one_mul] at k0 k1 k2
    subst k0 k1 k2
    rfl
  have hsurj : Function.Surjective f := fun w =>
    ⟨⟨⟨⟨_, proj_mem hc3 ha3 hac 0 w⟩, ⟨_, proj_mem hc3 ha3 hac 1 w⟩⟩,
      ⟨_, proj_mem hc3 ha3 hac 2 w⟩⟩, proj_prod hW2 hc3 hfpf w⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_prod]

end Weights

section Shift

theorem map_mem_wt_shift {a b c : MulAut W} (hac : a * c = c * a) (hbc : b * c = c * b) {s : ℕ}
    (hab : a * b = b * a * c ^ s) {j : ℕ} {w : W} (hw : w ∈ wt a c j) : b w ∈ wt a c (j + s) := by
  rw [mem_wt] at hw ⊢
  calc a (b w) = (a * b) w := rfl
    _ = (b * a * c ^ s) w := by rw [hab]
    _ = b (a ((c ^ s) w)) := rfl
    _ = b ((c ^ s) ((c ^ j) w)) := by rw [pow_apply_comm hac, hw]
    _ = (c ^ (j + s)) (b w) := by rw [pow_pow_apply, add_comm, pow_apply_comm hbc]

theorem card_wt_le_shift [Finite W] {a b c : MulAut W} (hac : a * c = c * a) (hbc : b * c = c * b)
    {s : ℕ} (hab : a * b = b * a * c ^ s) (j : ℕ) :
    Nat.card (wt a c j) ≤ Nat.card (wt a c (j + s)) :=
  Nat.card_le_card_of_injective (fun w => ⟨b w, map_mem_wt_shift hac hbc hab w.2⟩)
    fun _ _ hxy => Subtype.ext (b.injective (congrArg Subtype.val hxy))

theorem card_wt_eq [Finite W] {a b c : MulAut W} (hc3 : c ^ 3 = 1) (hac : a * c = c * a)
    (hbc : b * c = c * b) {s : ℕ} (hab : a * b = b * a * c ^ s) (hs : s % 3 ≠ 0) :
    Nat.card (wt a c 1) = Nat.card (wt a c 0) ∧ Nat.card (wt a c 2) = Nat.card (wt a c 0) := by
  have key := card_wt_le_shift hac hbc hab
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  rw [wt_mod hc3 (0 + s)] at k0
  rw [wt_mod hc3 (1 + s)] at k1
  rw [wt_mod hc3 (2 + s)] at k2
  have hs' : s % 3 = 1 ∨ s % 3 = 2 := by omega
  rcases hs' with h1 | h2
  · rw [show (0 + s) % 3 = 1 by omega] at k0
    rw [show (1 + s) % 3 = 2 by omega] at k1
    rw [show (2 + s) % 3 = 0 by omega] at k2
    exact ⟨by omega, by omega⟩
  · rw [show (0 + s) % 3 = 2 by omega] at k0
    rw [show (1 + s) % 3 = 0 by omega] at k1
    rw [show (2 + s) % 3 = 1 by omega] at k2
    exact ⟨by omega, by omega⟩

theorem map_mem_wt_inv {a c t : MulAut W} (hc3 : c ^ 3 = 1) (hac : a * c = c * a)
    (ht2 : t * t = 1) (htc : t * c = c * t) {k : ℕ} (hta : t * a * t = a⁻¹ * c ^ k) {j : ℕ}
    {w : W} (hw : w ∈ wt a c j) : t w ∈ wt a c (k + 2 * j) := by
  rw [mem_wt] at hw ⊢
  have hainv : a⁻¹ w = (c ^ (2 * j)) w := by
    apply a.injective
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply, pow_apply_comm hac, hw,
      pow_pow_apply, show 2 * j + j = 3 * j by ring, pow_mul c 3 j, hc3, one_pow,
      MulAut.one_apply]
  have htt : ∀ x : W, t (t x) = x := fun x => by
    rw [← MulAut.mul_apply, ht2, MulAut.one_apply]
  calc a (t w) = t (t (a (t w))) := (htt _).symm
    _ = t ((t * a * t) w) := rfl
    _ = t ((a⁻¹ * c ^ k) w) := by rw [hta]
    _ = t ((c ^ k) (a⁻¹ w)) := by
        rw [MulAut.mul_apply,
          ← pow_apply_comm (a := a⁻¹) (c := c) (Commute.inv_left (show Commute a c from hac)).eq]
    _ = (c ^ (k + 2 * j)) (t w) := by rw [hainv, pow_pow_apply, pow_apply_comm htc]

end Shift

section Tr

@[expose] def trHom (t : MulAut W) : W →* W where
  toFun w := w * t w
  map_one' := by simp
  map_mul' _ _ := by
    simp only [map_mul]
    ac_rfl

theorem trHom_apply (t : MulAut W) (w : W) : trHom t w = w * t w := rfl

theorem mem_ker_trHom (hW2 : ∀ w : W, w * w = 1) {t : MulAut W} {w : W} :
    w ∈ (trHom t).ker ↔ t w = w := by
  rw [MonoidHom.mem_ker, trHom_apply]
  constructor
  · intro h
    have e := congrArg (w * ·) h
    simp only [← mul_assoc, hW2, one_mul, mul_one] at e
    exact e
  · intro h
    rw [h, hW2]

theorem mem_fixV_zpowers {t : MulAut W} {w : W} :
    w ∈ fixV (Subgroup.zpowers t) ↔ t w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem fixV_zpowers_eq_ker (hW2 : ∀ w : W, w * w = 1) (t : MulAut W) :
    fixV (Subgroup.zpowers t) = (trHom t).ker := by
  ext w
  rw [mem_fixV_zpowers, mem_ker_trHom hW2]

theorem commV_zpowers_eq_range (hW2 : ∀ w : W, w * w = 1) {t : MulAut W} (ht2 : t * t = 1) :
    commV (Subgroup.zpowers t) = (trHom t).range := by
  have hinv : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_left (hW2 w)
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have htn : t ^ n = 1 ∨ t ^ n = t := by
      have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht2]
      have e : t ^ n = t ^ (2 * (n / 2) + n % 2) := by
        congr 1
        omega
      rw [e, zpow_add, zpow_mul, h2, one_zpow, one_mul]
      have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases hm with hm | hm
      · left; rw [hm, zpow_zero]
      · right; rw [hm, zpow_one]
    rcases htn with h1 | h1
    · rw [h1, MulAut.one_apply, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [h1, hinv, mul_comm]
      exact ⟨v, rfl⟩
  · rintro _ ⟨v, rfl⟩
    refine Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, v, ?_⟩
    rw [trHom_apply, hinv, mul_comm]

end Tr

section Main

variable [Finite W]

omit [Finite W] in
theorem isPGroup_two (hW2 : ∀ w : W, w * w = 1) : IsPGroup 2 W := fun w =>
  ⟨1, by rw [pow_one, sq]; exact hW2 w⟩

theorem four_le_card (hW2 : ∀ w : W, w * w = 1) {c : MulAut W} (hc3 : c ^ 3 = 1)
    (hfpf : ∀ w : W, c w = w → w = 1) {S : Subgroup W} (hS : ∀ x ∈ S, c x ∈ S) (hne : S ≠ ⊥) :
    4 ≤ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := card_mod_three hc3 hfpf hS
  obtain ⟨n, hn⟩ := ((isPGroup_two hW2).to_subgroup S).exists_card_eq
  have h1 : Nat.card S ≠ 1 := fun h1 => hne (Subgroup.eq_bot_of_card_eq S h1)
  rw [hn] at hmod h1 ⊢
  rcases n with _ | _ | n
  · exact absurd rfl h1
  · norm_num at hmod
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

omit [Finite W] in
theorem wt_invariant {a c : MulAut W} (hac : a * c = c * a) {j : ℕ} {x : W} (hx : x ∈ wt a c j) :
    c x ∈ wt a c j := by
  rw [mem_wt] at hx ⊢
  rw [← MulAut.mul_apply, hac, MulAut.mul_apply, hx, ← MulAut.mul_apply, ← MulAut.mul_apply,
    ← pow_succ', ← pow_succ]

theorem card_wt_le_commV (hW2 : ∀ w : W, w * w = 1) {a c t : MulAut W} (hc3 : c ^ 3 = 1)
    (hfpf : ∀ w : W, c w = w → w = 1) (hac : a * c = c * a) (ht2 : t * t = 1)
    (htc : t * c = c * t) {k : ℕ} (hta : t * a * t = a⁻¹ * c ^ k) :
    Nat.card (wt a c ((2 * k + 1) % 3)) ≤ Nat.card (commV (Subgroup.zpowers t)) := by
  set p := (2 * k + 1) % 3 with hp
  set q := (k + 2 * p) % 3 with hq
  have hpq : p ≠ q := by omega
  have hdisj := wt_inf_eq_bot (a := a) hc3 hfpf (show p < 3 by omega) (show q < 3 by omega) hpq
  rw [commV_zpowers_eq_range hW2 ht2]
  refine Nat.card_le_card_of_injective (fun w => ⟨trHom t w, w, rfl⟩) ?_
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  have e : trHom t x = trHom t y := congrArg Subtype.val hxy
  set u := x * y⁻¹ with hu
  have huwt : u ∈ wt a c p := (wt a c p).mul_mem hx ((wt a c p).inv_mem hy)
  have htu : t u = u := by
    have h1 : u * t u = 1 := by
      rw [hu, map_mul, map_inv]
      calc x * y⁻¹ * (t x * (t y)⁻¹) = (x * t x) * (y * t y)⁻¹ := by
            rw [mul_inv_rev]; ac_rfl
        _ = 1 := by rw [← trHom_apply, ← trHom_apply, e, mul_inv_cancel]
    have e2 := congrArg (u * ·) h1
    simp only [← mul_assoc, hW2, one_mul, mul_one] at e2
    exact e2
  have hu1 : u ∈ wt a c q := by
    rw [← htu, hq, ← wt_mod hc3]
    exact map_mem_wt_inv hc3 hac ht2 htc hta huwt
  have : u = 1 := by
    have hmem : u ∈ wt a c p ⊓ wt a c q := Subgroup.mem_inf.mpr ⟨huwt, hu1⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact hmem
  have hxy' : x = y := by
    rw [hu, mul_inv_eq_one] at this
    exact this
  exact Subtype.ext hxy'

theorem card_eq_sixtyfour (hW2 : ∀ w : W, w * w = 1) {a b c t : MulAut W} (hc3 : c ^ 3 = 1)
    (hfpf : ∀ w : W, c w = w → w = 1) (ha3 : a ^ 3 = 1) (hac : a * c = c * a)
    (hbc : b * c = c * b) {s : ℕ} (hab : a * b = b * a * c ^ s) (hs : s % 3 ≠ 0)
    (ht2 : t * t = 1) (htc : t * c = c * t) {k : ℕ} (hta : t * a * t = a⁻¹ * c ^ k)
    (hne : ∃ w : W, w ≠ 1) (hcomm : Nat.card (commV (Subgroup.zpowers t)) ≤ 4) :
    Nat.card W = 64 ∧ (∀ j, j < 3 → Nat.card (wt a c j) = 4) ∧
      Nat.card (commV (Subgroup.zpowers t)) = 4 := by
  obtain ⟨h1, h2⟩ := card_wt_eq hc3 hac hbc hab hs
  have hcard := card_eq_prod hW2 hc3 hfpf ha3 hac
  rw [h1, h2] at hcard
  have hle := card_wt_le_commV hW2 hc3 hfpf hac ht2 htc hta
  have hp : Nat.card (wt a c ((2 * k + 1) % 3)) = Nat.card (wt a c 0) := by
    have : (2 * k + 1) % 3 = 0 ∨ (2 * k + 1) % 3 = 1 ∨ (2 * k + 1) % 3 = 2 := by omega
    rcases this with h | h | h <;> rw [h] <;> simp [h1, h2]
  rw [hp] at hle
  have hne0 : wt a c 0 ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcard
    obtain ⟨w, hw⟩ := hne
    have : Subsingleton W := Finite.card_le_one_iff_subsingleton.mp (by rw [hcard])
    exact hw (Subsingleton.elim _ _)
  have h4 := four_le_card hW2 hc3 hfpf (fun x hx => wt_invariant hac hx) hne0
  have h0 : Nat.card (wt a c 0) = 4 := by omega
  refine ⟨by rw [hcard, h0], fun j hj => ?_, by omega⟩
  interval_cases j
  · exact h0
  · rw [h1, h0]
  · rw [h2, h0]

omit [Finite W] in
theorem eq_top_of_invariant (hW2 : ∀ w : W, w * w = 1) {a b c : MulAut W} (hc3 : c ^ 3 = 1)
    (hfpf : ∀ w : W, c w = w → w = 1) (ha3 : a ^ 3 = 1) (hac : a * c = c * a)
    (hbc : b * c = c * b) {s : ℕ} (hab : a * b = b * a * c ^ s) (hs : s % 3 ≠ 0)
    (h4 : ∀ j, j < 3 → Nat.card (wt a c j) = 4) {W' : Subgroup W}
    (hW'a : ∀ w ∈ W', a w ∈ W') (hW'b : ∀ w ∈ W', b w ∈ W') (hW'c : ∀ w ∈ W', c w ∈ W')
    (hne : W' ≠ ⊥) : W' = ⊤ := by
  have hpt : ∀ i, i < 3 → IsPt c (wt a c i) := fun i hi =>
    ⟨h4 i hi, fun x hx => wt_invariant hac hx⟩
  have hcn : ∀ n : ℕ, ∀ w ∈ W', (c ^ n) w ∈ W' := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih => intro w hw; rw [pow_succ', MulAut.mul_apply]; exact hW'c _ (ih w hw)
  have hle : ∀ i, i < 3 → ∀ x ∈ wt a c i, x ≠ 1 → x ∈ W' → wt a c i ≤ W' := by
    intro i hi x hx hx1 hxW y hy
    rcases pt_mem_cases hc3 hfpf (hpt i hi) hx hx1 y hy with rfl | rfl | rfl | rfl
    · exact W'.one_mem
    · exact hxW
    · exact hW'c _ hxW
    · exact hW'c _ (hW'c _ hxW)
  have hstep : ∀ i, i < 3 → wt a c i ≤ W' → wt a c ((i + s) % 3) ≤ W' := by
    intro i hi hiW
    obtain ⟨x, hx, hx1⟩ := pt_exists_ne_one (hpt i hi)
    have hbx : b x ∈ wt a c ((i + s) % 3) := by
      rw [← wt_mod hc3]
      exact map_mem_wt_shift hac hbc hab hx
    refine hle _ (Nat.mod_lt _ (by norm_num)) (b x) hbx
      (fun h => hx1 (b.injective (h.trans (map_one b).symm))) (hW'b _ (hiW hx))
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ W', w ≠ 1 := by
    by_contra hno
    push Not at hno
    exact hne ((Subgroup.eq_bot_iff_forall W').mpr hno)
  have hproj : ∀ j, proj a c j w ∈ W' := fun j =>
    W'.mul_mem (W'.mul_mem hw (hcn _ _ (hW'a _ hw))) (hcn _ _ (hW'a _ (hW'a _ hw)))
  obtain ⟨j₀, hj₀, hj₀W⟩ : ∃ j₀, j₀ < 3 ∧ wt a c j₀ ≤ W' := by
    by_contra hno
    push Not at hno
    have hall : ∀ j, j < 3 → proj a c j w = 1 := by
      intro j hj
      by_contra h1
      exact hno j hj (hle j hj _ (proj_mem hc3 ha3 hac j w) h1 (hproj j))
    apply hw1
    rw [← proj_prod hW2 hc3 hfpf (a := a) w, hall 0 (by norm_num), hall 1 (by norm_num),
      hall 2 (by norm_num), mul_one, mul_one]
  have hj₁ := hstep j₀ hj₀ hj₀W
  have hj₂ := hstep _ (Nat.mod_lt _ (by norm_num)) hj₁
  have e1 : (j₀ + s) % 3 = (j₀ + s % 3) % 3 := by omega
  have e2 : ((j₀ + s) % 3 + s) % 3 = (j₀ + 2 * (s % 3)) % 3 := by omega
  rw [e1] at hj₁
  rw [e2] at hj₂
  have hall : ∀ i, i < 3 → wt a c i ≤ W' := by
    intro i hi
    have hs' : s % 3 = 1 ∨ s % 3 = 2 := by omega
    rcases hs' with hr | hr <;> rw [hr] at hj₁ hj₂ <;> interval_cases j₀ <;> interval_cases i <;>
      norm_num at hj₁ hj₂ ⊢ <;> assumption
  refine eq_top_iff.mpr fun v _ => ?_
  rw [← proj_prod hW2 hc3 hfpf (a := a) v]
  exact W'.mul_mem (W'.mul_mem (hall 0 (by norm_num) (proj_mem hc3 ha3 hac 0 v))
    (hall 1 (by norm_num) (proj_mem hc3 ha3 hac 1 v)))
    (hall 2 (by norm_num) (proj_mem hc3 ha3 hac 2 v))

omit [Finite W] in
theorem commV_le_fixV (hW2 : ∀ w : W, w * w = 1) {t : MulAut W} (ht2 : t * t = 1) :
    commV (Subgroup.zpowers t) ≤ fixV (Subgroup.zpowers t) := by
  rw [commV_zpowers_eq_range hW2 ht2]
  rintro _ ⟨w, rfl⟩
  rw [mem_fixV_zpowers, trHom_apply, map_mul, apply_apply_eq ht2, MulAut.one_apply, mul_comm]

omit [Finite W] in
theorem card_fixV_t (hW2 : ∀ w : W, w * w = 1) {t : MulAut W} (ht2 : t * t = 1)
    (hcard : Nat.card W = 64) (hcomm : Nat.card (commV (Subgroup.zpowers t)) = 4) :
    Nat.card (fixV (Subgroup.zpowers t)) = 16 := by
  have h := Subgroup.card_ker_mul_card_range (trHom t)
  rw [← fixV_zpowers_eq_ker hW2, ← commV_zpowers_eq_range hW2 ht2, hcomm, hcard] at h
  omega

theorem fixV_eq_commV (hW2 : ∀ w : W, w * w = 1) {c t y : MulAut W} (hc3 : c ^ 3 = 1)
    (hfpf : ∀ w : W, c w = w → w = 1) (htc : t * c = c * t) (hyc : y * c = c * y)
    (hyt : y * y = t) (ht2 : t * t = 1) (hcard : Nat.card W = 64)
    (hcomm : Nat.card (commV (Subgroup.zpowers t)) = 4) :
    fixV (Subgroup.zpowers y) = commV (Subgroup.zpowers t) := by
  set D := commV (Subgroup.zpowers t) with hD
  have hDr : D = (trHom t).range := commV_zpowers_eq_range hW2 ht2
  have hDc : ∀ x ∈ D, c x ∈ D := by
    rw [hDr]
    rintro _ ⟨w, rfl⟩
    refine ⟨c w, ?_⟩
    rw [trHom_apply, trHom_apply, map_mul, comm_apply htc]
  have hyt' : y * t = t * y := by rw [← hyt, mul_assoc]
  have hDy : ∀ x ∈ D, y x ∈ D := by
    rw [hDr]
    rintro _ ⟨w, rfl⟩
    refine ⟨y w, ?_⟩
    rw [trHom_apply, trHom_apply, map_mul, comm_apply hyt']
  have hy4 : y ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, sq, hyt, ht2]
  have hDfix : D ≤ fixV (Subgroup.zpowers y) := by
    intro x hx
    rw [mem_fixV_zpowers]
    exact fix_of_stable hc3 hfpf hyc ⟨hcomm, hDc⟩ hDy (m := 4) (by norm_num) hy4 x hx
  set F := fixV (Subgroup.zpowers y) with hF
  have hFker : F = (trHom y).ker := fixV_zpowers_eq_ker hW2 y
  have hFt : F ≤ fixV (Subgroup.zpowers t) := by
    intro x hx
    rw [hF, mem_fixV_zpowers] at hx
    rw [mem_fixV_zpowers, ← hyt, MulAut.mul_apply, hx, hx]
  have hFc : ∀ x ∈ F, c x ∈ F := by
    intro x hx
    rw [hF, mem_fixV_zpowers] at hx ⊢
    rw [comm_apply hyc, hx]
  have h16 := card_fixV_t hW2 ht2 hcard hcomm
  have hdvd : Nat.card F ∣ 16 := h16 ▸ Subgroup.card_dvd_of_le hFt
  have hmod : Nat.card F % 3 = 1 := card_mod_three hc3 hfpf hFc
  have hF4 : 4 ≤ Nat.card F := hcomm ▸ Subgroup.card_le_of_le hDfix
  have hne16 : Nat.card F ≠ 16 := by
    intro hF16
    have hFeq : F = fixV (Subgroup.zpowers t) :=
      Subgroup.eq_of_le_of_card_ge hFt (by rw [h16, hF16])
    have hry := Subgroup.card_ker_mul_card_range (trHom y)
    rw [← hFker, hF16, hcard] at hry
    have hr4 : Nat.card (trHom y).range = 4 := by omega
    have hsub : D ≤ (trHom y).range := by
      rw [hDr]
      rintro _ ⟨w, rfl⟩
      refine ⟨trHom y w, ?_⟩
      rw [trHom_apply, trHom_apply, trHom_apply, map_mul, apply_apply_eq hyt]
      calc w * y w * (y w * t w) = w * (y w * y w) * t w := by ac_rfl
        _ = w * t w := by rw [hW2, mul_one]
    have hDeq : D = (trHom y).range :=
      Subgroup.eq_of_le_of_card_ge hsub (by rw [hr4, hcomm])
    have hall : ∀ w : W, trHom t w = 1 := by
      intro w
      have hmemD : trHom y w ∈ D := by rw [hDeq]; exact ⟨w, rfl⟩
      have h1 : trHom y w ∈ F := by rw [hFeq]; exact commV_le_fixV hW2 ht2 hmemD
      have h2 : trHom y (trHom y w) = 1 := by rw [hFker] at h1; exact h1
      rw [trHom_apply, trHom_apply, map_mul, apply_apply_eq hyt] at h2
      rw [trHom_apply]
      calc w * t w = w * y w * (y w * t w) := by
            calc w * t w = w * (y w * y w) * t w := by rw [hW2, mul_one]
              _ = w * y w * (y w * t w) := by ac_rfl
        _ = 1 := h2
    have hbot : D = ⊥ := by
      rw [hDr, eq_bot_iff]
      rintro _ ⟨w, rfl⟩
      exact (Subgroup.mem_bot).mpr (hall w)
    rw [hbot, Subgroup.card_bot] at hcomm
    norm_num at hcomm
  have hle16 : Nat.card F ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
  have hF4' : Nat.card F = 4 := by
    interval_cases hn : Nat.card F <;> omega
  exact (Subgroup.eq_of_le_of_card_ge hDfix (by rw [hF4', hcomm])).symm

end Main

end CFSG.Quasithin.H13.L32A.HeisMod
