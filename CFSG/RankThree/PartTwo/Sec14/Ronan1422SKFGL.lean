module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SKFBase
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm

theorem sign_c2_six : sign (c2 6) = 1 := by decide +kernel

@[expose] def hConjPerm : Perm (Fin 6) := swap 0 5 * swap 5 2 * swap 2 3 * swap 1 4

theorem sign_hConjPerm : sign hConjPerm = 1 := by decide +kernel

theorem hConjPerm_conj : hConjPerm * (c1 6 * c2 6) * hConjPerm⁻¹ = c1 6 * c2 6 ^ 2 := by
  decide +kernel

theorem k2Perm_conj : k2Perm * c1 6 * k2Perm⁻¹ = c2 6 := by decide +kernel

@[expose] def s34 : Perm (Fin 6) := swap 3 4

theorem s34_conj_c1 : s34 * c1 6 * s34⁻¹ = c1 6 := by decide +kernel

theorem s34_conj_c2_sq : s34 * c2 6 ^ 2 * s34⁻¹ = c2 6 := by decide +kernel

theorem c1c2_comm : c1 6 * c2 6 = c2 6 * c1 6 := by decide +kernel

theorem c1_pow_three : c1 6 ^ 3 = 1 := by decide +kernel

theorem c2_pow_three : c2 6 ^ 3 = 1 := by decide +kernel

theorem c1c2_pow_three : (c1 6 * c2 6) ^ 3 = 1 := by decide +kernel

theorem c1c2sq_pow_three : (c1 6 * c2 6 ^ 2) ^ 3 = 1 := by decide +kernel

theorem c1_ne_c2 : c1 6 ≠ c2 6 := by decide +kernel

theorem c2_ne_c1_sq : c2 6 ≠ c1 6 ^ 2 := by decide +kernel

theorem c1c2_ne_one : c1 6 * c2 6 ≠ 1 := by decide +kernel

theorem three_pw_perm : ∀ i j : Fin 3,
    (c1 6 ^ (i : ℕ) * c2 6 ^ (j : ℕ)).support.card = 3 ↔
      ((i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0)) := by
  decide +kernel

theorem pw_inj_perm : ∀ i j i' j' : Fin 3,
    c1 6 ^ (i : ℕ) * c2 6 ^ (j : ℕ) = c1 6 ^ (i' : ℕ) * c2 6 ^ (j' : ℕ) → i = i' ∧ j = j' := by
  decide +kernel

theorem pw21_perm :
    c1 6 ^ ((2 : Fin 3) : ℕ) * c2 6 ^ ((1 : Fin 3) : ℕ) = (c1 6 * c2 6 ^ 2) ^ 2 := by
  decide +kernel

theorem pw22_perm :
    c1 6 ^ ((2 : Fin 3) : ℕ) * c2 6 ^ ((2 : Fin 3) : ℕ) = (c1 6 * c2 6) ^ 2 := by
  decide +kernel

theorem three_pw_cases : ∀ i j : Fin 3, ((i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0)) →
    (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 0) := by
  decide

theorem three_pw_other : ∀ i j : Fin 3, i ≠ 0 → j ≠ 0 →
    (i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨ (i = 2 ∧ j = 2) := by
  decide

theorem three_pw_nonzero : ∀ i j : Fin 3,
    ¬((i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0)) → ¬(i = 0 ∧ j = 0) → i ≠ 0 ∧ j ≠ 0 := by
  decide

@[expose] def ca : alternatingGroup (Fin 6) := alt6 (c1 6) sign_c1_six

@[expose] def cb : alternatingGroup (Fin 6) := alt6 (c2 6) sign_c2_six

@[expose] def hA6 : alternatingGroup (Fin 6) := alt6 hConjPerm sign_hConjPerm

@[expose] def kA6 : alternatingGroup (Fin 6) := alt6 k2Perm signs_six.2.1

@[simp] theorem coe_ca : (ca : Perm (Fin 6)) = c1 6 := rfl

@[simp] theorem coe_cb : (cb : Perm (Fin 6)) = c2 6 := rfl

theorem ca_ne_one : ca ≠ 1 := fun h => c1_six_ne_one (congrArg Subtype.val h)

theorem ca_mem_F06 : ca ∈ F06 := c1_mem_F06 sign_c1_six

theorem cb_mem_F06 : cb ∈ F06 := mem_F06.mpr ⟨![0, 1], f0Facts_six.e2⟩

theorem ca_pow_three : ca ^ 3 = 1 := Subtype.ext c1_pow_three

theorem cb_pow_three : cb ^ 3 = 1 := Subtype.ext c2_pow_three

theorem cc_pow_three : (ca * cb) ^ 3 = 1 := Subtype.ext c1c2_pow_three

theorem cc_ne_one : ca * cb ≠ 1 := fun h => c1c2_ne_one (congrArg Subtype.val h)

theorem cd_pow_three : (ca * cb ^ 2) ^ 3 = 1 := Subtype.ext c1c2sq_pow_three

theorem kA6_conj : kA6 * ca * kA6⁻¹ = cb := Subtype.ext k2Perm_conj

theorem hA6_conj : hA6 * (ca * cb) * hA6⁻¹ = ca * cb ^ 2 := Subtype.ext hConjPerm_conj

@[expose] def pw (i j : Fin 3) : alternatingGroup (Fin 6) := ca ^ (i : ℕ) * cb ^ (j : ℕ)

theorem coe_pw (i j : Fin 3) :
    ((pw i j : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      c1 6 ^ (i : ℕ) * c2 6 ^ (j : ℕ) := by
  simp [pw]

theorem pw_mem_F06 (i j : Fin 3) : pw i j ∈ F06 :=
  mul_mem (pow_mem ca_mem_F06 _) (pow_mem cb_mem_F06 _)

theorem exists_pw {u : alternatingGroup (Fin 6)} (hu : u ∈ F06) :
    ∃ i j : Fin 3, u = pw i j := by
  obtain ⟨v, hv⟩ := mem_F06.mp hu
  refine ⟨⟨(v 0).val, ZMod.val_lt _⟩, ⟨(v 1).val, ZMod.val_lt _⟩, Subtype.ext ?_⟩
  rw [coe_pw]
  exact hv.symm

theorem pw_zero_zero : pw 0 0 = 1 := by simp [pw]

theorem pw_zero_one : pw 0 1 = cb := by simp [pw]

theorem pw_zero_two : pw 0 2 = cb ^ 2 := by simp [pw]

theorem pw_one_zero : pw 1 0 = ca := by simp [pw]

theorem pw_one_one : pw 1 1 = ca * cb := by simp [pw]

theorem pw_one_two : pw 1 2 = ca * cb ^ 2 := by simp [pw]

theorem pw_two_zero : pw 2 0 = ca ^ 2 := by simp [pw]

theorem pw_two_one : pw 2 1 = (ca * cb ^ 2) ^ 2 :=
  Subtype.ext (by rw [coe_pw]; exact pw21_perm)

theorem pw_two_two : pw 2 2 = (ca * cb) ^ 2 :=
  Subtype.ext (by rw [coe_pw]; exact pw22_perm)

theorem three_pw_iff (i j : Fin 3) :
    IsThreeCycle ((pw i j : alternatingGroup (Fin 6)) : Perm (Fin 6)) ↔
      ((i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0)) := by
  rw [coe_pw, ← card_support_eq_three_iff]
  exact three_pw_perm i j

@[expose] def conjA6 (σ : Perm (Fin 6)) : MulAut (alternatingGroup (Fin 6)) where
  toFun w := ⟨σ * (w : Perm (Fin 6)) * σ⁻¹,
    (alternatingGroup.normal : (alternatingGroup (Fin 6)).Normal).conj_mem _ w.2 σ⟩
  invFun w := ⟨σ⁻¹ * (w : Perm (Fin 6)) * σ,
    (alternatingGroup.normal : (alternatingGroup (Fin 6)).Normal).conj_mem _ w.2 σ⁻¹⟩
  left_inv w := Subtype.ext (by simp [mul_assoc])
  right_inv w := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conj_of_fix_ca_cb (γ : MulAut (alternatingGroup (Fin 6))) (ha : γ ca = ca)
    (hb : γ cb = cb) :
    ∃ b₀ : alternatingGroup (Fin 6), ∀ w : alternatingGroup (Fin 6),
      ((γ w : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
        (b₀ : Perm (Fin 6)) * (w : Perm (Fin 6)) * (b₀ : Perm (Fin 6))⁻¹ := by
  have hfix : ∀ f ∈ F06, γ f = f := by
    intro f hf
    obtain ⟨i, j, rfl⟩ := exists_pw hf
    rw [pw, map_mul, map_pow, map_pow, ha, hb]
  obtain ⟨b₀, -, hγ⟩ := exists_mem_F06_eq_conj_of_fix γ hfix
  refine ⟨b₀, fun w => ?_⟩
  subst hγ
  rfl

theorem isS6_of_threeCycle (β : MulAut (alternatingGroup (Fin 6)))
    (hβ : ∀ w : alternatingGroup (Fin 6), IsThreeCycle (w : Perm (Fin 6)) →
      IsThreeCycle ((β w : alternatingGroup (Fin 6)) : Perm (Fin 6))) :
    ∃ σ : Perm (Fin 6), ∀ w : alternatingGroup (Fin 6),
      ((β w : alternatingGroup (Fin 6)) : Perm (Fin 6)) = σ * (w : Perm (Fin 6)) * σ⁻¹ := by
  have hca3 : IsThreeCycle (c1 6) := card_support_eq_three_iff.mp (by decide +kernel)
  have hcb3 : IsThreeCycle (c2 6) := card_support_eq_three_iff.mp (by decide +kernel)
  have h1 : (c1 6).cycleType = {3} := hca3
  have h2 : ((β ca : alternatingGroup (Fin 6)) : Perm (Fin 6)).cycleType = {3} := hβ ca hca3
  obtain ⟨σ₁, hσ₁⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr (h1.trans h2.symm))
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ : MulAut (alternatingGroup (Fin 6)), γ = conjA6 σ₁⁻¹ * β :=
    ⟨_, rfl⟩
  have hγ₁_apply : ∀ w : alternatingGroup (Fin 6),
      ((γ₁ w : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
        σ₁⁻¹ * ((β w : alternatingGroup (Fin 6)) : Perm (Fin 6)) * σ₁⁻¹⁻¹ := by
    intro w
    subst hγ₁
    rfl
  have hβ_apply : ∀ w : alternatingGroup (Fin 6),
      ((β w : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
        σ₁ * ((γ₁ w : alternatingGroup (Fin 6)) : Perm (Fin 6)) * σ₁⁻¹ := by
    intro w
    rw [hγ₁_apply]
    group
  have hγ₁a : γ₁ ca = ca := by
    apply Subtype.ext
    show ((γ₁ ca : alternatingGroup (Fin 6)) : Perm (Fin 6)) = c1 6
    rw [hγ₁_apply, ← hσ₁]
    group
  have hγ₁3 : ∀ w : alternatingGroup (Fin 6), IsThreeCycle (w : Perm (Fin 6)) →
      IsThreeCycle ((γ₁ w : alternatingGroup (Fin 6)) : Perm (Fin 6)) := by
    intro w hw
    have hb := hβ w hw
    unfold IsThreeCycle at hb ⊢
    rw [hγ₁_apply, cycleType_conj]
    exact hb
  have hcomm : ca * γ₁ cb = γ₁ cb * ca := by
    have h : γ₁ (ca * cb) = γ₁ (cb * ca) := by
      rw [show ca * cb = cb * ca from Subtype.ext c1c2_comm]
    rwa [map_mul, map_mul, hγ₁a] at h
  have hmemF : γ₁ cb ∈ F06 :=
    centralizer_le_F06 ca_mem_F06 ca_ne_one (mem_centralizer_singleton_iff.mpr hcomm.symm)
  obtain ⟨i, j, hij⟩ := exists_pw hmemF
  have hcyc : IsThreeCycle ((pw i j : alternatingGroup (Fin 6)) : Perm (Fin 6)) := by
    rw [← hij]
    exact hγ₁3 cb hcb3
  have hcb_cases : γ₁ cb = cb ∨ γ₁ cb = cb ^ 2 := by
    rcases three_pw_cases i j ((three_pw_iff i j).mp hcyc) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left
      rw [hij, pw_zero_one]
    · right
      rw [hij, pw_zero_two]
    · exfalso
      have e : γ₁ cb = γ₁ ca := by
        rw [hγ₁a, hij, pw_one_zero]
      exact c1_ne_c2 (congrArg Subtype.val ((MulEquiv.injective γ₁) e)).symm
    · exfalso
      have e : γ₁ cb = γ₁ (ca ^ 2) := by
        rw [map_pow, hγ₁a, hij, pw_two_zero]
      exact c2_ne_c1_sq (congrArg Subtype.val ((MulEquiv.injective γ₁) e))
  rcases hcb_cases with hA | hB
  · obtain ⟨b₀, hb₀⟩ := conj_of_fix_ca_cb γ₁ hγ₁a hA
    refine ⟨σ₁ * (b₀ : Perm (Fin 6)), fun w => ?_⟩
    rw [hβ_apply w, hb₀ w]
    group
  ·
    obtain ⟨γ₂, hγ₂⟩ : ∃ γ : MulAut (alternatingGroup (Fin 6)), γ = conjA6 s34 * γ₁ :=
      ⟨_, rfl⟩
    have hγ₂_apply : ∀ w : alternatingGroup (Fin 6),
        ((γ₂ w : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
          s34 * ((γ₁ w : alternatingGroup (Fin 6)) : Perm (Fin 6)) * s34⁻¹ := by
      intro w
      subst hγ₂
      rfl
    have hγ₂a : γ₂ ca = ca := by
      apply Subtype.ext
      show ((γ₂ ca : alternatingGroup (Fin 6)) : Perm (Fin 6)) = c1 6
      rw [hγ₂_apply, hγ₁a]
      exact s34_conj_c1
    have hγ₂b : γ₂ cb = cb := by
      apply Subtype.ext
      show ((γ₂ cb : alternatingGroup (Fin 6)) : Perm (Fin 6)) = c2 6
      rw [hγ₂_apply, hB]
      exact s34_conj_c2_sq
    obtain ⟨b₀, hb₀⟩ := conj_of_fix_ca_cb γ₂ hγ₂a hγ₂b
    refine ⟨σ₁ * s34⁻¹ * (b₀ : Perm (Fin 6)), fun w => ?_⟩
    have h1' : ((γ₁ w : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
        s34⁻¹ * ((γ₂ w : alternatingGroup (Fin 6)) : Perm (Fin 6)) * s34⁻¹⁻¹ := by
      rw [hγ₂_apply]
      group
    rw [hβ_apply w, h1', hb₀ w]
    group

@[expose] def fixSub {W : Type*} [Group W] (g : MulAut W) : Subgroup W where
  carrier := {w | g w = w}
  one_mem' := by
    show g 1 = 1
    exact map_one g
  mul_mem' := by
    intro a b ha hb
    change g a = a at ha
    change g b = b at hb
    change g (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    change g a = a at ha
    change g a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_fixSub {W : Type*} [Group W] {g : MulAut W} {w : W} :
    w ∈ fixSub g ↔ g w = w :=
  Iff.rfl

theorem card_fixSub_conj {W : Type*} [Group W] (h g : MulAut W) :
    Nat.card (fixSub (h * g * h⁻¹)) = Nat.card (fixSub g) := by
  have key : fixSub (h * g * h⁻¹) = (fixSub g).map (MulEquiv.toMonoidHom h) := by
    ext w
    rw [Subgroup.mem_map, mem_fixSub]
    constructor
    · intro hw
      rw [MulAut.mul_apply, MulAut.mul_apply] at hw
      refine ⟨h⁻¹ w, ?_, MulAut.apply_inv_self _ h w⟩
      rw [mem_fixSub]
      calc g (h⁻¹ w) = h⁻¹ (h (g (h⁻¹ w))) := (MulAut.inv_apply_self _ h _).symm
        _ = h⁻¹ w := by rw [hw]
    · rintro ⟨y, hy, rfl⟩
      rw [mem_fixSub] at hy
      show (h * g * h⁻¹) (h y) = h y
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self _ h, hy]
  rw [key, Subgroup.card_map_of_injective (f := MulEquiv.toMonoidHom h) (MulEquiv.injective h)]

theorem fixSub_sq {W : Type*} [Group W] {g : MulAut W} (hg : g ^ 3 = 1) :
    fixSub (g ^ 2) = fixSub g := by
  ext w
  rw [mem_fixSub, mem_fixSub, pow_two, MulAut.mul_apply]
  constructor
  · intro h2
    have h3 : g (g (g w)) = w := by
      have h := congrArg (fun e : MulAut W => e w) hg
      simp only [pow_three, MulAut.mul_apply, MulAut.one_apply] at h
      exact h
    rw [h2] at h3
    exact h3
  · intro h1
    rw [h1, h1]

theorem card_fixSub_mem {W : Type*} [Group W] [Finite W] (hW : Nat.card W = 16) {g : MulAut W}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) : Nat.card (fixSub g) = 1 ∨ Nat.card (fixSub g) = 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hG : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hfp : MulAction.fixedPoints ↥(Subgroup.zpowers g) W =
      ((fixSub g : Subgroup W) : Set W) := by
    ext w
    rw [MulAction.mem_fixedPoints, SetLike.mem_coe, mem_fixSub]
    constructor
    · intro h
      exact h ⟨g, Subgroup.mem_zpowers g⟩
    · intro h m
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp m.2
      have hfix : w ∈ MulAction.fixedBy W g := h
      have hk' : w ∈ MulAction.fixedBy W (g ^ k) := MulAction.mem_fixedBy_zpow hfix k
      change (m : MulAut W) w = w
      rw [← hk]
      exact hk'
  have hmod := hG.card_modEq_card_fixedPoints W
  rw [hfp] at hmod
  have hmod' : Nat.card W ≡ Nat.card (fixSub g) [MOD 3] := hmod
  rw [hW] at hmod'
  have hdvd : Nat.card (fixSub g) ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hW]
    exact Subgroup.card_subgroup_dvd_card (fixSub g)
  have hne : Nat.card (fixSub g) ≠ 16 := by
    intro h16
    apply hg1
    have htop : fixSub g = ⊤ := Subgroup.eq_top_of_card_eq (fixSub g) (by rw [h16, hW])
    apply MulEquiv.ext
    intro w
    have hw : w ∈ fixSub g := by
      rw [htop]
      exact Subgroup.mem_top w
    rw [MulAut.one_apply]
    exact mem_fixSub.mp hw
  obtain ⟨i, hi, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hc] at hmod' hne ⊢
  interval_cases i
  · left
    norm_num
  · exfalso
    norm_num [Nat.ModEq] at hmod'
  · right
    norm_num
  · exfalso
    norm_num [Nat.ModEq] at hmod'
  · exfalso
    exact hne (by norm_num)

theorem nine_dvd_sum_fixedBy {W G : Type*} [Group W] [Finite W] [Group G] [Fintype G]
    [MulAction G W] (hG : Nat.card G = 9) :
    9 ∣ ∑ g : G, Nat.card (MulAction.fixedBy W g) := by
  classical
  haveI : ∀ g : G, Fintype (MulAction.fixedBy W g) := fun g => Fintype.ofFinite _
  haveI : Fintype (Quotient (MulAction.orbitRel G W)) := Fintype.ofFinite _
  have key := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (X := W) (G := G)
  simp only [← Nat.card_eq_fintype_card, hG] at key
  exact ⟨Nat.card (Quotient (MulAction.orbitRel G W)), by rw [key, mul_comm]⟩

@[expose] noncomputable def fixCount {W : Type*} [Group W]
    (ι : alternatingGroup (Fin 6) →* MulAut W) (w : alternatingGroup (Fin 6)) : ℕ :=
  Nat.card (fixSub (ι w))

theorem fixCount_one {W : Type*} [Group W] [Finite W] (hW : Nat.card W = 16)
    (ι : alternatingGroup (Fin 6) →* MulAut W) : fixCount ι 1 = 16 := by
  have htop : fixSub (1 : MulAut W) = ⊤ := by
    ext w
    simp [mem_fixSub]
  unfold fixCount
  rw [map_one, htop, Subgroup.card_top, hW]

theorem fixCount_conj {W : Type*} [Group W] (ι : alternatingGroup (Fin 6) →* MulAut W)
    (k w : alternatingGroup (Fin 6)) : fixCount ι (k * w * k⁻¹) = fixCount ι w := by
  unfold fixCount
  rw [map_mul, map_mul, map_inv]
  exact card_fixSub_conj _ _

theorem fixCount_pow_two {W : Type*} [Group W] (ι : alternatingGroup (Fin 6) →* MulAut W)
    (w : alternatingGroup (Fin 6)) (h3 : w ^ 3 = 1) : fixCount ι (w ^ 2) = fixCount ι w := by
  have hg3 : ι w ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  unfold fixCount
  rw [map_pow, fixSub_sq hg3]

theorem fixCount_val {W : Type*} [Group W] [Finite W] (hW : Nat.card W = 16)
    (ι : alternatingGroup (Fin 6) →* MulAut W) (hι : Function.Injective ι)
    (w : alternatingGroup (Fin 6)) (h3 : w ^ 3 = 1) (h1 : w ≠ 1) :
    fixCount ι w = 1 ∨ fixCount ι w = 4 := by
  unfold fixCount
  apply card_fixSub_mem hW
  · rw [← map_pow, h3, map_one]
  · intro h
    apply h1
    apply hι
    rw [h, map_one]

theorem fixCount_pw_00 {W : Type*} [Group W] [Finite W] (hW : Nat.card W = 16)
    (ι : alternatingGroup (Fin 6) →* MulAut W) : fixCount ι (pw 0 0) = 16 := by
  rw [pw_zero_zero, fixCount_one hW]

theorem fixCount_pw_01 {W : Type*} [Group W] (ι : alternatingGroup (Fin 6) →* MulAut W) :
    fixCount ι (pw 0 1) = fixCount ι ca := by
  rw [pw_zero_one, ← kA6_conj, fixCount_conj]

theorem fixCount_pw_02 {W : Type*} [Group W] (ι : alternatingGroup (Fin 6) →* MulAut W) :
    fixCount ι (pw 0 2) = fixCount ι ca := by
  rw [pw_zero_two, fixCount_pow_two ι cb cb_pow_three, ← kA6_conj, fixCount_conj]

theorem fixCount_pw_10 {W : Type*} [Group W] (ι : alternatingGroup (Fin 6) →* MulAut W) :
    fixCount ι (pw 1 0) = fixCount ι ca := by
  rw [pw_one_zero]

theorem fixCount_pw_11 {W : Type*} [Group W] (ι : alternatingGroup (Fin 6) →* MulAut W) :
    fixCount ι (pw 1 1) = fixCount ι (ca * cb) := by
  rw [pw_one_one]

theorem fixCount_pw_12 {W : Type*} [Group W] (ι : alternatingGroup (Fin 6) →* MulAut W) :
    fixCount ι (pw 1 2) = fixCount ι (ca * cb) := by
  rw [pw_one_two, ← hA6_conj, fixCount_conj]

theorem fixCount_pw_20 {W : Type*} [Group W] (ι : alternatingGroup (Fin 6) →* MulAut W) :
    fixCount ι (pw 2 0) = fixCount ι ca := by
  rw [pw_two_zero, fixCount_pow_two ι ca ca_pow_three]

theorem fixCount_pw_21 {W : Type*} [Group W] (ι : alternatingGroup (Fin 6) →* MulAut W) :
    fixCount ι (pw 2 1) = fixCount ι (ca * cb) := by
  rw [pw_two_one, fixCount_pow_two ι _ cd_pow_three, ← hA6_conj, fixCount_conj]

theorem fixCount_pw_22 {W : Type*} [Group W] (ι : alternatingGroup (Fin 6) →* MulAut W) :
    fixCount ι (pw 2 2) = fixCount ι (ca * cb) := by
  rw [pw_two_two, fixCount_pow_two ι _ cc_pow_three]

theorem fixCount_pw_cond {W : Type*} [Group W] (ι : alternatingGroup (Fin 6) →* MulAut W)
    (i j : Fin 3) (hc : (i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0)) :
    fixCount ι (pw i j) = fixCount ι ca := by
  rcases three_pw_cases i j hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact fixCount_pw_01 ι
  · exact fixCount_pw_02 ι
  · exact fixCount_pw_10 ι
  · exact fixCount_pw_20 ι

theorem fixCount_pw_other {W : Type*} [Group W] (ι : alternatingGroup (Fin 6) →* MulAut W)
    (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) :
    fixCount ι (pw i j) = fixCount ι (ca * cb) := by
  rcases three_pw_other i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact fixCount_pw_11 ι
  · exact fixCount_pw_12 ι
  · exact fixCount_pw_21 ι
  · exact fixCount_pw_22 ι

theorem nine_dvd_sum_pw {W : Type*} [Group W] [Finite W]
    (ι : alternatingGroup (Fin 6) →* MulAut W) :
    9 ∣ ∑ p : Fin 3 × Fin 3, fixCount ι (pw p.1 p.2) := by
  classical
  letI : MulAction F06 W := MulAction.compHom W (ι.comp F06.subtype)
  haveI : Fintype F06 := Fintype.ofFinite _
  have hF : Nat.card F06 = 9 := card_F06
  have hB := nine_dvd_sum_fixedBy (W := W) (G := F06) hF
  have hset : ∀ x : F06, MulAction.fixedBy W x =
      ((fixSub (ι (x : alternatingGroup (Fin 6))) : Subgroup W) : Set W) := by
    intro x
    ext w
    exact Iff.rfl
  have hbij : Function.Bijective (fun p : Fin 3 × Fin 3 =>
      (⟨pw p.1 p.2, pw_mem_F06 p.1 p.2⟩ : F06)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, ?_⟩
    · rintro ⟨i, j⟩ ⟨i', j'⟩ hpq
      have h1 : pw i j = pw i' j' := congrArg Subtype.val hpq
      have h2 : c1 6 ^ (i : ℕ) * c2 6 ^ (j : ℕ) = c1 6 ^ (i' : ℕ) * c2 6 ^ (j' : ℕ) := by
        rw [← coe_pw, ← coe_pw, h1]
      obtain ⟨e1, e2⟩ := pw_inj_perm i j i' j' h2
      rw [e1, e2]
    · have h9 : Fintype.card (Fin 3 × Fin 3) = 9 := by simp
      rw [h9, ← Nat.card_eq_fintype_card, hF]
  have hpt : ∀ p : Fin 3 × Fin 3, fixCount ι (pw p.1 p.2) =
      Nat.card (MulAction.fixedBy W (⟨pw p.1 p.2, pw_mem_F06 p.1 p.2⟩ : F06)) := by
    intro p
    rw [hset]
    rfl
  have hsum : ∑ p : Fin 3 × Fin 3, fixCount ι (pw p.1 p.2) =
      ∑ x : F06, Nat.card (MulAction.fixedBy W x) :=
    Fintype.sum_bijective _ hbij (fun p : Fin 3 × Fin 3 => fixCount ι (pw p.1 p.2))
      (fun x : F06 => Nat.card (MulAction.fixedBy W x)) hpt
  rw [hsum]
  exact hB

theorem sum_fixCount_pw {W : Type*} [Group W] [Finite W] (hW : Nat.card W = 16)
    (ι : alternatingGroup (Fin 6) →* MulAut W) :
    ∑ p : Fin 3 × Fin 3, fixCount ι (pw p.1 p.2) =
      16 + 4 * fixCount ι ca + 4 * fixCount ι (ca * cb) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, fixCount_pw_00 hW ι,
    fixCount_pw_01 ι, fixCount_pw_02 ι, fixCount_pw_10 ι, fixCount_pw_11 ι,
    fixCount_pw_12 ι, fixCount_pw_20 ι, fixCount_pw_21 ι, fixCount_pw_22 ι]
  ring

theorem fixCount_ca_ne_cb {W : Type*} [Group W] [Finite W] (hW : Nat.card W = 16)
    (ι : alternatingGroup (Fin 6) →* MulAut W) (hι : Function.Injective ι) :
    fixCount ι ca ≠ fixCount ι (ca * cb) := by
  have hsum := nine_dvd_sum_pw ι
  rw [sum_fixCount_pw hW ι] at hsum
  have hx := fixCount_val hW ι hι ca ca_pow_three ca_ne_one
  have hy := fixCount_val hW ι hι (ca * cb) cc_pow_three cc_ne_one
  omega

theorem isThreeCycle_iff_fixCount {W : Type*} [Group W] [Finite W] (hW : Nat.card W = 16)
    (ι : alternatingGroup (Fin 6) →* MulAut W) (hι : Function.Injective ι)
    (w : alternatingGroup (Fin 6)) (h3 : w ^ 3 = 1) (h1 : w ≠ 1) :
    IsThreeCycle (w : Perm (Fin 6)) ↔ fixCount ι w = fixCount ι ca := by
  have hxy := fixCount_ca_ne_cb hW ι hι
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE : IsPGroup 3 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime h3 h1, pow_one])
  have hF : Nat.card F06 = 3 ^ (Nat.card (alternatingGroup (Fin 6))).factorization 3 := by
    rw [factorization_card_alt6_three, card_F06]
    norm_num
  obtain ⟨g, hg⟩ := exists_le_map_conj_of_card hF hE
  obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.mp (hg (Subgroup.mem_zpowers w))
  have hwu : w = g * u * g⁻¹ := hug.symm
  have hfc : fixCount ι w = fixCount ι u := by
    rw [hwu, fixCount_conj]
  have hcyc : IsThreeCycle (w : Perm (Fin 6)) ↔ IsThreeCycle (u : Perm (Fin 6)) := by
    have hc : (w : Perm (Fin 6)) =
        (g : Perm (Fin 6)) * (u : Perm (Fin 6)) * (g : Perm (Fin 6))⁻¹ := by
      simp only [hwu, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hc]
    unfold IsThreeCycle
    rw [cycleType_conj]
  obtain ⟨i, j, rfl⟩ := exists_pw hu
  have hu1 : pw i j ≠ 1 := by
    intro h
    apply h1
    rw [hwu, h, mul_one, mul_inv_cancel]
  have hnot : ¬(i = 0 ∧ j = 0) := by
    rintro ⟨rfl, rfl⟩
    exact hu1 pw_zero_zero
  rw [hcyc, hfc, three_pw_iff]
  by_cases hc : (i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0)
  · exact iff_of_true hc (fixCount_pw_cond ι i j hc)
  · obtain ⟨hi, hj⟩ := three_pw_nonzero i j hc hnot
    exact iff_of_false hc (fun h => hxy ((fixCount_pw_other ι i j hi hj).symm.trans h).symm)

theorem kf1422GL42_holds : KF1422GL42 := by
  unfold KF1422GL42
  intro G₀ _ V _ hcard Y hY g hg
  haveI : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨ψ⟩ := hY
  let α : MulAut Y := Y.normalizerMonoidHom ⟨g, hg⟩
  have hα : ∀ k : Y, ((α k : Y) : MulAut ↥V) = g * (k : MulAut ↥V) * g⁻¹ :=
    fun k => rfl
  let ι : alternatingGroup (Fin 6) →* MulAut ↥V := Y.subtype.comp ψ.symm.toMonoidHom
  have hι : Function.Injective ι := fun a b hab => ψ.symm.injective (Subtype.ext hab)
  let β : MulAut (alternatingGroup (Fin 6)) := (ψ.symm.trans α).trans ψ
  have hβι : ∀ w, ι (β w) = g * ι w * g⁻¹ := by
    intro w
    have h1 : ι (β w) = ((α (ψ.symm w) : Y) : MulAut ↥V) := by
      show ((ψ.symm (ψ (α (ψ.symm w))) : Y) : MulAut ↥V) = _
      rw [MulEquiv.symm_apply_apply]
    rw [h1]
    exact hα (ψ.symm w)
  have hΦ : ∀ w, fixCount ι (β w) = fixCount ι w := by
    intro w
    unfold fixCount
    rw [hβι w, card_fixSub_conj]
  have hβ3 : ∀ w : alternatingGroup (Fin 6), IsThreeCycle (w : Perm (Fin 6)) →
      IsThreeCycle ((β w : alternatingGroup (Fin 6)) : Perm (Fin 6)) := by
    intro w hw
    have hw3' : (w : Perm (Fin 6)) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one (w : Perm (Fin 6))
      rwa [hw.orderOf] at h
    have hw3 : w ^ 3 = 1 := Subtype.ext hw3'
    have hw1 : w ≠ 1 := fun h => hw.ne_one (congrArg Subtype.val h)
    have hβw3 : β w ^ 3 = 1 := by rw [← map_pow, hw3, map_one]
    have hβw1 : β w ≠ 1 := fun h => hw1 ((MulEquiv.injective β) (h.trans (map_one β).symm))
    rw [isThreeCycle_iff_fixCount hcard ι hι (β w) hβw3 hβw1, hΦ w]
    exact (isThreeCycle_iff_fixCount hcard ι hι w hw3 hw1).mp hw
  obtain ⟨σ, hσ⟩ := isS6_of_threeCycle β hβ3
  unfold IsS6Type
  refine ⟨ψ, σ, fun k => ?_⟩
  have hk : β (ψ k) = ψ (α k) := by
    show ψ (α (ψ.symm (ψ k))) = ψ (α k)
    rw [MulEquiv.symm_apply_apply]
  have h := hσ (ψ k)
  rw [hk] at h
  exact h

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
