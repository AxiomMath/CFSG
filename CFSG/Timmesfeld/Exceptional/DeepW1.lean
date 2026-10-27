module

public import CFSG.Timmesfeld.Exceptional.SigmaDiam
import CFSG.Timmesfeld.Bridge.SchurNarrow
import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang CFSG.Blueprint
open CFSG.Timmesfeld.Moufang.J2 (nativeGens)

variable {G : Type*} [Group G] {D : Set G}

private theorem mul_mul_self_cancel' {d : G} (hd2 : d * d = 1) (y : G) : d * (d * y) = y := by
  rw [← mul_assoc, hd2, one_mul]

theorem orderOf_eq_three_of_pow_six {a : G} (h6 : a ^ 6 = 1) (hodd : Odd (orderOf a))
    (h1 : a ≠ 1) : orderOf a = 3 := by
  have hdvd := orderOf_dvd_of_pow_eq_one h6
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have hne1 : orderOf a ≠ 1 := fun e => h1 (orderOf_eq_one_iff.1 e)
  interval_cases hn : orderOf a <;> simp_all <;> contradiction

theorem orderOf_eq_five_of_pow_ten {a : G} (h10 : a ^ 10 = 1) (hodd : Odd (orderOf a))
    (h1 : a ≠ 1) : orderOf a = 5 := by
  have hdvd := orderOf_dvd_of_pow_eq_one h10
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have hne1 : orderOf a ≠ 1 := fun e => h1 (orderOf_eq_one_iff.1 e)
  interval_cases hn : orderOf a <;> simp_all <;> contradiction

theorem special_of_ne_line' (hD : IsRootInvolutionSet D)
    (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hNL : NoLevi D) (hNP : NoPolar D)
    (hPl : ExcNoPlane D) {d x₁ x₂ : G} (hd : d ∈ D) (hx₁ : x₁ ∈ D) (hdx₁ : Commute d x₁)
    (hdx₁D : d * x₁ ∈ D) (hx₂ : x₂ ∈ D) (hdx₂ : Commute d x₂) (hdx₂D : d * x₂ ∈ D)
    (hne : x₂ ≠ x₁) (hne' : x₂ ≠ d * x₁) :
    orderOf (x₁ * x₂) = 4 ∧ (x₁ * x₂) ^ 2 = d := by
  have hnc : ¬ Commute x₁ x₂ := by
    intro h12
    have h12D : x₁ * x₂ ∈ D := hNP x₁ hx₁ x₂ hx₂ h12 (Ne.symm hne)
    have hd12 : Commute d (x₁ * x₂) := hdx₁.mul_right hdx₂
    have hd12D : d * (x₁ * x₂) ∈ D := by
      refine hNP d hd _ h12D hd12 fun he => hne' ?_
      calc x₂ = x₁ * (x₁ * x₂) := by rw [← mul_assoc, hD.mul_self_eq_one hx₁, one_mul]
        _ = x₁ * d := by rw [← he]
        _ = d * x₁ := hdx₁.eq.symm
    have hdx₁ne : d ≠ x₁ := fun e => hD.ne_one hdx₁D (by rw [← e, hD.mul_self_eq_one hd])
    have hx₂d : x₂ ≠ d := fun e => hD.ne_one hdx₂D (by rw [e, hD.mul_self_eq_one hd])
    exact hPl d hd x₁ hx₁ x₂ hx₂ hdx₁ hdx₂ h12 hdx₁ne hx₂d hne hne' hdx₁D hdx₂D h12D
      (by rw [mul_assoc]; exact hd12D)
  have h4 : orderOf (x₁ * x₂) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hx₁ hx₂ with h1 | h1 | ⟨hodd, -⟩
    · exact absurd h1 hnc
    · exact h1
    · exact absurd hdx₂ (hNL x₁ hx₁ x₂ hx₂ hnc hodd d hd hdx₁)
  exact ⟨h4, NoLevi.sq_eq_of_commute hD hconj hNL hNP hPl hx₁ hx₂ hd hdx₁ hdx₂ hnc⟩

theorem lineConfig_of_lines' (hD : IsRootInvolutionSet D)
    (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hNL : NoLevi D) (hNP : NoPolar D)
    (hPl : ExcNoPlane D) {n : ℕ} {d c : G} {x : Fin n → G} (hd : d ∈ D) (hc : c ∈ D)
    (h5 : orderOf (d * c) = 5) (hx : ∀ i, x i ∈ D) (hxd : ∀ i, Commute d (x i))
    (hxdD : ∀ i, d * x i ∈ D) (hne : ∀ i j, i ≠ j → x j ≠ x i ∧ x j ≠ d * x i)
    (hx3 : ∀ i, orderOf (c * x i) = 3) (hx5 : ∀ i, orderOf (c * (d * x i)) = 5) :
    LineConfig d c x where
  d_sq := hD.mul_self_eq_one hd
  c_sq := hD.mul_self_eq_one hc
  x_sq i := hD.mul_self_eq_one (hx i)
  dc_pow := by rw [← h5]; exact pow_orderOf_eq_one _
  d_comm := hxd
  sq_eq i j hij := (special_of_ne_line' hD hconj hNL hNP hPl hd (hx i) (hxd i) (hxdD i) (hx j)
    (hxd j) (hxdD j) (hne i j hij).1 (hne i j hij).2).2
  cx_pow i := by rw [← hx3 i]; exact pow_orderOf_eq_one _
  cdx_pow i := by rw [← hx5 i]; exact pow_orderOf_eq_one _

theorem eq_line_of_five' (h : Hyp G D) (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D)
    {d c : G} (hd : d ∈ D) (hc : c ∈ D) (h5 : orderOf (d * c) = 5) {x : Fin 5 → G}
    (hx : ∀ i, x i ∈ D) (hxd : ∀ i, Commute d (x i)) (hxdD : ∀ i, d * x i ∈ D)
    (hu : x 0 * x 1 * x 2 * x 3 * x 4 * (x 0 * x 1 * x 2 * x 3 * x 4) = 1)
    (huc : Commute (x 0 * x 1 * x 2 * x 3 * x 4) c) {w : G} (hw : w ∈ D) (hwd : Commute d w)
    (hwdD : d * w ∈ D) (hw3 : orderOf (c * w) = 3) : ∃ i, w = x i ∨ w = d * x i := by
  by_contra hno
  push Not at hno
  have hD := h.root
  have hconj : ∀ g : G, ∀ y ∈ D, g * y * g⁻¹ ∈ D := fun g y hy => h.conj_mem g hy
  have hd2 := hD.mul_self_eq_one hd
  have hw2 : w * w = 1 := hD.mul_self_eq_one hw
  have hconj' : ∀ i, w * x i * w = x i * d := by
    intro i
    have hsp := (special_of_ne_line' hD hconj hNL hNP hPl hd (hx i) (hxd i) (hxdD i) hw hwd
      hwdD (hno i).1 (hno i).2).2
    rw [pow_two] at hsp
    have hxi2 := hD.mul_self_eq_one (hx i)
    calc w * x i * w = x i * (x i * w * (x i * w)) := by
          rw [show x i * (x i * w * (x i * w)) = (x i * x i) * w * x i * w by group, hxi2,
            one_mul]
      _ = x i * d := by rw [hsp]
  have key : ∀ a b : G, (w * a * w) * (w * b * w) = w * (a * b) * w := fun a b => by
    rw [show (w * a * w) * (w * b * w) = w * a * (w * w) * b * w by group, hw2, mul_one]
    group
  have hp : ∀ (a : G) (i : Fin 5), a * d * (x i * d) = a * x i := fun a i => by
    rw [show a * d * (x i * d) = a * (d * x i) * d by group, (hxd i).eq,
      show a * (x i * d) * d = a * x i * (d * d) by group, hd2, mul_one]
  set u := x 0 * x 1 * x 2 * x 3 * x 4 with hu_def
  have hdu : Commute d u := by
    rw [hu_def]
    exact ((((hxd 0).mul_right (hxd 1)).mul_right (hxd 2)).mul_right (hxd 3)).mul_right (hxd 4)
  have hwu : w * u * w = u * d := by
    calc w * u * w = (w * x 0 * w) * (w * x 1 * w) * (w * x 2 * w) * (w * x 3 * w) *
          (w * x 4 * w) := by
          rw [key, key, key, key]
      _ = x 0 * d * (x 1 * d) * (x 2 * d) * (x 3 * d) * (x 4 * d) := by simp only [hconj']
      _ = u * d := by
          rw [hp (x 0) 1, show x 0 * x 1 * (x 2 * d) = x 0 * x 1 * x 2 * d by group,
            hp (x 0 * x 1 * x 2) 3, hu_def]
          group
  have h1 : u * w = w * (u * d) := by
    calc u * w = w * (w * u * w) := by
          rw [show w * (w * u * w) = (w * w) * u * w by group, hw2, one_mul]
      _ = w * (u * d) := by rw [hwu]
  have h2 : u * w * u = w * d := by
    rw [h1, show w * (u * d) * u = w * (u * d * u) by group,
      show u * d * u = d * (u * u) by rw [← hdu.eq]; group, hu, mul_one]
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hcu : u * c * u = c := by rw [huc.eq, mul_assoc, hu, mul_one]
  have hconjc : u * (w * c) * u⁻¹ = w * d * c := by
    rw [hui]
    calc u * (w * c) * u = (u * w * u) * (u * c * u) := by
          rw [show (u * w * u) * (u * c * u) = u * w * (u * u) * c * u by group, hu, mul_one]
          group
      _ = w * d * c := by rw [h2, hcu]
  have e1 := orderOf_conj_eq u (w * c)
  rw [hconjc, ← hwd.eq] at e1
  have h3 : orderOf (w * c) = 3 := by rw [orderOf_mul_comm_eq]; exact hw3
  have hdw2 : d * w * (d * w) = 1 := hD.mul_self_eq_one hwdD
  have hodd : Odd (orderOf (w * (d * w) * c)) := by
    rw [show w * (d * w) * c = d * c by
      rw [← mul_assoc, ← hwd.eq, mul_assoc d w w, hw2, mul_one], h5]
    decide
  exact false_of_orderOf_three_three_of_line hw2 hdw2 (hD.mul_self_eq_one hc)
    (hwd.symm.mul_right (Commute.refl w)) h3 (e1.trans h3) hodd

section FiveLines

variable {d c : G} {x : Fin 3 → G}

theorem lift_point' (h : Hyp G D) (hNP : NoPolar D) (hd : d ∈ D) (hc : c ∈ D)
    (h5 : orderOf (d * c) = 5) (hTO : TotallyOpposite D d c) (hcfg : LineConfig d c x)
    {q : P3.Pres} {k : Fin 5} (hqD : threeLinesHom hcfg q ∈ D)
    (hqk : P3.toSeed q = nativeGens (k.addNat 2)) :
    Commute d (threeLinesHom hcfg q) ∧ d * threeLinesHom hcfg q ∈ D ∧
      orderOf (c * threeLinesHom hcfg q) = 3 ∧ orderOf (c * (d * threeLinesHom hcfg q)) = 5 := by
  have hD := h.root
  have hd2 := hD.mul_self_eq_one hd
  set φ := threeLinesHom hcfg with hφ
  have hφ0 : φ (PresentedGroup.of 0) = d := threeLinesHom_zero hcfg
  have hφ1 : φ (PresentedGroup.of 1) = c := threeLinesHom_one hcfg
  have hJ := lineConfig_native
  have ht0 : P3.toSeed (PresentedGroup.of 0) = nativeGens 0 := P3.toSeed_of 0
  have ht1 : P3.toSeed (PresentedGroup.of 1) = nativeGens 1 := P3.toSeed_of 1
  have hq : P3.toSeed ((q * PresentedGroup.of 0) * (q * PresentedGroup.of 0)) = 1 := by
    rw [map_mul, map_mul, hqk, ht0, ← pow_two]
    exact (commute_iff_mul_sq_eq_one (hJ.x_sq k) hJ.d_sq).1 (hJ.d_comm k).symm
  have hz2 := P3.mul_self_eq_one_of_toSeed φ hq
  have hzc := P3.commute_of_toSeed φ hq
  rw [map_mul, map_mul, hφ0] at hz2 hzc
  have hcomm : Commute d (φ q) := by
    by_contra hnc
    have hnc' : ¬ Commute (φ q) d := fun e => hnc e.symm
    have h4 : orderOf (φ q * d) = 4 := by
      rw [commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hqD) hd2] at hnc'
      have : orderOf (φ q * d) = 2 ^ 2 := by
        refine orderOf_eq_prime_pow (p := 2) ?_ ?_
        · simpa using hnc'
        · rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two]
          exact hz2
      simpa using this
    have hzD := hD.sq_mem hqD hd h4
    rw [pow_two] at hzD
    have hdz : Commute d (φ q * d * (φ q * d)) := by
      have := hzc (PresentedGroup.of 0)
      rw [hφ0] at this
      exact this.symm
    have hzc' : Commute (φ q * d * (φ q * d)) c := by
      have := hzc (PresentedGroup.of 1)
      rwa [hφ1] at this
    exact false_of_commute_of_five h hNP hd hc h5 hzD hdz hzc'
  have hq3 : P3.toSeed ((PresentedGroup.of 1 * q) ^ 3) = 1 := by
    rw [map_pow, map_mul, ht1, hqk]
    exact hJ.cx_pow k
  have h6 : (c * φ q) ^ 6 = 1 := by
    have := P3.mul_self_eq_one_of_toSeed φ hq3
    rw [map_pow, map_mul, hφ1, ← pow_add] at this
    exact this
  have hne0 : φ q ≠ d := by
    intro e
    rw [e] at h6
    have := orderOf_dvd_of_pow_eq_one h6
    rw [orderOf_mul_comm_eq, h5] at this
    exact absurd this (by norm_num)
  have hdqD : d * φ q ∈ D := hNP d hd _ hqD hcomm hne0.symm
  have hq5 : P3.toSeed ((PresentedGroup.of 1 * (PresentedGroup.of 0 * q)) ^ 5) = 1 := by
    rw [map_pow, map_mul, map_mul, ht1, ht0, hqk]
    exact hJ.cdx_pow k
  have h10 : (c * (d * φ q)) ^ 10 = 1 := by
    have := P3.mul_self_eq_one_of_toSeed φ hq5
    rw [map_pow, map_mul, map_mul, hφ1, hφ0, ← pow_add] at this
    exact this
  obtain ⟨n1, o1⟩ := hTO (φ q) hqD hcomm
  obtain ⟨n2, o2⟩ := hTO (d * φ q) hdqD ((Commute.refl d).mul_right hcomm)
  refine ⟨hcomm, hdqD, orderOf_eq_three_of_pow_six h6 (by rwa [orderOf_mul_comm_eq]) ?_,
    orderOf_eq_five_of_pow_ten h10 (by rwa [orderOf_mul_comm_eq]) ?_⟩
  · intro h1
    exact n1 ((eq_inv_of_mul_eq_one_right h1).symm ▸ (Commute.refl c).inv_left)
  · intro h1
    exact n2 ((eq_inv_of_mul_eq_one_right h1).symm ▸ (Commute.refl c).inv_left)

@[expose] noncomputable def fivePoints (hcfg : LineConfig d c x) : Fin 5 → G :=
  ![x 0, x 1, x 2, threeLinesHom hcfg (P3.conjPoint P3.conjX3),
    threeLinesHom hcfg (P3.conjPoint P3.conjX4)]

theorem exists_preimage_fivePoints (hcfg : LineConfig d c x) (i : Fin 5) :
    ∃ q : P3.Pres, threeLinesHom hcfg q = fivePoints hcfg i ∧
      P3.toSeed q = nativeGens (i.addNat 2) := by
  have htx : ∀ i : Fin 3, P3.toSeed (PresentedGroup.of (i.addNat 2)) =
      nativeGens ((Fin.castLE (by norm_num) i : Fin 5).addNat 2) := toSeed_addNat
  fin_cases i
  · exact ⟨_, threeLinesHom_addNat hcfg 0, by rw [htx 0]; rfl⟩
  · exact ⟨_, threeLinesHom_addNat hcfg 1, by rw [htx 1]; rfl⟩
  · exact ⟨_, threeLinesHom_addNat hcfg 2, by rw [htx 2]; rfl⟩
  · exact ⟨_, rfl, P3.toSeed_conjX3⟩
  · exact ⟨_, rfl, P3.toSeed_conjX4⟩

theorem fivePoints_spec (h : Hyp G D) (hNP : NoPolar D) (hd : d ∈ D) (hc : c ∈ D)
    (h5 : orderOf (d * c) = 5) (hTO : TotallyOpposite D d c) (hcfg : LineConfig d c x)
    (hx : ∀ i, x i ∈ D) (hxd : ∀ i, Commute d (x i)) (hxdD : ∀ i, d * x i ∈ D)
    (hx3 : ∀ i, orderOf (c * x i) = 3) (hx5 : ∀ i, orderOf (c * (d * x i)) = 5) :
    (∀ i, fivePoints hcfg i ∈ (threeLinesHom hcfg).range) ∧
      (∀ i, fivePoints hcfg i ∈ D) ∧ (∀ i, Commute d (fivePoints hcfg i)) ∧
      (∀ i, d * fivePoints hcfg i ∈ D) ∧ (∀ i, orderOf (c * fivePoints hcfg i) = 3) ∧
      (∀ i, orderOf (c * (d * fivePoints hcfg i)) = 5) ∧
      (∀ g ∈ (threeLinesHom hcfg).range, Commute (fivePoints hcfg 0 * fivePoints hcfg 1 *
        fivePoints hcfg 2 * fivePoints hcfg 3 * fivePoints hcfg 4) g) ∧
      fivePoints hcfg 0 * fivePoints hcfg 1 * fivePoints hcfg 2 * fivePoints hcfg 3 *
        fivePoints hcfg 4 * (fivePoints hcfg 0 * fivePoints hcfg 1 * fivePoints hcfg 2 *
        fivePoints hcfg 3 * fivePoints hcfg 4) = 1 := by
  set φ := threeLinesHom hcfg with hφ
  have hφ0 : φ (PresentedGroup.of 0) = d := threeLinesHom_zero hcfg
  have hφx : ∀ i : Fin 3, φ (PresentedGroup.of (i.addNat 2)) = x i := threeLinesHom_addNat hcfg
  have htx : ∀ i : Fin 3, P3.toSeed (PresentedGroup.of (i.addNat 2)) =
      nativeGens ((Fin.castLE (by norm_num) i : Fin 5).addNat 2) := toSeed_addNat
  have hφp : ∀ w : List (Fin 5 × Bool), φ (P3.conjPoint w) ∈ D := fun w => by
    rw [P3.conjPoint_def, map_mul, map_mul, map_inv, hφ0]
    exact h.conj_mem _ hd
  obtain ⟨hc₃, hcD₃, h3₃, h5₃⟩ := lift_point' h hNP hd hc h5 hTO hcfg (k := 3) (hφp _)
    P3.toSeed_conjX3
  obtain ⟨hc₄, hcD₄, h3₄, h5₄⟩ := lift_point' h hNP hd hc h5 hTO hcfg (k := 4) (hφp _)
    P3.toSeed_conjX4
  have hu : P3.toSeed (PresentedGroup.of ((0 : Fin 3).addNat 2) *
      PresentedGroup.of ((1 : Fin 3).addNat 2) * PresentedGroup.of ((2 : Fin 3).addNat 2) *
      P3.conjPoint P3.conjX3 * P3.conjPoint P3.conjX4) = 1 := by
    rw [map_mul, map_mul, map_mul, map_mul, htx 0, htx 1, htx 2, P3.toSeed_conjX3,
      P3.toSeed_conjX4]
    exact ovoid_native
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · obtain ⟨q, hq, -⟩ := exists_preimage_fivePoints hcfg i
    exact ⟨q, hq⟩
  · fin_cases i
    · exact hx 0
    · exact hx 1
    · exact hx 2
    · exact hφp _
    · exact hφp _
  · fin_cases i
    · exact hxd 0
    · exact hxd 1
    · exact hxd 2
    · exact hc₃
    · exact hc₄
  · fin_cases i
    · exact hxdD 0
    · exact hxdD 1
    · exact hxdD 2
    · exact hcD₃
    · exact hcD₄
  · fin_cases i
    · exact hx3 0
    · exact hx3 1
    · exact hx3 2
    · exact h3₃
    · exact h3₄
  · fin_cases i
    · exact hx5 0
    · exact hx5 1
    · exact hx5 2
    · exact h5₃
    · exact h5₄
  · rintro g ⟨q, rfl⟩
    have := P3.commute_of_toSeed φ hu q
    rwa [map_mul, map_mul, map_mul, map_mul, hφx 0, hφx 1, hφx 2] at this
  · have := P3.mul_self_eq_one_of_toSeed φ hu
    rwa [map_mul, map_mul, map_mul, map_mul, hφx 0, hφx 1, hφx 2] at this

theorem fivePoints_ne (hD : IsRootInvolutionSet D) (hd : d ∈ D) (hc : c ∈ D)
    (h5 : orderOf (d * c) = 5) (hcfg : LineConfig d c x) (i j : Fin 5) (hij : i ≠ j) :
    fivePoints hcfg j ≠ fivePoints hcfg i ∧ fivePoints hcfg j ≠ d * fivePoints hcfg i := by
  set φ := threeLinesHom hcfg with hφ
  have hφ0 : φ (PresentedGroup.of 0) = d := threeLinesHom_zero hcfg
  have hφ1 : φ (PresentedGroup.of 1) = c := threeLinesHom_one hcfg
  have hdc : ¬ Commute (φ (PresentedGroup.of 0)) (φ (PresentedGroup.of 1)) := by
    rw [hφ0, hφ1]
    exact not_commute_of_orderOf_eq_five hD hd hc h5
  have ht0 : P3.toSeed (PresentedGroup.of 0) = nativeGens 0 := P3.toSeed_of 0
  obtain ⟨p, hp, hpi⟩ := exists_preimage_fivePoints hcfg i
  obtain ⟨q, hq, hqj⟩ := exists_preimage_fivePoints hcfg j
  rw [← hp, ← hq]
  have hn := native_ne hij
  refine ⟨fun e => hn.1 ?_, fun e => hn.2 ?_⟩
  · rw [← hqj, ← hpi]
    exact P3.toSeed_eq_of_eq φ hdc e
  · rw [← hqj, ← hpi, ← ht0, ← map_mul]
    exact P3.toSeed_eq_of_eq φ hdc (by rw [map_mul, hφ0]; exact e)

end FiveLines

theorem exists_five_lines' (h : Hyp G D) (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D)
    {d c : G} (hd : d ∈ D) (hc : c ∈ D) (h5 : orderOf (d * c) = 5) (hTO : TotallyOpposite D d c)
    {x : Fin 3 → G} (hx : ∀ i, x i ∈ D) (hxd : ∀ i, Commute d (x i)) (hxdD : ∀ i, d * x i ∈ D)
    (hne : ∀ i j, i ≠ j → x j ≠ x i ∧ x j ≠ d * x i) (hx3 : ∀ i, orderOf (c * x i) = 3)
    (hx5 : ∀ i, orderOf (c * (d * x i)) = 5) :
    ∃ (K : Subgroup G) (y : Fin 5 → G), d ∈ K ∧ c ∈ K ∧ (∀ i, y i ∈ K) ∧
      y 0 = x 0 ∧ y 1 = x 1 ∧ y 2 = x 2 ∧
      (∀ i, y i ∈ D) ∧ (∀ i, Commute d (y i)) ∧ (∀ i, d * y i ∈ D) ∧
      (∀ i j, i ≠ j → y j ≠ y i ∧ y j ≠ d * y i) ∧
      (∀ i, orderOf (c * y i) = 3) ∧ (∀ i, orderOf (c * (d * y i)) = 5) ∧
      (∀ g ∈ K, Commute (y 0 * y 1 * y 2 * y 3 * y 4) g) ∧
      y 0 * y 1 * y 2 * y 3 * y 4 * (y 0 * y 1 * y 2 * y 3 * y 4) = 1 := by
  have hD := h.root
  have hconj : ∀ g : G, ∀ y ∈ D, g * y * g⁻¹ ∈ D := fun g y hy => h.conj_mem g hy
  have hcfg := lineConfig_of_lines' hD hconj hNL hNP hPl hd hc h5 hx hxd hxdD hne hx3 hx5
  obtain ⟨hK, hyD, hyd, hydD, hy3, hy5, huK, hu⟩ :=
    fivePoints_spec h hNP hd hc h5 hTO hcfg hx hxd hxdD hx3 hx5
  exact ⟨(threeLinesHom hcfg).range, fivePoints hcfg, ⟨_, threeLinesHom_zero hcfg⟩,
    ⟨_, threeLinesHom_one hcfg⟩, hK, rfl, rfl, rfl, hyD, hyd, hydD,
    fivePoints_ne hD hd hc h5 hcfg, hy3, hy5, huK, hu⟩

theorem orders_of_near (h : Hyp G D) (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D)
    (hP1 : ExcP1 D) {c p x : G} (hc : c ∈ D) (hp : p ∈ D) (hp4 : p ∈ nbhd D c 4)
    (hp3 : p ∉ nbhd D c 3) (hx : x ∈ collinearSet D p) (hx3 : x ∈ nbhd D c 3) :
    orderOf (c * x) = 3 ∧ orderOf (c * (p * x)) = 5 := by
  have hD := h.root
  obtain ⟨hxD, hpx, hpxD⟩ := hx
  have hx2 : x ∉ nbhd D c 2 := fun h2 => hp3 (mem_nbhd_succ_of_commute hp h2 hpx)
  have h3 := orderOf_eq_three_of_mem_nbhd_three hD hNL hNP hP1 hc hx3 hx2
  have hppx : Commute p (p * x) := (Commute.refl p).mul_right hpx
  have hpx2 : p * x ∉ nbhd D c 2 := fun h2 => hp3 (mem_nbhd_succ_of_commute hp h2 hppx)
  have hpx4 : p * x ∈ nbhd D c 4 :=
    mem_nbhd_succ_of_commute hpxD hx3 (hpx.mul_left (Commute.refl x))
  have h5p := orderOf_eq_five_of_mem_nbhd_four h.isClass hD hNL hNP hPl hP1 hp hc hp4 hp3
  have hpx3 : p * x ∉ nbhd D c 3 := by
    intro h3'
    have h33 := orderOf_eq_three_of_mem_nbhd_three hD hNL hNP hP1 hc h3' hpx2
    have hx2' := hD.mul_self_eq_one hxD
    have hodd : Odd (orderOf (x * (p * x) * c)) := by
      rw [show x * (p * x) * c = p * c by
        rw [← mul_assoc, ← hpx.eq, mul_assoc p x x, hx2', mul_one], h5p]
      decide
    exact false_of_orderOf_three_three_of_line hx2' (hD.mul_self_eq_one hpxD)
      (hD.mul_self_eq_one hc) (hpx.symm.mul_right (Commute.refl x)) h3 h33 hodd
  have h5 := orderOf_eq_five_of_mem_nbhd_four h.isClass hD hNL hNP hPl hP1 hpxD hc hpx4 hpx3
  exact ⟨by rw [orderOf_mul_comm_eq]; exact h3, by rw [orderOf_mul_comm_eq]; exact h5⟩

private theorem same_line {p a b w : G} (hp2 : p * p = 1) (ha : a = w ∨ a = p * w)
    (hb : b = w ∨ b = p * w) : b = a ∨ b = p * a := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl
  · exact .inr (mul_mul_self_cancel' hp2 _).symm
  · exact .inl rfl

theorem not_six_near (h : Hyp G D) (hNP : NoPolar D) (hNL : NoLevi D) (hPl : ExcNoPlane D)
    (hP1 : ExcP1 D) {c p : G} (hc : c ∈ D) (hp : p ∈ D) (hp4 : p ∈ nbhd D c 4)
    (hp3 : p ∉ nbhd D c 3) {x : Fin 6 → G} (hx : ∀ i, x i ∈ collinearSet D p)
    (hx3 : ∀ i, x i ∈ nbhd D c 3) : ¬ ∀ i j, i ≠ j → x j ≠ x i ∧ x j ≠ p * x i := by
  intro hne
  have hD := h.root
  have hp2 := hD.mul_self_eq_one hp
  have h5 := orderOf_eq_five_of_mem_nbhd_four h.isClass hD hNL hNP hPl hP1 hp hc hp4 hp3
  have hTO : TotallyOpposite D p c := (totallyOpposite_iff_not_mem_nbhd_three hD hNL hc hp).2 hp3
  have hord := fun i => orders_of_near h hNL hNP hPl hP1 hc hp hp4 hp3 (hx i) (hx3 i)
  have hconj : ∀ g : G, ∀ y ∈ D, g * y * g⁻¹ ∈ D := fun g y hy => h.conj_mem g hy
  have hx₃ : ∀ i, ![x 0, x 1, x 2] i ∈ D := fun i => by fin_cases i <;> exact (hx _).1
  have hxd₃ : ∀ i, Commute p (![x 0, x 1, x 2] i) := fun i => by
    fin_cases i <;> exact (hx _).2.1
  have hxdD₃ : ∀ i, p * ![x 0, x 1, x 2] i ∈ D := fun i => by fin_cases i <;> exact (hx _).2.2
  have hne₃ : ∀ i j, i ≠ j → ![x 0, x 1, x 2] j ≠ ![x 0, x 1, x 2] i ∧
      ![x 0, x 1, x 2] j ≠ p * ![x 0, x 1, x 2] i := fun i j hij => by
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact hne _ _ (by decide)
  have hx3₃ : ∀ i, orderOf (c * ![x 0, x 1, x 2] i) = 3 := fun i => by
    fin_cases i <;> exact (hord _).1
  have hx5₃ : ∀ i, orderOf (c * (p * ![x 0, x 1, x 2] i)) = 5 := fun i => by
    fin_cases i <;> exact (hord _).2
  have hcfg := lineConfig_of_lines' hD hconj hNL hNP hPl hp hc h5 hx₃ hxd₃ hxdD₃ hne₃ hx3₃ hx5₃
  obtain ⟨-, hyD, hyd, hydD, -, -, huK, hu⟩ :=
    fivePoints_spec h hNP hp hc h5 hTO hcfg hx₃ hxd₃ hxdD₃ hx3₃ hx5₃
  set y := fivePoints hcfg with hy
  have hcK : c ∈ (threeLinesHom hcfg).range := ⟨_, threeLinesHom_one hcfg⟩
  have hy0' : y 0 = x 0 := rfl
  have hy1' : y 1 = x 1 := rfl
  have hy2' : y 2 = x 2 := rfl
  have hon : ∀ j : Fin 6, 3 ≤ j.val →
      (x j = y 3 ∨ x j = p * y 3) ∨ (x j = y 4 ∨ x j = p * y 4) := by
    intro j hj
    obtain ⟨i, hi⟩ := eq_line_of_five' h hNL hNP hPl hp hc h5 hyD hyd hydD hu (huK c hcK)
      (hx j).1 (hx j).2.1 (hx j).2.2 (hord j).1
    have hlow : ∀ k : Fin 6, k.val < 3 → ¬ (x j = x k ∨ x j = p * x k) := by
      intro k hk hjk
      have hkj : k ≠ j := fun e => by omega
      rcases hjk with e | e
      · exact (hne k j hkj).1 e
      · exact (hne k j hkj).2 e
    fin_cases i
    · exact absurd (by rw [← hy0']; exact hi) (hlow 0 (by decide))
    · exact absurd (by rw [← hy1']; exact hi) (hlow 1 (by decide))
    · exact absurd (by rw [← hy2']; exact hi) (hlow 2 (by decide))
    · exact .inl hi
    · exact .inr hi
  have hsame : ∀ a b : Fin 6, a ≠ b → ∀ k : Fin 5, (x a = y k ∨ x a = p * y k) →
      (x b = y k ∨ x b = p * y k) → False := by
    intro a b hab k ha hb
    rcases same_line hp2 ha hb with e | e
    · exact (hne a b hab).1 e
    · exact (hne a b hab).2 e
  rcases hon 3 (by decide) with h3 | h3 <;> rcases hon 4 (by decide) with h4 | h4 <;>
    rcases hon 5 (by decide) with h5' | h5'
  · exact hsame 3 4 (by decide) 3 h3 h4
  · exact hsame 3 4 (by decide) 3 h3 h4
  · exact hsame 3 5 (by decide) 3 h3 h5'
  · exact hsame 4 5 (by decide) 4 h4 h5'
  · exact hsame 4 5 (by decide) 3 h4 h5'
  · exact hsame 3 5 (by decide) 4 h3 h5'
  · exact hsame 3 4 (by decide) 4 h3 h4
  · exact hsame 3 4 (by decide) 4 h3 h4

theorem isSporadicJ2_of_three_near {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hNP : NoPolar D) (hNL : NoLevi D) (hPl : ExcNoPlane D) (hP1 : ExcP1 D) {c p : G}
    (hc : c ∈ D) (hp : p ∈ D) (hp4 : p ∈ nbhd D c 4) (hp3 : p ∉ nbhd D c 3) {x : Fin 3 → G}
    (hx : ∀ i, x i ∈ collinearSet D p) (hx3 : ∀ i, x i ∈ nbhd D c 3)
    (hne : ∀ i j, i ≠ j → x j ≠ x i ∧ x j ≠ p * x i)
    (h10 : (collinearSet D p).ncard = 10) : NativeSporadic.IsSporadic G .J2 := by
  have := h.finite
  have hD := h.root
  have hconj : ∀ g : G, ∀ y ∈ D, g * y * g⁻¹ ∈ D := fun g y hy => h.conj_mem g hy
  have hp2 := hD.mul_self_eq_one hp
  have h5 := orderOf_eq_five_of_mem_nbhd_four h.isClass hD hNL hNP hPl hP1 hp hc hp4 hp3
  have hTO : TotallyOpposite D p c := (totallyOpposite_iff_not_mem_nbhd_three hD hNL hc hp).2 hp3
  have hord := fun i => orders_of_near h hNL hNP hPl hP1 hc hp hp4 hp3 (hx i) (hx3 i)
  obtain ⟨K, y, hpK, hcK, hyK, -, -, -, hyD, hyd, hydD, hyne, hy3, hy5, huK, hu⟩ :=
    exists_five_lines' h hNL hNP hPl hp hc h5 hTO (fun i => (hx i).1) (fun i => (hx i).2.1)
      (fun i => (hx i).2.2) hne (fun i => (hord i).1) (fun i => (hord i).2)
  have hinj1 : Function.Injective y := fun i j hij => by
    by_contra hij'
    exact (hyne i j hij').1 hij.symm
  have hinj2 : Function.Injective fun i => p * y i := fun i j hij =>
    hinj1 (mul_left_cancel hij)
  have hdisj : Disjoint (Set.range y) (Set.range fun i => p * y i) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    by_cases hij : i = j
    · subst hij
      exact hD.ne_one hp (mul_eq_right.1 hj)
    · exact (hyne j i (Ne.symm hij)).2 hj.symm
  have hsub : Set.range y ∪ Set.range (fun i => p * y i) ⊆ collinearSet D p := by
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨hyD i, hyd i, hydD i⟩
    · exact ⟨hydD i, (Commute.refl p).mul_right (hyd i),
        by rw [mul_mul_self_cancel' hp2]; exact hyD i⟩
  have hcard : (Set.range y ∪ Set.range (fun i => p * y i)).ncard = 10 := by
    rw [Set.ncard_union_eq hdisj, Set.ncard_range_of_injective hinj1,
      Set.ncard_range_of_injective hinj2, Nat.card_eq_fintype_card, Fintype.card_fin]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [h10, hcard])
  have hlines : LinesAt D p c y := by
    refine ⟨hyD, hyd, hydD, hyne, hy3, fun f hf hpf => ?_⟩
    by_cases hfp : f = p
    · exact .inl hfp
    · right
      have hfL : f ∈ collinearSet D p := ⟨hf, hpf, hNP p hp f hf hpf (Ne.symm hfp)⟩
      rw [← heq] at hfL
      rcases hfL with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨i, .inl rfl⟩
      · exact ⟨i, .inr rfl⟩
  have hcfg := lineConfig_of_lines' hD hconj hNL hNP hPl hp hc h5 hyD hyd hydD hyne hy3 hy5
  have hconn := Bridge.commConnected_of_noPolar
    (Bridge.asc73Input_of_theoremTwo CFSG.ShultStronglyClosedTI.theoremTwo) h hNP
  have hdH : p ∈ Subgroup.closure (insert p (insert c (Set.range y))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hcH : c ∈ Subgroup.closure (insert p (insert c (Set.range y))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hyH : ∀ i, y i ∈ Subgroup.closure (insert p (insert c (Set.range y))) := fun i =>
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
  have hconj' := fun i => (hcfg.subgroup hdH hcH hyH).isConj i
  have htop := closure_eq_top_of_isConj h hconn hp hlines fun i =>
    ⟨exists_mem_of_isConj (hconj' i).1, exists_mem_of_isConj (hconj' i).2⟩
  have hK : K = ⊤ := by
    rw [eq_top_iff, ← htop, Subgroup.closure_le]
    rintro g (rfl | rfl | ⟨i, rfl⟩)
    · exact hpK
    · exact hcK
    · exact hyK i
  have hcen : y 0 * y 1 * y 2 * y 3 * y 4 ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact (huK g (hK ▸ Subgroup.mem_top g)).eq.symm
  rw [h.center_eq_bot, Subgroup.mem_bot] at hcen
  have hpc1 : p * c ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at h5
    exact absurd h5 (by norm_num)
  exact (j2Endgame G p c y hcfg hcen hpc1 htop).2

end CFSG.Timmesfeld.Moufang.Deep
