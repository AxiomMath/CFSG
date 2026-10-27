module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFixRMod2
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.Quasithin.H13.L32A.E9

open CFSG.Quasithin CFSG.Quasithin.FixR

variable {W : Type} [CommGroup W]

@[expose] def nu3Hom (g : MulAut W) : W →* W where
  toFun w := w * g w * g (g w)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]; ac_rfl

theorem nu3Hom_apply (g : MulAut W) (w : W) : nu3Hom g w = w * g w * g (g w) := rfl

theorem apply_three {g : MulAut W} (hg : g ^ 3 = 1) (w : W) : g (g (g w)) = w := by
  have h := congrArg (fun f : MulAut W => f w) hg
  simpa only [pow_three, MulAut.mul_apply, MulAut.one_apply] using h

theorem mul_self_eq_one (hW : ∀ w : W, w ^ 2 = 1) (a : W) : a * a = 1 := by
  rw [← sq]
  exact hW a

theorem apply_comm {g h : MulAut W} (hc : h * g = g * h) (v : W) : h (g v) = g (h v) := by
  have := congrArg (fun f : MulAut W => f v) hc
  simpa only [MulAut.mul_apply] using this

theorem nu3_fixed {g : MulAut W} (hg : g ^ 3 = 1) (w : W) : g (nu3Hom g w) = nu3Hom g w := by
  rw [nu3Hom_apply, map_mul, map_mul, apply_three hg]
  ac_rfl

theorem nu3_comm {g h : MulAut W} (hc : h * g = g * h) (w : W) :
    h (nu3Hom g w) = nu3Hom g (h w) := by
  simp only [nu3Hom_apply, map_mul, apply_comm hc]

theorem nu3_nu3 {x y : MulAut W} (hxy : x * y = y * x) (w : W) :
    nu3Hom x (nu3Hom y w) = nu3Hom y (nu3Hom x w) := by
  rw [nu3Hom_apply x (nu3Hom y w), nu3_comm hxy w, nu3_comm hxy (x w), nu3Hom_apply x w, map_mul,
    map_mul]

theorem nu3_nu3_self (hW : ∀ w : W, w ^ 2 = 1) {g : MulAut W} (hg : g ^ 3 = 1) (w : W) :
    nu3Hom g (nu3Hom g w) = nu3Hom g w := by
  rw [nu3Hom_apply g (nu3Hom g w), nu3_fixed hg, nu3_fixed hg, mul_self_eq_one hW, one_mul]

theorem mem_commSub_of_nu3_eq_one (hW : ∀ w : W, w ^ 2 = 1) {g : MulAut W} {U : Subgroup W}
    {w : W} (hwU : w ∈ U) (hw : nu3Hom g w = 1) : w ∈ commSub U (Subgroup.zpowers g) := by
  have hinv : ∀ a : W, a⁻¹ = a := fun a => inv_eq_self_of_sq hW a
  have h2 : w * (g w * g (g w)) = 1 := by rw [← mul_assoc]; exact hw
  have h3 : w = g w * g (g w) := (eq_inv_of_mul_eq_one_left h2).trans (hinv _)
  have h1 : w = g w * w⁻¹ * ((g * g) w * w⁻¹) := by
    rw [hinv w, MulAut.mul_apply]
    calc w = g w * g (g w) := h3
      _ = g w * g (g w) * (w * w) := by rw [mul_self_eq_one hW w, mul_one]
      _ = g w * w * (g (g w) * w) := by rw [mul_mul_mul_comm]
  rw [h1]
  refine (commSub U _).mul_mem (Subgroup.subset_closure ⟨g, Subgroup.mem_zpowers g, w, hwU, rfl⟩)
    (Subgroup.subset_closure ⟨g * g, ?_, w, hwU, rfl⟩)
  exact (Subgroup.zpowers g).mul_mem (Subgroup.mem_zpowers g) (Subgroup.mem_zpowers g)

theorem mem_commV_of_nu3_eq_one (hW : ∀ w : W, w ^ 2 = 1) {g : MulAut W} {w : W}
    (hw : nu3Hom g w = 1) : w ∈ commV (Subgroup.zpowers g) := by
  rw [commV_eq_commSub]
  exact mem_commSub_of_nu3_eq_one hW (Subgroup.mem_top w) hw

theorem commV_le_ker_nu3 {g : MulAut W} (hg : g ^ 3 = 1) :
    commV (Subgroup.zpowers g) ≤ (nu3Hom g).ker := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨x, hx, v, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← nu3_comm ((Commute.zpow_left (Commute.refl g) k).eq) v]
  exact (mem_fixV_zpowers_iff.mpr (nu3_fixed hg v)) _
    (Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) k)

theorem nu3_mem_commV (P : Subgroup (MulAut W)) {g : MulAut W} (hg : g ∈ P) {w : W}
    (hw : w ∈ commV P) : nu3Hom g w ∈ commV P := by
  have h1 : g w ∈ commV P := apply_mem_commV P (Subgroup.le_normalizer hg) hw
  have h2 : g (g w) ∈ commV P := apply_mem_commV P (Subgroup.le_normalizer hg) h1
  rw [nu3Hom_apply]
  exact (commV P).mul_mem ((commV P).mul_mem hw h1) h2

theorem commV_mono' {P Q : Subgroup (MulAut W)} (h : P ≤ Q) : commV P ≤ commV Q := by
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, hx, v, rfl⟩
  exact ⟨x, h hx, v, rfl⟩

theorem eq_one_of_fixed_of_mem_commV9 (hW : ∀ w : W, w ^ 2 = 1) (P : Subgroup (MulAut W))
    [Fintype ↥P] (hP : Fintype.card ↥P = 9) {w : W} (hw : w ∈ commV P)
    (hfix : ∀ κ ∈ P, κ w = w) : w = 1 := by
  have h1 : normHom P w = 1 := commV_le_ker_normHom P hw
  have h2 : normHom P w = w ^ 9 := by
    rw [FixR.normHom_apply]
    simp only [fun κ : ↥P => hfix κ κ.2, Finset.prod_const, Finset.card_univ, hP]
  rw [h2] at h1
  have h3 : w ^ 9 = w := by
    have : w ^ 9 = (w ^ 2) ^ 4 * w := by rw [← pow_mul, ← pow_succ]
    rw [this, hW w, one_pow, one_mul]
  rw [← h3, h1]

theorem tp_inf_tp9 (hW : ∀ w : W, w ^ 2 = 1) (P L L' : Subgroup (MulAut W)) [Fintype ↥P]
    (hP : Fintype.card ↥P = 9) (hsup : L ⊔ L' = P) : tp P L ⊓ tp P L' = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hw, hw'⟩
  have hfix := fix_of_le_sup hw.1 hw'.1
  rw [hsup] at hfix
  exact Subgroup.mem_bot.mpr (eq_one_of_fixed_of_mem_commV9 hW P hP hw.2 hfix)

theorem sup_eq_of_ne9 [Finite W] {P L L' : Subgroup (MulAut W)} [Fintype ↥P]
    (hP : Fintype.card ↥P = 9) (hL : L ≤ P) (hL' : L' ≤ P) (h3 : Nat.card L = 3)
    (h3' : Nat.card L' = 3) (hne : L ≠ L') : L ⊔ L' = P := by
  have hP' : Nat.card P = 9 := by rw [Nat.card_eq_fintype_card, hP]
  have hle : L ⊔ L' ≤ P := sup_le hL hL'
  have hd1 : Nat.card L ∣ Nat.card ↥(L ⊔ L') := Subgroup.card_dvd_of_le le_sup_left
  have hd2 : Nat.card ↥(L ⊔ L') ∣ Nat.card P := Subgroup.card_dvd_of_le hle
  rw [hP'] at hd2
  rw [h3] at hd1
  by_cases h9 : Nat.card ↥(L ⊔ L') = 9
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hP', h9])
  · have h3s : Nat.card ↥(L ⊔ L') = 3 := by
      have : Nat.card ↥(L ⊔ L') ∈ Nat.divisors 9 := by simp [hd2]
      have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
      rw [hdiv] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h
      · rw [h] at hd1; omega
      · exact h
      · exact absurd h h9
    have e1 : L = L ⊔ L' := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3, h3s])
    have e2 : L' = L ⊔ L' := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h3', h3s])
    exact absurd (e1.trans e2.symm) hne

theorem zpowers_eq_of_card_three [Finite W] {L : Subgroup (MulAut W)} (h3 : Nat.card L = 3)
    {κ : MulAut W} (hκ : κ ∈ L) (hκ1 : κ ≠ 1) : Subgroup.zpowers κ = L := by
  have hle : Subgroup.zpowers κ ≤ L := (Subgroup.zpowers_le).mpr hκ
  have hdvd : Nat.card ↥(Subgroup.zpowers κ) ∣ 3 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [h3] at this
  have hne : Nat.card ↥(Subgroup.zpowers κ) ≠ 1 := by
    intro h1
    rw [Nat.card_zpowers] at h1
    exact hκ1 (orderOf_eq_one_iff.mp h1)
  have h3' : Nat.card ↥(Subgroup.zpowers κ) = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h3, h3'])

theorem exists_ne_one_of_card_three {L : Subgroup (MulAut W)} (h3 : Nat.card L = 3) :
    ∃ κ ∈ L, κ ≠ 1 := by
  by_contra h
  push Not at h
  have : L = ⊥ := (Subgroup.eq_bot_iff_forall L).mpr h
  rw [this] at h3
  simp at h3

theorem four_le_card_tp [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {P L : Subgroup (MulAut W)}
    [Fintype ↥P] (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP : Fintype.card ↥P = 9)
    (hL : L ≤ P) (hne : tp P L ≠ ⊥) : 4 ≤ Nat.card (tp P L) := by
  have hP' : Nat.card P = 9 := by rw [Nat.card_eq_fintype_card, hP]
  have hPg : IsPGroup 3 ↥P := IsPGroup.of_card (n := 2) (by rw [hP']; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : MulAction ↥P ↥(tp P L) :=
    { smul := fun κ s => ⟨(κ : MulAut W) s, smul_mem_tp hPc hL κ.2 s.2⟩
      one_smul := fun s => Subtype.ext rfl
      mul_smul := fun a b s => Subtype.ext rfl }
  have hmod := hPg.card_modEq_card_fixedPoints ↥(tp P L)
  have hfix : MulAction.fixedPoints ↥P ↥(tp P L) = {1} := by
    ext s
    simp only [Set.mem_singleton_iff, MulAction.mem_fixedPoints]
    constructor
    · intro h
      apply Subtype.ext
      refine eq_one_of_fixed_of_mem_commV9 hW P hP (tp_le_commV P L s.2) (fun κ hκ => ?_)
      exact congrArg Subtype.val (h ⟨κ, hκ⟩)
    · intro h κ
      rw [h]
      exact Subtype.ext (map_one _)
  have h1 : Nat.card (MulAction.fixedPoints ↥P ↥(tp P L)) = 1 := by
    rw [hfix]
    simp
  rw [h1] at hmod
  have hcard : Nat.card (tp P L) = 2 ^ rk (tp P L) := card_eq_two_pow hW _
  have hrk : rk (tp P L) ≠ 0 := fun h0 => hne ((rk_eq_zero_iff hW).mp h0)
  rw [hcard] at hmod ⊢
  by_contra hlt
  have hd : rk (tp P L) < 2 := by
    by_contra h
    exact hlt (by calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ rk (tp P L) := Nat.pow_le_pow_right (by norm_num) (not_lt.mp h))
  generalize rk (tp P L) = d at hmod hrk hd
  interval_cases d <;> simp [Nat.ModEq] at hmod hrk

theorem tp_le_ker_nu3 [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {P : Subgroup (MulAut W)}
    [Fintype ↥P] (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP : Fintype.card ↥P = 9)
    {c : MulAut W} (hc : c ∈ P) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) {L : Subgroup (MulAut W)}
    (hL : L ≤ P) (hLc : Nat.card L = 3) (hne : Subgroup.zpowers c ≠ L) :
    tp P L ≤ (nu3Hom c).ker := by
  intro w hw
  rw [MonoidHom.mem_ker]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3' : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hMc : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hc3']
  have hMP : Subgroup.zpowers c ≤ P := (Subgroup.zpowers_le).mpr hc
  have hsup : Subgroup.zpowers c ⊔ L = P := sup_eq_of_ne9 hP hMP hL hMc hLc hne
  have hzq : c (nu3Hom c w) = nu3Hom c w := nu3_fixed hc3 w
  have hzL : ∀ l ∈ L, l (nu3Hom c w) = nu3Hom c w := fun l hl => by
    rw [nu3_comm (hPc l (hL hl) c hc) w, hw.1 l hl]
  have hzM : ∀ x ∈ Subgroup.zpowers c, x (nu3Hom c w) = nu3Hom c w := by
    have : Subgroup.zpowers c ≤ MulAction.stabilizer (MulAut W) (nu3Hom c w) :=
      (Subgroup.zpowers_le).mpr hzq
    exact fun x hx => this hx
  have hzP : ∀ x ∈ P, x (nu3Hom c w) = nu3Hom c w := by
    have := fix_of_le_sup hzM hzL
    rwa [hsup] at this
  exact eq_one_of_fixed_of_mem_commV9 hW P hP (nu3_mem_commV P hc hw.2) hzP

theorem tp_sup_inf9 [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {P L₁ L₂ L₃ : Subgroup (MulAut W)}
    [Fintype ↥P] (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP : Fintype.card ↥P = 9)
    (h₁ : L₁ ≤ P) (h₂ : L₂ ≤ P) (h₃ : L₃ ≤ P) (c₁ : Nat.card L₁ = 3) (c₂ : Nat.card L₂ = 3)
    (c₃ : Nat.card L₃ = 3) (n₁₂ : L₁ ≠ L₂) (n₁₃ : L₁ ≠ L₃) (n₂₃ : L₂ ≠ L₃) :
    tp P L₃ ⊓ (tp P L₁ ⊔ tp P L₂) = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hw3, hw12⟩
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.mp hw12
  obtain ⟨κ, hκL, hκ1⟩ := exists_ne_one_of_card_three c₁
  have hκP : κ ∈ P := h₁ hκL
  have hu3 : κ (w₁ * w₂) * (w₁ * w₂)⁻¹ ∈ tp P L₃ :=
    (tp P L₃).mul_mem (smul_mem_tp hPc h₃ hκP hw3) ((tp P L₃).inv_mem hw3)
  have hfix1 : κ w₁ = w₁ := hw₁.1 κ hκL
  have hu2 : κ (w₁ * w₂) * (w₁ * w₂)⁻¹ = κ w₂ * w₂⁻¹ := by
    rw [map_mul, hfix1, mul_inv_rev]
    calc w₁ * κ w₂ * (w₂⁻¹ * w₁⁻¹) = (w₁ * w₁⁻¹) * (κ w₂ * w₂⁻¹) := by ac_rfl
      _ = κ w₂ * w₂⁻¹ := by rw [mul_inv_cancel, one_mul]
  have hu2' : κ w₂ * w₂⁻¹ ∈ tp P L₂ :=
    (tp P L₂).mul_mem (smul_mem_tp hPc h₂ hκP hw₂) ((tp P L₂).inv_mem hw₂)
  have hbot23 : tp P L₂ ⊓ tp P L₃ = ⊥ :=
    tp_inf_tp9 hW P L₂ L₃ hP (sup_eq_of_ne9 hP h₂ h₃ c₂ c₃ n₂₃)
  have hc : κ w₂ * w₂⁻¹ = 1 := by
    have : κ w₂ * w₂⁻¹ ∈ tp P L₂ ⊓ tp P L₃ := ⟨hu2', hu2 ▸ hu3⟩
    rw [hbot23] at this
    exact Subgroup.mem_bot.mp this
  have hκw₂ : κ w₂ = w₂ := mul_inv_eq_one.mp hc
  have hzp : Subgroup.zpowers κ = L₁ := zpowers_eq_of_card_three c₁ hκL hκ1
  have hfL₁ : ∀ x ∈ L₁, x w₂ = w₂ := by
    have : Subgroup.zpowers κ ≤ MulAction.stabilizer (MulAut W) w₂ :=
      (Subgroup.zpowers_le).mpr hκw₂
    intro x hx
    rw [← hzp] at hx
    exact this hx
  have hfixP : ∀ x ∈ P, x w₂ = w₂ := by
    have := fix_of_le_sup hfL₁ hw₂.1
    rwa [sup_eq_of_ne9 hP h₁ h₂ c₁ c₂ n₁₂] at this
  have hw₂1 : w₂ = 1 := eq_one_of_fixed_of_mem_commV9 hW P hP (tp_le_commV P L₂ hw₂) hfixP
  subst hw₂1
  have hbot13 : tp P L₁ ⊓ tp P L₃ = ⊥ :=
    tp_inf_tp9 hW P L₁ L₃ hP (sup_eq_of_ne9 hP h₁ h₃ c₁ c₃ n₁₃)
  have : w₁ ∈ tp P L₁ ⊓ tp P L₃ := ⟨hw₁, by simpa using hw3⟩
  rw [hbot13] at this
  simpa using this

theorem fixed_mul_nu3 (hW : ∀ w : W, w ^ 2 = 1) {x y : MulAut W} (hy : y ^ 3 = 1)
    (hxy : x * y = y * x) {u : W} (hux : nu3Hom x u = 1) (huy : nu3Hom y u = 1) :
    (x * y * y) (u * nu3Hom (x * y) u) = u * nu3Hom (x * y) u := by
  have hsq := mul_self_eq_one hW
  have hinv : ∀ a : W, a⁻¹ = a := fun a => inv_eq_self_of_sq hW a
  have hc : ∀ v, x (y v) = y (x v) := apply_comm hxy
  have key : ∀ (g : MulAut W) (v : W), nu3Hom g v = 1 → g (g v) = v * g v := by
    intro g v h
    rw [nu3Hom_apply] at h
    rw [eq_inv_of_mul_eq_one_right h, hinv]
  have hR1 : x (x u) = u * x u := key x u hux
  have hR2 : y (y u) = u * y u := key y u huy
  have hR3 : x (x (y u)) = y u * x (y u) := by
    refine key x (y u) ?_
    rw [← nu3_comm hxy.symm u, hux, map_one]
  have hxxyy : x (x (y (y u))) = u * x u * (y u * x (y u)) := by
    rw [hR2, map_mul, map_mul, hR1, hR3]
  have hs : u * nu3Hom (x * y) u = u * x u * y u := by
    rw [nu3Hom_apply]
    simp only [MulAut.mul_apply]
    rw [← hc (y u), hxxyy]
    calc u * (u * x (y u) * (u * x u * (y u * x (y u))))
        = (u * u) * (x (y u) * x (y u)) * (u * x u * y u) := by ac_rfl
      _ = u * x u * y u := by rw [hsq, hsq, one_mul, one_mul]
  have e1 : x (y (y u)) = x u * x (y u) := by rw [hR2, map_mul]
  have e2 : x (y (y (x u))) = u * x u * (y u * x (y u)) := by
    rw [← hc u, ← hc (y u), hxxyy]
  have e3 : x (y (y (y u))) = x u := by rw [apply_three hy]
  have hgoal : (x * y * y) (u * x u * y u) =
      x (y (y u)) * x (y (y (x u))) * x (y (y (y u))) := by
    simp only [MulAut.mul_apply, map_mul]
  rw [hs, hgoal, e1, e2, e3]
  calc x u * x (y u) * (u * x u * (y u * x (y u))) * x u
      = (x u * x u) * (x (y u) * x (y u)) * (u * x u * y u) := by ac_rfl
    _ = u * x u * y u := by rw [hsq, hsq, one_mul, one_mul]

theorem decomp (hW : ∀ w : W, w ^ 2 = 1) {x y : MulAut W} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : x * y = y * x) {w : W} (hw : nu3Hom x w = 1) :
    y (nu3Hom y w) = nu3Hom y w ∧
      (x * y) (nu3Hom (x * y) (w * nu3Hom y w)) = nu3Hom (x * y) (w * nu3Hom y w) ∧
      (x * y * y) (w * nu3Hom y w * nu3Hom (x * y) (w * nu3Hom y w)) =
        w * nu3Hom y w * nu3Hom (x * y) (w * nu3Hom y w) ∧
      w = nu3Hom y w * nu3Hom (x * y) (w * nu3Hom y w) *
        (w * nu3Hom y w * nu3Hom (x * y) (w * nu3Hom y w)) := by
  have hsq := mul_self_eq_one hW
  have hxy3 : (x * y) ^ 3 = 1 := by rw [(Commute.mul_pow hxy 3), hx, hy, one_mul]
  have hux : nu3Hom x (w * nu3Hom y w) = 1 := by
    rw [map_mul, hw, nu3_nu3 hxy, hw, map_one, one_mul]
  have huy : nu3Hom y (w * nu3Hom y w) = 1 := by
    rw [map_mul, nu3_nu3_self hW hy, hsq]
  refine ⟨nu3_fixed hy w, nu3_fixed hxy3 _, fixed_mul_nu3 hW hy hxy hux huy, ?_⟩
  calc w = (nu3Hom y w * nu3Hom y w) *
        (nu3Hom (x * y) (w * nu3Hom y w) * nu3Hom (x * y) (w * nu3Hom y w)) * w := by
        rw [hsq, hsq, one_mul, one_mul]
    _ = nu3Hom y w * nu3Hom (x * y) (w * nu3Hom y w) *
        (w * nu3Hom y w * nu3Hom (x * y) (w * nu3Hom y w)) := by ac_rfl

theorem false_of_tp_eq_bot [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {P : Subgroup (MulAut W)}
    (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP3 : ∀ κ ∈ P, κ ^ 3 = 1) {x y : MulAut W}
    (hxP : x ∈ P) (hyP : y ∈ P) (hyx : y ∉ Subgroup.zpowers x)
    (h1 : tp P (Subgroup.zpowers x) = ⊥) (h2 : tp P (Subgroup.zpowers y) = ⊥)
    (h3 : tp P (Subgroup.zpowers (x * y)) = ⊥) : False := by
  have hsq := mul_self_eq_one hW
  have hxy : x * y = y * x := hPc x hxP y hyP
  have hx3 := hP3 x hxP
  have hy3 := hP3 y hyP
  have hxyP : x * y ∈ P := P.mul_mem hxP hyP
  have hyxP : y * x ∈ P := P.mul_mem hyP hxP
  have hc : ∀ v, x (y v) = y (x v) := apply_comm hxy
  have hx3' : ∀ v, x (x (x v)) = v := apply_three hx3
  have piece : ∀ {g : MulAut W}, g ∈ P → tp P (Subgroup.zpowers g) = ⊥ → ∀ {v : W},
      v ∈ commV P → g (nu3Hom g v) = nu3Hom g v → nu3Hom g v = 1 := by
    intro g hg hbot v hv hfix
    have hm : nu3Hom g v ∈ tp P (Subgroup.zpowers g) :=
      ⟨mem_fixV_zpowers_iff.mpr hfix, nu3_mem_commV P hg hv⟩
    rw [hbot] at hm
    exact Subgroup.mem_bot.mp hm
  have hA : ∀ w ∈ commV (Subgroup.zpowers x), (x * y * y) w = w := by
    intro w hw
    have hwP : w ∈ commV P := commV_mono' ((Subgroup.zpowers_le).mpr hxP) hw
    obtain ⟨d1, d2, d3, -⟩ := decomp hW hx3 hy3 hxy (commV_le_ker_nu3 hx3 hw)
    have e1 : nu3Hom y w = 1 := piece hyP h2 hwP d1
    have e2 : nu3Hom (x * y) (w * nu3Hom y w) = 1 :=
      piece hxyP h3 ((commV P).mul_mem hwP (nu3_mem_commV P hyP hwP)) d2
    rw [e2, e1] at d3
    simpa only [mul_one] using d3
  have hB : ∀ w ∈ commV (Subgroup.zpowers y), (x * y * y) w = w := by
    intro w hw
    have hwP : w ∈ commV P := commV_mono' ((Subgroup.zpowers_le).mpr hyP) hw
    obtain ⟨d1, d2, d3, -⟩ := decomp hW hy3 hx3 hxy.symm (commV_le_ker_nu3 hy3 hw)
    have h3' : tp P (Subgroup.zpowers (y * x)) = ⊥ := by rw [← hxy]; exact h3
    have e1 : nu3Hom x w = 1 := piece hxP h1 hwP d1
    have e2 : nu3Hom (y * x) (w * nu3Hom x w) = 1 :=
      piece hyxP h3' ((commV P).mul_mem hwP (nu3_mem_commV P hxP hwP)) d2
    rw [e2, e1] at d3
    have d3' : (y * x * x) w = w := by simpa only [mul_one] using d3
    calc (x * y * y) w = y (y (x w)) := by
          simp only [MulAut.mul_apply]
          rw [hc, hc]
      _ = (y * x * x) ((y * x * x) w) := by
          simp only [MulAut.mul_apply]
          rw [hc, hx3', hc]
      _ = w := by rw [d3', d3']
  have hz2 : ∀ v : W, (x * y * y) ((x * y * y) v) = v := by
    intro v
    set u := x (y (y v)) * (y (y v))⁻¹ * ((y * y) v * v⁻¹) with hu
    have ha : x (y (y v)) * (y (y v))⁻¹ ∈ commV (Subgroup.zpowers x) :=
      Subgroup.subset_closure ⟨x, Subgroup.mem_zpowers x, y (y v), rfl⟩
    have hb : (y * y) v * v⁻¹ ∈ commV (Subgroup.zpowers y) :=
      Subgroup.subset_closure ⟨y * y, (Subgroup.zpowers y).mul_mem (Subgroup.mem_zpowers y)
        (Subgroup.mem_zpowers y), v, rfl⟩
    have hzu : (x * y * y) u = u := by
      rw [hu, map_mul, hA _ ha, hB _ hb]
    have hzv : (x * y * y) v = u * v := by
      rw [hu]
      simp only [MulAut.mul_apply]
      group
    rw [hzv, map_mul, hzu, hzv, ← mul_assoc, hsq, one_mul]
  have hzz : (x * y * y) * (x * y * y) = 1 := MulEquiv.ext fun v => hz2 v
  have hz3 : (x * y * y) ^ 3 = 1 := by
    have hc2 : Commute x (y * y) := Commute.mul_right hxy hxy
    rw [mul_assoc, Commute.mul_pow hc2 3, hx3, one_mul, ← sq, ← pow_mul, mul_comm, pow_mul, hy3,
      one_pow]
  have hz1 : x * y * y = 1 := by
    generalize x * y * y = z at hz3 hzz ⊢
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, hzz, inv_one, one_mul]
  apply hyx
  have hyy : y * y = x⁻¹ := by
    have : x * (y * y) = 1 := by rw [← mul_assoc]; exact hz1
    exact eq_inv_of_mul_eq_one_right this
  have hy4 : y = (y * y) * (y * y) := by
    calc y = y * y ^ 3 := by rw [hy3, mul_one]
      _ = (y * y) * (y * y) := by rw [pow_three]; simp only [mul_assoc]
  rw [hy4, hyy]
  exact (Subgroup.zpowers x).mul_mem (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
    (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))

end CFSG.Quasithin.H13.L32A.E9
