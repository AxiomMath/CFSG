module

public import CFSG.Quasithin.Background.FixVTransport
public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.FixR

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

@[expose] noncomputable def normHom (P : Subgroup (MulAut W)) [Fintype ↥P] : W →* W where
  toFun w := ∏ κ : ↥P, (κ : MulAut W) w
  map_one' := by simp
  map_mul' a b := by simp [Finset.prod_mul_distrib]

theorem normHom_apply (P : Subgroup (MulAut W)) [Fintype ↥P] (w : W) :
    normHom P w = ∏ κ : ↥P, (κ : MulAut W) w := rfl

theorem normHom_smul (P : Subgroup (MulAut W)) [Fintype ↥P] {x : MulAut W} (hx : x ∈ P) (w : W) :
    normHom P (x w) = normHom P w := by
  rw [normHom_apply, normHom_apply]
  exact Fintype.prod_equiv (Equiv.mulRight (⟨x, hx⟩ : ↥P)) _ _ (fun κ => rfl)

theorem commV_le_ker_normHom (P : Subgroup (MulAut W)) [Fintype ↥P] :
    commV P ≤ (normHom P).ker := by
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro _ ⟨x, hx, v, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, normHom_smul P hx, mul_inv_cancel]

theorem eq_one_of_fixed_of_mem_commV (hW : ∀ w : W, w ^ 2 = 1) (P : Subgroup (MulAut W))
    [Fintype ↥P] (hP : Fintype.card ↥P = 25) {w : W} (hw : w ∈ commV P)
    (hfix : ∀ κ ∈ P, κ w = w) : w = 1 := by
  have h1 : normHom P w = 1 := commV_le_ker_normHom P hw
  have h2 : normHom P w = w ^ 25 := by
    rw [normHom_apply]
    simp only [fun κ : ↥P => hfix κ κ.2, Finset.prod_const, Finset.card_univ, hP]
  rw [h2] at h1
  have h3 : w ^ 25 = w := by
    have : w ^ 25 = (w ^ 2) ^ 12 * w := by rw [← pow_mul, ← pow_succ]
    rw [this, hW w, one_pow, one_mul]
  rw [← h3, h1]

@[expose] def tp (P L : Subgroup (MulAut W)) : Subgroup W := fixV L ⊓ commV P

theorem tp_le_commV (P L : Subgroup (MulAut W)) : tp P L ≤ commV P := inf_le_right

theorem map_commV_le (P : Subgroup (MulAut W)) {γ : MulAut W}
    (hγ : γ ∈ Subgroup.normalizer (P : Set (MulAut W))) :
    (commV P).map γ.toMonoidHom ≤ commV P := by
  rw [commV, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨c, ⟨x, hx, v, rfl⟩, rfl⟩
  refine ⟨γ * x * γ⁻¹, (Subgroup.mem_normalizer_iff.mp hγ x).mp hx, γ v, ?_⟩
  simp [MulAut.mul_apply]

theorem map_commV (P : Subgroup (MulAut W)) {γ : MulAut W}
    (hγ : γ ∈ Subgroup.normalizer (P : Set (MulAut W))) :
    (commV P).map γ.toMonoidHom = commV P := by
  refine le_antisymm (map_commV_le P hγ) fun c hc => ?_
  have h1 := map_commV_le P (Subgroup.inv_mem _ hγ) ⟨c, hc, rfl⟩
  exact ⟨γ⁻¹ c, by simpa using h1, by simp⟩

theorem fixV_conj (L : Subgroup (MulAut W)) (γ : MulAut W) :
    fixV (L.map (MulAut.conj γ).toMonoidHom) = (fixV L).map γ.toMonoidHom :=
  CFSG.Quasithin.fixV_map_conj_eq L γ

theorem map_tp (P L : Subgroup (MulAut W)) {γ : MulAut W}
    (hγ : γ ∈ Subgroup.normalizer (P : Set (MulAut W))) :
    (tp P L).map γ.toMonoidHom = tp P (L.map (MulAut.conj γ).toMonoidHom) := by
  rw [tp, tp, Subgroup.map_inf _ _ _ γ.injective, map_commV P hγ, fixV_conj]

theorem fix_of_le_sup {w : W} {L L' : Subgroup (MulAut W)} (h : ∀ x ∈ L, x w = w)
    (h' : ∀ x ∈ L', x w = w) : ∀ x ∈ L ⊔ L', x w = w := by
  have : L ⊔ L' ≤ MulAction.stabilizer (MulAut W) w :=
    sup_le (fun x hx => h x hx) (fun x hx => h' x hx)
  exact fun x hx => this hx

theorem tp_inf_tp (hW : ∀ w : W, w ^ 2 = 1) (P L L' : Subgroup (MulAut W)) [Fintype ↥P]
    (hP : Fintype.card ↥P = 25) (hsup : L ⊔ L' = P) : tp P L ⊓ tp P L' = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hw, hw'⟩
  have hfix := fix_of_le_sup hw.1 hw'.1
  rw [hsup] at hfix
  exact Subgroup.mem_bot.mpr (eq_one_of_fixed_of_mem_commV hW P hP hw.2 hfix)

theorem conj_eq_self {P L : Subgroup (MulAut W)} (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hL : L ≤ P) {κ : MulAut W} (hκ : κ ∈ P) : L.map (MulAut.conj κ).toMonoidHom = L := by
  have key : ∀ y ∈ L, κ * y * κ⁻¹ = y := fun y hy => by
    rw [hPc κ hκ y (hL hy)]
    simp
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := key y hy
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    rw [this]
    exact hy
  · intro hx
    exact ⟨x, hx, by simp [MulAut.conj_apply, key x hx]⟩

theorem smul_mem_tp {P L : Subgroup (MulAut W)} (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hL : L ≤ P) {κ : MulAut W} (hκ : κ ∈ P) {w : W} (hw : w ∈ tp P L) : κ w ∈ tp P L := by
  have := map_tp P L (Subgroup.le_normalizer hκ)
  rw [conj_eq_self hPc hL hκ] at this
  rw [← this]
  exact ⟨w, hw, rfl⟩

theorem sup_eq_of_ne [Finite W] {P L L' : Subgroup (MulAut W)} [Fintype ↥P]
    (hP : Fintype.card ↥P = 25) (hL : L ≤ P) (hL' : L' ≤ P) (h5 : Nat.card L = 5)
    (h5' : Nat.card L' = 5) (hne : L ≠ L') : L ⊔ L' = P := by
  have hP' : Nat.card P = 25 := by rw [Nat.card_eq_fintype_card, hP]
  have hle : L ⊔ L' ≤ P := sup_le hL hL'
  have hd1 : Nat.card L ∣ Nat.card ↥(L ⊔ L') := Subgroup.card_dvd_of_le le_sup_left
  have hd2 : Nat.card ↥(L ⊔ L') ∣ Nat.card P := Subgroup.card_dvd_of_le hle
  rw [hP'] at hd2
  rw [h5] at hd1
  by_cases h25 : Nat.card ↥(L ⊔ L') = 25
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hP', h25])
  · have h5s : Nat.card ↥(L ⊔ L') = 5 := by
      have : Nat.card ↥(L ⊔ L') ∈ Nat.divisors 25 := by simp [hd2]
      have hdiv : Nat.divisors 25 = {1, 5, 25} := by decide
      rw [hdiv] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h
      · rw [h] at hd1; omega
      · exact h
      · exact absurd h h25
    have e1 : L = L ⊔ L' := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h5, h5s])
    have e2 : L' = L ⊔ L' := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h5', h5s])
    exact absurd (e1.trans e2.symm) hne

theorem zpowers_eq_of_card_five [Finite W] {L : Subgroup (MulAut W)} (h5 : Nat.card L = 5)
    {κ : MulAut W} (hκ : κ ∈ L) (hκ1 : κ ≠ 1) : Subgroup.zpowers κ = L := by
  have hle : Subgroup.zpowers κ ≤ L := (Subgroup.zpowers_le).mpr hκ
  have hdvd : Nat.card ↥(Subgroup.zpowers κ) ∣ 5 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [h5] at this
  have hne : Nat.card ↥(Subgroup.zpowers κ) ≠ 1 := by
    intro h1
    rw [Nat.card_zpowers] at h1
    exact hκ1 (orderOf_eq_one_iff.mp h1)
  have h5' : Nat.card ↥(Subgroup.zpowers κ) = 5 :=
    ((Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd).resolve_left hne
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h5, h5'])

theorem exists_ne_one_of_card_five {L : Subgroup (MulAut W)} (h5 : Nat.card L = 5) :
    ∃ κ ∈ L, κ ≠ 1 := by
  by_contra h
  push Not at h
  have : L = ⊥ := (Subgroup.eq_bot_iff_forall L).mpr h
  rw [this] at h5
  simp at h5

theorem sixteen_le_card_tp [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {P L : Subgroup (MulAut W)}
    [Fintype ↥P] (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP : Fintype.card ↥P = 25)
    (hL : L ≤ P) (hne : tp P L ≠ ⊥) : 16 ≤ Nat.card (tp P L) := by
  have hP' : Nat.card P = 25 := by rw [Nat.card_eq_fintype_card, hP]
  have hPg : IsPGroup 5 ↥P := IsPGroup.of_card (n := 2) (by rw [hP']; norm_num)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
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
      refine eq_one_of_fixed_of_mem_commV hW P hP (tp_le_commV P L s.2) (fun κ hκ => ?_)
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
  have hd : rk (tp P L) < 4 := by
    by_contra h
    exact hlt (by calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ rk (tp P L) := Nat.pow_le_pow_right (by norm_num) (not_lt.mp h))
  generalize rk (tp P L) = d at hmod hrk hd
  interval_cases d <;> simp [Nat.ModEq] at hmod hrk

theorem tp_sup_inf [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {P L₁ L₂ L₃ : Subgroup (MulAut W)}
    [Fintype ↥P] (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP : Fintype.card ↥P = 25)
    (h₁ : L₁ ≤ P) (h₂ : L₂ ≤ P) (h₃ : L₃ ≤ P) (c₁ : Nat.card L₁ = 5) (c₂ : Nat.card L₂ = 5)
    (c₃ : Nat.card L₃ = 5) (n₁₂ : L₁ ≠ L₂) (n₁₃ : L₁ ≠ L₃) (n₂₃ : L₂ ≠ L₃) :
    tp P L₃ ⊓ (tp P L₁ ⊔ tp P L₂) = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hw3, hw12⟩
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.mp hw12
  obtain ⟨κ, hκL, hκ1⟩ := exists_ne_one_of_card_five c₁
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
  have hbot23 : tp P L₂ ⊓ tp P L₃ = ⊥ := tp_inf_tp hW P L₂ L₃ hP (sup_eq_of_ne hP h₂ h₃ c₂ c₃ n₂₃)
  have hc : κ w₂ * w₂⁻¹ = 1 := by
    have : κ w₂ * w₂⁻¹ ∈ tp P L₂ ⊓ tp P L₃ := ⟨hu2', hu2 ▸ hu3⟩
    rw [hbot23] at this
    exact Subgroup.mem_bot.mp this
  have hκw₂ : κ w₂ = w₂ := mul_inv_eq_one.mp hc
  have hzp : Subgroup.zpowers κ = L₁ := zpowers_eq_of_card_five c₁ hκL hκ1
  have hfL₁ : ∀ x ∈ L₁, x w₂ = w₂ := by
    have : Subgroup.zpowers κ ≤ MulAction.stabilizer (MulAut W) w₂ :=
      (Subgroup.zpowers_le).mpr hκw₂
    intro x hx
    rw [← hzp] at hx
    exact this hx
  have hfixP : ∀ x ∈ P, x w₂ = w₂ := by
    have := fix_of_le_sup hfL₁ hw₂.1
    rwa [sup_eq_of_ne hP h₁ h₂ c₁ c₂ n₁₂] at this
  have hw₂1 : w₂ = 1 := eq_one_of_fixed_of_mem_commV hW P hP (tp_le_commV P L₂ hw₂) hfixP
  subst hw₂1
  have hbot13 : tp P L₁ ⊓ tp P L₃ = ⊥ := tp_inf_tp hW P L₁ L₃ hP (sup_eq_of_ne hP h₁ h₃ c₁ c₃ n₁₃)
  have : w₁ ∈ tp P L₁ ⊓ tp P L₃ := ⟨hw₁, by simpa using hw3⟩
  rw [hbot13] at this
  simpa using this

end CFSG.Quasithin.FixR
