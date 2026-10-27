module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpWitness
public import CFSG.LieType.Universal.Spin.Roots.TypeD
import CFSG.Timmesfeld.ARS.CaseOAWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsWeyl

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin
open CFSG.StandardType

private theorem omWeyl_sum_Iic_succ {n : ℕ} {a : Fin n} (ha : 0 < a.val) (f : Fin n → ℤ) :
    ∑ b ∈ Finset.Iic a, f b =
      ∑ b ∈ Finset.Iic (⟨a.val - 1, by omega⟩ : Fin n), f b + f a := by
  have hIio : Finset.Iio a = Finset.Iic (⟨a.val - 1, by omega⟩ : Fin n) := by
    ext x
    simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def]
    omega
  rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons, hIio]
  ring

private theorem omWeyl_sum_univ_eq_Iic_last {n : ℕ} (hn : 1 ≤ n) (f : Fin n → ℤ) :
    ∑ b, f b = ∑ b ∈ Finset.Iic (⟨n - 1, by omega⟩ : Fin n), f b := by
  have h : (Finset.univ : Finset (Fin n)) = Finset.Iic (⟨n - 1, by omega⟩ : Fin n) := by
    ext x
    have hx : x.val < n := x.isLt
    simp only [Finset.mem_univ, true_iff, Finset.mem_Iic, Fin.le_def]
    omega
  rw [h]

private theorem omWeyl_sum_Iic_zero {n : ℕ} {a : Fin n} (ha : a.val = 0) (f : Fin n → ℤ) :
    ∑ b ∈ Finset.Iic a, f b = f a := by
  have h : Finset.Iic a = {a} := by
    ext x
    simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
    omega
  rw [h, Finset.sum_singleton]

private theorem omWeyl_sum_univ_eq_Iic_Iic {n : ℕ} (_hn : 2 ≤ n) {a : Fin n}
    (ha : a.val + 2 = n) (ha0 : 0 < a.val) (f : Fin n → ℤ) :
    ∑ b, f b = ∑ b ∈ Finset.Iic (⟨a.val - 1, by omega⟩ : Fin n), f b + f a +
      f ⟨n - 1, by omega⟩ := by
  have hu := omWeyl_sum_univ_eq_Iic_last (n := n) (by omega) f
  have h1 := omWeyl_sum_Iic_succ (a := (⟨n - 1, by omega⟩ : Fin n)) (by simp only; omega) f
  have h2 := omWeyl_sum_Iic_succ (a := a) ha0 f
  have e1 : (⟨(⟨n - 1, by omega⟩ : Fin n).val - 1, by omega⟩ : Fin n) = a :=
    Fin.ext (by change n - 1 - 1 = a.val; omega)
  rw [hu, h1, e1, h2]

private theorem omWeyl_sum_univ_eq_zero {n : ℕ} (_hn : 2 ≤ n) {a : Fin n}
    (ha : a.val + 2 = n) (ha0 : a.val = 0) (f : Fin n → ℤ) :
    ∑ b, f b = f a + f ⟨n - 1, by omega⟩ := by
  have hu := omWeyl_sum_univ_eq_Iic_last (n := n) (by omega) f
  have h1 := omWeyl_sum_Iic_succ (a := (⟨n - 1, by omega⟩ : Fin n)) (by simp only; omega) f
  have h2 := omWeyl_sum_Iic_zero (a := a) ha0 f
  have e1 : (⟨(⟨n - 1, by omega⟩ : Fin n).val - 1, by omega⟩ : Fin n) = a :=
    Fin.ext (by change n - 1 - 1 = a.val; omega)
  rw [hu, h1, e1, h2]

@[expose] def omFromStdD2 (n : ℕ) (c : Fin n → ℤ) : Fin n → ℤ := fun a =>
  if a.val + 1 = n then ∑ b, c b
  else if h : a.val + 2 = n then ∑ b, c b - 2 * c ⟨a.val + 1, by omega⟩
  else 2 * ∑ b ∈ Finset.Iic a, c b

private theorem omWeyl_toStdD_third {n : ℕ} (c : Fin n → ℤ) {a : Fin n}
    (h2 : a.val + 2 < n) :
    toStdD n (omFromStdD2 n c) a = 2 * c a := by
  have hva : omFromStdD2 n c a = 2 * ∑ b ∈ Finset.Iic a, c b := by
    unfold omFromStdD2
    rw [if_neg (by omega), dif_neg (by omega)]
  simp only [toStdD]
  rw [hva]
  by_cases ha0 : 0 < a.val
  · have hvp : omFromStdD2 n c ⟨a.val - 1, by omega⟩ =
        2 * ∑ b ∈ Finset.Iic (⟨a.val - 1, by omega⟩ : Fin n), c b := by
      unfold omFromStdD2
      rw [if_neg (by simp only; omega), dif_neg (by simp only; omega)]
    rw [dif_pos ha0, hvp, dif_neg (by omega)]
    rw [omWeyl_sum_Iic_succ ha0 c]
    ring
  · rw [dif_neg ha0, dif_neg (by omega)]
    rw [omWeyl_sum_Iic_zero (by omega) c]
    ring

private theorem omWeyl_toStdD_second {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℤ) {a : Fin n}
    (h1 : a.val + 1 < n) (h2 : a.val + 2 = n) :
    toStdD n (omFromStdD2 n c) a = 2 * c a := by
  have hva : omFromStdD2 n c a = ∑ b, c b - 2 * c ⟨a.val + 1, by omega⟩ := by
    unfold omFromStdD2
    rw [if_neg (by omega), dif_pos h2]
  have hva1 : omFromStdD2 n c ⟨a.val + 1, by omega⟩ = ∑ b, c b := by
    unfold omFromStdD2
    rw [if_pos (by simp only; omega)]
  simp only [toStdD]
  rw [hva, dif_pos h2, hva1]
  by_cases ha0 : 0 < a.val
  · have hvp : omFromStdD2 n c ⟨a.val - 1, by omega⟩ =
        2 * ∑ b ∈ Finset.Iic (⟨a.val - 1, by omega⟩ : Fin n), c b := by
      unfold omFromStdD2
      rw [if_neg (by simp only; omega), dif_neg (by simp only; omega)]
    rw [dif_pos ha0, hvp]
    rw [omWeyl_sum_univ_eq_Iic_Iic hn h2 ha0 c]
    have hlast : (⟨a.val + 1, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ :=
      Fin.ext (by change a.val + 1 = n - 1; omega)
    rw [hlast]
    ring
  · rw [dif_neg ha0]
    rw [omWeyl_sum_univ_eq_zero hn h2 (by omega) c]
    have hlast : (⟨a.val + 1, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ :=
      Fin.ext (by change a.val + 1 = n - 1; omega)
    rw [hlast]
    ring

private theorem omWeyl_toStdD_first {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℤ) {a : Fin n}
    (h1 : a.val + 1 = n) :
    toStdD n (omFromStdD2 n c) a = 2 * c a := by
  have hva : omFromStdD2 n c a = ∑ b, c b := by
    unfold omFromStdD2
    rw [if_pos h1]
  have hva1 : omFromStdD2 n c ⟨a.val - 1, by omega⟩ = ∑ b, c b - 2 * c a := by
    unfold omFromStdD2
    rw [if_neg (by simp only; omega), dif_pos (by simp only; omega)]
    congr 1
    congr 1
    congr 1
    exact Fin.ext (by change a.val - 1 + 1 = a.val; omega)
  have ha0 : 0 < a.val := by omega
  simp only [toStdD]
  rw [hva, dif_pos ha0, hva1, dif_neg (by omega)]
  ring

theorem toStdD_omFromStdD2 {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℤ) :
    toStdD n (omFromStdD2 n c) = fun a => 2 * c a := by
  funext a
  have ha : a.val < n := a.isLt
  rcases lt_trichotomy (a.val + 1) n with h1 | h1 | h1
  · rcases lt_trichotomy (a.val + 2) n with h2 | h2 | h2
    · exact omWeyl_toStdD_third c h2
    · exact omWeyl_toStdD_second hn c h1 h2
    · exfalso; omega
  · exact omWeyl_toStdD_first hn c h1
  · exfalso; omega

private theorem omWeyl_stdReflD_two_mul (n : ℕ) (k : Fin n) (c : Fin n → ℤ) :
    stdReflD n k (fun a => 2 * c a) = fun a => 2 * stdReflD n k c a := by
  by_cases h : k.val + 1 < n
  · rw [stdReflD_of_lt n h, stdReflD_of_lt n h]
    funext a
    simp only [Function.comp_apply]
  · rw [stdReflD_of_not_lt n h, stdReflD_of_not_lt n h]
    funext a
    ring

theorem weylAction_simple_omFromStdD2 {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℤ) (k : Fin n) :
    weylAction (isFiniteType_cartanD n)
        ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple k) (omFromStdD2 n c) =
      omFromStdD2 n (stdReflD n k c) := by
  apply toStdD_injective n
  rw [weylAction_simple, toStdD_reflection, toStdD_omFromStdD2 hn, toStdD_omFromStdD2 hn]
  exact omWeyl_stdReflD_two_mul n k c

@[expose] def OmRealizes (n : ℕ) (w : (coxeterMatrix (isFiniteType_cartanD n)).Group)
    (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ) : Prop :=
  ∀ γ, toStdD n (weylAction (isFiniteType_cartanD n) w γ) =
    fun b => s (π.symm b) * toStdD n γ (π.symm b)

private theorem omWeyl_OmRealizes_congr {n : ℕ}
    {w : (coxeterMatrix (isFiniteType_cartanD n)).Group} {π π' : Equiv.Perm (Fin n)}
    {s s' : Fin n → ℤ} (h : OmRealizes n w π s) (hπ : π = π') (hs : s = s') :
    OmRealizes n w π' s' := hπ ▸ hs ▸ h

theorem omRealizes_one (n : ℕ) : OmRealizes n 1 1 1 := fun γ => by
  rw [map_one, Module.End.one_apply]
  funext b
  change toStdD n γ b = 1 * toStdD n γ b
  rw [one_mul]

theorem OmRealizes.mul {n : ℕ} {w₁ w₂ : (coxeterMatrix (isFiniteType_cartanD n)).Group}
    {π₁ π₂ : Equiv.Perm (Fin n)} {s₁ s₂ : Fin n → ℤ} (h₁ : OmRealizes n w₁ π₁ s₁)
    (h₂ : OmRealizes n w₂ π₂ s₂) :
    OmRealizes n (w₁ * w₂) (π₁ * π₂) (fun c => s₂ c * s₁ (π₂ c)) := fun γ => by
  rw [weylAction_mul_apply, h₁, h₂]
  funext b
  simp only [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  ring

theorem omRealizes_simple_of_lt {n : ℕ} {k : Fin n} (h : k.val + 1 < n) :
    OmRealizes n ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple k)
      (Equiv.swap k ⟨k.val + 1, h⟩) 1 := fun γ => by
  rw [weylAction_simple, toStdD_reflection_of_lt n h]
  funext b
  simp [Equiv.symm_swap]

private theorem omWeyl_signD_eq {n : ℕ} (b : Fin n) :
    (if b.val + 2 = n ∨ b.val + 1 = n then (-1 : ℤ) else 1) =
      (if n ≤ b.val + 2 then -1 else 1) := by
  have hb : b.val < n := b.isLt
  split_ifs <;> omega

private theorem omWeyl_signD_swap {n : ℕ} (hn : 2 ≤ n) {k : Fin n} (h : ¬ k.val + 1 < n)
    (b : Fin n) :
    (if n ≤ ((Equiv.swap (⟨n - 2, by omega⟩ : Fin n) k).symm b).val + 2
      then (-1 : ℤ) else 1) = (if n ≤ b.val + 2 then -1 else 1) := by
  have hkval : k.val = n - 1 := by omega
  rw [Equiv.symm_swap]
  by_cases hbp : b = (⟨n - 2, by omega⟩ : Fin n)
  · subst hbp
    rw [Equiv.swap_apply_left]
    rw [if_pos (by omega), if_pos (by change n ≤ n - 2 + 2; omega)]
  · by_cases hbk : b = k
    · subst hbk
      rw [Equiv.swap_apply_right]
      rw [if_pos (by change n ≤ n - 2 + 2; omega), if_pos (by omega)]
    · rw [Equiv.swap_apply_of_ne_of_ne hbp hbk]

private theorem omWeyl_stdReflD_of_not_lt {n : ℕ} (hn : 2 ≤ n) {k : Fin n}
    (h : ¬ k.val + 1 < n) (e : Fin n → ℤ) :
    stdReflD n k e = fun b => (if n ≤ b.val + 2 then (-1 : ℤ) else 1) *
      e ((Equiv.swap (⟨n - 2, by omega⟩ : Fin n) k).symm b) := by
  have hklt : k.val < n := k.isLt
  have hk : (⟨k.val - 1, by omega⟩ : Fin n) = ⟨n - 2, by omega⟩ :=
    Fin.ext (by change k.val - 1 = n - 2; omega)
  have hswap : Equiv.swap (⟨k.val - 1, by omega⟩ : Fin n) k =
      Equiv.swap (⟨n - 2, by omega⟩ : Fin n) k := by rw [hk]
  rw [stdReflD_of_not_lt n h]
  funext b
  rw [omWeyl_signD_eq b, Equiv.symm_swap, hswap]

theorem omRealizes_simple_of_not_lt {n : ℕ} (hn : 2 ≤ n) {k : Fin n} (h : ¬ k.val + 1 < n) :
    OmRealizes n ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple k)
      (Equiv.swap ⟨n - 2, by omega⟩ k) (fun a => if n ≤ a.val + 2 then -1 else 1) := fun γ => by
  rw [weylAction_simple, toStdD_reflection, omWeyl_stdReflD_of_not_lt hn h]
  funext b
  dsimp only
  rw [omWeyl_signD_swap hn h b]

theorem exists_omRealizes {n : ℕ} (hn : 2 ≤ n)
    (w : (coxeterMatrix (isFiniteType_cartanD n)).Group) :
    ∃ (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ), SpIsSign s ∧ ∏ a, s a = 1 ∧
      OmRealizes n w π s := by
  obtain ⟨π₀, s₀, hs₀, hprod, hπ₀⟩ :=
    CFSG.Timmesfeld.ARS.CaseOA.exists_signedPerm_toStdD_weylAction hn w
  refine ⟨π₀.symm, fun c => s₀ (π₀.symm c), fun c => hs₀ _, ?_, ?_⟩
  · rw [← hprod]
    exact Equiv.prod_comp π₀.symm s₀
  · intro γ
    rw [hπ₀ γ]
    funext b
    simp [Equiv.symm_apply_apply]

private theorem omWeyl_even_card_support {n : ℕ} {t : Fin n → ℤ} (ht : SpIsSign t)
    (hprod : ∏ a, t a = 1) :
    Even (Finset.univ.filter (fun a => t a = -1)).card := by
  have hcongr : ∏ a, (if a ∈ Finset.univ.filter (fun a => t a = -1) then (-1 : ℤ) else 1) =
      ∏ a, t a := by
    apply Finset.prod_congr rfl
    intro a _
    by_cases ha : a ∈ Finset.univ.filter (fun a => t a = -1)
    · rw [if_pos ha]
      exact ((Finset.mem_filter.mp ha).2).symm
    · rw [if_neg ha]
      rcases ht a with h | h
      · exact h.symm
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h⟩) ha
  have h2 : ((-1 : ℤ)) ^ (Finset.univ.filter (fun a => t a = -1)).card = 1 := by
    have h1 : ∏ a, (if a ∈ Finset.univ.filter (fun a => t a = -1) then (-1 : ℤ) else 1) =
        1 := by rw [hcongr, hprod]
    rw [Finset.prod_ite_mem (s := Finset.univ)
      (t := Finset.univ.filter (fun a => t a = -1)) (f := fun _ => (-1 : ℤ))] at h1
    simpa [Finset.univ_inter, Finset.prod_const] using h1
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℤ) ≠ 1)).mp h2

private theorem omWeyl_support_negPair {n : ℕ} {t : Fin n → ℤ} {x y : Fin n}
    (hxy : x ≠ y) (htx : t x = -1) (hty : t y = -1) :
    (Finset.univ.filter (fun a =>
        (if a = x ∨ a = y then (-1 : ℤ) else 1) * t a = -1)) =
      ((Finset.univ.filter (fun a => t a = -1)).erase x).erase y := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  by_cases hcx : c = x
  · subst hcx
    simp [htx, hxy]
  · by_cases hcy : c = y
    · subst hcy
      simp [hty]
    · simp [hcx, hcy]

private theorem omWeyl_card_support_negPair {n : ℕ} {t : Fin n → ℤ} {x y : Fin n}
    (hxy : x ≠ y) (htx : t x = -1) (hty : t y = -1)
    (hxS : x ∈ Finset.univ.filter (fun a => t a = -1))
    (hyS : y ∈ Finset.univ.filter (fun a => t a = -1)) (k : ℕ)
    (htcard : (Finset.univ.filter (fun a => t a = -1)).card = k) :
    (Finset.univ.filter (fun a =>
        (if a = x ∨ a = y then (-1 : ℤ) else 1) * t a = -1)).card = k - 2 := by
  rw [omWeyl_support_negPair hxy htx hty,
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, hyS⟩),
    Finset.card_erase_of_mem hxS, htcard]
  omega

private theorem omWeyl_isSign_negPair {n : ℕ} {t : Fin n → ℤ} (ht : SpIsSign t)
    {x y : Fin n} :
    SpIsSign (fun c => (if c = x ∨ c = y then (-1 : ℤ) else 1) * t c) := by
  intro c
  simp only []
  have hneg : (if c = x ∨ c = y then (-1 : ℤ) else 1) = 1 ∨
      (if c = x ∨ c = y then (-1 : ℤ) else 1) = -1 := by split_ifs <;> simp
  rcases hneg with h | h <;> rcases ht c with h2 | h2 <;> rw [h, h2] <;> simp

private theorem omWeyl_negPair_realizes {n : ℕ} {x y : Fin n} (g : ggWeylD n)
    (hg : ∀ v, toStdD n (weylAction (isFiniteType_cartanD n) g v) =
      fun c => if c = x ∨ c = y then -toStdD n v c else toStdD n v c) :
    OmRealizes n g 1 (fun c => if c = x ∨ c = y then (-1 : ℤ) else 1) := by
  intro v
  rw [hg v]
  funext b
  change (if b = x ∨ b = y then -toStdD n v b else toStdD n v b) =
    (if b = x ∨ b = y then (-1 : ℤ) else 1) * toStdD n v b
  by_cases hb : b = x ∨ b = y
  · rw [if_pos hb, if_pos hb]; ring
  · rw [if_neg hb, if_neg hb]; ring

private theorem omWeyl_exists_sign_zero {n : ℕ} {t : Fin n → ℤ} (ht : SpIsSign t)
    (htcard : (Finset.univ.filter (fun a => t a = -1)).card = 0) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanD n)).Group, OmRealizes n w 1 t := by
  have hsupp : Finset.univ.filter (fun a => t a = -1) = ∅ :=
    Finset.card_eq_zero.mp htcard
  have ht1 : t = 1 := by
    funext a
    by_contra hne
    have hneg : t a = -1 := by
      rcases ht a with h | h
      · exact absurd h hne
      · exact h
    have : a ∈ Finset.univ.filter (fun a => t a = -1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, hneg⟩
    rw [hsupp] at this
    exact Finset.notMem_empty a this
  subst ht1
  exact ⟨1, omRealizes_one n⟩

private theorem omWeyl_exists_sign_succ {n : ℕ} (hn : 2 ≤ n) {t : Fin n → ℤ}
    (ht : SpIsSign t) {k : ℕ} (hk0 : k ≠ 0)
    (htcard : (Finset.univ.filter (fun a => t a = -1)).card = k) (heven : Even k)
    (ih : ∀ m < k, ∀ t : Fin n → ℤ, SpIsSign t →
      (Finset.univ.filter (fun a => t a = -1)).card = m → Even m →
      ∃ w, OmRealizes n w 1 t) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanD n)).Group, OmRealizes n w 1 t := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  obtain ⟨x, hxS⟩ := Finset.card_pos.mp (by rw [htcard]; exact hkpos)
  have htx : t x = -1 := (Finset.mem_filter.mp hxS).2
  have hcard_erase :
      ((Finset.univ.filter (fun a => t a = -1)).erase x).card = k - 1 := by
    rw [Finset.card_erase_of_mem hxS, htcard]
  have hk2 : 2 ≤ k := by
    rcases heven with ⟨m, rfl⟩
    omega
  have hpos_erase : 0 < ((Finset.univ.filter (fun a => t a = -1)).erase x).card := by
    rw [hcard_erase]; omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos_erase
  have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
  have hyS : y ∈ Finset.univ.filter (fun a => t a = -1) := (Finset.mem_erase.mp hy).2
  have hty : t y = -1 := (Finset.mem_filter.mp hyS).2
  have hxy : x ≠ y := hyne.symm
  set s' : Fin n → ℤ := fun c => (if c = x ∨ c = y then (-1 : ℤ) else 1) * t c
    with hs'def
  have hs' : SpIsSign s' := by rw [hs'def]; exact omWeyl_isSign_negPair ht
  have hs'card : (Finset.univ.filter (fun a => s' a = -1)).card = k - 2 := by
    have hset : Finset.univ.filter (fun a => s' a = -1) =
        Finset.univ.filter (fun a =>
          (if a = x ∨ a = y then (-1 : ℤ) else 1) * t a = -1) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs'def]
    rw [hset, omWeyl_card_support_negPair hxy htx hty hxS hyS k htcard]
  obtain ⟨w', hw'⟩ := ih (k - 2) (by omega) s' hs' hs'card (by
    rcases heven with ⟨m, rfl⟩
    exact ⟨m - 1, by omega⟩)
  obtain ⟨g, hg⟩ := ggD_exists_negPair hn hxy
  refine ⟨g * w', ?_⟩
  refine omWeyl_OmRealizes_congr ((omWeyl_negPair_realizes g hg).mul hw')
    (by rw [mul_one]) ?_
  funext c
  simp only [hs'def]
  change (if c = x ∨ c = y then (-1 : ℤ) else 1) * t c *
      (if c = x ∨ c = y then (-1 : ℤ) else 1) = t c
  by_cases hc : c = x ∨ c = y
  · rw [if_pos hc]; ring
  · rw [if_neg hc]; ring

private theorem omWeyl_exists_sign {n : ℕ} (hn : 2 ≤ n) {t : Fin n → ℤ} (ht : SpIsSign t)
    (hprod : ∏ a, t a = 1) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanD n)).Group, OmRealizes n w 1 t := by
  have key : ∀ k, ∀ t : Fin n → ℤ, SpIsSign t →
      (Finset.univ.filter (fun a => t a = -1)).card = k → Even k →
      ∃ w, OmRealizes n w 1 t := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t ht htcard heven
      by_cases hk0 : k = 0
      · subst hk0
        exact omWeyl_exists_sign_zero ht htcard
      · exact omWeyl_exists_sign_succ hn ht hk0 htcard heven ih
  exact key _ t ht rfl (omWeyl_even_card_support ht hprod)

theorem exists_omRealizes_of_even {n : ℕ} (hn : 2 ≤ n) (π : Equiv.Perm (Fin n))
    {s : Fin n → ℤ} (hs : SpIsSign s) (hprod : ∏ a, s a = 1) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanD n)).Group, OmRealizes n w π s := by
  have hs' : SpIsSign (fun c => s (π.symm c)) := fun c => hs (π.symm c)
  have hprod' : ∏ c, s (π.symm c) = 1 := by
    rw [Equiv.prod_comp π.symm s]
    exact hprod
  obtain ⟨w₁, h₁⟩ := omWeyl_exists_sign hn hs' hprod'
  obtain ⟨w₂, h₂⟩ := ggD_exists_perm hn π.symm
  have h₂' : OmRealizes n w₂ π 1 := by
    intro γ
    rw [h₂ γ]
    funext b
    simp
  refine ⟨w₁ * w₂, ?_⟩
  refine omWeyl_OmRealizes_congr (h₁.mul h₂') (by rw [one_mul]) ?_
  funext c
  simp [Equiv.symm_apply_apply]

theorem omRealizes_unique {n : ℕ} (hn : 2 ≤ n)
    {w : (coxeterMatrix (isFiniteType_cartanD n)).Group} {π π' : Equiv.Perm (Fin n)}
    {s s' : Fin n → ℤ} (h : OmRealizes n w π s) (h' : OmRealizes n w π' s')
    (hs : SpIsSign s) : π = π' ∧ s = s' := by
  have key : ∀ a, π a = π' a ∧ s a = s' a := by
    intro a
    let γ : Fin n → ℤ := omFromStdD2 n (Pi.single a 1)
    have hγ : toStdD n γ = fun c => 2 * Pi.single a 1 c := toStdD_omFromStdD2 hn _
    have heq : s (π.symm (π a)) * toStdD n γ (π.symm (π a)) =
        s' (π'.symm (π a)) * toStdD n γ (π'.symm (π a)) := by
      have h1 := congrFun (h γ) (π a)
      have h2 := congrFun (h' γ) (π a)
      exact h1.symm.trans h2
    rw [hγ] at heq
    simp only [Equiv.symm_apply_apply, Pi.single_eq_same] at heq
    by_cases hd : π'.symm (π a) = a
    · have hπ : π a = π' a := by
        have := congrArg π' hd
        rwa [Equiv.apply_symm_apply] at this
      refine ⟨hπ, ?_⟩
      rw [hd] at heq
      simp only [Pi.single_eq_same] at heq
      omega
    · exfalso
      have hz : s a = 0 := by
        have hsingle : (Pi.single a (1 : ℤ) : Fin n → ℤ) (π'.symm (π a)) = 0 := by
          rw [Pi.single_apply, if_neg hd]
        rw [hsingle] at heq
        simp only [mul_zero] at heq
        omega
      rcases hs a with h1 | h1 <;> omega
  exact ⟨Equiv.ext fun a => (key a).1, funext fun a => (key a).2⟩

end CFSG.LocalAnalysis.WeakClosure81
