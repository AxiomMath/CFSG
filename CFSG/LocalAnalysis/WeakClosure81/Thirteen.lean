module

public import CFSG.Quasithin.Background.G11Basic
public import CFSG.LocalAnalysis.WeakClosure81.TenFive
public import CFSG.LocalAnalysis.WeakClosure81.LemmaD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

@[expose] noncomputable def mOf (A B : Subgroup (LGL 2 V)) : ℕ :=
  Nat.log 2 ((B.subgroupOf A).index)

@[expose] noncomputable def mRank (A : Subgroup (LGL 2 V)) : ℕ :=
  Nat.log 2 (Nat.card A)

theorem mOf_bot (A : Subgroup (LGL 2 V)) : mOf A ⊥ = mRank A := by
  simp [mOf, mRank, Subgroup.bot_subgroupOf, Subgroup.index_bot]

structure Assumption131 (G : Subgroup (LGL 2 V)) (Γ : Set (Subgroup (LGL 2 V)))
    (VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V) (i : ℕ) : Prop where
  pos_i : 0 < i
  le_G : ∀ A ∈ Γ, A ≤ G
  isElemAb : ∀ A ∈ Γ, IsElemAbelian 2 A
  invariant : ∀ A ∈ Γ, ∀ g ∈ G, cj g A ∈ Γ
  ne_bot : ∀ A ∈ Γ, A ≠ ⊥
  inf_pCore : ∀ A ∈ Γ, A ⊓ pCoreOf 2 G = ⊥
  normalizer_eq : ∀ A ∈ Γ, G ⊓ Subgroup.normalizer (A : Set (LGL 2 V)) =
    stabilizerOf G (VA A)
  disjoint : ∀ A ∈ Γ, ∀ B ∈ Γ, A ≠ B → VA A ⊓ VA B = ⊥
  cond2 : ∀ A ∈ Γ, ∀ B : Subgroup (LGL 2 V), B ≤ A → mOf A B ≤ i →
    commSpace A (fixSub B) ≤ VA A
  quadratic : ∀ A ∈ Γ, commSpace A (commSub A) = ⊥
  equivariant : ∀ A ∈ Γ, ∀ g ∈ G, VA (cj g A) = conjSub g (VA A)

theorem commSub_le_VA_of_mRank_le (h : Assumption131 G Γ VA i) {A : Subgroup (LGL 2 V)}
    (hA : A ∈ Γ) (hrank : mRank A ≤ i) : commSub A ≤ VA A := by
  have h2 := h.cond2 A hA ⊥ bot_le (by rwa [mOf_bot])
  rwa [fixSub_bot, commSpace_top_eq_commSub] at h2

theorem commSub_ne_bot_of_mem (h : Assumption131 G Γ VA i) {A : Subgroup (LGL 2 V)}
    (hA : A ∈ Γ) : commSub A ≠ ⊥ :=
  fun hbot => h.ne_bot A hA ((commSub_eq_bot_iff A).mp hbot)

theorem inf_eq_bot_of_mem (h : Assumption131 G Γ VA i) (hrank : ∀ A ∈ Γ, mRank A ≤ i)
    {A B : Subgroup (LGL 2 V)} (hA : A ∈ Γ) (hB : B ∈ Γ) (hne : A ≠ B) :
    A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  rintro a ha
  rw [Subgroup.mem_bot]
  by_contra ha1
  have hleA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha.1
  have hleB : Subgroup.zpowers a ≤ B := Subgroup.zpowers_le.mpr ha.2
  have hcA : commSub (Subgroup.zpowers a) ≤ VA A :=
    (commSub_mono _ _ hleA).trans (commSub_le_VA_of_mRank_le h hA (hrank A hA))
  have hcB : commSub (Subgroup.zpowers a) ≤ VA B :=
    (commSub_mono _ _ hleB).trans (commSub_le_VA_of_mRank_le h hB (hrank B hB))
  have hne0 : commSub (Subgroup.zpowers a) ≠ ⊥ := fun hbot =>
    ha1 (Subgroup.zpowers_eq_bot.mp ((commSub_eq_bot_iff (Subgroup.zpowers a)).mp hbot))
  refine hne0 (le_bot_iff.mp ?_)
  calc commSub (Subgroup.zpowers a) ≤ VA A ⊓ VA B := le_inf hcA hcB
    _ = ⊥ := h.disjoint A hA B hB hne

private def fixingSubgroup (v : V) : Subgroup (LGL 2 V) where
  carrier := {g | g v = v}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    change a (b v) = v
    rw [hb, ha]
  inv_mem' := by
    intro a ha
    change a⁻¹ v = v
    calc a⁻¹ v = a⁻¹ (a v) := by conv_lhs => rw [← ha]
      _ = v := LinearEquiv.symm_apply_apply a v

private theorem add_self_two (v : V) : v + v = 0 := ZModModule.add_self v

private theorem sub_eq_add_two (x y : V) : x - y = x + y := ZModModule.sub_eq_add x y

private theorem apply_eq_of_sq_apply_eq_of_odd {g : LGL 2 V} {w : V}
    (hodd : Odd (orderOf g)) (h : g (g w) = w) : g w = w := by
  obtain ⟨m, hm⟩ := hodd
  have hg : g = (g ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    rw [show 2 * (m + 1) = orderOf g + 1 by rw [hm]; ring]
    rw [pow_succ, pow_orderOf_eq_one, one_mul]
  have hpow : ∀ j : ℕ, ((g ^ 2) ^ j) w = w := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [pow_succ']
        change (g ^ 2) (((g ^ 2) ^ j) w) = w
        rw [ih, pow_two, LinearEquiv.mul_apply]
        exact h
  rw [hg]
  exact hpow (m + 1)

private theorem mul_comm_of_conj_eq_self {g x : LGL 2 V} (h : g * x * g⁻¹ = x) :
    g * x = x * g := by
  conv_rhs => rw [← h]
  group

private theorem quadratic_apply_sub {A : Subgroup (LGL 2 V)}
    (hquad : commSpace A (commSub A) = ⊥) {a b : LGL 2 V} (ha : a ∈ A) (hb : b ∈ A)
    (v : V) : b (a v - v) = a v - v :=
  (commSpace_eq_bot_iff.mp hquad) b hb (a v - v) (sub_mem_commSub A ha v)

private theorem apply_eq_of_quadratic_conj {A : Subgroup (LGL 2 V)}
    (hquad : commSpace A (commSub A) = ⊥)
    {a₁ a₂ x₂ : LGL 2 V} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (ha₁sq : a₁ * a₁ = 1) (ha₂sq : a₂ * a₂ = 1)
    (hcomm : a₁ * x₂ = x₂ * a₁) (hinv : a₂ * x₂ * a₂⁻¹ = x₂⁻¹)
    (hodd : Odd (orderOf x₂)) (v : V) : x₂ (a₁ v - v) = a₁ v - v := by
  set w : V := a₁ v - v with hw
  have ha₂w : a₂ w = w := by rw [hw]; exact quadratic_apply_sub hquad ha₁ ha₂ v
  have hcomm' : x₂⁻¹ * a₁ = a₁ * x₂⁻¹ := by
    have h := congrArg Inv.inv hcomm
    simpa [mul_inv_rev, inv_eq_of_mul_eq_one_right ha₁sq] using h
  have hx₂invw : x₂⁻¹ w = a₁ (x₂⁻¹ v) - x₂⁻¹ v := by
    rw [hw]
    calc x₂⁻¹ (a₁ v - v) = (x₂⁻¹ * a₁) v - x₂⁻¹ v := by rw [map_sub, LinearEquiv.mul_apply]
      _ = (a₁ * x₂⁻¹) v - x₂⁻¹ v := by rw [hcomm']
      _ = a₁ (x₂⁻¹ v) - x₂⁻¹ v := by rw [LinearEquiv.mul_apply]
  have ha₂x₂invw : a₂ (x₂⁻¹ w) = x₂⁻¹ w := by
    rw [hx₂invw]
    exact quadratic_apply_sub hquad ha₁ ha₂ (x₂⁻¹ v)
  have ha₂inv_eq : a₂⁻¹ = a₂ := inv_eq_of_mul_eq_one_right ha₂sq
  have ha₂x₂a₂ : a₂ * x₂ * a₂ = x₂⁻¹ := by rwa [ha₂inv_eq] at hinv
  have h1 : x₂⁻¹ * x₂⁻¹ = a₂ * (x₂ * a₂ * x₂⁻¹) := by
    calc x₂⁻¹ * x₂⁻¹ = (a₂ * x₂ * a₂) * x₂⁻¹ := by rw [ha₂x₂a₂]
      _ = a₂ * (x₂ * a₂ * x₂⁻¹) := by group
  have h2 : (x₂ * a₂ * x₂⁻¹) w = w := by
    change x₂ (a₂ (x₂⁻¹ w)) = w
    rw [ha₂x₂invw]
    exact LinearEquiv.apply_symm_apply x₂ w
  have h3 : (x₂⁻¹ * x₂⁻¹) w = w := by
    rw [h1]
    change a₂ ((x₂ * a₂ * x₂⁻¹) w) = w
    rw [h2, ha₂w]
  have hsq : x₂ (x₂ w) = w := by
    have h4 : (x₂ * x₂) w = w := by
      have h5 : (x₂ * x₂)⁻¹ w = w := by rw [mul_inv_rev]; exact h3
      have h6 := congrArg (fun u : V => (x₂ * x₂) u) h5
      have h7 : (x₂ * x₂) ((x₂ * x₂)⁻¹ w) = w := LinearEquiv.apply_symm_apply (x₂ * x₂) w
      rw [h7] at h6
      exact h6.symm
    rwa [LinearEquiv.mul_apply] at h4
  exact apply_eq_of_sq_apply_eq_of_odd hodd hsq

private theorem x1_fixes_span_of_forall_apply_eq {a₁ x₁ : LGL 2 V}
    (ha₁sq : a₁ * a₁ = 1) (hinv : a₁ * x₁ * a₁⁻¹ = x₁⁻¹)
    (hno : ∀ v : V, a₁ (x₁ (a₁ v - v)) = x₁ (a₁ v - v))
    (hodd : Odd (orderOf x₁)) :
    ∀ w ∈ Submodule.span (ZMod 2) {w : V | ∃ v : V, w = a₁ v - v}, x₁ w = w := by
  have ha₁fix : ∀ v : V, a₁ (a₁ v - v) = a₁ v - v := by
    intro v
    calc a₁ (a₁ v - v) = a₁ (a₁ v) - a₁ v := map_sub a₁ (a₁ v) v
      _ = (a₁ * a₁) v - a₁ v := by rw [← LinearEquiv.mul_apply]
      _ = v - a₁ v := by rw [ha₁sq]; rfl
      _ = a₁ v - v := by rw [sub_eq_add_two, sub_eq_add_two, add_comm]
  have ha₁x₁ : a₁ * x₁ = x₁⁻¹ * a₁ := by rw [← hinv]; group
  have hgen : ∀ v : V, x₁ (a₁ v - v) = a₁ v - v := by
    intro v
    have h1 : a₁ (x₁ (a₁ v - v)) = x₁⁻¹ (a₁ v - v) := by
      calc a₁ (x₁ (a₁ v - v)) = (a₁ * x₁) (a₁ v - v) := (LinearEquiv.mul_apply a₁ x₁ _).symm
        _ = (x₁⁻¹ * a₁) (a₁ v - v) := by rw [ha₁x₁]
        _ = x₁⁻¹ (a₁ (a₁ v - v)) := LinearEquiv.mul_apply x₁⁻¹ a₁ _
        _ = x₁⁻¹ (a₁ v - v) := by rw [ha₁fix v]
    have hx₁inv : x₁⁻¹ (a₁ v - v) = x₁ (a₁ v - v) := by rw [← h1, hno v]
    have hsq : x₁ (x₁ (a₁ v - v)) = a₁ v - v := by
      calc x₁ (x₁ (a₁ v - v)) = x₁ (x₁⁻¹ (a₁ v - v)) := by rw [← hx₁inv]
        _ = a₁ v - v := LinearEquiv.apply_symm_apply x₁ _
    exact apply_eq_of_sq_apply_eq_of_odd hodd hsq
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨v, rfl⟩ := hx; exact hgen v
  | zero => exact map_zero x₁
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

private theorem x1_pow_four_eq_one_of_fixes_span {a₁ x₁ : LGL 2 V}
    (ha₁sq : a₁ * a₁ = 1) (hinv : a₁ * x₁ * a₁⁻¹ = x₁⁻¹)
    (hfix : ∀ w ∈ Submodule.span (ZMod 2) {w : V | ∃ v : V, w = a₁ v - v}, x₁ w = w) :
    x₁ ^ 4 = 1 := by
  have ha₁fix : ∀ v : V, a₁ (a₁ v - v) = a₁ v - v := by
    intro v
    calc a₁ (a₁ v - v) = a₁ (a₁ v) - a₁ v := map_sub a₁ (a₁ v) v
      _ = (a₁ * a₁) v - a₁ v := by rw [← LinearEquiv.mul_apply]
      _ = v - a₁ v := by rw [ha₁sq]; rfl
      _ = a₁ v - v := by rw [sub_eq_add_two, sub_eq_add_two, add_comm]
  have ha₁inv_eq : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right ha₁sq
  have ha₁x₁a₁ : a₁ * x₁ * a₁ = x₁⁻¹ := by rwa [ha₁inv_eq] at hinv
  have hsq_eq : x₁⁻¹ * x₁⁻¹ = a₁ * (x₁ * a₁ * x₁⁻¹) := by
    calc x₁⁻¹ * x₁⁻¹ = (a₁ * x₁ * a₁) * x₁⁻¹ := by rw [ha₁x₁a₁]
      _ = a₁ * (x₁ * a₁ * x₁⁻¹) := by group
  have hz_mem : ∀ v : V, (x₁⁻¹ * x₁⁻¹) v - v ∈
      Submodule.span (ZMod 2) {w : V | ∃ v : V, w = a₁ v - v} := by
    intro v
    have hw' : a₁ (x₁⁻¹ v) - x₁⁻¹ v ∈
        Submodule.span (ZMod 2) {w : V | ∃ v : V, w = a₁ v - v} :=
      Submodule.subset_span ⟨x₁⁻¹ v, rfl⟩
    have hx₁w' : x₁ (a₁ (x₁⁻¹ v) - x₁⁻¹ v) = a₁ (x₁⁻¹ v) - x₁⁻¹ v := hfix _ hw'
    have hkey : x₁ (a₁ (x₁⁻¹ v) - x₁⁻¹ v) = (x₁ * a₁ * x₁⁻¹) v - v := by
      calc x₁ (a₁ (x₁⁻¹ v) - x₁⁻¹ v) = x₁ (a₁ (x₁⁻¹ v)) - x₁ (x₁⁻¹ v) := map_sub x₁ _ _
        _ = (x₁ * a₁ * x₁⁻¹) v - v := by
              have hv : x₁ (x₁⁻¹ v) = v := LinearEquiv.apply_symm_apply x₁ v
              rw [hv]
              rfl
    have hkey' : (x₁ * a₁ * x₁⁻¹) v - v = a₁ (x₁⁻¹ v) - x₁⁻¹ v := by rw [← hkey, hx₁w']
    have hlin : a₁ ((x₁ * a₁ * x₁⁻¹) v) - v =
        a₁ ((x₁ * a₁ * x₁⁻¹) v - v) + (a₁ v - v) := by rw [map_sub]; abel
    have hsum : (x₁⁻¹ * x₁⁻¹) v - v =
        a₁ ((x₁ * a₁ * x₁⁻¹) v - v) + (a₁ v - v) := by
      rw [hsq_eq, LinearEquiv.mul_apply, hlin]
    rw [hsum]
    apply Submodule.add_mem
    · have : a₁ ((x₁ * a₁ * x₁⁻¹) v - v) = a₁ (x₁⁻¹ v) - x₁⁻¹ v := by
        rw [hkey']; exact ha₁fix (x₁⁻¹ v)
      rw [this]; exact hw'
    · exact Submodule.subset_span ⟨v, rfl⟩
  have hfixz : ∀ v : V, (x₁⁻¹ * x₁⁻¹) ((x₁⁻¹ * x₁⁻¹) v - v) = (x₁⁻¹ * x₁⁻¹) v - v := by
    intro v
    have hz := hz_mem v
    have hzfix : x₁ ((x₁⁻¹ * x₁⁻¹) v - v) = (x₁⁻¹ * x₁⁻¹) v - v := hfix _ hz
    have hzfix' : x₁⁻¹ ((x₁⁻¹ * x₁⁻¹) v - v) = (x₁⁻¹ * x₁⁻¹) v - v := by
      conv_lhs => rw [← hzfix]
      exact LinearEquiv.symm_apply_apply x₁ ((x₁⁻¹ * x₁⁻¹) v - v)
    change (x₁⁻¹ * x₁⁻¹) (((x₁⁻¹ * x₁⁻¹) v) - v) = ((x₁⁻¹ * x₁⁻¹) v) - v
    rw [LinearEquiv.mul_apply, hzfix', hzfix']
  have hfour : ∀ v : V, (x₁⁻¹ * x₁⁻¹) ((x₁⁻¹ * x₁⁻¹) v) = v := by
    intro v
    have hzv' : (x₁⁻¹ * x₁⁻¹) v = ((x₁⁻¹ * x₁⁻¹) v - v) + v := by
      rw [sub_eq_add_two, add_assoc, add_self_two, add_zero]
    calc (x₁⁻¹ * x₁⁻¹) ((x₁⁻¹ * x₁⁻¹) v)
        = (x₁⁻¹ * x₁⁻¹) (((x₁⁻¹ * x₁⁻¹) v - v) + v) := by
            conv_lhs => rw [hzv']
      _ = (x₁⁻¹ * x₁⁻¹) ((x₁⁻¹ * x₁⁻¹) v - v) + (x₁⁻¹ * x₁⁻¹) v := map_add _ _ _
      _ = ((x₁⁻¹ * x₁⁻¹) v - v) + (x₁⁻¹ * x₁⁻¹) v := by rw [hfixz v]
      _ = v := by
            rw [sub_eq_add_two, add_assoc, add_comm v ((x₁⁻¹ * x₁⁻¹) v), ← add_assoc,
              add_self_two, zero_add]
  have hyy : (x₁⁻¹ * x₁⁻¹) * (x₁⁻¹ * x₁⁻¹) = 1 := by
    apply LinearEquiv.ext
    intro v
    change ((x₁⁻¹ * x₁⁻¹) * (x₁⁻¹ * x₁⁻¹)) v = v
    rw [LinearEquiv.mul_apply]
    exact hfour v
  have hx₁2 : x₁ * x₁ = x₁⁻¹ * x₁⁻¹ := by
    have hyinv : (x₁⁻¹ * x₁⁻¹)⁻¹ = x₁⁻¹ * x₁⁻¹ := inv_eq_of_mul_eq_one_right hyy
    rwa [mul_inv_rev, inv_inv] at hyinv
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_two, pow_two, hx₁2, hyy]

private theorem exists_apply_sub_ne {A : Subgroup (LGL 2 V)}
    (hquad : commSpace A (commSub A) = ⊥)
    {a₁ x₁ : LGL 2 V} (ha₁ : a₁ ∈ A) (ha₁sq : a₁ * a₁ = 1)
    (hinv : a₁ * x₁ * a₁⁻¹ = x₁⁻¹) (hprime : (orderOf x₁).Prime)
    (hodd : Odd (orderOf x₁)) :
    ∃ v : V, a₁ (x₁ (a₁ v - v)) ≠ x₁ (a₁ v - v) := by
  by_contra hcon
  push Not at hcon
  have hfix := x1_fixes_span_of_forall_apply_eq ha₁sq hinv hcon hodd
  have h4 : x₁ ^ 4 = 1 := x1_pow_four_eq_one_of_fixes_span ha₁sq hinv hfix
  have hdvd : orderOf x₁ ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hdvd2 : orderOf x₁ ∣ 2 :=
    hprime.dvd_of_dvd_pow (n := 2) (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hdvd)
  have h2 : orderOf x₁ = 2 := (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp hdvd2
  rw [h2] at hodd
  obtain ⟨k, hk⟩ := hodd
  omega

theorem index_centralizer_le_two (h : Assumption131 G Γ VA i) {A : Subgroup (LGL 2 V)} (hA : A ∈ Γ)
    {X : Subgroup (LGL 2 V)} (hXG : X ≤ G) (hodd : Odd (Nat.card X))
    (hAX : A ≤ Subgroup.normalizer (X : Set (LGL 2 V))) :
    ((A ⊓ Subgroup.centralizer (X : Set (LGL 2 V))).subgroupOf A).index ≤ 2 := by
  classical
  by_contra hgoal
  have hAab : IsElemAbelian 2 A := h.isElemAb A hA
  have hindex : 4 ≤ ((A ⊓ Subgroup.centralizer (X : Set (LGL 2 V))).subgroupOf A).index := by
    by_contra hlt
    exact hgoal (index_le_two_of_lt_four hAab (not_le.mp hlt))
  obtain ⟨d⟩ := lemmaD hAab hAX hodd hindex
  have hx₁G : d.x₁ ∈ G := hXG (d.X₀_le d.x₁_mem)
  have hx₂G : d.x₂ ∈ G := hXG (d.X₀_le d.x₂_mem)
  have hx₁X : d.x₁ ∈ X := d.X₀_le d.x₁_mem
  have hx₂X : d.x₂ ∈ X := d.X₀_le d.x₂_mem
  have ha₁sq : d.a₁ * d.a₁ = 1 := by rw [← pow_two]; exact hAab.2 d.a₁ d.a₁_mem
  have ha₂sq : d.a₂ * d.a₂ = 1 := by rw [← pow_two]; exact hAab.2 d.a₂ d.a₂_mem
  have hx₁odd : Odd (orderOf d.x₁) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard X hx₁X)
  have hx₂odd : Odd (orderOf d.x₂) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard X hx₂X)
  have hp₂odd : Odd d.p₂ := by rw [d.x₂_order] at hx₂odd; exact hx₂odd
  have hprime₁ : (orderOf d.x₁).Prime := by rw [d.x₁_order]; exact d.p₁_prime
  have hquad : commSpace A (commSub A) = ⊥ := h.quadratic A hA
  obtain ⟨v₀, hv₀⟩ := exists_apply_sub_ne (hquad := hquad) (ha₁ := d.a₁_mem)
    (ha₁sq := ha₁sq) (hinv := d.a₁_inverts) (hprime := hprime₁) (hodd := hx₁odd)
  set u : V := d.x₁ (d.a₁ v₀ - v₀) with hu
  set w : V := d.a₁ u - u with hw
  have hwne : w ≠ 0 := by
    intro h0
    apply hv₀
    rw [hw] at h0
    exact sub_eq_zero.mp h0
  have hBA : d.D ⊔ Subgroup.zpowers d.a₂ ≤ A :=
    sup_le (by rw [d.D_eq]; exact inf_le_left) (Subgroup.zpowers_le.mpr d.a₂_mem)
  have h1mOf : mOf A (d.D ⊔ Subgroup.zpowers d.a₂) = 1 := by
    unfold mOf
    rw [d.hyperplane]
    decide
  have hmOf : mOf A (d.D ⊔ Subgroup.zpowers d.a₂) ≤ i := by
    rw [h1mOf]
    exact Nat.succ_le_of_lt h.pos_i
  have hu_fix : u ∈ fixSub (d.D ⊔ Subgroup.zpowers d.a₂) := by
    intro b hb
    have hD_le : d.D ≤ fixingSubgroup u := by
      intro g hg
      have hg' : g ∈ A ⊓ Subgroup.centralizer (d.X₀ : Set (LGL 2 V)) := by
        rwa [d.D_eq] at hg
      have hgA : g ∈ A := hg'.1
      have hgcent : g ∈ Subgroup.centralizer (d.X₀ : Set (LGL 2 V)) := hg'.2
      have hgw₀ : g (d.a₁ v₀ - v₀) = d.a₁ v₀ - v₀ :=
        quadratic_apply_sub hquad d.a₁_mem hgA v₀
      have hcent : d.x₁ * g = g * d.x₁ :=
        (Subgroup.mem_centralizer_iff.mp hgcent) d.x₁ d.x₁_mem
      calc g u = g (d.x₁ (d.a₁ v₀ - v₀)) := by rw [hu]
        _ = (g * d.x₁) (d.a₁ v₀ - v₀) := (LinearEquiv.mul_apply g d.x₁ _).symm
        _ = (d.x₁ * g) (d.a₁ v₀ - v₀) := by rw [hcent]
        _ = d.x₁ (g (d.a₁ v₀ - v₀)) := LinearEquiv.mul_apply d.x₁ g _
        _ = d.x₁ (d.a₁ v₀ - v₀) := by rw [hgw₀]
        _ = u := by rw [hu]
    have hzp_le : Subgroup.zpowers d.a₂ ≤ fixingSubgroup u := by
      refine Subgroup.zpowers_le.mpr ?_
      have ha₂w₀ : d.a₂ (d.a₁ v₀ - v₀) = d.a₁ v₀ - v₀ :=
        quadratic_apply_sub hquad d.a₁_mem d.a₂_mem v₀
      have ha₂x₁ : d.a₂ * d.x₁ = d.x₁ * d.a₂ :=
        mul_comm_of_conj_eq_self d.a₂_centralizes
      show d.a₂ u = u
      calc d.a₂ u = d.a₂ (d.x₁ (d.a₁ v₀ - v₀)) := by rw [hu]
        _ = (d.a₂ * d.x₁) (d.a₁ v₀ - v₀) := (LinearEquiv.mul_apply d.a₂ d.x₁ _).symm
        _ = (d.x₁ * d.a₂) (d.a₁ v₀ - v₀) := by rw [ha₂x₁]
        _ = d.x₁ (d.a₂ (d.a₁ v₀ - v₀)) := LinearEquiv.mul_apply d.x₁ d.a₂ _
        _ = d.x₁ (d.a₁ v₀ - v₀) := by rw [ha₂w₀]
        _ = u := by rw [hu]
    exact (sup_le hD_le hzp_le) hb
  have hwcomm : w ∈ commSpace A (fixSub (d.D ⊔ Subgroup.zpowers d.a₂)) := by
    have h := sub_mem_commSpace (K := A) (U := fixSub (d.D ⊔ Subgroup.zpowers d.a₂))
      d.a₁_mem hu_fix
    rwa [← hw] at h
  have hwVA : w ∈ VA A := h.cond2 A hA (d.D ⊔ Subgroup.zpowers d.a₂) hBA hmOf hwcomm
  have hx₂u : d.x₂ u = u := by
    have hx₂w₀ : d.x₂ (d.a₁ v₀ - v₀) = d.a₁ v₀ - v₀ :=
      apply_eq_of_quadratic_conj (hquad := hquad) d.a₁_mem d.a₂_mem ha₁sq ha₂sq
        (mul_comm_of_conj_eq_self d.a₁_centralizes) d.a₂_inverts hx₂odd v₀
    have hx₂x₁ : d.x₂ * d.x₁ = d.x₁ * d.x₂ := d.x_comm.symm
    calc d.x₂ u = d.x₂ (d.x₁ (d.a₁ v₀ - v₀)) := by rw [hu]
      _ = (d.x₂ * d.x₁) (d.a₁ v₀ - v₀) := (LinearEquiv.mul_apply d.x₂ d.x₁ _).symm
      _ = (d.x₁ * d.x₂) (d.a₁ v₀ - v₀) := by rw [hx₂x₁]
      _ = d.x₁ (d.x₂ (d.a₁ v₀ - v₀)) := LinearEquiv.mul_apply d.x₁ d.x₂ _
      _ = d.x₁ (d.a₁ v₀ - v₀) := by rw [hx₂w₀]
      _ = u := by rw [hu]
  have hx₂w : d.x₂ w = w := by
    have hcomm : d.x₂ * d.a₁ = d.a₁ * d.x₂ :=
      (mul_comm_of_conj_eq_self d.a₁_centralizes).symm
    calc d.x₂ w = d.x₂ (d.a₁ u - u) := by rw [hw]
      _ = d.x₂ (d.a₁ u) - d.x₂ u := map_sub d.x₂ _ _
      _ = (d.x₂ * d.a₁) u - u := by rw [LinearEquiv.mul_apply, hx₂u]
      _ = (d.a₁ * d.x₂) u - u := by rw [hcomm]
      _ = d.a₁ (d.x₂ u) - u := by rw [LinearEquiv.mul_apply]
      _ = d.a₁ u - u := by rw [hx₂u]
      _ = w := by rw [hw]
  have hwVA' : w ∈ VA (cj d.x₂ A) := by
    rw [h.equivariant A hA d.x₂ hx₂G]
    exact Submodule.mem_map.mpr ⟨w, hwVA, hx₂w⟩
  have hAx₂eq : cj d.x₂ A = A := by
    by_contra hne
    have hdisj : VA A ⊓ VA (cj d.x₂ A) = ⊥ :=
      h.disjoint A hA (cj d.x₂ A) (h.invariant A hA d.x₂ hx₂G) (Ne.symm hne)
    have hmem : w ∈ VA A ⊓ VA (cj d.x₂ A) := ⟨hwVA, hwVA'⟩
    rw [hdisj, Submodule.mem_bot] at hmem
    exact hwne hmem
  have hx₂norm : d.x₂ ∈ Subgroup.normalizer (A : Set (LGL 2 V)) :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := A) (g := d.x₂)).mpr hAx₂eq
  have hx₂2A : d.x₂ ^ 2 ∈ A := by
    have ha₂inv' : d.a₂ * d.x₂⁻¹ * d.a₂⁻¹ = d.x₂ := by
      calc d.a₂ * d.x₂⁻¹ * d.a₂⁻¹ = (d.a₂ * d.x₂ * d.a₂⁻¹)⁻¹ := by group
        _ = (d.x₂⁻¹)⁻¹ := by rw [d.a₂_inverts]
        _ = d.x₂ := by group
    have hmem : d.x₂ * d.a₂ * d.x₂⁻¹ * d.a₂⁻¹ ∈ A :=
      A.mul_mem ((Subgroup.mem_normalizer_iff.mp hx₂norm d.a₂).mp d.a₂_mem)
        (A.inv_mem d.a₂_mem)
    have heq : d.x₂ * d.a₂ * d.x₂⁻¹ * d.a₂⁻¹ = d.x₂ ^ 2 := by
      rw [show d.x₂ * d.a₂ * d.x₂⁻¹ * d.a₂⁻¹ = d.x₂ * (d.a₂ * d.x₂⁻¹ * d.a₂⁻¹) by group,
        ha₂inv']
      rw [← pow_two]
    rwa [heq] at hmem
  have hx₂2X : d.x₂ ^ 2 ∈ X := X.pow_mem hx₂X 2
  have hAXbot : A ⊓ X = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hg2 : g ^ 2 = 1 := hAab.2 g hg.1
    have hdvd : orderOf g ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hg.2
    have hoddg : Odd (orderOf g) := Odd.of_dvd_nat hodd hdvd
    have hdvd2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
    exact orderOf_eq_one_iff.mp (odd_dvd_two hoddg hdvd2)
  have hx₂2bot : d.x₂ ^ 2 = 1 := by
    have : d.x₂ ^ 2 ∈ A ⊓ X := ⟨hx₂2A, hx₂2X⟩
    rwa [hAXbot, Subgroup.mem_bot] at this
  have hdvd₂ : orderOf d.x₂ ∣ 2 := orderOf_dvd_of_pow_eq_one hx₂2bot
  have hp₂dvd : d.p₂ ∣ 2 := by rwa [d.x₂_order] at hdvd₂
  have hp₂2 : d.p₂ = 2 := (Nat.prime_dvd_prime_iff_eq d.p₂_prime Nat.prime_two).mp hp₂dvd
  rw [hp₂2] at hp₂odd
  obtain ⟨k, hk⟩ := hp₂odd
  omega

end CFSG.LocalAnalysis.WeakClosure81
