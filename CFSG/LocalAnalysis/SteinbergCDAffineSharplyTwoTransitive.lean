module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.SteinbergCD

theorem perm_apply_inv_self {α : Type*} (f : Equiv.Perm α) (x : α) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

section Defs

variable (K : Type*) [Field K]

@[expose] def affPerm : Subgroup (Equiv.Perm K) where
  carrier := {f | ∃ g : K ≃+ K, ∃ b : K, ∀ x, f x = g x + b}
  one_mem' := ⟨AddEquiv.refl K, 0, fun x => by simp⟩
  mul_mem' := by
    rintro f f' ⟨g, b, hf⟩ ⟨g', b', hf'⟩
    refine ⟨g'.trans g, g b' + b, fun x => ?_⟩
    simp only [Equiv.Perm.mul_apply, hf, hf', map_add, AddEquiv.trans_apply]
    abel
  inv_mem' := by
    rintro f ⟨g, b, hf⟩
    refine ⟨g.symm, -g.symm b, fun x => ?_⟩
    apply f.injective
    rw [perm_apply_inv_self, hf, map_add, map_neg, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply]
    abel

@[expose] def scalarPerm : Subgroup (Equiv.Perm K) where
  carrier := {f | ∃ a : K, a ≠ 0 ∧ ∀ x, f x = a * x}
  one_mem' := ⟨1, one_ne_zero, fun x => by simp⟩
  mul_mem' := by
    rintro f f' ⟨a, ha, hf⟩ ⟨a', ha', hf'⟩
    exact ⟨a * a', mul_ne_zero ha ha', fun x => by
      rw [Equiv.Perm.mul_apply, hf', hf, mul_assoc]⟩
  inv_mem' := by
    rintro f ⟨a, ha, hf⟩
    refine ⟨a⁻¹, inv_ne_zero ha, fun x => ?_⟩
    apply f.injective
    rw [perm_apply_inv_self, hf, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]

@[expose] def translPerm : Subgroup (Equiv.Perm K) where
  carrier := {f | ∃ b : K, ∀ x, f x = x + b}
  one_mem' := ⟨0, fun x => by simp⟩
  mul_mem' := by
    rintro f f' ⟨b, hf⟩ ⟨b', hf'⟩
    exact ⟨b' + b, fun x => by rw [Equiv.Perm.mul_apply, hf', hf, add_assoc]⟩
  inv_mem' := by
    rintro f ⟨b, hf⟩
    refine ⟨-b, fun x => ?_⟩
    apply f.injective
    rw [perm_apply_inv_self, hf, neg_add_cancel_right]

end Defs

section Basic

variable {K : Type*} [Field K]

theorem scalarPerm_le_affPerm : scalarPerm K ≤ affPerm K := by
  rintro f ⟨a, ha, hf⟩
  exact ⟨DistribMulAction.toAddEquiv K (Units.mk0 a ha), 0, fun x => by
    simp [hf, Units.smul_def]⟩

theorem scalarPerm_apply_zero {s : Equiv.Perm K} (hs : s ∈ scalarPerm K) : s 0 = 0 := by
  obtain ⟨a, -, hs⟩ := hs
  rw [hs, mul_zero]

theorem eq_zero_of_scalarPerm_fix {s : Equiv.Perm K} (hs : s ∈ scalarPerm K) (hs1 : s ≠ 1) {x : K}
    (hx : s x = x) : x = 0 := by
  obtain ⟨a, -, has⟩ := hs
  by_contra hx0
  apply hs1
  have ha : a = 1 := by
    have h1 : a * x = 1 * x := by rw [← has, hx, one_mul]
    exact mul_right_cancel₀ hx0 h1
  ext y
  rw [has, ha, one_mul]
  rfl

theorem translPerm_inf_scalarPerm : translPerm K ⊓ scalarPerm K = ⊥ := by
  rw [eq_bot_iff]
  rintro f ⟨⟨b, hf⟩, hs⟩
  have hb : b = 0 := by
    have := scalarPerm_apply_zero hs
    rwa [hf, zero_add] at this
  rw [Subgroup.mem_bot]
  ext x
  rw [hf, hb, add_zero]
  rfl

theorem card_translPerm : Nat.card (translPerm K) = Nat.card K := by
  refine Nat.card_congr
    { toFun := fun f => (f : Equiv.Perm K) 0
      invFun := fun b => ⟨Equiv.addRight b, ⟨b, fun x => rfl⟩⟩
      left_inv := fun f => by
        obtain ⟨b, hb⟩ := f.2
        apply Subtype.ext
        ext x
        simp [hb]
      right_inv := fun b => by simp }

theorem translPerm_regular (x y : K) : ∃! t, t ∈ translPerm K ∧ t x = y := by
  refine ⟨Equiv.addRight (y - x), ⟨⟨y - x, fun z => rfl⟩, by simp⟩, ?_⟩
  rintro t ⟨⟨b, hb⟩, htx⟩
  rw [hb] at htx
  ext z
  rw [hb, Equiv.coe_addRight, ← htx, add_sub_cancel_left]

theorem card_scalarPerm [Finite K] : Nat.card (scalarPerm K) = Nat.card K - 1 := by
  rw [← Nat.card_units]
  refine (Nat.card_congr
    { toFun := fun a => (⟨Units.mulLeft a, ⟨(a : K), a.ne_zero, fun x => rfl⟩⟩ : scalarPerm K)
      invFun := fun f => Units.mk0 ((f : Equiv.Perm K) 1) (by
        obtain ⟨a, ha, hf⟩ := f.2
        rw [hf, mul_one]
        exact ha)
      left_inv := fun a => by
        apply Units.ext
        simp
      right_inv := fun f => by
        obtain ⟨a, ha, hf⟩ := f.2
        apply Subtype.ext
        ext x
        simp [hf] }).symm

variable [CharP K 2]

theorem isElementaryAbelian_translPerm : IsElementaryAbelian 2 (translPerm K) where
  is_comm := ⟨fun f f' => by
    obtain ⟨b, hb⟩ := f.2
    obtain ⟨b', hb'⟩ := f'.2
    apply Subtype.ext
    ext x
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hb, hb']
    abel⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun f => by
    obtain ⟨b, hb⟩ := f.2
    apply Subtype.ext
    ext x
    rw [Subgroup.coe_pow, pow_two, Equiv.Perm.mul_apply, hb, hb, Subgroup.coe_one,
      Equiv.Perm.one_apply, add_assoc, CharTwo.add_self_eq_zero, add_zero]

end Basic

section Linear

variable {K : Type*} [Field K]

@[expose] def linPart (f : Equiv.Perm K) (x : K) : K := f x - f 0

theorem linPart_eq {f : Equiv.Perm K} (hf : f ∈ affPerm K) :
    ∃ g : K ≃+ K, ∀ x, linPart f x = g x := by
  obtain ⟨g, b, hg⟩ := hf
  exact ⟨g, fun x => by rw [linPart, hg, hg, map_zero, zero_add, add_sub_cancel_right]⟩

theorem linPart_mul {f f' : Equiv.Perm K} (hf : f ∈ affPerm K) (x : K) :
    linPart (f * f') x = linPart f (linPart f' x) := by
  obtain ⟨g, hg⟩ := linPart_eq hf
  have h1 : linPart (f * f') x = linPart f (f' x) - linPart f (f' 0) := by
    simp only [linPart, Equiv.Perm.mul_apply]
    abel
  rw [h1, hg, hg, hg, ← map_sub]
  rfl

theorem linPart_injective {f : Equiv.Perm K} : Function.Injective (linPart f) := by
  intro x y h
  exact f.injective (sub_left_injective h)

theorem linPart_zero (f : Equiv.Perm K) : linPart f 0 = 0 := sub_self _

theorem linPart_one : linPart (1 : Equiv.Perm K) = id := by
  funext x
  simp [linPart]

theorem linPart_scalarPerm {s : Equiv.Perm K} {a : K} (hs : ∀ x, s x = a * x) (x : K) :
    linPart s x = a * x := by
  rw [linPart, hs, hs, mul_zero, sub_zero]

theorem mem_translPerm_of_linPart {f : Equiv.Perm K} (h : ∀ x, linPart f x = x) :
    f ∈ translPerm K :=
  ⟨f 0, fun x => by rw [← sub_eq_iff_eq_add]; exact h x⟩

variable [Finite K]

@[expose] noncomputable def linPartHom {Q : Subgroup (Equiv.Perm K)} (hQ : Q ≤ affPerm K) :
    Q →* Equiv.Perm K where
  toFun f := Equiv.ofBijective (linPart (f : Equiv.Perm K))
    (Finite.injective_iff_bijective.1 linPart_injective)
  map_one' := by
    ext x
    simp [linPart_one]
  map_mul' f f' := by
    ext x
    simp only [Equiv.ofBijective_apply, Equiv.Perm.mul_apply, Subgroup.coe_mul]
    exact linPart_mul (hQ f.2) x

variable [CharP K 2]

theorem le_translPerm_of_normal {H Q : Subgroup (Equiv.Perm K)} (hH : H ≤ affPerm K)
    (hS : scalarPerm K ≤ H) (hQH : Q ≤ H) (hQn : (Q.subgroupOf H).Normal)
    (hQ2 : IsPGroup 2 Q) : Q ≤ translPerm K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQA : Q ≤ affPerm K := hQH.trans hH
  let _ : MulAction Q K := MulAction.compHom K (linPartHom hQA)
  have hmod := hQ2.card_modEq_card_fixedPoints K
  have heven : 2 ∣ Nat.card K := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 2 n.ne_zero
  have hfix : 2 ∣ Nat.card (MulAction.fixedPoints Q K) :=
    Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 heven))
  have h0mem : (0 : K) ∈ MulAction.fixedPoints Q K := fun f => linPart_zero (f : Equiv.Perm K)
  obtain ⟨⟨w, hw⟩, hne⟩ : ∃ x : MulAction.fixedPoints Q K, x ≠ ⟨0, h0mem⟩ := by
    by_contra hall
    push Not at hall
    have h1 : Nat.card (MulAction.fixedPoints Q K) = 1 :=
      Nat.card_eq_one_iff_exists.2 ⟨⟨0, h0mem⟩, hall⟩
    rw [h1] at hfix
    norm_num at hfix
  have hw0 : w ≠ 0 := fun h => hne (Subtype.ext h)
  have hwfix : ∀ f : Q, linPart (f : Equiv.Perm K) w = w := fun f => hw f
  intro f hf
  refine mem_translPerm_of_linPart fun y => ?_
  by_cases hy : y = 0
  · rw [hy, linPart_zero]
  set a := y / w with ha
  have ha0 : a ≠ 0 := div_ne_zero hy hw0
  have hay : a * w = y := div_mul_cancel₀ y hw0
  set s : Equiv.Perm K := Units.mulLeft (Units.mk0 a ha0) with hsdef
  have hs : ∀ x, s x = a * x := fun x => rfl
  have hsS : s ∈ scalarPerm K := ⟨a, ha0, hs⟩
  have hsH : s ∈ H := hS hsS
  have hs' : ∀ x, s⁻¹ x = a⁻¹ * x := fun x => by
    apply s.injective
    rw [perm_apply_inv_self, hs, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
  have hconj : s⁻¹ * f * s ∈ Q := by
    have h := hQn.conj_mem ⟨f, hQH hf⟩ (Subgroup.mem_subgroupOf.mpr hf) ⟨s, hsH⟩⁻¹
    rw [inv_inv] at h
    exact Subgroup.mem_subgroupOf.mp h
  have h1 := hwfix ⟨_, hconj⟩
  simp only at h1
  rw [linPart_mul (mul_mem (scalarPerm_le_affPerm (inv_mem hsS)) (hQA hf)),
    linPart_mul (scalarPerm_le_affPerm (inv_mem hsS)), linPart_scalarPerm hs,
    linPart_scalarPerm hs', hay] at h1
  calc linPart f y = a * (a⁻¹ * linPart f y) := by rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
    _ = a * w := by rw [h1]
    _ = y := hay

end Linear

theorem perm_inv_apply_self {α : Type*} (f : Equiv.Perm α) (x : α) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

section Counting

variable {K : Type*} [Field K] {F : Subgroup (Equiv.Perm K)}
  (htrans : ∀ x y : K, ∃ f ∈ F, f x = y)
  (hF0 : ∀ f : Equiv.Perm K, f ∈ F ∧ f 0 = 0 ↔ f ∈ scalarPerm K)

include htrans hF0

theorem eq_of_fixed {f : Equiv.Perm K} (hf : f ∈ F) (hf1 : f ≠ 1) {x y : K} (hx : f x = x)
    (hy : f y = y) : x = y := by
  obtain ⟨h, hh, hh0⟩ := htrans 0 x
  have hF' : h⁻¹ * f * h ∈ F := mul_mem (mul_mem (inv_mem hh) hf) hh
  have h0 : (h⁻¹ * f * h) 0 = 0 := by
    simp only [Equiv.Perm.mul_apply, hh0, hx]
    rw [← hh0, perm_inv_apply_self]
  have hS' := (hF0 _).1 ⟨hF', h0⟩
  have h1 : h⁻¹ * f * h ≠ 1 := fun h1 => hf1 (by
    have : f = h * (h⁻¹ * f * h) * h⁻¹ := by group
    rw [this, h1, mul_one, mul_inv_cancel])
  have hy' : (h⁻¹ * f * h) (h⁻¹ y) = h⁻¹ y := by
    simp only [Equiv.Perm.mul_apply, perm_apply_inv_self, hy]
  have hz := eq_zero_of_scalarPerm_fix hS' h1 hy'
  rw [← hh0, ← hz, perm_apply_inv_self]

variable [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem card_F : Nat.card F = Nat.card K * (Nat.card K - 1) := by
  classical
  have := Fintype.ofFinite K
  have hstab0 : (Finset.univ.filter (fun f : Equiv.Perm K => f ∈ F ∧ f 0 = 0)).card =
      Nat.card K - 1 := by
    rw [← card_scalarPerm, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact congrArg Finset.card (Finset.filter_congr fun f _ => hF0 f)
  have hfiber : ∀ x : K, (Finset.univ.filter (fun f : Equiv.Perm K => f ∈ F ∧ f 0 = x)).card =
      Nat.card K - 1 := by
    intro x
    obtain ⟨h, hh, hh0⟩ := htrans 0 x
    rw [← hstab0]
    refine Finset.card_nbij' (fun f => h⁻¹ * f) (fun g => h * g) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
      refine ⟨mul_mem (inv_mem hh) hf.1, ?_⟩
      rw [Equiv.Perm.mul_apply, hf.2, ← hh0, perm_inv_apply_self]
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
      exact ⟨mul_mem hh hg.1, by rw [Equiv.Perm.mul_apply, hg.2, hh0]⟩
    · intro f _
      simp only
      group
    · intro g _
      simp only
      group
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_card_fiberwise (f := fun f : Equiv.Perm K => f 0) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  have h : ∀ x : K, ((Finset.univ.filter fun f : Equiv.Perm K => f ∈ F).filter
      fun f => f 0 = x).card = Nat.card K - 1 := fun x => by
    rw [Finset.filter_filter]
    exact hfiber x
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card]

theorem mem_sylow_iff {P : Subgroup (Equiv.Perm K)} (hPF : P ≤ F) (hP2 : IsPGroup 2 P)
    (hPcard : Nat.card P = Nat.card K) (f : Equiv.Perm K) :
    f ∈ P ↔ f ∈ F ∧ (f = 1 ∨ ∀ x, f x ≠ x) := by
  classical
  have := Fintype.ofFinite K
  have hodd : Odd (Nat.card K - 1) := by
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hn]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, n.ne_zero⟩) odd_one
  set Fs := Finset.univ.filter (fun f : Equiv.Perm K => f ∈ F) with hFs
  have hstab0 : (Finset.univ.filter (fun f : Equiv.Perm K => f ∈ F ∧ f 0 = 0)).card =
      Nat.card K - 1 := by
    rw [← card_scalarPerm, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact congrArg Finset.card (Finset.filter_congr fun f _ => hF0 f)
  have hstab : ∀ x : K, (Finset.univ.filter (fun f : Equiv.Perm K => f ∈ F ∧ f x = x)).card =
      Nat.card K - 1 := by
    intro x
    obtain ⟨h, hh, hh0⟩ := htrans 0 x
    rw [← hstab0]
    refine Finset.card_nbij' (fun f => h⁻¹ * f * h) (fun g => h * g * h⁻¹) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
      refine ⟨mul_mem (mul_mem (inv_mem hh) hf.1) hh, ?_⟩
      simp only [Equiv.Perm.mul_apply, hh0, hf.2]
      rw [← hh0, perm_inv_apply_self]
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
      refine ⟨mul_mem (mul_mem hh hg.1) (inv_mem hh), ?_⟩
      simp only [Equiv.Perm.mul_apply]
      rw [← hh0, perm_inv_apply_self, hg.2]
    · intro f _
      simp only
      group
    · intro g _
      simp only
      group
  have hFcard : Fs.card = Nat.card K * (Nat.card K - 1) := by
    rw [← card_F htrans hF0, Nat.card_eq_fintype_card, Fintype.card_subtype]
  set c : Equiv.Perm K → ℕ := fun g => (Finset.univ.filter (fun x : K => g x = x)).card
  have hsum : ∑ g ∈ Fs, c g = Fs.card := by
    rw [hFcard]
    simp only [c, Finset.card_filter]
    rw [Finset.sum_comm]
    have h : ∀ x : K, ∑ g ∈ Fs, (if g x = x then 1 else 0) = Nat.card K - 1 := fun x => by
      rw [← hstab x, Finset.card_filter, hFs, Finset.sum_filter]
      refine Finset.sum_congr rfl fun g _ => ?_
      by_cases hg : g ∈ F <;> by_cases hgx : g x = x <;> simp [hg, hgx]
    rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.card_eq_fintype_card]
  have hfree : ∀ g ∈ P, g ≠ 1 → ∀ x, g x ≠ x := by
    intro g hg hg1 x hx
    apply hg1
    set Fx : Subgroup (Equiv.Perm K) := F ⊓ MulAction.stabilizer (Equiv.Perm K) x
    have hgFx : g ∈ Fx := ⟨hPF hg, hx⟩
    have hcardFx : Nat.card Fx = Nat.card K - 1 := by
      rw [← hstab x, Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact congrArg Finset.card (Finset.filter_congr fun f _ => Iff.rfl)
    have h1 := Subgroup.orderOf_dvd_natCard Fx hgFx
    obtain ⟨k, hk⟩ := hP2 ⟨g, hg⟩
    have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 := orderOf_dvd_of_pow_eq_one hk'
    rw [hcardFx] at h1
    have hcop : Nat.Coprime (2 ^ k) (Nat.card K - 1) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h2 h1)
  constructor
  · intro hf
    by_cases hf1 : f = 1
    · exact ⟨hPF hf, Or.inl hf1⟩
    · exact ⟨hPF hf, Or.inr (hfree f hf hf1)⟩
  rintro ⟨hfF, hf1 | hfree0⟩
  · rw [hf1]
    exact P.one_mem
  by_contra hfP
  set Ps := Finset.univ.filter (fun f : Equiv.Perm K => f ∈ P) with hPsdef
  have hPs : Ps ⊆ Fs := fun g hg => by
    simp only [Ps, Fs, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    exact hPF hg
  have hPscard : Ps.card = Nat.card K := by
    rw [← hPcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.sum_sdiff hPs] at hsum
  have hsumP : ∑ g ∈ Ps, c g = Nat.card K := by
    rw [Finset.sum_eq_single 1]
    · simp only [c, Equiv.Perm.one_apply]
      rw [Finset.filter_true_of_mem fun _ _ => trivial, Finset.card_univ,
        Nat.card_eq_fintype_card]
    · intro g hg hg1
      simp only [Ps, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      simp only [c, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
        true_implies]
      exact hfree g hg hg1
    · intro h1
      exact absurd (by simp [Ps] : (1 : Equiv.Perm K) ∈ Ps) h1
  have hfmem : f ∈ Fs \ Ps := by
    simp only [Fs, Ps, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hfF, hfP⟩
  have hcf : c f = 0 := by
    simp only [c, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
    exact hfree0
  have hle : ∀ g ∈ (Fs \ Ps).erase f, c g ≤ 1 := by
    intro g hg
    simp only [Fs, Ps, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
      true_and] at hg
    have hg1 : g ≠ 1 := fun h1 => hg.2.2 (h1 ▸ P.one_mem)
    exact Finset.card_le_one.2 fun x hx y hy => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact eq_of_fixed htrans hF0 hg.2.1 hg1 hx hy
  have hsplit := Finset.add_sum_erase (Fs \ Ps) c hfmem
  have hbound : ∑ g ∈ (Fs \ Ps).erase f, c g ≤ ((Fs \ Ps).erase f).card := by
    calc ∑ g ∈ (Fs \ Ps).erase f, c g ≤ ∑ g ∈ (Fs \ Ps).erase f, 1 := Finset.sum_le_sum hle
      _ = ((Fs \ Ps).erase f).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  have hcard1 : ((Fs \ Ps).erase f).card = (Fs \ Ps).card - 1 := Finset.card_erase_of_mem hfmem
  have hcard2 : (Fs \ Ps).card = Fs.card - Ps.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hPs]
  have hpos : 1 ≤ (Fs \ Ps).card := Finset.card_pos.2 ⟨f, hfmem⟩
  have hPle : Ps.card ≤ Fs.card := Finset.card_le_card hPs
  omega

end Counting

theorem affine_scalar_sharply_two_transitive_normal_translations (K : Type*) [Field K] [Finite K]
    [CharP K 2] (H F : Subgroup (Equiv.Perm K)) (hH : H ≤ affPerm K) (hS : scalarPerm K ≤ H)
    (hFH : F ≤ H) (hFn : (F.subgroupOf H).Normal) (htrans : ∀ x y : K, ∃ f ∈ F, f x = y)
    (hF0 : ∀ f : Equiv.Perm K, f ∈ F ∧ f 0 = 0 ↔ f ∈ scalarPerm K) :
    translPerm K ≤ H ∧ CFSG.pCore 2 H = (translPerm K).subgroupOf H ∧
      translPerm K ≤ F ∧ ((translPerm K).subgroupOf F).Normal ∧
      translPerm K ⊓ scalarPerm K = ⊥ ∧ translPerm K ⊔ scalarPerm K = F ∧
      IsElementaryAbelian 2 (translPerm K) ∧ Nat.card (translPerm K) = Nat.card K ∧
      ∀ x y : K, ∃! t, t ∈ translPerm K ∧ t x = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hq : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hq1 : 1 ≤ Nat.card K := Finite.card_pos
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 F) := inferInstance
  set P : Subgroup (Equiv.Perm K) := (P₀ : Subgroup F).map F.subtype with hPdef
  have hPF : P ≤ F := by
    rintro _ ⟨g, -, rfl⟩
    exact g.2
  have hP2 : IsPGroup 2 P := P₀.isPGroup'.map _
  have hPcard : Nat.card P = Nat.card K := by
    rw [hPdef, Subgroup.card_map_of_injective F.subtype_injective, P₀.card_eq_multiplicity,
      card_F htrans hF0, hq]
    have hodd : ¬ 2 ∣ 2 ^ (n : ℕ) - 1 := by
      rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
      exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, n.ne_zero⟩) odd_one
    rw [Nat.factorization_mul (by positivity) (by
        have : 1 < 2 ^ (n : ℕ) := Nat.one_lt_two_pow n.ne_zero
        omega),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hodd, Finsupp.single_eq_same, add_zero]
  have hPchar := mem_sylow_iff htrans hF0 hPF hP2 hPcard
  have hPn : (P.subgroupOf H).Normal := by
    refine ⟨fun g hg h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    obtain ⟨hgF, hg1⟩ := (hPchar g).1 hg
    have hconjF : (h : Equiv.Perm K) * g * (h : Equiv.Perm K)⁻¹ ∈ F := by
      have := hFn.conj_mem ⟨g, hFH hgF⟩ (Subgroup.mem_subgroupOf.mpr hgF) h
      exact Subgroup.mem_subgroupOf.mp this
    refine (hPchar _).2 ⟨by simpa using hconjF, ?_⟩
    rcases hg1 with h1 | hfree
    · left
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h1, mul_one, Subgroup.coe_inv, mul_inv_cancel]
    · right
      intro x hx
      apply hfree ((h : Equiv.Perm K)⁻¹ x)
      have := congrArg (fun y => (h : Equiv.Perm K)⁻¹ y) hx
      simpa [Equiv.Perm.mul_apply] using this
  have hPT : P ≤ translPerm K := le_translPerm_of_normal hH hS (hPF.trans hFH) hPn hP2
  have hPeq : P = translPerm K :=
    Subgroup.eq_of_le_of_card_ge hPT (by rw [card_translPerm, hPcard])
  have hTF : translPerm K ≤ F := hPeq ▸ hPF
  have hTH : translPerm K ≤ H := hTF.trans hFH
  have hTn : ((translPerm K).subgroupOf H).Normal := hPeq ▸ hPn
  have hTel := isElementaryAbelian_translPerm (K := K)
  refine ⟨hTH, ?_, hTF, ?_, translPerm_inf_scalarPerm, ?_, hTel, card_translPerm,
    translPerm_regular⟩
  ·
    apply le_antisymm
    · intro x hx
      have hQ : (CFSG.pCore 2 H).map H.subtype ≤ translPerm K := by
        refine le_translPerm_of_normal hH hS (Subgroup.map_subtype_le _) ?_ ?_
        · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
          exact CFSG.pCore_normal
        · exact CFSG.pCore_isPGroup.map _
      exact Subgroup.mem_subgroupOf.mpr (hQ ⟨x, hx, rfl⟩)
    · refine le_sSup ⟨hTn, ?_⟩
      have h2 : IsPGroup 2 (translPerm K) := IsElementaryAbelian.isPGroup 2 _
      exact h2.comap_of_injective H.subtype H.subtype_injective |>.to_le (by
        intro x hx
        exact hx)
  ·
    refine ⟨fun g hg f => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    have := hTn.conj_mem ⟨g, hTH hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨f, hFH f.2⟩
    exact Subgroup.mem_subgroupOf.mp this
  ·
    apply le_antisymm (sup_le hTF fun s hs => ((hF0 s).2 hs).1)
    intro f hf
    have ht : Equiv.addRight (f 0) ∈ translPerm K := ⟨f 0, fun x => rfl⟩
    have hs : (Equiv.addRight (f 0))⁻¹ * f ∈ scalarPerm K := by
      refine (hF0 _).1 ⟨mul_mem (inv_mem (hTF ht)) hf, ?_⟩
      rw [Equiv.Perm.mul_apply]
      apply (Equiv.addRight (f 0)).injective
      rw [perm_apply_inv_self, Equiv.coe_addRight]
      exact (zero_add _).symm
    have : f = Equiv.addRight (f 0) * ((Equiv.addRight (f 0))⁻¹ * f) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hs)

end CFSG.LocalAnalysis.SteinbergCD
