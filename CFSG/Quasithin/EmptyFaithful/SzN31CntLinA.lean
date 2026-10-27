module

public import CFSG.Quasithin.EmptyFaithful.SzN31CntFrame
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.Quasithin.SzN31

theorem gFun_ge_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : 2 ≤ gFun p := by
  have _ := hp
  have _ := hp2
  unfold gFun
  split_ifs <;> omega

theorem gFun_ge_four {p : ℕ} (hp5 : 5 ≤ p) : 4 ≤ gFun p := by
  unfold gFun
  split_ifs <;> omega

theorem eq_five_of_gFun_eq_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : gFun p = 4) :
    p = 5 := by
  have _ := hp
  have _ := hp2
  unfold gFun at h
  split_ifs at h <;> omega

theorem gFun_le_of_dvd {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n) (he : Even n)
    (hd : p ∣ 2 ^ n - 1) : gFun p ≤ n := by
  obtain ⟨m, hm⟩ := he
  have hn2 : 2 ≤ n := by omega
  unfold gFun
  split_ifs with h3 h5
  · exact hn2
  · by_contra hlt
    have : n = 2 := by omega
    subst this
    subst h5
    norm_num at hd
  · have hp7 : 7 ≤ p := by
      by_contra hlt
      have h2 := hp.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hp (by decide)
      have h6 : p ≠ 6 := by
        rintro rfl
        exact absurd hp (by decide)
      omega
    by_contra hlt
    have : n = 2 ∨ n = 4 := by omega
    rcases this with rfl | rfl
    · have h3' : p ∣ 3 := by simpa using hd
      have := Nat.le_of_dvd (by norm_num) h3'
      omega
    · have h15 : p ∣ 3 * 5 := by simpa using hd
      rcases (Nat.Prime.dvd_mul hp).1 h15 with h | h
      · have := Nat.le_of_dvd (by norm_num) h
        omega
      · have := Nat.le_of_dvd (by norm_num) h
        omega

theorem three_le_of_dvd {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n)
    (hd : p ∣ 2 ^ n - 1) : 3 ≤ n := by
  have _ := hp
  by_contra hlt
  have : n = 1 ∨ n = 2 := by omega
  rcases this with rfl | rfl
  · have h1 : p ∣ 1 := by simpa using hd
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  · have h3 : p ∣ 3 := by simpa using hd
    have := Nat.le_of_dvd (by norm_num) h3
    omega

namespace CntLin

section Basic

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem zmod2_add_self (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_smul]

theorem zmod2_neg (v : V) : -v = v := neg_eq_of_add_eq_zero_right (zmod2_add_self v)

theorem nsmul_odd {p : ℕ} (hp : Odd p) (v : V) : p • v = v := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_eq_one_iff_odd.2 hp, one_smul]

theorem mem_fixSp {t : V ≃ₗ[ZMod 2] V} {S : Submodule (ZMod 2) V} {v : V} :
    v ∈ fixSp V t S ↔ v ∈ S ∧ t v = v := by
  simp [fixSp, sub_eq_zero]

theorem mem_commSp {t : V ≃ₗ[ZMod 2] V} {S : Submodule (ZMod 2) V} {v : V} :
    v ∈ commSp V t S ↔ ∃ s ∈ S, t s - s = v := by
  simp [commSp]

theorem pow_succ_apply (x : V ≃ₗ[ZMod 2] V) (n : ℕ) (v : V) :
    (x ^ (n + 1)) v = x ((x ^ n) v) := by
  rw [pow_succ', LinearEquiv.mul_apply]

theorem pow_succ_apply' (x : V ≃ₗ[ZMod 2] V) (n : ℕ) (v : V) :
    (x ^ (n + 1)) v = (x ^ n) (x v) := by
  rw [pow_succ, LinearEquiv.mul_apply]

theorem pow_apply_mem {x : V ≃ₗ[ZMod 2] V} {S : Submodule (ZMod 2) V} (hS : ∀ s ∈ S, x s ∈ S)
    (n : ℕ) {s : V} (hs : s ∈ S) : (x ^ n) s ∈ S := by
  induction n with
  | zero => simpa using hs
  | succ n ih => rw [pow_succ_apply]; exact hS _ ih

theorem telescope (x : V ≃ₗ[ZMod 2] V) (s : V) (n : ℕ) :
    x (∑ i ∈ Finset.range n, (x ^ i) s) - ∑ i ∈ Finset.range n, (x ^ i) s = (x ^ n) s - s := by
  calc _ = ∑ i ∈ Finset.range n, ((x ^ (i + 1)) s - (x ^ i) s) := by
        simp only [map_sum, ← Finset.sum_sub_distrib, pow_succ_apply]
    _ = (x ^ n) s - s := by rw [Finset.sum_range_sub (fun i => (x ^ i) s) n]; simp

theorem inv_apply_mem {x : V ≃ₗ[ZMod 2] V} {p : ℕ} (hp : 0 < p) (hx : x ^ p = 1)
    {S : Submodule (ZMod 2) V} (hS : ∀ s ∈ S, x s ∈ S) {s : V} (hs : s ∈ S) : x⁻¹ s ∈ S := by
  have h : x⁻¹ = x ^ (p - 1) := by
    refine (eq_inv_of_mul_eq_one_right ?_).symm
    rw [← pow_succ', Nat.sub_add_cancel hp]
    exact hx
  rw [h]
  exact pow_apply_mem hS _ hs

end Basic

section Dihedral

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem apply_inv_apply (x : V ≃ₗ[ZMod 2] V) (v : V) : x (x⁻¹ v) = v := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]
  rfl

theorem inv_apply_apply (x : V ≃ₗ[ZMod 2] V) (v : V) : x⁻¹ (x v) = v := by
  rw [← LinearEquiv.mul_apply, inv_mul_cancel]
  rfl

theorem dihedral_apply_x {x a : V ≃ₗ[ZMod 2] V} (hax : a * x * a⁻¹ = x⁻¹) (v : V) :
    a (x v) = x⁻¹ (a v) := by
  have h : a * x = x⁻¹ * a := by
    calc a * x = a * x * a⁻¹ * a := (inv_mul_cancel_right _ _).symm
      _ = x⁻¹ * a := by rw [hax]
  have := DFunLike.congr_fun h v
  rwa [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this

theorem dihedral_apply_xinv {x a : V ≃ₗ[ZMod 2] V} (hax : a * x * a⁻¹ = x⁻¹) (v : V) :
    a (x⁻¹ v) = x (a v) := by
  have h := dihedral_apply_x hax (x⁻¹ v)
  rw [apply_inv_apply] at h
  rw [h, apply_inv_apply]

theorem fix_of_sq_fix {x : V ≃ₗ[ZMod 2] V} {p : ℕ} (hp : Odd p) (hx : x ^ p = 1) {t : V}
    (h : x (x t) = t) : x t = t := by
  obtain ⟨k, rfl⟩ := hp
  have h1 : ∀ m : ℕ, (x ^ (2 * m)) t = t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ_apply, pow_succ_apply, ih]
      exact h
  have h2 : x ^ (2 * (k + 1)) = x := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hx, one_mul]
  calc x t = (x ^ (2 * (k + 1))) t := by rw [h2]
    _ = t := h1 _

end Dihedral

end CntLin

open CntLin

theorem decomp_fix_comm {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (x : V ≃ₗ[ZMod 2] V)
    {p : ℕ} (hp : Odd p) (hx : x ^ p = 1) (S : Submodule (ZMod 2) V) (hS : ∀ s ∈ S, x s ∈ S) :
    Disjoint (fixSp V x S) (commSp V x S) ∧ fixSp V x S ⊔ commSp V x S = S := by
  have hxp : ∀ s : V, (x ^ p) s = s := fun s => by rw [hx]; rfl
  constructor
  · rw [Submodule.disjoint_def]
    intro t ht ht'
    rw [mem_fixSp] at ht
    obtain ⟨s', hs', rfl⟩ := mem_commSp.1 ht'
    have h1 : ∑ i ∈ Finset.range p, (x ^ i) (x s' - s') = 0 := by
      have e : ∀ i, (x ^ i) (x s' - s') = (x ^ (i + 1)) s' - (x ^ i) s' := by
        intro i; rw [map_sub, pow_succ_apply']
      simp only [e]
      rw [Finset.sum_range_sub (fun i => (x ^ i) s') p]
      simp [hxp]
    have h2 : ∀ i, (x ^ i) (x s' - s') = x s' - s' := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ_apply, ih]; exact ht.2
    simp only [h2, Finset.sum_const, Finset.card_range] at h1
    rwa [nsmul_odd hp] at h1
  · apply le_antisymm
    · refine sup_le inf_le_left ?_
      rintro v hv
      obtain ⟨s, hs, rfl⟩ := mem_commSp.1 hv
      exact sub_mem (hS s hs) hs
    · intro s hs
      set N : V := ∑ i ∈ Finset.range p, (x ^ i) s with hN
      set M : V := ∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, (x ^ i) s with hM
      have hNS : N ∈ S := Submodule.sum_mem _ fun i _ => pow_apply_mem hS i hs
      have hMS : M ∈ S :=
        Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => pow_apply_mem hS i hs
      have hNfix : x N = N := sub_eq_zero.1 (by rw [hN, telescope, hxp, sub_self])
      have hMM : x M - M = N - s := by
        rw [hM, map_sum, ← Finset.sum_sub_distrib]
        simp only [telescope]
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_odd hp]
      have hkey : x (-M) - -M = s - N := by
        rw [map_neg, neg_sub_neg, ← neg_sub, hMM, neg_sub]
      have h1 : N ∈ fixSp V x S := mem_fixSp.2 ⟨hNS, hNfix⟩
      have h2 : s - N ∈ commSp V x S := mem_commSp.2 ⟨-M, S.neg_mem hMS, hkey⟩
      have := Submodule.add_mem_sup h1 h2
      rwa [add_sub_cancel] at this

theorem pgroup_dvd_two_pow {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {q : ℕ}
    (hq : q.Prime) (P : Subgroup (V ≃ₗ[ZMod 2] V)) (hP : IsPGroup q P) (T : Submodule (ZMod 2) V)
    (hT : ∀ g ∈ P, ∀ v ∈ T, g v ∈ T) (h0 : ∀ v ∈ T, (∀ g ∈ P, g v = v) → v = 0) :
    q ∣ 2 ^ Module.finrank (ZMod 2) T - 1 := by
  have : Fact q.Prime := ⟨hq⟩
  let T' : SubMulAction P V := ⟨(T : Set V), fun g v hv => hT g g.2 v hv⟩
  have hmod := hP.card_modEq_card_fixedPoints T'
  have hfix : Nat.card (MulAction.fixedPoints P T') = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨⟨0, T.zero_mem⟩, fun g => Subtype.ext (smul_zero g)⟩⟩⟩
    have ha : ((a : T') : V) = 0 := h0 _ (a.1).2 fun g hg => congrArg Subtype.val (a.2 ⟨g, hg⟩)
    have hb : ((b : T') : V) = 0 := h0 _ (b.1).2 fun g hg => congrArg Subtype.val (b.2 ⟨g, hg⟩)
    exact Subtype.ext (Subtype.ext (ha.trans hb.symm))
  have hcard : Nat.card T' = 2 ^ Module.finrank (ZMod 2) T := by
    have : Module.Finite (ZMod 2) T := Module.Finite.of_finite
    rw [show Nat.card T' = Nat.card T from Nat.card_congr (Equiv.refl _),
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hfix, hcard] at hmod
  exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).1 hmod.symm

theorem cyclic_dvd_two_pow {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {q : ℕ}
    (hq : q.Prime) (x : V ≃ₗ[ZMod 2] V) (hx : x ^ q = 1) (T : Submodule (ZMod 2) V)
    (hxT : ∀ t ∈ T, x t ∈ T) (h0 : ∀ t ∈ T, x t = t → t = 0) :
    q ∣ 2 ^ Module.finrank (ZMod 2) T - 1 := by
  have hinv : ∀ t ∈ T, x⁻¹ t ∈ T := fun t ht => inv_apply_mem hq.pos hx hxT ht
  have hz : ∀ k : ℤ, ∀ t ∈ T, (x ^ k) t ∈ T := by
    intro k
    induction k using Int.induction_on with
    | zero => intro t ht; simpa using ht
    | succ k ih => intro t ht; rw [zpow_add_one, LinearEquiv.mul_apply]; exact ih _ (hxT t ht)
    | pred k ih => intro t ht; rw [zpow_sub_one, LinearEquiv.mul_apply]; exact ih _ (hinv t ht)
  refine pgroup_dvd_two_pow hq (Subgroup.zpowers x) ?_ T ?_ ?_
  · intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  · intro g hg t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact hz k t ht
  · intro v hv hfix
    exact h0 v hv (hfix x (Subgroup.mem_zpowers x))

theorem dihedral_split {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (x a : V ≃ₗ[ZMod 2] V) {p : ℕ} (hx : x ^ p = 1) (hp : Odd p) (ha : a * a = 1)
    (hax : a * x * a⁻¹ = x⁻¹) (T : Submodule (ZMod 2) V) (hxT : ∀ t ∈ T, x t ∈ T)
    (haT : ∀ t ∈ T, a t ∈ T) (hfp : fixSp V x T = ⊥) :
    Disjoint (fixSp V a T) ((fixSp V a T).map (x : V →ₗ[ZMod 2] V)) ∧
      fixSp V a T ⊔ (fixSp V a T).map (x : V →ₗ[ZMod 2] V) = T := by
  have hxinv : ∀ t ∈ T, x⁻¹ t ∈ T := fun t ht => inv_apply_mem hp.pos hx hxT ht
  have haa : ∀ v, a (a v) = v := by
    intro v
    rw [← LinearEquiv.mul_apply, ha]
    rfl
  have hsq : ∀ t ∈ T, x (x t) = t → t = 0 := by
    intro t ht h
    have hmem : t ∈ fixSp V x T := mem_fixSp.2 ⟨ht, fix_of_sq_fix hp hx h⟩
    rw [hfp] at hmem
    simpa using hmem
  let σ : V →ₗ[ZMod 2] V := (x : V →ₗ[ZMod 2] V) + ((x⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)
  have hσ : ∀ v, σ v = x v + x⁻¹ v := fun v => rfl
  have hσT : ∀ t ∈ T, σ t ∈ T := fun t ht => T.add_mem (hxT t ht) (hxinv t ht)
  have hσinj : ∀ t ∈ T, σ t = 0 → t = 0 := by
    intro t ht h
    refine hsq t ht ?_
    have h' : x (x t) + t = 0 := by
      have := congrArg x h
      rwa [hσ, map_add, apply_inv_apply, map_zero] at this
    exact (eq_neg_of_add_eq_zero_left h').trans (zmod2_neg t)
  have hsurj : ∀ u ∈ T, ∃ w ∈ T, σ w = u := by
    intro u hu
    let f : T → T := fun t => ⟨σ t, hσT t t.2⟩
    have hf : Function.Injective f := by
      intro t t' h
      have h1 : σ ((t : V) - t') = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val h
      exact Subtype.ext (sub_eq_zero.1 (hσinj _ (T.sub_mem t.2 t'.2) h1))
    obtain ⟨w, hw⟩ := Finite.injective_iff_surjective.1 hf ⟨u, hu⟩
    exact ⟨w, w.2, congrArg Subtype.val hw⟩
  have hcomm : ∀ v, σ (a v) = a (σ v) := by
    intro v
    rw [hσ, hσ, map_add, dihedral_apply_x hax, dihedral_apply_xinv hax, add_comm]
  have hspan : ∀ t ∈ T,
      t ∈ fixSp V a T ⊔ (fixSp V a T).map (x : V →ₗ[ZMod 2] V) := by
    intro t ht
    have hu : t + a t ∈ T := T.add_mem ht (haT t ht)
    obtain ⟨w', hw'T, hw'⟩ := hsurj _ hu
    have haw' : a w' = w' := by
      have h1 : σ (a w' + w') = 0 := by
        rw [map_add, hcomm, hw', map_add, haa]
        calc a t + t + (t + a t) = (a t + a t) + (t + t) := by abel
          _ = 0 := by rw [zmod2_add_self, zmod2_add_self, add_zero]
      have h2 := hσinj _ (T.add_mem (haT w' hw'T) hw'T) h1
      exact (eq_neg_of_add_eq_zero_left h2).trans (zmod2_neg w')
    have hwT : t + x w' ∈ T := T.add_mem ht (hxT w' hw'T)
    have haw : a (t + x w') = t + x w' := by
      have h2 : (t + x w') + a (t + x w') = 0 := by
        rw [map_add, dihedral_apply_x hax, haw']
        calc t + x w' + (a t + x⁻¹ w') = (t + a t) + (x w' + x⁻¹ w') := by abel
          _ = 0 := by rw [← hσ, hw', zmod2_add_self]
      exact (eq_neg_of_add_eq_zero_right h2).trans (zmod2_neg _)
    have hmem : t + x w' ∈ fixSp V a T := mem_fixSp.2 ⟨hwT, haw⟩
    have hmem2 : x w' ∈ (fixSp V a T).map (x : V →ₗ[ZMod 2] V) :=
      Submodule.mem_map.2 ⟨w', mem_fixSp.2 ⟨hw'T, haw'⟩, rfl⟩
    have := Submodule.add_mem_sup hmem hmem2
    rwa [add_assoc, zmod2_add_self, add_zero] at this
  refine ⟨?_, le_antisymm ?_ hspan⟩
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv'
    have hw1 := mem_fixSp.1 hw
    have hv1 : a (x w) = x w := (mem_fixSp.1 hv).2
    have h1 : x w = x⁻¹ w := by
      rw [← hv1, dihedral_apply_x hax, hw1.2]
    have h2 : x (x w) = w := by rw [h1, apply_inv_apply]
    rw [hsq w hw1.1 h2, map_zero]
  · refine sup_le inf_le_left ?_
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
    exact hxT w (mem_fixSp.1 hw).1

theorem dihedral_finrank {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (x a : V ≃ₗ[ZMod 2] V) {p : ℕ} (hx : x ^ p = 1) (hp : Odd p) (ha : a * a = 1)
    (hax : a * x * a⁻¹ = x⁻¹) (T : Submodule (ZMod 2) V) (hxT : ∀ t ∈ T, x t ∈ T)
    (haT : ∀ t ∈ T, a t ∈ T) (hfp : fixSp V x T = ⊥) :
    Module.finrank (ZMod 2) T = 2 * Module.finrank (ZMod 2) (fixSp V a T) := by
  obtain ⟨hdisj, hsup⟩ := dihedral_split x a hx hp ha hax T hxT haT hfp
  have h1 : Module.Finite (ZMod 2) (fixSp V a T) := Module.Finite.of_finite
  have h2 : Module.Finite (ZMod 2) ((fixSp V a T).map (x : V →ₗ[ZMod 2] V)) :=
    Module.Finite.of_finite
  have := Submodule.finrank_sup_add_finrank_inf_eq (fixSp V a T)
    ((fixSp V a T).map (x : V →ₗ[ZMod 2] V))
  rw [hsup, hdisj.eq_bot, finrank_bot, add_zero, LinearEquiv.finrank_map_eq x] at this
  omega

end CFSG.Quasithin.SzN31
