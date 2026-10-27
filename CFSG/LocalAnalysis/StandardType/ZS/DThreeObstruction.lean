module

public import CFSG.LocalAnalysis.StandardType.ZS.DThreeConfig
public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import CFSG.LocalAnalysis.StandardType.ZS.ReflHyp
import CFSG.LocalAnalysis.StandardType.ZS.UnitaryObstruction

public section

namespace CFSG.StandardType.ZS

open Module

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}

local instance (priority := high) obstructionZModAddCommGroup : AddCommGroup (ZMod p) :=
  Ring.toAddCommGroup

private theorem list_prod_mul_self_of_involutions {M : Type*} [Group M] :
    ∀ (l : List M), (∀ x ∈ l, x * x = 1) → (∀ x ∈ l, ∀ y ∈ l, Commute x y) →
      l.prod * l.prod = 1
  | [], _, _ => by simp
  | a :: l, hsq, hcomm => by
      have ha : a * a = 1 := hsq a (by simp)
      have hl : l.prod * l.prod = 1 :=
        list_prod_mul_self_of_involutions l (fun x hx => hsq x (by simp [hx]))
          (fun x hx y hy => hcomm x (by simp [hx]) y (by simp [hy]))
      have hacomm : Commute a l.prod :=
        Commute.list_prod_right l a (fun x hx => hcomm a (by simp) x (by simp [hx]))
      calc
        (a :: l).prod * (a :: l).prod = (a * l.prod) * (a * l.prod) := rfl
        _ = a * (l.prod * a) * l.prod := by group
        _ = a * (a * l.prod) * l.prod := by rw [← hacomm.eq]
        _ = (a * a) * (l.prod * l.prod) := by group
        _ = 1 := by rw [ha, hl, one_mul]

private theorem commute_subtype_coe_iff {M : Type*} [Group M] {N : Subgroup M} {a b : N} :
    Commute (a : M) (b : M) ↔ Commute a b := by
  rw [commute_iff_eq, commute_iff_eq]
  constructor
  · intro h
    exact Subtype.ext (by simpa using h)
  · intro h
    simpa using congrArg (Subtype.val) h

omit [Module.Finite (ZMod p) U] in
private theorem prod_reflection_apply (hp : p ≠ 2) (k : ℕ) :
    ∀ (u : Fin k → U) (φ : Fin k → Dual (ZMod p) U) (hφ : ∀ i, φ i (u i) = 2),
      (∀ i j, i ≠ j →
        Commute (Module.reflection (hφ i)) (Module.reflection (hφ j))) →
      (∀ i j, i ≠ j →
        Module.reflection (hφ i) ≠ Module.reflection (hφ j)) →
      ∀ v : U,
        ((List.ofFn fun i => Module.reflection (hφ i)).prod : U ≃ₗ[ZMod p] U) v =
          v - ∑ i, φ i v • u i := by
  induction k with
  | zero =>
      intro u φ hφ hcomm hne v
      simp
  | succ k ih =>
      intro u φ hφ hcomm hne v
      have hcomm' : ∀ i j : Fin k, i ≠ j →
          Commute (Module.reflection (hφ i.succ)) (Module.reflection (hφ j.succ)) :=
        fun i j hij => hcomm i.succ j.succ (fun h => hij (Fin.succ_injective k h))
      have hne' : ∀ i j : Fin k, i ≠ j →
          Module.reflection (hφ i.succ) ≠ Module.reflection (hφ j.succ) :=
        fun i j hij h => hne i.succ j.succ (fun hh => hij (Fin.succ_injective k hh)) h
      have hcross : ∀ i j : Fin (k + 1), i ≠ j → φ i (u j) = 0 :=
        fun i j hij =>
          apply_eq_zero_of_commute hp (hφ i) (hφ j) (hcomm i j hij) (hne i j hij)
      have htail := ih (fun i : Fin k => u i.succ) (fun i : Fin k => φ i.succ)
        (fun i => hφ i.succ) hcomm' hne' v
      have hphi : φ 0 (((List.ofFn fun i : Fin k =>
          Module.reflection (hφ i.succ)).prod) v) = φ 0 v := by
        rw [htail, map_sub, map_sum,
          Finset.sum_eq_zero (fun i _ => by
            rw [LinearMap.map_smul, hcross 0 i.succ (Fin.succ_ne_zero i).symm,
              smul_eq_mul, mul_zero])]
        simp
      rw [List.ofFn_succ, List.prod_cons, LinearEquiv.mul_apply, Module.reflection_apply,
        hphi, htail, Fin.sum_univ_succ]
      module

private theorem pairing_eq_zero_or_one_of_isRefl (hp : p ≠ 2) {r t : ↥A}
    (hr : IsRefl p (r : U ≃ₗ[ZMod p] U)) (ht : IsRefl p (t : U ≃ₗ[ZMod p] U))
    {a b : U} {ψ φ : Dual (ZMod p) U} (hψ : ψ a = 2) (hφ : φ b = 2)
    (hrR : (r : U ≃ₗ[ZMod p] U) = Module.reflection hψ)
    (htR : (t : U ≃ₗ[ZMod p] U) = Module.reflection hφ)
    (hle : orderOf ((r : U ≃ₗ[ZMod p] U) * (t : U ≃ₗ[ZMod p] U)) ≤ 3)
    (hne : (r : U ≃ₗ[ZMod p] U) ≠ (t : U ≃ₗ[ZMod p] U)) :
    (ψ b * φ a = 0 ∧ Commute r t) ∨ (ψ b * φ a = 1 ∧ ¬ Commute r t) := by
  by_cases hc : Commute r t
  · left
    have hamb : Commute (r : U ≃ₗ[ZMod p] U) (t : U ≃ₗ[ZMod p] U) :=
      (commute_subtype_coe_iff).mpr hc
    have hzero : ψ b = 0 := by
      rw [hrR, htR] at hamb hne
      exact apply_eq_zero_of_commute hp hψ hφ hamb hne
    exact ⟨by rw [hzero, zero_mul], hc⟩
  · right
    have hnc : ¬ Commute (r : U ≃ₗ[ZMod p] U) (t : U ≃ₗ[ZMod p] U) :=
      fun h => hc ((commute_subtype_coe_iff).mp h)
    have hord : orderOf ((r : U ≃ₗ[ZMod p] U) * (t : U ≃ₗ[ZMod p] U)) = 3 :=
      orderOf_mul_eq_three_of_not_commute hr ht hnc hle
    have hord' : orderOf (Module.reflection hψ * Module.reflection hφ) = 3 := by
      simpa [hrR, htR] using hord
    exact ⟨mul_eq_one_of_orderOf_eq_three hp hψ hφ hord', hc⟩

private theorem commute_of_commute_mk_center (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {t z : ↥A}
    (ht : IsRefl p (t : U ≃ₗ[ZMod p] U))
    (h : Commute (QuotientGroup.mk (s := Subgroup.center ↥A) t)
      (QuotientGroup.mk (s := Subgroup.center ↥A) z)) :
    Commute t z := by
  let c : ↥A := t * z * t⁻¹ * z⁻¹
  have hc_mem : c ∈ Subgroup.center ↥A := by
    apply (QuotientGroup.eq_one_iff (N := Subgroup.center ↥A) c).mp
    dsimp only [c]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h.eq]
    group
  obtain ⟨lam, hlam⟩ := hirr.exists_eq_smul_of_mem_center hc_mem
  have hs : IsRefl p (((z⁻¹ * t * z : ↥A) : U ≃ₗ[ZMod p] U)) := by
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using ht.conj (z : U ≃ₗ[ZMod p] U)⁻¹
  obtain ⟨v, hv0, hsv, htv⟩ := IsRefl.exists_ne_zero_fixed hn hs ht
  have hcapply : ∀ x : U, (c : U ≃ₗ[ZMod p] U) x = (lam : ZMod p) • x := by
    intro x
    have := congrArg (fun f : U →ₗ[ZMod p] U => f x) hlam
    simpa using this
  have hcval : (c : U ≃ₗ[ZMod p] U) ((z : U ≃ₗ[ZMod p] U) ((t : U ≃ₗ[ZMod p] U) v)) =
      (t : U ≃ₗ[ZMod p] U) ((z : U ≃ₗ[ZMod p] U) v) := by
    dsimp only [c]
    simp [Subgroup.coe_mul, LinearEquiv.mul_apply]
  have hzrel : (t : U ≃ₗ[ZMod p] U) ((z : U ≃ₗ[ZMod p] U) v) =
      (lam : ZMod p) • ((z : U ≃ₗ[ZMod p] U) ((t : U ≃ₗ[ZMod p] U) v)) := by
    rw [← hcval, hcapply]
  have hsl : (((z⁻¹ * t * z : ↥A) : U ≃ₗ[ZMod p] U)) v =
      (lam : ZMod p) • ((t : U ≃ₗ[ZMod p] U) v) := by
    have hcomp : (((z⁻¹ * t * z : ↥A) : U ≃ₗ[ZMod p] U)) v =
        (z : U ≃ₗ[ZMod p] U)⁻¹ ((t : U ≃ₗ[ZMod p] U) ((z : U ≃ₗ[ZMod p] U) v)) := by
      simp [Subgroup.coe_mul, LinearEquiv.mul_apply]
    rw [hcomp, hzrel]
    simp
  have hlamv : (lam : ZMod p) • v = v := by
    calc
      (lam : ZMod p) • v = (lam : ZMod p) • ((t : U ≃ₗ[ZMod p] U) v) := by rw [htv]
      _ = (((z⁻¹ * t * z : ↥A) : U ≃ₗ[ZMod p] U)) v := hsl.symm
      _ = v := hsv
  have hlam1 : lam = 1 := by
    have hzero : (lam - 1) • v = 0 := by rw [sub_smul, one_smul, hlamv, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero_iff_left hv0).mp hzero)
  have hc1 : c = 1 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    have := congrArg (fun f : U →ₗ[ZMod p] U => f x) hlam
    rw [hlam1] at this
    simpa using this
  have htz : t * z = z * t := by
    have hc1' : t * z * t⁻¹ * z⁻¹ = 1 := by simpa [c] using hc1
    calc
      t * z = (t * z * t⁻¹ * z⁻¹) * (z * t) := by group
      _ = 1 * (z * t) := by rw [hc1']
      _ = z * t := one_mul _
  exact (commute_iff_eq t z).mpr htz

omit [Module.Finite (ZMod p) U] in
private theorem frame_pairing_eq_zero (hp : p ≠ 2) {k : ℕ} {a : Fin k → U}
    {ψ : Fin k → Dual (ZMod p) U} {b : U} (hψ : ∀ i, ψ i (a i) = 2)
    (hcomm : ∀ i j, i ≠ j →
      Commute (Module.reflection (hψ i)) (Module.reflection (hψ j)))
    (hne : ∀ i j, i ≠ j →
      Module.reflection (hψ i) ≠ Module.reflection (hψ j))
    (hsum : ∑ i, ψ i b • a i = 0) : ∀ i, ψ i b = 0 := by
  have hLI : LinearIndependent (ZMod p) a :=
    linearIndependent_of_pairwise_commute hp hψ hcomm hne
  rw [linearIndependent_iff'] at hLI
  exact fun i => hLI Finset.univ (fun j => ψ j b) hsum i (Finset.mem_univ i)

omit [Module.Finite (ZMod p) U] in
private theorem scalar_mul_self_eq_one (hp : p ≠ 2) {s t : U ≃ₗ[ZMod p] U} {u : U}
    {φ : Dual (ZMod p) U} (hφ : φ u = 2) (ht : t = Module.reflection hφ)
    (hcomm : Commute s t) (hsq : s (s u) = u) :
    ∃ c : ZMod p, s u = c • u ∧ c * c = 1 := by
  have htu : t u = -u := by rw [ht, Module.reflection_apply_self]
  have htsu : t (s u) = -(s u) := by
    calc
      t (s u) = (t * s) u := rfl
      _ = (s * t) u := by rw [hcomm.eq]
      _ = s (t u) := rfl
      _ = s (-u) := by rw [htu]
      _ = -(s u) := map_neg s u
  have h2 : (2 : ZMod p) • s u = φ (s u) • u := by
    have h : s u - φ (s u) • u = -(s u) := by
      simpa only [ht, Module.reflection_apply] using htsu
    have h' : s u + s u = φ (s u) • u := by
      calc
        s u + s u = (s u - φ (s u) • u) + (φ (s u) • u + s u) := by abel
        _ = (-(s u)) + (φ (s u) • u + s u) := by rw [h]
        _ = φ (s u) • u := by abel
    rw [two_smul]
    exact h'
  let c : ZMod p := (2 : ZMod p)⁻¹ * φ (s u)
  have hsu : s u = c • u := by
    calc
      s u = ((2 : ZMod p)⁻¹ * 2) • s u := by
        have h2inv : (2 : ZMod p)⁻¹ * 2 = 1 :=
          inv_mul_cancel₀ (ZMod.prime_ne_zero p 2 hp)
        rw [h2inv, one_smul]
      _ = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • s u) := by rw [smul_smul]
      _ = (2 : ZMod p)⁻¹ • (φ (s u) • u) := by rw [h2]
      _ = c • u := by rw [smul_smul]
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hφ
    exact (ZMod.prime_ne_zero p 2 hp) hφ.symm
  have hcc : c * c = 1 := by
    have hinj : Function.Injective (fun a : ZMod p => a • u) := by
      intro a b hab
      have h : (a - b) • u = 0 := by
        rw [sub_smul]
        exact sub_eq_zero.mpr hab
      exact sub_eq_zero.mp ((smul_eq_zero_iff_left hu0).mp h)
    apply hinj
    calc
      (c * c) • u = c • (c • u) := by rw [smul_smul]
      _ = c • (s u) := by rw [hsu]
      _ = s (c • u) := by rw [← map_smul]
      _ = s (s u) := by rw [hsu]
      _ = u := hsq
      _ = (1 : ZMod p) • u := by rw [one_smul]
  exact ⟨c, hsu, hcc⟩

omit [Module.Finite (ZMod p) U] in
private theorem natCard_eq_of_pairing {k : ℕ} {u : Fin k → U}
    {φ : Fin k → Dual (ZMod p) U} {u₀ : U} {φ₀ : Dual (ZMod p) U}
    {d : Fin k → ↥A ⧸ Subgroup.center ↥A} {e : ↥A ⧸ Subgroup.center ↥A}
    (hterm : ∀ i, φ i u₀ * φ₀ (u i) = 0 ∨ φ i u₀ * φ₀ (u i) = 1)
    (hiff : ∀ i, φ i u₀ * φ₀ (u i) = 1 ↔ ¬ Commute e (d i))
    (hsum : ∑ i, φ i u₀ * φ₀ (u i) = 4) :
    ((Nat.card {i // ¬ Commute e (d i)} : ℕ) : ZMod p) = 4 := by
  have hcard : (Nat.card {i // ¬ Commute e (d i)} : ZMod p) =
      ∑ i, φ i u₀ * φ₀ (u i) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff).symm, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rcases hterm i with h | h <;> simp [h]
  rw [hcard, hsum]

omit [Module.Finite (ZMod p) U] in
private theorem affineTriangle_lift_orders (hp : p ≠ 2)
    {ua ub uc : U} {φa φb φc : Dual (ZMod p) U}
    (hφa : φa ua = 2) (hφb : φb ub = 2) (hφc : φc uc = 2)
    (hab : orderOf (Module.reflection hφa * Module.reflection hφb) = 3)
    (hac : orderOf (Module.reflection hφa * Module.reflection hφc) = 3)
    (hbc : orderOf (Module.reflection hφb * Module.reflection hφc) = 3) :
    φb ua = (φa ub)⁻¹ ∧ φc ub = (φb uc)⁻¹ ∧ φa uc = (φc ua)⁻¹ ∧
      φa ub ≠ 0 ∧ φb uc ≠ 0 ∧ φc ua ≠ 0 := by
  have hx : φa ub * φb ua = 1 := mul_eq_one_of_orderOf_eq_three hp hφa hφb hab
  have hy : φb uc * φc ub = 1 := mul_eq_one_of_orderOf_eq_three hp hφb hφc hbc
  have hw : φa uc * φc ua = 1 := mul_eq_one_of_orderOf_eq_three hp hφa hφc hac
  have hx0 : φa ub ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hx
    exact zero_ne_one hx
  have hy0 : φb uc ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hy
    exact zero_ne_one hy
  have hw0 : φc ua ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hw
    exact zero_ne_one hw
  exact ⟨eq_inv_of_mul_eq_one_right hx, eq_inv_of_mul_eq_one_right hy,
    eq_inv_of_mul_eq_one_left hw, hx0, hy0, hw0⟩

omit [Module.Finite (ZMod p) U] in
private theorem pairing_conj_reflection (hp : p ≠ 2)
    {ua ub uc : U} {φa φb φc : Dual (ZMod p) U}
    (hφa : φa ua = 2) (hφb : φb ub = 2) (hφc : φc uc = 2) (hφauc : φa uc = (φc ua)⁻¹)
    (hcab : orderOf (Module.reflection hφc * Module.reflection hφa *
      Module.reflection hφc * Module.reflection hφb) = 3) :
    (φa - (φc ua)⁻¹ • φc) ub * φb (ua - φc ua • uc) = 1 := by
  let w : ZMod p := φc ua
  let uac : U := ua - w • uc
  let φac : Dual (ZMod p) U := φa - w⁻¹ • φc
  have hφac : φac uac = 2 := by
    have hcu : φc ua = w := rfl
    calc
      φac uac = φa ua - w * φa uc - w⁻¹ * (φc ua - w * φc uc) := by
        simp [φac, uac, map_sub, map_smul, smul_eq_mul]
        ring
      _ = 2 - w * w⁻¹ - w⁻¹ * (w - w * 2) := by rw [hφa, hφc, hφauc, hcu]
      _ = 2 := by ring
  have hCv : ∀ v : U, (Module.reflection hφc) v = v - φc v • uc :=
    fun v => by rw [Module.reflection_apply v hφc]
  have hcomp : (φa ∘ₗ ((Module.reflection hφc).symm : U →ₗ[ZMod p] U)) = φac := by
    ext v
    rw [LinearMap.comp_apply, Module.reflection_symm]
    change φa ((Module.reflection hφc) v) = φac v
    rw [hCv]
    simp only [map_sub, map_smul, smul_eq_mul, φac, LinearMap.sub_apply,
      LinearMap.smul_apply, hφauc, w]
    ring_nf
  have hCua : (Module.reflection hφc) ua = uac := hCv ua
  have h' : (φa ∘ₗ ((Module.reflection hφc).symm : U →ₗ[ZMod p] U))
      (Module.reflection hφc ua) = 2 := by
    rw [LinearMap.comp_apply]
    change φa ((Module.reflection hφc).symm ((Module.reflection hφc) ua)) = 2
    rw [LinearEquiv.symm_apply_apply, hφa]
  have hconj := conj_reflection (g := Module.reflection hφc) hφa h'
  have hconj' : Module.reflection hφc * Module.reflection hφa * Module.reflection hφc =
      Module.reflection h' := by
    simpa [Module.reflection_inv hφc] using hconj
  have hconj_eq : Module.reflection h' = Module.reflection hφac := by
    apply LinearEquiv.ext
    intro v
    have h1 : (Module.reflection h') v =
        v - ((φa ∘ₗ (Module.reflection hφc).symm) v) • ((Module.reflection hφc) ua) :=
      Module.reflection_apply v h'
    have h2 : (Module.reflection hφac) v = v - φac v • uac := Module.reflection_apply v hφac
    rw [h1, h2, hcomp, hCua]
  have hcab' : orderOf (Module.reflection h' * Module.reflection hφb) = 3 := by
    rw [← hconj']
    exact hcab
  have hcab'' : orderOf (Module.reflection hφac * Module.reflection hφb) = 3 := by
    rwa [hconj_eq] at hcab'
  have hpq : φac ub * φb uac = 1 :=
    mul_eq_one_of_orderOf_eq_three hp hφac hφb hcab''
  simpa [uac, φac, w] using hpq

omit [Module.Finite (ZMod p) U] in
private theorem affineTriangle_lift_pairing (hp : p ≠ 2)
    {ua ub uc : U} {φa φb φc : Dual (ZMod p) U}
    (hφa : φa ua = 2) (hφb : φb ub = 2) (hφc : φc uc = 2)
    (hab : orderOf (Module.reflection hφa * Module.reflection hφb) = 3)
    (hac : orderOf (Module.reflection hφa * Module.reflection hφc) = 3)
    (hbc : orderOf (Module.reflection hφb * Module.reflection hφc) = 3)
    (hcab : orderOf (Module.reflection hφc * Module.reflection hφa *
      Module.reflection hφc * Module.reflection hφb) = 3) :
    (φa ub - (φc ua)⁻¹ * (φb uc)⁻¹) * ((φa ub)⁻¹ - (φc ua) * φb uc) = 1 := by
  obtain ⟨hφbua, hφcub, hφauc, -, -, -⟩ :=
    affineTriangle_lift_orders hp hφa hφb hφc hab hac hbc
  have hpq := pairing_conj_reflection hp hφa hφb hφc hφauc hcab
  have hpu : (φa - (φc ua)⁻¹ • φc) ub = φa ub - (φc ua)⁻¹ * (φb uc)⁻¹ := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, hφcub, smul_eq_mul]
  have hbu : φb (ua - φc ua • uc) = (φa ub)⁻¹ - φc ua * φb uc := by
    simp only [map_sub, map_smul, smul_eq_mul, hφbua]
  rw [← hpu, ← hbu]
  exact hpq

private theorem affineTriangle_quadratic {x y w : ZMod p}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hw0 : w ≠ 0)
    (hpair : (x - w⁻¹ * y⁻¹) * (x⁻¹ - w * y) = 1) :
    (x * y * w) ^ 2 - (x * y * w) + 1 = 0 := by
  let t : ZMod p := x * y * w
  have hexp : (x - w⁻¹ * y⁻¹) * (x⁻¹ - w * y) = 2 - (t + t⁻¹) := by
    field_simp [t, hx0, hy0, hw0]
    ring
  have ht : t + t⁻¹ = 1 := by
    rw [hexp] at hpair
    linear_combination -hpair
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, inv_zero, add_zero] at ht
    exact zero_ne_one ht
  have hmul : t * t + 1 = t := by
    calc
      t * t + 1 = t * t + t * t⁻¹ := by rw [mul_inv_cancel₀ ht0]
      _ = (t + t⁻¹) * t := by ring
      _ = 1 * t := by rw [ht]
      _ = t := one_mul t
  have ht2 : t ^ 2 - t + 1 = 0 := by
    rw [pow_two]
    linear_combination hmul
  simpa [t] using ht2

omit [Module.Finite (ZMod p) U] in
private theorem zom_affineTriangle_pairing_data
    (hp : p ≠ 2) {ua ub uc : U} {φa φb φc : Dual (ZMod p) U}
    (hφa : φa ua = 2) (hφb : φb ub = 2) (hφc : φc uc = 2)
    (hab : orderOf (Module.reflection hφa * Module.reflection hφb) = 3)
    (hac : orderOf (Module.reflection hφa * Module.reflection hφc) = 3)
    (hbc : orderOf (Module.reflection hφb * Module.reflection hφc) = 3)
    (hcab : orderOf ((Module.reflection hφc * Module.reflection hφa *
      Module.reflection hφc) * Module.reflection hφb) = 3) :
    φb ua = (φa ub)⁻¹ ∧ φc ub = (φb uc)⁻¹ ∧ φa uc = (φc ua)⁻¹ ∧
      φa ub ≠ 0 ∧ φb uc ≠ 0 ∧ φc ua ≠ 0 ∧
      (φa ub * φb uc * φc ua) ^ 2 - (φa ub * φb uc * φc ua) + 1 = 0 := by
  have hpair := affineTriangle_lift_pairing hp hφa hφb hφc hab hac hbc hcab
  obtain ⟨hia, hib, hic, hx0, hy0, hw0⟩ :=
    affineTriangle_lift_orders hp hφa hφb hφc hab hac hbc
  exact ⟨hia, hib, hic, hx0, hy0, hw0, affineTriangle_quadratic hx0 hy0 hw0 hpair⟩

private theorem orderOf_mul_of_orderOf_mk_mul (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {r s : ↥A}
    (hr : IsRefl p (r : U ≃ₗ[ZMod p] U)) (hs : IsRefl p (s : U ≃ₗ[ZMod p] U))
    {x y : ↥A ⧸ Subgroup.center ↥A}
    (hrx : QuotientGroup.mk (s := Subgroup.center ↥A) r = x)
    (hsy : QuotientGroup.mk (s := Subgroup.center ↥A) s = y) {n : ℕ}
    (h : orderOf (x * y) = n) : orderOf ((r : U ≃ₗ[ZMod p] U) * (s : U ≃ₗ[ZMod p] U)) = n := by
  have hsub : orderOf (r * s) = n := by
    rw [← hirr.orderOf_mk_mul_mk hn hr hs, hrx, hsy]
    exact h
  rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
  exact hsub

omit [Module.Finite (ZMod p) U] in
private theorem ofFn_prod_mul_self {k : ℕ} {r : Fin k → ↥A}
    (hsq : ∀ i, r i * r i = 1) (hcomm : ∀ i j, i ≠ j → Commute (r i) (r j)) :
    (List.ofFn r).prod * (List.ofFn r).prod = 1 := by
  apply list_prod_mul_self_of_involutions
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hsq i
  · intro x hx y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    by_cases hij : i = j
    · rw [hij]
      exact Commute.refl _
    · exact hcomm i j hij

omit [Module.Finite (ZMod p) U] in
private theorem mk_ofFn_prod {k : ℕ} {r : Fin k → ↥A}
    {d : Fin k → ↥A ⧸ Subgroup.center ↥A}
    (hr : ∀ i, QuotientGroup.mk (s := Subgroup.center ↥A) (r i) = d i) :
    QuotientGroup.mk (s := Subgroup.center ↥A) (List.ofFn r).prod = (List.ofFn d).prod := by
  change (QuotientGroup.mk' (Subgroup.center ↥A)) ((List.ofFn r).prod) = (List.ofFn d).prod
  rw [← List.prod_hom (List.ofFn r) (QuotientGroup.mk' (Subgroup.center ↥A)),
    ← List.ofFn_comp' r (QuotientGroup.mk' (Subgroup.center ↥A))]
  have hfun : (fun i => (QuotientGroup.mk' (Subgroup.center ↥A)) (r i)) = d := by
    funext i
    exact hr i
  rw [hfun]

private theorem frame_lift_pairing (hp : p ≠ 2) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {k : ℕ} {r : Fin k → ↥A} {t : ↥A}
    (hr : ∀ i, IsRefl p (r i : U ≃ₗ[ZMod p] U))
    (ht : IsRefl p (t : U ≃ₗ[ZMod p] U)) {u : Fin k → U}
    {φ : Fin k → Dual (ZMod p) U} {u₀ : U} {φ₀ : Dual (ZMod p) U}
    (hφ : ∀ i, φ i (u i) = 2) (hφ₀ : φ₀ u₀ = 2)
    (hrR : ∀ i, (r i : U ≃ₗ[ZMod p] U) = Module.reflection (hφ i))
    (htR : (t : U ≃ₗ[ZMod p] U) = Module.reflection hφ₀)
    (hle : ∀ i, orderOf ((r i : U ≃ₗ[ZMod p] U) * (t : U ≃ₗ[ZMod p] U)) ≤ 3)
    (hne : ∀ i, (r i : U ≃ₗ[ZMod p] U) ≠ (t : U ≃ₗ[ZMod p] U))
    {d : Fin k → ↥A ⧸ Subgroup.center ↥A} {e : ↥A ⧸ Subgroup.center ↥A}
    (htk : QuotientGroup.mk (s := Subgroup.center ↥A) t = e)
    (hrk : ∀ i, QuotientGroup.mk (s := Subgroup.center ↥A) (r i) = d i) :
    (∀ i, (φ i u₀ * φ₀ (u i) = 0 ∧ Commute (r i) t) ∨
      (φ i u₀ * φ₀ (u i) = 1 ∧ ¬ Commute (r i) t)) ∧
    (∀ i, Commute (r i) t ↔ Commute e (d i)) := by
  refine ⟨fun i => pairing_eq_zero_or_one_of_isRefl hp (hr i) ht (hφ i) hφ₀ (hrR i) htR
    (hle i) (hne i), ?_⟩
  intro i
  have h := (hirr.commute_mk_iff hn (ht := hr i) (s := t))
  rw [htk, hrk i] at h
  exact ⟨fun hri => h.mpr hri.symm, fun hed => (h.mp hed).symm⟩

omit [Module.Finite (ZMod p) U] in
private theorem frame_case_one (hp : p ≠ 2) {k : ℕ} {r : Fin k → ↥A} {t : ↥A}
    {u : Fin k → U} {φ : Fin k → Dual (ZMod p) U} {u₀ : U}
    {φ₀ : Dual (ZMod p) U} {d : Fin k → ↥A ⧸ Subgroup.center ↥A}
    {e : ↥A ⧸ Subgroup.center ↥A} (hφ : ∀ i, φ i (u i) = 2)
    (hcommR : ∀ i j, i ≠ j →
      Commute (Module.reflection (hφ i)) (Module.reflection (hφ j)))
    (hneR : ∀ i j, i ≠ j →
      Module.reflection (hφ i) ≠ Module.reflection (hφ j))
    (hzact : ∀ v : U, (((List.ofFn r).prod : ↥A) : U ≃ₗ[ZMod p] U) v =
      v - ∑ i, φ i v • u i)
    (hzu : (((List.ofFn r).prod : ↥A) : U ≃ₗ[ZMod p] U) u₀ = u₀)
    (hpair_i : ∀ i, (φ i u₀ * φ₀ (u i) = 0 ∧ Commute (r i) t) ∨
      (φ i u₀ * φ₀ (u i) = 1 ∧ ¬ Commute (r i) t))
    (hcomm_pair : ∀ i, Commute (r i) t ↔ Commute e (d i))
    (hne : ∃ i, ¬ Commute e (d i)) : False := by
  have hsum0 : ∑ i, φ i u₀ • u i = 0 := by
    have h := hzact u₀
    rw [hzu] at h
    have h' : u₀ - (u₀ - ∑ i, φ i u₀ • u i) = 0 := by rw [← h, sub_self]
    simpa using h'
  have hzero := frame_pairing_eq_zero (b := u₀) hp hφ hcommR hneR hsum0
  have hall : ∀ i, Commute e (d i) := by
    intro i
    rcases hpair_i i with ⟨-, hci⟩ | ⟨h1, -⟩
    · exact (hcomm_pair i).mp hci
    · exfalso
      rw [hzero i, zero_mul] at h1
      exact zero_ne_one h1
  obtain ⟨i, hi⟩ := hne
  exact absurd (hall i) hi

omit [Module.Finite (ZMod p) U] in
private theorem frame_case_neg_one
    {k : ℕ} {r : Fin k → ↥A} {t : ↥A} {u : Fin k → U}
    {φ : Fin k → Dual (ZMod p) U} {u₀ : U} {φ₀ : Dual (ZMod p) U}
    {d : Fin k → ↥A ⧸ Subgroup.center ↥A} {e : ↥A ⧸ Subgroup.center ↥A}
    (hφ₀ : φ₀ u₀ = 2)
    (hzact : ∀ v : U, (((List.ofFn r).prod : ↥A) : U ≃ₗ[ZMod p] U) v =
      v - ∑ i, φ i v • u i)
    (hzu : (((List.ofFn r).prod : ↥A) : U ≃ₗ[ZMod p] U) u₀ = -u₀)
    (hpair_i : ∀ i, (φ i u₀ * φ₀ (u i) = 0 ∧ Commute (r i) t) ∨
      (φ i u₀ * φ₀ (u i) = 1 ∧ ¬ Commute (r i) t))
    (hcomm_pair : ∀ i, Commute (r i) t ↔ Commute e (d i)) :
    ((Nat.card {i // ¬ Commute e (d i)} : ℕ) : ZMod p) = 4 := by
  have hsum2 : ∑ i, φ i u₀ • u i = (2 : ZMod p) • u₀ := by
    have h := hzact u₀
    rw [hzu] at h
    calc
      ∑ i, φ i u₀ • u i = u₀ - (u₀ - ∑ i, φ i u₀ • u i) := by abel
      _ = u₀ - (-u₀) := by rw [← h]
      _ = (2 : ZMod p) • u₀ := by module
  have hsum4 : ∑ i, φ i u₀ * φ₀ (u i) = 4 := by
    calc
      ∑ i, φ i u₀ * φ₀ (u i) = φ₀ (∑ i, φ i u₀ • u i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul, smul_eq_mul]
      _ = φ₀ ((2 : ZMod p) • u₀) := congrArg φ₀ hsum2
      _ = (2 : ZMod p) • φ₀ u₀ := LinearMap.map_smul φ₀ (2 : ZMod p) u₀
      _ = (2 : ZMod p) * φ₀ u₀ := smul_eq_mul 2 (φ₀ u₀)
      _ = 4 := by rw [hφ₀]; norm_num
  have hterm : ∀ i, φ i u₀ * φ₀ (u i) = 0 ∨ φ i u₀ * φ₀ (u i) = 1 := by
    intro i
    rcases hpair_i i with ⟨h0, -⟩ | ⟨h1, -⟩
    · exact Or.inl h0
    · exact Or.inr h1
  have hiff : ∀ i, φ i u₀ * φ₀ (u i) = 1 ↔ ¬ Commute e (d i) := by
    intro i
    constructor
    · intro h1 hci
      rcases hpair_i i with ⟨h0, -⟩ | ⟨-, hnc⟩
      · rw [h0] at h1
        exact zero_ne_one h1
      · exact hnc ((hcomm_pair i).mpr hci)
    · intro hnc
      rcases hpair_i i with ⟨-, hci⟩ | ⟨h1, -⟩
      · exact absurd ((hcomm_pair i).mp hci) hnc
      · exact h1
  exact natCard_eq_of_pairing hterm hiff hsum4

omit [Module.Finite (ZMod p) U] in
private theorem coe_ofFn_prod_eq {k : ℕ} {r : Fin k → ↥A} {u : Fin k → U}
    {φ : Fin k → Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hrR : ∀ i, (r i : U ≃ₗ[ZMod p] U) = Module.reflection (hφ i)) :
    ((List.ofFn r).prod : U ≃ₗ[ZMod p] U) =
      (List.ofFn fun i => Module.reflection (hφ i)).prod := by
  change (Subgroup.subtype A) ((List.ofFn r).prod) = _
  rw [← List.prod_hom (List.ofFn r) (Subgroup.subtype A),
    ← List.ofFn_comp' r (Subgroup.subtype A)]
  have hfun : (fun i => (Subgroup.subtype A) (r i)) =
      fun i => Module.reflection (hφ i) := funext hrR
  rw [hfun]

private theorem frame_commute_data (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {k : ℕ} {r : Fin k → ↥A}
    {u : Fin k → U} {φ : Fin k → Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hr : ∀ i, IsRefl p (r i : U ≃ₗ[ZMod p] U))
    (hrR : ∀ i, (r i : U ≃ₗ[ZMod p] U) = Module.reflection (hφ i))
    {d : Fin k → ↥A ⧸ Subgroup.center ↥A}
    (hrk : ∀ i, QuotientGroup.mk (s := Subgroup.center ↥A) (r i) = d i)
    (hinj : Function.Injective d) (hpair : Pairwise fun i j => Commute (d i) (d j)) :
    (∀ i j, i ≠ j → Commute (r i) (r j)) ∧
    (∀ i j, i ≠ j →
      Commute (Module.reflection (hφ i)) (Module.reflection (hφ j))) ∧
    (∀ i j, i ≠ j → Module.reflection (hφ i) ≠ Module.reflection (hφ j)) := by
  have hcommA : ∀ i j, i ≠ j → Commute (r i) (r j) := by
    intro i j hij
    exact (hirr.commute_mk_iff hn (ht := hr j) (s := r i)).mp (by
      rw [hrk i, hrk j]
      exact hpair hij)
  have hcommR : ∀ i j, i ≠ j →
      Commute (Module.reflection (hφ i)) (Module.reflection (hφ j)) := by
    intro i j hij
    have h := (commute_subtype_coe_iff (N := A) (a := r i) (b := r j)).mpr (hcommA i j hij)
    rwa [hrR i, hrR j] at h
  have hneR : ∀ i j, i ≠ j →
      Module.reflection (hφ i) ≠ Module.reflection (hφ j) := by
    intro i j hij heq
    have hrij : r i = r j := by
      apply Subtype.ext
      rw [hrR i, hrR j]
      exact heq
    have hde : d i = d j := by rw [← hrk i, ← hrk j, hrij]
    exact hij (hinj hde)
  exact ⟨hcommA, hcommR, hneR⟩

theorem natCard_not_commute_eq_four_of_scalarFrame (hp : p ≠ 2) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {k : ℕ} {d : Fin k → ↥A ⧸ Subgroup.center ↥A} {e : ↥A ⧸ Subgroup.center ↥A}
    (h : ScalarFrame (reflImage p A) d e) (hne : ∃ i, ¬ Commute e (d i)) :
    ((Nat.card {i // ¬ Commute e (d i)} : ℕ) : ZMod p) = 4 := by
  obtain ⟨hdE, hinj, hpair, heE, hne', hprod⟩ := h
  choose r hr hrk using fun i => exists_unique_refl_of_mem_reflImage hirr hn (hdE i)
  obtain ⟨t, ⟨ht, htk⟩, -⟩ := exists_unique_refl_of_mem_reflImage hirr hn heE
  choose u φ hφ hrR using fun i => (isRefl_iff hp (r i : U ≃ₗ[ZMod p] U)).mp (hr i).1
  obtain ⟨u₀, φ₀, hφ₀, htR⟩ := (isRefl_iff hp (t : U ≃ₗ[ZMod p] U)).mp ht
  obtain ⟨hcommA, hcommR, hneR⟩ := frame_commute_data hirr hn hφ
    (fun i => (hr i).1) hrR (fun i => (hr i).2) hinj hpair
  let z : ↥A := (List.ofFn r).prod
  have hzR : (z : U ≃ₗ[ZMod p] U) =
      (List.ofFn fun i => Module.reflection (hφ i)).prod := by
    dsimp only [z]
    exact coe_ofFn_prod_eq hφ hrR
  have hzact : ∀ v : U, (z : U ≃ₗ[ZMod p] U) v = v - ∑ i, φ i v • u i := by
    intro v
    rw [hzR]
    exact prod_reflection_apply hp k u φ hφ hcommR hneR v
  have hzsq : z * z = 1 := by
    dsimp only [z]
    exact ofFn_prod_mul_self (fun i => by
      apply Subtype.ext
      simpa using (hr i).1.1) (fun i j hij => hcommA i j hij)
  have hzsq_amb : (z : U ≃ₗ[ZMod p] U) ((z : U ≃ₗ[ZMod p] U) u₀) = u₀ := by
    have h := congrArg (fun x : ↥A => (x : U ≃ₗ[ZMod p] U) u₀) hzsq
    simpa [Subgroup.coe_mul, LinearEquiv.mul_apply] using h
  have hmkz : QuotientGroup.mk (s := Subgroup.center ↥A) z = (List.ofFn d).prod := by
    dsimp only [z]
    exact mk_ofFn_prod (fun i => (hr i).2)
  have hcommquot : Commute (QuotientGroup.mk (s := Subgroup.center ↥A) t)
      (QuotientGroup.mk (s := Subgroup.center ↥A) z) := by
    rw [htk, hmkz]
    exact hprod
  have htz : Commute t z := commute_of_commute_mk_center hirr hn ht hcommquot
  have hzt_amb : Commute (z : U ≃ₗ[ZMod p] U) (t : U ≃ₗ[ZMod p] U) :=
    ((commute_subtype_coe_iff (N := A) (a := t) (b := z)).mpr htz).symm
  obtain ⟨c, hc, hc2⟩ := scalar_mul_self_eq_one hp hφ₀ htR hzt_amb hzsq_amb
  have hle : ∀ i, orderOf ((r i : U ≃ₗ[ZMod p] U) * (t : U ≃ₗ[ZMod p] U)) ≤ 3 :=
    fun i => h3 (r i) (r i).2 t t.2 (hr i).1 ht
  have hne_t : ∀ i, (r i : U ≃ₗ[ZMod p] U) ≠ (t : U ≃ₗ[ZMod p] U) := by
    intro i hri
    have hsub : r i = t := Subtype.ext hri
    have hde : d i = e := by rw [← (hr i).2, ← htk, hsub]
    exact hne' i hde.symm
  obtain ⟨hpair_i, hcomm_pair⟩ :=
    frame_lift_pairing (d := d) (e := e) hp hirr hn (fun i => (hr i).1) ht hφ hφ₀ hrR htR
      hle hne_t htk (fun i => (hr i).2)
  rcases mul_self_eq_one_iff.mp hc2 with hc1 | hcneg
  · rw [hc1] at hc
    exfalso
    exact frame_case_one hp hφ hcommR hneR hzact (by simpa [z] using hc)
      hpair_i hcomm_pair hne
  · rw [hcneg] at hc
    exact frame_case_neg_one hφ₀ hzact (by simpa [z] using hc) hpair_i hcomm_pair

theorem false_of_scalarFrame_eight (hp : p ≠ 2) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {d : Fin 8 → ↥A ⧸ Subgroup.center ↥A} {e : ↥A ⧸ Subgroup.center ↥A}
    (h : ScalarFrame (reflImage p A) d e) (hall : ∀ i, ¬ Commute e (d i)) : False := by
  have hcard : Nat.card {i : Fin 8 // ¬ Commute e (d i)} = 8 := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_fin]
  have h8 : ((8 : ℕ) : ZMod p) = 4 := by
    have h := natCard_not_commute_eq_four_of_scalarFrame hp hirr hn h3 h ⟨0, hall 0⟩
    rwa [hcard] at h
  have h4 : ((4 : ℕ) : ZMod p) = 0 := by
    have h : ((8 : ℕ) : ZMod p) - ((4 : ℕ) : ZMod p) = 0 := sub_eq_zero.mpr h8
    norm_num at h
    exact h
  have hdvd : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp h4
  have hdvd2 : p ∣ 2 ^ 2 := by simpa using hdvd
  have hdvd' : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow (Fact.out) hdvd2
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp hdvd'
  exact hp hp2

theorem eq_three_of_scalarFrame_seven (hp : p ≠ 2) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {d : Fin 7 → ↥A ⧸ Subgroup.center ↥A} {e : ↥A ⧸ Subgroup.center ↥A}
    (h : ScalarFrame (reflImage p A) d e) (hall : ∀ i, ¬ Commute e (d i)) : p = 3 := by
  have hcard : Nat.card {i : Fin 7 // ¬ Commute e (d i)} = 7 := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_fin]
  have h7 : ((7 : ℕ) : ZMod p) = 4 := by
    have h := natCard_not_commute_eq_four_of_scalarFrame hp hirr hn h3 h ⟨0, hall 0⟩
    rwa [hcard] at h
  have h3zero : ((3 : ℕ) : ZMod p) = 0 := by
    have h : ((7 : ℕ) : ZMod p) - ((4 : ℕ) : ZMod p) = 0 := sub_eq_zero.mpr h7
    norm_num at h
    exact h
  have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3zero
  exact (Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp hdvd

omit [Module.Finite (ZMod p) U] in
private theorem zng_prod_scalar_eq_neg (hp : p ≠ 2) (hirr : AbsIrred p A)
    {k : ℕ} (hk : 0 < k) {z : ↥A} {u : Fin k → U} {φ : Fin k → Dual (ZMod p) U}
    (hφ : ∀ i, φ i (u i) = 2) (hcross : ∀ i j, i ≠ j → φ i (u j) = 0)
    (hzcenter : z ∈ Subgroup.center ↥A)
    (hzact : ∀ v : U, (z : U ≃ₗ[ZMod p] U) v = v - ∑ i, φ i v • u i) :
    (z : U ≃ₗ[ZMod p] U) = LinearEquiv.neg (ZMod p) := by
  obtain ⟨c, hc⟩ := hirr.exists_eq_smul_of_mem_center hzcenter
  let i₀ : Fin k := ⟨0, hk⟩
  have hu₀ : u i₀ ≠ 0 := by
    intro h0
    have h2 : (2 : ZMod p) = 0 := by
      have := hφ i₀
      rw [h0, map_zero] at this
      exact this.symm
    exact (ZMod.prime_ne_zero p 2 hp) h2
  have hsum₀ : ∑ i, φ i (u i₀) • u i = (2 : ZMod p) • u i₀ := by
    rw [Finset.sum_eq_single i₀]
    · rw [hφ]
    · intro j _ hj
      rw [hcross j i₀ hj, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  have hzu₀ : (z : U ≃ₗ[ZMod p] U) (u i₀) = -u i₀ := by
    rw [hzact, hsum₀]
    module
  have hcapply : ∀ v : U, (z : U ≃ₗ[ZMod p] U) v = c • v := by
    intro v
    have := congrArg (fun f : U →ₗ[ZMod p] U => f v) hc
    simpa using this
  have hcneg : c = -1 := by
    have h : c • u i₀ = (-1 : ZMod p) • u i₀ := by
      rw [← hcapply, hzu₀]
      simp
    have h' : (c - (-1)) • u i₀ = 0 := by
      rw [sub_smul, h, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero_iff_left hu₀).mp h')
  apply LinearEquiv.ext
  intro v
  rw [hcapply v, hcneg, LinearEquiv.neg_apply, neg_one_smul]

omit [Module.Finite (ZMod p) U] in
private theorem zng_span_eq_top (hp : p ≠ 2) {k : ℕ} {z : ↥A} {u : Fin k → U}
    {φ : Fin k → Dual (ZMod p) U}
    (hzact : ∀ v : U, (z : U ≃ₗ[ZMod p] U) v = v - ∑ i, φ i v • u i)
    (hneg : (z : U ≃ₗ[ZMod p] U) = LinearEquiv.neg (ZMod p)) :
    Submodule.span (ZMod p) (Set.range u) = ⊤ := by
  have h2 : ∀ v : U, (2 : ZMod p) • v = ∑ i, φ i v • u i := by
    intro v
    have h := hzact v
    rw [hneg, LinearEquiv.neg_apply] at h
    rw [two_smul]
    calc
      v + v = v - (-v) := by abel
      _ = v - (v - ∑ i, φ i v • u i) := by rw [h]
      _ = ∑ i, φ i v • u i := by abel
  rw [eq_top_iff]
  intro v _
  have h2inv : (2 : ZMod p)⁻¹ * 2 = 1 :=
    inv_mul_cancel₀ (ZMod.prime_ne_zero p 2 hp)
  have hv : v = (2 : ZMod p)⁻¹ • ∑ i, φ i v • u i := by
    calc
      v = ((2 : ZMod p)⁻¹ * 2) • v := by rw [h2inv, one_smul]
      _ = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • v) := by rw [smul_smul]
      _ = (2 : ZMod p)⁻¹ • ∑ i, φ i v • u i := by rw [h2 v]
  rw [hv]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem finrank_eq_and_neg_mem_of_prod_eq_one (hp : p ≠ 2) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {k : ℕ} (hk : 0 < k)
    {d : Fin k → ↥A ⧸ Subgroup.center ↥A} (hd : ∀ i, d i ∈ reflImage p A)
    (hinj : Function.Injective d) (hcomm : Pairwise fun i j => Commute (d i) (d j))
    (hprod : (List.ofFn d).prod = 1) :
    Module.finrank (ZMod p) U = k ∧ (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ A := by
  choose r hr hrk using fun i => exists_unique_refl_of_mem_reflImage hirr hn (hd i)
  choose u φ hφ hrR using fun i => (isRefl_iff hp (r i : U ≃ₗ[ZMod p] U)).mp (hr i).1
  obtain ⟨-, hcommR, hneR⟩ := frame_commute_data hirr hn hφ (fun i => (hr i).1) hrR
    (fun i => (hr i).2) hinj hcomm
  let z : ↥A := (List.ofFn r).prod
  have hzR : (z : U ≃ₗ[ZMod p] U) =
      (List.ofFn fun i => Module.reflection (hφ i)).prod := by
    dsimp only [z]
    exact coe_ofFn_prod_eq hφ hrR
  have hzact : ∀ v : U, (z : U ≃ₗ[ZMod p] U) v = v - ∑ i, φ i v • u i := by
    intro v
    rw [hzR]
    exact prod_reflection_apply hp k u φ hφ hcommR hneR v
  have hcross : ∀ i j, i ≠ j → φ i (u j) = 0 := fun i j hij =>
    apply_eq_zero_of_commute hp (hφ i) (hφ j) (hcommR i j hij) (hneR i j hij)
  have hmkz : QuotientGroup.mk (s := Subgroup.center ↥A) z = 1 := by
    dsimp only [z]
    rw [mk_ofFn_prod (fun i => (hr i).2), hprod]
  have hzcenter : z ∈ Subgroup.center ↥A :=
    (QuotientGroup.eq_one_iff (N := Subgroup.center ↥A) z).mp hmkz
  have hneg := zng_prod_scalar_eq_neg hp hirr hk hφ hcross hzcenter hzact
  have hmem : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ A := by
    rw [← hneg]
    exact z.2
  have hspan := zng_span_eq_top hp (z := z) (u := u) (φ := φ) hzact hneg
  have hLI : LinearIndependent (ZMod p) u :=
    linearIndependent_of_pairwise_commute hp hφ hcommR hneR
  have hfr : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range u)) = k := by
    rw [finrank_span_eq_card hLI, Fintype.card_fin]
  have htop := congrArg (fun W : Submodule (ZMod p) U => Module.finrank (ZMod p) W) hspan
  rw [hfr, finrank_top] at htop
  exact ⟨htop.symm, hmem⟩

private structure zom_RawLift (A : Subgroup (U ≃ₗ[ZMod p] U))
    (a b c : ↥A ⧸ Subgroup.center ↥A) where
  rA : ↥A
  rB : ↥A
  rC : ↥A
  ua : U
  ub : U
  uc : U
  φa : Dual (ZMod p) U
  φb : Dual (ZMod p) U
  φc : Dual (ZMod p) U
  hφa : φa ua = 2
  hφb : φb ub = 2
  hφc : φc uc = 2
  mka : QuotientGroup.mk (s := Subgroup.center ↥A) rA = a
  mkb : QuotientGroup.mk (s := Subgroup.center ↥A) rB = b
  mkc : QuotientGroup.mk (s := Subgroup.center ↥A) rC = c
  rAeq : (rA : U ≃ₗ[ZMod p] U) = Module.reflection hφa
  rBeq : (rB : U ≃ₗ[ZMod p] U) = Module.reflection hφb
  rCeq : (rC : U ≃ₗ[ZMod p] U) = Module.reflection hφc
  hba : φb ua = (φa ub)⁻¹
  hcb : φc ub = (φb uc)⁻¹
  hac : φa uc = (φc ua)⁻¹
  hx0 : φa ub ≠ 0
  hy0 : φb uc ≠ 0
  hw0 : φc ua ≠ 0
  hquad : (φa ub * φb uc * φc ua) ^ 2 - (φa ub * φb uc * φc ua) + 1 = 0

private theorem exists_lift_of_affineTriangle (hp : p ≠ 2) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {a b c : ↥A ⧸ Subgroup.center ↥A}
    (h : AffineTriangle (reflImage p A) a b c) :
    Nonempty (zom_RawLift A a b c) := by
  obtain ⟨haE, hbE, hcE, hab, hac, hbc, hcab⟩ := h
  obtain ⟨rA, ⟨hrA, hrAmk⟩, -⟩ := exists_unique_refl_of_mem_reflImage hirr hn haE
  obtain ⟨rB, ⟨hrB, hrBmk⟩, -⟩ := exists_unique_refl_of_mem_reflImage hirr hn hbE
  obtain ⟨rC, ⟨hrC, hrCmk⟩, -⟩ := exists_unique_refl_of_mem_reflImage hirr hn hcE
  obtain ⟨ua, φa, hφa, hrAR⟩ := (isRefl_iff hp (rA : U ≃ₗ[ZMod p] U)).mp hrA
  obtain ⟨ub, φb, hφb, hrBR⟩ := (isRefl_iff hp (rB : U ≃ₗ[ZMod p] U)).mp hrB
  obtain ⟨uc, φc, hφc, hrCR⟩ := (isRefl_iff hp (rC : U ≃ₗ[ZMod p] U)).mp hrC
  have hAB : orderOf ((rA : U ≃ₗ[ZMod p] U) * (rB : U ≃ₗ[ZMod p] U)) = 3 :=
    orderOf_mul_of_orderOf_mk_mul hirr hn hrA hrB hrAmk hrBmk hab
  have hAC : orderOf ((rA : U ≃ₗ[ZMod p] U) * (rC : U ≃ₗ[ZMod p] U)) = 3 :=
    orderOf_mul_of_orderOf_mk_mul hirr hn hrA hrC hrAmk hrCmk hac
  have hBC : orderOf ((rB : U ≃ₗ[ZMod p] U) * (rC : U ≃ₗ[ZMod p] U)) = 3 :=
    orderOf_mul_of_orderOf_mk_mul hirr hn hrB hrC hrBmk hrCmk hbc
  have hCAC : IsRefl p (((rC * rA * rC : ↥A) : U ≃ₗ[ZMod p] U)) :=
    hrA.conj_mul_self hrC
  have hCACmk : QuotientGroup.mk (s := Subgroup.center ↥A) (rC * rA * rC) = c * a * c := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hrCmk, hrAmk]
  have hcab' : orderOf ((Module.reflection hφc * Module.reflection hφa *
      Module.reflection hφc) * Module.reflection hφb) = 3 := by
    have h := orderOf_mul_of_orderOf_mk_mul hirr hn hCAC hrB hCACmk hrBmk hcab
    simpa [Subgroup.coe_mul, hrAR, hrBR, hrCR] using h
  have hab3 : orderOf (Module.reflection hφa * Module.reflection hφb) = 3 := by
    simpa [hrAR, hrBR] using hAB
  have hac3 : orderOf (Module.reflection hφa * Module.reflection hφc) = 3 := by
    simpa [hrAR, hrCR] using hAC
  have hbc3 : orderOf (Module.reflection hφb * Module.reflection hφc) = 3 := by
    simpa [hrBR, hrCR] using hBC
  obtain ⟨hia, hib, hic, hx0, hy0, hw0, hquad⟩ :=
    zom_affineTriangle_pairing_data hp hφa hφb hφc hab3 hac3 hbc3 hcab'
  exact ⟨⟨rA, rB, rC, ua, ub, uc, φa, φb, φc, hφa, hφb, hφc, hrAmk, hrBmk, hrCmk, hrAR,
    hrBR, hrCR, hia, hib, hic, hx0, hy0, hw0, hquad⟩⟩

omit [Module.Finite (ZMod p) U] in
private theorem zor_exists_smul_of_reflection_eq (hp : p ≠ 2) {u w : U}
    {φ ψ : Dual (ZMod p) U} (hφ : φ u = 2) (hψ : ψ w = 2)
    (h : Module.reflection hφ = Module.reflection hψ) :
    ∃ t : ZMod p, t ≠ 0 ∧ w = t • u ∧ ψ = t⁻¹ • φ := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hu : u ≠ 0 := fun h0 => h2 (by rw [h0, map_zero] at hφ; exact hφ.symm)
  have hw0 : w ≠ 0 := fun h0 => h2 (by rw [h0, map_zero] at hψ; exact hψ.symm)
  have hbase : φ w • u = (2 : ZMod p) • w := by
    have h1 := congrArg (fun e : U ≃ₗ[ZMod p] U => e w) h
    rw [Module.reflection_apply w hφ, Module.reflection_apply w hψ, hψ] at h1
    exact sub_right_inj.mp h1
  let t : ZMod p := (2 : ZMod p)⁻¹ * φ w
  have hw : w = t • u := by
    calc w = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • w) := by
          rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
      _ = (2 : ZMod p)⁻¹ • (φ w • u) := by rw [← hbase]
      _ = t • u := by rw [smul_smul]
  have ht : t ≠ 0 := by
    intro h0
    exact hw0 (by rw [hw, h0, zero_smul])
  refine ⟨t, ht, hw, ?_⟩
  ext x
  have h1 := congrArg (fun e : U ≃ₗ[ZMod p] U => e x) h
  rw [Module.reflection_apply x hφ, Module.reflection_apply x hψ, hw, smul_smul] at h1
  have hinj : Function.Injective (fun c : ZMod p => c • u) := by
    intro a b hab
    have hzero : (a - b) • u = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr hab
    exact sub_eq_zero.mp ((smul_eq_zero_iff_left hu).mp hzero)
  have hcoef : φ x = ψ x * t := hinj (sub_right_inj.mp h1)
  have hgoal : ψ x = t⁻¹ * φ x := by
    rw [hcoef, ← mul_assoc, mul_comm t⁻¹ (ψ x), mul_assoc, inv_mul_cancel₀ ht, mul_one]
  simpa [LinearMap.smul_apply, smul_eq_mul] using hgoal

omit [Module.Finite (ZMod p) U] in
private theorem zor_conj_smul (hp : p ≠ 2) (g : U ≃ₗ[ZMod p] U) {u w : U}
    {φ ψ : Dual (ZMod p) U} (hφ : φ u = 2) (hψ : ψ w = 2)
    (h : g * Module.reflection hφ * g⁻¹ = Module.reflection hψ) :
    ∃ t : ZMod p, t ≠ 0 ∧ w = t • (g u) ∧
      ψ = t⁻¹ • (φ ∘ₗ (g.symm : U →ₗ[ZMod p] U)) := by
  have h' : (φ ∘ₗ (g.symm : U →ₗ[ZMod p] U)) (g u) = 2 := by
    simpa using hφ
  have hconj := conj_reflection g hφ h'
  rw [hconj] at h
  exact zor_exists_smul_of_reflection_eq hp h' hψ h

omit [Module.Finite (ZMod p) U] in
private theorem zor_root_of_smul {t : ZMod p} (ht : t ≠ 0) {g : U ≃ₗ[ZMod p] U} {u w : U}
    (h : w = t • (g u)) : g u = t⁻¹ • w := by
  have h' := congrArg (fun x : U => t⁻¹ • x) h
  rw [smul_smul, inv_mul_cancel₀ ht, one_smul] at h'
  exact h'.symm

omit [Module.Finite (ZMod p) U] in
private theorem zor_left_of_eq_smul_comp {g : U ≃ₗ[ZMod p] U}
    {φ ψ : Dual (ZMod p) U} {t : ZMod p} (ht : t ≠ 0)
    (h : ψ = t⁻¹ • (φ ∘ₗ (g.symm : U →ₗ[ZMod p] U))) :
    ∀ x : U, φ x = t * ψ (g x) := by
  intro x
  have hv : (g.symm : U →ₗ[ZMod p] U) (g x) = x := by simp
  have hx := congrArg (fun f : Dual (ZMod p) U => f (g x)) h
  rw [LinearMap.smul_apply, LinearMap.comp_apply, hv, smul_eq_mul] at hx
  rw [hx, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]

private theorem zor_conj_smul_of_mk (hp : p ≠ 2) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {ĝ r s : ↥A} {u w : U}
    {φ ψ : Dual (ZMod p) U} (hφ : φ u = 2) (hψ : ψ w = 2)
    (hrR : (r : U ≃ₗ[ZMod p] U) = Module.reflection hφ)
    (hsR : (s : U ≃ₗ[ZMod p] U) = Module.reflection hψ)
    (hmk : QuotientGroup.mk (s := Subgroup.center ↥A) (ĝ * r * ĝ⁻¹) =
      QuotientGroup.mk (s := Subgroup.center ↥A) s) :
    ∃ t : ZMod p, t ≠ 0 ∧ w = t • ((ĝ : U ≃ₗ[ZMod p] U) u) ∧
      ψ = t⁻¹ • (φ ∘ₗ ((ĝ : U ≃ₗ[ZMod p] U).symm : U →ₗ[ZMod p] U)) := by
  have hr : IsRefl p (r : U ≃ₗ[ZMod p] U) := by
    rw [hrR]
    exact isRefl_reflection hp hφ
  have hs : IsRefl p (s : U ≃ₗ[ZMod p] U) := by
    rw [hsR]
    exact isRefl_reflection hp hψ
  have hconj : ĝ * r * ĝ⁻¹ = s := by
    refine hirr.mk_injOn_refl hn ?_ hs hmk
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hr.conj (ĝ : U ≃ₗ[ZMod p] U)
  have hlin : (ĝ : U ≃ₗ[ZMod p] U) * Module.reflection hφ * (ĝ : U ≃ₗ[ZMod p] U)⁻¹ =
      Module.reflection hψ := by
    have h1 := congrArg (fun x : ↥A => (x : U ≃ₗ[ZMod p] U)) hconj
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hrR, hsR] at h1
    exact h1
  exact zor_conj_smul hp (ĝ : U ≃ₗ[ZMod p] U) hφ hψ hlin

omit [Module.Finite (ZMod p) U] in
private theorem zor_eq_three_of_kappa {κ ta tb tc x y w x' y' w' : ZMod p}
    (hκ : κ = x * y * w) (hquad : κ ^ 2 - κ + 1 = 0)
    (hx : x = ta * tb⁻¹ * x') (hy : y = tb * tc⁻¹ * y') (hw : w = tc * ta⁻¹ * w')
    (hia : w' = x⁻¹) (hib : y' = y⁻¹) (hic : x' = w⁻¹)
    (hta : ta ≠ 0) (htb : tb ≠ 0) (htc : tc ≠ 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hw0 : w ≠ 0) : p = 3 := by
  have hcalc : κ = (ta * tb⁻¹) * (tb * tc⁻¹) * (tc * ta⁻¹) * (x' * y' * w') := by
    rw [hκ, hx, hy, hw]
    ring
  have hcoef : (ta * tb⁻¹) * (tb * tc⁻¹) * (tc * ta⁻¹) = 1 := by
    field_simp [hta, htb, htc]
  have hprod : x' * y' * w' = κ⁻¹ := by
    rw [hic, hib, hia, hκ]
    field_simp [hx0, hy0, hw0]
  have hκeq : κ = κ⁻¹ := by
    calc κ = (ta * tb⁻¹) * (tb * tc⁻¹) * (tc * ta⁻¹) * (x' * y' * w') := hcalc
      _ = 1 * (x' * y' * w') := by rw [hcoef]
      _ = κ⁻¹ := by rw [one_mul, hprod]
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact mul_ne_zero (mul_ne_zero hx0 hy0) hw0
  have hκsq : κ * κ = 1 := by
    have h := congrArg (fun z : ZMod p => z * κ) hκeq
    rwa [inv_mul_cancel₀ hκ0] at h
  have hκ2 : κ = 2 := by
    linear_combination -hquad + hκsq
  have h3 : (3 : ZMod p) = 0 := by
    have h2' : (2 : ZMod p) ^ 2 - 2 + 1 = 0 := by simpa [hκ2] using hquad
    linear_combination h2'
  have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3
  exact (Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp hdvd

theorem eq_three_of_affineTriangle_of_conj (hp : p ≠ 2) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {a b c g : ↥A ⧸ Subgroup.center ↥A}
    (h : AffineTriangle (reflImage p A) a b c) (ha : g * a * g⁻¹ = a) (hb : g * b * g⁻¹ = c)
    (hc : g * c * g⁻¹ = b) : p = 3 := by
  obtain ⟨raw⟩ := exists_lift_of_affineTriangle hp hirr hn h
  obtain ⟨ĝ, hĝ⟩ := QuotientGroup.mk_surjective g
  obtain ⟨ta, hta0, hua_eq, hφa_eq⟩ :=
    zor_conj_smul_of_mk (ĝ := ĝ) (r := raw.rA) (s := raw.rA) (u := raw.ua) (w := raw.ua)
      (φ := raw.φa) (ψ := raw.φa) hp hirr hn raw.hφa raw.hφa raw.rAeq raw.rAeq (by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, raw.mka, hĝ, ha])
  obtain ⟨tb, htb0, hub_eq, hφb_eq⟩ :=
    zor_conj_smul_of_mk (ĝ := ĝ) (r := raw.rB) (s := raw.rC) (u := raw.ub) (w := raw.uc)
      (φ := raw.φb) (ψ := raw.φc) hp hirr hn raw.hφb raw.hφc raw.rBeq raw.rCeq (by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, raw.mkb, raw.mkc,
          hĝ, hb])
  obtain ⟨tc, htc0, huc_eq, hφc_eq⟩ :=
    zor_conj_smul_of_mk (ĝ := ĝ) (r := raw.rC) (s := raw.rB) (u := raw.uc) (w := raw.ub)
      (φ := raw.φc) (ψ := raw.φb) hp hirr hn raw.hφc raw.hφb raw.rCeq raw.rBeq (by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, raw.mkc, raw.mkb,
          hĝ, hc])
  have hĝua : (ĝ : U ≃ₗ[ZMod p] U) raw.ua = ta⁻¹ • raw.ua :=
    zor_root_of_smul hta0 hua_eq
  have hĝub : (ĝ : U ≃ₗ[ZMod p] U) raw.ub = tb⁻¹ • raw.uc :=
    zor_root_of_smul htb0 hub_eq
  have hĝuc : (ĝ : U ≃ₗ[ZMod p] U) raw.uc = tc⁻¹ • raw.ub :=
    zor_root_of_smul htc0 huc_eq
  have hφa_pt := zor_left_of_eq_smul_comp hta0 hφa_eq
  have hφb_pt := zor_left_of_eq_smul_comp htb0 hφb_eq
  have hφc_pt := zor_left_of_eq_smul_comp htc0 hφc_eq
  have hx : raw.φa raw.ub = ta * tb⁻¹ * raw.φa raw.uc := by
    calc raw.φa raw.ub = ta * raw.φa ((ĝ : U ≃ₗ[ZMod p] U) raw.ub) := hφa_pt raw.ub
      _ = ta * raw.φa (tb⁻¹ • raw.uc) := by rw [hĝub]
      _ = ta * tb⁻¹ * raw.φa raw.uc := by rw [map_smul, smul_eq_mul]; ring
  have hy : raw.φb raw.uc = tb * tc⁻¹ * raw.φc raw.ub := by
    calc raw.φb raw.uc = tb * raw.φc ((ĝ : U ≃ₗ[ZMod p] U) raw.uc) := hφb_pt raw.uc
      _ = tb * raw.φc (tc⁻¹ • raw.ub) := by rw [hĝuc]
      _ = tb * tc⁻¹ * raw.φc raw.ub := by rw [map_smul, smul_eq_mul]; ring
  have hw : raw.φc raw.ua = tc * ta⁻¹ * raw.φb raw.ua := by
    calc raw.φc raw.ua = tc * raw.φb ((ĝ : U ≃ₗ[ZMod p] U) raw.ua) := hφc_pt raw.ua
      _ = tc * raw.φb (ta⁻¹ • raw.ua) := by rw [hĝua]
      _ = tc * ta⁻¹ * raw.φb raw.ua := by rw [map_smul, smul_eq_mul]; ring
  exact zor_eq_three_of_kappa (κ := raw.φa raw.ub * raw.φb raw.uc * raw.φc raw.ua)
    (ta := ta) (tb := tb) (tc := tc) (x := raw.φa raw.ub) (y := raw.φb raw.uc)
    (w := raw.φc raw.ua) (x' := raw.φa raw.uc) (y' := raw.φc raw.ub) (w' := raw.φb raw.ua)
    rfl raw.hquad hx hy hw raw.hba raw.hcb raw.hac hta0 htb0 htc0 raw.hx0 raw.hy0 raw.hw0

theorem false_of_unitaryFourConfig (hp : p ≠ 2) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {a b c d : ↥A ⧸ Subgroup.center ↥A}
    (h : UnitaryFourConfig (reflImage p A) a b c d) : False := by
  obtain ⟨haE, hbE, hcE, hdE, hab, hac, had, hbc, hcd, hbd, hacb, hacd, hlast⟩ := h
  obtain ⟨rA, ⟨hrA, hrAmk⟩, -⟩ := exists_unique_refl_of_mem_reflImage hirr hn haE
  obtain ⟨rB, ⟨hrB, hrBmk⟩, -⟩ := exists_unique_refl_of_mem_reflImage hirr hn hbE
  obtain ⟨rC, ⟨hrC, hrCmk⟩, -⟩ := exists_unique_refl_of_mem_reflImage hirr hn hcE
  obtain ⟨rD, ⟨hrD, hrDmk⟩, -⟩ := exists_unique_refl_of_mem_reflImage hirr hn hdE
  have hAB := orderOf_mul_of_orderOf_mk_mul hirr hn hrA hrB hrAmk hrBmk hab
  have hAC := orderOf_mul_of_orderOf_mk_mul hirr hn hrA hrC hrAmk hrCmk hac
  have hAD := orderOf_mul_of_orderOf_mk_mul hirr hn hrA hrD hrAmk hrDmk had
  have hBC := orderOf_mul_of_orderOf_mk_mul hirr hn hrB hrC hrBmk hrCmk hbc
  have hCD := orderOf_mul_of_orderOf_mk_mul hirr hn hrC hrD hrCmk hrDmk hcd
  have hBD := orderOf_mul_of_orderOf_mk_mul hirr hn hrB hrD hrBmk hrDmk hbd
  have hCAC : IsRefl p (((rC * rA * rC : ↥A) : U ≃ₗ[ZMod p] U)) :=
    hrA.conj_mul_self hrC
  have hCACmk : QuotientGroup.mk (s := Subgroup.center ↥A) (rC * rA * rC) = c * a * c := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hrCmk, hrAmk]
  have hACB_sub : orderOf ((rC * rA * rC : ↥A) * rB) = 3 := by
    rw [← hirr.orderOf_mk_mul_mk hn hCAC hrB, hCACmk, hrBmk]
    exact hacb
  have hACB : orderOf ((((rC * rA * rC : ↥A) : U ≃ₗ[ZMod p] U)) *
      (rB : U ≃ₗ[ZMod p] U)) = 3 := by
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
    exact hACB_sub
  have hACD_sub : orderOf ((rC * rA * rC : ↥A) * rD) = 3 := by
    rw [← hirr.orderOf_mk_mul_mk hn hCAC hrD, hCACmk, hrDmk]
    exact hacd
  have hACD : orderOf ((((rC * rA * rC : ↥A) : U ≃ₗ[ZMod p] U)) *
      (rD : U ≃ₗ[ZMod p] U)) = 3 := by
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
    exact hACD_sub
  have hBAB : IsRefl p (((rB * rA * rB : ↥A) : U ≃ₗ[ZMod p] U)) :=
    hrA.conj_mul_self hrB
  have hDCD : IsRefl p (((rD * rC * rD : ↥A) : U ≃ₗ[ZMod p] U)) :=
    hrC.conj_mul_self hrD
  have hBABmk : QuotientGroup.mk (s := Subgroup.center ↥A) (rB * rA * rB) = b * a * b := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hrBmk, hrAmk]
  have hDCDmk : QuotientGroup.mk (s := Subgroup.center ↥A) (rD * rC * rD) = d * c * d := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hrDmk, hrCmk]
  have hlastAmb : orderOf ((((rB * rA * rB : ↥A) : U ≃ₗ[ZMod p] U)) *
      (((rD * rC * rD : ↥A) : U ≃ₗ[ZMod p] U))) = 3 ∨
      ((rB * rA * rB : ↥A) : U ≃ₗ[ZMod p] U) =
        ((rD * rC * rD : ↥A) : U ≃ₗ[ZMod p] U) := by
    rcases hlast with hord | heq
    · left
      have hsub : orderOf ((rB * rA * rB : ↥A) * (rD * rC * rD : ↥A)) = 3 := by
        rw [← hirr.orderOf_mk_mul_mk hn hBAB hDCD, hBABmk, hDCDmk]
        exact hord
      rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
      exact hsub
    · right
      have hEq : (rB * rA * rB : ↥A) = rD * rC * rD :=
        hirr.mk_injOn_refl hn hBAB hDCD (by rw [hBABmk, hDCDmk]; exact heq)
      simpa using congrArg (fun x : ↥A => (x : U ≃ₗ[ZMod p] U)) hEq
  exact false_of_unitaryFour_of_isRefl hp hrA hrB hrC hrD hAB hAC hAD hBC hCD hBD
    hACB hACD hlastAmb

private structure zom_Lift (A : Subgroup (U ≃ₗ[ZMod p] U))
    (a b c : ↥A ⧸ Subgroup.center ↥A) where
  rA : ↥A
  rB : ↥A
  rC : ↥A
  ua : U
  ub : U
  uc : U
  φa : Dual (ZMod p) U
  φb : Dual (ZMod p) U
  φc : Dual (ZMod p) U
  hφa : φa ua = 2
  hφb : φb ub = 2
  hφc : φc uc = 2
  mka : QuotientGroup.mk rA = a
  mkb : QuotientGroup.mk rB = b
  mkc : QuotientGroup.mk rC = c
  rAeq : (rA : U ≃ₗ[ZMod p] U) = Module.reflection hφa
  rBeq : (rB : U ≃ₗ[ZMod p] U) = Module.reflection hφb
  rCeq : (rC : U ≃ₗ[ZMod p] U) = Module.reflection hφc
  κ : ZMod p
  hab : φa ub = 1
  hba : φb ua = 1
  hbc : φb uc = 1
  hcb : φc ub = 1
  hca : φc ua = κ
  hac : φa uc = κ⁻¹
  hκ : κ ^ 2 - κ + 1 = 0

variable {a b c : ↥A ⧸ Subgroup.center ↥A}

private def zom_Lift.r (L : zom_Lift A a b c) : Fin 3 → ↥A := ![L.rA, L.rB, L.rC]

private def zom_Lift.u (L : zom_Lift A a b c) : Fin 3 → U := ![L.ua, L.ub, L.uc]

private def zom_Lift.φ (L : zom_Lift A a b c) : Fin 3 → Dual (ZMod p) U :=
  ![L.φa, L.φb, L.φc]

private def zom_Lift.q (_L : zom_Lift A a b c) :
    Fin 3 → ↥A ⧸ Subgroup.center ↥A := ![a, b, c]

omit [Module.Finite (ZMod p) U] in
private theorem zom_Lift.hpair (L : zom_Lift A a b c) (i : Fin 3) :
    L.φ i (L.u i) = 2 := by
  fin_cases i <;> simp [zom_Lift.φ, zom_Lift.u, L.hφa, L.hφb, L.hφc]

omit [Module.Finite (ZMod p) U] in
private theorem zom_Lift.rEq (L : zom_Lift A a b c) (i : Fin 3) :
    (L.r i : U ≃ₗ[ZMod p] U) = Module.reflection (L.hpair i) := by
  fin_cases i
  · simpa [zom_Lift.r, zom_Lift.hpair, zom_Lift.φ, zom_Lift.u] using L.rAeq
  · simpa [zom_Lift.r, zom_Lift.hpair, zom_Lift.φ, zom_Lift.u] using L.rBeq
  · simpa [zom_Lift.r, zom_Lift.hpair, zom_Lift.φ, zom_Lift.u] using L.rCeq

omit [Module.Finite (ZMod p) U] in
private theorem zom_Lift.mk_r (L : zom_Lift A a b c) (i : Fin 3) :
    QuotientGroup.mk (L.r i) = L.q i := by
  fin_cases i
  · simpa [zom_Lift.r, zom_Lift.q] using L.mka
  · simpa [zom_Lift.r, zom_Lift.q] using L.mkb
  · simpa [zom_Lift.r, zom_Lift.q] using L.mkc

private theorem zom_pairing_eq_zero_of_commute_mk (hp : p ≠ 2) (hirr : AbsIrred p A)
    (hn3 : 3 ≤ Module.finrank (ZMod p) U)
    {r r' : ↥A} {u u' : U} {φ φ' : Dual (ZMod p) U}
    (hφ : φ u = 2) (hφ' : φ' u' = 2)
    (hr : (r : U ≃ₗ[ZMod p] U) = Module.reflection hφ)
    (hr' : (r' : U ≃ₗ[ZMod p] U) = Module.reflection hφ')
    (hmk : Commute (QuotientGroup.mk (s := Subgroup.center ↥A) r)
      (QuotientGroup.mk (s := Subgroup.center ↥A) r'))
    (hne : QuotientGroup.mk (s := Subgroup.center ↥A) r ≠
      QuotientGroup.mk (s := Subgroup.center ↥A) r') : φ u' = 0 := by
  have hcommA : Commute r r' :=
    (hirr.commute_mk_iff hn3 (by rw [hr']; exact isRefl_reflection hp hφ')).mp hmk
  have hcommL : Commute (r : U ≃ₗ[ZMod p] U) (r' : U ≃ₗ[ZMod p] U) :=
    (commute_subtype_coe_iff).mpr hcommA
  have hneL : (r : U ≃ₗ[ZMod p] U) ≠ (r' : U ≃ₗ[ZMod p] U) := by
    intro h
    exact hne (by rw [Subtype.ext h])
  exact apply_eq_zero_of_commute hp hφ hφ' (by simpa [hr, hr'] using hcommL)
    (by simpa [hr, hr'] using hneL)

private theorem zom_false_of_commute_involutions {X : Type*} [Group X] {x y : X}
    (hx : x * x = 1) (hy : y * y = 1) (hc : Commute x y)
    (h : orderOf (x * y) = 3) : False := by
  have hsq : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hc.eq]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx, hy, one_mul]
  have hdvd : orderOf (x * y) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hsq)
  rw [h] at hdvd
  norm_num at hdvd

private theorem zom_ne_second_of_commute {X : Type*} [Group X] {x y a' b' c' : X}
    (hx : x * x = 1) (hy : y * y = 1) (hxy : orderOf (x * y) = 3)
    (ha : Commute y a') (hb : Commute y b') (hc : Commute y c') :
    x ≠ a' ∧ x ≠ b' ∧ x ≠ c' := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact zom_false_of_commute_involutions hx hy (by rw [← h] at ha; exact ha.symm) hxy
  · intro h
    exact zom_false_of_commute_involutions hx hy (by rw [← h] at hb; exact hb.symm) hxy
  · intro h
    exact zom_false_of_commute_involutions hx hy (by rw [← h] at hc; exact hc.symm) hxy

omit [Module.Finite (ZMod p) U] in
private theorem zom_Lift.mk_sq (hp : p ≠ 2) (L : zom_Lift A a b c) (i : Fin 3) :
    QuotientGroup.mk (s := Subgroup.center ↥A) (L.r i) *
      QuotientGroup.mk (s := Subgroup.center ↥A) (L.r i) = 1 := by
  rw [← QuotientGroup.mk_mul (N := Subgroup.center ↥A)]
  have h2 : L.r i * L.r i = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, L.rEq i]
    exact (isRefl_reflection hp (L.hpair i)).1
  rw [h2, QuotientGroup.mk_one]

omit [Module.Finite (ZMod p) U] in
private theorem zom_Lift.q_sq (hp : p ≠ 2) (L : zom_Lift A a b c) (i : Fin 3) :
    L.q i * L.q i = 1 := by
  rw [← L.mk_r i, zom_Lift.mk_sq hp L i]

variable {a' b' c' : ↥A ⧸ Subgroup.center ↥A}

private theorem zom_cross_pairings (hp : p ≠ 2) (hirr : AbsIrred p A)
    (hn3 : 3 ≤ Module.finrank (ZMod p) U)
    (L : zom_Lift A a b c) (L' : zom_Lift A a' b' c')
    (hcomm : ∀ i j : Fin 3, Commute (L.q i) (L'.q j))
    (hne : ∀ i j : Fin 3, L.q i ≠ L'.q j) :
    (∀ i j : Fin 3, L.φ i (L'.u j) = 0) ∧
      (∀ i j : Fin 3, L'.φ i (L.u j) = 0) := by
  constructor
  · intro i j
    exact zom_pairing_eq_zero_of_commute_mk hp hirr hn3 (L.hpair i) (L'.hpair j)
      (L.rEq i) (L'.rEq j)
      (by rw [L.mk_r i, L'.mk_r j]; exact hcomm i j)
      (by rw [L.mk_r i, L'.mk_r j]; exact hne i j)
  · intro i j
    exact zom_pairing_eq_zero_of_commute_mk hp hirr hn3 (L'.hpair i) (L.hpair j)
      (L'.rEq i) (L.rEq j)
      (by rw [L'.mk_r i, L.mk_r j]; exact (hcomm j i).symm)
      (by rw [L'.mk_r i, L.mk_r j]; exact fun h => hne j i h.symm)

private theorem zom_det_three {κ : ZMod p} (hκ : κ ^ 2 - κ + 1 = 0) :
    (!![2, 1, κ⁻¹; 1, 2, 1; κ, 1, 2] : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 3 := by
  have hκ0 : κ ≠ 0 := by
    intro h0
    rw [h0] at hκ
    norm_num at hκ
  rw [Matrix.det_fin_three]
  norm_num
  field_simp [hκ0]
  linear_combination hκ

private theorem zom_coeff_zero (hp3 : p ≠ 3) {κ a b c : ZMod p}
    (hκ : κ ^ 2 - κ + 1 = 0)
    (e1 : 2 * a + b + κ⁻¹ * c = 0)
    (e2 : a + 2 * b + c = 0)
    (e3 : κ * a + b + 2 * c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hdet : (!![2, 1, κ⁻¹; 1, 2, 1; κ, 1, 2] : Matrix (Fin 3) (Fin 3) (ZMod p)).det ≠ 0 := by
    rw [zom_det_three hκ]
    exact ZMod.prime_ne_zero p 3 hp3
  let g : Fin 3 → ZMod p := ![a, b, c]
  have hv : (!![2, 1, κ⁻¹; 1, 2, 1; κ, 1, 2] : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec g = 0 := by
    ext i
    fin_cases i
    · simp [g]
      linear_combination e1
    · simp [g]
      linear_combination e2
    · simp [g]
      linear_combination e3
  have hg := Matrix.eq_zero_of_mulVec_eq_zero hdet hv
  have ha : a = 0 := by simpa [g] using congrFun hg 0
  have hb : b = 0 := by simpa [g] using congrFun hg 1
  have hc : c = 0 := by simpa [g] using congrFun hg 2
  exact ⟨ha, hb, hc⟩

omit [Module.Finite (ZMod p) U] in
private theorem zom_cross_left_a (L : zom_Lift A a b c) (L' : zom_Lift A a' b' c')
    (hcross : (∀ i j : Fin 3, L.φ i (L'.u j) = 0) ∧
      (∀ i j : Fin 3, L'.φ i (L.u j) = 0)) (j : Fin 3) : L.φa (L'.u j) = 0 := by
  simpa [zom_Lift.φ] using hcross.1 0 j

omit [Module.Finite (ZMod p) U] in
private theorem zom_cross_left_b (L : zom_Lift A a b c) (L' : zom_Lift A a' b' c')
    (hcross : (∀ i j : Fin 3, L.φ i (L'.u j) = 0) ∧
      (∀ i j : Fin 3, L'.φ i (L.u j) = 0)) (j : Fin 3) : L.φb (L'.u j) = 0 := by
  simpa [zom_Lift.φ] using hcross.1 1 j

omit [Module.Finite (ZMod p) U] in
private theorem zom_cross_left_c (L : zom_Lift A a b c) (L' : zom_Lift A a' b' c')
    (hcross : (∀ i j : Fin 3, L.φ i (L'.u j) = 0) ∧
      (∀ i j : Fin 3, L'.φ i (L.u j) = 0)) (j : Fin 3) : L.φc (L'.u j) = 0 := by
  simpa [zom_Lift.φ] using hcross.1 2 j

omit [Module.Finite (ZMod p) U] in
private theorem zom_cross_right_a (L : zom_Lift A a b c) (L' : zom_Lift A a' b' c')
    (hcross : (∀ i j : Fin 3, L.φ i (L'.u j) = 0) ∧
      (∀ i j : Fin 3, L'.φ i (L.u j) = 0)) (j : Fin 3) : L'.φa (L.u j) = 0 := by
  simpa [zom_Lift.φ] using hcross.2 0 j

omit [Module.Finite (ZMod p) U] in
private theorem zom_cross_right_b (L : zom_Lift A a b c) (L' : zom_Lift A a' b' c')
    (hcross : (∀ i j : Fin 3, L.φ i (L'.u j) = 0) ∧
      (∀ i j : Fin 3, L'.φ i (L.u j) = 0)) (j : Fin 3) : L'.φb (L.u j) = 0 := by
  simpa [zom_Lift.φ] using hcross.2 1 j

omit [Module.Finite (ZMod p) U] in
private theorem zom_cross_right_c (L : zom_Lift A a b c) (L' : zom_Lift A a' b' c')
    (hcross : (∀ i j : Fin 3, L.φ i (L'.u j) = 0) ∧
      (∀ i j : Fin 3, L'.φ i (L.u j) = 0)) (j : Fin 3) : L'.φc (L.u j) = 0 := by
  simpa [zom_Lift.φ] using hcross.2 2 j

omit [Module.Finite (ZMod p) U] in
private theorem zom_Lift.pair01 (L : zom_Lift A a b c) : L.φ 0 (L.u 1) = 1 := by
  simpa [zom_Lift.φ, zom_Lift.u] using L.hab

omit [Module.Finite (ZMod p) U] in
private theorem zom_Lift.pair02 (L : zom_Lift A a b c) : L.φ 0 (L.u 2) = L.κ⁻¹ := by
  simpa [zom_Lift.φ, zom_Lift.u] using L.hac

omit [Module.Finite (ZMod p) U] in
private theorem zom_Lift.pair10 (L : zom_Lift A a b c) : L.φ 1 (L.u 0) = 1 := by
  simpa [zom_Lift.φ, zom_Lift.u] using L.hba

omit [Module.Finite (ZMod p) U] in
private theorem zom_Lift.pair12 (L : zom_Lift A a b c) : L.φ 1 (L.u 2) = 1 := by
  simpa [zom_Lift.φ, zom_Lift.u] using L.hbc

omit [Module.Finite (ZMod p) U] in
private theorem zom_Lift.pair20 (L : zom_Lift A a b c) : L.φ 2 (L.u 0) = L.κ := by
  simpa [zom_Lift.φ, zom_Lift.u] using L.hca

omit [Module.Finite (ZMod p) U] in
private theorem zom_Lift.pair21 (L : zom_Lift A a b c) : L.φ 2 (L.u 1) = 1 := by
  simpa [zom_Lift.φ, zom_Lift.u] using L.hcb

omit [Module.Finite (ZMod p) U] in
private theorem zom_pair_roots_linearIndependent (hp3 : p ≠ 3)
    (L : zom_Lift A a b c) (L' : zom_Lift A a' b' c')
    (hcross : (∀ i j : Fin 3, L.φ i (L'.u j) = 0) ∧
      (∀ i j : Fin 3, L'.φ i (L.u j) = 0)) :
    LinearIndependent (ZMod p) (![L.ua, L.ub, L.uc, L'.ua, L'.ub, L'.uc] : Fin 6 → U) := by
  rw [Fintype.linearIndependent_iff]
  let root : Fin 6 → U := ![L.u 0, L.u 1, L.u 2, L'.u 0, L'.u 1, L'.u 2]
  have hroot : root = ![L.ua, L.ub, L.uc, L'.ua, L'.ub, L'.uc] := by
    simp [root, zom_Lift.u]
  intro g hg
  have hg' : ∑ i, g i • root i = 0 := by simpa [hroot] using hg
  have e1 : 2 * g 0 + g 1 + L.κ⁻¹ * g 2 = 0 := by
    have h := congrArg (fun v => L.φ 0 v) hg'
    simp only [map_zero, map_add, map_smul, Fin.sum_univ_six, root, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, smul_eq_mul,
      hcross.1 0 0, hcross.1 0 1, hcross.1 0 2, L.hpair, L.pair01, L.pair02] at h
    linear_combination h
  have e2 : g 0 + 2 * g 1 + g 2 = 0 := by
    have h := congrArg (fun v => L.φ 1 v) hg'
    simp only [map_zero, map_add, map_smul, Fin.sum_univ_six, root, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, smul_eq_mul,
      hcross.1 1 0, hcross.1 1 1, hcross.1 1 2, L.hpair, L.pair10, L.pair12] at h
    linear_combination h
  have e3 : L.κ * g 0 + g 1 + 2 * g 2 = 0 := by
    have h := congrArg (fun v => L.φ 2 v) hg'
    simp only [map_zero, map_add, map_smul, Fin.sum_univ_six, root, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, smul_eq_mul,
      hcross.1 2 0, hcross.1 2 1, hcross.1 2 2, L.hpair, L.pair20, L.pair21] at h
    linear_combination h
  obtain ⟨h0, h1, h2⟩ := zom_coeff_zero hp3 L.hκ e1 e2 e3
  have e4 : 2 * g 3 + g 4 + L'.κ⁻¹ * g 5 = 0 := by
    have h := congrArg (fun v => L'.φ 0 v) hg'
    simp only [map_zero, map_add, map_smul, Fin.sum_univ_six, root, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, smul_eq_mul,
      hcross.2 0 0, hcross.2 0 1, hcross.2 0 2, L'.hpair, L'.pair01, L'.pair02] at h
    linear_combination h
  have e5 : g 3 + 2 * g 4 + g 5 = 0 := by
    have h := congrArg (fun v => L'.φ 1 v) hg'
    simp only [map_zero, map_add, map_smul, Fin.sum_univ_six, root, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, smul_eq_mul,
      hcross.2 1 0, hcross.2 1 1, hcross.2 1 2, L'.hpair, L'.pair10, L'.pair12] at h
    linear_combination h
  have e6 : L'.κ * g 3 + g 4 + 2 * g 5 = 0 := by
    have h := congrArg (fun v => L'.φ 2 v) hg'
    simp only [map_zero, map_add, map_smul, Fin.sum_univ_six, root, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, smul_eq_mul,
      hcross.2 2 0, hcross.2 2 1, hcross.2 2 2, L'.hpair, L'.pair20, L'.pair21] at h
    linear_combination h
  obtain ⟨h3, h4, h5⟩ := zom_coeff_zero hp3 L'.hκ e4 e5 e6
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

omit [Module.Finite (ZMod p) U] in
private theorem zom_cycle_first_apply
    {ua ub uc : U} {φa φb φc : Dual (ZMod p) U}
    (hφa : φa ua = 2) (hφb : φb ub = 2) (hφc : φc uc = 2)
    {κ : ZMod p} (hκ0 : κ ≠ 0)
    (hab : φa ub = 1) (hba : φb ua = 1) (hbc : φb uc = 1) (hcb : φc ub = 1)
    (hca : φc ua = κ) (hac : φa uc = κ⁻¹) :
    (Module.reflection hφa * Module.reflection hφb * Module.reflection hφc) ua =
        -(κ - 1) • ua + (κ - 1) • ub - κ • uc ∧
      (Module.reflection hφa * Module.reflection hφb * Module.reflection hφc) ub =
        κ⁻¹ • ua - uc ∧
      (Module.reflection hφa * Module.reflection hφb * Module.reflection hφc) uc =
        (κ⁻¹ - 1) • ua + ub - uc := by
  have hinv : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ0
  refine ⟨?_, ?_, ?_⟩
  · simp only [LinearEquiv.mul_apply, Module.reflection_apply, map_sub, map_smul,
      hφa, hab, hba, hbc, hca, hac]
    simp only [smul_sub, smul_smul, hinv, one_smul]
    module
  · simp only [LinearEquiv.mul_apply, Module.reflection_apply, map_sub, map_smul,
      hφb, hab, hbc, hcb, hac]
    simp only [smul_sub, smul_smul, one_smul]
    module
  · simp only [LinearEquiv.mul_apply, Module.reflection_apply, map_sub, map_smul,
      hφc, hab, hbc, hac]
    simp only [smul_sub, smul_smul, one_smul]
    module

omit [Module.Finite (ZMod p) U] in
private theorem zom_cycle_sq
    {ua ub uc : U} {φa φb φc : Dual (ZMod p) U}
    (hφa : φa ua = 2) (hφb : φb ub = 2) (hφc : φc uc = 2)
    {κ : ZMod p}
    (hab : φa ub = 1) (hba : φb ua = 1) (hbc : φb uc = 1) (hcb : φc ub = 1)
    (hca : φc ua = κ) (hac : φa uc = κ⁻¹)
    (hκ : κ ^ 2 - κ + 1 = 0) :
    ((Module.reflection hφa * Module.reflection hφb * Module.reflection hφc) ^ 2) ua =
        (κ - 1) • ua ∧
      ((Module.reflection hφa * Module.reflection hφb * Module.reflection hφc) ^ 2) ub =
        (κ - 1) • ub ∧
      ((Module.reflection hφa * Module.reflection hφb * Module.reflection hφc) ^ 2) uc =
        (κ - 1) • uc := by
  let T : U ≃ₗ[ZMod p] U := Module.reflection hφa * Module.reflection hφb * Module.reflection hφc
  have hκ0 : κ ≠ 0 := by
    intro h0
    rw [h0] at hκ
    norm_num at hκ
  have hsum : κ + κ⁻¹ = 1 := by
    field_simp [hκ0]
    linear_combination hκ
  have hkinv : κ⁻¹ = 1 - κ := by linear_combination hsum
  have hκua : (κ ^ 2 - κ + 1) • ua = 0 := by rw [hκ, zero_smul]
  have hκub : (κ ^ 2 - κ + 1) • ub = 0 := by rw [hκ, zero_smul]
  have hκuc : (κ ^ 2 - κ + 1) • uc = 0 := by rw [hκ, zero_smul]
  obtain ⟨hfst, hsnd, hthd⟩ :=
    zom_cycle_first_apply hφa hφb hφc hκ0 hab hba hbc hcb hca hac
  have hTua : T ua = -(κ - 1) • ua + (κ - 1) • ub - κ • uc := by simpa [T] using hfst
  have hTub : T ub = κ⁻¹ • ua - uc := by simpa [T] using hsnd
  have hTuc : T uc = (κ⁻¹ - 1) • ua + ub - uc := by simpa [T] using hthd
  have h2a : (T ^ 2) ua = (κ - 1) • ua := by
    calc
      (T ^ 2) ua = T (T ua) := by rw [pow_two, LinearEquiv.mul_apply]
      _ = T (-(κ - 1) • ua + (κ - 1) • ub - κ • uc) := by rw [hTua]
      _ = -(κ - 1) • T ua + (κ - 1) • T ub - κ • T uc := by
        simp [map_sub, map_smul, map_add]
      _ = (κ - 1) • ua := by
        rw [hTua, hTub, hTuc, hkinv]
        linear_combination (norm := module) hκua - hκub + hκuc
  have h2b : (T ^ 2) ub = (κ - 1) • ub := by
    calc
      (T ^ 2) ub = T (T ub) := by rw [pow_two, LinearEquiv.mul_apply]
      _ = T (κ⁻¹ • ua - uc) := by rw [hTub]
      _ = κ⁻¹ • T ua - T uc := by simp [map_sub, map_smul]
      _ = (κ - 1) • ub := by
        rw [hTua, hTuc, hkinv]
        linear_combination (norm := module) hκua - hκub + hκuc
  have h2c : (T ^ 2) uc = (κ - 1) • uc := by
    calc
      (T ^ 2) uc = T (T uc) := by rw [pow_two, LinearEquiv.mul_apply]
      _ = T ((κ⁻¹ - 1) • ua + ub - uc) := by rw [hTuc]
      _ = (κ⁻¹ - 1) • T ua + T ub - T uc := by simp [map_sub, map_smul, map_add]
      _ = (κ - 1) • uc := by
        rw [hTua, hTub, hTuc, hkinv]
        linear_combination (norm := module) hκua - hκub + hκuc
  exact ⟨by simpa [T] using h2a, by simpa [T] using h2b, by simpa [T] using h2c⟩

private structure zom_DataCore (L : zom_Lift A a b c) (L' : zom_Lift A a' b' c') where
  t : ↥A
  s : ↥A
  T : U ≃ₗ[ZMod p] U
  S : U ≃ₗ[ZMod p] U
  hTcoe : (t : U ≃ₗ[ZMod p] U) = T
  hScoe : (s : U ≃ₗ[ZMod p] U) = S
  hT : T = Module.reflection L.hφa * Module.reflection L.hφb * Module.reflection L.hφc
  hS : S = Module.reflection L'.hφa * Module.reflection L'.hφb * Module.reflection L'.hφc
  ω : ZMod p
  ω' : ZMod p
  hω : ω ^ 2 + ω + 1 = 0
  hω' : ω' ^ 2 + ω' + 1 = 0
  hT2a : ∀ i : Fin 3, (T ^ 2) (L.u i) = ω • L.u i
  hS2a : ∀ i : Fin 3, (S ^ 2) (L'.u i) = ω' • L'.u i

private structure zom_Data (L : zom_Lift A a b c) (L' : zom_Lift A a' b' c')
    extends zom_DataCore L L' where
  hTfix2 : ∀ j : Fin 3, (T ^ 2) (L'.u j) = L'.u j
  hSfix2 : ∀ i : Fin 3, (S ^ 2) (L.u i) = L.u i
  hSfix4 : ∀ i : Fin 3, ((S ^ 2) ^ 2) (L.u i) = L.u i

private def zom_data_core (L : zom_Lift A a b c) (L' : zom_Lift A a' b' c') :
    zom_DataCore L L' := by
  let t : ↥A := L.rA * L.rB * L.rC
  let s : ↥A := L'.rA * L'.rB * L'.rC
  let T : U ≃ₗ[ZMod p] U := t
  let S : U ≃ₗ[ZMod p] U := s
  let ω : ZMod p := L.κ - 1
  let ω' : ZMod p := L'.κ - 1
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h := L.hκ
    simp only [ω]
    linear_combination h
  have hω' : ω' ^ 2 + ω' + 1 = 0 := by
    have h := L'.hκ
    simp only [ω']
    linear_combination h
  have hT : T = Module.reflection L.hφa * Module.reflection L.hφb * Module.reflection L.hφc := by
    simp [T, t, Subgroup.coe_mul, L.rAeq, L.rBeq, L.rCeq]
  have hS : S = Module.reflection L'.hφa * Module.reflection L'.hφb * Module.reflection L'.hφc := by
    simp [S, s, Subgroup.coe_mul, L'.rAeq, L'.rBeq, L'.rCeq]
  have hsq := zom_cycle_sq L.hφa L.hφb L.hφc L.hab L.hba L.hbc L.hcb L.hca L.hac L.hκ
  have hsq' := zom_cycle_sq L'.hφa L'.hφb L'.hφc L'.hab L'.hba L'.hbc L'.hcb L'.hca L'.hac L'.hκ
  have hT2a : ∀ i : Fin 3, (T ^ 2) (L.u i) = ω • L.u i := by
    intro i
    fin_cases i
    · simpa [hT, ω, zom_Lift.u] using hsq.1
    · simpa [hT, ω, zom_Lift.u] using hsq.2.1
    · simpa [hT, ω, zom_Lift.u] using hsq.2.2
  have hS2a : ∀ i : Fin 3, (S ^ 2) (L'.u i) = ω' • L'.u i := by
    intro i
    fin_cases i
    · simpa [hS, ω', zom_Lift.u] using hsq'.1
    · simpa [hS, ω', zom_Lift.u] using hsq'.2.1
    · simpa [hS, ω', zom_Lift.u] using hsq'.2.2
  exact ⟨t, s, T, S, rfl, rfl, hT, hS, ω, ω', hω, hω', hT2a, hS2a⟩

private def zom_data (L : zom_Lift A a b c) (L' : zom_Lift A a' b' c')
    (hcross : (∀ i j : Fin 3, L.φ i (L'.u j) = 0) ∧
      (∀ i j : Fin 3, L'.φ i (L.u j) = 0)) : zom_Data L L' := by
  let D : zom_DataCore L L' := zom_data_core L L'
  have hfixT : ∀ j : Fin 3, D.T (L'.u j) = L'.u j := by
    intro j
    have h1 : Module.reflection L.hφa (L'.u j) = L'.u j := by
      rw [Module.reflection_apply, zom_cross_left_a L L' hcross j, zero_smul, sub_zero]
    have h2 : Module.reflection L.hφb (L'.u j) = L'.u j := by
      rw [Module.reflection_apply, zom_cross_left_b L L' hcross j, zero_smul, sub_zero]
    have h3 : Module.reflection L.hφc (L'.u j) = L'.u j := by
      rw [Module.reflection_apply, zom_cross_left_c L L' hcross j, zero_smul, sub_zero]
    simp [D.hT, LinearEquiv.mul_apply, h1, h2, h3]
  have hfixS : ∀ i : Fin 3, D.S (L.u i) = L.u i := by
    intro i
    have h1 : Module.reflection L'.hφa (L.u i) = L.u i := by
      rw [Module.reflection_apply, zom_cross_right_a L L' hcross i, zero_smul, sub_zero]
    have h2 : Module.reflection L'.hφb (L.u i) = L.u i := by
      rw [Module.reflection_apply, zom_cross_right_b L L' hcross i, zero_smul, sub_zero]
    have h3 : Module.reflection L'.hφc (L.u i) = L.u i := by
      rw [Module.reflection_apply, zom_cross_right_c L L' hcross i, zero_smul, sub_zero]
    simp [D.hS, LinearEquiv.mul_apply, h1, h2, h3]
  have hTfix2 : ∀ j : Fin 3, (D.T ^ 2) (L'.u j) = L'.u j := by
    intro j
    rw [pow_two, LinearEquiv.mul_apply, hfixT j, hfixT j]
  have hSfix2 : ∀ i : Fin 3, (D.S ^ 2) (L.u i) = L.u i := by
    intro i
    rw [pow_two, LinearEquiv.mul_apply, hfixS i, hfixS i]
  have hSfix4 : ∀ i : Fin 3, ((D.S ^ 2) ^ 2) (L.u i) = L.u i := by
    intro i
    rw [pow_two, LinearEquiv.mul_apply, hSfix2 i, hSfix2 i]
  exact ⟨D, hTfix2, hSfix2, hSfix4⟩

omit [Module.Finite (ZMod p) U] in
private theorem zom_case_eq (L : zom_Lift A a b c) (L' : zom_Lift A a' b' c')
    (D : zom_Data L L')
    (hspan : Submodule.span (ZMod p)
      (Set.range (![L.u 0, L.u 1, L.u 2, L'.u 0, L'.u 1, L'.u 2] : Fin 6 → U)) = ⊤)
    (hcase : D.ω' = D.ω) :
    ∃ g ∈ A, ∀ v, g v = D.ω • v := by
  let gA : ↥A := D.t ^ 2 * D.s ^ 2
  have hcoe : (gA : U ≃ₗ[ZMod p] U) = D.T ^ 2 * D.S ^ 2 := by
    simp [gA, D.hTcoe, D.hScoe, Subgroup.coe_mul]
  refine ⟨(gA : U ≃ₗ[ZMod p] U), gA.2, ?_⟩
  have hact : (gA : U ≃ₗ[ZMod p] U) = D.ω • (LinearMap.id : U →ₗ[ZMod p] U) := by
    refine LinearMap.ext_on hspan ?_
    rintro x ⟨i, rfl⟩
    fin_cases i <;>
      simp [hcoe, D.hSfix2, D.hT2a, D.hTfix2, D.hS2a, hcase,
        Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  intro v
  have := LinearMap.congr_fun hact v
  simpa using this

omit [Module.Finite (ZMod p) U] in
private theorem zom_case_ne (L : zom_Lift A a b c) (L' : zom_Lift A a' b' c')
    (D : zom_Data L L')
    (hspan : Submodule.span (ZMod p)
      (Set.range (![L.u 0, L.u 1, L.u 2, L'.u 0, L'.u 1, L'.u 2] : Fin 6 → U)) = ⊤)
    (hneq : D.ω' ≠ D.ω) :
    ∃ g ∈ A, ∀ v, g v = D.ω • v := by
  have hω'eq : D.ω' = D.ω ^ 2 := by
    have hfac : (D.ω' - D.ω) * (D.ω' + D.ω + 1) = 0 := by
      linear_combination D.hω' - D.hω
    have hne : D.ω' - D.ω ≠ 0 := sub_ne_zero.mpr hneq
    have hsum : D.ω' + D.ω + 1 = 0 := (mul_eq_zero.mp hfac).resolve_left hne
    linear_combination hsum - D.hω
  have hω3 : D.ω ^ 3 = 1 := by
    linear_combination (D.ω - 1) * D.hω
  have hω4 : D.ω ^ 2 * D.ω ^ 2 = D.ω := by
    calc
      D.ω ^ 2 * D.ω ^ 2 = D.ω ^ 4 := by ring
      _ = D.ω ^ 3 * D.ω := by ring
      _ = D.ω := by rw [hω3, one_mul]
  have hω'2 : D.ω' * D.ω' = D.ω := by simpa [hω'eq] using hω4
  let gA : ↥A := D.t ^ 2 * (D.s ^ 2) ^ 2
  have hcoe : (gA : U ≃ₗ[ZMod p] U) = D.T ^ 2 * (D.S ^ 2) ^ 2 := by
    simp [gA, D.hTcoe, D.hScoe, Subgroup.coe_mul]
  refine ⟨(gA : U ≃ₗ[ZMod p] U), gA.2, ?_⟩
  have hS4 : ∀ j : Fin 3, ((D.S ^ 2) ^ 2) (L'.u j) = D.ω • L'.u j := by
    intro j
    calc
      ((D.S ^ 2) ^ 2) (L'.u j) = (D.S ^ 2) ((D.S ^ 2) (L'.u j)) := by
        rw [pow_two, LinearEquiv.mul_apply]
      _ = (D.S ^ 2) (D.ω' • L'.u j) := by rw [D.hS2a j]
      _ = D.ω' • (D.S ^ 2) (L'.u j) := by rw [map_smul]
      _ = D.ω' • (D.ω' • L'.u j) := by rw [D.hS2a j]
      _ = (D.ω' * D.ω') • L'.u j := by rw [smul_smul]
      _ = D.ω • L'.u j := by rw [hω'2]
  have hact : (gA : U ≃ₗ[ZMod p] U) = D.ω • (LinearMap.id : U →ₗ[ZMod p] U) := by
    refine LinearMap.ext_on hspan ?_
    rintro x ⟨i, rfl⟩
    fin_cases i <;>
      simp [hcoe, D.hSfix4, D.hT2a, D.hTfix2, hS4,
        Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  intro v
  have := LinearMap.congr_fun hact v
  simpa using this

omit [Module.Finite (ZMod p) U] in
private theorem zom_scalar_of_lifts (hp3 : p ≠ 3)
    (L : zom_Lift A a b c) (L' : zom_Lift A a' b' c')
    (hcross : (∀ i j : Fin 3, L.φ i (L'.u j) = 0) ∧
      (∀ i j : Fin 3, L'.φ i (L.u j) = 0))
    (hn : Module.finrank (ZMod p) U = 6) :
    ∃ ω : ZMod p, ω ^ 2 + ω + 1 = 0 ∧ ∃ g ∈ A, ∀ v, g v = ω • v := by
  have D : zom_Data L L' := zom_data L L' hcross
  let root : Fin 6 → U := ![L.u 0, L.u 1, L.u 2, L'.u 0, L'.u 1, L'.u 2]
  have hLI : LinearIndependent (ZMod p) root := by
    simpa [root, zom_Lift.u] using zom_pair_roots_linearIndependent hp3 L L' hcross
  have hspan : Submodule.span (ZMod p) (Set.range root) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hn])
  have hspan' : Submodule.span (ZMod p)
      (Set.range (![L.u 0, L.u 1, L.u 2, L'.u 0, L'.u 1, L'.u 2] : Fin 6 → U)) = ⊤ := by
    simpa [root] using hspan
  by_cases hcase : D.ω' = D.ω
  · obtain ⟨g, hg, hact⟩ := zom_case_eq L L' D hspan' hcase
    exact ⟨D.ω, D.hω, g, hg, hact⟩
  · obtain ⟨g, hg, hact⟩ := zom_case_ne L L' D hspan' hcase
    exact ⟨D.ω, D.hω, g, hg, hact⟩

omit [Module.Finite (ZMod p) U] in
private theorem zom_cross_conditions (hp : p ≠ 2) (L : zom_Lift A a b c)
    (L' : zom_Lift A a' b' c') (h : AffineTriangle (reflImage p A) a b c)
    (hcomm : ∀ x ∈ [a, b, c], ∀ y ∈ [a', b', c'], Commute x y) :
    (∀ i j : Fin 3, Commute (L.q i) (L'.q j)) ∧
      ∀ i j : Fin 3, L.q i ≠ L'.q j := by
  obtain ⟨-, -, -, hab3, hac3, -, -⟩ := h
  have ha2 : a * a = 1 := by simpa [zom_Lift.q] using L.q_sq hp 0
  have hb2 : b * b = 1 := by simpa [zom_Lift.q] using L.q_sq hp 1
  have hc2 : c * c = 1 := by simpa [zom_Lift.q] using L.q_sq hp 2
  have hcomm' : ∀ i j : Fin 3, Commute (L.q i) (L'.q j) := by
    intro i j
    have hx : L.q i ∈ [a, b, c] := by fin_cases i <;> simp [zom_Lift.q]
    have hy : L'.q j ∈ [a', b', c'] := by fin_cases j <;> simp [zom_Lift.q]
    exact hcomm _ hx _ hy
  have hA := zom_ne_second_of_commute ha2 hb2 hab3
    (hcomm' 1 0) (hcomm' 1 1) (hcomm' 1 2)
  have hba3 : orderOf (b * a) = 3 := by
    have hsc : SemiconjBy a (b * a) (a * b) := by
      simp only [SemiconjBy]
      rw [mul_assoc]
    rw [SemiconjBy.orderOf_eq a hsc]
    exact hab3
  have hca3 : orderOf (c * a) = 3 := by
    have hsc : SemiconjBy a (c * a) (a * c) := by
      simp only [SemiconjBy]
      rw [mul_assoc]
    rw [SemiconjBy.orderOf_eq a hsc]
    exact hac3
  have hB := zom_ne_second_of_commute hb2 ha2 hba3
    (hcomm' 0 0) (hcomm' 0 1) (hcomm' 0 2)
  have hC := zom_ne_second_of_commute hc2 ha2 hca3
    (hcomm' 0 0) (hcomm' 0 1) (hcomm' 0 2)
  refine ⟨hcomm', ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp [zom_Lift.q]
  · exact hA.1
  · exact hA.2.1
  · exact hA.2.2
  · exact hB.1
  · exact hB.2.1
  · exact hB.2.2
  · exact hC.1
  · exact hC.2.1
  · exact hC.2.2
omit [Module.Finite (ZMod p) U] in
private theorem zom_reflection_smul_inv {u : U} {φ : Dual (ZMod p) U} (hφ : φ u = 2)
    {c : ZMod p} (hc : c ≠ 0) (hφ' : (c • φ) (c⁻¹ • u) = 2) :
    Module.reflection hφ' = Module.reflection hφ := by
  apply LinearEquiv.ext
  intro v
  rw [Module.reflection_apply, Module.reflection_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  field_simp [hc]

omit [Module.Finite (ZMod p) U] in
private theorem zom_normalize (h : zom_RawLift (A := A) a b c) : Nonempty (zom_Lift A a b c) := by
  let x : ZMod p := h.φa h.ub
  let y : ZMod p := h.φb h.uc
  let w : ZMod p := h.φc h.ua
  let c : ZMod p := x * y
  let κ : ZMod p := x * y * w
  have hx0 : x ≠ 0 := h.hx0
  have hy0 : y ≠ 0 := h.hy0
  have hc0 : c ≠ 0 := mul_ne_zero hx0 hy0
  have hφb' : (x • h.φb) (x⁻¹ • h.ub) = 2 := by
    simp only [LinearMap.smul_apply, map_smul, h.hφb, smul_eq_mul]
    field_simp [hx0]
  have hφc' : (c • h.φc) (c⁻¹ • h.uc) = 2 := by
    simp only [LinearMap.smul_apply, map_smul, h.hφc, smul_eq_mul]
    field_simp [hc0]
  have hrB' : (h.rB : U ≃ₗ[ZMod p] U) = Module.reflection hφb' := by
    rw [h.rBeq]
    exact (zom_reflection_smul_inv h.hφb hx0 hφb').symm
  have hrC' : (h.rC : U ≃ₗ[ZMod p] U) = Module.reflection hφc' := by
    rw [h.rCeq]
    exact (zom_reflection_smul_inv h.hφc hc0 hφc').symm
  have hab' : h.φa (x⁻¹ • h.ub) = 1 := by
    rw [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hx0
  have hba' : (x • h.φb) h.ua = 1 := by
    rw [LinearMap.smul_apply, h.hba, smul_eq_mul]
    exact mul_inv_cancel₀ hx0
  have hcdef : c = x * y := rfl
  have hydef : h.φb h.uc = y := rfl
  have hbc' : (x • h.φb) (c⁻¹ • h.uc) = 1 := by
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    rw [hcdef]
    rw [hydef]
    field_simp [hx0, hy0]
  have hcb' : (c • h.φc) (x⁻¹ • h.ub) = 1 := by
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    rw [h.hcb]
    rw [hydef]
    rw [hcdef]
    field_simp [hx0, hy0]
  have hca' : (c • h.φc) h.ua = κ := by
    simp only [LinearMap.smul_apply, smul_eq_mul, κ, c]
    ring
  have hac' : h.φa (c⁻¹ • h.uc) = κ⁻¹ := by
    rw [map_smul, h.hac, smul_eq_mul]
    simp only [κ, c, w]
    field_simp [hc0]
  have hκ : κ ^ 2 - κ + 1 = 0 := by
    simpa [κ, x, y, w] using h.hquad
  exact ⟨h.rA, h.rB, h.rC, h.ua, x⁻¹ • h.ub, c⁻¹ • h.uc, h.φa, x • h.φb, c • h.φc,
    h.hφa, hφb', hφc', h.mka, h.mkb, h.mkc, h.rAeq, hrB', hrC', κ, hab', hba', hbc', hcb',
    hca', hac', hκ⟩

private theorem zom_normalized_lift (hp : p ≠ 2) (hirr : AbsIrred p A)
    (hn3 : 3 ≤ Module.finrank (ZMod p) U) {a b c : ↥A ⧸ Subgroup.center ↥A}
    (h : AffineTriangle (reflImage p A) a b c) : Nonempty (zom_Lift A a b c) := by
  obtain ⟨raw⟩ := exists_lift_of_affineTriangle hp hirr hn3 h
  exact zom_normalize raw

theorem exists_smul_mem_of_affineTriangle_pair (hp : p ≠ 2) (hp3 : p ≠ 3) (hirr : AbsIrred p A)
    (hn : Module.finrank (ZMod p) U = 6) {a b c a' b' c' : ↥A ⧸ Subgroup.center ↥A}
    (h : AffineTriangle (reflImage p A) a b c) (h' : AffineTriangle (reflImage p A) a' b' c')
    (hcomm : ∀ x ∈ [a, b, c], ∀ y ∈ [a', b', c'], Commute x y) :
    ∃ ω : ZMod p, ω ^ 2 + ω + 1 = 0 ∧ ∃ g ∈ A, ∀ v, g v = ω • v := by
  have hn3 : 3 ≤ Module.finrank (ZMod p) U := by omega
  obtain ⟨L⟩ := zom_normalized_lift hp hirr hn3 h
  obtain ⟨L'⟩ := zom_normalized_lift hp hirr hn3 h'
  obtain ⟨hcomm', hne⟩ := zom_cross_conditions hp L L' h hcomm
  have hcross := zom_cross_pairings hp hirr hn3 L L' hcomm' hne
  exact zom_scalar_of_lifts hp3 L L' hcross hn

end CFSG.StandardType.ZS
