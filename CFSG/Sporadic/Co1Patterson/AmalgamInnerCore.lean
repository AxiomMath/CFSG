module

public import CFSG.Sporadic.Co1Patterson.AmalgamIso
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.Co1Patterson

open Subgroup

variable {G : Type*} [Group G]

section Four

variable {a w : G}

theorem four_mul_mem (ha : a * a = 1) (hw : w * w = 1) (haw : a * w = w * a) {x y : G}
    (hx : x = 1 ∨ x = a ∨ x = w ∨ x = w * a) (hy : y = 1 ∨ y = a ∨ y = w ∨ y = w * a) :
    x * y = 1 ∨ x * y = a ∨ x * y = w ∨ x * y = w * a := by
  have e1 : a * (w * a) = w := by rw [← mul_assoc, haw, mul_assoc, ha, mul_one]
  have e2 : w * (w * a) = a := by rw [← mul_assoc, hw, one_mul]
  have e3 : w * a * a = w := by rw [mul_assoc, ha, mul_one]
  have e4 : w * a * w = a := by rw [mul_assoc, haw, ← mul_assoc, hw, one_mul]
  have e5 : w * a * (w * a) = 1 := by rw [← mul_assoc, e4, ha]
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp only [one_mul, mul_one, ha, hw, e1, e2, e3, e4, e5, haw, true_or, or_true]

@[expose] def fourGroup (ha : a * a = 1) (hw : w * w = 1) (haw : a * w = w * a) : Subgroup G where
  carrier := {x | x = 1 ∨ x = a ∨ x = w ∨ x = w * a}
  mul_mem' hx hy := four_mul_mem ha hw haw hx hy
  one_mem' := Or.inl rfl
  inv_mem' {x} hx := by
    have hxx : x * x = 1 := by
      rcases hx with rfl | rfl | rfl | rfl
      · exact mul_one 1
      · exact ha
      · exact hw
      · calc w * a * (w * a) = w * (a * w) * a := by group
          _ = w * (w * a) * a := by rw [haw]
          _ = 1 := by rw [← mul_assoc, hw, one_mul, ha]
    rw [inv_eq_of_mul_eq_one_right hxx]
    exact hx

theorem mem_fourGroup (ha : a * a = 1) (hw : w * w = 1) (haw : a * w = w * a) {x : G} :
    x ∈ fourGroup ha hw haw ↔ x = 1 ∨ x = a ∨ x = w ∨ x = w * a := Iff.rfl

end Four

@[expose] def vCent {K V : Subgroup G} (hV : ∀ v ∈ V, ∀ g ∈ K, v * g = g * v) (r : G) :
    Subgroup G where
  carrier := {s | s ∈ K ∧ r * s * r⁻¹ * s⁻¹ ∈ V}
  mul_mem' {s t} hs ht := by
    refine ⟨K.mul_mem hs.1 ht.1, ?_⟩
    have e : r * (s * t) * r⁻¹ * (s * t)⁻¹ =
        (r * s * r⁻¹ * s⁻¹) * (s * (r * t * r⁻¹ * t⁻¹) * s⁻¹) := by group
    have hc : s * (r * t * r⁻¹ * t⁻¹) * s⁻¹ = r * t * r⁻¹ * t⁻¹ := by
      rw [← hV _ ht.2 s hs.1, mul_inv_cancel_right]
    rw [e, hc]
    exact V.mul_mem hs.2 ht.2
  one_mem' := ⟨K.one_mem, by rw [mul_one, mul_inv_cancel, inv_one, mul_one]; exact V.one_mem⟩
  inv_mem' {s} hs := by
    refine ⟨K.inv_mem hs.1, ?_⟩
    have e : r * s⁻¹ * r⁻¹ * s⁻¹⁻¹ = s⁻¹ * (r * s * r⁻¹ * s⁻¹)⁻¹ * s⁻¹⁻¹ := by group
    have hc : s⁻¹ * (r * s * r⁻¹ * s⁻¹)⁻¹ * s⁻¹⁻¹ = (r * s * r⁻¹ * s⁻¹)⁻¹ := by
      rw [← hV _ (V.inv_mem hs.2) s⁻¹ (K.inv_mem hs.1), mul_inv_cancel_right]
    rw [e, hc]
    exact V.inv_mem hs.2

structure CoreData (K R V : Subgroup G) : Prop where
  le_K : R ≤ K
  le_R : V ≤ R
  central : ∀ v ∈ V, ∀ g ∈ K, v * g = g * v
  mul_self : ∀ v ∈ V, v * v = 1
  conj_mem : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R
  comm_mem : ∀ r ∈ R, ∀ s ∈ R, r * s * r⁻¹ * s⁻¹ ∈ V
  mem_of_comm : ∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ∈ V

namespace CoreData

variable {K R V : Subgroup G}

theorem mem_K {hD : CoreData K R V} {v : G} (hv : v ∈ V) : v ∈ K := hD.le_K (hD.le_R hv)

theorem conj_eq (hD : CoreData K R V) {v g : G} (hv : v ∈ V) (hg : g ∈ K) :
    g * v * g⁻¹ = v := by
  rw [← hD.central v hv g hg, mul_inv_cancel_right]

theorem eq_of_conj_mem (hD : CoreData K R V) {y c : G} (hc : c ∈ K) (h : c * y * c⁻¹ ∈ V) :
    y = c * y * c⁻¹ := by
  have e := hD.conj_eq h (inv_mem hc)
  rw [inv_inv] at e
  calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
    _ = c * y * c⁻¹ := e

variable {f : G → G}

@[expose] def fixSub (hD : CoreData K R V) (hf : IsoOn f K K) : Subgroup G where
  carrier := {r | r ∈ R ∧ f r * r⁻¹ ∈ V}
  mul_mem' {r s} hr hs := by
    refine ⟨R.mul_mem hr.1 hs.1, ?_⟩
    have hc := hD.central _ hs.2 (f r) (hf.map_mem r (hD.le_K hr.1))
    have e : f (r * s) * (r * s)⁻¹ = (f s * s⁻¹) * (f r * r⁻¹) := by
      rw [hf.map_mul r (hD.le_K hr.1) s (hD.le_K hs.1), mul_inv_rev]
      calc f r * f s * (s⁻¹ * r⁻¹) = f r * (f s * s⁻¹) * r⁻¹ := by group
        _ = (f s * s⁻¹) * f r * r⁻¹ := by rw [← hc]
        _ = (f s * s⁻¹) * (f r * r⁻¹) := by group
    rw [e]
    exact V.mul_mem hs.2 hr.2
  one_mem' := ⟨R.one_mem, by rw [hf.map_one, inv_one, mul_one]; exact V.one_mem⟩
  inv_mem' {r} hr := by
    refine ⟨R.inv_mem hr.1, ?_⟩
    have e : f r⁻¹ * r⁻¹⁻¹ = r⁻¹ * (f r * r⁻¹)⁻¹ * r⁻¹⁻¹ := by
      rw [hf.map_inv (hD.le_K hr.1)]
      group
    rw [e, hD.conj_eq (V.inv_mem hr.2) (inv_mem (hD.le_K hr.1))]
    exact V.inv_mem hr.2

theorem conj_mem_fixSub (hD : CoreData K R V) (hf : IsoOn f K K)
    (hfR : ∀ g ∈ K, f g * g⁻¹ ∈ R) {k r : G} (hk : k ∈ K) (hr : r ∈ hD.fixSub hf) :
    k * r * k⁻¹ ∈ hD.fixSub hf := by
  obtain ⟨hrR, hu⟩ := hr
  have hrK := hD.le_K hrR
  have hρ := hfR k hk
  have hs : k * r * k⁻¹ ∈ R := hD.conj_mem k hk r hrR
  refine ⟨hs, ?_⟩
  have hfk : f k = (f k * k⁻¹) * k := by group
  have hfr : f r = (f r * r⁻¹) * r := by group
  have e : f (k * r * k⁻¹) * (k * r * k⁻¹)⁻¹ =
      (f k * k⁻¹) * (k * (f r * r⁻¹) * k⁻¹) * (k * r * k⁻¹) * (f k * k⁻¹)⁻¹ *
        (k * r * k⁻¹)⁻¹ := by
    rw [hf.map_conj hk hrK]
    conv_lhs => rw [hfk, hfr]
    group
  rw [e, hD.conj_eq hu hk, ← hD.central _ hu _ (hD.le_K hρ)]
  have e2 : f r * r⁻¹ * (f k * k⁻¹) * (k * r * k⁻¹) * (f k * k⁻¹)⁻¹ * (k * r * k⁻¹)⁻¹ =
      (f r * r⁻¹) * ((f k * k⁻¹) * (k * r * k⁻¹) * (f k * k⁻¹)⁻¹ * (k * r * k⁻¹)⁻¹) := by
    group
  rw [e2]
  exact V.mul_mem hu (hD.comm_mem _ hρ _ hs)

theorem mem_fixSub_of_stab (hD : CoreData K R V) (hf : IsoOn f K K)
    (hfV : ∀ v ∈ V, f v = v) (hfR : ∀ g ∈ K, f g * g⁻¹ ∈ R) {r₀ : G} (hr₀ : r₀ ∈ R)
    (hsq : r₀ * r₀ ∈ V) {Γ : Set G} (hΓ : Γ ⊆ K) (hfix : ∀ g ∈ Γ, g * r₀ * g⁻¹ * r₀⁻¹ ∈ V)
    (huniq : ∀ r ∈ R, (∀ g ∈ Γ, g * r * g⁻¹ * r⁻¹ ∈ V) → r * r = r₀ * r₀ → r * r₀⁻¹ ∈ V) :
    r₀ ∈ hD.fixSub hf := by
  have hr₀K := hD.le_K hr₀
  have hr' : f r₀ ∈ R := by
    have e : f r₀ = (f r₀ * r₀⁻¹) * r₀ := by group
    rw [e]
    exact R.mul_mem (hfR r₀ hr₀K) hr₀
  refine ⟨hr₀, huniq _ hr' (fun g hg => ?_) ?_⟩
  · have hgK := hΓ hg
    have hv := hfix g hg
    have hρ := hfR g hgK
    have hρK := hD.le_K hρ
    have e1 : g * r₀ * g⁻¹ = (g * r₀ * g⁻¹ * r₀⁻¹) * r₀ := by group
    have h1 := hf.map_conj hgK hr₀K
    rw [e1, hf.map_mul _ (hD.mem_K hv) _ hr₀K, hfV _ hv] at h1
    have hfg : f g = (f g * g⁻¹) * g := by group
    rw [hfg] at h1
    have e2 : g * f r₀ * g⁻¹ * (f r₀)⁻¹ = (f g * g⁻¹)⁻¹ *
        ((f g * g⁻¹) * g * f r₀ * ((f g * g⁻¹) * g)⁻¹) * (f g * g⁻¹) * (f r₀)⁻¹ := by group
    rw [e2, ← h1]
    have e3 : (f g * g⁻¹)⁻¹ * ((g * r₀ * g⁻¹ * r₀⁻¹) * f r₀) * (f g * g⁻¹) * (f r₀)⁻¹ =
        (f g * g⁻¹)⁻¹ * (g * r₀ * g⁻¹ * r₀⁻¹) * f r₀ * (f g * g⁻¹) * (f r₀)⁻¹ := by group
    rw [e3, ← hD.central _ hv _ (inv_mem hρK)]
    have e4 : g * r₀ * g⁻¹ * r₀⁻¹ * (f g * g⁻¹)⁻¹ * f r₀ * (f g * g⁻¹) * (f r₀)⁻¹ =
        (g * r₀ * g⁻¹ * r₀⁻¹) * ((f g * g⁻¹)⁻¹ * f r₀ * (f g * g⁻¹)⁻¹⁻¹ * (f r₀)⁻¹) := by group
    rw [e4]
    exact V.mul_mem hv (hD.comm_mem _ (R.inv_mem hρ) _ hr')
  · rw [← hf.map_mul _ hr₀K _ hr₀K, hfV _ hsq]

theorem fix_mod (hD : CoreData K R V) (hf : IsoOn f K K) (hfV : ∀ v ∈ V, f v = v)
    (hfR : ∀ g ∈ K, f g * g⁻¹ ∈ R) {S : Set G} (hSR : S ⊆ R) (hSV : ∀ r₀ ∈ S, r₀ * r₀ ∈ V)
    (hstab : ∀ r₀ ∈ S, ∃ Γ : Set G, Γ ⊆ K ∧ (∀ g ∈ Γ, g * r₀ * g⁻¹ * r₀⁻¹ ∈ V) ∧
      ∀ r ∈ R, (∀ g ∈ Γ, g * r * g⁻¹ * r⁻¹ ∈ V) → r * r = r₀ * r₀ → r * r₀⁻¹ ∈ V)
    (hgen : ∀ F : Subgroup G, V ≤ F → S ⊆ F →
      (∀ k ∈ K, ∀ r ∈ F, r ∈ R → k * r * k⁻¹ ∈ F) → R ≤ F) :
    ∀ r ∈ R, f r * r⁻¹ ∈ V := by
  have hle := hgen (hD.fixSub hf)
    (fun v hv => ⟨hD.le_R hv, by rw [hfV v hv, mul_inv_cancel]; exact V.one_mem⟩)
    (fun r₀ hr₀ => by
      obtain ⟨Γ, hΓ, hfix, huniq⟩ := hstab r₀ hr₀
      exact hD.mem_fixSub_of_stab hf hfV hfR (hSR hr₀) (hSV r₀ hr₀) hΓ hfix huniq)
    (fun k hk r hr _ => hD.conj_mem_fixSub hf hfR hk hr)
  exact fun r hr => (hle hr).2

theorem exists_mod_eq [Finite G] (hD : CoreData K R V) {x : G} (hx : x ∈ K)
    (hfpf : ∀ t ∈ R, t * x * t⁻¹ * x⁻¹ ∈ V → t ∈ V) :
    ∀ ρ ∈ R, ∃ s ∈ R, (s * x * s⁻¹ * x⁻¹)⁻¹ * ρ ∈ V := by
  intro ρ hρ
  let N : Subgroup R := V.subgroupOf R
  have hmem : ∀ s : R, (s : G) * x * (s : G)⁻¹ * x⁻¹ ∈ R := fun s => by
    have e : (s : G) * x * (s : G)⁻¹ * x⁻¹ = (s : G) * (x * (s : G)⁻¹ * x⁻¹) := by group
    rw [e]
    exact R.mul_mem s.2 (hD.conj_mem x hx _ (R.inv_mem s.2))
  let φ : R → R := fun s => ⟨(s : G) * x * (s : G)⁻¹ * x⁻¹, hmem s⟩
  have hφ : ∀ a b : R, (a : G)⁻¹ * b ∈ V → φ a = φ b := by
    intro a b hab
    apply Subtype.ext
    have hb : (b : G) = a * ((a : G)⁻¹ * b) := by group
    show (a : G) * x * (a : G)⁻¹ * x⁻¹ = (b : G) * x * (b : G)⁻¹ * x⁻¹
    rw [hb]
    calc (a : G) * x * (a : G)⁻¹ * x⁻¹ =
        a * (((a : G)⁻¹ * b) * x) * ((a : G)⁻¹ * b)⁻¹ * (a : G)⁻¹ * x⁻¹ := by
          rw [hD.central _ hab x hx]
          group
      _ = (a * ((a : G)⁻¹ * b)) * x * (a * ((a : G)⁻¹ * b))⁻¹ * x⁻¹ := by group
  let Φ : R ⧸ N → R ⧸ N := Quotient.map' φ (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [hφ a b ((mem_subgroupOf).1 hab), inv_mul_cancel]
    exact N.one_mem)
  have hΦ : ∀ s : R, Φ (QuotientGroup.mk s) = QuotientGroup.mk (φ s) := fun _ => rfl
  have hinj : Function.Injective Φ := by
    intro p q hpq
    induction p using QuotientGroup.induction_on with | H a => ?_
    induction q using QuotientGroup.induction_on with | H b => ?_
    rw [hΦ, hΦ, QuotientGroup.eq, mem_subgroupOf] at hpq
    rw [QuotientGroup.eq, mem_subgroupOf]
    have hc : x * (a : G) ∈ K := K.mul_mem hx (hD.le_K a.2)
    set t : G := (a : G)⁻¹ * b with ht
    have htR : t ∈ R := R.mul_mem (R.inv_mem a.2) b.2
    have hb : (b : G) = a * t := by rw [ht]; group
    have e : ((φ a : R) : G)⁻¹ * (φ b : R) =
        (x * (a : G)) * (x⁻¹ * t * x * t⁻¹) * (x * (a : G))⁻¹ := by
      show ((a : G) * x * (a : G)⁻¹ * x⁻¹)⁻¹ * ((b : G) * x * (b : G)⁻¹ * x⁻¹) = _
      rw [hb]
      group
    have push : (x⁻¹ * t * x * t⁻¹ : G) ∈ V := by
      have h1 : (x⁻¹ * t * x * t⁻¹ : G) = (x * (a : G)) * (x⁻¹ * t * x * t⁻¹) * (x * (a : G))⁻¹ :=
        hD.eq_of_conj_mem hc (by rw [← e]; exact hpq)
      rw [h1, ← e]
      exact hpq
    have h2 : t * x * t⁻¹ * x⁻¹ = x * (x⁻¹ * t * x * t⁻¹) * x⁻¹ := by group
    have h3 : t * x * t⁻¹ * x⁻¹ ∈ V := by
      rw [h2, hD.conj_eq push hx]
      exact push
    exact hfpf t htR h3
  have hsurj := Finite.surjective_of_injective hinj
  obtain ⟨p, hp⟩ := hsurj (QuotientGroup.mk ⟨ρ, hρ⟩)
  induction p using QuotientGroup.induction_on with | H s => ?_
  rw [hΦ, QuotientGroup.eq, mem_subgroupOf] at hp
  exact ⟨s, s.2, hp⟩

theorem exists_conj_fix [Finite G] (hD : CoreData K R V) (hf : IsoOn f K K)
    (hfR : ∀ g ∈ K, f g * g⁻¹ ∈ R) {x : G} (hx : x ∈ K) {n : ℕ} (hn : Odd n)
    (hxn : x ^ n = 1) (hfpf : ∀ t ∈ R, t * x * t⁻¹ * x⁻¹ ∈ V → t ∈ V) :
    ∃ s ∈ R, f x = s * x * s⁻¹ := by
  obtain ⟨s, hs, hv⟩ := hD.exists_mod_eq hx hfpf _ (hfR x hx)
  refine ⟨s, hs, ?_⟩
  set v : G := (s * x * s⁻¹ * x⁻¹)⁻¹ * (f x * x⁻¹) with hvdef
  have hsx : s * x * s⁻¹ ∈ K := K.mul_mem (K.mul_mem (hD.le_K hs) hx) (inv_mem (hD.le_K hs))
  have hfx : f x = s * x * s⁻¹ * v := by
    have e : f x = (s * x * s⁻¹ * x⁻¹) * v * x := by rw [hvdef]; group
    rw [e, mul_assoc _ v x, hD.central v hv x hx]
    group
  have hpow : (s * x * s⁻¹ * v) ^ n = (s * x * s⁻¹) ^ n * v ^ n :=
    (Commute.mul_pow (hD.central v hv _ hsx).symm n)
  have hconj : (s * x * s⁻¹) ^ n = s * x ^ n * s⁻¹ := conj_pow
  have h1 : f (x ^ n) = (f x) ^ n := hf.map_pow hx n
  rw [hxn, hf.map_one, hfx, hpow, hconj, hxn, mul_one, mul_inv_cancel, one_mul] at h1
  obtain ⟨k, rfl⟩ := hn
  have hv2 := hD.mul_self v hv
  have hvk : v ^ (2 * k + 1) = v := by
    rw [pow_succ, pow_mul, sq, hv2, one_pow, one_mul]
  rw [hvk] at h1
  rw [hfx, ← h1, mul_one]

theorem fix_R [Finite G] (hD : CoreData K R V) (hf : IsoOn f K K) (hfV : ∀ v ∈ V, f v = v)
    {x : G} (hx : x ∈ K) (hfx : f x = x) (hfpf : ∀ t ∈ R, t * x * t⁻¹ * x⁻¹ ∈ V → t ∈ V)
    (hmod : ∀ r ∈ R, f r * r⁻¹ ∈ V) : ∀ r ∈ R, f r = r := by
  have hu_mul : ∀ r ∈ R, ∀ s ∈ R,
      f (r * s) * (r * s)⁻¹ = (f s * s⁻¹) * (f r * r⁻¹) := by
    intro r hr s hs
    have hc := hD.central _ (hmod s hs) (f r) (hf.map_mem r (hD.le_K hr))
    rw [hf.map_mul r (hD.le_K hr) s (hD.le_K hs), mul_inv_rev]
    calc f r * f s * (s⁻¹ * r⁻¹) = f r * (f s * s⁻¹) * r⁻¹ := by group
      _ = (f s * s⁻¹) * f r * r⁻¹ := by rw [← hc]
      _ = (f s * s⁻¹) * (f r * r⁻¹) := by group
  have hu_conj : ∀ r ∈ R, f (x * r * x⁻¹) * (x * r * x⁻¹)⁻¹ = f r * r⁻¹ := by
    intro r hr
    rw [hf.map_conj hx (hD.le_K hr), hfx]
    have e : x * f r * x⁻¹ * (x * r * x⁻¹)⁻¹ = x * (f r * r⁻¹) * x⁻¹ := by group
    rw [e, hD.conj_eq (hmod r hr) hx]
  have hu_inv : ∀ r ∈ R, f r⁻¹ * r⁻¹⁻¹ = (f r * r⁻¹)⁻¹ := by
    intro r hr
    have h := hu_mul r⁻¹ (R.inv_mem hr) r hr
    rw [inv_mul_cancel, hf.map_one, inv_one, mul_one] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hcomm : ∀ t ∈ R, f (t * x * t⁻¹ * x⁻¹) * (t * x * t⁻¹ * x⁻¹)⁻¹ = 1 := by
    intro t ht
    have htx : x * t⁻¹ * x⁻¹ ∈ R := hD.conj_mem x hx _ (R.inv_mem ht)
    have e : t * x * t⁻¹ * x⁻¹ = t * (x * t⁻¹ * x⁻¹) := by group
    rw [e, hu_mul t ht _ htx, hu_conj _ (R.inv_mem ht), hu_inv t ht, inv_mul_cancel]
  intro r hr
  obtain ⟨s, hs, hv⟩ := hD.exists_mod_eq hx hfpf r hr
  have hsx : s * x * s⁻¹ * x⁻¹ ∈ R := by
    have e : s * x * s⁻¹ * x⁻¹ = s * (x * s⁻¹ * x⁻¹) := by group
    rw [e]
    exact R.mul_mem hs (hD.conj_mem x hx _ (R.inv_mem hs))
  have e : r = (s * x * s⁻¹ * x⁻¹) * ((s * x * s⁻¹ * x⁻¹)⁻¹ * r) := by group
  have hr' := hu_mul _ hsx _ (hD.le_R hv)
  rw [← e, hcomm s hs, mul_one, hfV _ hv, mul_inv_cancel] at hr'
  exact mul_inv_eq_one.1 hr'

theorem fix_K (hD : CoreData K R V) (hf : IsoOn f K K) (hfR' : ∀ r ∈ R, f r = r)
    (hfR : ∀ g ∈ K, f g * g⁻¹ ∈ R) {x₁ x₂ : G} (hx₁ : x₁ ∈ K) (hfx₁ : f x₁ = x₁)
    (hx₂ : x₂ ∈ K) {m : ℕ} (hm : Odd m) (hx₂m : x₂ ^ m ∈ R)
    (hgen : ∀ D : Subgroup G, D ≤ K → R ≤ D → x₁ ∈ D → x₂ ∈ D → K ≤ D) :
    ∀ g ∈ K, f g = g := by
  have hd : ∀ g ∈ K, g⁻¹ * f g ∈ V := by
    intro g hg
    have hdR : g⁻¹ * f g ∈ R := by
      have e : g⁻¹ * f g = g⁻¹ * (f g * g⁻¹) * g⁻¹⁻¹ := by group
      rw [e]
      exact hD.conj_mem _ (inv_mem hg) _ (hfR g hg)
    refine hD.mem_of_comm _ hdR fun r hr => ?_
    have hgr : g * r * g⁻¹ ∈ R := hD.conj_mem g hg r hr
    have h1 := hf.map_conj hg (hD.le_K hr)
    rw [hfR' _ hgr, hfR' r hr] at h1
    have e : g⁻¹ * f g * r = (g⁻¹ * (f g * r * (f g)⁻¹) * g) * (g⁻¹ * f g) := by group
    rw [e, ← h1]
    group
  let D : Subgroup G :=
    { carrier := {g | g ∈ K ∧ f g = g}
      mul_mem' := fun {g h} hg hh => ⟨K.mul_mem hg.1 hh.1, by
        rw [hf.map_mul g hg.1 h hh.1, hg.2, hh.2]⟩
      one_mem' := ⟨K.one_mem, hf.map_one⟩
      inv_mem' := fun {g} hg => ⟨K.inv_mem hg.1, by rw [hf.map_inv hg.1, hg.2]⟩ }
  have hx₂D : f x₂ = x₂ := by
    have hdv := hd x₂ hx₂
    have hfx : f x₂ = x₂ * (x₂⁻¹ * f x₂) := by group
    have hpow := hf.map_pow hx₂ m
    rw [hfR' _ hx₂m, hfx, Commute.mul_pow (hD.central _ hdv _ hx₂).symm m] at hpow
    have h1 : (x₂⁻¹ * f x₂) ^ m = 1 := by
      have := congrArg (fun y => (x₂ ^ m)⁻¹ * y) hpow
      simpa using this.symm
    obtain ⟨k, rfl⟩ := hm
    have hv2 := hD.mul_self _ hdv
    rw [pow_succ, pow_mul, sq, hv2, one_pow, one_mul] at h1
    rw [hfx, h1, mul_one]
  have hle := hgen D (fun g hg => hg.1) (fun r hr => ⟨hD.le_K hr, hfR' r hr⟩) ⟨hx₁, hfx₁⟩
    ⟨hx₂, hx₂D⟩
  exact fun g hg => (hle hg).2

theorem exists_conj [Finite G] (hD : CoreData K R V) (hf : IsoOn f K K)
    (hfV : ∀ v ∈ V, f v = v) (hfR : ∀ g ∈ K, f g * g⁻¹ ∈ R)
    {S : Set G} (hSR : S ⊆ R) (hSV : ∀ r₀ ∈ S, r₀ * r₀ ∈ V)
    (hstab : ∀ r₀ ∈ S, ∃ Γ : Set G, Γ ⊆ K ∧ (∀ g ∈ Γ, g * r₀ * g⁻¹ * r₀⁻¹ ∈ V) ∧
      ∀ r ∈ R, (∀ g ∈ Γ, g * r * g⁻¹ * r⁻¹ ∈ V) → r * r = r₀ * r₀ → r * r₀⁻¹ ∈ V)
    (hgenR : ∀ F : Subgroup G, V ≤ F → S ⊆ F →
      (∀ k ∈ K, ∀ r ∈ F, r ∈ R → k * r * k⁻¹ ∈ F) → R ≤ F)
    {x₁ x₂ : G} (hx₁ : x₁ ∈ K) {n : ℕ} (hn : Odd n) (hx₁n : x₁ ^ n = 1)
    (hfpf : ∀ t ∈ R, t * x₁ * t⁻¹ * x₁⁻¹ ∈ V → t ∈ V)
    (hx₂ : x₂ ∈ K) {m : ℕ} (hm : Odd m) (hx₂m : x₂ ^ m ∈ R)
    (hgenK : ∀ D : Subgroup G, D ≤ K → R ≤ D → x₁ ∈ D → x₂ ∈ D → K ≤ D) :
    ∃ s ∈ R, ∀ g ∈ K, f g = s * g * s⁻¹ := by
  have hmod := hD.fix_mod hf hfV hfR hSR hSV hstab hgenR
  obtain ⟨s, hs, hfx⟩ := hD.exists_conj_fix hf hfR hx₁ hn hx₁n hfpf
  have hsK := hD.le_K hs
  have hc : ∀ y, y ∈ K ↔ s⁻¹ * y * s⁻¹⁻¹ ∈ K := fun y =>
    ⟨fun hy => K.mul_mem (K.mul_mem (inv_mem hsK) hy) (inv_mem (inv_mem hsK)), fun hy => by
      have e : y = s * (s⁻¹ * y * s⁻¹⁻¹) * s⁻¹ := by group
      rw [e]
      exact K.mul_mem (K.mul_mem hsK hy) (inv_mem hsK)⟩
  have hf' : IsoOn (fun y => s⁻¹ * f y * s⁻¹⁻¹) K K := hf.comp (isoOn_conj s⁻¹ hc)
  have hf'V : ∀ v ∈ V, s⁻¹ * f v * s⁻¹⁻¹ = v := fun v hv => by
    rw [hfV v hv]
    exact hD.conj_eq hv (inv_mem hsK)
  have hf'R : ∀ g ∈ K, s⁻¹ * f g * s⁻¹⁻¹ * g⁻¹ ∈ R := fun g hg => by
    have e : s⁻¹ * f g * s⁻¹⁻¹ * g⁻¹ = s⁻¹ * (f g * g⁻¹) * (g * s * g⁻¹) := by group
    rw [e]
    exact R.mul_mem (R.mul_mem (R.inv_mem hs) (hfR g hg)) (hD.conj_mem g hg s hs)
  have hf'mod : ∀ r ∈ R, s⁻¹ * f r * s⁻¹⁻¹ * r⁻¹ ∈ V := fun r hr => by
    have hu := hmod r hr
    have e : s⁻¹ * f r * s⁻¹⁻¹ * r⁻¹ =
        (s⁻¹ * (f r * r⁻¹) * s⁻¹⁻¹) * (s⁻¹ * r * s⁻¹⁻¹ * r⁻¹) := by group
    rw [e, hD.conj_eq hu (inv_mem hsK)]
    exact V.mul_mem hu (hD.comm_mem _ (R.inv_mem hs) r hr)
  have hf'x : s⁻¹ * f x₁ * s⁻¹⁻¹ = x₁ := by
    rw [hfx]
    group
  have hf'R' := hD.fix_R hf' hf'V hx₁ hf'x hfpf hf'mod
  have hf'K := hD.fix_K hf' hf'R' hf'R hx₁ hf'x hx₂ hm hx₂m hgenK
  refine ⟨s, hs, fun g hg => ?_⟩
  have h : s⁻¹ * f g * s⁻¹⁻¹ = g := hf'K g hg
  calc f g = s * (s⁻¹ * f g * s⁻¹⁻¹) * s⁻¹ := by group
    _ = s * g * s⁻¹ := by rw [h]

end CoreData

end CFSG.Sporadic.Co1Patterson
