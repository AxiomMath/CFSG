module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.C134Res

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def elemCenter (Q : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Q ∧ x ∈ centralizer (Q : Set G) ∧ x ^ 2 = 1}
  one_mem' := ⟨Q.one_mem, Subgroup.one_mem _, one_pow 2⟩
  mul_mem' := by
    rintro x y ⟨hxQ, hxc, hx2⟩ ⟨hyQ, hyc, hy2⟩
    refine ⟨Q.mul_mem hxQ hyQ, Subgroup.mul_mem _ hxc hyc, ?_⟩
    have hxy : Commute x y := (Subgroup.mem_centralizer_iff.1 hxc y hyQ).symm
    rw [hxy.mul_pow, hx2, hy2, one_mul]
  inv_mem' := by
    rintro x ⟨hxQ, hxc, hx2⟩
    exact ⟨Q.inv_mem hxQ, Subgroup.inv_mem _ hxc, by rw [inv_pow, hx2, inv_one]⟩

theorem elemCenter_le (Q : Subgroup G) : elemCenter Q ≤ Q := fun _ hx => hx.1

theorem elemCenter_comm {Q : Subgroup G} {x y : G} (hx : x ∈ elemCenter Q)
    (hy : y ∈ elemCenter Q) : x * y = y * x :=
  (Subgroup.mem_centralizer_iff.1 hx.2.1 y hy.1).symm

theorem conj_mem_centralizer_of_mem_normalizer {H : Subgroup G} {p : G}
    (hp : p ∈ normalizer (H : Set G)) {y : G} (hy : y ∈ centralizer (H : Set G)) :
    p * y * p⁻¹ ∈ centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh' : p⁻¹ * h * p ∈ H := by
    have := (Subgroup.mem_normalizer_iff.1 ((normalizer (H : Set G)).inv_mem hp) h).1 hh
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 hy _ hh'
  calc h * (p * y * p⁻¹) = p * ((p⁻¹ * h * p) * y) * p⁻¹ := by group
    _ = p * (y * (p⁻¹ * h * p)) * p⁻¹ := by rw [h1]
    _ = p * y * p⁻¹ * h := by group

theorem conj_mem_elemCenter {Q : Subgroup G} {g : G} (hg : g ∈ normalizer (Q : Set G)) {x : G}
    (hx : x ∈ elemCenter Q) : g * x * g⁻¹ ∈ elemCenter Q := by
  refine ⟨(Subgroup.mem_normalizer_iff.1 hg x).1 hx.1,
    conj_mem_centralizer_of_mem_normalizer hg hx.2.1, ?_⟩
  have : g * x * g⁻¹ = (MulAut.conj g) x := rfl
  rw [this, ← map_pow, hx.2.2, map_one]

theorem le_normalizer_elemCenter {X Q : Subgroup G} (h : X ≤ normalizer (Q : Set G)) :
    X ≤ normalizer (elemCenter Q : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_elemCenter (h hg) hx, fun hx => ?_⟩
  have := conj_mem_elemCenter (h (X.inv_mem hg)) hx
  simpa [mul_assoc] using this

theorem le_normalizer_commutator_of {A B X : Subgroup G} (hA : X ≤ normalizer (A : Set G))
    (hB : X ≤ normalizer (B : Set G)) : X ≤ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hA' := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hx)
  have hB' := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hx)
  rw [Subgroup.map_commutator, hA', hB']

theorem exists_orderOf_eq_two [Finite G] {X : Subgroup G} (hX : IsPGroup 2 X) (hX1 : X ≠ ⊥) :
    ∃ x ∈ X, orderOf x = 2 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hX1 (Subgroup.card_eq_one.mp (by simpa using hn))
  have h2 : 2 ∣ Nat.card X := by rw [hn]; exact dvd_pow_self 2 hn0
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact ⟨c, c.2, by rw [Subgroup.orderOf_coe]; exact hc⟩

theorem inf_center_ne_bot_of_normalized [Finite G] {T N : Subgroup G} (hT : IsPGroup 2 T)
    (hNT : N ≤ T) (hn : T ≤ normalizer (N : Set G)) (hN : N ≠ ⊥) :
    N ⊓ (T ⊓ centralizer (T : Set G)) ≠ ⊥ := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (N.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hn
  have hne : N.subgroupOf T ≠ ⊥ := by
    intro h
    apply hN
    rw [← Subgroup.map_subgroupOf_eq_of_le hNT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ N ⊓ (T ⊓ centralizer (T : Set G)) := ⟨hy.1, y.2, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem exists_involution_central [Finite G] {T N : Subgroup G} (hT : IsPGroup 2 T) (hNT : N ≤ T)
    (hn : T ≤ normalizer (N : Set G)) (hN : N ≠ ⊥) :
    ∃ x ∈ N, x ≠ 1 ∧ x ^ 2 = 1 ∧ ∀ t ∈ T, t * x = x * t := by
  have hA := inf_center_ne_bot_of_normalized hT hNT hn hN
  have hAp : IsPGroup 2 ↥(N ⊓ (T ⊓ centralizer (T : Set G))) :=
    hT.to_le (inf_le_right.trans inf_le_left)
  obtain ⟨x, hxA, hx2⟩ := exists_orderOf_eq_two hAp hA
  refine ⟨x, hxA.1, ?_, ?_, fun t ht => Subgroup.mem_centralizer_iff.1 hxA.2.2 t ht⟩
  · intro h
    rw [h, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  · rw [← hx2]
    exact pow_orderOf_eq_one x

theorem card_two_centralized {W X : Subgroup G} (hW : Nat.card W = 2)
    (hX : X ≤ normalizer (W : Set G)) {x : G} (hx : x ∈ X) {w : G} (hw : w ∈ W) :
    x * w = w * x := by
  by_cases hw1 : w = 1
  · rw [hw1]; simp
  obtain ⟨a, b, -, hab⟩ := Nat.card_eq_two_iff.1 hW
  have hmem : ∀ v : W, v = a ∨ v = b := fun v => by
    have : v ∈ (Set.univ : Set W) := Set.mem_univ v
    rw [← hab] at this
    simpa using this
  have hc : x * w * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 (hX hx) w).1 hw
  have hc1 : x * w * x⁻¹ ≠ 1 := fun h => hw1 (by simpa using h)
  have key : (⟨x * w * x⁻¹, hc⟩ : W) = ⟨w, hw⟩ := by
    have h1 : (1 : W) ≠ ⟨w, hw⟩ := fun h => hw1 (congrArg Subtype.val h).symm
    have h2 : (1 : W) ≠ ⟨x * w * x⁻¹, hc⟩ := fun h => hc1 (congrArg Subtype.val h).symm
    rcases hmem 1 with e1 | e1 <;> rcases hmem ⟨w, hw⟩ with e2 | e2 <;>
      rcases hmem ⟨x * w * x⁻¹, hc⟩ with e3 | e3 <;> simp_all
  have := congrArg Subtype.val key
  simp only at this
  calc x * w = (x * w * x⁻¹) * x := by group
    _ = w * x := by rw [this]

section Coprime

open scoped IsMulCommutative

theorem comm_inf_centralizer_eq_bot [Finite G] {B K : Subgroup G}
    (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hBK : B ≤ normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card B) (Nat.card K)) :
    ⁅B, K⁆ ⊓ centralizer (B : Set G) = ⊥ := by
  classical
  let _ : Fintype B := Fintype.ofFinite B
  have _ : IsMulCommutative K := ⟨⟨fun x y => Subtype.ext (hK x x.2 y y.2)⟩⟩
  have hconj : ∀ b ∈ B, ∀ k ∈ K, b * k * b⁻¹ ∈ K := fun b hb k hk =>
    (mem_normalizer_iff.mp (hBK hb) k).mp hk
  let f : B → K → K := fun b k => ⟨(b : G) * k * (b : G)⁻¹, hconj b b.2 k k.2⟩
  have hfmul : ∀ b k₁ k₂, f b (k₁ * k₂) = f b k₁ * f b k₂ := fun b k₁ k₂ =>
    Subtype.ext (by simp only [f, Subgroup.coe_mul]; group)
  let σ : K →* K := MonoidHom.mk' (fun k => ∏ b : B, f b k) fun k₁ k₂ => by
    show ∏ b, f b (k₁ * k₂) = (∏ b, f b k₁) * ∏ b, f b k₂
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ => hfmul b k₁ k₂
  have hσ : ∀ k, σ k = ∏ b : B, f b k := fun k => rfl
  have hker : ⁅B, K⁆ ≤ σ.ker.map K.subtype := by
    rw [Subgroup.commutator_le]
    intro b hb k hk
    refine ⟨⟨b * k * b⁻¹, hconj b hb k hk⟩ * ⟨k, hk⟩⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one, hσ, hσ]
      exact Fintype.prod_equiv (Equiv.mulRight (⟨b, hb⟩ : B)) _ _ fun c =>
        Subtype.ext (by simp only [f, Equiv.coe_mulRight, Subgroup.coe_mul, mul_inv_rev]; group)
    · simp [commutatorElement_def]
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxc, hxB⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hk, rfl⟩ := hker hxc
  have hfix : ∀ b : B, f b k = k := fun b => Subtype.ext (by
    have hb : (b : G) * k = k * b := mem_centralizer_iff.mp hxB b b.2
    show (b : G) * k * (b : G)⁻¹ = k
    rw [hb, mul_inv_cancel_right])
  have h1 : k ^ Fintype.card B = 1 := by
    rw [← MonoidHom.mem_ker.mp hk, hσ]
    simp only [hfix, Finset.prod_const, Finset.card_univ]
  have h2 : k ^ Nat.card K = 1 := pow_card_eq_one'
  have h3 := (pow_gcd_eq_one (a := k)).mpr ⟨h1, h2⟩
  rw [← Nat.card_eq_fintype_card, Nat.Coprime.gcd_eq_one hcop, pow_one] at h3
  rw [h3, Subgroup.mem_bot]
  rfl

end Coprime

end CFSG.Quasithin.C134Res
