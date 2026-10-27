module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Loc
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph Equiv

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem exists_affine_smul {a : V} (ha : pval Γ a = 5) {x : G}
    (hx : x ∈ MulAction.stabilizer G a) {β : Fin 5 → V} (hadj : ∀ i, Γ.Adj a (β i))
    (hinj : Function.Injective β) (hxβ : ∀ i, x • β i = β (i + 1)) {g : G}
    (hg : g ∈ MulAction.stabilizer G a) :
    ∃ u c : Fin 5, u ≠ 0 ∧ ∀ i, g • β i = β (u * i + c) := by
  open Fin.CommRing Fin.NatCast in
  classical
  have hfin := F.finite_neighborSet a
  let nb : Fin 5 → Γ.neighborSet a := fun i => ⟨β i, hadj i⟩
  have hnb_inj : Function.Injective nb := fun i j h => hinj (congrArg Subtype.val h)
  have hcard : Nat.card (Γ.neighborSet a) = 5 := ha
  have hbij : Function.Bijective nb :=
    hnb_inj.bijective_of_nat_card_le (by rw [hcard]; simp)
  let ι := F.localHom a
  let X : MulAction.stabilizer G a := ⟨x, hx⟩
  let Y : MulAction.stabilizer G a := ⟨g, hg⟩
  have hσ : ∀ i, ι X (nb i) = nb (i + 1) := fun i => Subtype.ext (hxβ i)
  have hσpow : ∀ (n : ℕ) (i : Fin 5), ((ι X) ^ n) (nb i) = nb (i + (n : Fin 5)) := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
      intro i
      rw [pow_succ, Perm.mul_apply, hσ, ih]
      congr 1
      push_cast
      ring
  have hσ5 : (ι X) ^ 5 = 1 := by
    ext w
    obtain ⟨i, rfl⟩ := hbij.2 w
    rw [hσpow]
    simp
  have hσne : ι X ≠ 1 := by
    intro h
    have h1 := hσ 0
    rw [h] at h1
    have h2 : (0 : Fin 5) = 0 + 1 := hnb_inj h1
    exact absurd h2 (by decide)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf (ι X) = pval Γ a := by
    rw [ha]
    exact orderOf_eq_prime hσ5 hσne
  obtain ⟨i, hi⟩ := FrobPrime.conj_pow_of_frobenius (F.valence_isPrime a) rfl ι.range
    (F.localHom_frobenius a) (MonoidHom.mem_range.2 ⟨X, rfl⟩) hord (ι Y)
    (MonoidHom.mem_range.2 ⟨Y, rfl⟩)
  obtain ⟨c, hc⟩ := hbij.2 (ι Y (nb 0))
  refine ⟨(i : Fin 5), c, ?_, ?_⟩
  · intro h0
    have h5 : 5 ∣ i := (Fin.natCast_eq_zero).1 h0
    obtain ⟨m, rfl⟩ := h5
    rw [pow_mul, hσ5, one_pow] at hi
    apply hσne
    have h3 := congrArg (fun q => (ι Y)⁻¹ * q * ι Y) hi
    simpa [mul_assoc] using h3
  · intro j
    have hnj : nb j = ((ι X) ^ (j : ℕ)) (nb 0) := by
      rw [hσpow]
      simp
    have hconj : ι Y * (ι X) ^ (j : ℕ) * (ι Y)⁻¹ = (ι X) ^ (i * (j : ℕ)) := by
      rw [← conj_pow, hi, ← pow_mul]
    have h1 : ι Y * (ι X) ^ (j : ℕ) = (ι X) ^ (i * (j : ℕ)) * ι Y := by
      rw [← hconj]
      group
    have h2 : ι Y (nb j) = nb (c + ((i * (j : ℕ) : ℕ) : Fin 5)) := by
      rw [hnj, ← Perm.mul_apply, h1, Perm.mul_apply, ← hc, hσpow]
    have h3 := congrArg Subtype.val h2
    rw [F.localHom_apply_coe] at h3
    show g • β j = _
    rw [h3]
    show β (c + ((i * (j : ℕ) : ℕ) : Fin 5)) = β ((i : Fin 5) * j + c)
    congr 1
    rw [Nat.cast_mul, Fin.cast_val_eq_self, add_comm]

theorem exists_eq_of_adj_val5 {a : V} (ha : pval Γ a = 5) {β : Fin 5 → V}
    (hadj : ∀ i, Γ.Adj a (β i)) (hinj : Function.Injective β) {w : V} (hw : Γ.Adj a w) :
    ∃ i, β i = w := by
  have hfin := F.finite_neighborSet a
  let nb : Fin 5 → Γ.neighborSet a := fun i => ⟨β i, hadj i⟩
  have hnb_inj : Function.Injective nb := fun i j h => hinj (congrArg Subtype.val h)
  have hcard : Nat.card (Γ.neighborSet a) = 5 := ha
  have hbij : Function.Bijective nb :=
    hnb_inj.bijective_of_nat_card_le (by rw [hcard]; simp)
  obtain ⟨i, hi⟩ := hbij.2 ⟨w, hw⟩
  exact ⟨i, congrArg Subtype.val hi⟩

theorem affine_mem_gcirc_iff {a : V} (ha : pval Γ a = 5) {β : Fin 5 → V}
    (hadj : ∀ i, Γ.Adj a (β i)) (hinj : Function.Injective β) {g : G} {u c : Fin 5} (j : Fin 5)
    (hg : g ∈ MulAction.stabilizer G a) (hgβ : ∀ i, g • β i = β (u * i + c))
    (hj : g • β j = β j) : g ∈ Gcirc Γ G a (β j) ↔ u * u = 1 := by
  open Fin.CommRing in
  have hfix : u * j + c = j := hinj ((hgβ j).symm.trans hj)
  have hgg : ∀ i, (g * g) • β i = β (u * (u * i + c) + c) := by
    intro i
    rw [mul_smul, hgβ, hgβ]
  constructor
  · rintro ⟨-, hK⟩
    have h0 : u * (u * 0 + c) + c = 0 := hinj ((hgg 0).symm.trans (mem_nbrStab.1 hK _ (hadj 0)))
    have h1 : u * (u * 1 + c) + c = 1 := hinj ((hgg 1).symm.trans (mem_nbrStab.1 hK _ (hadj 1)))
    linear_combination h1 - h0
  · intro hu
    refine ⟨⟨hg, MulAction.mem_stabilizer_iff.2 hj⟩, mem_nbrStab.2 fun w hw => ?_⟩
    obtain ⟨i, rfl⟩ := F.exists_eq_of_adj_val5 ha hadj hinj hw
    rw [hgg]
    congr 1
    have hc : c = j - u * j := by linear_combination hfix
    rw [hc]
    linear_combination (i - j) * hu

theorem smul_eq_two_mul_sub {a : V} (ha : pval Γ a = 5) {x : G}
    (hx : x ∈ MulAction.stabilizer G a) {β : Fin 5 → V} (hadj : ∀ i, Γ.Adj a (β i))
    (hinj : Function.Injective β) (hxβ : ∀ i, x • β i = β (i + 1)) {g : G} {m : Fin 5}
    (hg : g ∈ MulAction.stabilizer G a) (hgm : g • β m = β m) (hg2 : g * g = 1)
    (hgK : g ∉ nbrStab Γ G a) : ∀ k, g • β k = β (2 * m - k) := by
  open Fin.CommRing in
  obtain ⟨u, c, -, hgβ⟩ := F.exists_affine_smul ha hx hadj hinj hxβ hg
  have hfix : u * m + c = m := hinj ((hgβ m).symm.trans hgm)
  have hu : u * u = 1 := (F.affine_mem_gcirc_iff ha hadj hinj m hg hgβ hgm).1
    (mem_gcirc_of_sq_eq_one ⟨hg, MulAction.mem_stabilizer_iff.2 hgm⟩ hg2)
  have key : ∀ w : Fin 5, w * w = 1 → w = 1 ∨ w = -1 := by decide
  rcases key u hu with rfl | rfl
  · exfalso
    apply hgK
    refine mem_nbrStab.2 fun w hw => ?_
    obtain ⟨i, rfl⟩ := F.exists_eq_of_adj_val5 ha hadj hinj hw
    rw [hgβ]
    congr 1
    linear_combination hfix
  · intro k
    rw [hgβ]
    congr 1
    linear_combination hfix

theorem not_exists_gcirc_of_affine {a : V} (ha : pval Γ a = 5) {x : G}
    (hx : x ∈ MulAction.stabilizer G a) {β : Fin 5 → V} (hadj : ∀ i, Γ.Adj a (β i))
    (hinj : Function.Injective β) (hxβ : ∀ i, x • β i = β (i + 1)) (j p q : Fin 5) {δ δ' : V}
    (hδ : Γ.Adj (β p) δ) (hδ' : Γ.Adj (β q) δ') (hδ'a : δ' ≠ a)
    (hq : q - j ≠ p - j ∧ q - j ≠ -(p - j)) : ¬ ∃ g ∈ Gcirc Γ G a (β j), g • δ = δ' := by
  open Fin.CommRing in
  rintro ⟨g, hg, hgδ⟩
  obtain ⟨u, c, -, hgβ⟩ := F.exists_affine_smul ha hx hadj hinj hxβ hg.1.1
  have hj : g • β j = β j := MulAction.mem_stabilizer_iff.1 hg.1.2
  have hu : u * u = 1 := (F.affine_mem_gcirc_iff ha hadj hinj j hg.1.1 hgβ hj).1 hg
  have hfix : u * j + c = j := hinj ((hgβ j).symm.trans hj)
  have hpq : g • β p = β q := by
    refine F.eq_of_adj_adj (u₁ := a) (u₂ := δ') (F.adj_smul_of_mem_stabilizer hg.1.1 (hadj p)) ?_
      (hadj q) hδ' hδ'a.symm
    have := (F.adj_smul g (β p) δ).2 hδ
    rwa [hgδ] at this
  have hqp : u * p + c = q := hinj ((hgβ p).symm.trans hpq)
  have key : ∀ w : Fin 5, w * w = 1 → w = 1 ∨ w = -1 := by decide
  rcases key u hu with rfl | rfl
  · exact hq.1 (by linear_combination hfix - hqp)
  · exact hq.2 (by linear_combination hfix - hqp)

end FanTree

end CFSG.Quasithin.Fan86
