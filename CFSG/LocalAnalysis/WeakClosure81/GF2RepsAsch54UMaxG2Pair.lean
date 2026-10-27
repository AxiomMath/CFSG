module

public import Mathlib.GroupTheory.PGroup
import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch80G2

open Subgroup
open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab (mem_sup_of_commute mem_zpowers_of_sq)

variable {Y : Type} [Group Y]

@[expose] def sqCent (E : Subgroup Y) (z : Y) : Subgroup Y :=
  closure {x | ∃ g ∈ E, g * z = z * g ∧ g * g = x}

theorem sq_mem_sqCent {E : Subgroup Y} {z g : Y} (hg : g ∈ E) (hgz : g * z = z * g) :
    g * g ∈ sqCent E z :=
  subset_closure ⟨g, hg, hgz, rfl⟩

theorem sqCent_le (E : Subgroup Y) (z : Y) : sqCent E z ≤ E :=
  (closure_le E).2 fun _ ⟨g, hg, _, hx⟩ => hx ▸ E.mul_mem hg hg

theorem sqCent_le_centralizer (E : Subgroup Y) (z : Y) :
    sqCent E z ≤ centralizer ({z} : Set Y) := by
  refine (closure_le _).2 fun _ ⟨g, _, hgz, hx⟩ => ?_
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff, ← hx]
  have hc : Commute g z := hgz
  exact hc.mul_left hc

theorem conj_mem_sqCent {E : Subgroup Y} {z t x : Y} (htE : t ∈ normalizer (E : Set Y))
    (htz : t * z = z * t) (hx : x ∈ sqCent E z) : t * x * t⁻¹ ∈ sqCent E z := by
  have hle : sqCent E z ≤ (sqCent E z).comap (MulAut.conj t).toMonoidHom := by
    refine (closure_le _).2 ?_
    rintro _ ⟨g, hg, hgz, rfl⟩
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      show t * (g * g) * t⁻¹ = t * g * t⁻¹ * (t * g * t⁻¹) by group]
    have hc : Commute t z := htz
    exact sq_mem_sqCent ((mem_normalizer_iff.mp htE g).mp hg)
      ((hc.mul_left hgz).mul_left hc.inv_left)
  simpa [MulAut.conj_apply] using hle hx

theorem mem_sup_zpowers {z u x : Y} (hz : z * z = 1) (hu : u * u = 1) (hc : z * u = u * z)
    (hx : x ∈ zpowers z ⊔ zpowers u) : x = 1 ∨ x = z ∨ x = u ∨ x = z * u := by
  have hcomm : ∀ c ∈ zpowers z, ∀ d ∈ zpowers u, c * d = d * c := by
    intro c hc' d hd
    rcases mem_zpowers_of_sq hz hc' with rfl | rfl <;>
      rcases mem_zpowers_of_sq hu hd with rfl | rfl <;> simp [hc]
  obtain ⟨c, hc', d, hd, rfl⟩ := mem_sup_of_commute hcomm hx
  rcases mem_zpowers_of_sq hz hc' with rfl | rfl <;>
    rcases mem_zpowers_of_sq hu hd with rfl | rfl <;> simp

theorem exists_le_normalizer_of_odd_card [Finite Y] {T : Subgroup Y} (hT : IsPGroup 2 T)
    {𝒮 : Set (Subgroup Y)}
    (h𝒮 : ∀ t ∈ T, ∀ V ∈ 𝒮, V.map (MulAut.conj t).toMonoidHom ∈ 𝒮)
    (hodd : Odd (Nat.card ↥𝒮)) : ∃ V ∈ 𝒮, T ≤ normalizer (V : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction ↥T ↥𝒮 :=
    { smul := fun t V => ⟨V.1.map (MulAut.conj (t : Y)).toMonoidHom, h𝒮 t t.2 V.1 V.2⟩
      one_smul := fun V => Subtype.ext <| by
        change V.1.map (MulAut.conj ((1 : ↥T) : Y)).toMonoidHom = V.1
        ext x
        simp [Subgroup.mem_map]
      mul_smul := fun t t' V => Subtype.ext <| by
        change V.1.map (MulAut.conj ((t * t' : ↥T) : Y)).toMonoidHom =
          (V.1.map (MulAut.conj (t' : Y)).toMonoidHom).map (MulAut.conj (t : Y)).toMonoidHom
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [mul_assoc] }
  have h2 : ¬ 2 ∣ Nat.card ↥𝒮 := fun hd => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hd)
  obtain ⟨V, hV⟩ := hT.nonempty_fixed_point_of_prime_not_dvd_card ↥𝒮 h2
  refine ⟨V.1, V.2, fun t ht => ?_⟩
  have hmap : V.1.map (MulAut.conj t).toMonoidHom = V.1 := congrArg Subtype.val (hV ⟨t, ht⟩)
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by simpa [MulAut.conj_apply] using hyx
    rwa [← this]

private theorem g2Pair_card_eq_mul {α β : Type*} [Finite α] [Finite β] (f : α → β) (k : ℕ)
    (h : ∀ b, Nat.card {a // f a = b} = k) : Nat.card α = k * Nat.card β := by
  classical
  have := Fintype.ofFinite β
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  simp only [h]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, mul_comm]

structure SL2Pair (E : Subgroup Y) (z : Y) (J₁ J₂ : Subgroup Y) : Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  comm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a
  inter : J₁ ⊓ J₂ = zpowers z
  sq_eq : sqCent E z = J₁ ⊔ J₂
  inv₁ : ∀ a ∈ J₁, a * a = 1 → a ∈ zpowers z
  inv₂ : ∀ b ∈ J₂, b * b = 1 → b ∈ zpowers z
  conj₁ : ∀ a ∈ J₁, ∀ a' ∈ J₁, a * a = z → a' * a' = z → ∃ c ∈ J₁, c * a * c⁻¹ = a'
  card₁ : Nat.card {a : Y // a ∈ J₁ ∧ a * a = z} % 4 = 2
  card₂ : Nat.card {b : Y // b ∈ J₂ ∧ b * b = z} % 4 = 2
  cent : ∀ w ∈ E, w * z = z * w → (∀ x ∈ sqCent E z, w * x = x * w) → w ∈ zpowers z

@[expose] def fours (E : Subgroup Y) (z : Y) : Set (Subgroup Y) :=
  {V | ∃ u ∈ sqCent E z, u * u = 1 ∧ u ∉ zpowers z ∧ V = zpowers z ⊔ zpowers u}

namespace SL2Pair

variable {E : Subgroup Y} {z : Y} {J₁ J₂ : Subgroup Y} (h : SL2Pair E z J₁ J₂)
include h

theorem z_mem₁ : z ∈ J₁ := by
  have : z ∈ J₁ ⊓ J₂ := by rw [h.inter]; exact mem_zpowers z
  exact this.1

theorem z_mem₂ : z ∈ J₂ := by
  have : z ∈ J₁ ⊓ J₂ := by rw [h.inter]; exact mem_zpowers z
  exact this.2

theorem le_sqCent₁ : J₁ ≤ sqCent E z := by rw [h.sq_eq]; exact le_sup_left

theorem mem_zpowers_iff {x : Y} : x ∈ zpowers z ↔ x = 1 ∨ x = z := by
  refine ⟨mem_zpowers_of_sq h.z_sq, ?_⟩
  rintro (rfl | rfl)
  · exact one_mem _
  · exact mem_zpowers _

theorem comm_z₁ {a : Y} (ha : a ∈ J₁) : a * z = z * a := h.comm a ha z h.z_mem₂

theorem comm_z₂ {b : Y} (hb : b ∈ J₂) : z * b = b * z := h.comm z h.z_mem₁ b hb

theorem exists_mul {u : Y} (hu : u ∈ sqCent E z) (hu2 : u * u = 1) (huz : u ∉ zpowers z) :
    ∃ a ∈ J₁, ∃ b ∈ J₂, a * a = z ∧ b * b = z ∧ a * b = u := by
  rw [h.sq_eq] at hu
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute h.comm hu
  have hab : a * b = b * a := h.comm a ha b hb
  have hsq : a * a * (b * b) = 1 := by
    calc a * a * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hab]
      _ = a * b * (a * b) := by group
      _ = 1 := hu2
  have hbb : b * b = (a * a)⁻¹ := eq_inv_of_mul_eq_one_right hsq
  have haa : a * a ∈ zpowers z := by
    rw [← h.inter]
    refine Subgroup.mem_inf.2 ⟨mul_mem ha ha, ?_⟩
    have : b * b ∈ J₂ := mul_mem hb hb
    rw [hbb] at this
    exact (Subgroup.inv_mem_iff _).1 this
  rcases h.mem_zpowers_iff.1 haa with h1 | h1
  · exfalso
    apply huz
    have hb1 : b * b = 1 := by rw [hbb, h1, inv_one]
    exact mul_mem (h.inv₁ a ha h1) (h.inv₂ b hb hb1)
  · refine ⟨a, ha, b, hb, h1, ?_, rfl⟩
    rw [hbb, h1]
    exact inv_eq_of_mul_eq_one_right h.z_sq

theorem mul_mem_fours {a b : Y} (ha : a ∈ J₁) (hb : b ∈ J₂) (haa : a * a = z)
    (hbb : b * b = z) : a * b ∈ sqCent E z ∧ a * b * (a * b) = 1 ∧ a * b ∉ zpowers z := by
  have hab : a * b = b * a := h.comm a ha b hb
  refine ⟨by rw [h.sq_eq]; exact mul_mem (mem_sup_left ha) (mem_sup_right hb), ?_, ?_⟩
  · calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = a * a * (b * b) := by group
      _ = 1 := by rw [haa, hbb, h.z_sq]
  · intro hmem
    have hz1 : ∀ c ∈ J₁, c ∈ J₂ → c * c ≠ z := by
      intro c hc1 hc2 hcc
      have : c ∈ zpowers z := by rw [← h.inter]; exact ⟨hc1, hc2⟩
      rcases h.mem_zpowers_iff.1 this with rfl | rfl
      · exact h.z_ne (by rw [← hcc, one_mul])
      · exact h.z_ne (by rw [← hcc, h.z_sq])
    rcases h.mem_zpowers_iff.1 hmem with h1 | h1
    · refine hz1 a ha ?_ haa
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem hb
    · refine hz1 a ha ?_ haa
      rw [eq_mul_inv_of_mul_eq h1]
      exact mul_mem h.z_mem₂ (inv_mem hb)

theorem mem_sqCent_of_mem {u : Y} (hu : u ∈ sqCent E z) (hu2 : u * u = 1)
    (huz : u ∉ zpowers z) : z ∈ sqCent E u := by
  obtain ⟨a, ha, b, hb, haa, -, rfl⟩ := h.exists_mul hu hu2 huz
  have haE : a ∈ E := sqCent_le E z (h.le_sqCent₁ ha)
  have hab : a * b = b * a := h.comm a ha b hb
  rw [← haa]
  refine sq_mem_sqCent haE ?_
  calc a * (a * b) = a * (b * a) := by rw [hab]
    _ = a * b * a := by group

theorem not_mem_zpowers {u : Y} (hu2 : u * u = 1) (huz : u ∉ zpowers z) : z ∉ zpowers u := by
  intro hz
  rcases mem_zpowers_of_sq hu2 hz with h1 | h1
  · exact h.z_ne h1
  · exact huz (by rw [← h1]; exact mem_zpowers z)

theorem exists_swap {w : Y} (hw : w ∈ sqCent E z) (hw2 : w * w = 1) (hwz : w ∉ zpowers z) :
    ∃ c ∈ E, c * z = z * c ∧ c * w * c⁻¹ = w * z := by
  obtain ⟨a, ha, b, hb, haa, -, rfl⟩ := h.exists_mul hw hw2 hwz
  have haa' : a⁻¹ * a⁻¹ = z := by
    rw [← mul_inv_rev, haa]
    exact inv_eq_of_mul_eq_one_right h.z_sq
  obtain ⟨c, hc, hca⟩ := h.conj₁ a ha a⁻¹ (inv_mem ha) haa haa'
  refine ⟨c, sqCent_le E z (h.le_sqCent₁ hc), h.comm_z₁ hc, ?_⟩
  have hcb : c * b = b * c := h.comm c hc b hb
  have hinv : a⁻¹ = a * z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, haa, h.z_sq])
  calc c * (a * b) * c⁻¹ = c * a * c⁻¹ * (c * b * c⁻¹) := by group
    _ = a⁻¹ * b := by rw [hca, hcb]; group
    _ = a * z * b := by rw [hinv]
    _ = a * b * z := by rw [mul_assoc, h.comm_z₂ hb, ← mul_assoc]

theorem factor {a a' b b' c : Y} (ha : a ∈ J₁) (ha' : a' ∈ J₁) (hb : b ∈ J₂) (hb' : b' ∈ J₂)
    (hc : c ∈ zpowers z) (he : a' * b' = c * (a * b)) :
    a' * a⁻¹ ∈ zpowers z ∧ b' * b⁻¹ ∈ zpowers z := by
  have hc₁ : c ∈ J₁ := by
    have : c ∈ J₁ ⊓ J₂ := by rw [h.inter]; exact hc
    exact this.1
  have hwe : b * b'⁻¹ = (c * a)⁻¹ * a' := by
    rw [eq_mul_inv_of_mul_eq he]
    group
  have hw : b * b'⁻¹ ∈ zpowers z := by
    rw [← h.inter]
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem hb (inv_mem hb')⟩
    rw [hwe]
    exact mul_mem (inv_mem (mul_mem hc₁ ha)) ha'
  have hwa : a * (b * b'⁻¹) = b * b'⁻¹ * a := h.comm a ha _ (mul_mem hb (inv_mem hb'))
  have ha'2 : a' = c * a * (b * b'⁻¹) := by
    rw [hwe]
    group
  refine ⟨?_, ?_⟩
  · have : a' * a⁻¹ = c * (b * b'⁻¹) := by
      rw [ha'2, mul_assoc c a, hwa]
      group
    rw [this]
    exact mul_mem hc hw
  · have : b' * b⁻¹ = (b * b'⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hw

theorem sup_eq_iff {a a' b b' : Y} (ha : a ∈ J₁) (ha' : a' ∈ J₁) (hb : b ∈ J₂) (hb' : b' ∈ J₂)
    (haa : a * a = z) (haa' : a' * a' = z) (hbb : b * b = z) (hbb' : b' * b' = z) :
    zpowers z ⊔ zpowers (a' * b') = zpowers z ⊔ zpowers (a * b) ↔
      a' * a⁻¹ ∈ zpowers z ∧ b' * b⁻¹ ∈ zpowers z := by
  obtain ⟨-, hu2, -⟩ := h.mul_mem_fours ha hb haa hbb
  obtain ⟨-, -, huz'⟩ := h.mul_mem_fours ha' hb' haa' hbb'
  have hza : Commute z a := (h.comm_z₁ ha).symm
  have hzb : Commute z b := h.comm_z₂ hb
  have hzu : z * (a * b) = a * b * z := hza.mul_right hzb
  constructor
  · intro heq
    have hmem : a' * b' ∈ zpowers z ⊔ zpowers (a * b) := by
      rw [← heq]
      exact mem_sup_right (mem_zpowers _)
    rcases mem_sup_zpowers h.z_sq hu2 hzu hmem with h1 | h1 | h1 | h1
    · exact (huz' (by rw [h1]; exact one_mem _)).elim
    · exact (huz' (by rw [h1]; exact mem_zpowers z)).elim
    · exact h.factor ha ha' hb hb' (one_mem _) (by rw [h1, one_mul])
    · exact h.factor ha ha' hb hb' (mem_zpowers z) h1
  · rintro ⟨h1, h2⟩
    have hy₂ : b' * b⁻¹ ∈ J₂ := mul_mem hb' (inv_mem hb)
    have hya : a * (b' * b⁻¹) = b' * b⁻¹ * a := h.comm a ha _ hy₂
    have key : a' * b' = a' * a⁻¹ * (b' * b⁻¹) * (a * b) := by
      calc a' * b' = a' * a⁻¹ * (a * (b' * b⁻¹)) * b := by group
        _ = a' * a⁻¹ * (b' * b⁻¹ * a) * b := by rw [hya]
        _ = a' * a⁻¹ * (b' * b⁻¹) * (a * b) := by group
    have hxy : a' * a⁻¹ * (b' * b⁻¹) ∈ zpowers z := mul_mem h1 h2
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rw [zpowers_le, key]
      exact mul_mem (mem_sup_left hxy) (mem_sup_right (mem_zpowers _))
    · refine sup_le le_sup_left ?_
      rw [zpowers_le, show a * b = (a' * a⁻¹ * (b' * b⁻¹))⁻¹ * (a' * b') by rw [key]; group]
      exact mul_mem (mem_sup_left (inv_mem hxy)) (mem_sup_right (mem_zpowers _))

theorem mul_left₁ {x a : Y} (hx : x ∈ zpowers z) (ha : a ∈ J₁) (haa : a * a = z) :
    x * a ∈ J₁ ∧ x * a * (x * a) = z := by
  have hx₁ : x ∈ J₁ := by
    have : x ∈ J₁ ⊓ J₂ := by rw [h.inter]; exact hx
    exact this.1
  refine ⟨mul_mem hx₁ ha, ?_⟩
  rcases h.mem_zpowers_iff.1 hx with h1 | h1
  · rw [h1, one_mul, haa]
  · rw [h1]
    calc z * a * (z * a) = z * (a * z) * a := by group
      _ = z * (z * a) * a := by rw [h.comm_z₁ ha]
      _ = z * z * (a * a) := by group
      _ = z := by rw [h.z_sq, haa, one_mul]

theorem mul_left₂ {x b : Y} (hx : x ∈ zpowers z) (hb : b ∈ J₂) (hbb : b * b = z) :
    x * b ∈ J₂ ∧ x * b * (x * b) = z := by
  have hx₂ : x ∈ J₂ := by
    have : x ∈ J₁ ⊓ J₂ := by rw [h.inter]; exact hx
    exact this.2
  refine ⟨mul_mem hx₂ hb, ?_⟩
  rcases h.mem_zpowers_iff.1 hx with h1 | h1
  · rw [h1, one_mul, hbb]
  · rw [h1]
    calc z * b * (z * b) = z * (b * z) * b := by group
      _ = z * (z * b) * b := by rw [h.comm_z₂ hb]
      _ = z * z * (b * b) := by group
      _ = z := by rw [h.z_sq, hbb, one_mul]

theorem odd_card_fours [Finite Y] : Odd (Nat.card ↥(fours E z)) := by
  classical
  have : Finite (Subgroup Y) :=
    Finite.of_injective (fun H : Subgroup Y => (H : Set Y)) SetLike.coe_injective
  let Φ : {a : Y // a ∈ J₁ ∧ a * a = z} × {b : Y // b ∈ J₂ ∧ b * b = z} → ↥(fours E z) :=
    fun p => ⟨zpowers z ⊔ zpowers (p.1.1 * p.2.1), p.1.1 * p.2.1,
      (h.mul_mem_fours p.1.2.1 p.2.2.1 p.1.2.2 p.2.2.2).1,
      (h.mul_mem_fours p.1.2.1 p.2.2.1 p.1.2.2 p.2.2.2).2.1,
      (h.mul_mem_fours p.1.2.1 p.2.2.1 p.1.2.2 p.2.2.2).2.2, rfl⟩
  have hz2 : Nat.card ↥(zpowers z) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact h.z_sq) h.z_ne
  have hfib : ∀ V, Nat.card {p // Φ p = V} = 4 := by
    intro V
    obtain ⟨u, hu, hu2, huz, hV⟩ := V.2
    obtain ⟨a, ha, b, hb, haa, hbb, rfl⟩ := h.exists_mul hu hu2 huz
    have hiff : ∀ p : {a : Y // a ∈ J₁ ∧ a * a = z} × {b : Y // b ∈ J₂ ∧ b * b = z},
        Φ p = V ↔ p.1.1 * a⁻¹ ∈ zpowers z ∧ p.2.1 * b⁻¹ ∈ zpowers z := fun p => by
      rw [Subtype.ext_iff, hV]
      exact h.sup_eq_iff ha p.1.2.1 hb p.2.2.1 haa p.1.2.2 hbb p.2.2.2
    let e : {p // Φ p = V} ≃ ↥(zpowers z) × ↥(zpowers z) :=
      { toFun := fun p => (⟨p.1.1.1 * a⁻¹, ((hiff p.1).1 p.2).1⟩,
          ⟨p.1.2.1 * b⁻¹, ((hiff p.1).1 p.2).2⟩)
        invFun := fun xy => ⟨(⟨xy.1.1 * a, h.mul_left₁ xy.1.2 ha haa⟩,
            ⟨xy.2.1 * b, h.mul_left₂ xy.2.2 hb hbb⟩), (hiff _).2
            ⟨by simp only [mul_inv_cancel_right]; exact xy.1.2,
              by simp only [mul_inv_cancel_right]; exact xy.2.2⟩⟩
        left_inv := fun p => by
          apply Subtype.ext
          apply Prod.ext <;> apply Subtype.ext <;> simp
        right_inv := fun xy => by
          apply Prod.ext <;> apply Subtype.ext <;> simp }
    rw [Nat.card_congr e, Nat.card_prod, hz2]
  have hcard := g2Pair_card_eq_mul Φ 4 hfib
  rw [Nat.card_prod] at hcard
  have h1 := h.card₁
  have h2 := h.card₂
  obtain ⟨k₁, hk₁⟩ : ∃ k, Nat.card {a : Y // a ∈ J₁ ∧ a * a = z} = 2 * (2 * k + 1) :=
    ⟨Nat.card {a : Y // a ∈ J₁ ∧ a * a = z} / 4, by omega⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k, Nat.card {b : Y // b ∈ J₂ ∧ b * b = z} = 2 * (2 * k + 1) :=
    ⟨Nat.card {b : Y // b ∈ J₂ ∧ b * b = z} / 4, by omega⟩
  rw [hk₁, hk₂] at hcard
  have h4 : 4 * Nat.card ↥(fours E z) = 4 * ((2 * k₁ + 1) * (2 * k₂ + 1)) := by
    rw [← hcard]
    ring
  rw [Nat.eq_of_mul_eq_mul_left (by norm_num) h4]
  exact (odd_two_mul_add_one k₁).mul (odd_two_mul_add_one k₂)

theorem exists_le_normalizer [Finite Y] {T : Subgroup Y} (hT : IsPGroup 2 T)
    (hTE : T ≤ normalizer (E : Set Y)) (hTz : T ≤ centralizer ({z} : Set Y)) :
    ∃ u ∈ sqCent E z, u * u = 1 ∧ u ∉ zpowers z ∧
      T ≤ normalizer ((zpowers z ⊔ zpowers u : Subgroup Y) : Set Y) := by
  have hinv : ∀ t ∈ T, ∀ V ∈ fours E z, V.map (MulAut.conj t).toMonoidHom ∈ fours E z := by
    rintro t ht _ ⟨u, hu, hu2, huz, rfl⟩
    have htz : t * z = z * t := mem_centralizer_singleton_iff.1 (hTz ht)
    have htz' : t * z * t⁻¹ = z := by rw [htz]; group
    refine ⟨t * u * t⁻¹, conj_mem_sqCent (hTE ht) htz hu, ?_, ?_, ?_⟩
    · rw [show t * u * t⁻¹ * (t * u * t⁻¹) = t * (u * u) * t⁻¹ by group, hu2]
      group
    · intro hm
      rcases h.mem_zpowers_iff.1 hm with h1 | h1
      · exact huz (by rw [conj_eq_one_iff.1 h1]; exact one_mem _)
      · apply huz
        have : u = t⁻¹ * (t * u * t⁻¹) * t := by group
        rw [this, h1, show t⁻¹ * z * t = z by rw [mul_assoc, ← htz]; group]
        exact mem_zpowers z
    · rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_apply, htz']
  obtain ⟨V, ⟨u, hu, hu2, huz, rfl⟩, hTV⟩ :=
    exists_le_normalizer_of_odd_card hT hinv h.odd_card_fours
  exact ⟨u, hu, hu2, huz, hTV⟩

end SL2Pair

end CFSG.LocalAnalysis.WeakClosure81.Asch80G2

end
