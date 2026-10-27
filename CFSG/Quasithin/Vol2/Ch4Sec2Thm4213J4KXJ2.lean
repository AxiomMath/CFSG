module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXJ1
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXQS

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

open scoped commutatorElement

theorem center_centralizes_of_card {Γ : Type} [Group Γ] [Finite Γ] {KX J J' : Subgroup Γ} {r : Γ}
    (hKX : CFSG.IsQuasisimple ↥KX) (hKXz : Nat.card ↥(Subgroup.center ↥KX) = 6)
    (hcomm : ∀ j ∈ J, ∀ j' ∈ J', j * j' = j' * j)
    (hKXJ : KX ≤ J ⊔ J') (hr : ∀ k ∈ KX, r * k = k * r)
    (hrJ' : ∀ j' ∈ J', r⁻¹ * j' * r ∈ J)
    (hJZ : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card (↥KX ⧸ Subgroup.center ↥KX)) :
    ∀ g ∈ Subgroup.center ↥KX, ∀ j ∈ J, (g : Γ) * j = j * (g : Γ) := by
  classical
  have hdec : ∀ k ∈ KX, ∃ j ∈ J, ∃ j' ∈ J', k = j * j' := fun k hk =>
    mem_sup_decomp hcomm (hKXJ hk)
  have hconjJ : ∀ k ∈ KX, ∀ j ∈ J, k * j * k⁻¹ ∈ J := by
    intro k hk j hj
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec k hk
    have hbj : b * j * b⁻¹ = j := by
      rw [← hcomm j hj b hb, mul_assoc, mul_inv_cancel, mul_one]
    have e : a * b * j * (a * b)⁻¹ = a * (b * j * b⁻¹) * a⁻¹ := by group
    rw [e, hbj]
    exact J.mul_mem (J.mul_mem ha hj) (J.inv_mem ha)
  let N : Subgroup ↥KX :=
    { carrier := {k | ∀ j ∈ J, (k : Γ) * j = j * (k : Γ)}
      mul_mem' := by
        intro a b ha hb j hj
        simp only [Subgroup.coe_mul]
        calc (a : Γ) * (b : Γ) * j = (a : Γ) * ((b : Γ) * j) := mul_assoc _ _ _
          _ = (a : Γ) * (j * (b : Γ)) := by rw [hb j hj]
          _ = ((a : Γ) * j) * (b : Γ) := (mul_assoc _ _ _).symm
          _ = (j * (a : Γ)) * (b : Γ) := by rw [ha j hj]
          _ = j * ((a : Γ) * (b : Γ)) := mul_assoc _ _ _
      one_mem' := fun j _ => by simp
      inv_mem' := by
        intro a ha j hj
        exact ((show Commute (a : Γ) j from ha j hj).inv_left).eq }
  have hNnorm : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    intro j hj
    have hj0 : (g : Γ)⁻¹ * j * (g : Γ) ∈ J := by
      have := hconjJ (g : Γ)⁻¹ (KX.inv_mem g.2) j hj
      simpa using this
    have key : (n : Γ) * ((g : Γ)⁻¹ * j * (g : Γ)) = ((g : Γ)⁻¹ * j * (g : Γ)) * (n : Γ) :=
      hn _ hj0
    have hk2 : (g : Γ) * (n : Γ) * ((g : Γ)⁻¹ * j * (g : Γ)) =
        (g : Γ) * ((g : Γ)⁻¹ * j * (g : Γ)) * (n : Γ) := by
      calc (g : Γ) * (n : Γ) * ((g : Γ)⁻¹ * j * (g : Γ)) = (g : Γ) * ((n : Γ) * ((g : Γ)⁻¹ * j * (g : Γ))) :=
            mul_assoc _ _ _
        _ = (g : Γ) * (((g : Γ)⁻¹ * j * (g : Γ)) * (n : Γ)) := by rw [key]
        _ = (g : Γ) * ((g : Γ)⁻¹ * j * (g : Γ)) * (n : Γ) := (mul_assoc _ _ _).symm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (g : Γ) * (n : Γ) * (g : Γ)⁻¹ * j
        = (g : Γ) * (n : Γ) * ((g : Γ)⁻¹ * j * (g : Γ)) * (g : Γ)⁻¹ := by group
      _ = (g : Γ) * ((g : Γ)⁻¹ * j * (g : Γ)) * (n : Γ) * (g : Γ)⁻¹ := by rw [hk2]
      _ = j * ((g : Γ) * (n : Γ) * (g : Γ)⁻¹) := by group
  have hNle : N ≤ Subgroup.center ↥KX := by
    rcases normal_le_center_or_top hKX N with h | htop
    · exact h
    · exfalso
      have hKXJ' : ∀ k ∈ KX, ∀ j ∈ J, k * j = j * k := fun k hk j hj => by
        have : (⟨k, hk⟩ : ↥KX) ∈ N := by rw [htop]; exact Subgroup.mem_top _
        exact this j hj
      have hrk : ∀ k ∈ KX, r * k = k * r := hr
      have hKXJ'' : ∀ k ∈ KX, ∀ j' ∈ J', k * j' = j' * k := by
        intro k hk j' hj'
        have hj : r⁻¹ * j' * r ∈ J := hrJ' j' hj'
        have e : j' = r * (r⁻¹ * j' * r) * r⁻¹ := by group
        have hrk' : r⁻¹ * k = k * r⁻¹ := by
          calc r⁻¹ * k = r⁻¹ * (k * r) * r⁻¹ := by group
            _ = r⁻¹ * (r * k) * r⁻¹ := by rw [hrk k hk]
            _ = k * r⁻¹ := by group
        calc k * j' = k * (r * (r⁻¹ * j' * r) * r⁻¹) := by rw [← e]
          _ = (k * r) * (r⁻¹ * j' * r) * r⁻¹ := by group
          _ = (r * k) * (r⁻¹ * j' * r) * r⁻¹ := by rw [← hrk k hk]
          _ = r * (k * (r⁻¹ * j' * r)) * r⁻¹ := by group
          _ = r * ((r⁻¹ * j' * r) * k) * r⁻¹ := by rw [hKXJ' k hk _ hj]
          _ = r * (r⁻¹ * j' * r) * (k * r⁻¹) := by group
          _ = r * (r⁻¹ * j' * r) * (r⁻¹ * k) := by rw [hrk'.symm]
          _ = j' * k := by group
      have hab : ∀ a ∈ KX, ∀ b ∈ KX, a * b = b * a := by
        intro a ha b hb
        obtain ⟨j, hj, j', hj', rfl⟩ := hdec b hb
        calc a * (j * j') = (a * j) * j' := by group
          _ = (j * a) * j' := by rw [hKXJ' a ha j hj]
          _ = j * (a * j') := by group
          _ = j * (j' * a) := by rw [hKXJ'' a ha j' hj']
          _ = (j * j') * a := by group
      obtain ⟨a, b, hab'⟩ := hKX.2.2
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      apply hab'
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hab _ a'.2 _ b'.2)
  have hdec' : ∀ k : ↥KX, ∃ j ∈ J, ∃ j' ∈ J', (k : Γ) = j * j' := fun k => hdec k k.2
  choose jf hjf j'f hj'f hkf using hdec'
  let ψ : ↥KX → ↥J ⧸ Subgroup.center ↥J := fun k => QuotientGroup.mk ⟨jf k, hjf k⟩
  have hψ : ∀ (k : ↥KX) (j j' : Γ) (hj : j ∈ J) (hj' : j' ∈ J'), (k : Γ) = j * j' →
      (QuotientGroup.mk ⟨j, hj⟩ : ↥J ⧸ Subgroup.center ↥J) = ψ k := by
    intro k j j' hj hj' hk
    show (QuotientGroup.mk ⟨j, hj⟩ : ↥J ⧸ Subgroup.center ↥J) = QuotientGroup.mk ⟨jf k, hjf k⟩
    rw [QuotientGroup.eq]
    have e : (jf k)⁻¹ * j = j'f k * j'⁻¹ := by
      have h1 : jf k * j'f k = j * j' := (hkf k).symm.trans hk
      calc (jf k)⁻¹ * j = (jf k)⁻¹ * (j * j') * j'⁻¹ := by group
        _ = (jf k)⁻¹ * (jf k * j'f k) * j'⁻¹ := by rw [h1]
        _ = j'f k * j'⁻¹ := by group
    have hmem : (jf k)⁻¹ * j ∈ J' := by
      rw [e]
      exact J'.mul_mem (hj'f k) (J'.inv_mem hj')
    have hmemJ : (jf k)⁻¹ * j ∈ J := J.mul_mem (J.inv_mem (hjf k)) hj
    have hcen : (⟨(jf k)⁻¹ * j, hmemJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hcomm g.1 g.2 _ hmem
    convert Subgroup.inv_mem _ hcen using 1
    apply Subtype.ext
    simp
  have hψmul : ∀ a b : ↥KX, ψ (a * b) = ψ a * ψ b := by
    intro a b
    have hJab : jf a * jf b ∈ J := J.mul_mem (hjf a) (hjf b)
    have hJ'ab : j'f a * j'f b ∈ J' := J'.mul_mem (hj'f a) (hj'f b)
    have hab_eq : ((a * b : ↥KX) : Γ) = (jf a * jf b) * (j'f a * j'f b) := by
      rw [Subgroup.coe_mul, hkf a, hkf b]
      calc jf a * j'f a * (jf b * j'f b) = jf a * (j'f a * jf b) * j'f b := by group
        _ = jf a * (jf b * j'f a) * j'f b := by rw [← hcomm (jf b) (hjf b) (j'f a) (hj'f a)]
        _ = jf a * jf b * (j'f a * j'f b) := by group
    rw [← hψ (a * b) (jf a * jf b) (j'f a * j'f b) hJab hJ'ab hab_eq]
    show QuotientGroup.mk ((⟨jf a, hjf a⟩ : ↥J) * (⟨jf b, hjf b⟩ : ↥J)) = QuotientGroup.mk (⟨jf a, hjf a⟩ : ↥J) * QuotientGroup.mk (⟨jf b, hjf b⟩ : ↥J)
    rw [QuotientGroup.mk_mul]
  let φ : ↥KX →* ↥J ⧸ Subgroup.center ↥J := MonoidHom.mk' ψ hψmul
  have hφ : ∀ a, φ a = ψ a := fun a => rfl
  have hker : φ.ker = N := by
    ext a
    rw [MonoidHom.mem_ker, hφ]
    constructor
    · intro ha j hj
      have hc : (⟨jf a, hjf a⟩ : ↥J) ∈ Subgroup.center ↥J := by
        have := (QuotientGroup.eq_one_iff (⟨jf a, hjf a⟩ : ↥J)).mp ha
        exact this
      have hcj : (jf a) * j = j * (jf a) := by
        have := Subgroup.mem_center_iff.mp hc ⟨j, hj⟩
        exact congrArg Subtype.val this.symm
      have ha' : (a : Γ) = jf a * j'f a := hkf a
      show (a : Γ) * j = j * (a : Γ)
      rw [ha', mul_assoc, ← hcomm j hj (j'f a) (hj'f a), ← mul_assoc, hcj, mul_assoc]
    · intro ha
      have hgc : ∀ x ∈ J, x * (j'f a)⁻¹ = (j'f a)⁻¹ * x := by
        intro x hx
        have hx' : x * j'f a = j'f a * x := hcomm x hx (j'f a) (hj'f a)
        calc x * (j'f a)⁻¹ = (j'f a)⁻¹ * ((j'f a) * x) * (j'f a)⁻¹ := by group
          _ = (j'f a)⁻¹ * (x * j'f a) * (j'f a)⁻¹ := by rw [← hx']
          _ = (j'f a)⁻¹ * x := by group
      have hjf_eq : jf a = (a : Γ) * (j'f a)⁻¹ := by
        rw [hkf a]
        group
      have hcen : (⟨jf a, hjf a⟩ : ↥J) ∈ Subgroup.center ↥J := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hjf_eq]
        calc (g : Γ) * ((a : Γ) * (j'f a)⁻¹) = ((g : Γ) * (a : Γ)) * (j'f a)⁻¹ := by group
          _ = ((a : Γ) * (g : Γ)) * (j'f a)⁻¹ := by rw [← ha g.1 g.2]
          _ = (a : Γ) * ((g : Γ) * (j'f a)⁻¹) := by group
          _ = (a : Γ) * ((j'f a)⁻¹ * (g : Γ)) := by rw [hgc g.1 g.2]
          _ = ((a : Γ) * (j'f a)⁻¹) * (g : Γ) := by group
      exact (QuotientGroup.eq_one_iff (⟨jf a, hjf a⟩ : ↥J)).mpr hcen
  have hcard : Nat.card (↥KX ⧸ N) ≤ Nat.card (↥KX ⧸ Subgroup.center ↥KX) := by
    have hk := Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivRange φ)).toEquiv
    rw [hk]
    exact (Subgroup.card_le_card_group _).trans hJZ
  have h1 : Nat.card ↥KX = Nat.card (↥KX ⧸ Subgroup.center ↥KX) * 6 := by
    rw [← hKXz]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card ↥KX = Nat.card (↥KX ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hqpos : 0 < Nat.card (↥KX ⧸ N) := Nat.card_pos
  have hn6 : 6 ≤ Nat.card N := by
    by_contra hlt
    rw [not_le] at hlt
    nlinarith
  have hNeq : N = Subgroup.center ↥KX :=
    Subgroup.eq_of_le_of_card_ge hNle (by rw [hKXz]; exact hn6)
  intro g hg j hj
  have hgN : g ∈ N := by rw [hNeq]; exact hg
  exact hgN j hj

end CFSG.Quasithin.H13.Ch4.J4KX
