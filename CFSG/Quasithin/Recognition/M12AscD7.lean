module

public import CFSG.Quasithin.Recognition.M12AscD6

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

namespace AscCox

variable {m : AscModel z} (c : AscCox m)

theorem mem_D_of_inverted_z
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z)
    (h27 : 27 ∣ Nat.card G) {y : G} (h : OuterData c y) {q : G}
    (hq : q ∈ Subgroup.centralizer (c.D : Set G)) (hzq : z * q * z⁻¹ = q⁻¹) : q ∈ c.D := by
  have hbq := c.b_inverts_C hyp h27 h hq
  have hz2 : z * z = 1 := c.z_sq
  have hu : c.u' = (c.u' * z) * z := by rw [mul_assoc, hz2, mul_one]
  have e : c.u' * q * c.u'⁻¹ = q := by
    calc c.u' * q * c.u'⁻¹ = ((c.u' * z) * z) * q * ((c.u' * z) * z)⁻¹ := by rw [← hu]
      _ = (c.u' * z) * (z * q * z⁻¹) * (c.u' * z)⁻¹ := by group
      _ = (c.u' * z) * q⁻¹ * (c.u' * z)⁻¹ := by rw [hzq]
      _ = ((c.u' * z) * q * (c.u' * z)⁻¹)⁻¹ := by group
      _ = q := by rw [hbq, inv_inv]
  have hqu : q * c.u' = c.u' * q := by
    calc q * c.u' = (c.u' * q * c.u'⁻¹) * c.u' := by rw [e]
      _ = c.u' * q := by group
  have hconj := c.isConj_u' hyp
  have hypu := asc03Hyp_of_isConj hyp hconj
  have hcardu : Nat.card ↥(ascH c.u') = 192 := AscModel.card_ascH hypu
  let S : Subgroup G := Subgroup.centralizer (c.D : Set G) ⊓ ascH c.u'
  have hSodd : ∀ g ∈ S, Odd (orderOf g) := fun g hg =>
    c.odd_orderOf_of_centralizes_D hyp h27 ((mem_C c).1 hg.1)
  have hx1C : c.x1 ∈ Subgroup.centralizer (c.D : Set G) :=
    (mem_C c).2 (fun d hd => c.D_comm c.x1_mem_D hd)
  have hx1S : c.x1 ∈ S := ⟨hx1C, Subgroup.mem_centralizer_singleton_iff.2 c.x1_u⟩
  obtain ⟨hSeq, -⟩ := eq_zpowers_of_odd_sub hcardu inf_le_right hSodd hx1S c.x1_ne
  have hqS : q ∈ S := ⟨hq, Subgroup.mem_centralizer_singleton_iff.2 hqu⟩
  have hqz : q ∈ zpowers c.x1 := by
    rw [← hSeq]
    exact hqS
  exact (Subgroup.zpowers_le.2 c.x1_mem_D) hqz

theorem centralizer_D_le
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z)
    (h27 : 27 ∣ Nat.card G) {y : G} (h : OuterData c y) {q : G}
    (hq : q ∈ Subgroup.centralizer (c.D : Set G)) : q ∈ c.D := by
  classical
  let C : Subgroup G := Subgroup.centralizer (c.D : Set G)
  have hz2 : z * z = 1 := c.z_sq
  have hzC : ∀ p ∈ C, z * p * z⁻¹ ∈ C := fun p hp => c.conj_mem_C c.z_mem_N hp
  let τ : ↥C →* ↥C := conjP C z hzC
  have hτ : ∀ a, τ (τ a) = a := by
    intro a
    apply Subtype.ext
    simp only [τ, conjP_coe]
    calc z * (z * (a : G) * z⁻¹) * z⁻¹ = (z * z) * (a : G) * (z * z)⁻¹ := by group
      _ = a := by rw [hz2]; group
  have hcomm : ∀ a b : ↥C, a * b = b * a := fun a b =>
    Subtype.ext (c.C_comm hyp h27 h a.2 b.2)
  have hqodd : Odd (orderOf (⟨q, hq⟩ : ↥C)) := by
    rw [Subgroup.orderOf_mk]
    exact c.odd_orderOf_of_centralizes_D hyp h27 ((mem_C c).1 hq)
  obtain ⟨ap, am, hsplit, hp, hm⟩ := exists_split τ hτ hcomm hqodd
  have hq_eq : q = (ap : G) * (am : G) := congrArg Subtype.val hsplit
  have hp' : z * (ap : G) * z⁻¹ = ap := congrArg Subtype.val hp
  have hm' : z * (am : G) * z⁻¹ = (am : G)⁻¹ := congrArg Subtype.val hm
  rw [hq_eq]
  exact mul_mem (c.mem_D_of_fixed_z ((mem_C c).1 ap.2) hp')
    (c.mem_D_of_inverted_z hyp h27 h am.2 hm')

end AscCox

end CFSG.Quasithin
