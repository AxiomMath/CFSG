module

public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Inner
public import CFSG.LocalAnalysis.StandardType.ZS.ReflFrame

public section

namespace CFSG.StandardType.ZS.DimThree

open Subgroup CFSG.RankThree.PartOne CFSG.RepresentationTheory
open CFSG.RankThree.PartOne.LIT (autGL)

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private lemma a5_orderOf_le_five_z5 (x : alternatingGroup (Fin 5)) : orderOf x ≤ 5 := by
  have h : ∀ y : alternatingGroup (Fin 5),
      y ^ 1 = 1 ∨ y ^ 2 = 1 ∨ y ^ 3 = 1 ∨ y ^ 4 = 1 ∨ y ^ 5 = 1 := by
    decide +kernel
  rcases h x with h1 | h2 | h3 | h4 | h5
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h1).trans (by norm_num)
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h2).trans (by norm_num)
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h3).trans (by norm_num)
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h4).trans (by norm_num)
  · exact orderOf_le_of_pow_eq_one (by norm_num) h5

private lemma a5_pair_z5 :
    ∃ a b : alternatingGroup (Fin 5), a * a = 1 ∧ a ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧
      (a * b) ^ 5 = 1 ∧ a * b ≠ 1 := by
  decide +kernel

private lemma a5_involution_conj_z5 :
    ∀ x y : alternatingGroup (Fin 5), x * x = 1 → x ≠ 1 → y * y = 1 → y ≠ 1 →
      ∃ g : alternatingGroup (Fin 5), g * x * g⁻¹ = y := by
  decide +kernel

private lemma a5_noncomm_z5 :
    ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
  decide +kernel

private lemma a5_hatt_z5 :
    ∃ a b : alternatingGroup (Fin 5), a * a = 1 ∧ a ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧
      orderOf (a * b) = 5 := by
  obtain ⟨a, b, ha, ha1, hb, hb1, hpow, hne⟩ := a5_pair_z5
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact ⟨a, b, ha, ha1, hb, hb1, orderOf_eq_prime hpow hne⟩

private lemma a5_ambivalent_z5 :
    ∀ x : alternatingGroup (Fin 5), ∃ y, y * x * y⁻¹ = x⁻¹ := by
  decide +kernel

theorem excData_of_alternatingFive (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ A.map (autGL e).toMonoidHom)
    (hirr : IsIrreducibleMatrixRep H.subtype) (e5 : H ≃* alternatingGroup (Fin 5))
    (hp10 : p % 10 = 1 ∨ p % 10 = 9)
    (hdec : ∀ g ∈ A.map (autGL e).toMonoidHom, ∃ h ∈ H, ∃ z ∈ A.map (autGL e).toMonoidHom,
      (∀ y ∈ A.map (autGL e).toMonoidHom, z * y = y * z) ∧ g = h * z) :
    ExcData p .H3 A := by
  have hp5 : p ≠ 5 := by
    rintro rfl
    omega
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
  have hcardK : 2 * Nat.card (alternatingGroup (Fin 5)) = ExcRow.H3.ord := by
    rw [show Nat.card (alternatingGroup (Fin 5)) = 60 by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
      decide]
    norm_num [ExcRow.ord]
  have hZK : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by norm_num)
  have hcenK : 2 = ExcRow.H3.cen := by norm_num [ExcRow.cen]
  have hleK : ∀ a b : alternatingGroup (Fin 5), a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 →
      orderOf (a * b) ≤ ExcRow.H3.dmax := by
    intro a b _ _ _ _
    simpa [ExcRow.dmax] using a5_orderOf_le_five_z5 (a * b)
  have hdec' : ∀ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t →
      ∃ h ∈ H, ∃ z : GL (Fin 3) (ZMod p), (∀ x ∈ H, z * x = x * z) ∧ t = h * z := by
    intro t ht _
    obtain ⟨h, hh, z, _, hzc, htz⟩ := hdec t ht
    exact ⟨h, hh, z, fun x hx => hzc x (hHG hx), htz⟩
  exact excData_of_inner_of_mulEquiv hp e hR hI hHG hirr hdec' e5 ExcRow.H3 hp5 rfl
    hcardK hZK hcenK a5_noncomm_z5 hleK a5_hatt_z5
    (fun a b ha ha1 hb hb1 => by
      obtain ⟨g, hg⟩ := a5_involution_conj_z5 a b ha ha1 hb hb1
      exact isConj_iff.mpr ⟨g, hg⟩)

private def rfr_a5v0 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap ⟨0, 1, by decide, rfl⟩ ⟨2, 3, by decide, rfl⟩⟩

private def rfr_a5v1 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap ⟨0, 2, by decide, rfl⟩ ⟨1, 3, by decide, rfl⟩⟩

private def rfr_a5v2 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 3 * Equiv.swap 1 2,
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap ⟨0, 3, by decide, rfl⟩ ⟨1, 2, by decide, rfl⟩⟩

private def rfr_a5u : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 4 * Equiv.swap 1 2,
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap ⟨0, 4, by decide, rfl⟩ ⟨1, 2, by decide, rfl⟩⟩

private lemma rfr_a5_invol :
    rfr_a5v0 * rfr_a5v0 = 1 ∧ rfr_a5v0 ≠ 1 ∧ rfr_a5v1 * rfr_a5v1 = 1 ∧ rfr_a5v1 ≠ 1 ∧
    rfr_a5v2 * rfr_a5v2 = 1 ∧ rfr_a5v2 ≠ 1 ∧ rfr_a5u * rfr_a5u = 1 ∧ rfr_a5u ≠ 1 := by
  decide +kernel

private lemma rfr_a5_comm :
    rfr_a5v0 ≠ rfr_a5v1 ∧ rfr_a5v0 ≠ rfr_a5v2 ∧ rfr_a5v1 ≠ rfr_a5v2 ∧
    rfr_a5v0 * rfr_a5v1 = rfr_a5v1 * rfr_a5v0 ∧
    rfr_a5v0 * rfr_a5v2 = rfr_a5v2 * rfr_a5v0 ∧
    rfr_a5v1 * rfr_a5v2 = rfr_a5v2 * rfr_a5v1 := by
  decide +kernel

private lemma rfr_a5_order0 : orderOf (rfr_a5v0 * rfr_a5u) = 5 := by
  have h : (rfr_a5v0 * rfr_a5u) ^ 5 = 1 ∧ rfr_a5v0 * rfr_a5u ≠ 1 := by decide +kernel
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime h.1 h.2

private lemma rfr_a5_order1 : orderOf (rfr_a5v1 * rfr_a5u) = 5 := by
  have h : (rfr_a5v1 * rfr_a5u) ^ 5 = 1 ∧ rfr_a5v1 * rfr_a5u ≠ 1 := by decide +kernel
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime h.1 h.2

private lemma rfr_a5_order2 : orderOf (rfr_a5v2 * rfr_a5u) = 3 := by
  have h : (rfr_a5v2 * rfr_a5u) ^ 3 = 1 ∧ rfr_a5v2 * rfr_a5u ≠ 1 := by decide +kernel
  let : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime h.1 h.2

private lemma rfr_a5_pull_invol {H : Subgroup (GL (Fin 3) (ZMod p))}
    (e5 : H ≃* alternatingGroup (Fin 5)) {v : alternatingGroup (Fin 5)}
    (hv2 : v * v = 1) (hv1 : v ≠ 1) :
    ((e5.symm v : H) : GL (Fin 3) (ZMod p)) * ((e5.symm v : H) : GL (Fin 3) (ZMod p)) = 1 ∧
      ((e5.symm v : H) : GL (Fin 3) (ZMod p)) ≠ 1 := by
  constructor
  · have h : (e5.symm v : H) * (e5.symm v : H) = 1 := by
      apply e5.injective
      rw [map_mul, map_one, e5.apply_symm_apply]
      exact hv2
    simpa using congrArg Subtype.val h
  · intro h
    apply hv1
    have h' : (e5.symm v : H) = 1 := Subtype.ext h
    simpa using congrArg e5 h'

private lemma rfr_a5_lift (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ A.map (autGL e).toMonoidHom)
    [Group.IsPerfect H] (hirr : IsIrreducibleMatrixRep H.subtype)
    (hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a)
    (hinn : ∀ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t →
      ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹)
    (e5 : H ≃* alternatingGroup (Fin 5)) {v : alternatingGroup (Fin 5)}
    (hv2 : v * v = 1) (hv1 : v ≠ 1) :
    ∃ x ∈ A, IsRefl p x ∧ autGL e x = (-1) * ((e5.symm v : H) : GL (Fin 3) (ZMod p)) := by
  obtain ⟨ha2, ha1⟩ := rfr_a5_pull_invol e5 hv2 hv1
  exact exists_isRefl_of_involution hp e hR hI hHG hirr hnc hinn (e5.symm v).2 ha2 ha1

private lemma rfr_a5_ne_lift (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {H : Subgroup (GL (Fin 3) (ZMod p))}
    (e5 : H ≃* alternatingGroup (Fin 5)) {x y : U ≃ₗ[ZMod p] U} {v w : alternatingGroup (Fin 5)}
    (hx : autGL e x = (-1) * ((e5.symm v : H) : GL (Fin 3) (ZMod p)))
    (hy : autGL e y = (-1) * ((e5.symm w : H) : GL (Fin 3) (ZMod p))) (hv : v ≠ w) :
    x ≠ y :=
  (ne_iff_of_autGL_eq_neg_mul e hx hy).mpr fun h => hv (e5.symm.injective (Subtype.ext h))

private lemma rfr_a5_commute_lift (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {H : Subgroup (GL (Fin 3) (ZMod p))}
    (e5 : H ≃* alternatingGroup (Fin 5)) {x y : U ≃ₗ[ZMod p] U} {v w : alternatingGroup (Fin 5)}
    (hx : autGL e x = (-1) * ((e5.symm v : H) : GL (Fin 3) (ZMod p)))
    (hy : autGL e y = (-1) * ((e5.symm w : H) : GL (Fin 3) (ZMod p)))
    (hv : Commute v w) : Commute x y :=
  (commute_iff_of_autGL_eq_neg_mul e hx hy).mpr (by
    rw [commute_iff_eq]
    have hH : (e5.symm v : H) * (e5.symm w : H) = (e5.symm w : H) * (e5.symm v : H) := by
      rw [commute_iff_eq] at hv
      rw [← map_mul, ← map_mul, hv]
    simpa using congrArg Subtype.val hH)

private lemma rfr_a5_order_lift (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {H : Subgroup (GL (Fin 3) (ZMod p))}
    (e5 : H ≃* alternatingGroup (Fin 5)) {x y : U ≃ₗ[ZMod p] U} {v w : alternatingGroup (Fin 5)}
    (hx : autGL e x = (-1) * ((e5.symm v : H) : GL (Fin 3) (ZMod p)))
    (hy : autGL e y = (-1) * ((e5.symm w : H) : GL (Fin 3) (ZMod p))) {q : ℕ}
    (hv : orderOf (v * w) = q) : orderOf (x * y) = q := by
  rw [orderOf_mul_eq_of_autGL_eq_neg_mul e hx hy]
  have hcoe : ((e5.symm v : H) : GL (Fin 3) (ZMod p)) *
      ((e5.symm w : H) : GL (Fin 3) (ZMod p)) =
        ((e5.symm (v * w) : H) : GL (Fin 3) (ZMod p)) := by
    have hH : (e5.symm v : H) * (e5.symm w : H) = e5.symm (v * w) := by
      rw [map_mul]
    exact congrArg Subtype.val hH
  rw [hcoe, Subgroup.orderOf_coe]
  exact (MulEquiv.orderOf_eq e5.symm (v * w)).trans hv

theorem h3Frame_of_alternatingFive (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ A.map (autGL e).toMonoidHom)
    (hirr : IsIrreducibleMatrixRep H.subtype) (e5 : H ≃* alternatingGroup (Fin 5))
    (hdec : ∀ g ∈ A.map (autGL e).toMonoidHom, ∃ h ∈ H, ∃ z ∈ A.map (autGL e).toMonoidHom,
      (∀ y ∈ A.map (autGL e).toMonoidHom, z * y = y * z) ∧ g = h * z) :
    H3Frame p A := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
  let : Group.IsPerfect H :=
    Group.IsPerfect.ofSurjective (f := e5.symm.toMonoidHom) e5.symm.surjective
  have hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := a5_noncomm_z5
    refine ⟨(e5.symm x : GL (Fin 3) (ZMod p)), (e5.symm x).2,
      (e5.symm y : GL (Fin 3) (ZMod p)), (e5.symm y).2, fun h => hxy ?_⟩
    have h' : (e5.symm x : H) * (e5.symm y : H) = (e5.symm y : H) * (e5.symm x : H) :=
      Subtype.ext h
    simpa using congrArg e5 h'
  have hdec' : ∀ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t →
      ∃ h ∈ H, ∃ z : GL (Fin 3) (ZMod p), (∀ x ∈ H, z * x = x * z) ∧ t = h * z := by
    intro t ht _
    obtain ⟨h, hh, z, _, hzc, htz⟩ := hdec t ht
    exact ⟨h, hh, z, fun x hx => hzc x (hHG hx), htz⟩
  have hinn : ∀ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t →
      ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹ := by
    intro t ht hrefl
    obtain ⟨h, hh, z, hzc, htz⟩ := hdec' t ht hrefl
    refine ⟨h, hh, fun x hx => ?_⟩
    rw [htz]
    calc h * z * x * (h * z)⁻¹ = h * (z * x * z⁻¹) * h⁻¹ := by group
      _ = h * x * h⁻¹ := by rw [hzc x hx]; group
  obtain ⟨hv02, hv01, hv12, hv11, hv22, hv21, hu2, hu1⟩ := rfr_a5_invol
  obtain ⟨hc01, hc02, hc12, hcomm01, hcomm02, hcomm12⟩ := rfr_a5_comm
  obtain ⟨h0, h0A, hr0, hh0⟩ := rfr_a5_lift hp e hR hI hHG hirr hnc hinn e5 hv02 hv01
  obtain ⟨h1, h1A, hr1, hh1⟩ := rfr_a5_lift hp e hR hI hHG hirr hnc hinn e5 hv12 hv11
  obtain ⟨h2, h2A, hr2, hh2⟩ := rfr_a5_lift hp e hR hI hHG hirr hnc hinn e5 hv22 hv21
  obtain ⟨a, aA, hra, hha⟩ := rfr_a5_lift hp e hR hI hHG hirr hnc hinn e5 hu2 hu1
  exact ⟨h0, h0A, h1, h1A, h2, h2A, a, aA, hr0, hr1, hr2, hra,
    rfr_a5_ne_lift e e5 hh0 hh1 hc01, rfr_a5_ne_lift e e5 hh0 hh2 hc02,
    rfr_a5_ne_lift e e5 hh1 hh2 hc12,
    rfr_a5_commute_lift e e5 hh0 hh1 hcomm01,
    rfr_a5_commute_lift e e5 hh0 hh2 hcomm02,
    rfr_a5_commute_lift e e5 hh1 hh2 hcomm12,
    rfr_a5_order_lift e e5 hh0 hha rfr_a5_order0,
    rfr_a5_order_lift e e5 hh1 hha rfr_a5_order1,
    rfr_a5_order_lift e e5 hh2 hha rfr_a5_order2⟩

private lemma preimage_central_pow_two_z5 (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hcen : Nat.card (Subgroup.center A) = 2)
    {z : GL (Fin 3) (ZMod p)} (hzG : z ∈ A.map (autGL e).toMonoidHom)
    (hzcomm : ∀ y ∈ A.map (autGL e).toMonoidHom, z * y = y * z) :
    ∃ a ∈ A, (autGL e) a = z ∧ a * a = 1 := by
  obtain ⟨a, haA, haz⟩ := Subgroup.mem_map.mp hzG
  have haz' : (autGL e) a = z := haz
  have hacent : (⟨a, haA⟩ : A) ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : autGL e (a * (y : U ≃ₗ[ZMod p] U)) = autGL e ((y : U ≃ₗ[ZMod p] U) * a) := by
      rw [map_mul, map_mul, haz']
      exact hzcomm (autGL e (y : U ≃ₗ[ZMod p] U)) (Subgroup.mem_map_of_mem _ y.2)
    exact Subtype.ext (((autGL e).injective hy).symm)
  have ha2 : a * a = 1 := by
    have h1 := orderOf_dvd_natCard (⟨⟨a, haA⟩, hacent⟩ : Subgroup.center A)
    rw [hcen] at h1
    have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
    simpa [pow_two] using
      congrArg (fun w : Subgroup.center A => ((w : A) : U ≃ₗ[ZMod p] U)) h2
  exact ⟨a, haA, haz', ha2⟩

private lemma conj_inv_of_central_involution_z5 {G : Subgroup (GL (Fin 3) (ZMod p))}
    {h z k₀ : GL (Fin 3) (ZMod p)} (hhG : h ∈ G) (hkG : k₀ ∈ G)
    (hz : ∀ y ∈ G, z * y = y * z) (hzz : z * z = 1) (hk : k₀ * h * k₀⁻¹ = h⁻¹) :
    k₀ * (h * z) * k₀⁻¹ = (h * z)⁻¹ := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hkz : k₀ * z * k₀⁻¹ = z := by
    rw [← hz k₀ hkG]
    group
  have hL : k₀ * (h * z) * k₀⁻¹ = h⁻¹ * z := by
    calc k₀ * (h * z) * k₀⁻¹
        = (k₀ * h * k₀⁻¹) * (k₀ * z * k₀⁻¹) := by group
      _ = h⁻¹ * z := by rw [hk, hkz]
  have hR : (h * z)⁻¹ = h⁻¹ * z := by
    rw [mul_inv_rev, hzinv]
    calc z * h⁻¹ = h⁻¹ * (h * z) * h⁻¹ := by group
      _ = h⁻¹ * (z * h) * h⁻¹ := by rw [← hz h hhG]
      _ = h⁻¹ * z := by group
  rw [hL, hR]

theorem isConj_inv_of_alternatingFive (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ A.map (autGL e).toMonoidHom)
    (hirr : IsIrreducibleMatrixRep H.subtype) (e5 : H ≃* alternatingGroup (Fin 5))
    (hp10 : p % 10 = 1 ∨ p % 10 = 9)
    (hdec : ∀ g ∈ A.map (autGL e).toMonoidHom, ∃ h ∈ H, ∃ z ∈ A.map (autGL e).toMonoidHom,
      (∀ y ∈ A.map (autGL e).toMonoidHom, z * y = y * z) ∧ g = h * z) :
    ∀ g ∈ A, ∃ k ∈ A, k * g * k⁻¹ = g⁻¹ := by
  have hcen : Nat.card (Subgroup.center A) = 2 := by
    have h := (excData_of_alternatingFive hp e hR hI hHG hirr e5 hp10 hdec).2.2.2.1
    rw [h]
    norm_num [ExcRow.cen]
  intro g hgA
  obtain ⟨h, hhH, z, hzG, hzcomm, hgz⟩ := hdec (autGL e g) (Subgroup.mem_map_of_mem _ hgA)
  obtain ⟨a, haA, haz, ha2⟩ := preimage_central_pow_two_z5 e hcen hzG hzcomm
  have hzz : z * z = 1 := by
    rw [← haz, ← map_mul, ha2, map_one]
  obtain ⟨y, hy⟩ := a5_ambivalent_z5 (e5 ⟨h, hhH⟩)
  have hk₀H : (e5.symm y : GL (Fin 3) (ZMod p)) ∈ H := (e5.symm y).2
  have hk₀ : (e5.symm y : GL (Fin 3) (ZMod p)) * h * (e5.symm y : GL (Fin 3) (ZMod p))⁻¹
      = h⁻¹ := by
    have h1 : (e5.symm y : H) * ⟨h, hhH⟩ * (e5.symm y : H)⁻¹ = ⟨h, hhH⟩⁻¹ := by
      apply e5.injective
      simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hy
    simpa using congrArg (fun w : H => (w : GL (Fin 3) (ZMod p))) h1
  obtain ⟨k, hkA, hkmap⟩ := Subgroup.mem_map.mp (hHG hk₀H)
  have hkmap' : (autGL e) k = (e5.symm y : GL (Fin 3) (ZMod p)) := hkmap
  refine ⟨k, hkA, ?_⟩
  have hL : (autGL e) (k * g * k⁻¹) = (h * z)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hkmap', hgz]
    exact conj_inv_of_central_involution_z5 (hHG hhH) (hHG hk₀H) hzcomm hzz hk₀
  have hR : (autGL e) g⁻¹ = (h * z)⁻¹ :=
    (MulEquiv.map_inv (autGL e) g).trans (congrArg Inv.inv hgz)
  exact (autGL e).injective (hL.trans hR.symm)

end CFSG.StandardType.ZS.DimThree
