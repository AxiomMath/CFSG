module

public import CFSG.Monster.B.TwoA.Amalgam.OrderThree
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeTTCore

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar)

section Root

variable (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) {v : CVert} {s : Shat}
  (hs : cvMul cv0 s = v) (iv : cgraph.neighborSet v ≃ rootClass)

theorem rhoV_clabel
    (H1 : ∀ (e : Eam) (h : cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s ∈
        cgraph.neighborSet v),
      SemidirectProduct.inl (iv ⟨_, h⟩ : stdGroup) = θ (QuotientGroup.mk (xconj e)))
    (a : cgraph.neighborSet v) (y : vStab v) (hy : ((y : Shat) : Dfull) = clabel a) :
    rhoV θ hs y = SemidirectProduct.inl (iv a : stdGroup) := by
  obtain ⟨e, he⟩ := exists_eq_cvMul_nbr hs a.2
  have ha' : cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s ∈ cgraph.neighborSet v :=
    he ▸ a.2
  have haeq : a = ⟨_, ha'⟩ := Subtype.ext he
  have hcl : clabel a = (s : Dfull)⁻¹ * (cQ * ((e : Dfull)⁻¹ * xhat * e)) * s := by
    rw [he, clabel_cvMul, clabel_nbr]
  have hst : stabToEam hs y = cE' * xconj e := by
    apply Subtype.ext
    show ((s * y * s⁻¹ : Shat) : Dfull) = cQ * ((e : Dfull)⁻¹ * xhat * e)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hy, hcl]
    group
  have hmk : (QuotientGroup.mk (cE' * xconj e) : Eam ⧸ Subgroup.zpowers cE') =
      QuotientGroup.mk (xconj e) := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff cE').2 (Subgroup.mem_zpowers _), one_mul]
  show θ (QuotientGroup.mk (stabToEam hs y)) = _
  rw [hst, hmk, ← H1 e ha', haeq]

theorem rhoV_mem_range_of_mem_cnGroup (H : ∀ x : CVert, LocalHom x)
    (H1 : ∀ (e : Eam) (h : cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s ∈
        cgraph.neighborSet v),
      SemidirectProduct.inl (iv ⟨_, h⟩ : stdGroup) = θ (QuotientGroup.mk (xconj e)))
    {w : CVert} (y : vStab v) (hy : (y : Shat) ∈ cnGroup v w) :
    rhoV θ hs y ∈ (SemidirectProduct.inl : stdGroup →* GStar).range := by
  have hle : ∀ x ∈ cnGroup v w, x ∈ vStab v := fun x hx =>
    (Subgroup.mem_inf.1 (cnGroup_le H v w hx)).1
  have key : ∀ x (hx : x ∈ Subgroup.closure (cnLabels v w)) (hxv : x ∈ vStab v),
      rhoV θ hs ⟨x, hxv⟩ ∈ (SemidirectProduct.inl : stdGroup →* GStar).range := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := hz
      intro hxv
      rw [rhoV_clabel θ hs iv H1 ⟨u, hu.1⟩ ⟨_, hxv⟩ rfl]
      exact MonoidHom.mem_range.2 ⟨_, rfl⟩
    | one =>
      intro hxv
      rw [show (⟨1, hxv⟩ : vStab v) = 1 from rfl, map_one]
      exact one_mem _
    | mul x z hx hz ihx ihz =>
      intro hxv
      rw [show (⟨x * z, hxv⟩ : vStab v) = ⟨x, hle x hx⟩ * ⟨z, hle z hz⟩ from rfl, map_mul]
      exact mul_mem (ihx _) (ihz _)
    | inv x hx ihx =>
      intro hxv
      rw [show (⟨x⁻¹, hxv⟩ : vStab v) = (⟨x, hle x hx⟩)⁻¹ from rfl, map_inv]
      exact inv_mem (ihx _)
  exact key _ hy y.2

theorem eq_one_of_rhoV_eq_one
    {w : CVert} (hw : w ∈ sphereThree v)
    (H3 : ∀ (y : vStab v) (u : cgraph.neighborSet v),
      SemidirectProduct.inl (iv (stabAct y u) : stdGroup) =
        (rhoV θ hs y)⁻¹ * SemidirectProduct.inl (iv u : stdGroup) * rhoV θ hs y)
    (H5 : ∀ y : Shat, (cvMul v y = v ∧ ∀ u ∈ cgraph.neighborSet v, cvMul u y = u) ↔
      (y : Dfull) ∈ Subgroup.zpowers (clabel v))
    (y : vStab v) (hyw : cvMul w y = w) (h1 : rhoV θ hs y = 1) : y = 1 := by
  have hfix : ∀ u ∈ cgraph.neighborSet v, cvMul u y = u := by
    intro u hu
    have e := H3 y ⟨u, hu⟩
    rw [h1, inv_one, one_mul, mul_one] at e
    have e2 := iv.injective (Subtype.ext (SemidirectProduct.inl_injective e))
    exact congrArg Subtype.val e2
  have hz := (H5 y).1 ⟨mem_vStab.1 y.2, hfix⟩
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf (orderOf_clabel v) hz with h | h
  · exact Subtype.ext (Subtype.ext h)
  · exfalso
    have hyS : (y : Shat) = clabelS v := Subtype.ext h
    rw [hyS] at hyw
    exact ((native_order_three_label_products_and_dihedral_triples v).2.1 w hw).2.1 hyw

end Root

end CFSG.Monster.B.TwoA.Amalgam
