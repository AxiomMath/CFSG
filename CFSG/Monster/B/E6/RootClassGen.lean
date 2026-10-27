module

public import CFSG.Monster.B.E6.GStarStructure
public import CFSG.Monster.B.E6.StdF4Points
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Monster.B.E6 CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension

theorem eq_one_of_forall_commute_inl
    {γ : GStar}
    (h : ∀ m : stdGroup, γ * SemidirectProduct.inl m = SemidirectProduct.inl m * γ) : γ = 1 := by
  have key : ∀ m : stdGroup, (γ.right : MulAut stdGroup) m = γ.left⁻¹ * m * γ.left := by
    intro m
    have h1 := congrArg SemidirectProduct.left (h m)
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply] at h1
    rw [show γ.left⁻¹ * m * γ.left = γ.left⁻¹ * (m * γ.left) by group, ← h1]
    simp only [inv_mul_cancel_left]
    rfl
  rcases mem_betaGroup_iff.1 γ.right.2 with hr | hr
  · have hc : γ.left ∈ Subgroup.center stdGroup := by
      rw [Subgroup.mem_center_iff]
      intro m
      have h1 := key m
      rw [hr, MulAut.one_apply] at h1
      calc m * γ.left = γ.left * (γ.left⁻¹ * m * γ.left) := by group
        _ = γ.left * m := by rw [← h1]
    rw [center_stdGroup, Subgroup.mem_bot] at hc
    exact SemidirectProduct.ext hc (Subtype.ext hr)
  · exfalso
    apply betaG_ne_conj γ.left⁻¹
    ext m
    rw [← hr, key m, MulAut.conj_apply, inv_inv]

theorem closure_rootClass :
    Subgroup.closure rootClass = ⊤ := by
  have hsub : Group.conjugatesOfSet rootClass ⊆ rootClass := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.1 hy
    exact IsConj.trans hx hxy
  have hle : Subgroup.normalClosure rootClass ≤ Subgroup.closure rootClass :=
    Subgroup.closure_mono hsub
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ stdGroup_isSimpleGroup _
      (Subgroup.normalClosure_normal (s := rootClass)) with h | h
  · exfalso
    have h1 : rootInv ∈ Subgroup.normalClosure rootClass :=
      Subgroup.subset_normalClosure (IsConj.refl rootInv)
    rw [h, Subgroup.mem_bot] at h1
    exact standard_F4_root_involution_point_geometry.2.1.2.1 h1
  · exact top_le_iff.1 (h ▸ hle)

theorem eq_one_of_forall_commute_rootClass
    {γ : GStar}
    (h : ∀ x ∈ rootClass, γ * SemidirectProduct.inl x = SemidirectProduct.inl x * γ) :
    γ = 1 := by
  apply eq_one_of_forall_commute_inl
  intro m
  have hm : m ∈ Subgroup.closure rootClass := closure_rootClass ▸ Subgroup.mem_top m
  induction hm using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => rw [map_one, mul_one, one_mul]
  | mul x y _ _ hx hy => rw [map_mul, ← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  | inv x _ hx =>
    rw [map_inv]
    calc γ * (SemidirectProduct.inl x)⁻¹
        = (SemidirectProduct.inl x)⁻¹ * (SemidirectProduct.inl x * γ) *
          (SemidirectProduct.inl x)⁻¹ := by group
      _ = (SemidirectProduct.inl x)⁻¹ * (γ * SemidirectProduct.inl x) *
          (SemidirectProduct.inl x)⁻¹ := by rw [hx]
      _ = (SemidirectProduct.inl x)⁻¹ * γ := by group

end CFSG.Monster.B.E6.StdF4
