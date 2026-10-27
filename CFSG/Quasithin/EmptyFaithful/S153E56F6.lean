module

public import CFSG.Quasithin.EmptyFaithful.S153E56F4
public import CFSG.Quasithin.EmptyFaithful.S153E56F5

public section

namespace CFSG.Quasithin

namespace S153E56f

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits CFSG.Quasithin.S153E
open scoped commutatorElement Pointwise

section Steps

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y : G}

omit [Finite G] in
theorem J_le_YU (hyY : y ∈ Y153 Mc M) :
    Jgp153 T M V₁ Mc y ≤ Y153 Mc M ⊔ UH153 T M V₁ Mc := by
  refine sup_le le_sup_right fun x hx => ?_
  have hx' : y * x * y⁻¹ ∈ UH153 T M V₁ Mc := mem_conjSubgroup_iff.1 hx
  have e : x = y⁻¹ * (y * x * y⁻¹) * y := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hyY))
    (Subgroup.mem_sup_right hx')) (Subgroup.mem_sup_left hyY)

theorem P_le_centralizer {cx : Ctx15350 T Mc M V₁ V₂ t} (c : Chain15354 cx N₁ N₂ g s) :
    Pgp153 T M V₁ Mc g ≤ Subgroup.centralizer (VZ T M : Set G) := by
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (c.h54.two_center hv).2 p hp).symm

theorem exists_j₀ (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15355 cx N₁ N₂ g s)
    (hy : y ∈ Yi153 T Mc M V₁ N₁ ∧ y ∉ pCoreOf 2 (Yi153 T Mc M V₁ N₁)) :
    ∃ j₀ ∈ Jgp153 T M V₁ Mc y, y * j₀⁻¹ ∈ Pgp153 T M V₁ Mc g := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨hyN, hybN₁, hyb1, hyb3, -⟩ := yb_facts h113 cx c hy
  obtain ⟨a, b, haU, -, haN, -, ha1, -, haa, -, -, -⟩ := ubdata cx c.toChain15354.toChain15353
  obtain ⟨e₁⟩ := c.h53one.iso₁
  have hapa : a * cb cx y hyN * a⁻¹ = (cb cx y hyN)⁻¹ :=
    inv_of_invol (W := Wd cx) e₁ haN hybN₁ haa ha1 hyb3 hyb1
  obtain ⟨⟨ua, huaN⟩, huaU, hua⟩ := (mem_autI hV).1 haU
  have hyY : y ∈ Y153 Mc M := (oTwoUpper_le _ hy.1).1
  have hyYU : y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.mem_sup_left hyY
  have hconj : y⁻¹ * ua * y ∈ conjSubgroup (UH153 T M V₁ Mc) y := by
    rw [mem_conjSubgroup_iff]
    have e : y * (y⁻¹ * ua * y) * y⁻¹ = ua := by group
    rw [e]
    exact huaU
  have hj₁J : ua * (y⁻¹ * ua * y) ∈ Jgp153 T M V₁ Mc y := Subgroup.mul_mem_sup huaU hconj
  have hj₀J : (ua * (y⁻¹ * ua * y)) * (ua * (y⁻¹ * ua * y)) ∈ Jgp153 T M V₁ Mc y :=
    Subgroup.mul_mem _ hj₁J hj₁J
  refine ⟨(ua * (y⁻¹ * ua * y)) * (ua * (y⁻¹ * ua * y)), hj₀J, ?_⟩
  have hconjN : y⁻¹ * ua * y ∈ Subgroup.normalizer (VZ T M : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyN) huaN) hyN
  have hj₁N : ua * (y⁻¹ * ua * y) ∈ Subgroup.normalizer (VZ T M : Set G) :=
    Subgroup.mul_mem _ huaN hconjN
  have hj₀N : (ua * (y⁻¹ * ua * y)) * (ua * (y⁻¹ * ua * y)) ∈ Subgroup.normalizer (VZ T M : Set G) :=
    Subgroup.mul_mem _ hj₁N hj₁N
  have hcb₁ : cb cx (ua * (y⁻¹ * ua * y)) hj₁N = a * ((cb cx y hyN)⁻¹ * a * cb cx y hyN) := by
    rw [cb_mul cx ua (y⁻¹ * ua * y) huaN hconjN, cb_conj cx y ua hyN huaN hconjN]
    have h' : cb cx ua huaN = a := hua
    rw [h']
  have hcb₀ : cb cx ((ua * (y⁻¹ * ua * y)) * (ua * (y⁻¹ * ua * y))) hj₀N = cb cx y hyN := by
    rw [cb_mul cx _ _ hj₁N hj₁N, hcb₁, ← pow_two]
    exact lift_calc haa hapa hyb3
  have hC : y * ((ua * (y⁻¹ * ua * y)) * (ua * (y⁻¹ * ua * y)))⁻¹ ∈
      Subgroup.centralizer (VZ T M : Set G) := by
    have hN' : y * ((ua * (y⁻¹ * ua * y)) * (ua * (y⁻¹ * ua * y)))⁻¹ ∈
        Subgroup.normalizer (VZ T M : Set G) :=
      Subgroup.mul_mem _ hyN (Subgroup.inv_mem _ hj₀N)
    rw [← cb_eq_one_iff cx _ hN', cb_mul cx y _ hyN (Subgroup.inv_mem _ hj₀N),
      cb_inv cx _ hj₀N, hcb₀]
    exact mul_inv_cancel _
  exact S153E55.centralizer_le_P c.h54.one cx
    ⟨Subgroup.mul_mem _ hyYU (Subgroup.inv_mem _ (J_le_YU hyY hj₀J)), hC⟩

theorem comm_y_mem_V (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15355 cx N₁ N₂ g s)
    (hy : y ∈ Yi153 T Mc M V₁ N₁ ∧ y ∉ pCoreOf 2 (Yi153 T Mc M V₁ N₁))
    (iJ : JStruct56 T Mc M V₁ N₁ y) :
    ∀ e ∈ Egp153 T M V₁ Mc y ⊓ Pgp153 T M V₁ Mc g, e * y * e⁻¹ * y⁻¹ ∈ VZ T M := by
  intro e he
  obtain ⟨j₀, hj₀J, hp⟩ := exists_j₀ h113 cx c hy
  obtain ⟨hyN, -⟩ := yb_facts h113 cx c hy
  have hV0V : quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y ≤ VZ T M := by
    refine sup_le cx.c.hyp.Z_le_VZ fun x hx => ?_
    have hx' : y * x * y⁻¹ ∈ quasithinOmegaOneCenter T := mem_conjSubgroup_iff.1 hx
    have e' : x = y⁻¹ * (y * x * y⁻¹) * y := by group
    rw [e']
    exact conj_inv_mem_V hyN (cx.c.hyp.Z_le_VZ hx')
  have hcomm_j : e * j₀ * e⁻¹ * j₀⁻¹ ∈ VZ T M :=
    hV0V (iJ.E_comm (Subgroup.commutator_mem_commutator he.1 hj₀J))
  have pd := S153E55.pdecomp cx c.toChain15354
  have hPV : ∀ a ∈ Pgp153 T M V₁ Mc g, ∀ b ∈ Pgp153 T M V₁ Mc g, a * b * a⁻¹ * b⁻¹ ∈ VZ T M :=
    fun a ha b hb => pdecomp_comm_mem_V pd (comm_mem_of_nat c.h54.four_nat₁)
      (comm_mem_of_nat c.h54.four_nat₂) ha hb
  have hep : e * (y * j₀⁻¹) * e⁻¹ * (y * j₀⁻¹)⁻¹ ∈ VZ T M := hPV e he.2 _ hp
  have e1 : e * y * e⁻¹ * y⁻¹ = (e * (y * j₀⁻¹) * e⁻¹ * (y * j₀⁻¹)⁻¹) *
      ((y * j₀⁻¹) * (e * j₀ * e⁻¹ * j₀⁻¹) * (y * j₀⁻¹)⁻¹) := by group
  rw [e1]
  exact (VZ T M).mul_mem hep (pd.conj_V (pd.P_le_I hp) hcomm_j)

end Steps

end S153E56f

end CFSG.Quasithin
