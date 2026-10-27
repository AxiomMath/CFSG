module

public import CFSG.Quasithin.Background.C126A5Lift2
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.Background.C1PackSubnormal

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 Equiv
  CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Lift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : Setting H T M V Y hV}
  {d : Data H T V Y hV}

variable (s) in
@[expose] def Jt : Subgroup G where
  carrier := {g | g ∈ H ∧ cv hV g ∈ autI hV (thompsonJ H)}
  one_mem' := ⟨H.one_mem, by
    rw [cv_of_mem hV (Subgroup.one_mem _)]
    exact (show convI hV (1 : Subgroup.normalizer (V : Set G)) = 1 from map_one _) ▸
      (autI hV (thompsonJ H)).one_mem⟩
  mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, by
    rw [cv_mul hV (s.H_le_N ha.1) (s.H_le_N hb.1)]; exact (autI hV (thompsonJ H)).mul_mem ha.2 hb.2⟩
  inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, by
    rw [cv_inv hV (s.H_le_N ha.1)]; exact (autI hV (thompsonJ H)).inv_mem ha.2⟩

theorem A₁_le_Jt : A₁ s d ≤ Jt s := fun _ ha => ⟨(mem_A₁.1 ha).1, d.L_J (mem_A₁.1 ha).2⟩

theorem Jt_le_H : Jt s ≤ H := fun _ hg => hg.1

theorem conj_mem_A₁ {j a : G} (hj : j ∈ Jt s) (ha : a ∈ A₁ s d) : j * a * j⁻¹ ∈ A₁ s d := by
  obtain ⟨haH, haL⟩ := mem_A₁.1 ha
  have hjN : cv hV j ∈ Subgroup.normalizer (d.L : Set (MulAut (IntMod V hV))) := d.J_N hj.2
  refine mem_A₁.2 ⟨H.mul_mem (H.mul_mem hj.1 haH) (H.inv_mem hj.1), ?_⟩
  rw [cv_mul hV (Subgroup.mul_mem _ (s.H_le_N hj.1) (s.H_le_N haH)) (s.H_le_N (H.inv_mem hj.1)),
    cv_mul hV (s.H_le_N hj.1) (s.H_le_N haH), cv_inv hV (s.H_le_N hj.1)]
  exact (Subgroup.mem_normalizer_iff.1 hjN (cv hV a)).1 haL

theorem Jt_normalizes_A₁ : Jt s ≤ Subgroup.normalizer (A₁ s d : Set G) := by
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => conj_mem_A₁ hj ha, fun h => ?_⟩
  have := conj_mem_A₁ (Subgroup.inv_mem _ hj) h
  simpa [mul_assoc] using this

theorem H_normalizes_Jt : H ≤ Subgroup.normalizer (Jt s : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ h ∈ H, ∀ j ∈ Jt s, h * j * h⁻¹ ∈ Jt s := by
    intro h hh j hj
    refine ⟨H.mul_mem (H.mul_mem hh hj.1) (H.inv_mem hh), ?_⟩
    obtain ⟨j₀, hj₀, hcv⟩ := (mem_autI_iff hV ((thompsonJ_le H).trans s.H_le_N)).1 hj.2
    have hj₀H : j₀ ∈ H := thompsonJ_le H hj₀
    have e : cv hV (h * j * h⁻¹) = cv hV (h * j₀ * h⁻¹) := by
      rw [cv_mul hV (Subgroup.mul_mem _ (s.H_le_N hh) (s.H_le_N hj.1)) (s.H_le_N (H.inv_mem hh)),
        cv_mul hV (s.H_le_N hh) (s.H_le_N hj.1),
        cv_mul hV (Subgroup.mul_mem _ (s.H_le_N hh) (s.H_le_N hj₀H)) (s.H_le_N (H.inv_mem hh)),
        cv_mul hV (s.H_le_N hh) (s.H_le_N hj₀H), hcv]
    rw [e]
    have hmem : h * j₀ * h⁻¹ ∈ thompsonJ H :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_thompsonJ H hh) j₀).1 hj₀
    exact (mem_autI_iff hV ((thompsonJ_le H).trans s.H_le_N)).2 ⟨_, hmem, rfl⟩
  intro j
  exact ⟨fun hj => key h hh j hj, fun hj => by
    simpa [mul_assoc] using key h⁻¹ (H.inv_mem hh) _ hj⟩

namespace XData

variable {x : G} (hx : XData s d x)

include hx

theorem Khat_normal_in_A₁ : ((Khat s d x).subgroupOf (A₁ s d)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hx.Khat_le_A₁).2 hx.A₁_le_normalizer_Khat

theorem Khat_isSubnormal : IsSubnormal (Khat s d x) H := by
  refine IsSubnormal.step hx.Khat_le_A₁ hx.Khat_normal_in_A₁ ?_
  refine IsSubnormal.step A₁_le_Jt ((Subgroup.normal_subgroupOf_iff_le_normalizer A₁_le_Jt).2
    Jt_normalizes_A₁) ?_
  exact IsSubnormal.step Jt_le_H ((Subgroup.normal_subgroupOf_iff_le_normalizer Jt_le_H).2
    H_normalizes_Jt) (IsSubnormal.refl H)

theorem Khat_subgroupOf_isSubnormal : ((Khat s d x).subgroupOf H).IsSubnormal := by
  have h1 : ((Khat s d x).subgroupOf (A₁ s d)).IsSubnormal := hx.Khat_normal_in_A₁.isSubnormal
  have h2 : ((A₁ s d).subgroupOf (Jt s)).IsSubnormal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer A₁_le_Jt).2 Jt_normalizes_A₁).isSubnormal
  have h3 : ((Jt s).subgroupOf H).IsSubnormal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer Jt_le_H).2 H_normalizes_Jt).isSubnormal
  exact C1Pack.isSubnormal_subgroupOf_trans' (hx.Khat_le_A₁.trans A₁_le_Jt) Jt_le_H
    (C1Pack.isSubnormal_subgroupOf_trans' hx.Khat_le_A₁ A₁_le_Jt h1 h2) h3

theorem charTwo_Khat : CharTwo (Khat s d x) :=
  A4.charTwo_of_subnormal hx.Khat_isSubnormal s.charTwo

theorem pCoreOf_Khat : pCoreOf 2 (Khat s d x) = Khat s d x ⊓ pCoreOf 2 H := by
  apply le_antisymm
  · exact le_inf (pCoreOf_le 2 _) (A4.pCoreOf_le_of_subnormal 2 hx.Khat_isSubnormal)
  · refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
    intro k hk
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hk, le_normalizer_pCoreOf 2 H (hx.Khat_le_H hk)⟩

end XData

end Lift

end CFSG.Quasithin.C126.A5
