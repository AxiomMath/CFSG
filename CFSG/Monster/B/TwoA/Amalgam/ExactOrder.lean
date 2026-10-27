module

public import CFSG.Monster.B.TwoA.Amalgam.ExactOrderChart
public import CFSG.Monster.B.TwoA.Amalgam.Exact3510
public import CFSG.Monster.B.TwoA.Amalgam.ExactOrderLocal
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeTT

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar)
open CFSG.Monster.B.Classical.UnitarySix (IsoPt ProjSU tPt projAct)

instance zpowers_clabelS_subgroupOf_normal
    (v w u : CVert) :
    ((Subgroup.zpowers (clabelS u)).subgroupOf (cnGroup v w ⊓ vStab u)).Normal := by
  refine ⟨fun n hn t => ?_⟩
  have ht : cvMul u (t : Shat)⁻¹ = u :=
    mem_vStab.1 ((vStab u).inv_mem (Subgroup.mem_inf.1 t.2).2)
  have hc : (t : Shat) * clabelS u * (t : Shat)⁻¹ = clabelS u := by
    have h := (congrArg clabelS ht).symm.trans (clabelS_cvMul u (t : Shat)⁻¹)
    simp only [inv_inv] at h
    exact h.symm
  have hn' := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hn)
  obtain ⟨k, hk⟩ := hn'
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩)
  have e : clabelS u ^ k = (t : Shat) * (n : Shat) * (t : Shat)⁻¹ :=
    (congrArg (· ^ k) hc).symm.trans
      (conj_zpow.trans (congrArg (fun x => (t : Shat) * x * (t : Shat)⁻¹) hk))
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using e

section Main

variable {v w : CVert} (hw : w ∈ sphereThree v)
include hw

theorem exists_mem_cnGroup_cvMul_eq
    {u z : CVert} (hu : u ∈ cgraph.commonNeighbors v w)
    (hz : z ∈ cgraph.commonNeighbors v w) : ∃ h ∈ cnGroup v w, cvMul u h = z := by
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  obtain ⟨-, -, -, -, -, hcl, -⟩ :=
    native_order_three_common_neighbor_three_transposition_group.choose_spec.2 v w hw
  have hmem : clabelS z ∈ cnLabels v w := ⟨z, hz, rfl⟩
  rw [hcl u hu] at hmem
  obtain ⟨h, hh, he⟩ := hmem
  refine ⟨h, hh, ?_⟩
  have hhQ := Subgroup.mem_inf.1 (cnGroup_le H v w hh)
  have hC := cvMul_mem_commonNeighbors (mem_vStab.1 hhQ.1) (mem_vStab.1 hhQ.2) hu
  refine clabel_injOn_neighborSet v hC.1 hz.1 ?_
  rw [clabel_cvMul, ← coe_clabelS z, he, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_clabelS]

theorem natCard_cnGroup_eq_mul
    {u : CVert} (hu : u ∈ cgraph.commonNeighbors v w) :
    Nat.card (cnGroup v w) = 3510 * Nat.card (cnGroup v w ⊓ vStab u : Subgroup Shat) := by
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  have horb : {x | ∃ s ∈ cnGroup v w, cvMul u s = x} = cgraph.commonNeighbors v w := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hsQ := Subgroup.mem_inf.1 (cnGroup_le H v w hs)
      exact cvMul_mem_commonNeighbors (mem_vStab.1 hsQ.1) (mem_vStab.1 hsQ.2) hu
    · intro hx
      exact exists_mem_cnGroup_cvMul_eq hw hu hx
  have hC : (cgraph.commonNeighbors v w).ncard = 3510 :=
    (native_order_three_common_neighbors_exact_3510.1 v w hw).2.2.1
  rw [natCard_subgroup_eq_mul _ u, horb, hC]

omit hw in
theorem cnStab_eq_inf_centralizer
    {u : CVert} (hu : u ∈ cgraph.commonNeighbors v w) :
    cnGroup v w ⊓ vStab u = cnGroup v w ⊓ Subgroup.centralizer {clabelS u} := by
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  ext y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, mem_vStab]
  refine and_congr_right fun hy => ?_
  have hyQ := Subgroup.mem_inf.1 (cnGroup_le H v w hy)
  have hC := cvMul_mem_commonNeighbors (mem_vStab.1 hyQ.1) (mem_vStab.1 hyQ.2) hu
  have e := clabelS_cvMul u y
  constructor
  · intro h
    rw [h] at e
    calc y * clabelS u = y * (y⁻¹ * clabelS u * y) := by rw [← e]
      _ = clabelS u * y := by group
  · intro h
    refine clabel_injOn_neighborSet v hC.1 hu.1 ?_
    rw [← coe_clabelS, ← coe_clabelS, e, mul_assoc, ← h, inv_mul_cancel_left]

theorem natCard_cnStab_and_mem
    (L : LocalHom v) {u : CVert}
    (hu : u ∈ cgraph.commonNeighbors v w) :
    Nat.card (cnGroup v w ⊓ vStab u : Subgroup Shat) = 18393661440 ∧
    ∀ (y : Shat) (_ : y ∈ vStab v ⊓ vStab w ⊓ vStab u) (hyL : y ∈ L.stab),
      L.rho ⟨y, hyL⟩ ∈ (SemidirectProduct.inl : stdGroup →* GStar).range → y ∈ cnGroup v w := by
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  have hkey := card_ker_rightHom_mul_two
    (L.rho.comp (Subgroup.inclusion (stab3_le_stab (w := w) (u := u) L)))
    (exists_rho_not_mem_range hw hu L)
  have hT := natCard_stab3 hw hu
  have hmemK : ∀ y : (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat),
      y ∈ (SemidirectProduct.rightHom.comp
        (L.rho.comp (Subgroup.inclusion (stab3_le_stab (w := w) (u := u) L)))).ker ↔
      L.rho (Subgroup.inclusion (stab3_le_stab (w := w) (u := u) L) y) ∈
        (SemidirectProduct.inl : stdGroup →* GStar).range := fun y =>
    (MonoidHom.mem_ker.trans (MonoidHom.mem_ker (f := SemidirectProduct.rightHom)).symm).trans
      (SetLike.ext_iff.1 SemidirectProduct.range_inl_eq_ker_rightHom _).symm
  have hRT : cnGroup v w ⊓ vStab u ≤ vStab v ⊓ vStab w ⊓ vStab u := fun y hy =>
    ⟨cnGroup_le H v w hy.1, hy.2⟩
  have hle : (cnGroup v w ⊓ vStab u).subgroupOf (vStab v ⊓ vStab w ⊓ vStab u) ≤
      (SemidirectProduct.rightHom.comp
        (L.rho.comp (Subgroup.inclusion (stab3_le_stab (w := w) (u := u) L)))).ker := fun y hy =>
    (hmemK y).2 (L.rho_mem_range_of_mem_cnGroup _ (Subgroup.mem_subgroupOf.1 hy).1)
  have hcR : Nat.card ((cnGroup v w ⊓ vStab u).subgroupOf (vStab v ⊓ vStab w ⊓ vStab u)) =
      Nat.card (cnGroup v w ⊓ vStab u : Subgroup Shat) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRT).toEquiv
  have hup := Subgroup.card_le_of_le hle
  have hlow := two_mul_le_natCard_cnStab hw hu
  have hR : Nat.card (cnGroup v w ⊓ vStab u : Subgroup Shat) = 18393661440 := by omega
  have heq := Subgroup.eq_of_le_of_card_ge hle (by omega)
  refine ⟨hR, fun y hyT hyL hG => ?_⟩
  have hK := (hmemK ⟨y, hyT⟩).2 hG
  exact (Subgroup.mem_subgroupOf.1 ((SetLike.ext_iff.1 heq _).2 hK)).1

theorem natCard_cnGroup
    (L : LocalHom v) : Nat.card (cnGroup v w) = 64561751654400 := by
  obtain ⟨u, hu⟩ := (native_order_three_common_neighbor_local_unitary_graph.2.2 v w hw).1
  rw [natCard_cnGroup_eq_mul hw hu, (natCard_cnStab_and_mem hw L hu).1]

theorem mem_cnGroup_iff
    (L : LocalHom v) (y : L.stab) (hy : (y : Shat) ∈ vStab v ⊓ vStab w) :
    (y : Shat) ∈ cnGroup v w ↔ L.rho y ∈ (SemidirectProduct.inl : stdGroup →* GStar).range := by
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  refine ⟨L.rho_mem_range_of_mem_cnGroup y, fun hG => ?_⟩
  obtain ⟨u, hu⟩ := (native_order_three_common_neighbor_local_unitary_graph.2.2 v w hw).1
  have hyQ := Subgroup.mem_inf.1 hy
  obtain ⟨h, hh, hhu⟩ := exists_mem_cnGroup_cvMul_eq hw hu
    (cvMul_mem_commonNeighbors (mem_vStab.1 hyQ.1) (mem_vStab.1 hyQ.2) hu)
  have hhQ := Subgroup.mem_inf.1 (cnGroup_le H v w hh)
  have hhL : h ∈ L.stab := (L.mem_stab h).2 (mem_vStab.1 hhQ.1)
  have htu : cvMul u ((y : Shat) * h⁻¹) = u := by
    rw [cvMul_mul, ← hhu, cvMul_inv_cancel]
  have htT : (y : Shat) * h⁻¹ ∈ vStab v ⊓ vStab w ⊓ vStab u :=
    Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ hy (Subgroup.inv_mem _ (cnGroup_le H v w hh)),
      mem_vStab.2 htu⟩
  have htL : (y : Shat) * h⁻¹ ∈ L.stab := mul_mem y.2 (inv_mem hhL)
  have e1 : L.rho ⟨(y : Shat) * h⁻¹, htL⟩ = L.rho y * (L.rho ⟨h, hhL⟩)⁻¹ :=
    (map_mul L.rho y (⟨h, hhL⟩ : L.stab)⁻¹).trans (congrArg (L.rho y * ·) (map_inv L.rho _))
  have htG : L.rho ⟨(y : Shat) * h⁻¹, htL⟩ ∈ (SemidirectProduct.inl : stdGroup →* GStar).range :=
    (congrArg (· ∈ (SemidirectProduct.inl : stdGroup →* GStar).range) e1).mpr
      (mul_mem hG (inv_mem (L.rho_mem_range_of_mem_cnGroup ⟨h, hhL⟩ hh)))
  have htH := (natCard_cnStab_and_mem hw L hu).2 _ htT htL htG
  have e2 : (y : Shat) = (y : Shat) * h⁻¹ * h := by group
  exact (congrArg (· ∈ cnGroup v w) e2).mpr (mul_mem htH hh)

theorem relindex_cnGroup
    (L : LocalHom v) : (cnGroup v w).relIndex (vStab v ⊓ vStab w) = 2 := by
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  have hQ := (native_order_three_common_neighbors_exact_3510.1 v w hw).2.2.2.2.2
  have hH := natCard_cnGroup hw L
  have h := Subgroup.card_mul_index ((cnGroup v w).subgroupOf (vStab v ⊓ vStab w))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cnGroup_le H v w)).toEquiv, hH, hQ] at h
  rw [Subgroup.relIndex]
  omega

end Main

theorem native_three_transposition_group_exact_order :
    ∀ v w : CVert, w ∈ sphereThree v → ∀ L : LocalHom v,
      (∀ y : L.stab, (y : Shat) ∈ vStab v ⊓ vStab w → L.rho y = 1 → y = 1) ∧
      (∀ y : L.stab, (y : Shat) ∈ vStab v ⊓ vStab w →
        ((y : Shat) ∈ cnGroup v w ↔
          L.rho y ∈ (SemidirectProduct.inl : stdGroup →* GStar).range)) ∧
      (cnGroup v w).relIndex (vStab v ⊓ vStab w) = 2 ∧
      Nat.card (cnGroup v w) = 64561751654400 ∧
      ∀ u ∈ cgraph.commonNeighbors v w,
        cnGroup v w ⊓ vStab u = cnGroup v w ⊓ Subgroup.centralizer {clabelS u} ∧
        Nat.card (cnGroup v w ⊓ vStab u : Subgroup Shat) = 18393661440 ∧
        (∀ y ∈ cnGroup v w ⊓ vStab u,
          (∀ x ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w, cvMul x y = x) ↔
            y ∈ Subgroup.zpowers (clabelS u)) ∧
        (∃ (τ : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) ≃ IsoPt)
            (φ : (cnGroup v w ⊓ vStab u : Subgroup Shat) →* ProjSU),
          Function.Surjective φ ∧
          (∀ a, φ a = 1 ↔ (a : Shat) ∈ Subgroup.zpowers (clabelS u)) ∧
          (∀ (z : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w))
            (a : (cnGroup v w ⊓ vStab u : Subgroup Shat)), (a : Shat) = clabelS z →
              φ a = tPt (τ z)) ∧
          ∀ (a : (cnGroup v w ⊓ vStab u : Subgroup Shat))
            (x : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w))
            (h : cvMul (x : CVert) (a : Shat) ∈
              cgraph.neighborSet u ∩ cgraph.commonNeighbors v w),
            τ ⟨_, h⟩ = (projAct (φ a))⁻¹ (τ x)) ∧
        Nonempty ((cnGroup v w ⊓ vStab u : Subgroup Shat) ⧸
          (Subgroup.zpowers (clabelS u)).subgroupOf (cnGroup v w ⊓ vStab u) ≃* ProjSU) ∧
        CFSG.pCore 2 (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat) =
          (Subgroup.zpowers (clabelS u)).subgroupOf (vStab v ⊓ vStab w ⊓ vStab u) := by
  intro v w hw L
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  refine ⟨fun y hy h1 => L.eq_one_of_rho_eq_one hw y (Subgroup.mem_inf.1 hy).2 h1,
    mem_cnGroup_iff hw L, relindex_cnGroup hw L, natCard_cnGroup hw L, fun u hu => ?_⟩
  have hR := (natCard_cnStab_and_mem hw L hu).1
  have hch := exists_chart_of_natCard_le hw hu (hR.le.trans (by norm_num))
  obtain ⟨τ, φ, hφs, hφk, hφl, hφe⟩ := hch
  have hkerφ : φ.ker = (Subgroup.zpowers (clabelS u)).subgroupOf (cnGroup v w ⊓ vStab u) := by
    ext a
    exact MonoidHom.mem_ker.trans ((hφk a).trans Subgroup.mem_subgroupOf.symm)
  refine ⟨cnStab_eq_inf_centralizer hu, hR, fun y hy => ?_, ⟨τ, φ, hφs, hφk, hφl, hφe⟩,
    ⟨(QuotientGroup.quotientMulEquivOfEq hkerφ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)⟩, pCore_stab3_eq hw hu⟩
  exact fix_slice_iff hw hu ⟨cnGroup_le H v w hy.1, hy.2⟩

end CFSG.Monster.B.TwoA.Amalgam
