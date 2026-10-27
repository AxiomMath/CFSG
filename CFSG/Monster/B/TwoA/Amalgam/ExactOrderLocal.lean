module

public import CFSG.Monster.B.TwoA.Amalgam.ExactOrderCore
public import CFSG.Monster.B.TwoA.Amalgam.OrderThree
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeTTCore

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar)
open CFSG.Monster.B.Classical.UnitarySix (IsoPt ProjSU tPt projAct LBeta extAct)

@[expose] def vxPerm
    (K : Subgroup Shat) (X : Set CVert)
    (hK : ∀ k ∈ K, ∀ x ∈ X, cvMul x k ∈ X) : K →* Equiv.Perm X where
  toFun k :=
    { toFun := fun x => ⟨cvMul x (k : Shat)⁻¹, hK _ (K.inv_mem k.2) x x.2⟩
      invFun := fun x => ⟨cvMul x k, hK _ k.2 x x.2⟩
      left_inv := fun x => Subtype.ext (cvMul_inv_cancel' _ _)
      right_inv := fun x => Subtype.ext (cvMul_inv_cancel _ _) }
  map_one' := Equiv.ext fun x => Subtype.ext (by
    show cvMul (x : CVert) ((1 : K) : Shat)⁻¹ = x
    rw [OneMemClass.coe_one, inv_one, cvMul_one])
  map_mul' a b := Equiv.ext fun x => Subtype.ext (by
    show cvMul (x : CVert) ((a * b : K) : Shat)⁻¹ = cvMul (cvMul x (b : Shat)⁻¹) (a : Shat)⁻¹
    rw [Subgroup.coe_mul, mul_inv_rev, cvMul_mul])

theorem coe_vxPerm
    (K : Subgroup Shat) (X : Set CVert) (hK : ∀ k ∈ K, ∀ x ∈ X, cvMul x k ∈ X)
    (k : K) (x : X) : ((vxPerm K X hK k x : X) : CVert) = cvMul x (k : Shat)⁻¹ := rfl

namespace LocalHom

variable {v : CVert} (L : LocalHom v)

theorem rho_mem_range_of_mem_cnGroup
    {w : CVert} (y : L.stab) (hy : (y : Shat) ∈ cnGroup v w) :
    L.rho y ∈ (SemidirectProduct.inl : stdGroup →* GStar).range := by
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  have hle : ∀ x ∈ cnGroup v w, x ∈ L.stab := fun x hx =>
    (L.mem_stab x).2 (Subgroup.mem_inf.1 (cnGroup_le H v w hx)).1
  have key : ∀ x (hx : x ∈ Subgroup.closure (cnLabels v w)) (hxv : x ∈ L.stab),
      L.rho ⟨x, hxv⟩ ∈ (SemidirectProduct.inl : stdGroup →* GStar).range := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := hz
      intro hxv
      rw [L.rho_clabel ⟨u, hu.1⟩ ⟨_, hxv⟩ rfl]
      exact MonoidHom.mem_range.2 ⟨_, rfl⟩
    | one =>
      intro hxv
      rw [show (⟨1, hxv⟩ : L.stab) = 1 from rfl, map_one]
      exact one_mem _
    | mul x z hx hz ihx ihz =>
      intro hxv
      rw [show (⟨x * z, hxv⟩ : L.stab) = ⟨x, hle x hx⟩ * ⟨z, hle z hz⟩ from rfl, map_mul]
      exact mul_mem (ihx _) (ihz _)
    | inv x hx ihx =>
      intro hxv
      rw [show (⟨x⁻¹, hxv⟩ : L.stab) = (⟨x, hle x hx⟩)⁻¹ from rfl, map_inv]
      exact inv_mem (ihx _)
  exact key _ hy y.2

theorem eq_one_of_rho_eq_one
    {w : CVert} (hw : w ∈ sphereThree v) (y : L.stab)
    (hyw : cvMul w (y : Shat) = w) (h1 : L.rho y = 1) : y = 1 := by
  have hz := L.mem_zpowers_of_rho_eq_one h1
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf L.orderOf_clabel hz with h | h
  · exact Subtype.ext (Subtype.ext h)
  · exfalso
    have hyS : (y : Shat) = clabelS v := Subtype.ext h
    rw [hyS] at hyw
    exact ((native_order_three_label_products_and_dihedral_triples v).2.1 w hw).2.1 hyw

end LocalHom

section Local

variable {v w u : CVert}

theorem cvMul_mem_slice
    {y : Shat} (hy : y ∈ vStab v ⊓ vStab w ⊓ vStab u) {x : CVert}
    (hx : x ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) :
    cvMul x y ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w := by
  obtain ⟨⟨hyv, hyw⟩, hyu⟩ := hy
  refine ⟨?_, cvMul_mem_commonNeighbors hyv hyw hx.2⟩
  have h := (cgraph_adj_cvMul u x y).2 hx.1
  rwa [show cvMul u y = u from hyu] at h

theorem clabelS_mem_stab3
    (hu : u ∈ cgraph.commonNeighbors v w) :
    clabelS u ∈ vStab v ⊓ vStab w ⊓ vStab u := by
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  refine ⟨⟨?_, ?_⟩, cvMul_clabelS_self H u⟩
  · exact cvMul_clabelS_of_mem H ((cgraph.mem_neighborSet _ _).2 (hu.1 : cgraph.Adj v u).symm)
  · exact cvMul_clabelS_of_mem H ((cgraph.mem_neighborSet _ _).2 (hu.2 : cgraph.Adj w u).symm)

theorem zpowers_clabelS_le_stab3
    (hu : u ∈ cgraph.commonNeighbors v w) :
    Subgroup.zpowers (clabelS u) ≤ vStab v ⊓ vStab w ⊓ vStab u :=
  Subgroup.zpowers_le.2 (clabelS_mem_stab3 hu)

theorem stab3_le_stab
    (L : LocalHom v) : vStab v ⊓ vStab w ⊓ vStab u ≤ L.stab := fun y hy =>
  (L.mem_stab y).2 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hy).1).1

variable (hw : w ∈ sphereThree v) (hu : u ∈ cgraph.commonNeighbors v w)
include hw hu

theorem exists_cvMul_eq_of_mem_slice
    {x x' : CVert}
    (hx : x ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w)
    (hx' : x' ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) :
    ∃ y ∈ vStab v ⊓ vStab w ⊓ vStab u, cvMul x y = x' := by
  obtain ⟨-, -, -, ι, φ, hφs, -, -, hι⟩ :=
    (native_order_three_common_neighbor_local_unitary_graph.2.2 v w hw).2.2.2.2 u hu
  obtain ⟨a, ha⟩ := CFSG.Monster.B.Classical.UnitarySix.projAct_transitive (ι ⟨x', hx'⟩)
    (ι ⟨x, hx⟩)
  obtain ⟨y, hy⟩ := hφs (SemidirectProduct.inl a)
  have h := hι y ⟨x, hx⟩ (cvMul_mem_slice y.2 hx)
  rw [hy, CFSG.Monster.B.Classical.UnitarySix.extAct_inl, ← ha, ← Equiv.Perm.mul_apply,
    inv_mul_cancel, Equiv.Perm.one_apply] at h
  exact ⟨y, y.2, congrArg Subtype.val (ι.injective h)⟩

theorem fix_slice_iff
    {y : Shat} (hy : y ∈ vStab v ⊓ vStab w ⊓ vStab u) :
    (∀ x ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w, cvMul x y = x) ↔
      y ∈ Subgroup.zpowers (clabelS u) := by
  have hker := ((native_order_three_common_neighbor_local_unitary_graph.2.2 v w hw).2.2.2.2 u
    hu).2.1
  rw [mem_zpowers_subtype_iff]
  exact ⟨fun h => (hker y).1 ⟨hy, h⟩, fun h => ((hker y).2 h).2⟩

theorem ncard_slice :
    (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w).ncard = 693 :=
  ((native_order_three_common_neighbor_local_unitary_graph.2.2 v w hw).2.2.2.2 u hu).1

theorem natCard_stab3 :
    Nat.card (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat) = 36787322880 :=
  ((native_order_three_common_neighbor_local_unitary_graph.2.2 v w hw).2.2.2.2 u hu).2.2.1

theorem mem_zpowers_of_normal_two
    (N : Subgroup (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat))
    (hN : N.Normal) (h2 : IsPGroup 2 N) {n : (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat)}
    (hn : n ∈ N) : (n : Shat) ∈ Subgroup.zpowers (clabelS u) := by
  let ρ := (vxPerm (vStab v ⊓ vStab w ⊓ vStab u) (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w)
    fun k hk x hx => cvMul_mem_slice hk hx).comp N.subtype
  let : MulAction N ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) :=
    MulAction.compHom _ ρ
  have hodd : ¬ 2 ∣ Nat.card ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) := by
    rw [Nat.card_coe_set_eq, ncard_slice hw hu]
    decide
  obtain ⟨x₀, hx₀⟩ := h2.nonempty_fixed_point_of_prime_not_dvd_card _ hodd
  have hfix₀ : ∀ m : N, cvMul (x₀ : CVert)
      ((m : (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat)) : Shat) = x₀ := by
    intro m
    have h := congrArg Subtype.val (hx₀ m⁻¹)
    change cvMul (x₀ : CVert)
      (((m⁻¹ : N) : (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat)) : Shat)⁻¹ = x₀ at h
    rwa [InvMemClass.coe_inv, InvMemClass.coe_inv, inv_inv] at h
  refine (fix_slice_iff hw hu n.2).1 fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := exists_cvMul_eq_of_mem_slice hw hu x₀.2 hx
  have hconj : (⟨t, ht⟩ : (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat)) * n *
      (⟨t, ht⟩ : (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat))⁻¹ ∈ N := hN.conj_mem n hn _
  have h1 := hfix₀ ⟨_, hconj⟩
  calc cvMul (cvMul (x₀ : CVert) t) (n : Shat)
      = cvMul (cvMul (x₀ : CVert) (t * n * t⁻¹)) t := by
        rw [← cvMul_mul, ← cvMul_mul, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
    _ = cvMul (x₀ : CVert) t := by
        rw [show t * n * t⁻¹ = (((⟨_, hconj⟩ : N) : (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat)) :
          Shat) from rfl, h1]

theorem pCore_stab3_eq :
    CFSG.pCore 2 (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat) =
      (Subgroup.zpowers (clabelS u)).subgroupOf (vStab v ⊓ vStab w ⊓ vStab u) := by
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  apply le_antisymm
  · refine sSup_le fun N hN n hn => ?_
    exact Subgroup.mem_subgroupOf.2 (mem_zpowers_of_normal_two hw hu N hN.1 hN.2 hn)
  · refine le_sSup ⟨⟨fun n hn t => ?_⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn
      have hc : (t : Shat) * clabelS u * (t : Shat)⁻¹ = clabelS u := by
        have h := clabelS_cvMul u (t : Shat)⁻¹
        rw [inv_inv, show cvMul u (t : Shat)⁻¹ = u from
          (vStab u).inv_mem (Subgroup.mem_inf.1 t.2).2] at h
        exact h.symm
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hk, Subgroup.coe_inv, ← conj_zpow, hc]
    · have hcard : Nat.card ((Subgroup.zpowers (clabelS u)).subgroupOf
          (vStab v ⊓ vStab w ⊓ vStab u)) = 2 ^ 1 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_clabelS_le_stab3 hu)).toEquiv,
          Nat.card_zpowers, ← Subgroup.orderOf_coe, coe_clabelS, (H u).orderOf_clabel, pow_one]
      exact IsPGroup.of_card hcard

theorem natCard_le_two_of_normal_two
    (N : Subgroup (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat))
    (hN : N.Normal) (h2 : IsPGroup 2 N) : Nat.card N ≤ 2 := by
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  have hle : N ≤ (Subgroup.zpowers (clabelS u)).subgroupOf (vStab v ⊓ vStab w ⊓ vStab u) :=
    fun n hn => Subgroup.mem_subgroupOf.2 (mem_zpowers_of_normal_two hw hu N hN h2 hn)
  calc Nat.card N ≤ Nat.card ((Subgroup.zpowers (clabelS u)).subgroupOf
        (vStab v ⊓ vStab w ⊓ vStab u)) := Subgroup.card_le_of_le hle
    _ = 2 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_clabelS_le_stab3 hu)).toEquiv,
          Nat.card_zpowers, ← Subgroup.orderOf_coe, coe_clabelS, (H u).orderOf_clabel]

theorem exists_rho_not_mem_range
    (L : LocalHom v) :
    ∃ y : (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat),
      L.rho.comp (Subgroup.inclusion (stab3_le_stab L)) y ∉
        (SemidirectProduct.inl : stdGroup →* GStar).range := by
  by_contra hcon
  push Not at hcon
  have hψ : Function.Injective
      (L.rho.comp (Subgroup.inclusion (stab3_le_stab (w := w) (u := u) L))) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h := L.eq_one_of_rho_eq_one hw (Subgroup.inclusion (stab3_le_stab L) y)
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 y.2).1).2 hy
    exact Subtype.ext (congrArg (fun z : L.stab => (z : Shat)) h)
  have hc : ∀ y : (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat),
      L.rho.comp (Subgroup.inclusion (stab3_le_stab L)) y * L.pt ⟨u, hu.1⟩ =
        L.pt ⟨u, hu.1⟩ * L.rho.comp (Subgroup.inclusion (stab3_le_stab L)) y := fun y =>
    (L.cvMul_eq_self_iff (Subgroup.inclusion (stab3_le_stab L) y) ⟨u, hu.1⟩).1
      (Subgroup.mem_inf.1 y.2).2
  have h := card_le_of_commute_rootClass _ hψ hcon (L.iv ⟨u, hu.1⟩).2 hc
    (natCard_le_two_of_normal_two hw hu)
  rw [natCard_stab3 hw hu] at h
  exact absurd h (by norm_num)

end Local

end CFSG.Monster.B.TwoA.Amalgam
