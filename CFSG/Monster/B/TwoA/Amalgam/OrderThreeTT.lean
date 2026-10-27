module

public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeTTLocal
public import CFSG.Blueprint.FischerDefs
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeTTCo

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar)

theorem orderOf_clabelS
    (u : CVert) : orderOf (clabelS u) = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_clabel u

@[expose] def cnClass
    (v w : CVert) : Set (cnGroup v w) := {x | (x : Shat) ∈ cnLabels v w}

theorem pair_cnClass
    (H : ∀ x : CVert, LocalHom x) {v w : CVert} (hw : w ∈ sphereThree v) :
    CFSG.Blueprint.Fischer.Pair (cnGroup v w) (cnClass v w) := by
  obtain ⟨-, -, u₀, hvu, huw⟩ := cgraph_dist_eq_two_iff.1 hw.1
  have hu₀ : u₀ ∈ cgraph.commonNeighbors v w := ⟨hvu, huw.symm⟩
  refine ⟨inferInstance, ⟨⟨clabelS u₀, clabelS_mem_cnGroup hu₀⟩, ?_⟩, fun e he => ?_,
    fun e he f hf => ?_, Subgroup.closure_closure_coe_preimage⟩
  · ext x
    rw [Set.mem_ofPred_eq, isConj_iff]
    show (x : Shat) ∈ cnLabels v w ↔ _
    rw [cnLabels_eq_conj H hw hu₀]
    constructor
    · rintro ⟨h, hh, hx⟩
      refine ⟨⟨h, hh⟩⁻¹, Subtype.ext ?_⟩
      rw [hx]
      show h⁻¹ * clabelS u₀ * h⁻¹⁻¹ = h⁻¹ * clabelS u₀ * h
      rw [inv_inv]
    · rintro ⟨c, rfl⟩
      refine ⟨(c : Shat)⁻¹, inv_mem c.2, ?_⟩
      show (c : Shat) * clabelS u₀ * (c : Shat)⁻¹ = (c : Shat)⁻¹⁻¹ * clabelS u₀ * (c : Shat)⁻¹
      rw [inv_inv]
  · obtain ⟨u, -, hue⟩ := he
    rw [← Subgroup.orderOf_coe, ← hue]
    exact orderOf_clabelS u
  · obtain ⟨u, hu, hue⟩ := he
    obtain ⟨z, hz, hzf⟩ := hf
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, ← hue, ← hzf]
    by_cases huz : u = z
    · subst huz
      exact Or.inl (by rw [clabelS_mul_self H u, orderOf_one])
    · by_cases hadj : cgraph.Adj u z
      · refine Or.inr (Or.inl ?_)
        rw [← Subgroup.orderOf_coe]
        exact (orderOf_clabel_mul_of_adj hadj).2.2
      · refine Or.inr (Or.inr ?_)
        rw [← Subgroup.orderOf_coe]
        exact orderOf_clabel_mul_of_not_adj hw hu hz huz hadj

theorem native_order_three_common_neighbor_three_transposition_group :
    ∃ θ₀ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar, θ₀ (QuotientGroup.mk xhatEam) = rootStar ∧
    ∀ v w : CVert, w ∈ sphereThree v →
      cnGroup v w ≤ vStab v ⊓ vStab w ∧
      ((cnGroup v w).subgroupOf (vStab v ⊓ vStab w)).Normal ∧
      (∀ h ∈ cnGroup v w, (∀ x ∈ cgraph.commonNeighbors v w, cvMul x h = x) → h = 1) ∧
      Set.InjOn clabelS (cgraph.commonNeighbors v w) ∧
      (∀ u ∈ cgraph.commonNeighbors v w, orderOf (clabelS u) = 2) ∧
      (∀ u ∈ cgraph.commonNeighbors v w,
        cnLabels v w = {y | ∃ h ∈ cnGroup v w, y = h⁻¹ * clabelS u * h}) ∧
      (∀ u ∈ cgraph.commonNeighbors v w, ∀ z ∈ cgraph.commonNeighbors v w, u ≠ z →
        (cgraph.Adj u z → orderOf (clabelS u * clabelS z) = 2) ∧
        (¬cgraph.Adj u z → orderOf (clabelS u * clabelS z) = 3)) ∧
      (∀ u ∈ cgraph.commonNeighbors v w, ∀ z ∈ cgraph.commonNeighbors v w, u ≠ z →
        (cgraph.Adj u z ↔ Commute (clabelS u) (clabelS z))) ∧
      Finite (cnGroup v w) ∧ Subgroup.center (cnGroup v w) = ⊥ ∧
      CFSG.Blueprint.Fischer.Pair (cnGroup v w) (cnClass v w) ∧
      (cgraph.induce (cgraph.commonNeighbors v w))ᶜ.Connected ∧
      (∃ (s : Shat) (hs : cvMul cv0 s = v) (iv : cgraph.neighborSet v ≃ rootClass),
        (∀ (y : vStab v) (a : cgraph.neighborSet v),
          SemidirectProduct.inl (iv (stabAct y a) : stdGroup) =
            (rhoV θ₀ hs y)⁻¹ * SemidirectProduct.inl (iv a : stdGroup) * rhoV θ₀ hs y) ∧
        Function.Surjective (rhoV θ₀ hs) ∧
        (∀ y : vStab v, (y : Shat) ∈ vStab v ⊓ vStab w → rhoV θ₀ hs y = 1 → y = 1) ∧
        ∀ y : vStab v, (y : Shat) ∈ cnGroup v w →
          rhoV θ₀ hs y ∈ (SemidirectProduct.inl : stdGroup →* GStar).range) ∧
      (∀ q ∈ vStab v ⊓ vStab w, (∀ h ∈ cnGroup v w, q * h = h * q) → q = 1) ∧
      ∃ ψ : (vStab v ⊓ vStab w : Subgroup Shat) →* MulAut (cnGroup v w),
        Function.Injective ψ ∧ ∀ q h, ((ψ q h : cnGroup v w) : Shat) = q * h * (q : Shat)⁻¹ := by
  have hE := native_coset_graph_exact_root_local_geometry
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  refine ⟨hE.choose, hE.choose_spec.1, fun v w hw => ?_⟩
  have hfaith := (native_order_three_common_neighbor_local_unitary_graph.2.2 v w hw).2.2.1
  have hloc := hE.choose_spec.2 v
  refine ⟨cnGroup_le H v w, cnGroup_normal v w,
    fun h hh hfix => hfaith h (cnGroup_le H v w hh) hfix,
    fun x hx y hy h => clabel_injOn_neighborSet v hx.1 hy.1 (congrArg Subtype.val h),
    fun u _ => orderOf_clabelS u, fun u hu => cnLabels_eq_conj H hw hu,
    fun u hu z hz huz => ⟨fun h => ?_, fun h => ?_⟩,
    fun u hu z hz huz => ⟨fun h => ?_, fun h => ?_⟩,
    inferInstance, center_cnGroup_eq_bot H hw, pair_cnClass H hw,
    compl_connected_commonNeighbors hw,
    ⟨hloc.choose, hloc.choose_spec.choose, hloc.choose_spec.choose_spec.choose,
      hloc.choose_spec.choose_spec.choose_spec.2.2.1,
      hloc.choose_spec.choose_spec.choose_spec.2.2.2.1,
      fun y hy h1 => eq_one_of_rhoV_eq_one hE.choose hloc.choose_spec.choose
        hloc.choose_spec.choose_spec.choose hw hloc.choose_spec.choose_spec.choose_spec.2.2.1
        hloc.choose_spec.choose_spec.choose_spec.2.2.2.2.1 y
        (mem_vStab.1 (Subgroup.mem_inf.1 hy).2) h1,
      fun y hy => rhoV_mem_range_of_mem_cnGroup hE.choose hloc.choose_spec.choose
        hloc.choose_spec.choose_spec.choose H hloc.choose_spec.choose_spec.choose_spec.1 y hy⟩,
    fun q hq hc => eq_one_of_centralizes_cnGroup H hw hq hc, exists_conj_embedding H hw⟩
  · rw [← Subgroup.orderOf_coe]
    exact (orderOf_clabel_mul_of_adj h).2.2
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_clabel_mul_of_not_adj hw hu hz huz h
  · exact Subtype.ext (orderOf_clabel_mul_of_adj h).2.1.eq
  · by_contra hna
    have h3 := orderOf_clabel_mul_of_not_adj hw hu hz huz hna
    have hc : clabel u * clabel z = clabel z * clabel u := congrArg Subtype.val h.eq
    have h2 : (clabel u * clabel z) ^ 2 = 1 := by
      calc (clabel u * clabel z) ^ 2 = clabel u * (clabel z * clabel u) * clabel z := by
            rw [sq]
            group
        _ = clabel u * (clabel u * clabel z) * clabel z := by rw [← hc]
        _ = clabel u * clabel u * (clabel z * clabel z) := by group
        _ = 1 := by rw [clabel_mul_self H u, clabel_mul_self H z, one_mul]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h3] at this
    exact absurd this (by decide)

end CFSG.Monster.B.TwoA.Amalgam
