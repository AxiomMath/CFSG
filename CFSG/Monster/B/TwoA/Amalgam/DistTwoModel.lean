module

public import CFSG.Monster.B.TwoA.Amalgam.DistTwoStd
public import CFSG.Monster.B.TwoA.Amalgam.CosetGraph

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

structure RootModel
    (u : CVert) where
  iv : cgraph.neighborSet u ≃ rootClass
  adj_iff : ∀ v w : cgraph.neighborSet u, v ≠ w →
    (cgraph.Adj v w ↔ Commute (iv v : stdGroup) (iv w))
  exists_act : ∀ γ : GStar, ∃ y : Shat, cvMul u y = u ∧ ∀ v : cgraph.neighborSet u,
    ∃ hw : cvMul v y ∈ cgraph.neighborSet u,
      SemidirectProduct.inl (iv ⟨_, hw⟩ : stdGroup) =
        γ⁻¹ * SemidirectProduct.inl (iv v : stdGroup) * γ
  act : ∀ y : Shat, cvMul u y = u → ∃ γ : GStar, ∀ v : cgraph.neighborSet u,
    ∃ hw : cvMul v y ∈ cgraph.neighborSet u,
      SemidirectProduct.inl (iv ⟨_, hw⟩ : stdGroup) =
        γ⁻¹ * SemidirectProduct.inl (iv v : stdGroup) * γ

namespace RootModel

variable {u : CVert} (M : RootModel u)

abbrev pt (v : cgraph.neighborSet u) : GStar := SemidirectProduct.inl (M.iv v : stdGroup)

@[expose] def LabelCompat : Prop :=
  ∀ v w : cgraph.neighborSet u, orderOf (clabel v * clabel w) = orderOf (M.pt v * M.pt w) ∨
    orderOf (clabel v * clabel w) = 2 * orderOf (M.pt v * M.pt w)

theorem pt_mem (v : cgraph.neighborSet u) : M.pt v ∈ rootClassStar := by
  rw [mem_rootClassStar_iff]
  exact ⟨_, (M.iv v).2, rfl⟩

theorem pt_injective : Function.Injective M.pt := fun _ _ h =>
  M.iv.injective (Subtype.ext (SemidirectProduct.inl_injective h))

theorem adj_iff_commute {v w : cgraph.neighborSet u} (hne : v ≠ w) :
    cgraph.Adj v w ↔ Commute (M.pt v) (M.pt w) := by
  rw [M.adj_iff v w hne]
  constructor
  · intro h
    exact h.map SemidirectProduct.inl
  · intro h
    exact Commute.of_map (f := (SemidirectProduct.inl : stdGroup →* GStar))
      SemidirectProduct.inl_injective h

theorem exists_pt_eq {q : GStar} (hq : q ∈ rootClassStar) : ∃ v, M.pt v = q := by
  rw [mem_rootClassStar_iff] at hq
  obtain ⟨x, hx, rfl⟩ := hq
  exact ⟨M.iv.symm ⟨x, hx⟩, by rw [pt, Equiv.apply_symm_apply]⟩

theorem exists_smul_eq_pair {v w v' w' : cgraph.neighborSet u}
    (h : orbSize (M.pt v) (M.pt w) = orbSize (M.pt v') (M.pt w')) :
    ∃ y : Shat, cvMul u y = u ∧ cvMul v y = v' ∧ cvMul w y = w' := by
  obtain ⟨γ, hγv, hγw⟩ := exists_conj_pair_of_orbSize_eq (M.pt_mem v) (M.pt_mem w)
    (M.pt_mem v') (M.pt_mem w') h
  obtain ⟨y, hy, hact⟩ := M.exists_act γ⁻¹
  obtain ⟨hv, hv'⟩ := hact v
  obtain ⟨hw, hw'⟩ := hact w
  have hv2 : M.pt ⟨_, hv⟩ = γ⁻¹⁻¹ * M.pt v * γ⁻¹ := hv'
  have hw2 : M.pt ⟨_, hw⟩ = γ⁻¹⁻¹ * M.pt w * γ⁻¹ := hw'
  rw [inv_inv, hγv] at hv2
  rw [inv_inv, hγw] at hw2
  exact ⟨y, hy, congrArg Subtype.val (M.pt_injective hv2),
    congrArg Subtype.val (M.pt_injective hw2)⟩

theorem orbSize_smul {y : Shat} (hy : cvMul u y = u) (v w : cgraph.neighborSet u)
    (hv : cvMul v y ∈ cgraph.neighborSet u) (hw : cvMul w y ∈ cgraph.neighborSet u) :
    orbSize (M.pt ⟨_, hv⟩) (M.pt ⟨_, hw⟩) = orbSize (M.pt v) (M.pt w) := by
  obtain ⟨γ, hact⟩ := M.act y hy
  obtain ⟨hv0, hv'⟩ := hact v
  obtain ⟨hw0, hw'⟩ := hact w
  have e1 : M.pt ⟨_, hv⟩ = γ⁻¹ * M.pt v * γ⁻¹⁻¹ := by rw [inv_inv]; exact hv'
  have e2 : M.pt ⟨_, hw⟩ = γ⁻¹ * M.pt w * γ⁻¹⁻¹ := by rw [inv_inv]; exact hw'
  rw [e1, e2, orbSize_conj]

theorem natCard_orbSize_eq (v : cgraph.neighborSet u) (i : Fin 5) :
    Nat.card {w : cgraph.neighborSet u // orbSize (M.pt v) (M.pt w) = repSize i} = repSize i := by
  calc Nat.card {w : cgraph.neighborSet u // orbSize (M.pt v) (M.pt w) = repSize i}
      = Nat.card ↥{q | q ∈ rootClassStar ∧ orbSize (M.pt v) q = repSize i} :=
        Nat.card_congr
          { toFun := fun w => ⟨M.pt w.1, M.pt_mem w.1, w.2⟩
            invFun := fun q => ⟨(M.exists_pt_eq q.2.1).choose, by
              rw [(M.exists_pt_eq q.2.1).choose_spec]
              exact q.2.2⟩
            left_inv := fun w =>
              Subtype.ext (M.pt_injective (M.exists_pt_eq (M.pt_mem w.1)).choose_spec)
            right_inv := fun q => Subtype.ext (M.exists_pt_eq q.2.1).choose_spec }
    _ = repSize i := by rw [Nat.card_coe_set_eq, ncard_setOf_orbSize_eq (M.pt_mem v) i]

theorem natCard_orbit_eq_orbSize (v w : cgraph.neighborSet u) :
    Nat.card {w' : CVert // ∃ y : Shat, cvMul u y = u ∧ cvMul v y = v ∧ cvMul w y = w'} =
      orbSize (M.pt v) (M.pt w) := by
  rw [orbSize, ← Nat.card_coe_set_eq]
  have hmem : ∀ w' : {w' : CVert // ∃ y : Shat, cvMul u y = u ∧ cvMul v y = v ∧
      cvMul w y = w'}, (w' : CVert) ∈ cgraph.neighborSet u := by
    rintro ⟨_, y, hy, -, rfl⟩
    have h := (cgraph_adj_cvMul u w y).2 w.2
    rwa [hy] at h
  have hto : ∀ w' : {w' : CVert // ∃ y : Shat, cvMul u y = u ∧ cvMul v y = v ∧
      cvMul w y = w'}, M.pt ⟨_, hmem w'⟩ ∈ conjOrbit (Subgroup.centralizer {M.pt v}) (M.pt w) := by
    rintro ⟨_, y, hy, hyv, rfl⟩
    obtain ⟨γ, hact⟩ := M.act y hy
    obtain ⟨hv', hv''⟩ := hact v
    obtain ⟨hw', hw''⟩ := hact w
    have e : γ⁻¹ * M.pt v * γ = M.pt v := by
      have e0 : M.pt ⟨_, hv'⟩ = γ⁻¹ * M.pt v * γ := hv''
      rw [← e0]
      congr 1
      exact Subtype.ext hyv
    have hc : γ⁻¹ ∈ Subgroup.centralizer {M.pt v} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc γ⁻¹ * M.pt v = γ⁻¹ * M.pt v * γ * γ⁻¹ := by group
        _ = M.pt v * γ⁻¹ := by rw [e]
    refine ⟨γ⁻¹, hc, ?_⟩
    have e1 : M.pt ⟨_, hw'⟩ = γ⁻¹ * M.pt w * γ := hw''
    rw [inv_inv]
    exact e1.symm
  refine Nat.card_congr (Equiv.ofBijective (fun w' => ⟨M.pt ⟨_, hmem w'⟩, hto w'⟩) ⟨?_, ?_⟩)
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have h1 := M.pt_injective (congrArg Subtype.val hab)
    exact Subtype.ext (congrArg (fun z : cgraph.neighborSet u => (z : CVert)) h1)
  · rintro ⟨q, c, hc, rfl⟩
    obtain ⟨y, hy, hact⟩ := M.exists_act c⁻¹
    obtain ⟨hv', hv''⟩ := hact v
    obtain ⟨hw', hw''⟩ := hact w
    have hcv : c * M.pt v = M.pt v * c := Subgroup.mem_centralizer_singleton_iff.1 hc
    have hyv : cvMul v y = v := by
      have e : M.pt ⟨_, hv'⟩ = M.pt v := by
        have e0 : M.pt ⟨_, hv'⟩ = c⁻¹⁻¹ * M.pt v * c⁻¹ := hv''
        rw [e0, inv_inv, hcv, mul_inv_cancel_right]
      exact congrArg Subtype.val (M.pt_injective e)
    refine ⟨⟨_, y, hy, hyv, rfl⟩, Subtype.ext ?_⟩
    have e1 : M.pt ⟨_, hw'⟩ = c⁻¹⁻¹ * M.pt w * c⁻¹ := hw''
    rw [inv_inv] at e1
    exact e1

end RootModel

end CFSG.Monster.B.TwoA.Amalgam
