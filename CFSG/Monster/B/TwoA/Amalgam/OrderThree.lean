module

public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeTriple
public import CFSG.Monster.B.TwoA.Amalgam.DistTwo

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar)
open CFSG.Monster.B.Classical.UnitarySix (IsoPt isoGraph LBeta extAct)

theorem nonempty_localHom
    (v : CVert) : Nonempty (LocalHom v) := by
  obtain ⟨θ, -, hθ⟩ := native_coset_graph_exact_root_local_geometry
  obtain ⟨s, hs, iv, H1, H2, H3, H4, H5, H6, -⟩ := hθ v
  refine ⟨{ stab := vStab v
            mem_stab := fun _ => Iff.rfl
            iv := iv
            rho := rhoV θ hs
            adj_iff := H2
            act := fun y a _ => H3 y a
            surj := H4
            ker := H5
            orderOf_clabel := H6
            rho_clabel := fun a y hy => ?_ }⟩
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

theorem native_order_three_common_neighbor_local_unitary_graph :
    isoGraph.IsSRGWith 693 180 51 45 ∧ Function.Injective extAct ∧
    ∀ v w : CVert, w ∈ sphereThree v →
      (cgraph.commonNeighbors v w).Nonempty ∧ 694 ≤ (cgraph.commonNeighbors v w).ncard ∧
      (∀ s ∈ vStab v ⊓ vStab w, (∀ x ∈ cgraph.commonNeighbors v w, cvMul x s = x) → s = 1) ∧
      (∀ x ∈ cgraph.commonNeighbors v w, ∀ x' ∈ cgraph.commonNeighbors v w,
        ∃ s ∈ vStab v ⊓ vStab w, cvMul x s = x') ∧
      ∀ u ∈ cgraph.commonNeighbors v w,
        (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w).ncard = 693 ∧
        (∀ s : Shat, (s ∈ vStab v ⊓ vStab w ⊓ vStab u ∧
            ∀ x ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w, cvMul x s = x) ↔
          (s : Dfull) ∈ Subgroup.zpowers (clabel u)) ∧
        Nat.card (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat) = 36787322880 ∧
        ∃ (ι : cgraph.induce (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) ≃g isoGraph)
          (φ : (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat) →* LBeta),
          Function.Surjective φ ∧
          (∀ y, φ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel u)) ∧
          Nonempty ((vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat) ⧸ φ.ker ≃* LBeta) ∧
          ∀ (y : (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat))
            (x : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w))
            (h : cvMul x y ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w),
            ι ⟨_, h⟩ = (extAct (φ y))⁻¹ (ι x) := by
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  have htrans := native_coset_graph_two_distance_two_orbits.2.2.2.1
  refine ⟨CFSG.Monster.B.Classical.UnitarySix.unitary_six_isotropic_point_graph.1,
    standard_F4_opposite_root_common_neighbor_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun v w hw => ?_⟩
  have hd := cgraph_dist_eq_two_iff.1 hw.1
  have hC : (cgraph.commonNeighbors v w).Nonempty :=
    ⟨hd.2.2.choose, hd.2.2.choose_spec.1, hd.2.2.choose_spec.2.symm⟩
  have hcom := order_three_common H hd.1 hd.2.1 hw.2 hC
  refine ⟨hC, hcom.1, fun s hs hfix => hcom.2 s (Subgroup.mem_inf.1 hs).1
    (Subgroup.mem_inf.1 hs).2 hfix, fun x hx x' hx' => ?_, fun u hu => ?_⟩
  · have h := htrans v w hw.1 x hx x' hx'
    exact ⟨h.choose, Subgroup.mem_inf.2 ⟨h.choose_spec.1, h.choose_spec.2.1⟩,
      h.choose_spec.2.2⟩
  · have h := order_three_at H hd.1 hd.2.1 hw.2 hu (vStab v ⊓ vStab w ⊓ vStab u) fun y => by
      simp only [Subgroup.mem_inf, mem_vStab, and_assoc]
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.choose, h.2.2.2.choose_spec.choose,
      h.2.2.2.choose_spec.choose_spec.1, h.2.2.2.choose_spec.choose_spec.2.1,
      ⟨QuotientGroup.quotientKerEquivOfSurjective _ h.2.2.2.choose_spec.choose_spec.1⟩,
      h.2.2.2.choose_spec.choose_spec.2.2⟩

theorem native_order_three_label_products_and_dihedral_triples :
    ∀ v : CVert,
      (∀ w ∈ sphereThree v,
        orderOf (clabel v * clabel w) = 3 ∧
        ∃ r : CVert, r = cvMul w (clabelS v) ∧ r = cvMul v (clabelS w) ∧ r ≠ v ∧ r ≠ w ∧
          (∀ x ∈ ({v, w, r} : Set CVert), ∀ y ∈ ({v, w, r} : Set CVert), x ≠ y →
            y ∈ sphereThree x) ∧
          cgraph.commonNeighbors v w = cgraph.commonNeighbors v r ∧
          cgraph.commonNeighbors v w = cgraph.commonNeighbors w r ∧
          Nonempty (Subgroup.closure ({clabelS v, clabelS w} : Set Shat) ≃* Equiv.Perm (Fin 3)) ∧
          (∀ y ∈ Subgroup.closure ({clabelS v, clabelS w} : Set Shat),
            ∀ x ∈ cgraph.commonNeighbors v w, cvMul x y = x) ∧
          (∃ π : Subgroup.closure ({clabelS v, clabelS w} : Set Shat) ≃*
              Equiv.Perm ({v, w, r} : Set CVert),
            ∀ y x, ((π y x : ({v, w, r} : Set CVert)) : CVert) = cvMul x (y : Shat)⁻¹) ∧
          clabel r = clabel v * clabel w * clabel v ∧
          clabel r = clabel w * clabel v * clabel w) ∧
      (∀ w ∈ sphereThree v, cvMul w (clabelS v) ∈ sphereThree v ∧ cvMul w (clabelS v) ≠ w ∧
        cvMul (cvMul w (clabelS v)) (clabelS v) = w) ∧
      Even (sphereThree v).ncard := by
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  intro v
  refine ⟨fun w hw => ?_, fun w hw => sphereThree_pairing H hw, even_ncard_sphereThree H v⟩
  obtain ⟨r, hrd, hre, hrv, hrw, hdv, -, hew, -, hl1, hl2⟩ := order_three_triple H hw
  have hvw : v ≠ w := (cgraph_dist_eq_two_iff.1 hw.1).1
  have hT3 : Nat.card ({v, w, r} : Set CVert) = 3 := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_three]
    exact ⟨v, w, r, hvw, hrv.symm, hrw.symm, rfl⟩
  obtain ⟨π, hπ⟩ := exists_closure_equiv_perm H hw hrd hre hrv hrw
  have hvr : r ∈ sphereThree v := by
    have h := sphereThree_cvMul hw (clabelS v)
    rwa [hdv, ← hrd] at h
  have hrw' : w ∈ sphereThree r := by
    have h := sphereThree_cvMul hw (clabelS w)
    rwa [hew, ← hre] at h
  refine ⟨orderOf_clabel_mul_eq_three H hw, r, hrd, hre, hrv, hrw, fun x hx y hy hxy => ?_,
    ?_, ?_, ⟨π.trans (Equiv.permCongrHom (Finite.equivFinOfCardEq hT3))⟩,
    closure_clabelS_fix H v w, ⟨π, hπ⟩, hl1, hl2⟩
  · rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rw [hx, hy] at hxy ⊢ <;>
      first
      | exact absurd rfl hxy
      | exact hw
      | exact hvr
      | exact hrw'
      | exact mem_sphereThree_comm.1 hw
      | exact mem_sphereThree_comm.1 hvr
      | exact mem_sphereThree_comm.1 hrw'
  · rw [hrd, commonNeighbors_cvMul_clabelS H]
  · rw [SimpleGraph.commonNeighbors_symm cgraph w r, hre, commonNeighbors_cvMul_clabelS' H]

end CFSG.Monster.B.TwoA.Amalgam
