module

public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphLocal
public import CFSG.Monster.B.TwoA.Amalgam.LocalBldMain

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.Geometry

theorem parJ_cotype
    (i : Fin 4) : parJ {j | j ≠ i} = Pc i := by
  obtain ⟨j₀, hj₀⟩ := exists_ne i
  show parGroup ({j | j ≠ i} : Set (Fin 4)) = Pc i
  rw [parGroup_eq_iSup (J := ({j | j ≠ i} : Set (Fin 4))) hj₀, Pc_eq_iSup_Qam i]
  rfl

abbrev vtx
    (i : Fin 4) (x : Chamber) : Set Chamber := chamberCS.residue {j | j ≠ i} x

theorem chamberOf_mem_vtx_iff
    (i : Fin 4) (g h : Eam) :
    chamberOf h ∈ vtx i (chamberOf g) ↔ ((h * g⁻¹ : Eam) : Dfull) ∈ Pc i :=
  (mem_residue_chamberCS_iff _ g h).trans (SetLike.ext_iff.1 (parJ_cotype i) _)

theorem vtx_eq_iff
    (i : Fin 4) (g h : Eam) :
    vtx i (chamberOf g) = vtx i (chamberOf h) ↔ ((h * g⁻¹ : Eam) : Dfull) ∈ Pc i := by
  constructor
  · intro e
    have hh : chamberOf h ∈ vtx i (chamberOf g) := by
      rw [e]
      exact chamberCS.self_mem_residue _ _
    exact (chamberOf_mem_vtx_iff i g h).1 hh
  · intro hm
    exact (chamberCS.residue_eq_of_mem ((chamberOf_mem_vtx_iff i g h).2 hm)).symm

theorem vtx_inter_nonempty_iff
    (i j : Fin 4) (g h : Eam) :
    (vtx i (chamberOf g) ∩ vtx j (chamberOf h)).Nonempty ↔
      ∃ k : Eam, ((k * g⁻¹ : Eam) : Dfull) ∈ Pc i ∧ ((k * h⁻¹ : Eam) : Dfull) ∈ Pc j := by
  constructor
  · rintro ⟨z, hz1, hz2⟩
    obtain ⟨k, rfl⟩ := chamberOf_surjective z
    exact ⟨k, (chamberOf_mem_vtx_iff i g k).1 hz1, (chamberOf_mem_vtx_iff j h k).1 hz2⟩
  · rintro ⟨k, h1, h2⟩
    exact ⟨chamberOf k, (chamberOf_mem_vtx_iff i g k).2 h1, (chamberOf_mem_vtx_iff j h k).2 h2⟩

theorem image_vtx
    (i : Fin 4) (g : Eam) (x : Chamber) :
    chamberMulPerm g '' vtx i x = vtx i (chamberMul x g) :=
  ChamberSystem.image_residue_of_mem_typeAut (chamberMulPerm_mem_typeAut_F4 g) _ x

@[expose] def ptMap :
    P1Cos → Set Chamber :=
  Quotient.lift (fun e : Eam => vtx 0 (chamberOf e)) fun e f h =>
    (vtx_eq_iff 0 e f).2 (p1rel_iff.1 h)

theorem ptMap_mk
    (e : Eam) : ptMap (Quotient.mk _ e) = vtx 0 (chamberOf e) := rfl

theorem ptMap_injective :
    Function.Injective ptMap := by
  intro u w h
  obtain ⟨e, rfl⟩ := Quotient.mk_surjective u
  obtain ⟨f, rfl⟩ := Quotient.mk_surjective w
  exact Quotient.sound (p1rel_iff.2 ((vtx_eq_iff 0 e f).1 h))

theorem range_ptMap :
    Set.range ptMap = {R | ∃ x : Chamber, R = vtx 0 x} := by
  ext R
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨e, rfl⟩ := Quotient.mk_surjective u
    exact ⟨chamberOf e, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨e, rfl⟩ := chamberOf_surjective x
    exact ⟨Quotient.mk _ e, rfl⟩

theorem exists_ptMap_eq
    (u : P1Cos) : ∃ x : Chamber, ptMap u = vtx 0 x := by
  obtain ⟨e, rfl⟩ := Quotient.mk_surjective u
  exact ⟨chamberOf e, rfl⟩

@[expose] def ptEquiv :
    P1Cos ≃ {R : Set Chamber // ∃ x : Chamber, R = vtx 0 x} :=
  Equiv.ofBijective (fun u => ⟨ptMap u, exists_ptMap_eq u⟩)
    ⟨fun _ _ h => ptMap_injective (congrArg Subtype.val h), fun R => by
      obtain ⟨x, hx⟩ := R.2
      obtain ⟨e, rfl⟩ := chamberOf_surjective x
      exact ⟨Quotient.mk _ e, Subtype.ext hx.symm⟩⟩

theorem ptMap_mk_mul
    (e f : Eam) :
    ptMap (Quotient.mk _ (e * f)) = chamberMulPerm f '' ptMap (Quotient.mk _ e) := by
  rw [ptMap_mk, ptMap_mk, image_vtx, chamberMul_chamberOf]

theorem mem_cSigma_iff
    (v : CVert) (s : Shat) : v ∈ cSigma s ↔ cvMul v s⁻¹ ∈ cSigma 1 := by
  rw [mem_cSigma_one]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by rw [cvMul_cvOf, mul_inv_cancel_right]⟩
  · rintro ⟨x, hx, hv⟩
    refine ⟨x, hx, ?_⟩
    rw [← cvMul_cvOf, ← hv, cvMul_inv_cancel']

theorem cvMul_cv0_toS
    (e : Eam) : cvMul cv0 (toS e) = cv0 := (cvMul_cv0_iff _).2 e.2

theorem cSigma_isClique'
    (s : Shat) {v w : CVert} (hv : v ∈ cSigma s) (hw : w ∈ cSigma s)
    (hne : v ≠ w) : cgraph.Adj v w := by
  rw [mem_cSigma_iff] at hv hw
  have h := cSigma_isClique hv hw fun e => hne (by
    have := congrArg (fun z => cvMul z s) e
    simpa only [cvMul_inv_cancel'] using this)
  exact (cgraph_adj_cvMul _ _ _).1 h

theorem nbr_mem_cSigma_diff_iff
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) (e : Eam)
    (u : P1Cos) :
    nbr ha hn u ∈ cSigma (toS e) \ {cv0} ↔ (ptMap u ∩ vtx 3 (chamberOf e)).Nonempty := by
  obtain ⟨f, rfl⟩ := Quotient.mk_surjective u
  rw [ptMap_mk, vtx_inter_nonempty_iff]
  have hv0 : ∀ v : CVert, v ∈ cSigma (toS e) \ {cv0} ↔
      cvMul v (toS e)⁻¹ ∈ cSigma 1 \ {cv0} := by
    intro v
    rw [Set.mem_sdiff, Set.mem_sdiff, mem_cSigma_iff, Set.mem_singleton_iff,
      Set.mem_singleton_iff]
    refine and_congr Iff.rfl (not_congr ⟨fun h => ?_, fun h => ?_⟩)
    · rw [h]
      exact cvMul_cv0_toS e⁻¹
    · have h2 := congrArg (fun z => cvMul z (toS e)) h
      simp only [cvMul_inv_cancel'] at h2
      rw [h2, cvMul_cv0_toS]
  have hmul : cvMul (nbr ha hn (Quotient.mk _ f)) (toS e)⁻¹ =
      nbr ha hn (Quotient.mk _ (f * e⁻¹)) := by
    rw [nbr_mk_mul]
    rfl
  rw [hv0, hmul, cSigma_diff_cv0 ha hn]
  constructor
  · rintro ⟨p, hp, hpe⟩
    have h2 : nbr ha hn (Quotient.mk _ (f * e⁻¹)) = nbr ha hn (Quotient.mk _ p) := hpe
    have h3 := p1rel_iff.1 (Quotient.exact (nbr_injective ha hn h2))
    refine ⟨p * e, ?_, ?_⟩
    · have e1 : ((p * e * f⁻¹ : Eam) : Dfull) = ((p * (f * e⁻¹)⁻¹ : Eam) : Dfull) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e1]
      exact h3
    · have e1 : ((p * e * e⁻¹ : Eam) : Dfull) = p := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e1]
      exact hp
  · rintro ⟨k, hk1, hk4⟩
    refine ⟨k * e⁻¹, hk4, ?_⟩
    show cvOf (elS ha * toS (f * e⁻¹)) = cvOf (elS ha * toS (k * e⁻¹))
    refine nbr_congr ha hn ?_
    have e1 : ((k * e⁻¹ * (f * e⁻¹)⁻¹ : Eam) : Dfull) = ((k * f⁻¹ : Eam) : Dfull) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1]
    exact hk1

theorem cv0_mem_cSigma :
    cv0 ∈ cSigma 1 := mem_cSigma_one.2 ⟨1, Xgrp.one_mem, rfl⟩

theorem ncard_cSigma_diff :
    (cSigma 1 \ {cv0}).ncard = 119 := by
  rw [Set.ncard_sdiff_singleton_of_mem cv0_mem_cSigma, ncard_cSigma]

theorem nbr_adj_of_common_vtx
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) {u w : P1Cos}
    (huw : u ≠ w) (x : Chamber) (hu : (ptMap u ∩ vtx 3 x).Nonempty)
    (hw : (ptMap w ∩ vtx 3 x).Nonempty) : cgraph.Adj (nbr ha hn u) (nbr ha hn w) := by
  obtain ⟨e, rfl⟩ := chamberOf_surjective x
  have hu' := (nbr_mem_cSigma_diff_iff ha hn e u).2 hu
  have hw' := (nbr_mem_cSigma_diff_iff ha hn e w).2 hw
  exact cSigma_isClique' (toS e) hu'.1 hw'.1 fun h => huw (nbr_injective ha hn h)

end CFSG.Monster.B.TwoA.Amalgam
