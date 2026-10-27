
module

public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertBase

public import CFSG.Monster.B.TwoA.Co2Inv.Rows
public import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertInputs
public import Certificates.Certificate3054
public import CFSG.Monster.B.Co2.Simple
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

theorem conjCheck_eq_true : conjCheck = true :=
  Certificates.certificate3054

theorem conjCheck_parts :
    natCertOK actConj 24 validConj rootConj conjCert = true ∧ conjCert.pts.size = 56925 ∧
    (∀ k < 24, ∀ j < 22, Native.actD 22 (gRows k) ((invRows[k]!)[j]!) = 1 <<< j) ∧
    (∀ t < 22, rowOf rootConj t = (gRows 12)[t]!) := by
  have h := conjCheck_eq_true
  simp only [conjCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem wAct_alpha_inv
    (k : Fin 24) :
    wAct v0 (⟨alpha k, alpha_mem_Kv k⟩ : Kstab v0)⁻¹ = rowsEnd invRows[(k : ℕ)]! := by
  have hr : wAct v0 ⟨alpha k, alpha_mem_Kv k⟩ * rowsEnd invRows[(k : ℕ)]! = 1 := by
    rw [wAct_alpha, rowsEnd_mul, ← rowsEnd_idRows]
    refine rowsEnd_congr fun t ht => ?_
    rw [rowsMul_getElem _ _ ht, idRows_getElem ht]
    exact conjCheck_parts.2.2.1 k k.2 t ht
  have hl : wAct v0 (⟨alpha k, alpha_mem_Kv k⟩ : Kstab v0)⁻¹ *
      wAct v0 ⟨alpha k, alpha_mem_Kv k⟩ = 1 := by
    rw [← wAct_mul, mul_inv_cancel, wAct_one]
  calc wAct v0 (⟨alpha k, alpha_mem_Kv k⟩ : Kstab v0)⁻¹
      = wAct v0 (⟨alpha k, alpha_mem_Kv k⟩ : Kstab v0)⁻¹ *
          (wAct v0 ⟨alpha k, alpha_mem_Kv k⟩ * rowsEnd invRows[(k : ℕ)]!) := by rw [hr, mul_one]
    _ = rowsEnd invRows[(k : ℕ)]! := by rw [← mul_assoc, hl, one_mul]

attribute [local instance] conjEndAction

@[expose] def gensConj (k : ℕ) :
    Kstab v0 :=
  if h : k < 24 then (⟨alpha ⟨k, h⟩, alpha_mem_Kv _⟩ : Kstab v0)⁻¹ else 1

theorem decE_actConj
    {k : ℕ} (hk : k < 24) (a : ℕ) :
    decE (actConj k a) = gensConj k • decE a := by
  rw [gensConj, dite_eq_left hk, smul_end_def, inv_inv, wAct_alpha_inv ⟨k, hk⟩, wAct_alpha, decE,
    decE]
  symm
  refine eq_rowsEnd_of fun t => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, rowsEnd_qbW, rowsEnd_decW, rowsEnd_decW,
    rowsOf_getElem _ t.2, actConj, rowOf_encL, decW_mod, conjRowsL,
    List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_map, List.getElem_range]
  rfl

theorem decE_rootConj :
    decE rootConj = wAct v0 rK := by
  rw [wAct_rK, decE]
  refine rowsEnd_congr fun t ht => ?_
  rw [rowsOf_getElem _ ht, conjCheck_parts.2.2.2 t ht]
  rfl

theorem alphaN_mem_closure (j : ℕ) :
    alphaN j ∈ (Subgroup.closure (gensConj '' {k | k < 24})).map (Kstab v0).subtype := by
  unfold alphaN
  split_ifs with h
  · refine ⟨⟨alpha ⟨j, h⟩, alpha_mem_Kv _⟩, ?_, rfl⟩
    have hg : gensConj j ∈ Subgroup.closure (gensConj '' {k | k < 24}) :=
      Subgroup.subset_closure ⟨j, h, rfl⟩
    have := Subgroup.inv_mem _ hg
    rwa [gensConj, dite_eq_left h, inv_inv] at this
  · exact Subgroup.one_mem _

theorem alphaWord_mem_closure :
    ∀ w : List ℤ,
    alphaWord w ∈ (Subgroup.closure (gensConj '' {k | k < 24})).map (Kstab v0).subtype
  | [] => Subgroup.one_mem _
  | l :: w => by
    rw [alphaWord]
    refine Subgroup.mul_mem _ ?_ (alphaWord_mem_closure w)
    split_ifs
    · exact alphaN_mem_closure _
    · exact Subgroup.inv_mem _ (alphaN_mem_closure _)

theorem closure_gensConj :
    Subgroup.closure (gensConj '' {k | k < 24}) = ⊤ := by
  have hA : Agrp ≤ (Subgroup.closure (gensConj '' {k | k < 24})).map (Kstab v0).subtype := by
    rw [Agrp, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact alphaWord_mem_closure _
    · exact alphaWord_mem_closure _
  rw [eq_top_iff]
  intro g _
  have hg : (g : OLq) ∈ Agrp := by
    rw [Agrp_eq_Kv]
    exact g.2
  obtain ⟨g', hg', e⟩ := hA hg
  have e' : g' = g := Subtype.ext e
  rw [← e']
  exact hg'

@[expose] def Cr :
    Subgroup (Kstab v0) := Subgroup.centralizer {rK}

theorem ncard_orbit_wAct_rK :
    (MulAction.orbit (Kstab v0) (wAct v0 rK)).ncard = 56925 := by
  have h := ncard_orbit_of_natCertOK (G := Kstab v0) conjCheck_parts.1
    (fun k hk a _ => decE_actConj hk a) (fun a b ha hb e => decE_injective ha hb e)
  rw [conjCheck_parts.2.1, decE_rootConj] at h
  rw [← h]
  have e : MulAction.orbit (Subgroup.closure (gensConj '' {k | k < 24})) (wAct v0 rK) =
      MulAction.orbit (Kstab v0) (wAct v0 rK) := by
    ext T
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨⟨g, closure_gensConj ▸ Subgroup.mem_top g⟩, rfl⟩
  rw [e]

theorem stabilizer_wAct_rK :
    MulAction.stabilizer (Kstab v0) (wAct v0 rK) = Cr := by
  ext g
  rw [MulAction.mem_stabilizer_iff, smul_wAct, Cr, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have e := eq_of_wAct_eq h
    calc g * rK = g * rK * g⁻¹ * g := by group
      _ = rK * g := by rw [e]
  · intro h
    rw [h, mul_inv_cancel_right]

theorem natCard_Cr :
    Nat.card Cr = 743178240 := by
  have h := (MulAction.stabilizer (Kstab v0) (wAct v0 rK)).index_mul_card
  rw [MulAction.index_stabilizer, ncard_orbit_wAct_rK, natCard_Kv, stabilizer_wAct_rK] at h
  omega

theorem ncard_conjClass_rK :
    {x : Kstab v0 | IsConj rK x}.ncard =
    56925 := by
  have himg : (fun x => wAct v0 x) '' {x : Kstab v0 | IsConj rK x} =
      MulAction.orbit (Kstab v0) (wAct v0 rK) := by
    ext T
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := isConj_iff.1 hx
      refine ⟨c, ?_⟩
      change c • wAct v0 rK = wAct v0 x
      rw [smul_wAct, hc]
    · rintro ⟨g, rfl⟩
      refine ⟨g * rK * g⁻¹, isConj_iff.2 ⟨g, rfl⟩, ?_⟩
      exact (smul_wAct g rK).symm
  rw [← ncard_orbit_wAct_rK, ← himg,
    Set.ncard_image_of_injective _ (fun x y h => eq_of_wAct_eq h)]

end CFSG.Monster.B.TwoA.Co2Inv
