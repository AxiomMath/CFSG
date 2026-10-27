module

public import CFSG.Sporadic.Co1Patterson.GraphRonanNative
public import CFSG.Sporadic.Co1Patterson.TitsMultiOrbit
public import Certificates.Certificate21156

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Monster.GMS
  CFSG.Sporadic.Co1Patterson.Native CFSG.Monster.B.Recog
open CFSG.Blueprint (NativeSporadic.Co1)

theorem tri_check : triCheck = true :=
  Certificates.certificate21156


@[expose] noncomputable def uT (j : Fin 3) : Vt := cV (triRoots.getD j 0)

abbrev triT : Set Vt → Prop := triOrb (X := NativeSporadic.Co1) vA vE uT

@[expose] def TriNull (x y z : Vt) : Prop :=
  ∀ (hxy : (a2Graph aNC).Adj x y) (hyz : (a2Graph aNC).Adj y z) (hzx : (a2Graph aNC).Adj z x),
    HomotopicBy triT (.cons hxy (.cons hyz (.cons hzx .nil)) : (a2Graph aNC).Walk x x) .nil

theorem triNull_smul (g : NativeSporadic.Co1) {x y z : Vt} (h : TriNull x y z) :
    TriNull (g • x) (g • y) (g • z) := by
  intro hxy hyz hzx
  have h1 := h ((a2Graph_adj_smul_iff g).1 hxy) ((a2Graph_adj_smul_iff g).1 hyz)
    ((a2Graph_adj_smul_iff g).1 hzx)
  exact HomotopicBy.map (conjIso (t := aNC) g).toHom (fun x y z hT => by
    have := triOrb_image_smul g hT
    rw [image_smul_triple] at this
    exact this) h1

@[expose] def locSet : Std.HashSet (Array ℕ) :=
  Std.HashSet.ofList ((locOrbs orbE).flatMap fun f => f.c.pts.toList)

theorem triCheck_parts :
    (1 ≤ swapIdx ∧ swapIdx ≤ 190) ∧
    Native.mul (Native.mul (gEl swapIdx) iotaARows) (gElInv swapIdx) = repRows 1 ∧
    Native.mul (Native.mul (gEl swapIdx) (repRows 1)) (gElInv swapIdx) = iotaARows ∧
    centOK (gensArr gensKe) (repRows 1) = true ∧
    (locOrbs orbE).length = triRoots.length ∧
    (∀ j < triRoots.length, orbOK (gensArr gensKe) (gensInvArr gensKe)
      orbE.c.pts[triRoots.getD j 0]! ((locOrbs orbE).getD j default) = true) ∧
    orbOK (gensArr gensKe) (gensInvArr gensKe) orbE.c.pts[t192Root]! (t192Orb orbE) = true ∧
    (∀ k < orbE.c.pts.size, (!(adjC (ptSet orbE) (repX 1) (repXi 1) orbE.c.pts[k]!) ||
      locSet.contains orbE.c.pts[k]! || (ptSet (t192Orb orbE)).contains orbE.c.pts[k]!) = true) ∧
    t192Root < orbE.c.pts.size ∧ coneIdx < orbE.c.pts.size ∧ coneK2 < orbE.c.pts.size ∧
    adjC (ptSet orbE) (repX 1) (repXi 1) orbE.c.pts[coneIdx]! = true ∧
    adjC (ptSet orbE) (xeK orbE t192Root) (xeiK orbE t192Root) orbE.c.pts[coneIdx]! = true ∧
    locSet.contains orbE.c.pts[coneIdx]! = true ∧
    locSet.contains (Native.mul (Native.mul orbE.his[t192Root]! orbE.c.pts[coneIdx]!)
      orbE.hs[t192Root]!) = true ∧
    Native.mul (Native.mul (gElInv swapIdx) orbE.c.pts[t192Root]!) (gEl swapIdx) =
      orbE.c.pts[coneK2]! ∧
    locSet.contains (Native.mul (Native.mul (Native.mul orbE.his[coneK2]! (gElInv swapIdx))
      orbE.c.pts[coneIdx]!) (Native.mul (gEl swapIdx) orbE.hs[coneK2]!)) = true ∧
    ∀ j < triRoots.length, locTriOK orbE j = true := by
  have h := tri_check
  unfold triCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
    h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩ := h
  exact ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩

theorem swap_smul :
    gElt swapIdx • vA = vE ∧ gElt swapIdx • vE = vA := by
  obtain ⟨⟨hs1, hs2⟩, hsa, hse, -⟩ := triCheck_parts
  have hs := nrep_gEl (dagOK_parts dagOK_true).1 swapIdx
  have hsi := nrep_gElInv dagOK_true hs1 hs2
  refine ⟨Subtype.ext (NRep.unique ((hs.mul nrep_aNC).mul hsi) ?_),
    Subtype.ext (NRep.unique ((hs.mul (nrep_repV (by norm_num))).mul hsi) ?_)⟩
  · rw [hsa]
    exact nrep_repV (by norm_num)
  · rw [hse]
    exact nrep_aNC

theorem exists_of_locSet {R : Native.Rows} {c : Vt} (hR : NRep R c)
    (h : locSet.contains R = true) :
    ∃ j : Fin 3, ∃ g ∈ centralizer ({aNC} : Set NativeSporadic.Co1) ⊓
      centralizer ({(vE : NativeSporadic.Co1)} : Set NativeSporadic.Co1), c = g • uT j := by
  obtain ⟨-, -, -, hcent, hlen, hlo, -⟩ := triCheck_parts
  unfold locSet at h
  rw [Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_flatMap] at h
  obtain ⟨f, hf1, hf2⟩ := h
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hf1
  rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hf2
  obtain ⟨p, hp, hpR⟩ := hf2
  have hn' : n < triRoots.length := hlen ▸ hn
  have h3 : n < 3 := hn'
  have hok := hlo n hn'
  have hfn : (locOrbs orbE).getD n default = (locOrbs orbE)[n] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
    rfl
  rw [hfn] at hok
  have hk : triRoots.getD n 0 < orbE.c.pts.size := by
    rw [size_orbE]
    interval_cases n <;> decide
  obtain ⟨g, hg, -, -, hgp⟩ := orbOK_sound matHom hok (gensElt gensKe)
    (fun l hl => nrep_gensArr dagOK_true _ hl) _ (nrep_cV hk) p hp
  refine ⟨⟨n, h3⟩, g, (Subgroup.closure_le _).2 (by
    rintro _ ⟨l, hl, rfl⟩
    exact mem_of_centOK hcent (fun l hl => nrep_gensArr dagOK_true _ hl)
      (nrep_repV (by norm_num)) l hl) hg, ?_⟩
  apply Subtype.ext
  rw [coe_smul_conjVert]
  refine NRep.unique hR ?_
  rw [← hpR, ← getElem!_pos _ p hp]
  exact hgp

theorem triT_of_locSet {R : Native.Rows} {c : Vt} (hR : NRep R c)
    (h : locSet.contains R = true) : triT {vA, vE, c} := by
  obtain ⟨j, g, hg, rfl⟩ := exists_of_locSet hR h
  refine ⟨g, j, ?_⟩
  rw [image_smul_triple, (smul_vA_eq_iff g).2 (mem_inf.1 hg).1,
    (smul_eq_self_iff g vE).2 (mem_inf.1 hg).2]

theorem triNull_t192 : TriNull vA vE (cV t192Root) := by
  obtain ⟨⟨hs1, hs2⟩, -, -, -, -, -, -, -, hk1, hkc, hk2, hce, hcu, hcl, hcl2, hsu, hcl3, -⟩ :=
    triCheck_parts
  obtain ⟨hsA, hsE⟩ := swap_smul
  have hs := nrep_gEl (dagOK_parts dagOK_true).1 swapIdx
  have hsi := nrep_gElInv dagOK_true hs1 hs2
  have hS1 := hE_spec hk1
  have hS2 := hE_spec hk2
  have hX := nrep_repX dagOK_true 1
  have hXi := nrep_repXi dagOK_true (show 1 < 10 by norm_num)
  have hXv := ((dagOK_parts dagOK_true).2 _ (repJ_mem (show 1 < 10 by norm_num)).1
    (repJ_mem (show 1 < 10 by norm_num)).2)
  intro hxy hyz hzx
  have hxv := adj_vA_cV hkc
  have hyv : (a2Graph aNC).Adj vE (cV coneIdx) := by
    have hbx : vE = gElt (repJ 1) • vA := repV_eq_smul 1
    rw [hbx]
    exact (adj_iff_adjC hX hXi (nrep_cV hkc) hXv.1 hXv.2.1 (valid_pts hkc)).2 hce
  have hzv : (a2Graph aNC).Adj (cV t192Root) (cV coneIdx) :=
    (adj_cV_iff hk1 (nrep_cV hkc) (valid_pts hkc)).2 hcu
  have h₁ : triT {vA, vE, cV coneIdx} := triT_of_locSet (nrep_cV hkc) hcl
  have h₃ : triT {cV t192Root, vA, cV coneIdx} := by
    have hR : NRep (Native.mul (Native.mul orbE.his[t192Root]! orbE.c.pts[coneIdx]!)
        orbE.hs[t192Root]!) (((hE t192Root)⁻¹ • cV coneIdx : Vt) : NativeSporadic.Co1) := by
      rw [coe_smul_conjVert, inv_inv]
      exact (hS1.2.2.1.mul (nrep_cV hkc)).mul hS1.2.1
    have := triOrb_image_smul (hE t192Root) (triT_of_locSet hR hcl2)
    rw [image_smul_triple, (smul_vA_eq_iff _).2 hS1.1, ← cV_eq, smul_inv_smul] at this
    rw [Set.insert_comm]
    exact this
  have h₂ : triT {vE, cV t192Root, cV coneIdx} := by
    have hsu' : (gElt swapIdx)⁻¹ • cV t192Root = cV coneK2 := by
      apply Subtype.ext
      refine NRep.unique (R := orbE.c.pts[coneK2]!) ?_ (nrep_cV hk2)
      rw [← hsu, coe_smul_conjVert, inv_inv]
      exact (hsi.mul (nrep_cV hk1)).mul hs
    have hR : NRep (Native.mul (Native.mul (Native.mul orbE.his[coneK2]! (gElInv swapIdx))
        orbE.c.pts[coneIdx]!) (Native.mul (gEl swapIdx) orbE.hs[coneK2]!))
        (((gElt swapIdx * hE coneK2)⁻¹ • cV coneIdx : Vt) : NativeSporadic.Co1) := by
      rw [coe_smul_conjVert, inv_inv, _root_.mul_inv_rev]
      exact ((hS2.2.2.1.mul hsi).mul (nrep_cV hkc)).mul (hs.mul hS2.2.1)
    have := triOrb_image_smul (gElt swapIdx * hE coneK2) (triT_of_locSet hR hcl3)
    rw [image_smul_triple, smul_inv_smul, mul_smul, mul_smul, (smul_vA_eq_iff _).2 hS2.1, hsA,
      ← cV_eq, ← hsu', smul_inv_smul] at this
    exact this
  exact homotopicBy_triangle_of_cone hxy hyz hzx hxv hyv hzv h₁ h₂ h₃

theorem triNull_base (c : Vt) (hec : (a2Graph aNC).Adj vE c) (hca : (a2Graph aNC).Adj c vA) :
    TriNull vA vE c := by
  obtain ⟨-, -, -, hcent, -, -, h192, hall, hk1, -⟩ := triCheck_parts
  obtain ⟨k, hk, rfl⟩ := exists_cV hca.symm
  have hX := nrep_repX dagOK_true 1
  have hXi := nrep_repXi dagOK_true (show 1 < 10 by norm_num)
  have hXv := ((dagOK_parts dagOK_true).2 _ (repJ_mem (show 1 < 10 by norm_num)).1
    (repJ_mem (show 1 < 10 by norm_num)).2)
  have hbx : vE = gElt (repJ 1) • vA := repV_eq_smul 1
  rw [hbx] at hec
  have hadj : adjC (ptSet orbE) (repX 1) (repXi 1) orbE.c.pts[k]! = true :=
    (adj_iff_adjC hX hXi (nrep_cV hk) hXv.1 hXv.2.1 (valid_pts hk)).1 hec
  have h := hall k hk
  rw [hadj] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
  rcases h with h | h
  · intro hxy hyz hzx
    exact homotopicBy_triangle_nil hxy hyz hzx (triT_of_locSet (nrep_cV hk) h)
  · rw [ptSet_contains_iff] at h
    obtain ⟨p, hp, hpk⟩ := h
    obtain ⟨g, hg, -, -, hgp⟩ := orbOK_sound matHom h192 (gensElt gensKe)
      (fun l hl => nrep_gensArr dagOK_true _ hl) _ (nrep_cV hk1) p hp
    have hgC := (Subgroup.closure_le _).2 (by
      rintro _ ⟨l, hl, rfl⟩
      exact mem_of_centOK hcent (fun l hl => nrep_gensArr dagOK_true _ hl)
        (nrep_repV (by norm_num)) l hl) hg
    have e1 : g • vA = vA := (smul_vA_eq_iff g).2 (mem_inf.1 hgC).1
    have e2 : g • vE = vE := (smul_eq_self_iff g vE).2 (mem_inf.1 hgC).2
    have e3 : g • cV t192Root = cV k := by
      apply Subtype.ext
      rw [coe_smul_conjVert]
      refine NRep.unique (R := (t192Orb orbE).c.pts[p]!) hgp ?_
      rw [hpk]
      exact nrep_cV hk
    have := triNull_smul g triNull_t192
    rw [e1, e2, e3] at this
    exact this

theorem triNull_all (x y z : Vt) : TriNull x y z := by
  intro hxy hyz hzx
  obtain ⟨g, rfl, rfl⟩ := (a2_adj_iff x y).1 hxy
  obtain ⟨c, rfl⟩ : ∃ c, z = g • c := ⟨g⁻¹ • z, (smul_inv_smul g z).symm⟩
  exact triNull_smul g (triNull_base c ((a2Graph_adj_smul_iff g).1 hyz)
    ((a2Graph_adj_smul_iff g).1 hzx)) hxy hyz hzx


theorem a2_triangulableBy : TriangulableBy (a2Graph aNC) triT :=
  TriangulableBy.of_triangulable a2_triangulable fun x y z hxy hyz hzx =>
    triNull_all x y z hxy hyz hzx

end CFSG.Sporadic.Co1Patterson
