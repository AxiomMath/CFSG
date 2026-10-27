
module

public import Certificates.Kernel.Co1ThreeK.GlueNodes
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1Cl CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KS.SporSch.M24
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree CFSG.Sporadic.SmallF2
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance Timmesfeld.Co1Leaf
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T (lG wG eltG aGA SplitData qG Qg root
  mem_expVecs_iff)

theorem expVecs_nodupK (p : ℕ) : ∀ r, (expVecs p r).Nodup
  | 0 => List.nodup_singleton _
  | r + 1 => by
    rw [expVecs, List.nodup_flatMap]
    refine ⟨fun e _ => List.Nodup.map (fun k k' h => by simpa using h) List.nodup_range, ?_⟩
    refine (expVecs_nodupK p r).imp fun {a b} hne x hx hx' => hne ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨k', -, h⟩ := List.mem_map.1 hx'
    exact (List.append_inj' h rfl).1.symm

theorem six_of_length {l : List ℕ} (h : l.length = 6) :
    ∃ x0 x1 x2 x3 x4 x5, l = [x0, x1, x2, x3, x4, x5] := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, l⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at h <;>
    first | omega | exact ⟨_, _, _, _, _, _, rfl⟩

theorem aGA_eq_aK : aGA = [aK 0 (by norm_num), aK 1 (by norm_num), aK 2 (by norm_num),
    aK 3 (by norm_num), aK 4 (by norm_num), aK 5 (by norm_num)] := rfl

theorem eltG_six (g0 g1 g2 g3 g4 g5 : ↥GA) (x0 x1 x2 x3 x4 x5 : ℕ) :
    eltG [g0, g1, g2, g3, g4, g5] [x0, x1, x2, x3, x4, x5] =
      g0 ^ x0 * g1 ^ x1 * g2 ^ x2 * g3 ^ x3 * g4 ^ x4 * g5 ^ x5 := by
  simp only [eltG, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil,
    one_mul]

theorem epM_six {M : Type*} [Monoid M] (f : ℕ → M) (v : ℕ) :
    epM f 3 [0, 1, 2, 3, 4, 5] v 1 = f 0 ^ (v % 3) * f 1 ^ (v / 3 % 3) * f 2 ^ (v / 3 / 3 % 3) *
      f 3 ^ (v / 3 / 3 / 3 % 3) * f 4 ^ (v / 3 / 3 / 3 / 3 % 3) *
        f 5 ^ (v / 3 / 3 / 3 / 3 / 3 % 3) := by
  simp only [epM, one_mul]

theorem coe_eltG_six (x0 x1 x2 x3 x4 x5 : ℕ) :
    (eltG aGA [x0, x1, x2, x3, x4, x5] : GL24) =
      a 0 ^ x0 * a 1 ^ x1 * a 2 ^ x2 * a 3 ^ x3 * a 4 ^ x4 * a 5 ^ x5 := by
  rw [aGA_eq_aK, eltG_six]
  simp only [Subgroup.coe_mul, Subgroup.coe_pow]
  rfl

theorem eProd_six (b : Fin 6 → ZMod 3) :
    eProd b = a 0 ^ (b 0).val * a 1 ^ (b 1).val * a 2 ^ (b 2).val * a 3 ^ (b 3).val *
      a 4 ^ (b 4).val * a 5 ^ (b 5).val := by
  simp only [eProd, List.finRange_succ, List.finRange_zero, List.map_cons, List.map_map,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

section Split

theorem eltG_six_inj {x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℕ} (hx0 : x0 < 3) (hx1 : x1 < 3)
    (hx2 : x2 < 3) (hx3 : x3 < 3) (hx4 : x4 < 3) (hx5 : x5 < 3) (hy0 : y0 < 3) (hy1 : y1 < 3)
    (hy2 : y2 < 3) (hy3 : y3 < 3) (hy4 : y4 < 3) (hy5 : y5 < 3)
    (h : eltG aGA [x0, x1, x2, x3, x4, x5] = eltG aGA [y0, y1, y2, y3, y4, y5]) :
    [x0, x1, x2, x3, x4, x5] = [y0, y1, y2, y3, y4, y5] := by
  have e := congrArg Subtype.val h
  rw [coe_eltG_six, coe_eltG_six] at e
  have ex : eProd ![(x0 : ZMod 3), x1, x2, x3, x4, x5] =
      a 0 ^ x0 * a 1 ^ x1 * a 2 ^ x2 * a 3 ^ x3 * a 4 ^ x4 * a 5 ^ x5 := by
    rw [eProd_six]
    simp only [Matrix.cons_val, ZMod.val_natCast, Nat.mod_eq_of_lt hx0, Nat.mod_eq_of_lt hx1,
      Nat.mod_eq_of_lt hx2, Nat.mod_eq_of_lt hx3, Nat.mod_eq_of_lt hx4, Nat.mod_eq_of_lt hx5]
  have ey : eProd ![(y0 : ZMod 3), y1, y2, y3, y4, y5] =
      a 0 ^ y0 * a 1 ^ y1 * a 2 ^ y2 * a 3 ^ y3 * a 4 ^ y4 * a 5 ^ y5 := by
    rw [eProd_six]
    simp only [Matrix.cons_val, ZMod.val_natCast, Nat.mod_eq_of_lt hy0, Nat.mod_eq_of_lt hy1,
      Nat.mod_eq_of_lt hy2, Nat.mod_eq_of_lt hy3, Nat.mod_eq_of_lt hy4, Nat.mod_eq_of_lt hy5]
  have hb := @eHom_injective (Multiplicative.ofAdd ![(x0 : ZMod 3), x1, x2, x3, x4, x5])
    (Multiplicative.ofAdd ![(y0 : ZMod 3), y1, y2, y3, y4, y5]) (ex.trans (e.trans ey.symm))
  have hv : ∀ i : Fin 6, (![(x0 : ZMod 3), x1, x2, x3, x4, x5] i).val =
      (![(y0 : ZMod 3), y1, y2, y3, y4, y5] i).val := fun i =>
    congrArg (fun m => (Multiplicative.toAdd m i).val) hb
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  simp only [Matrix.cons_val, ZMod.val_natCast] at h0 h1 h2 h3 h4 h5
  simp only [List.cons.injEq, and_true]
  omega

theorem eSplitK : SplitData (Co1T.Native.aGens ()) aGA where
  rep := Co1T.aGens_rep
  wf := by
    intro g hg
    rw [Co1T.Native.aGens, CertificateChecks.KernelSporSch.Co1Elem.aRows_eq, List.mem_map] at hg
    obtain ⟨i, -, rfl⟩ := hg
    unfold Native.wf
    rw [Bool.and_eq_true]
    refine ⟨by simp [MatL.unpack_size], ?_⟩
    rw [Array.all_eq_true]
    intro i hi
    rw [MatL.unpack_getElem]
    exact decide_eq_true (MatL.rowV_lt _ i)
  comm := by
    intro f hf f' hf'
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hf
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hf'
    exact Subtype.ext (a_comm i j).eq
  cube := by
    intro f hf
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hf
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact a_pow_three i
  nodup := by
    have hlen : (Co1T.Native.aGens ()).length = 6 := by simp [Co1T.Native.aGens]
    rw [hlen]
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) (expVecs_nodupK 3 6)
    have e : eltG aGA x = eltG aGA y := by
      have h1 := Co1T.mrep_eltR Co1T.aGens_rep x
      have h2 := Co1T.mrep_eltR Co1T.aGens_rep y
      rw [hxy] at h1
      exact Subtype.ext (h1.eq h2)
    obtain ⟨hlx, hx3⟩ := mem_expVecs_iff.1 hx
    obtain ⟨hly, hy3⟩ := mem_expVecs_iff.1 hy
    obtain ⟨x0, x1, x2, x3, x4, x5, rfl⟩ := six_of_length hlx
    obtain ⟨y0, y1, y2, y3, y4, y5, rfl⟩ := six_of_length hly
    exact eltG_six_inj (hx3 _ (by simp)) (hx3 _ (by simp)) (hx3 _ (by simp)) (hx3 _ (by simp))
      (hx3 _ (by simp)) (hx3 _ (by simp)) (hy3 _ (by simp)) (hy3 _ (by simp)) (hy3 _ (by simp))
      (hy3 _ (by simp)) (hy3 _ (by simp)) (hy3 _ (by simp)) e

end Split

@[expose] def digK (v : ℕ) : List ℕ :=
  [v % 3, v / 3 % 3, v / 3 / 3 % 3, v / 3 / 3 / 3 % 3, v / 3 / 3 / 3 / 3 % 3,
    v / 3 / 3 / 3 / 3 / 3 % 3]

section Codes

theorem eQ_eltG (v : ℕ) : eQ nodeK v = eltG aGA (digK v) := by
  rw [eQ, epM_six, aGA_eq_aK, digK, eltG_six, nodeK_a (i := 0) (by norm_num),
    nodeK_a (i := 1) (by norm_num), nodeK_a (i := 2) (by norm_num),
    nodeK_a (i := 3) (by norm_num), nodeK_a (i := 4) (by norm_num),
    nodeK_a (i := 5) (by norm_num)]

theorem eQ_injK : ∀ v < 729, ∀ w < 729, eQ nodeK v = eQ nodeK w → v = w := by
  intro v hv w hw h
  rw [eQ_eltG, eQ_eltG, digK, digK] at h
  have e := eltG_six_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) h
  simp only [List.cons.injEq, and_true] at e
  omega

theorem nodeK_mem_T {i : ℕ} (hi : i < 6) : nodeK i ∈ eSplitK.T := by
  rw [Co1T.SplitData.T_eq_closure, nodeK_a hi]
  refine Subgroup.subset_closure ?_
  change aK i hi ∈ aGA
  rw [aGA_eq_aK]
  interval_cases i <;> simp

theorem eQ_mem_T (v : ℕ) : eQ nodeK v ∈ eSplitK.T := eQ_mem_closure (fun _ hi => nodeK_mem_T hi) v

theorem wG_letter {i : ℕ} (hi : i < 6) : wG [2 * i + 2] = aK i hi := by
  apply Subtype.ext
  interval_cases i <;> exact one_mul _

theorem qGenWords_eq : Co1T.Data.qGenWords = [[2], [4], [6], [8], [10], [12],
    Co1T.Data.qGenWords.getD 6 [], Co1T.Data.qGenWords.getD 7 []] := rfl

theorem qG_eq : qG = [nodeK 0, nodeK 1, nodeK 2, nodeK 3, nodeK 4, nodeK 5, nodeK 9, nodeK 10] := by
  rw [Co1T.qG, qGenWords_eq, nodeK_a (i := 0) (by norm_num), nodeK_a (i := 1) (by norm_num),
    nodeK_a (i := 2) (by norm_num), nodeK_a (i := 3) (by norm_num),
    nodeK_a (i := 4) (by norm_num), nodeK_a (i := 5) (by norm_num), nodeK_q (j := 0) (by norm_num),
    nodeK_q (j := 1) (by norm_num), ← wG_letter (i := 0) (by norm_num),
    ← wG_letter (i := 1) (by norm_num), ← wG_letter (i := 2) (by norm_num),
    ← wG_letter (i := 3) (by norm_num), ← wG_letter (i := 4) (by norm_num),
    ← wG_letter (i := 5) (by norm_num)]
  rfl

theorem Qg_eq : Qg = Subgroup.closure ({nodeK 0, nodeK 1, nodeK 2, nodeK 3, nodeK 4, nodeK 5,
    nodeK 9, nodeK 10} : Set ↥GA) := by
  rw [Co1T.Qg, qG_eq]
  congr 1
  ext x
  simp

theorem card_QgK : Nat.card Qg = 3 ^ 9 := by
  rw [Qg_eq]
  exact card_closure qHypK eQ_injK

theorem fusion_rootK {t : ↥GA} (ht : t ∈ Qg) (hto : orderOf t = 3) :
    t ∈ eSplitK.T ∨ ∃ j, (j = 0 ∨ j = 1 ∨ j = 2) ∧ ∃ g : ↥GA, t = g * root j * g⁻¹ := by
  rw [Qg_eq] at ht
  have ht' : t ∈ codeSet nodeK := closure_le_codeSub qHypK ht
  obtain ⟨c, hc, rfl⟩ := mem_codeSet.1 ht'
  rcases Nat.lt_or_ge c 729 with hc7 | hc7
  · left
    rw [mdlQ, Nat.div_eq_of_lt hc7, Nat.mod_eq_of_lt hc7, Nat.add_zero, f_twelve qHypK, one_mul]
    exact eQ_mem_T c
  · right
    have h3 : mdlQ nodeK c ^ 3 = 1 := by rw [← hto]; exact pow_orderOf_eq_one _
    obtain ⟨r, hr, hconj⟩ := fus_rep qHypK (fun x hx h => mdlQ_eq_one qHypK eQ_injK hx h) c hc7 hc h3
    have hRP := kQRep
    simp only [Bool.and_eq_true] at hRP
    have hlen : FM.RP.length = 42 := by
      have h1 : lenL FM.RP = 42 := Nat.eq_of_beq_eq_true hRP.1.1
      rwa [CFSG.KC.Co1Cl.lenL_eq] at h1
    obtain ⟨i, hi, hri⟩ := List.getElem_of_mem hr
    have hi42 : i < 42 := hlen ▸ hi
    have hget : getL 0 FM.RP i = r := by
      rw [CFSG.KC.Co1Cl.getL_eq, List.getD_eq_getElem _ _ hi]
      exact hri
    subst hget
    obtain ⟨hj, -, hlet, he⟩ := rep_root qHypK hi42
    rw [matK_wordWK hlet, matK_RM hj] at he
    have hn : wG (getLL Co1T.Data.repConj i) * mdlQ nodeK (getL 0 FM.RP i) =
        root (getL 0 Co1T.Data.repRoot i) * wG (getLL Co1T.Data.repConj i) :=
      ιK_injective (by rw [map_mul, map_mul]; exact he)
    set n := wG (getLL Co1T.Data.repConj i)
    set j := getL 0 Co1T.Data.repRoot i
    refine ⟨j, by omega, ?_⟩
    obtain ⟨g, hg⟩ := isConj_iff.1 hconj
    refine ⟨g * n⁻¹, ?_⟩
    rw [← hg]
    have e : mdlQ nodeK (getL 0 FM.RP i) = n⁻¹ * root j * n := by
      rw [mul_assoc, ← hn]
      group
    rw [e]
    group

end Codes

end CertificateChecks.KernelCo1ThreeK

end
