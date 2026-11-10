
module

public import CFSG.Sporadic.Co2Schreier.KerCheckBase
public import CFSG.Sporadic.Co2Schreier.CentralizersBase
public import CFSG.Sporadic.Co2Schreier.CoresBase
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Schreier.CoreCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ChainCheckBase
public meta import Std.Data.HashMap
public import CFSG.Sporadic.Co2Schreier.KerCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.CoreCheckBase
public import CFSG.Sporadic.Co2Schreier.OrbitCheck
public meta import CFSG.Sporadic.Co2Schreier.OrbitCheck
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

section Hom

variable {G H : Type*} [Group G] [Group H] (f : G →* H)

theorem getD_map_hom (gs : List G) (k : ℕ) : (gs.map f).getD k 1 = f (gs.getD k 1) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases gs[k]? <;> simp

theorem map_letterValue (gs : List G) (l : ℤ) :
    f (letterValue gs l) = letterValue (gs.map f) l := by
  unfold letterValue
  split_ifs
  · rw [getD_map_hom]
  · rw [map_inv, getD_map_hom]

theorem map_wordValue (gs : List G) (w : List ℤ) :
    f (wordValue gs w) = wordValue (gs.map f) w := by
  unfold wordValue
  rw [map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun l _ => map_letterValue f gs l)

theorem map_extendTuple : ∀ (gs : List G) (ds : List (List ℤ)),
    (extendTuple gs ds).map f = extendTuple (gs.map f) ds
  | _, [] => rfl
  | gs, w :: ds => by
    rw [extendTuple_cons, extendTuple_cons, map_extendTuple _ ds, List.map_append,
      List.map_singleton, map_wordValue]

theorem map_getD_extendTuple (gs : List G) (ds : List (List ℤ)) (j : ℕ) :
    f ((extendTuple gs ds).getD j 1) = (extendTuple (gs.map f) ds).getD j 1 := by
  rw [← map_extendTuple, getD_map_hom]

end Hom

structure KerFacts : Prop where
  zs_size : (kerData.zs.size == 32) = true
  d_size : (kerData.d.size == 2) = true
  r_size : (kerData.r.size == kerData.rWords.length) = true
  surv : (kerData.survivors == [[0, 0], [0, 9]]) = true
  cand : allLt 32 (fun k0 => allLt 32 fun k1 =>
    !candOK kerData k0 k1 || kerData.survivors.contains [k0, k1]) = true
  inv : allLt 32 (fun k0 => allLt 32 fun k1 =>
    allInv (extendArrs (candArrs kerData k0 k1) kerData.derivD) &&
      allInv (extendArrs (candArrs kerData k0 k1) kerData.derivLegacy)) = true
  invD : allInv (extendArrs kerData.d kerData.derivD) = true
  extD : extWordsOK 2 kerData.derivD = true
  extL : extWordsOK 2 kerData.derivLegacy = true
  rW : kerData.rWords.all (lettersOK (2 + kerData.derivLegacy.length)) = true
  addW : kerData.addWords.all (lettersOK 2) = true
  siftD : kerData.fixedIdx.all (fun j => decide (j < 2 + kerData.derivD.length) &&
    siftA 2300 kerData.lv kerData.base 0 (extendArrs kerData.d kerData.derivD)[j]!) = true
  siftAdd : kerData.addWords.all (fun w =>
    siftA 2300 kerData.lv kerData.base 0 (wordArr kerData.d w)) = true
  zs0 : eqA 2300 kerData.zs[0]! (idA 2300) = true
  comm0 : commA kerData.d[0]! kerData.z = true
  comm1 : (!commA kerData.d[1]! kerData.z) = true
  conj1 : eqA 2300 (compA 2300 kerData.z kerData.d[1]!)
    (compA 2300 (compA 2300 kerData.d[1]! kerData.zs[9]!) kerData.z) = true

def zeta (k : ℕ) : Equiv.Perm (Fin 2300) := eltE enumR (centerIdxR.getD k 0)

theorem centerIdxR_length : centerIdxR.length = 32 := rfl

theorem centerIdxR_lt : ∀ k < 32, centerIdxR.getD k 0 < 2048 := by
  decide

theorem toArray_map_getElem! {β γ : Type*} [Inhabited γ] (l : List β) (g : β → γ) (d : β)
    {k : ℕ} (hk : k < l.length) : (l.map g).toArray[k]! = g (l.getD k d) := by
  rw [getElem!_pos _ k (by simpa using hk), List.getD_eq_getElem _ _ hk]
  simp

theorem dTuple_eq : dTuple = [dTuple.getD 0 1, dTuple.getD 1 1] := by
  obtain ⟨a, b, h⟩ := List.length_eq_two.1 dTuple_length
  rw [h]
  rfl

theorem dTuple_getD_mem (i : ℕ) : dTuple.getD i 1 ∈ co2P := by
  rw [List.getD_eq_getElem?_getD]
  cases h : dTuple[i]? with
  | none => exact co2P.one_mem
  | some g => exact dTuple_mem g (List.mem_of_getElem? h)

theorem dTuple_getD_mem_D (i : ℕ) : dTuple.getD i 1 ∈ locD := by
  rw [List.getD_eq_getElem?_getD]
  cases h : dTuple[i]? with
  | none => exact locD.one_mem
  | some g => exact Subgroup.subset_closure (List.mem_of_getElem? h)

def dP (i : ℕ) : co2P := ⟨dTuple.getD i 1, dTuple_getD_mem i⟩

def dPs : List co2P := [dP 0, dP 1]

theorem dPs_map_subtype : dPs.map co2P.subtype = dTuple := by
  rw [dTuple_eq]
  rfl

def candTuple (k0 k1 : ℕ) : List (Equiv.Perm (Fin 2300)) :=
  [dTuple.getD 0 1 * zeta k0, dTuple.getD 1 1 * zeta k1]

theorem repTuple_pair {a b : Array ℕ} {x y : Equiv.Perm (Fin 2300)} (ha : Rep 2300 a x)
    (hb : Rep 2300 b y) : RepTuple 2300 #[a, b] [x, y] := by
  refine ⟨rfl, fun h hh => ?_⟩
  have hh' : h < 2 := hh
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · exact ha
  · exact hb

theorem candTuple_length (k0 k1 : ℕ) : (candTuple k0 k1).length = 2 := rfl

section Fix

variable {α : MulAut co2P}
  (hα : ∀ c : co2P, (c : Equiv.Perm (Fin 2300)) ∈ locC → α c = c)
include hα

theorem fix_of_mem_S {c : co2P} (hc : (c : Equiv.Perm (Fin 2300)) ∈ locS) : α c = c :=
  hα c (locS_le_C hc)

omit hα in
theorem map_dPs {k0 k1 : ℕ}
    (h0 : ((α (dP 0) : co2P) : Equiv.Perm (Fin 2300)) = dTuple.getD 0 1 * zeta k0)
    (h1 : ((α (dP 1) : co2P) : Equiv.Perm (Fin 2300)) = dTuple.getD 1 1 * zeta k1) :
    (dPs.map α.toMonoidHom).map co2P.subtype = candTuple k0 k1 := by
  simp only [dPs, List.map_cons, List.map_nil, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
    h0, h1, candTuple]

end Fix

theorem closure_subtype_preimage_eq_top {G : Type*} [Group G] {K : Subgroup G} {X : Set G}
    (hX : Subgroup.closure X = K) : Subgroup.closure (K.subtype ⁻¹' X) = ⊤ := by
  subst hX
  exact Subgroup.closure_closure_coe_preimage

end CFSG.Sporadic.Co2Schreier
