module

public import Certificates.Data.CFSGNative.Chevalley.SteinbergBIWE8Native
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.Timmesfeld.Orders.ExceptionalWeyl

public noncomputable section

namespace CFSG.RankThree.Chevalley.WeylE8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Timmesfeld.ExceptionalOrders
open CFSG.LieType.Chevalley.WE8.Native

abbrev L8 := Fin Tag.E8.rank → ℤ

instance instNeZeroRankE8 : NeZero Tag.E8.rank := ⟨by decide⟩

@[expose] def toL (v : L8) : Vec := List.ofFn v

theorem getD_toL (v : L8) (k : Fin Tag.E8.rank) : (toL v).getD k 0 = v k := by
  rw [toL, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact k.2), List.getElem_ofFn]

theorem toL_injective : Function.Injective toL := fun _ _ h => List.ofFn_injective h

theorem cart_eq (i k : Fin Tag.E8.rank) : cart i k = Tag.cartan .E8 i k := by
  change cart i k = Tag.cartanE 8 i k
  fin_cases i <;> fin_cases k <;> rfl

theorem symmetrizedCartan_E8 (i k : Fin Tag.E8.rank) :
    Tag.symmetrizedCartan .E8 i k = Tag.cartan .E8 i k := by
  simp [Tag.symmetrizedCartan, Tag.symmetrizer]

theorem sum_ofFn_eq (f : Fin Tag.E8.rank → ℤ) :
    (List.ofFn fun k : Fin 8 => f k).sum = ∑ k : Fin Tag.E8.rank, f k := by
  rw [List.sum_ofFn]
  rfl

theorem ofFn_eq (f : Fin Tag.E8.rank → ℤ) :
    (List.ofFn fun k : Fin 8 => f k) = List.ofFn f :=
  rfl

theorem pair_toL (i : Fin Tag.E8.rank) (v : L8) :
    pair i (toL v) = ∑ k, Tag.cartan .E8 i k * v k := by
  rw [pair, sum_ofFn_eq fun k => cart i k * (toL v).getD k 0]
  exact Finset.sum_congr rfl fun k _ => by rw [cart_eq i k, getD_toL v k]

theorem ip_toL (u v : L8) : ip (toL u) (toL v) = iform u v := by
  rw [ip, sum_ofFn_eq fun i => (toL u).getD i 0 * pair i (toL v), iform]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [getD_toL u i, pair_toL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [symmetrizedCartan_E8]
  ring

theorem pair_toL_eq_iform (i : Fin Tag.E8.rank) (v : L8) :
    pair i (toL v) = iform (Pi.single i 1) v := by
  rw [pair_toL, iform_single_left]
  simp [Tag.symmetrizer]

theorem sRefl_toL (j : Fin Tag.E8.rank) (v : L8) :
    sRefl j (toL v) = toL (reflect .E8 j v) := by
  rw [sRefl, ofFn_eq fun k => if (k : ℕ) = j then (toL v).getD k 0 - pair j (toL v)
    else (toL v).getD k 0]
  refine congrArg List.ofFn (funext fun k => ?_)
  rw [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, getD_toL v k, pair_toL]
  by_cases h : (k : ℕ) = (j : ℕ)
  · rw [ite_eq_left h, Fin.ext h, Pi.single_eq_same, mul_one]
  · rw [ite_eq_right h, Pi.single_eq_of_ne (fun e => h (congrArg Fin.val e)), mul_zero,
      sub_zero]

theorem vadd_toL (u v : L8) : vadd (toL u) (toL v) = toL (u + v) := by
  rw [vadd, ofFn_eq fun k => (toL u).getD k 0 + (toL v).getD k 0]
  exact congrArg List.ofFn (funext fun k => by rw [getD_toL u k, getD_toL v k]; rfl)

theorem vsub_toL (u v : L8) : vsub (toL u) (toL v) = toL (u - v) := by
  rw [vsub, ofFn_eq fun k => (toL u).getD k 0 - (toL v).getD k 0]
  exact congrArg List.ofFn (funext fun k => by rw [getD_toL u k, getD_toL v k]; rfl)

theorem vsmul_toL (c : ℤ) (u : L8) : vsmul c (toL u) = toL (c • u) := by
  rw [vsmul, ofFn_eq fun k => c * (toL u).getD k 0]
  exact congrArg List.ofFn (funext fun k => by rw [getD_toL u k]; rfl)

theorem vneg_toL (u : L8) : vneg (toL u) = toL (-u) := by
  rw [vneg, ofFn_eq fun k => -(toL u).getD k 0]
  exact congrArg List.ofFn (funext fun k => by rw [getD_toL u k]; rfl)

theorem basisV_eq (i : Fin Tag.E8.rank) : basisV i = toL (Pi.single i 1) := by
  rw [basisV, ofFn_eq fun k => if (k : ℕ) = i then 1 else 0]
  refine congrArg List.ofFn (funext fun k => ?_)
  by_cases h : (k : ℕ) = (i : ℕ)
  · rw [ite_eq_left h, Fin.ext h, Pi.single_eq_same]
  · rw [ite_eq_right h, Pi.single_eq_of_ne (fun e => h (congrArg Fin.val e))]

theorem rootCodes_eq : rootCodes = Tag.E8.rootCertificate.roots := by
  decide +kernel

theorem rootsL_eq : rootsL = (rootList .E8).map toL := by
  rw [rootList, rootsL, rootCodes_eq, List.map_map]
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  rw [List.getElem_map, List.getElem_map, List.getElem_range]
  simp only [List.length_map] at h1
  change WE8.Native.decodeVec _ = toL (decodeVec _)
  rw [List.getD_eq_getElem _ _ h1]
  rfl

theorem mem_rootsL {v : L8} : toL v ∈ rootsL ↔ IsRoot .E8 v := by
  rw [rootsL_eq, List.mem_map, ← mem_rootList]
  exact ⟨fun ⟨u, hu, huv⟩ => toL_injective huv ▸ hu, fun h => ⟨v, h, rfl⟩⟩

theorem length_rootsL : rootsL.length = 240 := by
  rw [rootsL, List.length_map, rootCodes_eq]
  decide +kernel

theorem rootIdx_lt {v : L8} (hv : IsRoot .E8 v) : rootIdx (toL v) < 240 := by
  rw [← length_rootsL, rootIdx]
  exact List.idxOf_lt_length_of_mem (mem_rootsL.2 hv)

theorem getD_rootIdx {v : L8} (hv : IsRoot .E8 v) : rootsL.getD (rootIdx (toL v)) [] = toL v := by
  have h := List.idxOf_lt_length_of_mem (mem_rootsL.2 hv)
  change rootsL.getD (List.idxOf (toL v) rootsL) [] = toL v
  rw [List.getD_eq_getElem _ _ h, List.getElem_idxOf h]

theorem nodup_rootsL : rootsL.Nodup := by
  rw [rootsL_eq]
  exact nodup_rootList.map toL_injective

theorem getD_roots_map {β : Type} (f : Vec → β) (d : β) {a : ℕ} (ha : a < 240) :
    (roots.map f).getD a d = f (rootsL.getD a []) := by
  have ha' : a < rootsL.length := length_rootsL ▸ ha
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, roots, List.getElem?_toArray,
    List.getElem?_eq_getElem ha', List.getD_eq_getElem _ _ ha']
  rfl

theorem permT_getD (j : Fin Tag.E8.rank) {a : ℕ} (ha : a < 240) :
    (permT.getD j #[]).getD a 0 = rootIdx (sRefl j (rootsL.getD a [])) := by
  have e : permT.getD j #[] = roots.map fun v => rootIdx (sRefl j v) := by
    have hj : (j : ℕ) < 8 := j.2
    simp only [permT, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hj, dite_true,
      Option.getD_some]
  rw [e, getD_roots_map _ _ ha]

theorem negT_getD {a : ℕ} (ha : a < 240) :
    negT.getD a 0 = rootIdx (vneg (rootsL.getD a [])) :=
  getD_roots_map _ _ ha

theorem addT_getD {a b : ℕ} (ha : a < 240) (hb : b < 240) :
    (addT.getD a #[]).getD b 0 = if ip (rootsL.getD a []) (rootsL.getD b []) == -1 then
      rootIdx (vadd (rootsL.getD a []) (rootsL.getD b [])) else 0 := by
  rw [addT, getD_roots_map _ _ ha, getD_roots_map _ _ hb]

abbrev W8 := WeylGroup .E8

abbrev eb (i : Fin Tag.E8.rank) : L8 := Pi.single i 1

@[expose] def code (w : W8) : ICode :=
  List.ofFn fun i : Fin Tag.E8.rank => rootIdx (toL (w • eb i))

theorem isRoot_col (w : W8) (i : Fin Tag.E8.rank) : IsRoot .E8 (w • eb i) :=
  IsRoot.smul (isRoot_single _ i) w

theorem length_code (w : W8) : (code w).length = 8 := List.length_ofFn

theorem getD_code (w : W8) (i : Fin Tag.E8.rank) :
    (code w).getD i 0 = rootIdx (toL (w • eb i)) := by
  rw [code, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.2), List.getElem_ofFn]

theorem getD_code_lt (w : W8) (i : Fin Tag.E8.rank) : (code w).getD i 0 < 240 := by
  rw [getD_code]
  exact rootIdx_lt (isRoot_col w i)

theorem col_code (w : W8) (i : Fin Tag.E8.rank) :
    rootsL.getD ((code w).getD i 0) [] = toL (w • eb i) := by
  rw [getD_code, getD_rootIdx (isRoot_col w i)]

theorem code_injective : Function.Injective code := by
  intro w w' h
  refine ext_single fun i => toL_injective ?_
  rw [← col_code w i, ← col_code w' i, h]

theorem iform_eb (i j : Fin Tag.E8.rank) : iform (eb i) (eb j) = Tag.cartan .E8 i j := by
  rw [iform_single_left]
  simp [Tag.symmetrizer, Pi.single_apply]

theorem cartan_symm (i j : Fin Tag.E8.rank) : Tag.cartan .E8 i j = Tag.cartan .E8 j i := by
  rw [← iform_eb, ← iform_eb, iform_comm]

theorem cartan_off (i j : Fin Tag.E8.rank) (h : i ≠ j) :
    Tag.cartan .E8 j i = 0 ∨ Tag.cartan .E8 j i = -1 := by
  revert h
  change i ≠ j → Tag.cartanE 8 j i = 0 ∨ Tag.cartanE 8 j i = -1
  fin_cases i <;> fin_cases j <;> decide

theorem simple_smul_eb (j i : Fin Tag.E8.rank) :
    simple .E8 j • eb i = eb i - Tag.cartan .E8 j i • eb j := by
  rw [simple_smul, reflect]
  congr 2
  simp [Pi.single_apply]

theorem conj_smul_eb (j i : Fin Tag.E8.rank) (w : W8) :
    (simple .E8 j * w * simple .E8 j) • eb i =
      simple .E8 j • (w • eb i - Tag.cartan .E8 j i • (w • eb j)) := by
  rw [mul_smul, mul_smul, simple_smul_eb, smul_sub, smul_comm]

theorem ofFn_eq' {α : Type} (f : Fin Tag.E8.rank → α) :
    (List.ofFn fun k : Fin 8 => f k) = List.ofFn f :=
  rfl

theorem code_conj (j : Fin Tag.E8.rank) (w : W8) :
    code (simple .E8 j * w * simple .E8 j) = conjI j (code w) := by
  rw [conjI, ofFn_eq' fun i => if (i : ℕ) = j then
      negT.getD ((permT.getD j #[]).getD ((code w).getD j 0) 0) 0
    else if cart j i = -1 then
      (permT.getD j #[]).getD ((addT.getD ((code w).getD i 0) #[]).getD ((code w).getD j 0) 0) 0
    else (permT.getD j #[]).getD ((code w).getD i 0) 0, code]
  refine congrArg List.ofFn (funext fun i => ?_)
  rw [conj_smul_eb]
  have hj := getD_code_lt w j
  have hi := getD_code_lt w i
  by_cases hij : (i : ℕ) = j
  · have e : i = j := Fin.ext hij
    subst e
    rw [ite_eq_left hij, Tag.cartan_self, permT_getD i hj, col_code, sRefl_toL, ← simple_smul,
      negT_getD (rootIdx_lt (IsRoot.smul (isRoot_col w i) _)),
      getD_rootIdx (IsRoot.smul (isRoot_col w i) _),
      vneg_toL]
    congr 2
    rw [two_smul, sub_add_cancel_left, smul_neg]
  · rw [ite_eq_right hij, cart_eq]
    have hne : i ≠ j := fun e => hij (congrArg Fin.val e)
    rcases cartan_off i j hne with h0 | h1
    · rw [h0, ite_eq_right (by decide), zero_smul, sub_zero, permT_getD j hi, col_code, sRefl_toL,
        ← simple_smul]
    · have hip : ip (rootsL.getD ((code w).getD i 0) []) (rootsL.getD ((code w).getD j 0) []) =
          -1 := by
        rw [col_code, col_code, ip_toL, iform_smul, iform_eb, cartan_symm, h1]
      have hsum : IsRoot .E8 (w • eb i + w • eb j) := by
        have e : reflect .E8 j (eb i) = eb i + eb j := by
          rw [← simple_smul, simple_smul_eb, h1, neg_one_smul, sub_neg_eq_add]
        have h := IsRoot.reflect j (isRoot_single .E8 i)
        rw [e] at h
        rw [← smul_add]
        exact IsRoot.smul h w
      rw [h1, ite_eq_left rfl, addT_getD hi hj]
      simp only [hip, beq_self_eq_true, ↓reduceIte]
      rw [col_code, col_code, vadd_toL, permT_getD j (rootIdx_lt hsum), getD_rootIdx hsum,
        sRefl_toL, ← simple_smul, neg_one_smul, sub_neg_eq_add]

theorem applyI_code (w : W8) (v : L8) : applyI (code w) (toL v) = toL (w • v) := by
  rw [applyI, ofFn_eq' fun i => (List.ofFn fun k : Fin 8 =>
    (toL v).getD k 0 * (rootsL.getD ((code w).getD k 0) []).getD i 0).sum]
  refine congrArg List.ofFn (funext fun i => ?_)
  rw [sum_ofFn_eq fun k => (toL v).getD k 0 * (rootsL.getD ((code w).getD k 0) []).getD i 0,
    smul_eq_sum_smul_single w v, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [getD_toL, col_code, getD_toL]
  rfl

theorem code_mul (w w' : W8) : code (w * w') = mulI (code w) (code w') := by
  have e : code w' = List.ofFn fun i : Fin Tag.E8.rank => rootIdx (toL (w' • eb i)) := rfl
  rw [mulI, e, List.map_ofFn, code]
  refine congrArg List.ofFn (funext fun i => ?_)
  simp only [Function.comp_apply]
  rw [getD_rootIdx (isRoot_col w' i), applyI_code, mul_smul]

theorem code_one : code 1 = List.ofFn fun i : Fin Tag.E8.rank => rootIdx (basisV i) := by
  rw [code]
  exact congrArg List.ofFn (funext fun i => by rw [one_smul, basisV_eq])

theorem code_neg {z : W8} (hz : ∀ v : L8, z • v = -v) (w : W8) : code (z * w) = negI (code w) := by
  rw [negI, code, code, List.map_ofFn]
  refine congrArg List.ofFn (funext fun i => ?_)
  simp only [Function.comp_apply]
  rw [negT_getD (rootIdx_lt (isRoot_col w i)), getD_rootIdx (isRoot_col w i), vneg_toL,
    mul_smul, hz]

theorem iform_self_of_isRoot {β : L8} (hβ : IsRoot .E8 β) : iform β β = 2 := by
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
  rw [iform_smul, iform_eb, Tag.cartan_self]

theorem rRefl_toL {β : L8} (hβ : IsRoot .E8 β) (v : L8) :
    rRefl (toL β) (toL v) = toL (rootReflection β • v) := by
  have h := corootPair_mul hβ v
  rw [iform_self_of_isRoot hβ] at h
  have hc : corootPair β v = iform β v := by linarith
  rw [rRefl, ip_toL, vsmul_toL, vsub_toL, rootReflection_smul hβ, hc]

theorem code_frameProd (frame : List L8) (h : ∀ β ∈ frame, IsRoot .E8 β) :
    code ((frame.map rootReflection).prod) = frameCode (frame.map toL) := by
  rw [frameCode, ofFn_eq' fun i => rootIdx ((frame.map toL).foldr rRefl (basisV i)), code]
  refine congrArg List.ofFn (funext fun i => ?_)
  congr 1
  rw [basisV_eq]
  induction frame with
  | nil => rw [List.map_nil, List.prod_nil, one_smul, List.map_nil, List.foldr_nil]
  | cons β fr ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, List.map_cons, List.foldr_cons,
      ← rRefl_toL (h β List.mem_cons_self), ih fun γ hγ => h γ (List.mem_cons_of_mem _ hγ)]

theorem code_wordProd (ω : List (Fin Tag.E8.rank)) :
    code ((coxeterSystem .E8).wordProd ω) = wordCode (ω.map Fin.val) := by
  rw [wordCode, ofFn_eq' fun i => rootIdx ((ω.map Fin.val).foldr sRefl (basisV i)), code]
  refine congrArg List.ofFn (funext fun i => ?_)
  congr 1
  rw [basisV_eq]
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.map_nil, List.foldr_nil]
  | cons j ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, List.map_cons, List.foldr_cons, ← ih, sRefl_toL,
      ← simple_smul]

theorem negCount_code (w : W8) :
    WE8.Native.negCount (code w) = {α : L8 | IsRoot .E8 α ∧ w • α = -α}.ncard := by
  classical
  rw [ncard_setOf_isRoot_and, WE8.Native.negCount, rootsL_eq, List.filter_map, List.length_map,
    ← List.countP_eq_length_filter]
  refine List.countP_congr fun α _ => ?_
  simp only [Function.comp_apply, applyI_code, vneg_toL, beq_iff_eq, decide_eq_true_eq]
  exact toL_injective.eq_iff

end CFSG.RankThree.Chevalley.WeylE8
