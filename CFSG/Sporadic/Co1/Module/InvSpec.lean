
module

public import CFSG.Sporadic.Co1.Module.FormsBase
public import Certificates.Data.CFSGNative.Co1.Involutions

public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative Matrix

@[expose] def matHom : NativeSporadic.Co1 →* Matrix (Fin 24) (Fin 24) (ZMod 2) where
  toFun g := g.val.val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem matHom_injective : Function.Injective matHom := fun _ _ e => Units.ext (Subtype.ext e)

theorem co1Act_eq_mulVec (g : NativeSporadic.Co1) (v : Vec24) : co1Act g v = matHom g *ᵥ v := rfl

theorem matHom_inv_eq {g : NativeSporadic.Co1} {N : Matrix (Fin 24) (Fin 24) (ZMod 2)}
    (h : matHom g * N = 1) : matHom g⁻¹ = N := by
  calc matHom g⁻¹ = matHom g⁻¹ * (matHom g * N) := by rw [h, Matrix.mul_one]
    _ = (matHom g⁻¹ * matHom g) * N := by rw [Matrix.mul_assoc]
    _ = N := by rw [← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]

theorem rowsMatrix_genWordRows (G : Array (Array ℕ)) (w : List ℕ) :
    rowsMatrix 24 (genWordRows G w) = (w.map fun l => rowsMatrix 24 G[l]!).prod := by
  have key : ∀ (w : List ℕ) (acc : Array ℕ),
      rowsMatrix 24 (w.foldl (fun acc l => mulRows 24 acc G[l]!) acc) =
        rowsMatrix 24 acc * (w.map fun l => rowsMatrix 24 G[l]!).prod := by
    intro w
    induction w with
    | nil => intro acc; simp
    | cons l w ih =>
      intro acc
      rw [List.foldl_cons, ih, rowsMatrix_mulRows, List.map_cons, List.prod_cons, Matrix.mul_assoc]
  rw [genWordRows, key, rowsMatrix_idRows, Matrix.one_mul]

theorem rowsKey_eq_ofDigits (x : Array ℕ) : rowsKey x = Nat.ofDigits 16777216 x.toList := by
  unfold rowsKey
  induction x.toList with
  | nil => simp
  | cons a l ih => simp [List.foldr_cons, Nat.ofDigits_cons, ih]

theorem validRows_size {x : Array ℕ} (h : validRows x = true) : x.size = 24 := by
  simp only [validRows, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem validRows_lt {x : Array ℕ} (h : validRows x = true) {r : ℕ} (hr : r ∈ x.toList) :
    r < 16777216 := by
  simp only [validRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hi' : i < x.size := by simpa using hi
  simpa using h.2 i hi'

theorem rowsKey_inj {x y : Array ℕ} (hx : validRows x = true) (hy : validRows y = true)
    (h : rowsKey x = rowsKey y) : x = y := by
  rw [rowsKey_eq_ofDigits, rowsKey_eq_ofDigits] at h
  have hl : x.toList.length = y.toList.length := by
    rw [Array.length_toList, Array.length_toList, validRows_size hx, validRows_size hy]
  exact Array.toList_inj.1 (Nat.ofDigits_inj_of_len_eq (by norm_num) hl
    (fun l hl' => validRows_lt hx hl') (fun l hl' => validRows_lt hy hl') h)

theorem rowsMatrix_injective_of_valid {x y : Array ℕ} (hx : validRows x = true)
    (hy : validRows y = true) (h : rowsMatrix 24 x = rowsMatrix 24 y) : x = y := by
  have hxs := validRows_size hx
  have hys := validRows_size hy
  apply Array.ext (by rw [hxs, hys])
  intro i hix hiy
  have hi : i < 24 := hxs ▸ hix
  have hrow : toVecD 24 (x[i]?.getD 0) = toVecD 24 (y[i]?.getD 0) := by
    funext j
    exact congrFun (congrFun h ⟨i, hi⟩) j
  have hxi : x[i]?.getD 0 = x[i] := by simp [hix]
  have hyi : y[i]?.getD 0 = y[i] := by simp [hiy]
  rw [hxi, hyi] at hrow
  exact toVecD_injective (validRows_lt hx (by simp)) (validRows_lt hy (by simp)) hrow

theorem strictInc_isChain : ∀ l : List ℕ, strictInc l = true → List.IsChain (· < ·) l
  | [], _ => List.isChain_nil
  | [a], _ => List.isChain_singleton a
  | a :: b :: t, h => by
    simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.IsChain.cons_cons h.1 (strictInc_isChain (b :: t) h.2)

theorem distinctKeys_nodup {keys : List ℕ} (h : distinctKeys keys = true) : keys.Nodup := by
  have hp := List.mergeSort_perm keys keyLe
  have hsorted : (keys.mergeSort keyLe).Pairwise (· < ·) :=
    List.isChain_iff_pairwise.1 (strictInc_isChain _ h)
  exact hp.nodup_iff.1 (List.Pairwise.imp (fun h' => ne_of_lt h') hsorted)

theorem ctOK_sound {G Gi : Array (Array ℕ)} {root : Array ℕ} {c : ConjCert}
    (h : ctOK G Gi root c = true) (kk : ℕ → NativeSporadic.Co1)
    (hk : ∀ l < G.size, matHom (kk l) = rowsMatrix 24 G[l]!)
    (hki : ∀ l < G.size, mulRows 24 G[l]! Gi[l]! = idRows 24)
    (s : NativeSporadic.Co1) (hs : matHom s = rowsMatrix 24 root) :
    ∃ f : ℕ → NativeSporadic.Co1,
      (∀ i < c.pts.size, (∃ x ∈ Subgroup.closure (kk '' {l | l < G.size}), f i = x * s * x⁻¹) ∧
        matHom (f i) = rowsMatrix 24 c.pts[i]!) ∧
      ∀ i < c.pts.size, ∀ j < c.pts.size, f i = f j → i = j := by
  unfold ctOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hpos, hroot⟩, hall⟩, hdist⟩ := h
  have hpt := CFSG.Sporadic.Th.allIn_eq_true.1 hall
  have hinvmat : ∀ l < G.size, matHom (kk l)⁻¹ = rowsMatrix 24 Gi[l]! := by
    intro l hl
    apply matHom_inv_eq
    rw [hk l hl, ← rowsMatrix_mulRows, hki l hl, rowsMatrix_idRows]
  have hmain : ∀ i < c.pts.size, ∃ x ∈ Subgroup.closure (kk '' {l | l < G.size}),
      matHom (x * s * x⁻¹) = rowsMatrix 24 c.pts[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have hp := hpt i (Nat.zero_le _) hi
      simp only [ctPointOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
      by_cases hi0 : i = 0
      · subst hi0
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        rw [hroot]
        simpa using hs
      · obtain ⟨-, hp2⟩ := hp
        rcases hp2 with h0 | ⟨⟨hpar, hlab⟩, hconj⟩
        · exact absurd h0 hi0
        · obtain ⟨x', hx', hx'e⟩ := ih (c.par[i]!) hpar (by omega)
          refine ⟨kk (c.lab[i]!) * x', Subgroup.mul_mem _
            (Subgroup.subset_closure ⟨_, hlab, rfl⟩) hx', ?_⟩
          rw [hconj, conjRows, rowsMatrix_mulRows, rowsMatrix_mulRows, ← hk _ hlab, ← hx'e,
            ← hinvmat _ hlab]
          simp only [map_mul, _root_.mul_inv_rev, Matrix.mul_assoc]
  choose! x hx using hmain
  refine ⟨fun i => x i * s * (x i)⁻¹, fun i hi => ⟨⟨x i, (hx i hi).1, rfl⟩, (hx i hi).2⟩, ?_⟩
  intro i hi j hj hij
  have hvalid : ∀ i < c.pts.size, validRows c.pts[i]! = true := by
    intro i hi
    have hp := hpt i (Nat.zero_le _) hi
    simp only [ctPointOK, Bool.and_eq_true] at hp
    exact hp.1
  have hm : rowsMatrix 24 c.pts[i]! = rowsMatrix 24 c.pts[j]! := by
    rw [← (hx i hi).2, ← (hx j hj).2]
    exact congrArg matHom hij
  have hpe := rowsMatrix_injective_of_valid (hvalid i hi) (hvalid j hj) hm
  have hnd := distinctKeys_nodup hdist
  have hlen : (c.pts.toList.map rowsKey).length = c.pts.size := by simp
  have hgi : (c.pts.toList.map rowsKey)[i]'(hlen ▸ hi) = rowsKey c.pts[i]! := by
    simp [getElem!_pos c.pts i hi]
  have hgj : (c.pts.toList.map rowsKey)[j]'(hlen ▸ hj) = rowsKey c.pts[j]! := by
    simp [getElem!_pos c.pts j hj]
  exact (List.Nodup.getElem_inj_iff hnd).1 (hgi.trans ((congrArg rowsKey hpe).trans hgj.symm))

theorem countBelow_eq (p : ℕ → Bool) (n acc : ℕ) :
    countBelow p n acc = acc + ((Finset.range n).filter fun i => p i = true).card := by
  induction n generalizing acc with
  | zero => simp [countBelow]
  | succ n ih =>
    rw [countBelow, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases hp : p n = true
    · simp only [hp, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp)]
      omega
    · simp [hp]

theorem vecMulN_lt (R : Array ℕ) (hR : ∀ j : ℕ, R[j]?.getD 0 < 2 ^ 24) (v : ℕ) :
    vecMulN 24 R v < 2 ^ 24 := by
  have key : ∀ (m acc : ℕ), acc < 2 ^ 24 →
      (List.range m).foldl (fun acc j => if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc)
        acc < 2 ^ 24 := by
    intro m
    induction m with
    | zero => intro acc h; simpa using h
    | succ m ih =>
      intro acc h
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have := ih acc h
      split_ifs
      · exact Nat.xor_lt_two_pow this (hR m)
      · exact this
  exact key 24 0 (by norm_num)

theorem transposeRows_lt (M : Array ℕ) (j : ℕ) : (transposeRows 24 M)[j]?.getD 0 < 2 ^ 24 := by
  unfold transposeRows
  by_cases hj : j < 24
  · simp only [Array.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
    exact ofBits_lt _ _
  · simp [hj]

theorem isFixedN_iff (M : Array ℕ) {x : ℕ} (hx : x < 2 ^ 24) :
    isFixedN (transposeRows 24 M) x = true ↔ rowsMatrix 24 M *ᵥ toVecD 24 x = toVecD 24 x := by
  rw [isFixedN, beq_iff_eq, rowsMatrix_mulVec]
  constructor
  · intro h
    rw [h]
  · intro h
    exact toVecD_injective (vecMulN_lt _ (transposeRows_lt _) _) hx h

theorem toVecD_image_Iio : toVecD 24 '' Set.Iio (2 ^ 24) = Set.univ := by
  have hinj : Set.InjOn (toVecD 24) (Set.Iio (2 ^ 24)) :=
    fun x hx y hy h => toVecD_injective hx hy h
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ Set.finite_univ
  rw [Set.ncard_univ, Set.InjOn.ncard_image hinj, Set.ncard_Iio_nat]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem ncard_eq_countBelow {P : Vec24 → Prop} {p : ℕ → Bool}
    (h : ∀ x < 2 ^ 24, (p x = true ↔ P (toVecD 24 x))) :
    {v : Vec24 | P v}.ncard = countBelow p 16777216 0 := by
  have hset : {v : Vec24 | P v} = toVecD 24 '' {x | x < 2 ^ 24 ∧ p x = true} := by
    ext v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ : v ∈ toVecD 24 '' Set.Iio (2 ^ 24) := by
        rw [toVecD_image_Iio]
        trivial
      exact ⟨x, ⟨hx, (h x hx).2 hv⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hp⟩, rfl⟩
      exact (h x hx).1 hp
  rw [hset, Set.InjOn.ncard_image (fun x hx y hy e => toVecD_injective hx.1 hy.1 e),
    countBelow_eq, zero_add, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
  norm_num

theorem ncard_fix (M : Array ℕ) :
    {v : Vec24 | rowsMatrix 24 M *ᵥ v = v}.ncard = fixCount (transposeRows 24 M) :=
  ncard_eq_countBelow (fun _ hx => isFixedN_iff M hx)

theorem foldl_dot_zmod (x y : ℕ) (m : ℕ) (init : Bool) :
    (if (List.range m).foldl (fun acc j => acc ^^ (x.testBit j && y.testBit j)) init = true
        then (1 : ZMod 2) else 0) =
      (if init = true then 1 else 0) +
        ∑ j ∈ Finset.range m,
          (if (x.testBit j && y.testBit j) = true then (1 : ZMod 2) else 0) := by
  induction m with
  | zero => cases init <;> simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, ← add_assoc, ← ih]
    generalize (List.range m).foldl (fun acc j => acc ^^ (x.testBit j && y.testBit j)) init = b
    cases b <;> cases x.testBit m <;> cases y.testBit m <;> decide

theorem toVecD_dotProduct (x y : ℕ) :
    toVecD 24 x ⬝ᵥ toVecD 24 y = if dotN x y = true then 1 else 0 := by
  unfold dotN
  rw [foldl_dot_zmod]
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  rw [dotProduct, ← Fin.sum_univ_eq_sum_range
      (fun j => if (x.testBit j && y.testBit j) = true then (1 : ZMod 2) else 0) 24]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toVecD_apply, toVecD_apply]
  cases x.testBit j.val <;> cases y.testBit j.val <;> simp

theorem q₀_toVecD (x : ℕ) :
    q₀ (toVecD 24 x) = if q0N (transposeRows 24 qRows) x = true then 1 else 0 := by
  unfold q₀ q0N
  rw [show Qm = rowsMatrix 24 qRows from rfl, rowsMatrix_mulVec, toVecD_dotProduct]

theorem ncard_fixQ (M : Array ℕ) :
    {v : Vec24 | rowsMatrix 24 M *ᵥ v = v ∧ q₀ v = 1}.ncard =
      fixCountQ (transposeRows 24 M) (transposeRows 24 qRows) := by
  refine ncard_eq_countBelow (fun x hx => ?_)
  rw [Bool.and_eq_true, isFixedN_iff M hx, q₀_toVecD]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by simp [h2]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra hq
    simp [hq] at h2

theorem orderOf_eq_of_orderIs {x : NativeSporadic.Co1} {M : Array ℕ}
    (hx : matHom x = rowsMatrix 24 M) {n : ℕ} (hn : 0 < n) (h : orderIs M n = true) :
    orderOf x = n := by
  unfold orderIs at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [orderOf_eq_iff hn]
  have hpow : ∀ m, matHom (x ^ m) = rowsMatrix 24 (powRows 24 M m) := by
    intro m
    rw [map_pow, hx, rowsMatrix_powRows]
  refine ⟨?_, fun m hm hm0 hxm => ?_⟩
  · apply matHom_injective
    rw [hpow, h1, rowsMatrix_idRows, map_one]
  · have hne := (h2 m hm).resolve_left (by omega)
    have hm1 := hpow m
    rw [hxm, map_one] at hm1
    simp only [neqId, List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hne
    obtain ⟨i, hi, j, hj, hij⟩ := hne
    have hc := congrFun (congrFun hm1 ⟨i, hi⟩) ⟨j, hj⟩
    rw [Matrix.one_apply, rowsMatrix_apply, toVecD_apply] at hc
    by_cases hb : (powRows 24 M m)[i]?.getD 0 |>.testBit j <;>
      by_cases hij' : i = j <;> simp_all [Fin.ext_iff]

end CFSG.Sporadic.Co1.Module
