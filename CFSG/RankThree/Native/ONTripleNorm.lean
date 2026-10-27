module

public import CFSG.RankThree.Native.ONTripleSylow

public noncomputable section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.ONSchreier CFSG.ONSchreier.Native Subgroup

@[expose] def nG (k : ℕ) : GM := ⟨eM (if k = 0 then rN1 else rN2), eM_mem _⟩

@[expose] def cN (k i : ℕ) : ℕ :=
  ((conjData.filter fun d => d.1 == (if k = 0 then rN1 else rN2) && d.2.1 == i).getD 0
    (0, 0, 0, [])).2.2.1

@[expose] def eN (k i : ℕ) : List ℕ :=
  ((conjData.filter fun d => d.1 == (if k = 0 then rN1 else rN2) && d.2.1 == i).getD 0
    (0, 0, 0, [])).2.2.2

@[expose] def matN (k : ℕ) (i j : Fin 4) : ZMod 3 := ((eN k i).getD j 0 : ZMod 3)

@[expose] def vmul (M : Fin 4 → Fin 4 → ZMod 3) (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  fun j => v 0 * M 0 j + v 1 * M 1 j + v 2 * M 2 j + v 3 * M 3 j

@[expose] def vecWord (w : List ℕ) (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  w.foldl (fun u k => vmul (matN k) u) v

@[expose] def wordN (w : List ℕ) : GM := (w.map nG).prod

theorem conjData_spec (k : ℕ) (hk : k < 2) (i : ℕ) (hi : i < 4) :
    ((if k = 0 then rN1 else rN2), i, cN k i, eN k i) ∈ conjData := by
  interval_cases k <;> interval_cases i <;> decide

theorem eN_lt (k : ℕ) (hk : k < 2) (i : ℕ) (hi : i < 4) (j : ℕ) (hj : j < 4) :
    (eN k i).getD j 0 < 3 := by
  interval_cases k <;> interval_cases i <;> interval_cases j <;> decide

theorem cN_lt (k : ℕ) (hk : k < 2) (i : ℕ) (hi : i < 4) : cN k i < 3 := by
  interval_cases k <;> interval_cases i <;> decide

theorem eN_length (k : ℕ) (hk : k < 2) (i : ℕ) (hi : i < 4) : (eN k i).length = 4 := by
  interval_cases k <;> interval_cases i <;> rfl

theorem conj_xM (k : ℕ) (hk : k < 2) (i : Fin 4) :
    (eM (if k = 0 then rN1 else rN2))⁻¹ * xM i * eM (if k = 0 then rN1 else rN2) =
      xM 3 ^ (eN k i).getD 3 0 * xM 2 ^ (eN k i).getD 2 0 * xM 1 ^ (eN k i).getD 1 0 *
        xM 0 ^ (eN k i).getD 0 0 * zM ^ cN k i := by
  have hd := conj_facts _ (conjData_spec k hk i i.isLt)
  rw [← zM_eq]
  simp only [mul_assoc] at hd ⊢
  exact hd

theorem nG_mem_conj (k : ℕ) (hk : k < 2) (i : Fin 4) :
    (nG k)⁻¹ * xG i * nG k = threeNF zG xG (cN k i : ZMod 3) (fun j => matN k i j) := by
  apply Subtype.ext
  have hv : ∀ j : Fin 4, ((matN k i j).val) = (eN k i).getD j.val 0 := fun j => by
    rw [matN, ZMod.val_natCast, Nat.mod_eq_of_lt (eN_lt k hk i i.isLt j j.isLt)]
  have hc : (cN k i : ZMod 3).val = cN k i := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (cN_lt k hk i i.isLt)]
  simp only [threeNF, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, nG, xG, zG, hv, hc]
  exact conj_xM k hk i

theorem conj_mem_P0 (k : ℕ) (hk : k < 2) {g : GM} (hg : g ∈ P0G) :
    (nG k)⁻¹ * g * nG k ∈ P0G := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | ⟨i, rfl⟩
    · rw [show (nG k)⁻¹ * zG * nG k = zG by
        rw [mul_assoc, zG_central, ← mul_assoc, inv_mul_cancel, one_mul]]
      exact ThreeQRel.x_mem
    · rw [nG_mem_conj k hk i]
      exact ThreeQRel.nf_mem _ _
  | one => rw [mul_one, inv_mul_cancel]; exact one_mem _
  | mul a b _ _ ha hb =>
    rw [show (nG k)⁻¹ * (a * b) * nG k = ((nG k)⁻¹ * a * nG k) * ((nG k)⁻¹ * b * nG k) by group]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [show (nG k)⁻¹ * a⁻¹ * nG k = ((nG k)⁻¹ * a * nG k)⁻¹ by group]
    exact inv_mem ha

@[expose] def conjP0 (k : ℕ) (hk : k < 2) : P0G →* P0G where
  toFun g := ⟨(nG k)⁻¹ * g * nG k, conj_mem_P0 k hk g.2⟩
  map_one' := Subtype.ext (by
    show (nG k)⁻¹ * ((1 : P0G) : GM) * nG k = 1
    rw [Subgroup.coe_one, mul_one, inv_mul_cancel])
  map_mul' a b := Subtype.ext (by
    show (nG k)⁻¹ * ((a * b : P0G) : GM) * nG k =
      (nG k)⁻¹ * (a : GM) * nG k * ((nG k)⁻¹ * (b : GM) * nG k)
    rw [Subgroup.coe_mul]
    group)

@[expose] def vmulHom (M : Fin 4 → Fin 4 → ZMod 3) :
    Multiplicative (Fin 4 → ZMod 3) →* Multiplicative (Fin 4 → ZMod 3) where
  toFun v := Multiplicative.ofAdd (vmul M (Multiplicative.toAdd v))
  map_one' := by
    rw [toAdd_one]
    show Multiplicative.ofAdd (vmul M 0) = Multiplicative.ofAdd 0
    congr 1
    funext j
    simp [vmul]
  map_mul' a b := by
    rw [toAdd_mul, ← ofAdd_add]
    congr 1
    funext j
    simp only [vmul, Pi.add_apply]
    ring

theorem val_one_three : (1 : ZMod 3).val = 1 := rfl

theorem xG_eq_nf (i : Fin 4) : xG i = threeNF zG xG 0 (Pi.single i 1) := by
  fin_cases i <;> simp [threeNF, val_one_three]

theorem threeQ_closure_top :
    Subgroup.closure ((P0G).subtype ⁻¹' (insert zG (Set.range xG))) = ⊤ :=
  Subgroup.closure_closure_coe_preimage

theorem vmul_single (M : Fin 4 → Fin 4 → ZMod 3) (i : Fin 4) :
    vmul M (Pi.single i 1) = fun j => M i j := by
  funext j
  fin_cases i <;> simp [vmul]

theorem coord_conj (k : ℕ) (hk : k < 2) (g : P0G) :
    relG.coord (conjP0 k hk g) = vmul (matN k) (relG.coord g) := by
  have h : relG.coordHom.comp (conjP0 k hk) = (vmulHom (matN k)).comp relG.coordHom := by
    apply MonoidHom.eq_of_eqOn_dense threeQ_closure_top
    rintro ⟨g, hg⟩ hgS
    simp only [Set.mem_preimage, Subgroup.coe_subtype] at hgS
    rcases hgS with rfl | ⟨i, rfl⟩
    · have h0 : relG.coord ⟨zG, ThreeQRel.x_mem⟩ = 0 :=
        (relG.coord_eq_zero_iff _).2 (mem_zpowers zG)
      have hc : conjP0 k hk ⟨zG, ThreeQRel.x_mem⟩ = ⟨zG, ThreeQRel.x_mem⟩ := by
        apply Subtype.ext
        show (nG k)⁻¹ * zG * nG k = zG
        rw [mul_assoc, zG_central, ← mul_assoc, inv_mul_cancel, one_mul]
      simp only [MonoidHom.comp_apply, hc]
      change Multiplicative.ofAdd (relG.coord _) = Multiplicative.ofAdd (vmul _ (relG.coord _))
      rw [h0]
      congr 1
      funext j
      simp [vmul]
    · have hc : conjP0 k hk ⟨xG i, ThreeQRel.v_mem i⟩ =
          ⟨threeNF zG xG (cN k i : ZMod 3) (fun j => matN k i j), ThreeQRel.nf_mem _ _⟩ := by
        apply Subtype.ext
        exact nG_mem_conj k hk i
      have hx : (⟨xG i, ThreeQRel.v_mem i⟩ : P0G) =
          ⟨threeNF zG xG 0 (Pi.single i 1), ThreeQRel.nf_mem _ _⟩ := by
        apply Subtype.ext
        exact xG_eq_nf i
      simp only [MonoidHom.comp_apply, hc]
      change Multiplicative.ofAdd (relG.coord _) = Multiplicative.ofAdd (vmul _ (relG.coord _))
      rw [hx, relG.coord_nf, relG.coord_nf, vmul_single]
  have := congrArg (fun f => Multiplicative.toAdd (f g)) h
  exact this

theorem wordN_append (w : List ℕ) (k : ℕ) : wordN (w ++ [k]) = wordN w * nG k := by
  simp [wordN]

theorem conjW_mem (w : List ℕ) (hw : ∀ k ∈ w, k < 2) {g : GM} (hg : g ∈ P0G) :
    (wordN w)⁻¹ * g * wordN w ∈ P0G := by
  induction w using List.reverseRecOn with
  | nil => simpa [wordN] using hg
  | append_singleton w k ih =>
    have hk : k < 2 := hw k (by simp)
    have ih' := ih fun j hj => hw j (List.mem_append_left _ hj)
    rw [wordN_append, mul_inv_rev, show (nG k)⁻¹ * (wordN w)⁻¹ * g * (wordN w * nG k) =
      (nG k)⁻¹ * ((wordN w)⁻¹ * g * wordN w) * nG k by group]
    exact conj_mem_P0 k hk ih'

theorem coord_conjW (w : List ℕ) (hw : ∀ k ∈ w, k < 2) {g : GM} (hg : g ∈ P0G) :
    relG.coord ⟨(wordN w)⁻¹ * g * wordN w, conjW_mem w hw hg⟩ =
      vecWord w (relG.coord ⟨g, hg⟩) := by
  induction w using List.reverseRecOn with
  | nil => simp [vecWord, wordN]
  | append_singleton w k ih =>
    have hk : k < 2 := hw k (by simp)
    have hw' : ∀ j ∈ w, j < 2 := fun j hj => hw j (List.mem_append_left _ hj)
    have ih' := ih hw'
    have e : (⟨(wordN (w ++ [k]))⁻¹ * g * wordN (w ++ [k]), conjW_mem _ hw hg⟩ : P0G) =
        conjP0 k hk ⟨(wordN w)⁻¹ * g * wordN w, conjW_mem w hw' hg⟩ := by
      apply Subtype.ext
      show (wordN (w ++ [k]))⁻¹ * g * wordN (w ++ [k]) = (nG k)⁻¹ * ((wordN w)⁻¹ * g * wordN w) *
        nG k
      rw [wordN_append]
      group
    rw [e, coord_conj, ih', vecWord, vecWord, List.foldl_append]
    rfl

@[expose] def vecWordList : List ((Fin 4 → ZMod 3) × List ℕ) := [
    (![0, 0, 0, 1], [1]), (![0, 0, 0, 2], [1, 0]),
    (![0, 0, 1, 0], [0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1]), (![0, 0, 1, 1], [0, 0, 1]),
    (![0, 0, 1, 2], [1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1]),
    (![0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1]),
    (![0, 0, 2, 1], [1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1]), (![0, 0, 2, 2], [0, 0, 1, 0]),
    (![0, 1, 0, 0], [1, 0, 1, 0, 0, 1, 0, 0, 0, 1]), (![0, 1, 0, 1], [1, 0, 1, 0, 1]),
    (![0, 1, 0, 2], [0, 1, 0, 1, 0, 1]), (![0, 1, 1, 0], [1, 0, 0, 1]),
    (![0, 1, 1, 1], [0, 0, 1, 0, 0, 0, 1]), (![0, 1, 1, 2], [0, 1]),
    (![0, 1, 2, 0], [0, 1, 0, 0, 1]), (![0, 1, 2, 1], [0, 0, 0, 1, 0]),
    (![0, 1, 2, 2], [0, 1, 0, 0, 0, 1]), (![0, 2, 0, 0], [1, 0, 0, 0, 1, 0, 0, 1, 0, 1]),
    (![0, 2, 0, 1], [1, 0, 0, 0, 1]), (![0, 2, 0, 2], [1, 0, 1, 0, 1, 0]),
    (![0, 2, 1, 0], [0, 1, 0, 0, 1, 0]), (![0, 2, 1, 1], [0, 0, 1, 0, 1, 0, 1]),
    (![0, 2, 1, 2], [0, 0, 0, 1]), (![0, 2, 2, 0], [1, 0, 0, 1, 0]), (![0, 2, 2, 1], [0, 1, 0]),
    (![0, 2, 2, 2], [0, 0, 0, 1, 0, 1, 0, 1]), (![1, 0, 0, 0], []),
    (![1, 0, 0, 1], [1, 0, 0, 1, 0, 1]), (![1, 0, 0, 2], [0, 0, 1, 0, 1]),
    (![1, 0, 1, 0], [0, 0, 1, 0, 0, 0, 1, 0, 1, 0]), (![1, 0, 1, 1], [0, 0, 1, 0, 0, 1, 0, 1]),
    (![1, 0, 1, 2], [1, 0, 0, 1, 0, 1, 0, 0, 1]), (![1, 0, 2, 0], [1, 0, 0, 0, 1, 0, 1, 0]),
    (![1, 0, 2, 1], [1, 0, 1, 0, 0, 1, 0, 1]), (![1, 0, 2, 2], [1, 0, 1]),
    (![1, 1, 0, 0], [0, 1, 0, 0, 0, 1, 0, 1]), (![1, 1, 0, 1], [0, 0, 0, 1, 0, 1, 0, 0, 0, 1]),
    (![1, 1, 0, 2], [1, 0, 1, 0, 0, 1]), (![1, 1, 1, 0], [0, 1, 0, 1, 0, 0, 0, 1, 0, 1]),
    (![1, 1, 1, 1], [0, 0, 1, 0, 0, 1, 0, 1, 0, 1]), (![1, 1, 1, 2], [0, 0, 0, 1, 0, 1, 0]),
    (![1, 1, 2, 0], [1, 0, 1, 0, 0, 0, 1, 0, 1, 0]),
    (![1, 1, 2, 1], [0, 1, 0, 0, 1, 0, 0, 0, 1]), (![1, 1, 2, 2], [0, 1, 0, 1, 0, 0, 1, 0]),
    (![1, 2, 0, 0], [1, 0, 1, 0, 1, 0, 0, 1]), (![1, 2, 0, 1], [1, 0, 0, 1, 0, 1, 0, 1]),
    (![1, 2, 0, 2], [1, 0, 1, 0, 1, 0, 0, 0, 1]),
    (![1, 2, 1, 0], [1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1]),
    (![1, 2, 1, 1], [0, 1, 0, 1, 0, 0, 0, 1]), (![1, 2, 1, 2], [0, 1, 0, 1, 0]),
    (![1, 2, 2, 0], [0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1]),
    (![1, 2, 2, 1], [0, 1, 0, 0, 1, 0, 1, 0]), (![1, 2, 2, 2], [0, 0, 1, 0, 1, 0, 0, 1]),
    (![2, 0, 0, 0], [0]), (![2, 0, 0, 1], [0, 0, 1, 0, 1, 0]),
    (![2, 0, 0, 2], [1, 0, 0, 1, 0, 1, 0]), (![2, 0, 1, 0], [1, 0, 0, 0, 1, 0, 1]),
    (![2, 0, 1, 1], [1, 0, 1, 0]), (![2, 0, 1, 2], [0, 1, 0, 1, 0, 0, 1, 0, 1]),
    (![2, 0, 2, 0], [0, 0, 1, 0, 0, 0, 1, 0, 1]),
    (![2, 0, 2, 1], [0, 1, 0, 0, 1, 0, 1, 0, 0, 1]), (![2, 0, 2, 2], [1, 0, 0, 1, 0, 0, 0, 1]),
    (![2, 1, 0, 0], [1, 0, 1, 0, 1, 0, 0, 1, 0]), (![2, 1, 0, 1], [0, 0, 0, 1, 0, 1, 0, 0, 1]),
    (![2, 1, 0, 2], [1, 0, 1, 0, 0, 0, 1]),
    (![2, 1, 1, 0], [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1]),
    (![2, 1, 1, 1], [0, 0, 1, 0, 1, 0, 0, 1, 0]), (![2, 1, 1, 2], [0, 1, 0, 0, 1, 0, 1]),
    (![2, 1, 2, 0], [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1]), (![2, 1, 2, 1], [0, 1, 0, 1]),
    (![2, 1, 2, 2], [0, 1, 0, 0, 1, 0, 1, 0, 1]), (![2, 2, 0, 0], [0, 1, 0, 0, 0, 1, 0, 1, 0]),
    (![2, 2, 0, 1], [1, 0, 1, 0, 0, 1, 0]), (![2, 2, 0, 2], [0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1]),
    (![2, 2, 1, 0], [1, 0, 1, 0, 0, 0, 1, 0, 1]), (![2, 2, 1, 1], [0, 1, 0, 1, 0, 0, 1]),
    (![2, 2, 1, 2], [0, 0, 0, 1, 0, 0, 1, 0, 1]),
    (![2, 2, 2, 0], [0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0]), (![2, 2, 2, 1], [0, 0, 0, 1, 0, 1]),
    (![2, 2, 2, 2], [0, 0, 1, 0, 1, 0, 0, 0, 1])]

@[expose] def vw (v : Fin 4 → ZMod 3) : List ℕ := (vecWordList.lookup v).getD []

theorem vecWord_spec : ∀ v : Fin 4 → ZMod 3, v ≠ 0 → vecWord (vw v) v = Pi.single 0 1 := by
  decide +kernel

theorem vw_lt : ∀ v : Fin 4 → ZMod 3, ∀ k ∈ vw v, k < 2 := by
  decide +kernel

theorem exists_conj_x0 {g : GM} (hg : g ∈ P0G) (hgz : g ∉ zpowers zG) :
    ∃ (n : GM) (c : ZMod 3), n⁻¹ * g * n = xG 0 * zG ^ c.val := by
  set v := relG.coord ⟨g, hg⟩ with hv
  have hv0 : v ≠ 0 := fun h0 => hgz ((relG.coord_eq_zero_iff _).1 h0)
  refine ⟨wordN (vw v), (relG.nfEquiv.symm ⟨_, conjW_mem _ (vw_lt v) hg⟩).1, ?_⟩
  have hc := coord_conjW (vw v) (vw_lt v) hg
  rw [← hv, vecWord_spec v hv0] at hc
  have hnf := relG.eq_nf ⟨_, conjW_mem _ (vw_lt v) hg⟩
  rw [hc] at hnf
  refine hnf.trans ?_
  simp [threeNF, val_one_three]

end CFSG.RankThree.Native.ONTriple
