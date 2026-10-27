module

public import CFSG.Sporadic.J4.QTProof
public import CFSG.Sporadic.J4.QTOutLinGen
public import CFSG.Sporadic.J4.QT2ACheck

public section

namespace CFSG.Sporadic.J4.QT2A

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix

@[expose] noncomputable def gen5 (k : ℕ) : J :=
  if k < 3 then xJ k else if k = 3 then a else if k = 4 then b else 1

@[expose] noncomputable def el5 (w : List ℤ) : J := wordProd gen5 w

theorem wordProd_map {G H : Type*} [Group G] [Group H] (f : G →* H) (gs : ℕ → G) (w : List ℤ) :
    f (wordProd gs w) = wordProd (fun m => f (gs m)) w := by
  unfold wordProd
  induction w with
  | nil => simp
  | cons l w ih =>
    simp only [List.map_cons, List.prod_cons, map_mul]
    rw [ih]
    congr 1
    split_ifs <;> simp

theorem wordProd_append {G : Type*} [Group G] (gs : ℕ → G) (w w' : List ℤ) :
    wordProd gs (w ++ w') = wordProd gs w * wordProd gs w' := by
  unfold wordProd
  rw [List.map_append, List.prod_append]

theorem wordProd_invWord {G : Type*} [Group G] (gs : ℕ → G) :
    ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0) → wordProd gs (invWord w) = (wordProd gs w)⁻¹
  | [], _ => by simp [invWord, wordProd]
  | l :: w, h => by
    have hl : l ≠ 0 := h l (List.mem_cons_self ..)
    have ih := wordProd_invWord gs w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    have e : invWord (l :: w) = invWord w ++ [-l] := by
      simp [invWord, List.map_append]
    rw [e, wordProd_append, ih]
    have h1 : wordProd gs [-l] = (wordProd gs [l])⁻¹ := by
      unfold wordProd
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rcases lt_or_gt_of_ne hl with h1 | h1
      · have h2 : ¬ 0 < l := by omega
        have h3 : 0 < -l := by omega
        rw [ite_eq_left h3, ite_eq_right h2, inv_inv]
      · have h2 : 0 < l := h1
        have h3 : ¬ 0 < -l := by omega
        rw [ite_eq_right h3, ite_eq_left h2, neg_neg]
    rw [h1, show l :: w = [l] ++ w from rfl, wordProd_append, _root_.mul_inv_rev]

section Mat

variable (hM : MatFacts)
include hM

theorem g5Mats_spec (m : ℕ) :
    rowsMatrix ((g5Mats ())[m]?.getD idRows) =
      (((gen5 m : J) : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) := by
  have hl : (locMats ()).size = 3 := hM.locSize
  have hb : baseMats.size = 2 := rfl
  unfold g5Mats
  by_cases h3 : m < 3
  · rw [Array.getElem?_append_left (by omega), locMats_spec hM m, gen5, ite_eq_left h3]
    rfl
  · by_cases h4 : m = 3
    · subst h4
      rw [Array.getElem?_append_right (by omega), show 3 - (locMats ()).size = 0 by omega,
        baseMats_spec hM 0, gen5, ite_eq_right h3, ite_eq_left rfl]
      simp only [baseGL, ite_true, a_coe]
    · by_cases h5 : m = 4
      · subst h5
        rw [Array.getElem?_append_right (by omega), show 4 - (locMats ()).size = 1 by omega,
          baseMats_spec hM 1, gen5, ite_eq_right h3, ite_eq_right h4, ite_eq_left rfl]
        simp only [baseGL, b_coe]
        simp
      · have hn : (locMats () ++ baseMats)[m]? = none := by
          rw [Array.getElem?_eq_none]
          simp only [Array.size_append, hl, hb]
          omega
        rw [hn, Option.getD_none, rowsMatrix_idRows, gen5, ite_eq_right h3, ite_eq_right h4,
          ite_eq_right h5]
        simp

theorem g5Invs_spec (m : ℕ) :
    rowsMatrix ((g5Invs ())[m]?.getD idRows) =
      ((((gen5 m : J) : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2)) :
        Matrix (Fin 112) (Fin 112) (ZMod 2)) := by
  have hl : (locInvs ()).size = 3 := by
    have := hM.locSize
    simpa [locInvs] using this
  have hb : baseInvs.size = 2 := by simp [baseInvs, baseMats]
  unfold g5Invs
  by_cases h3 : m < 3
  · rw [Array.getElem?_append_left (by omega), locInvs_spec hM m, gen5, ite_eq_left h3]
    rfl
  · by_cases h4 : m = 3
    · subst h4
      rw [Array.getElem?_append_right (by omega), show 3 - (locInvs ()).size = 0 by omega,
        baseInvs_spec hM 0, gen5, ite_eq_right h3, ite_eq_left rfl]
      simp only [baseGL, ite_true, a_coe]
    · by_cases h5 : m = 4
      · subst h5
        rw [Array.getElem?_append_right (by omega), show 4 - (locInvs ()).size = 1 by omega,
          baseInvs_spec hM 1, gen5, ite_eq_right h3, ite_eq_right h4, ite_eq_left rfl]
        simp only [baseGL, b_coe]
        simp
      · have hn : (locInvs () ++ baseInvs)[m]? = none := by
          rw [Array.getElem?_eq_none]
          simp only [Array.size_append, hl, hb]
          omega
        rw [hn, Option.getD_none, rowsMatrix_idRows, gen5, ite_eq_right h3, ite_eq_right h4,
          ite_eq_right h5]
        simp

theorem Mx_el5 (w : List ℤ) : Mx (el5 w) = rowsMatrix (wR w) := by
  have h := rowsMatrix_wordRows (mats := g5Mats ()) (invs := g5Invs ())
    (gs := fun m => ((gen5 m : J) : GL (Fin 112) (ZMod 2))) (g5Mats_spec hM) (g5Invs_spec hM) w
  rw [wR, h]
  have := wordProd_map (J.subtype) gen5 w
  have h2 := congrArg
    (fun x => ((x : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2))) this
  simpa [Mx, el5] using h2

end Mat

abbrev V112 : Type := Fin 112 → ZMod 2

@[expose] noncomputable def zJ : J := eta uJ 11 1131

noncomputable abbrev Cz : Subgroup J := Subgroup.centralizer ({zJ} : Set J)

@[expose] noncomputable def phiM : Matrix (Fin 112) (Fin 112) (ZMod 2) := Mx zJ - 1

@[expose] noncomputable def Kz : Submodule (ZMod 2) V112 :=
  LinearMap.ker (Matrix.vecMulLinear phiM)

@[expose] noncomputable def Wz : Submodule (ZMod 2) V112 :=
  LinearMap.range (Matrix.vecMulLinear phiM)

theorem mem_Kz {v : V112} : v ∈ Kz ↔ v ᵥ* phiM = 0 := by
  simp [Kz, LinearMap.mem_ker]

theorem mem_Wz {x : V112} : x ∈ Wz ↔ ∃ u : V112, u ᵥ* phiM = x := by
  simp [Wz, LinearMap.mem_range]

theorem mem_Cz {g : J} : g ∈ Cz ↔ zJ * g = g * zJ := by
  rw [Subgroup.mem_centralizer_iff]
  simp

theorem comm_phi {g : J} (hg : g ∈ Cz) : Mx g * phiM = phiM * Mx g := by
  have h := congrArg Mx (mem_Cz.1 hg)
  rw [map_mul, map_mul] at h
  unfold phiM
  rw [mul_sub, sub_mul, mul_one, one_mul, ← h]

theorem vecMul_mem_Wz {g : J} (hg : g ∈ Cz) {x : V112} (hx : x ∈ Wz) : x ᵥ* Mx g ∈ Wz := by
  obtain ⟨u, rfl⟩ := mem_Wz.1 hx
  refine mem_Wz.2 ⟨u ᵥ* Mx g, ?_⟩
  rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, comm_phi hg]

theorem vecMul_mem_Kz {g : J} (hg : g ∈ Cz) {v : V112} (hv : v ∈ Kz) : v ᵥ* Mx g ∈ Kz := by
  rw [mem_Kz] at hv ⊢
  rw [Matrix.vecMul_vecMul, comm_phi hg, ← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]

@[expose] noncomputable def Qz : Subgroup J where
  carrier := {g | g ∈ Cz ∧ ∀ v ∈ Kz, v ᵥ* (Mx g - 1) ∈ Wz}
  one_mem' := ⟨Subgroup.one_mem _, fun v _ => by simp [Wz.zero_mem]⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨Subgroup.mul_mem _ hg hh, fun v hv => ?_⟩
    have e : v ᵥ* (Mx (g * h) - 1) = (v ᵥ* (Mx g - 1)) ᵥ* Mx h + v ᵥ* (Mx h - 1) := by
      simp only [map_mul, Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.sub_vecMul,
        Matrix.vecMul_vecMul]
      abel
    rw [e]
    exact Wz.add_mem (vecMul_mem_Wz hh (hg' v hv)) (hh' v hv)
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨Subgroup.inv_mem _ hg, fun v hv => ?_⟩
    have hmul : Mx g * Mx g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have e : v ᵥ* (Mx g⁻¹ - 1) = -((v ᵥ* (Mx g - 1)) ᵥ* Mx g⁻¹) := by
      simp only [Matrix.vecMul_sub, Matrix.sub_vecMul, Matrix.vecMul_one, Matrix.vecMul_vecMul,
        hmul]
      abel
    rw [e]
    exact Wz.neg_mem (vecMul_mem_Wz (Subgroup.inv_mem _ hg) (hg' v hv))

theorem mem_Qz {g : J} : g ∈ Qz ↔ g ∈ Cz ∧ ∀ v ∈ Kz, v ᵥ* (Mx g - 1) ∈ Wz := Iff.rfl

theorem Qz_le_Cz : Qz ≤ Cz := fun _ hg => hg.1

theorem Qz_conj {c : J} (hc : c ∈ Cz) {q : J} (hq : q ∈ Qz) : c * q * c⁻¹ ∈ Qz := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hc (Qz_le_Cz hq)) (Subgroup.inv_mem _ hc),
    fun v hv => ?_⟩
  have hmul : Mx c * Mx c⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have e : v ᵥ* (Mx (c * q * c⁻¹) - 1) = ((v ᵥ* Mx c) ᵥ* (Mx q - 1)) ᵥ* Mx c⁻¹ := by
    simp only [map_mul, Matrix.vecMul_sub, Matrix.sub_vecMul, Matrix.vecMul_one,
      Matrix.vecMul_vecMul]
    rw [hmul, Matrix.vecMul_one]
  rw [e]
  exact vecMul_mem_Wz (Subgroup.inv_mem _ hc) (hq.2 _ (vecMul_mem_Kz hc hv))

theorem getD_ofFn {n : ℕ} (f : Fin n → V2) (i : Fin n) :
    (Array.ofFn f)[i.val]?.getD V2.zero = f i := by
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]

theorem rowsMatrix_addRows (X Y : Array V2) :
    rowsMatrix (addRows X Y) = rowsMatrix X + rowsMatrix Y := by
  ext i j
  rw [rowsMatrix_apply, addRows, getD_ofFn, Matrix.add_apply, rowsMatrix_apply, rowsMatrix_apply,
    V2.toVec_xor]
  rfl

theorem vecMul_cancel {P Pi : Matrix (Fin 112) (Fin 112) (ZMod 2)} (hP : P * Pi = 1)
    {A x : V112} (h : A ᵥ* P = x ᵥ* P) : A = x := by
  have h3 := congrArg (fun w => w ᵥ* Pi) h
  simp only [Matrix.vecMul_vecMul, hP, Matrix.vecMul_one] at h3
  exact h3

theorem exists_pre_of_support {pat : Matrix (Fin 112) (Fin 112) (ZMod 2)}
    (hpat' : ∀ i j : Fin 112, pat i j = if 62 ≤ i.val ∧ j.val = i.val - 62 then 1 else 0)
    (y : V112) (hy : ∀ j : Fin 112, 50 ≤ j.val → y j = 0) : ∃ c : V112, c ᵥ* pat = y := by
  let c' : V112 := fun i => if h62 : 62 ≤ i.val then y ⟨i.val - 62, by omega⟩ else 0
  refine ⟨c', ?_⟩
  funext j
  by_cases hj : j.val < 50
  · simp only [Matrix.vecMul, dotProduct, hpat']
    rw [Finset.sum_eq_single (⟨j.val + 62, by omega⟩ : Fin 112)]
    · have h62 : 62 ≤ j.val + 62 := by omega
      have e : (⟨j.val + 62 - 62, by omega⟩ : Fin 112) = j := Fin.ext (by simp)
      simp only [c', h62, dite_true, e]
      simp
    · intro i _ hne
      by_cases h62 : 62 ≤ i.val
      · have : ¬ (62 ≤ i.val ∧ j.val = i.val - 62) := by
          intro hh
          apply hne
          apply Fin.ext
          simp only
          omega
        simp [this]
      · have : ¬ (62 ≤ i.val ∧ j.val = i.val - 62) := fun hh => h62 hh.1
        simp [this]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · rw [hy j (by omega)]
    simp only [Matrix.vecMul, dotProduct, hpat']
    apply Finset.sum_eq_zero
    intro i _
    have : ¬ (62 ≤ i.val ∧ j.val = i.val - 62) := by
      intro hh
      have := i.isLt
      omega
    simp [this]

theorem mem_range_iff_of_cert {Φ P Pi B Bi pat : Matrix (Fin 112) (Fin 112) (ZMod 2)}
    (hP : P * Pi = 1) (hBi : Bi * B = 1) (hpat : B * (Φ * P) = pat)
    (hpat' : ∀ i j : Fin 112, pat i j = if 62 ≤ i.val ∧ j.val = i.val - 62 then 1 else 0)
    (x : V112) :
    (∃ u : V112, u ᵥ* Φ = x) ↔ ∀ j : Fin 112, 50 ≤ j.val → (x ᵥ* P) j = 0 := by
  constructor
  · rintro ⟨u, rfl⟩ j hj
    have h1 : Φ * P = Bi * pat := by
      rw [← hpat, ← Matrix.mul_assoc, hBi, Matrix.one_mul]
    rw [Matrix.vecMul_vecMul, h1, ← Matrix.vecMul_vecMul]
    simp only [Matrix.vecMul, dotProduct, hpat']
    apply Finset.sum_eq_zero
    intro i _
    have : ¬ (62 ≤ i.val ∧ j.val = i.val - 62) := by
      intro h
      have := i.isLt
      omega
    simp [this]
  · intro h
    obtain ⟨c', hc'⟩ := exists_pre_of_support hpat' (x ᵥ* P) h
    refine ⟨c' ᵥ* B, ?_⟩
    have h2 : ((c' ᵥ* B) ᵥ* Φ) ᵥ* P = x ᵥ* P := by
      rw [← hc', ← hpat]
      simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc]
    exact vecMul_cancel hP h2

theorem matrix_add_one_eq_sub_one (M : Matrix (Fin 112) (Fin 112) (ZMod 2)) : M + 1 = M - 1 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply]
  exact (CharTwo.sub_eq_add _ _).symm

theorem idRows_toVec (k : ℕ) (hk : k < 112) (j : Fin 112) :
    (idRows[k]!).toVec j = if k = j.val then 1 else 0 := by
  have hs : k < idRows.size := by rw [idRows_size]; exact hk
  have h1 : idRows[k]! = idRows[k]'hs := getElem!_pos idRows k hs
  have h2 := rowsMatrix_apply idRows ⟨k, hk⟩ j
  rw [Array.getElem?_eq_getElem hs, Option.getD_some, rowsMatrix_idRows, Matrix.one_apply] at h2
  rw [h1, ← h2]
  simp [Fin.ext_iff]

theorem patRows_apply (i j : Fin 112) :
    rowsMatrix patRows i j = if 62 ≤ i.val ∧ j.val = i.val - 62 then 1 else 0 := by
  rw [rowsMatrix_apply, patRows, getD_ofFn]
  by_cases h : 62 ≤ i.val
  · have hk : i.val - 62 < 112 := by have := i.isLt; omega
    rw [ite_eq_left h, idRows_toVec _ hk]
    by_cases h2 : j.val = i.val - 62
    · simp [h, h2]
    · have : ¬ (i.val - 62 = j.val) := fun e => h2 e.symm
      simp [h, h2, this]
  · rw [ite_eq_right h, V2.toVec_zero]
    simp [h]

theorem getBang_toVec (X : Array V2) (hX : X.size = 112) (k j : Fin 112) :
    (X[k.val]!).toVec j = rowsMatrix X k j := by
  have hs : k.val < X.size := by rw [hX]; exact k.isLt
  rw [rowsMatrix_apply, Array.getElem?_eq_getElem hs, Option.getD_some]
  rw [getElem!_pos X k.val hs]

theorem phiR_size : (phiR ()).size = 112 := by
  simp [phiR, addRows]

theorem kIdx_facts : kIdx.size = 50 ∧ ∀ i < 50, kIdx[i]! < 112 := by
  have h := chkMod_true
  unfold chkMod at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hs, -⟩, hall⟩, -⟩, -⟩, -⟩, -⟩ := h
  have hs' : kIdx.size = 50 := beq_iff_eq.1 hs
  refine ⟨hs', fun i hi => ?_⟩
  have := Array.all_eq_true.1 hall i (by omega)
  rw [getElem!_pos kIdx i (by omega)]
  exact of_decide_eq_true this

theorem compV_size : compV.size = 12 := by
  have h := chkMod_true
  unfold chkMod at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, hs⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact beq_iff_eq.1 hs

theorem Bm_row_mid {i : Fin 112} (h1 : 50 ≤ i.val) (h2 : i.val < 62) (j : Fin 112) :
    rowsMatrix (bRows ()) i j = (compV[i.val - 50]!).toVec j := by
  rw [rowsMatrix_apply, bRows, getD_ofFn, ite_eq_right (by omega), ite_eq_left h2]

theorem row_mem_Wz (k : Fin 112) : phiM k ∈ Wz := by
  refine mem_Wz.2 ⟨Pi.single k 1, ?_⟩
  funext j
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

theorem inWB_iff (x : V2) :
    inWB x = true ↔ ∀ j : Fin 112, 50 ≤ j.val → (x.toVec ᵥ* rowsMatrix pRows) j = 0 := by
  have hy : ∀ j : Fin 112,
      (x.toVec ᵥ* rowsMatrix pRows) j = (frApply (frTable pRows) x).toVec j := by
    intro j
    rw [← frApply_toVec_eq_vecMul]
  unfold inWB
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true']
  constructor
  · intro h j hj
    rw [hy, V2.toVec_apply]
    have := h (j.val - 50) (by have := j.isLt; omega)
    rw [show 50 + (j.val - 50) = j.val by omega] at this
    simp [this]
  · intro h t ht
    have := h ⟨50 + t, by omega⟩ (by simp)
    rw [hy, V2.toVec_apply] at this
    by_contra hne
    have hb : (frApply (frTable pRows) x).testBit (50 + t) = true := by simpa using hne
    simp [hb] at this

section Cert

variable (hM : MatFacts)
include hM

theorem Mx_zJ : Mx zJ = rowsMatrix (zR ()) := Mx_eta hM 11 le_rfl 1131

theorem phiR_matrix : rowsMatrix (phiR ()) = phiM := by
  have h1 : rowsMatrix (phiR ()) = rowsMatrix (zR ()) + 1 := by
    show rowsMatrix (addRows (zR ()) idRows) = _
    rw [rowsMatrix_addRows, rowsMatrix_idRows]
  rw [h1, ← Mx_zJ hM, phiM, matrix_add_one_eq_sub_one]

theorem mod_matrix_facts :
    rowsMatrix (invRows (bRows ())) * rowsMatrix (bRows ()) = 1 ∧
    rowsMatrix (bRows ()) * (phiM * rowsMatrix pRows) = rowsMatrix patRows ∧
    rowsMatrix pRows * rowsMatrix (invRows pRows) = 1 := by
  have h := chkMod_true
  unfold chkMod at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h1⟩, h2⟩, h3⟩, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg rowsMatrix (eqRows_iff.1 h1)
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  · have := congrArg rowsMatrix (eqRows_iff.1 h2)
    rwa [rowsMatrix_mulRows, rowsMatrix_mulRows, phiR_matrix hM] at this
  · have := congrArg rowsMatrix (eqRows_iff.1 h3)
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this

theorem Bm_row_lt50 {i : Fin 112} (hi : i.val < 50) :
    ∃ k : Fin 112, ∀ j, rowsMatrix (bRows ()) i j = phiM k j := by
  have hk := (kIdx_facts.2 i.val hi)
  refine ⟨⟨kIdx[i.val]!, hk⟩, fun j => ?_⟩
  rw [rowsMatrix_apply, bRows, getD_ofFn, ite_eq_left hi]
  have := getBang_toVec (phiR ()) phiR_size ⟨kIdx[i.val]!, hk⟩ j
  rw [this, phiR_matrix hM]

end Cert

theorem row_mul_eq (B M : Matrix (Fin 112) (Fin 112) (ZMod 2)) (i : Fin 112) :
    (B * M) i = (fun k => B i k) ᵥ* M := by
  funext j
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

theorem vec_sub_eq_add (a b : V112) : a - b = a + b := by
  funext j
  simp [CharTwo.sub_eq_add]

section Cert2

variable (hM : MatFacts)
include hM

theorem Kz_span {v : V112} (hv : v ∈ Kz) :
    ∃ c : V112, v = c ᵥ* rowsMatrix (bRows ()) ∧ ∀ i : Fin 112, 62 ≤ i.val → c i = 0 := by
  obtain ⟨hBi, hBP, hPPi⟩ := mod_matrix_facts hM
  refine kernel_span (B := rowsMatrix (bRows ())) (Binv := rowsMatrix (invRows (bRows ())))
    (Φ := phiM * rowsMatrix pRows) (s := 62) hBi ?_ v ?_
  · intro i j
    rw [hBP, patRows_apply]
  · rw [← Matrix.vecMul_vecMul, mem_Kz.1 hv, Matrix.zero_vecMul]

theorem mem_Wz_iff (x : V112) :
    x ∈ Wz ↔ ∀ j : Fin 112, 50 ≤ j.val → (x ᵥ* rowsMatrix pRows) j = 0 := by
  obtain ⟨hBi, hBP, hPPi⟩ := mod_matrix_facts hM
  rw [mem_Wz]
  exact mem_range_iff_of_cert hPPi hBi hBP patRows_apply x

theorem toVec_mem_Wz_iff (x : V2) : x.toVec ∈ Wz ↔ inWB x = true := by
  rw [mem_Wz_iff hM, inWB_iff]

theorem Bm_row_mem_Kz {i : Fin 112} (hi : i.val < 62) :
    (fun j => rowsMatrix (bRows ()) i j) ∈ Kz := by
  obtain ⟨hBi, hBP, hPPi⟩ := mod_matrix_facts hM
  rw [mem_Kz]
  have h1 : (fun j => rowsMatrix (bRows ()) i j) ᵥ* (phiM * rowsMatrix pRows) = 0 := by
    rw [← row_mul_eq, hBP]
    funext j
    rw [patRows_apply]
    simp [show ¬ 62 ≤ i.val from by omega]
  rw [← Matrix.vecMul_vecMul] at h1
  exact vecMul_cancel hPPi (by rw [h1, Matrix.zero_vecMul])

noncomputable def compVec (j : ℕ) : V112 := (compV[j]!).toVec

theorem compVec_mem_Kz {j : ℕ} (hj : j < 12) : compVec j ∈ Kz := by
  have hi : 50 + j < 112 := by omega
  have h := Bm_row_mem_Kz hM (i := ⟨50 + j, hi⟩) (by simp; omega)
  have e : (fun k => rowsMatrix (bRows ()) ⟨50 + j, hi⟩ k) = compVec j := by
    funext k
    rw [Bm_row_mid (i := ⟨50 + j, hi⟩) (by simp) (by simp; omega) k]
    simp [compVec]
  rwa [e] at h

theorem mem_Qz_of_inQz {g : J} {R : Array V2} (hR : Mx g = rowsMatrix R) (h : inQz R = true) :
    g ∈ Qz := by
  unfold inQz at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hc, ht⟩ := h
  have hgz : g ∈ Cz := by
    unfold cmz at hc
    have h1 := congrArg rowsMatrix (eqRows_iff.1 hc)
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← hR, ← Mx_zJ hM, ← map_mul, ← map_mul] at h1
    exact mem_Cz.2 (Mx_injective h1).symm
  refine ⟨hgz, fun v hv => ?_⟩
  obtain ⟨c, hvc, hc62⟩ := Kz_span hM hv
  have hcomm : phiM * (Mx g - 1) = (Mx g - 1) * phiM := by
    have := comm_phi hgz
    rw [mul_sub, sub_mul, mul_one, one_mul, this]
  have hcomp : ∀ j : ℕ, j < 12 → compVec j ᵥ* (Mx g - 1) ∈ Wz := by
    intro j hj
    unfold trivOnComp at ht
    have h1 := List.all_eq_true.1 ht j (List.mem_range.2 hj)
    have h2 := (toVec_mem_Wz_iff hM _).2 h1
    rw [V2.toVec_xor, frApply_toVec_eq_vecMul, ← hR] at h2
    have e : compVec j ᵥ* (Mx g - 1) = (compV[j]!).toVec ᵥ* Mx g + (compV[j]!).toVec := by
      rw [Matrix.vecMul_sub, Matrix.vecMul_one, vec_sub_eq_add]
      rfl
    rw [e]
    exact h2
  have hrow : ∀ i : Fin 112, i.val < 62 →
      ((fun k => rowsMatrix (bRows ()) i k) ᵥ* (Mx g - 1)) ∈ Wz := by
    intro i hi
    by_cases hi50 : i.val < 50
    · obtain ⟨k, hk⟩ := Bm_row_lt50 hM hi50
      have e : (fun j => rowsMatrix (bRows ()) i j) = phiM k := funext hk
      rw [e]
      have e2 : phiM k = Pi.single k 1 ᵥ* phiM := (Matrix.single_one_vecMul k phiM).symm
      rw [e2, Matrix.vecMul_vecMul, hcomm, ← Matrix.vecMul_vecMul]
      exact mem_Wz.2 ⟨_, rfl⟩
    · have e : (fun j => rowsMatrix (bRows ()) i j) = compVec (i.val - 50) := by
        funext j
        rw [Bm_row_mid (by omega) hi j]
        rfl
      rw [e]
      exact hcomp _ (by omega)
  rw [hvc, Matrix.vecMul_vecMul, Matrix.vecMul_eq_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i.val < 62
  · rw [row_mul_eq]
    exact Submodule.smul_mem _ _ (hrow i hi)
  · rw [hc62 i (by omega), zero_smul]
    exact Wz.zero_mem

theorem not_mem_Qz_of_notQz {g : J} {R : Array V2} (hR : Mx g = rowsMatrix R)
    (h : notQz R = true) : g ∉ Qz := by
  intro hg
  unfold notQz at h
  have h1 : trivOnComp R = false := by simpa using h
  unfold trivOnComp at h1
  rw [List.all_eq_false] at h1
  obtain ⟨j, hj, hfalse⟩ := h1
  have hj12 := List.mem_range.1 hj
  have hK := compVec_mem_Kz hM hj12
  have h2 := hg.2 _ hK
  have e : compVec j ᵥ* (Mx g - 1) = (compV[j]!).toVec ᵥ* Mx g + (compV[j]!).toVec := by
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, vec_sub_eq_add]
    rfl
  rw [e] at h2
  have h3 : ((frApply (frTable R) compV[j]!).xor compV[j]!).toVec ∈ Wz := by
    rw [V2.toVec_xor, frApply_toVec_eq_vecMul, ← hR]
    exact h2
  exact hfalse ((toVec_mem_Wz_iff hM _).1 h3)

end Cert2

end CFSG.Sporadic.J4.QT2A
