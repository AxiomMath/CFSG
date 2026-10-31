
module

public import CFSG.Sporadic.Co1.Module.OddChecksInputs
public import Certificates.Data.Kernel.Co1M.Odd73
public import Certificates.Data.Kernel.Co1Odd71Data

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative Matrix CFSG.KC.Odd73 CFSG.KC.Co1F2 CFSG.KD.Co1Odd

attribute [local instance] vecAct vecSMul

attribute [local irreducible] rr regsRows

theorem reg_mul
    {i j k : ℕ} (h : rr k = mulRows 24 (rr i) (rr j)) : reg k = reg i * reg j := by
  apply mat_injective
  rw [map_mul, mat_reg, mat_reg, mat_reg, h, rowsMatrix_mulRows]

theorem reg_comm
    {i j : ℕ} (h : mulRows 24 (rr i) (rr j) = mulRows 24 (rr j) (rr i)) :
    reg i * reg j = reg j * reg i := by
  apply mat_injective
  rw [map_mul, map_mul, mat_reg, mat_reg, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, h]

theorem reg_mul_eq_one
    {i j : ℕ} (h : mulRows 24 (rr i) (rr j) = idRows 24) :
    reg i * reg j = 1 := by
  apply mat_injective
  rw [map_mul, mat_reg, mat_reg, ← rowsMatrix_mulRows, h, rowsMatrix_idRows, map_one]

theorem reg_inv
    {i j : ℕ} (h : mulRows 24 (rr i) (rr j) = idRows 24) : (reg i)⁻¹ = reg j :=
  inv_eq_of_mul_eq_one_right (reg_mul_eq_one h)

theorem mat_reg_inv
    {i j : ℕ} (h : mulRows 24 (rr i) (rr j) = idRows 24) :
    mat (reg i)⁻¹ = rowsMatrix 24 (rr j) := by
  rw [reg_inv h, mat_reg]

noncomputable def omega0 : Vec24 := toVecD 24 code4

theorem reg_fix
    {i : ℕ} (h : isFixedN (Mt i) code4 = true) : reg i • omega0 = omega0 := by
  rw [smul_eq_co1Act, omega0, co1Act_eq_mulVec, mat_reg]
  exact (isFixedN_iff (rr i) (by norm_num [code4])).1 h

noncomputable def n1 : NativeSporadic.Co1 := reg 23

noncomputable def n2 : NativeSporadic.Co1 := reg 17

noncomputable def rho3 : NativeSporadic.Co1 := reg 27

noncomputable def t1 : NativeSporadic.Co1 := reg 86

noncomputable def sRep
    (k : Fin 3) : NativeSporadic.Co1 := reg (sIdx[(k : ℕ)]!)

noncomputable abbrev Hst : Subgroup NativeSporadic.Co1 :=
  MulAction.stabilizer NativeSporadic.Co1 omega0

theorem eq_of_mul_eq_one_of_inv_eq {a b : NativeSporadic.Co1} (h : a * b = 1) (ha : a⁻¹ = a) :
    b = a := by
  have h' : a⁻¹ = b := inv_eq_of_mul_eq_one_right h
  rw [ha] at h'
  exact h'.symm

theorem forestOK_valid {P Q roots : Array (Array ℕ)} {F : Forest}
    (h : forestOK P Q roots F = true) : ∀ i < F.pts.size, validRows F.pts[i]! = true := by
  unfold forestOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hall⟩, -⟩ := h
  intro i hi
  have hp := hall i hi
  simp only [forestPointOK, Bool.and_eq_true] at hp
  exact hp.1

theorem forest_conj_sound {P Q roots : Array (Array ℕ)} {F : Forest}
    (h : forestOK P Q roots F = true) (gens : ℕ → NativeSporadic.Co1)
    (hg : ∀ l < P.size, mat (gens l) = rowsMatrix 24 P[l]!)
    (hgi : ∀ l < Q.size, mat (gens l)⁻¹ = rowsMatrix 24 Q[l]!)
    (K : Subgroup NativeSporadic.Co1) (hK : ∀ l < P.size, gens l ∈ K)
    (rr' : ℕ → NativeSporadic.Co1) (hr : ∀ j < roots.size, mat (rr' j) = rowsMatrix 24 roots[j]!) :
    ∃ f : ℕ → NativeSporadic.Co1,
      (∀ i < F.pts.size, F.rt[i]! < roots.size ∧ (∃ n ∈ K, f i = n * rr' F.rt[i]! * n⁻¹) ∧
        mat (f i) = rowsMatrix 24 F.pts[i]!) ∧
      ∀ i < F.pts.size, ∀ j < F.pts.size, f i = f j → i = j := by
  obtain ⟨f, hf, hinj⟩ := forestOK_sound h gens (fun l => (gens l)⁻¹) hg hgi rr' hr
    (fun j x => ∃ n ∈ K, x = n * rr' j * n⁻¹) (fun j _ => ⟨1, K.one_mem, by simp⟩)
    (fun l hl _ j x ⟨n, hn, hx⟩ => ⟨gens l * n, K.mul_mem (hK l hl) hn, by rw [hx]; group⟩)
  exact ⟨f, fun i hi => ⟨(hf i hi).1, (hf i hi).2.1, (hf i hi).2.2⟩, hinj⟩

theorem forest_mul_sound {P Q roots : Array (Array ℕ)} {F : Forest}
    (h : forestOK P Q roots F = true) (hP : ∀ l < P.size, P[l]! = idRows 24)
    (hroots : roots = #[idRows 24]) (zs : ℕ → NativeSporadic.Co1)
    (hz : ∀ l < Q.size, mat (zs l) = rowsMatrix 24 Q[l]!)
    (K : Subgroup NativeSporadic.Co1) (hK : ∀ l < Q.size, zs l ∈ K) :
    ∃ f : ℕ → NativeSporadic.Co1,
      (∀ i < F.pts.size, f i ∈ K ∧ mat (f i) = rowsMatrix 24 F.pts[i]!) ∧
      ∀ i < F.pts.size, ∀ j < F.pts.size, f i = f j → i = j := by
  obtain ⟨f, hf, hinj⟩ := forestOK_sound h (fun _ => 1) zs
    (fun l hl => by rw [hP l hl, rowsMatrix_idRows, map_one]) hz (fun _ => 1)
    (fun j hj => by
      subst hroots
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      simp [rowsMatrix_idRows])
    (fun _ x => x ∈ K) (fun j _ => K.one_mem)
    (fun l _ hl j x hx => by simpa using K.mul_mem hx (hK l hl))
  exact ⟨f, fun i hi => ⟨(hf i hi).2.1, (hf i hi).2.2⟩, hinj⟩

theorem oddCount_eq (ords : Array ℕ) :
    oddCount ords = {i | i < ords.size ∧ ords[i]! % 2 = 1 ∧ ords[i]! ≠ 1}.ncard := by
  unfold oddCount
  rw [countBelow_eq, zero_add, ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq]

theorem zeroCount_eq (ords : Array ℕ) :
    zeroCount ords = {i | i < ords.size ∧ ords[i]! = 0}.ncard := by
  unfold zeroCount
  rw [countBelow_eq, zero_add, ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, beq_iff_eq]

theorem rtCount_eq (F : Forest) (j : ℕ) :
    rtCount F j = {i | i < F.rt.size ∧ F.rt[i]! = j}.ncard := by
  unfold rtCount
  rw [countBelow_eq, zero_add, ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, beq_iff_eq]

theorem ordersWith_get (rho : Array ℕ) (F : Forest) {i : ℕ} (hi : i < F.pts.size) :
    (ordersWith rho F)[i]! = orderN (mulRows 24 rho F.pts[i]!) := by
  have h1 : i < (ordersWith rho F).size := by simpa [ordersWith] using hi
  rw [getElem!_pos (ordersWith rho F) i h1]
  simp only [ordersWith, Array.getElem_map]
  rw [getElem!_pos F.pts i hi]

theorem forestOK_sizes {P Q roots : Array (Array ℕ)} {F : Forest}
    (h : forestOK P Q roots F = true) : F.rt.size = F.pts.size := by
  unfold forestOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hrt⟩, -⟩, -⟩ := h
  exact hrt

theorem forestZOK_facts {k n : ℕ} (h : forestZOK k n = true) :
    forestOK (PZ k) (QZ k) rootsZ (FZ k) = true ∧ (FZ k).pts.size = n := by
  simp only [forestZOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem pairFixOK_facts {k fx f4 : ℕ} (h : pairFixOK k fx f4 = true) :
    fixCount [Mt 27, Mt (sIdx[k]!)] = fx ∧
    fixCount4 [Mt 27, Mt (sIdx[k]!)] (transposeRows 24 qRows) (orbitOf 2 98280).pts
      (posTable 24 (orbitOf 2 98280).pts) 98280 = f4 := by
  simp only [pairFixOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem faithGramOK_facts {k : ℕ} (h : faithGramOK k = true) :
    faithfulOK (FZ k).pts (Wk k) = true ∧ gramOK (transposeRows 24 f0Rows) (Wk k) = true := by
  simp only [faithGramOK, Bool.and_eq_true] at h
  exact h

theorem smul_reg_iff (i : ℕ) (v : Vec24) :
    reg i • v = v ↔ rowsMatrix 24 (rr i) *ᵥ v = v := by
  rw [smul_eq_co1Act, co1Act_eq_mulVec, mat_reg]

theorem reg_mem_centralizer {i : ℕ}
    (h : mulRows 24 (rr i) (rr 27) = mulRows 24 (rr 27) (rr i)) :
    reg i ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact reg_comm h

theorem fixed_set_eq (is : List ℕ) :
    {v : Vec24 | ∀ M ∈ is.map rr, rowsMatrix 24 M *ᵥ v = v} = {v | ∀ i ∈ is, reg i • v = v} := by
  ext v
  simp only [Set.mem_ofPred_eq, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  exact forall₂_congr fun i _ => (smul_reg_iff i v).symm

theorem map_toArray_get (L : List ℕ) {l : ℕ} (hl : l < L.length) :
    (L.map rr).toArray[l]! = rr (L[l]!) := by
  rw [getElem!_pos (L.map rr).toArray l (by simpa using hl), getElem!_pos L l hl]
  simp

theorem PS_get0 : PS[0]! = rr 23 := by simp [PS]

theorem PS_get1 : PS[1]! = rr 17 := by simp [PS]

theorem QS_get0 : QS[0]! = rr 24 := by simp [QS]

theorem QS_get1 : QS[1]! = rr 25 := by simp [QS]

theorem rootsS_get0 : rootsS[0]! = rr 86 := by simp [rootsS]

theorem rootsS_get1 : rootsS[1]! = rr 27 := by simp [rootsS]

theorem PZ_get (k l : ℕ) (hl : l < (PZ k).size) : (PZ k)[l]! = idRows 24 := by
  rw [getElem!_pos (PZ k) l hl]
  simp [PZ]

theorem finite_co1 : Finite NativeSporadic.Co1 :=
  Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)

theorem oddCount_zero {ords : Array ℕ} (h : oddCount ords = 0) {i : ℕ} (hi : i < ords.size) :
    ords[i]! % 2 = 1 → ords[i]! = 1 := by
  unfold oddCount at h
  rw [countBelow_eq, zero_add, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.2 hi)
  simpa using this

theorem ordersWith_size (rho : Array ℕ) (F : Forest) : (ordersWith rho F).size = F.pts.size := by
  simp [ordersWith]

theorem forall_mem_two {α : Type*} (p : α → Prop) (a b : α) :
    (∀ x ∈ [a, b], p x) ↔ p a ∧ p b := by simp

theorem gram_nondeg {k : ℕ}
    (hk : gramOK (transposeRows 24 f0Rows) (Wk k) = true) :
    ∀ u ∈ {v : Vec24 | reg 27 • v = v ∧ reg (sIdx[k]!) • v = v},
      (∀ v ∈ {v : Vec24 | reg 27 • v = v ∧ reg (sIdx[k]!) • v = v}, bil₀ u v = 0) → u = 0 := by
  have h := nondeg_of_gramOK (Ms := [rr 27, rr (sIdx[k]!)]) hk
  have e : {v : Vec24 | ∀ M ∈ [rr 27, rr (sIdx[k]!)], rowsMatrix 24 M *ᵥ v = v} =
      {v : Vec24 | reg 27 • v = v ∧ reg (sIdx[k]!) • v = v} := by
    ext v
    simp only [Set.mem_ofPred_eq, forall_mem_two]
    rw [smul_reg_iff, smul_reg_iff]
  rw [e] at h
  exact h

theorem sIdx_J73 {k : ℕ} (hk : k < 3) : sIdx[k]! = getL 0 J73 k := by
  interval_cases k <;> rfl

end CFSG.Sporadic.Co1.Module.Odd
