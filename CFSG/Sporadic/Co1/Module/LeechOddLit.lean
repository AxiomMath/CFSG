module

public import CFSG.Sporadic.Co1.Module.TwoBKernel
public import CFSG.Certificates.Kernel.Co1M.RankSound

public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative Matrix
open CFSG.KD.Co1Odd CFSG.KC.Co1F2 CFSG.KC.M1F2

attribute [local instance] vecAct vecSMul

theorem mat_unpack_mul (A B : ℕ) : rowsMatrix 24 (unpackR 24 A) * rowsMatrix 24 (unpackR 24 B) =
    rowsMatrix 24 (unpackR 24 (mulF 24 A B)) := by
  rw [← rowsMatrix_mulRows, CFSG.KC.F2W.mulRows_unpackR]

theorem mat_unpack_one : rowsMatrix 24 (unpackR 24 (idF 24)) = 1 := by
  rw [CFSG.KC.VecK.unpackR_idF, rowsMatrix_idRows]

theorem treeOK71_facts {G P par lab : List ℕ} {n : ℕ} (hT : treeOK71 G P par lab n = true) :
    P.length = n ∧ P.getD 0 0 = idF 24 ∧ ∀ i < n, i = 0 ∨ ((par.getD i 0 < i ∧
      lab.getD i 0 < G.length) ∧ P.getD i 0 = mulF 24 (P.getD (par.getD i 0) 0)
        (G.getD (lab.getD i 0) 0)) := by
  unfold treeOK71 ptsOK71 at hT
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hT
  obtain ⟨⟨⟨⟨h1, -⟩, -⟩, h0⟩, hall⟩ := hT
  refine ⟨h1, h0, fun i hi => ?_⟩
  have h := hall i (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩)
  unfold ptOK71 at h
  simpa only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] using h

theorem tree71_elems {G P par lab : List ℕ} {n : ℕ} (hT : treeOK71 G P par lab n = true)
    (gens : ℕ → NativeSporadic.Co1)
    (hg : ∀ l < G.length, mat (gens l) = rowsMatrix 24 (unpackR 24 (G.getD l 0)))
    (K : Subgroup NativeSporadic.Co1) (hK : ∀ l < G.length, gens l ∈ K) :
    ∀ i < n, ∃ x ∈ K, mat x = rowsMatrix 24 (unpackR 24 (P.getD i 0)) := by
  obtain ⟨-, h0, hall⟩ := treeOK71_facts hT
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases hall i hi with h | ⟨⟨hp, hl⟩, he⟩
    · subst h
      exact ⟨1, K.one_mem, by rw [map_one, h0, mat_unpack_one]⟩
    · obtain ⟨x, hxK, hx⟩ := ih _ hp (lt_trans hp hi)
      refine ⟨x * gens (lab.getD i 0), K.mul_mem hxK (hK _ hl), ?_⟩
      rw [map_mul, hx, hg _ hl, mat_unpack_mul, ← he]

theorem distinctL_nodup : ∀ L : List ℕ, distinctL L = true → L.Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    have h' : a ∉ t ∧ distinctL t = true := by simpa [distinctL] using h
    exact List.nodup_cons.2 ⟨h'.1, distinctL_nodup t h'.2⟩

theorem canonL_get {L : List ℕ} (h : canonL L = true) {i : ℕ} (hi : i < L.length) :
    TwoBK.Canon (L.getD i 0) := by
  unfold canonL canonsL at h
  rw [List.all_eq_true] at h
  exact beq_iff_eq.1 (h i (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩))

theorem eq_of_mat_unpack {A B : ℕ} (hA : TwoBK.Canon A) (hB : TwoBK.Canon B)
    (h : rowsMatrix 24 (unpackR 24 A) = rowsMatrix 24 (unpackR 24 B)) : A = B :=
  TwoBK.eq_of_unpackR hA hB (CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid
    (validRows_unpackR A) (validRows_unpackR B) h)

theorem tree71_inj {P : List ℕ} (hd : distinctL P = true) (hc : canonL P = true)
    {x : ℕ → NativeSporadic.Co1} (hx : ∀ i < P.length, mat (x i) = rowsMatrix 24 (unpackR 24 (P.getD i 0)))
    {i j : ℕ} (hi : i < P.length) (hj : j < P.length) (e : x i = x j) : i = j := by
  have h := hx i hi
  rw [e, hx j hj] at h
  have hP := eq_of_mat_unpack (canonL_get hc hi) (canonL_get hc hj) h.symm
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at hP
  exact (List.Nodup.getElem_inj_iff (distinctL_nodup P hd)).1 hP

theorem tree71_complete {K : Subgroup NativeSporadic.Co1} {n : ℕ} [Finite NativeSporadic.Co1]
    {x : ℕ → NativeSporadic.Co1} (hxK : ∀ i < n, x i ∈ K)
    (hinj : ∀ i < n, ∀ j < n, x i = x j → i = j) (hcard : Nat.card K = n) :
    ∀ y ∈ K, ∃ i < n, y = x i := by
  have hsub : x '' Set.Iio n ⊆ (K : Set NativeSporadic.Co1) := by
    rintro _ ⟨i, hi, rfl⟩
    exact hxK i hi
  have hcard' : (x '' Set.Iio n).ncard = n := by
    have hinj' : Set.InjOn x (Set.Iio n) := fun i hi j hj e => hinj i hi j hj e
    rw [hinj'.ncard_image, Set.ncard_Iio_nat]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [hcard', ← hcard, ← Nat.card_coe_set_eq]; rfl) (Set.toFinite _)
  intro y hy
  have : y ∈ x '' Set.Iio n := by rw [heq]; exact hy
  obtain ⟨i, hi, rfl⟩ := this
  exact ⟨i, hi, rfl⟩

theorem fix_ncard_conj {ρ y : NativeSporadic.Co1} (h : IsConj ρ y) :
    {v : Vec24 | y • v = v}.ncard = {v : Vec24 | ρ • v = v}.ncard := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have e : {v : Vec24 | (c * ρ * c⁻¹) • v = v} = (fun v => c • v) '' {v | ρ • v = v} := by
    ext v
    constructor
    · intro hv
      refine ⟨c⁻¹ • v, ?_, by simp⟩
      change ρ • c⁻¹ • v = c⁻¹ • v
      have hv' : (c * ρ * c⁻¹) • v = v := hv
      rw [mul_smul, mul_smul] at hv'
      have := congrArg (fun z => c⁻¹ • z) hv'
      simpa using this
    · rintro ⟨w, hw, rfl⟩
      change (c * ρ * c⁻¹) • c • w = c • w
      rw [mul_smul, mul_smul, inv_smul_smul]
      change c • ρ • w = c • w
      rw [show ρ • w = w from hw]
  rw [e, Set.ncard_image_of_injective _ (MulAction.injective c)]

theorem smul_mat_eq {g : NativeSporadic.Co1} {R : Array ℕ} (hg : mat g = rowsMatrix 24 R) (v : Vec24) :
    g • v = rowsMatrix 24 R *ᵥ v := by
  rw [smul_eq_co1Act, co1Act_eq_mulVec, ← hg]

theorem tree71_point {G P par lab : List ℕ} {n : ℕ} [Finite NativeSporadic.Co1]
    (hT : treeOK71 G P par lab n = true) (hd : distinctL P = true) (hc : canonL P = true)
    (gens : ℕ → NativeSporadic.Co1)
    (hg : ∀ l < G.length, mat (gens l) = rowsMatrix 24 (unpackR 24 (G.getD l 0)))
    (K : Subgroup NativeSporadic.Co1) (hK : ∀ l < G.length, gens l ∈ K) (hcard : Nat.card K = n) :
    ∀ y ∈ K, ∃ i < P.length, mat y = rowsMatrix 24 (unpackR 24 (P.getD i 0)) := by
  obtain ⟨hPn, -, -⟩ := treeOK71_facts hT
  have hel := tree71_elems hT gens hg K hK
  choose x hxK hxm using hel
  let x' : ℕ → NativeSporadic.Co1 := fun i => if h : i < n then x i h else 1
  have hx'K : ∀ i < n, x' i ∈ K := fun i hi => by simp only [x', hi, ↓reduceDIte]; exact hxK i hi
  have hx'm : ∀ i < P.length, mat (x' i) = rowsMatrix 24 (unpackR 24 (P.getD i 0)) := fun i hi => by
    have hi' : i < n := hPn ▸ hi
    simp only [x', hi', ↓reduceDIte]
    exact hxm i hi'
  have hinj : ∀ i < n, ∀ j < n, x' i = x' j → i = j := fun i hi j hj e =>
    tree71_inj hd hc hx'm (hPn ▸ hi) (hPn ▸ hj) e
  intro y hy
  obtain ⟨i, hi, rfl⟩ := tree71_complete hx'K hinj hcard y hy
  exact ⟨i, hPn ▸ hi, hx'm i (hPn ▸ hi)⟩

theorem conj_point_facts {ρ y : NativeSporadic.Co1} {M : ℕ} (W : List ℕ) (hconj : IsConj ρ y)
    (hm : mat y = rowsMatrix 24 (unpackR 24 M)) (hρ2 : ρ * ρ = 1)
    (hρ : {v : Vec24 | ρ • v = v}.ncard = 65536) :
    M ≠ idF 24 ∧ CFSG.KD.Co1Odd.invK M = true ∧ rankOK M W = false := by
  refine ⟨fun h1 => ?_, ?_, ?_⟩
  · rw [h1, mat_unpack_one] at hm
    have h1' : y = 1 := mat_injective (by rw [hm, map_one])
    rw [h1'] at hconj
    obtain ⟨c, hc1⟩ := isConj_iff.1 hconj
    have hρ1 : ρ = 1 := by
      have e : ρ = c⁻¹ * (c * ρ * c⁻¹) * c := by group
      rw [e, hc1]
      group
    rw [hρ1] at hρ
    simp only [one_smul, Set.ofPred_true, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fun, ZMod.card, Fintype.card_fin] at hρ
    norm_num at hρ
  · obtain ⟨c, hc'⟩ := isConj_iff.1 hconj
    have hsq : y * y = 1 := by
      rw [← hc']
      calc c * ρ * c⁻¹ * (c * ρ * c⁻¹) = c * (ρ * ρ) * c⁻¹ := by group
        _ = 1 := by rw [hρ2]; group
    have hmm : rowsMatrix 24 (unpackR 24 (mulF 24 M M)) = rowsMatrix 24 (unpackR 24 (idF 24)) := by
      rw [← mat_unpack_mul, ← hm, ← map_mul, hsq, map_one, mat_unpack_one]
    have e := eq_of_mat_unpack (TwoBK.canon_mulF _ _) TwoBK.canon_idF hmm
    unfold CFSG.KD.Co1Odd.invK
    rw [e]
    simp
  · cases h3 : rankOK M W
    · rfl
    · have hle := CFSG.KC.Co1M.fix_le_of_rankOK h3
      have hset : {v : Vec24 | y • v = v} =
          {v : Vec24 | rowsMatrix 24 (unpackR 24 M) *ᵥ v = v} := by
        ext v
        simp only [Set.mem_ofPred_eq, smul_mat_eq hm]
      rw [← hset, fix_ncard_conj hconj, hρ] at hle
      norm_num at hle

theorem not_conj_of_tree71 {G P par lab : List ℕ} {W : List (List ℕ)} {n : ℕ}
    [Finite NativeSporadic.Co1]
    (hT : treeOK71 G P par lab n = true) (hd : distinctL P = true) (hc : canonL P = true)
    (hW : noConjOK P W = true) (gens : ℕ → NativeSporadic.Co1)
    (hg : ∀ l < G.length, mat (gens l) = rowsMatrix 24 (unpackR 24 (G.getD l 0)))
    (K : Subgroup NativeSporadic.Co1) (hK : ∀ l < G.length, gens l ∈ K) (hcard : Nat.card K = n)
    {ρ : NativeSporadic.Co1} (hρ2 : ρ * ρ = 1) (hρ : {v : Vec24 | ρ • v = v}.ncard = 65536) :
    ∀ y ∈ K, ¬ IsConj ρ y := by
  intro y hy hconj
  obtain ⟨i, hiP, hm⟩ := tree71_point hT hd hc gens hg K hK hcard y hy
  obtain ⟨h1, h2, h3⟩ := conj_point_facts (W.getD i []) hconj hm hρ2 hρ
  unfold noConjOK ncsOK71 at hW
  rw [List.all_eq_true] at hW
  have hWi := hW i (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩)
  unfold ncOK71 at hWi
  rw [h2, h3] at hWi
  simp only [Bool.not_true, Bool.or_false, beq_iff_eq] at hWi
  exact h1 hWi

end CFSG.Sporadic.Co1.Module.Odd

end
