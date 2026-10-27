module

public import CFSG.Sporadic.Co2Smith.GlDataChain
public import CFSG.Sporadic.Co2Smith.GlDataRoot
public import CFSG.Sporadic.Co2Smith.GlDataRootCheck

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3 MulAction

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem rep_psiArr
    {g : K} {R : Array ℕ}
    (hg : g.val.val = rowsMatrix 22 R) (h : Native.glPermOK R (Native.glPermArr R) = true) :
    Rep 2300 (Native.glPsiArr R) (psiK g) := by
  rw [psiK_apply]
  exact rep_compA (rep_compA rep_glCArr (rep_co2PermHom_of_permOK hg h).2) rep_glCInv

theorem glChain_original
    {ws : List (List ℕ)}
    {bs : List (Fin 2300)} (hb : bs.Nodup) {W : Array (List ℤ)} {ord : ℕ}
    (hws : ∀ w ∈ ws, ∀ k ∈ w, k < 22) (h : Native.glChainOK ws (bs.map Fin.val) W ord = true) :
    ∃ hk : ws.length ≤ (Native.glExtend (Native.glOrig ws) W).size,
      rawChainOK 2300 ((Native.glExtend (Native.glOrig ws) W).extract 0 ws.length)
          (Native.glExtend (Native.glOrig ws) W) (bs.map Fin.val).toArray W 1 = true ∧
        (rawOrbitSizes 2300 (Native.glExtend (Native.glOrig ws) W)
          (bs.map Fin.val).toArray).prod = ord ∧
        (RawSchreierDatum.ofArrays 2300 (by norm_num) (Native.glExtend (Native.glOrig ws) W)
          ws.length hk bs hb W).originalSubgroup =
            Subgroup.closure {σ | ∃ w ∈ ws, psiK (glE w) = σ} := by
  simp only [Native.glChainOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hperm, hk⟩, heq⟩, hc⟩, hord⟩ := h
  have hinv := (chainCheckFacts hc).strong_inv
  refine ⟨hk, hc, hord, ?_⟩
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext σ
  simp only [Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original]
  have key : ∀ i (hi : i < ws.length),
      permOfArr 2300 (Native.glExtend (Native.glOrig ws) W)[i]! = psiK (glE ws[i]) := by
    intro i hi
    have hwi : ws[i]! = ws[i] := getElem!_pos ws i hi
    have hrep := rep_glPsiArr (hws _ (List.getElem_mem hi)) (hperm _ (List.getElem_mem hi))
    have he := allLt_spec heq hi
    rw [hwi] at he
    exact eq_of_eqA (rep_permOfArr (hinv i (by omega))).1 hrep he
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨ws[i], List.getElem_mem hi, (key i hi).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    exact ⟨i, hi, key i hi⟩

@[expose] noncomputable def G0c : Subgroup K :=
  Subgroup.closure {g | ∃ w ∈ Native.glG0Words, glE w = g}

theorem glG0Words_lt : ∀ w ∈ Native.glG0Words, ∀ k ∈ w, k < 22 := by decide

theorem glChainG0_parts :
    Native.glChainOK Native.glG0Words Native.glChainG0Base Native.glChainG0W 9196830720 = true ∧
    (∀ w ∈ Native.glG0Words, Native.glMaps (Native.glR w) 80 80 = true) ∧
    Native.glPermOK Native.glGa (Native.glPermArr Native.glGa) = true ∧
    siftA 2300 (rawLevels 2300 (Native.glExtend (Native.glOrig Native.glG0Words)
      Native.glChainG0W) Native.glChainG0Base.toArray) Native.glChainG0Base.toArray 0
      (Native.glPsiArr Native.glGa) = false ∧
    ∀ r < 18, ∀ t ∈ Native.glParams r,
      Native.glPermOK (Native.glRootRows r t) (Native.glPermArr (Native.glRootRows r t)) =
          true ∧
        siftA 2300 (rawLevels 2300 (Native.glExtend (Native.glOrig Native.glG0Words)
          Native.glChainG0W) Native.glChainG0Base.toArray) Native.glChainG0Base.toArray 0
          (Native.glPsiArr (Native.glRootRows r t)) = true := by
  have h := glChainG0_check
  simp only [Native.glChainG0OK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem glChainG0Base_eq :
    Native.glChainG0Base = ([1, 3, 2, 4, 5] : List (Fin 2300)).map Fin.val := by
  decide

theorem map_psiK_G0c :
    G0c.map psiK = Subgroup.closure {σ | ∃ w ∈ Native.glG0Words, psiK (glE w) = σ} := by
  rw [G0c, MonoidHom.map_closure]
  congr 1
  ext σ
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩

theorem glChainG0_original :
    ∃ hk : Native.glG0Words.length ≤
        (Native.glExtend (Native.glOrig Native.glG0Words) Native.glChainG0W).size,
      rawChainOK 2300 ((Native.glExtend (Native.glOrig Native.glG0Words)
          Native.glChainG0W).extract 0 Native.glG0Words.length)
          (Native.glExtend (Native.glOrig Native.glG0Words) Native.glChainG0W)
          (([1, 3, 2, 4, 5] : List (Fin 2300)).map Fin.val).toArray Native.glChainG0W 1 = true ∧
        (rawOrbitSizes 2300 (Native.glExtend (Native.glOrig Native.glG0Words) Native.glChainG0W)
          (([1, 3, 2, 4, 5] : List (Fin 2300)).map Fin.val).toArray).prod = 9196830720 ∧
        (RawSchreierDatum.ofArrays 2300 (by norm_num)
          (Native.glExtend (Native.glOrig Native.glG0Words) Native.glChainG0W)
          Native.glG0Words.length hk [1, 3, 2, 4, 5] (by decide)
          Native.glChainG0W).originalSubgroup = G0c.map psiK := by
  have h := glChainG0_parts.1
  rw [glChainG0Base_eq] at h
  obtain ⟨hk, hc, hord, heq⟩ := glChain_original (by decide) glG0Words_lt h
  exact ⟨hk, hc, hord, heq.trans map_psiK_G0c.symm⟩

theorem card_G0c :
    Nat.card G0c = 9196830720 := by
  obtain ⟨hk, hc, hord, heq⟩ := glChainG0_original
  have hA := chainArrays_ofArrays (n := 2300) (hn := by norm_num) (k := Native.glG0Words.length)
    (hk := hk) (base := ([1, 3, 2, 4, 5] : List (Fin 2300))) (hb := by decide)
    (W := Native.glChainG0W) (chainCheckFacts hc).strong_inv
  have hcard := card_originalSubgroup_of_chainOK hA (by norm_num) hc
  rw [hord, heq, Subgroup.card_map_of_injective psiK_injective] at hcard
  exact hcard

theorem G0c_le_G1c :
    G0c ≤ G1c := by
  rw [G0c, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  exact co2PermHom_apply_of_maps (glE_val (glG0Words_lt w hw)) (by norm_num) (by norm_num)
    (glChainG0_parts.2.1 w hw)

theorem mem_G0c_iff_sift
    {g : K} {R : Array ℕ} (hg : g.val.val = rowsMatrix 22 R)
    (hR : Native.glPermOK R (Native.glPermArr R) = true) :
    siftA 2300 (rawLevels 2300 (Native.glExtend (Native.glOrig Native.glG0Words)
      Native.glChainG0W) Native.glChainG0Base.toArray) Native.glChainG0Base.toArray 0
      (Native.glPsiArr R) = true ↔ g ∈ G0c := by
  obtain ⟨hk, hc, hord, heq⟩ := glChainG0_original
  have hA := chainArrays_ofArrays (n := 2300) (hn := by norm_num) (k := Native.glG0Words.length)
    (hk := hk) (base := ([1, 3, 2, 4, 5] : List (Fin 2300))) (hb := by decide)
    (W := Native.glChainG0W) (chainCheckFacts hc).strong_inv
  rw [glChainG0Base_eq, siftA_iff_mem_originalSubgroup hA (by norm_num) hc (rep_psiArr hg hR),
    heq, Subgroup.mem_map_iff_mem psiK_injective]

theorem γ3K_not_mem_G0c :
    γ3K ∉ G0c := by
  intro h
  have h' := (mem_G0c_iff_sift γ3K_val glChainG0_parts.2.2.1).2 h
  rw [glChainG0_parts.2.2.2.1] at h'
  exact absurd h' (by decide)

theorem xRootK_mem_G0c
    {r t : ℕ} (hr : r < 18) (ht : t ∈ Native.glParams r) :
    xRootK r t ∈ G0c :=
  (mem_G0c_iff_sift (xRootK_val r t) (glChainG0_parts.2.2.2.2 r hr t ht).1).1
    (glChainG0_parts.2.2.2.2 r hr t ht).2

end CFSG.Sporadic.Co2Smith
