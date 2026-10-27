module

public import CFSG.Sporadic.Co2Smith.GlDataG1
public import CFSG.Sporadic.Co2Rank3.Maximal

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3 MulAction

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem rep_glPsiArr
    {w : List ℕ}
    (hw : ∀ k ∈ w, k < 22)
    (h : Native.glPermOK (Native.glR w) (Native.glPermArr (Native.glR w)) = true) :
    Rep 2300 (Native.glPsiArr (Native.glR w)) (psiK (glE w)) := by
  rw [psiK_apply]
  exact rep_compA (rep_compA rep_glCArr (rep_co2PermHom_of_permOK (glE_val hw) h).2) rep_glCInv

theorem closure_psiK_card
    {ws : List (List ℕ)}
    {bs : List (Fin 2300)} (hb : bs.Nodup) {W : Array (List ℤ)} {ord : ℕ}
    (hws : ∀ w ∈ ws, ∀ k ∈ w, k < 22) (h : Native.glChainOK ws (bs.map Fin.val) W ord = true) :
    Nat.card (Subgroup.closure {σ | ∃ w ∈ ws, psiK (glE w) = σ}) = ord := by
  simp only [Native.glChainOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hperm, hk⟩, heq⟩, hc⟩, hord⟩ := h
  have hinv := (chainCheckFacts hc).strong_inv
  have hA := chainArrays_ofArrays (n := 2300) (hn := by norm_num) (k := ws.length) (hk := hk)
    (base := bs) (hb := hb) (W := W) hinv
  have hcard := card_originalSubgroup_of_chainOK hA (by norm_num) hc
  rw [hord] at hcard
  rw [← hcard, RawSchreierDatum.originalSubgroup]
  refine congrArg (fun A : Set (Equiv.Perm (Fin 2300)) => Nat.card (Subgroup.closure A)) ?_
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
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    exact ⟨i, hi, key i hi⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨ws[i], List.getElem_mem hi, (key i hi).symm⟩

theorem card_co2P03 :
    Nat.card (co2P0 ⊓ stabilizer (Equiv.Perm (Fin 2300)) (3 : Fin 2300) : Subgroup _) =
      20643840 := by
  have h := card_co2P0_eq_orbit_mul (3 : Fin 2300)
  rw [card_co2P0, ncard_co2Delta] at h
  omega

theorem card_co2P01 :
    Nat.card co2P01 = 13063680 := by
  have h := card_co2P0_eq_orbit_mul (1 : Fin 2300)
  rw [card_co2P0, ncard_co2Gamma] at h
  change Nat.card (co2P0 ⊓ stabilizer (Equiv.Perm (Fin 2300)) (1 : Fin 2300) : Subgroup _) = _
  omega

theorem glGen_spec :
    (∀ w ∈ Native.glNWords, Native.glMaps (Native.glR w) 80 80 = true ∧
      Native.glMaps (Native.glR w) 1172 1172 = true) ∧
    (∀ w ∈ Native.glMWords, Native.glMaps (Native.glR w) 80 80 = true ∧
      Native.glMaps (Native.glR w) 582 582 = true) := by
  have h := glElem_parts.2.2.2.2.2
  simp only [Native.glGenOK, Bool.and_eq_true, List.all_eq_true] at h
  exact h

theorem glNWords_lt : ∀ w ∈ Native.glNWords, ∀ k ∈ w, k < 22 := by decide

theorem glNWords_let :
    ∀ w ∈ Native.glNWords, (∀ k ∈ w, k ∈ Native.glCzLet) ∨ ∀ k ∈ w, k ∈ Native.glC0Let := by
  decide

theorem glNWords_mem :
    ∀ w ∈ Native.glNWords, glE w ∈ Cz ∨ glE w ∈ C0c := fun w hw =>
  (glNWords_let w hw).imp glE_mem_Cz glE_mem_C0c

theorem glNWords_fix :
    ∀ w ∈ Native.glNWords, co2PermHom (glE w) glP0 = glP0 ∧ co2PermHom (glE w) 1172 = 1172 :=
  fun w hw => ⟨co2PermHom_apply_of_maps (glE_val (glNWords_lt w hw)) _ _ (glGen_spec.1 w hw).1,
    co2PermHom_apply_of_maps (glE_val (glNWords_lt w hw)) _ _ (glGen_spec.1 w hw).2⟩

theorem closure_psiK_N :
    Subgroup.closure {σ | ∃ w ∈ Native.glNWords, psiK (glE w) = σ} =
      co2P0 ⊓ stabilizer (Equiv.Perm (Fin 2300)) (3 : Fin 2300) := by
  have hbase : Native.glChainNBase = ([1, 2, 522, 360] : List (Fin 2300)).map Fin.val := by
    decide
  have h : Native.glChainOK Native.glNWords Native.glChainNBase Native.glChainNW 20643840 =
      true := glChainN_check
  rw [hbase] at h
  have hcard := closure_psiK_card (by decide) glNWords_lt h
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hcard, card_co2P03])
  rw [Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨h0, h1⟩ := glNWords_fix w hw
  refine ⟨⟨psiK_mem_co2P _, MulAction.mem_stabilizer_iff.2 ?_⟩,
    MulAction.mem_stabilizer_iff.2 ?_⟩
  · rw [Equiv.Perm.smul_def, ← cPerm_p0, psiK_fix_iff]
    exact h0
  · rw [Equiv.Perm.smul_def, ← cPerm_1172, psiK_fix_iff]
    exact h1

end CFSG.Sporadic.Co2Smith
