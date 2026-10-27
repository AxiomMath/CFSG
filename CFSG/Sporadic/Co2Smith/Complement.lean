module

public import CFSG.Sporadic.Co2Smith.QNormal

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open CFSG.Certificates.ExtraspecialNF
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose, instance_reducible] noncomputable def vAction : MulAction K V where
  smul u v := u.val.val *ᵥ v
  one_smul v := by
    show (1 : K).val.val *ᵥ v = v
    rw [val_val_one, Matrix.one_mulVec]
  mul_smul u w v := by
    show (u * w).val.val *ᵥ v = u.val.val *ᵥ (w.val.val *ᵥ v)
    rw [val_val_mul, Matrix.mulVec_mulVec]

attribute [local instance] vAction

theorem smul_V_def (u : K) (v : V) : u • v = u.val.val *ᵥ v := rfl

abbrev S0 : Subgroup K := Subgroup.closure ({aE, bE} : Set K)

theorem S0_le_Cz : S0 ≤ Cz := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact aE_mem_Cz
  · exact bE_mem_Cz

theorem S0_le_stabilizer :
    S0 ≤ MulAction.stabilizer K (vec Native.wFix) := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact aE_fix
  · exact bE_fix

@[expose] def pairGens : Array (Array ℕ) := #[aR, bR]

@[expose] def pairRec : Array ℕ × Array ℕ × Array ℕ :=
  Native.orbitBFS (Native.pairStep pairGens) 2 (Native.pairU * 4194304 + Native.pairV) 20000

@[expose] def pairPts : Array ℕ := pairRec.1

theorem pair_spec :
    pairPts[0]! = Native.pairU * 4194304 + Native.pairV ∧
    (∀ i < pairPts.size, ∀ l < 2,
      (Native.posMapN pairPts).getD (Native.pairStep pairGens l pairPts[i]!) pairPts.size <
        pairPts.size ∧
      pairPts[(Native.posMapN pairPts).getD (Native.pairStep pairGens l pairPts[i]!)
        pairPts.size]! = Native.pairStep pairGens l pairPts[i]!) ∧
    pairPts.contains (Native.colAct seedRowsArr[0]! Native.pairU * 4194304 +
      Native.colAct seedRowsArr[0]! Native.pairV) = false ∧
    Native.pairU < 4194304 ∧ Native.pairV < 4194304 ∧
    ∀ (i : ℕ) (hi : i < pairPts.size), pairPts[i] < 17592186044416 := by
  have h := pair_check
  simp only [Native.pairOK, Native.treeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, decide_eq_true_eq, and_assoc, Bool.not_eq_true',
    Array.all_eq_true, Bool.not_true, Bool.false_or] at h
  obtain ⟨-, -, -, h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨h0, fun i hi l hl => (h1 i hi).2.2 l hl, h2, h3, h4, h5⟩

theorem pairGens_zero : pairGens[0]! = aR := rfl

theorem pairGens_one : pairGens[1]! = bR := rfl

theorem colAct_lt' (R : Array ℕ) (v : ℕ) : Native.colAct R v < 4194304 := by
  simpa using colAct_lt R v

@[expose] noncomputable def decPair (p : ℕ) : V × V := (vec (p / 4194304), vec (p % 4194304))

@[expose] noncomputable def pairSet : Set (V × V) :=
  {q | ∃ i < pairPts.size, q = decPair pairPts[i]!}

theorem gen_smul_decPair {g : K} {l : ℕ} (hg : g.val.val = rowsMatrix 22 pairGens[l]!) (p : ℕ) :
    g • decPair p = decPair (Native.pairStep pairGens l p) := by
  have h1 := colAct_lt' pairGens[l]! (p / 4194304)
  have h2 := colAct_lt' pairGens[l]! (p % 4194304)
  rw [decPair, decPair, Prod.smul_mk, smul_V_def, smul_V_def, mulVec_vec hg, mulVec_vec hg,
    Native.pairStep]
  congr 2 <;> omega

theorem smul_mem_pairSet_of_gen {g : K} {l : ℕ} (hl : l < 2)
    (hg : g.val.val = rowsMatrix 22 pairGens[l]!) {q : V × V} (hq : q ∈ pairSet) :
    g • q ∈ pairSet := by
  obtain ⟨i, hi, rfl⟩ := hq
  obtain ⟨hpos, heq⟩ := pair_spec.2.1 i hi l hl
  exact ⟨_, hpos, by rw [gen_smul_decPair hg, heq]⟩

theorem smul_mem_pairSet
    {g : K} (hg : g ∈ S0) {q : V × V} (hq : q ∈ pairSet) :
    g • q ∈ pairSet := by
  have hfin : pairSet.Finite := Set.toFinite _
  induction hg using Subgroup.closure_induction generalizing q with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact smul_mem_pairSet_of_gen (l := 0) (by norm_num) (by rw [pairGens_zero]; exact aE_val') hq
    · exact smul_mem_pairSet_of_gen (l := 1) (by norm_num) (by rw [pairGens_one]; exact bE_val') hq
  | one => rwa [one_smul]
  | mul x y _ _ hx hy => rw [mul_smul]; exact hx (hy hq)
  | inv x _ hx =>
    have hmaps : Set.MapsTo (fun v => x • v) pairSet pairSet := fun v hv => hx hv
    have hinj : Set.InjOn (fun v => x • v) pairSet := fun v _ w _ h => MulAction.injective x h
    obtain ⟨v, hv, hvu⟩ := ((hfin.injOn_iff_bijOn_of_mapsTo hmaps).mp hinj).surjOn hq
    rw [← hvu]
    simpa only [inv_smul_smul] using hv

theorem pairPts_size_pos : 0 < pairPts.size := by
  by_contra h
  have h0 := pair_spec.1
  rw [getElem!_neg pairPts 0 (by omega)] at h0
  simp [Native.pairU, Native.pairV] at h0

theorem start_mem_pairSet :
    (vec Native.pairU, vec Native.pairV) ∈ pairSet := by
  refine ⟨0, pairPts_size_pos, ?_⟩
  have h4 := pair_spec.2.2.2.2.1
  rw [pair_spec.1, decPair]
  congr 2

theorem z0_smul_start_not_mem :
    z0 • (vec Native.pairU, vec Native.pairV) ∉ pairSet := by
  rintro ⟨i, hi, h⟩
  rw [Prod.smul_mk, smul_V_def, smul_V_def, mulVec_vec z0_val, mulVec_vec z0_val, decPair,
    Prod.mk.injEq] at h
  have hb := pair_spec.2.2.2.2.2 i hi
  rw [← getElem!_pos pairPts i hi] at hb
  have e1 := vec_injective (colAct_lt _ _)
    (by rw [show (2 : ℕ) ^ 22 = 4194304 by norm_num]; omega) h.1
  have e2 := vec_injective (colAct_lt _ _)
    (by rw [show (2 : ℕ) ^ 22 = 4194304 by norm_num]; omega) h.2
  have hc := pair_spec.2.2.1
  rw [seedRowsArr_zero] at hc
  have heq : Native.colAct co2RowsA Native.pairU * 4194304 + Native.colAct co2RowsA Native.pairV =
      pairPts[i]! := by
    rw [e1, e2]
    exact Nat.div_add_mod' _ _
  have hmem : pairPts.contains (Native.colAct co2RowsA Native.pairU * 4194304 +
      Native.colAct co2RowsA Native.pairV) = true := by
    rw [Array.contains_iff_mem, heq, getElem!_pos pairPts i hi]
    exact Array.getElem_mem hi
  rw [hc] at hmem
  exact Bool.false_ne_true hmem

theorem z0_not_mem_S0 :
    z0 ∉ S0 := fun h =>
  z0_smul_start_not_mem (smul_mem_pairSet h start_mem_pairSet)

theorem S0_inf_Q :
    S0 ⊓ Qsub = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgS, hgQ⟩
  obtain ⟨σ, u, rfl⟩ := (mem_closure_iff hE_rel).mp hgQ
  have hfix : (nf z0 hE σ u).val.val *ᵥ vec Native.wFix = vec Native.wFix :=
    S0_le_stabilizer hgS
  by_cases hu : u = 0
  · subst hu
    rw [nf_zero_vec] at hgS ⊢
    rcases zmod_two_cases σ with rfl | rfl
    · rw [ZMod.val_zero, pow_zero]
      exact Subgroup.one_mem _
    · rw [ZMod.val_one, pow_one] at hgS
      exact absurd hgS z0_not_mem_S0
  · exact absurd hfix (nf_moves σ hu)

end CFSG.Sporadic.Co2Smith
