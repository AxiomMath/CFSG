module

public import CFSG.Sporadic.HNSchreier.SchreierData
public import CFSG.Sporadic.HNSchreier.SepCheck
public import CFSG.Sporadic.HNSchreier.Algebra
public import CFSG.Certificates.Kernel.StabChainBot
public import Certificates.Certificate2102
public import Certificates.Certificate2107
import Mathlib.Tactic.IntervalCases

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Sporadic.F5 CFSG.Sporadic.F5.Native CFSG.Sporadic.He.Native
open CFSG.Sporadic.HNSchreier.Native Matrix

theorem toMat_rowsM : toMat 5 133 rowsM = formM := by
  rw [rowsM, toMat_rowsOf, formM_eq]

theorem form_pres {C : Matrix (Fin 133) (Fin 133) (ZMod 5)} (hC : Cᵀ * formM * C = formM)
    (x y : Fin 133 → ZMod 5) : (C *ᵥ x) ⬝ᵥ (formM *ᵥ (C *ᵥ y)) = x ⬝ᵥ (formM *ᵥ y) := by
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hC]

theorem beta_eq (i j : X) : beta i j = vL i ⬝ᵥ (formM *ᵥ vL j) :=
  cert_hn_schreier_action_data.2.2.2.2.2.2.2.2.2.2.2.2.2 i j

theorem vL_a0 (i : X) : vL (a0 i) = matA *ᵥ vL i := by
  rw [a0_apply, ← (fam_hn_faithful_vector_orbit_action.2.2.2.1 i i.isLt).1]

theorem vL_a1 (i : X) : vL (a1 i) = matB *ᵥ vL i := by
  rw [a1_apply, ← (fam_hn_faithful_vector_orbit_action.2.2.2.1 i i.isLt).2]

@[expose] def betaStab : Subgroup (Equiv.Perm X) where
  carrier := {g | ∀ i j, beta (g i) (g j) = beta i j}
  mul_mem' {g h} hg hh i j := by
    show beta (g (h i)) (g (h j)) = beta i j
    rw [hg, hh]
  one_mem' i j := rfl
  inv_mem' {g} hg i j := by
    have := hg (g⁻¹ i) (g⁻¹ j)
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at this
    exact this.symm

theorem beta_invariant
    {g : Equiv.Perm X} (hg : g ∈ PH) (i j : X) :
    beta (g i) (g j) = beta i j := by
  have hle : PH ≤ betaStab := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · intro i j
      rw [beta_eq, beta_eq, vL_a0, vL_a0, form_pres form_parts.2.2.1]
    · intro i j
      rw [beta_eq, beta_eq, vL_a1, vL_a1, form_pres form_parts.2.2.2]
  exact hle hg i j

theorem toVec_bytesToNats (v : ByteArray) : toVec 5 133 (bytesToNats v) = toVecB 133 v := by
  funext j
  rw [toVec_apply, bytesToNats_get]
  rfl

@[irreducible] def sigR : Array (Array ℕ) := sigRows (hnsData.orbit ()) rowsM Data.baseList

theorem sigR_eq : sigR = sigRows (hnsData.orbit ()) rowsM Data.baseList := by unfold sigR; rfl

@[irreducible] def sigS : Array ByteArray :=
  sigsOf (hnsData.orbit ()) (frTable 22 133 sigR) hnsData.n

theorem sigS_eq : sigS = sigsOf (hnsData.orbit ()) (frTable 22 133 sigR) hnsData.n := by
  unfold sigS; rfl

theorem sigS_get {i : ℕ} (hi : i < nPts) :
    sigS[i]! = mulW 22 133 (frTable 22 133 sigR) (hnsData.orbit ()).keys[i]! := by
  rw [sigS_eq, sigsOf, getElem!_ofFn _ (show i < hnsData.n from hi)]

theorem sigR_get {k : ℕ} (hk : k < 22) :
    sigR[k]! = mulVec 5 133 rowsM (bytesToNats (hnsData.orbit ()).keys[baseIndex k]!) := by
  rw [sigR_eq, sigRows, getElem!_pos _ k (by simp [base_facts.1, hk])]
  simp only [List.getElem_toArray, List.getElem_map, baseIndex]
  rw [List.getD_eq_getElem _ _ (by rw [base_facts.1]; exact hk)]

theorem baseIndex_lt' {k : ℕ} (hk : k < 22) : baseIndex k < hnsData.n := baseIndex_lt hk

theorem sig_coord (i : X) (k : Fin 22) :
    toVecB 22 sigS[i.val]! k = beta i ⟨baseIndex k, baseIndex_lt' k.isLt⟩ := by
  rw [sigS_get i.isLt, toVecB_mulW (by norm_num) (by norm_num) _ (keys_canon' i.isLt)]
  rw [beta_eq, vL_eq i.isLt, vL_eq (baseIndex_lt k.isLt)]
  have hrow : ∀ j : Fin 133, toMatR 22 133 sigR k j = (formM *ᵥ PK (baseIndex k)) j := by
    intro j
    have e := congrFun (toVec_mulVec 5 133 rowsM
      (bytesToNats (hnsData.orbit ()).keys[baseIndex k]!)) j
    rw [← sigR_get k.isLt, toVec_bytesToNats, toMat_rowsM] at e
    exact e
  show ∑ j, toMatR 22 133 sigR k j * PK i j = ∑ j, PK i j * (formM *ᵥ PK (baseIndex k)) j
  exact Finset.sum_congr rfl fun j _ => by rw [hrow j, mul_comm]

abbrev baseX (k : Fin 22) : X := ⟨baseIndex k, baseIndex_lt' k.isLt⟩

theorem chainPt_eq : chainPt 0 = baseX 0 ∧ chainPt 1 = baseX 2 ∧ chainPt 2 = baseX 19 ∧
    chainPt 3 = baseX 1 := by
  decide +kernel

theorem eq_one_of_fix_chain
    {h : JH} (hfix : ∀ i < 4, h • chainPt i = chainPt i) : h = 1 := by
  obtain ⟨hcard, hL⟩ := level_cert
  have : Finite JH := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have htr := hns_pretransitive
  choose f hf using hL
  let P : ℕ → Finset X := fun i => match i with
    | 0 => Finset.univ
    | l + 1 => if hl : l < 3 then Finset.univ.image (fun k => f l hl k • chainPt (l + 1)) else ∅
  refine CFSG.KS.StabChain.eq_one_of_chain (G := JH) chainPt P 4 (fun i hi p hp => ?_) ?_ hfix
  · match i, hi, hp with
    | 0, _, _ => exact ⟨_, fun k hk => absurd hk (Nat.not_lt_zero k),
        (MulAction.exists_smul_eq JH (chainPt 0) p).choose_spec⟩
    | l + 1, hi, hp =>
      have hl : l < 3 := by omega
      simp only [P, dif_pos hl, Finset.mem_image] at hp
      obtain ⟨k, -, rfl⟩ := hp
      exact ⟨f l hl k, fun j hj => (hf l hl).1 k j (by omega), rfl⟩
  · have hc : ∀ l (hl : l < 3), (P (l + 1)).card = chainSizes.getD l 0 := by
      intro l hl
      simp only [P, dif_pos hl]
      rw [Finset.card_image_of_injective _ (hf l hl).2, Finset.card_univ, Fintype.card_fin]
    have h0 : (P 0).card = 1140000 := by
      simp only [P, Finset.card_univ, Fintype.card_fin]
      rfl
    rw [hcard, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_one, h0, hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num)]
    decide

theorem eq_one_of_fix_base
    {g : Equiv.Perm X} (hg : g ∈ PH) (hfix : ∀ k, g (baseX k) = baseX k) :
    g = 1 := by
  obtain ⟨h, hh⟩ := jEquivP.surjective ⟨g, hg⟩
  have e : ∀ x : X, h • x = g x := fun x => by
    rw [← jEquivP_apply h x, hh]
  have h1 : h = 1 := by
    refine eq_one_of_fix_chain fun i hi => ?_
    rw [e]
    obtain ⟨c0, c1, c2, c3⟩ := chainPt_eq
    interval_cases i
    · rw [c0]; exact hfix 0
    · rw [c1]; exact hfix 2
    · rw [c2]; exact hfix 19
    · rw [c3]; exact hfix 1
  have := congrArg Subtype.val hh
  rw [h1, map_one] at this
  exact this.symm

abbrev baseSet : Set X := {x | ∃ k : Fin 22, x = baseX k}

theorem ph_inf_fixing_base :
    PH ⊓ fixingSubgroup (Equiv.Perm X) baseSet = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgP, hgfix⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_bot]
  refine eq_one_of_fix_base hgP fun k => ?_
  have := (mem_fixingSubgroup_iff (Equiv.Perm X)).1 hgfix (baseX k) ⟨k, rfl⟩
  rwa [Equiv.Perm.smul_def] at this

theorem fam_hn_twenty_two_vector_separating_base :
    formMᵀ = formM ∧ formM.det ≠ 0 ∧ matAᵀ * formM * matA = formM ∧
      matBᵀ * formM * matB = formM ∧ (∀ g ∈ PH, ∀ i j : X, beta (g i) (g j) = beta i j) ∧
      PH ⊓ fixingSubgroup (Equiv.Perm X) baseSet = ⊥ :=
  ⟨form_parts.1, form_parts.2.1, form_parts.2.2.1, form_parts.2.2.2,
    fun _ hg => beta_invariant hg, ph_inf_fixing_base⟩

end CFSG.Sporadic.HNSchreier
