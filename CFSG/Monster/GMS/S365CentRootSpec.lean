module

public import CFSG.Monster.GMS.S365Root
public import CFSG.Monster.GMS.S365CosetSpec
public import CFSG.Monster.GMS.S365USpec
public import Certificates.Data.CFSGNative.Co1.S365CentRoot
public import CFSG.Monster.GMS.S365CentRootSpecInputs
public import Certificates.Certificate10038
public meta import CFSG.Monster.GMS.S365Root
public meta import CFSG.Sporadic.Co1.Module.PairsCheck
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import Certificates.Data.CFSGNative.Co1.S365CentRoot
public import CFSG.Monster.GMS.S365Coset
public import Certificates.Certificate10042Base

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

open scoped Matrix
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.S365UNative CFSG.Sporadic.Co1.S365CentNative

theorem rootCount120_ok : rootCount120 = true :=
  Certificates.certificate10038.1

theorem countBelow_eq_zero_iff (p : ℕ → Bool) (n : ℕ) :
    countBelow p n 0 = 0 ↔ ∀ x < n, p x = false := by
  rw [countBelow_eq, zero_add, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h x hx
    have := h (Finset.mem_range.2 hx)
    simpa using this
  · intro h x hx
    have := h x (Finset.mem_range.1 hx)
    simp [this]

theorem rootFixOK_ok : rootFixOK = true :=
  Certificates.certificate10038.2

@[expose] def VP (v : Fin 24 → ZMod 2) : Prop :=
  v ∈ co1Orbit 0 ∧ ∀ c ∈ rootFix, bil₀ v (toVecD 24 c) = 0

theorem orthAllN_iff {x : ℕ} :
    orthAllN rootGs x = true ↔ ∀ c ∈ rootFix, bil₀ (toVecD 24 x) (toVecD 24 c) = 0 := by
  have h : orthAllN rootGs x = orthAll rootGs x := rfl
  rw [h, orthAll_iff]
  constructor
  · intro hall c hc
    have h1 := hall (dualCode c) (List.mem_map.2 ⟨c, hc, rfl⟩)
    rw [bil₀_toVecD, h1]
    rfl
  · intro hall g hg
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hg
    have h1 := hall c hc
    rw [bil₀_toVecD] at h1
    by_contra hne
    have : parity24 (x &&& dualCode c) = true := by simpa using hne
    simp [this] at h1

theorem rootP_iff
    {x : ℕ} (hx : x < 2 ^ 24) :
    rootP qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 rootGs x = true ↔
      VP (toVecD 24 x) := by
  unfold rootP VP
  rw [Bool.and_eq_true, orthAllN_iff, beq_iff_eq, tyLabN_eq]
  constructor
  · rintro ⟨ho, h3⟩
    refine ⟨?_, ho⟩
    rw [co1Orbit_zero, orbit_Co1_eq]
    exact (tyLab_spec x hx 3 (by norm_num)).1 h3
  · rintro ⟨h0, ho⟩
    refine ⟨ho, ?_⟩
    rw [co1Orbit_zero, orbit_Co1_eq] at h0
    exact (tyLab_spec x hx 3 (by norm_num)).2 h0

theorem exists_onePlus_of_hasPreN {B : List (ℕ × ℕ)} {Mt : Array ℕ} {x : ℕ}
    (h : hasPreN B Mt x = true) : ∃ q, onePlus Mt q = x := by
  unfold hasPreN at h
  split at h
  · rename_i q _
    exact ⟨q, beq_iff_eq.1 h⟩
  · exact absurd h (by decide)

theorem bool_of_and_not {p b : Bool} (h : (p && !b) = false) (hp : p = true) : b = true := by
  cases p <;> cases b <;> simp_all

theorem exists_preimage_of_VP
    {sA : Co1} (hs : matHom sA = rowsMatrix 24 rowsSA)
    {u : Fin 24 → ZMod 2} (hu : VP u) : ∃ v, u = v + co1Act sA v := by
  have hcheck := rootCount120_ok
  unfold rootCount120 rootCountN rootCountNB at hcheck
  simp only [Bool.and_eq_true, beq_iff_eq] at hcheck
  obtain ⟨-, hbad⟩ := hcheck
  obtain ⟨x, hx, rfl⟩ : u ∈ toVecD 24 '' Set.Iio (2 ^ 24) := by
    rw [toVecD_image_Iio]
    trivial
  have hp : rootP qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 rootGs x =
      true := (rootP_iff hx).2 hu
  have hb := (countBelow_eq_zero_iff _ _).1 hbad x hx
  obtain ⟨q, e1⟩ := exists_onePlus_of_hasPreN (bool_of_and_not hb hp)
  refine ⟨toVecD 24 q, ?_⟩
  have e2 : toVecD 24 x = toVecD 24 q + rowsMatrix 24 rowsSA *ᵥ toVecD 24 q := by
    rw [← e1]
    unfold onePlus
    rw [toVecD_xor, rowsMatrix_mulVec]
  rw [e2, ← hs]
  rfl

theorem V_sA_eq
    {sA : Co1} (hs : matHom sA = rowsMatrix 24 rowsSA) :
    {u : Fin 24 → ZMod 2 | u ∈ co1Orbit 0 ∧ ∃ v, u = v + co1Act sA v} = {u | VP u} := by
  have hfix := rootFixOK_ok
  unfold rootFixOK at hfix
  ext u
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hu, v, hv⟩
    refine ⟨hu, fun c hc => ?_⟩
    have hc' := List.all_eq_true.1 hfix c hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
    have hfv : sA • toVecD 24 c = toVecD 24 c := by
      rw [act_packed sA rowsSA hs c]
      exact congrArg (toVecD 24) (beq_iff_eq.1 hc'.2)
    rw [hv]
    exact bil₀_add_smul_fixed hfv v
  · intro hu
    exact ⟨hu.1, exists_preimage_of_VP hs hu⟩

theorem card_V_sA
    {sA : Co1} (hs : matHom sA = rowsMatrix 24 rowsSA) :
    {u : Fin 24 → ZMod 2 | u ∈ co1Orbit 0 ∧ ∃ v, u = v + co1Act sA v}.ncard = 120 := by
  rw [V_sA_eq hs]
  have hcheck := rootCount120_ok
  unfold rootCount120 rootCountN rootCountNB at hcheck
  simp only [Bool.and_eq_true, beq_iff_eq] at hcheck
  obtain ⟨hcnt, -⟩ := hcheck
  rw [← hcnt]
  exact ncard_eq_countBelow (fun x hx => rootP_iff hx)

theorem card_V
    {r : Co1} (hr : IsCo1TwoA r) :
    {u : Fin 24 → ZMod 2 | u ∈ co1Orbit 0 ∧ ∃ v, u = v + co1Act r v}.ncard = 120 := by
  obtain ⟨sA, hs⟩ := exists_sA
  obtain ⟨hsA2, hsAf⟩ := sA_facts hs
  have hrf : (co1Fix r).ncard = 2 ^ 16 := (co1InvolutionFacts.1 r hr.1).2 hr.2
  obtain ⟨c₀, hc₀⟩ := isConj_iff.1 (isConj_of_fix hr.1 hrf hsA2 hsAf)
  have hcr : sA * c₀ = c₀ * r := by
    rw [← hc₀]
    group
  have hrc : r * c₀⁻¹ = c₀⁻¹ * sA := by
    rw [← hc₀]
    group
  rw [← card_V_sA hs]
  have himg : {u : Fin 24 → ZMod 2 | u ∈ co1Orbit 0 ∧ ∃ v, u = v + co1Act sA v} =
      (fun u => c₀ • u) '' {u : Fin 24 → ZMod 2 | u ∈ co1Orbit 0 ∧ ∃ v, u = v + co1Act r v} := by
    ext u
    constructor
    · rintro ⟨hu, v, hv⟩
      refine ⟨c₀⁻¹ • u, ⟨?_, c₀⁻¹ • v, ?_⟩, smul_inv_smul c₀ u⟩
      · rw [co1Orbit_zero] at hu ⊢
        exact orbit_smul_mem _ hu
      · have h1 : co1Act r (c₀⁻¹ • v) = c₀⁻¹ • co1Act sA v := by
          show r • (c₀⁻¹ • v) = c₀⁻¹ • (sA • v)
          rw [← mul_smul, ← mul_smul, hrc]
        rw [h1, ← smul_add, ← hv]
    · rintro ⟨u', ⟨hu', v, hv⟩, rfl⟩
      refine ⟨?_, c₀ • v, ?_⟩
      · rw [co1Orbit_zero] at hu' ⊢
        exact orbit_smul_mem _ hu'
      · have h1 : co1Act sA (c₀ • v) = c₀ • co1Act r v := by
          show sA • (c₀ • v) = c₀ • (r • v)
          rw [← mul_smul, ← mul_smul, hcr]
        rw [h1, ← smul_add, ← hv]
  rw [himg]
  exact (Set.ncard_image_of_injective _ (fun u u' h => by
    simpa using congrArg (fun z => c₀⁻¹ • z) h)).symm

end S365

end CFSG.Monster.GMS
