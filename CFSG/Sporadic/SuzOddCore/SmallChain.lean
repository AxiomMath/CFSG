module

public import CFSG.Sporadic.SuzOddCore.SmallChainCheck
public import CFSG.Sporadic.SuzOddCore.Family
public import CFSG.Certificates.NativeSchreierCard

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Certificates.RawSchreierDatum CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem chainArrays_rawOfArrays {n : ℕ} {hn : 1 ≤ n} {O S : Array (Array ℕ)}
    {hk : O.size ≤ S.size} {base : List (Fin n)} {hb : base.Nodup} {W : Array (List ℤ)}
    (hO : ∀ k < O.size, isInvA n O[k]! (invCand n O[k]!) = true)
    (hS : ∀ j < S.size, isInvA n S[j]! (invCand n S[j]!) = true) :
    ChainArrays (rawOfArrays n hn O S hk base hb W) O S (base.map Fin.val).toArray W where
  orig_size := rfl
  strong_size := rfl
  base_size := by
    change (base.map Fin.val).toArray.size = base.length
    simp
  orig i := by
    rw [rawOfArrays_original_get]
    exact (rep_permC (hO i i.2)).1
  strong j := by
    rw [rawOfArrays_strong_get]
    exact (rep_permC (hS j j.2)).1
  base_val i := by
    have hi : (i : ℕ) < base.length := i.2
    change (((⟨base.toArray, _⟩ : Vector (Fin n) base.length).get i : Fin n) : ℕ) = _
    rw [getElem!_pos _ _ (by simpa using hi)]
    simp [Vector.get]
    rfl
  deriv _ _ := rfl

theorem smallBase_vals : (smallBase.map Fin.val).toArray = smallBaseNat.toArray := by
  rw [smallBase_eq]
  rfl

theorem smallArr_inv {k : ℕ} (hk : k < 14) :
    isInvA 1782 (smallArr k) (invCand 1782 (smallArr k)) = true :=
  (Bool.and_eq_true_iff.1 (arrays_check.2.1 k hk)).2

theorem smallChain_arrays :
    ChainArrays smallChain smallGenArrs smallStrongArrs smallBaseNat.toArray smallDerivs := by
  rw [← smallBase_vals]
  refine chainArrays_rawOfArrays (fun k hk => ?_) (fun j hj => ?_)
  · have hk2 : k < 2 := by rw [smallGenArrs_size] at hk; exact hk
    interval_cases k
    · rw [smallGenArrs_get_zero]; exact smallArr_inv (by norm_num)
    · rw [smallGenArrs_get_one]; exact smallArr_inv (by norm_num)
  · have hj12 : j < 12 := by rw [smallStrongArrs_size] at hj; exact hj
    rw [smallStrongArrs_get hj12]
    exact smallArr_inv (by omega)

theorem smallChain_valid :
    ValidSchreier smallChain :=
  (validSchreier_of_chainOK smallChain_arrays (by norm_num) smallChain_check.1).1

theorem smallChain_orbitSizes :
    rawOrbitSizes 1782 smallStrongArrs smallBaseNat.toArray = [1782, 416, 100, 63, 32, 3] :=
  smallChain_check.2.1

theorem suzM_card_chain :
    Nat.card suzM = 448345497600 := by
  rw [← smallChain_originalSubgroup, card_originalSubgroup_of_chainOK smallChain_arrays
    (by norm_num) smallChain_check.1, smallChain_orbitSizes]
  rfl

theorem mem_suzM_iff_siftA
    {g : Array ℕ} {G : Equiv.Perm (Fin 1782)} (hG : Rep 1782 g G) :
    siftA 1782 smallLevels smallBaseNat.toArray 0 g = true ↔ G ∈ suzM := by
  rw [← smallChain_originalSubgroup]
  exact siftA_iff_mem_originalSubgroup smallChain_arrays (by norm_num) smallChain_check.1 hG

theorem smallStrong_mem
    {j : ℕ} (hj : j < 12) : permC 1782 (smallArr (j + 2)) ∈ suzM := by
  have hjf : j < smallChain.strongCount := by rw [smallChain_strongCount]; exact hj
  rw [← smallChain_originalSubgroup]
  have := smallChain.strong_mem_originalSubgroup smallChain_valid _
    (schreier_vector_get_mem_toList smallChain.strong ⟨j, hjf⟩)
  rwa [smallChain_strong_get] at this

theorem suzM_centralizer :

    Subgroup.centralizer (suzM : Set (Equiv.Perm (Fin 1782))) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  have hcm : ∀ m ∈ suzM, m * c = c * m := fun m hm => Subgroup.mem_centralizer_iff.1 hc m hm
  have h0 : c 0 = 0 := by
    by_contra hne
    obtain ⟨j, hj, hmove⟩ := smallChain_check.2.2.2.2.2.2.2 (c 0) (c 0).2 (fun h => hne (Fin.ext h))
    have hj12 : j < 12 := by
      have := List.mem_range.1 (List.mem_filter.1 hj).1
      rwa [smallStrongArrs_size] at this
    have hrep : Rep 1782 smallStrongArrs[j]! (permC 1782 (smallArr (j + 2))) := by
      rw [smallStrongArrs_get hj12]; exact rep_smallArr (by omega)
    have hfix : permC 1782 (smallArr (j + 2)) 0 = 0 := by
      rw [levelIdx, List.mem_filter, fixesFirst, allLt_iff] at hj
      have := hj.2 0 (by norm_num)
      rw [beq_iff_eq] at this
      have hb0 : smallBaseNat.toArray[0]! = 0 := rfl
      rw [hb0, hrep.apply (by norm_num)] at this
      exact Fin.ext this
    apply hmove
    rw [hrep (c 0)]
    have := congrArg (fun σ : Equiv.Perm (Fin 1782) => σ 0) (hcm _ (smallStrong_mem hj12))
    simp only [Equiv.Perm.mul_apply, hfix] at this
    rw [this]
  ext d
  obtain ⟨m, hm, rfl⟩ := suzM_transitive d
  have := congrArg (fun σ : Equiv.Perm (Fin 1782) => σ 0) (hcm m hm)
  simp only [Equiv.Perm.mul_apply, h0] at this
  rw [Equiv.Perm.one_apply, ← this]

theorem suzV_sq :
    suzV * suzV = 1 := by
  have h := eq_of_eqA (rep_compA rep_v rep_v) rep_idA smallChain_check.2.2.1
  exact h

theorem suzV_inv : suzV⁻¹ = suzV := by
  rw [inv_eq_iff_mul_eq_one, suzV_sq]

theorem suzV_ne_one : suzV ≠ 1 := by
  intro h
  have h0 := rep_v 0
  rw [h, Equiv.Perm.one_apply] at h0
  exact smallChain_check.2.2.2.1 h0

theorem suzV_not_mem :
    suzV ∉ suzM := by
  rw [← mem_suzM_iff_siftA rep_v, smallChain_check.2.2.2.2.1]
  simp

theorem suzV_conj_b0 :
    suzV * suzB0 * suzV⁻¹ ∈ suzM := by
  rw [suzV_inv, mul_assoc, ← mem_suzM_iff_siftA (rep_compA rep_v (rep_compA rep_b0 rep_v))]
  exact smallChain_check.2.2.2.2.2.1

theorem suzV_conj_b1 :
    suzV * suzB1 * suzV⁻¹ ∈ suzM := by
  rw [suzV_inv, mul_assoc, ← mem_suzM_iff_siftA (rep_compA rep_v (rep_compA rep_b1 rep_v))]
  exact smallChain_check.2.2.2.2.2.2.1

theorem suzV_conj_mem
    {m : Equiv.Perm (Fin 1782)} (hm : m ∈ suzM) : suzV * m * suzV⁻¹ ∈ suzM := by
  have hle : suzM ≤ suzM.comap (MulAut.conj suzV).toMonoidHom := by
    rw [suzM, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact suzV_conj_b0
    · exact suzV_conj_b1
  exact hle hm

theorem suzV_conj_eq :
    suzM.map (MulAut.conj suzV).toMonoidHom = suzM := by
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    exact suzV_conj_mem hm
  · intro m hm
    refine ⟨suzV⁻¹ * m * suzV, ?_, ?_⟩
    · have := suzV_conj_mem hm
      rw [suzV_inv] at this ⊢
      exact this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem mem_suzT_of_mem_suzM {m : Equiv.Perm (Fin 1782)} (hm : m ∈ suzM) : m ∈ suzT :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ hm)

theorem suzV_mem_suzT : suzV ∈ suzT := Subgroup.subset_closure (Set.mem_insert _ _)

theorem mem_suzT_iff
    (g : Equiv.Perm (Fin 1782)) : g ∈ suzT ↔ g ∈ suzM ∨ suzV * g ∈ suzM := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | hg
      · right; rw [suzV_sq]; exact suzM.one_mem
      · left; exact hg
    | one => left; exact suzM.one_mem
    | mul g h _ _ hg hh =>
      rcases hg with hg | hg <;> rcases hh with hh | hh
      · left; exact suzM.mul_mem hg hh
      · right
        rw [show suzV * (g * h) = suzV * g * suzV⁻¹ * (suzV * h) by group]
        exact suzM.mul_mem (suzV_conj_mem hg) hh
      · right; rw [← mul_assoc]; exact suzM.mul_mem hg hh
      · left
        have e : g * h = suzV * (suzV * g) * suzV⁻¹ * (suzV * h) := by
          rw [show suzV * (suzV * g) * suzV⁻¹ * (suzV * h) =
            (suzV * suzV) * g * (suzV⁻¹ * suzV) * h by group, suzV_sq, inv_mul_cancel, one_mul,
            mul_one]
        rw [e]
        exact suzM.mul_mem (suzV_conj_mem hg) hh
    | inv g _ hg =>
      rcases hg with hg | hg
      · left; exact suzM.inv_mem hg
      · right
        have e : suzV * g⁻¹ = suzV * (suzV * g)⁻¹ * suzV⁻¹ := by
          rw [show suzV * (suzV * g)⁻¹ * suzV⁻¹ = suzV * g⁻¹ * (suzV * suzV)⁻¹ by group, suzV_sq,
            inv_one, mul_one]
        rw [e]
        exact suzV_conj_mem (suzM.inv_mem hg)
  · rintro (h | h)
    · exact mem_suzT_of_mem_suzM h
    · have := suzT.mul_mem suzV_mem_suzT (mem_suzT_of_mem_suzM h)
      rwa [← mul_assoc, suzV_sq, one_mul] at this

theorem suzM_le_suzT : suzM ≤ suzT := fun _ hm => mem_suzT_of_mem_suzM hm

theorem suzM_normal_T :
    (suzM.subgroupOf suzT).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rcases (mem_suzT_iff g).1 g.2 with hg | hg
  · exact suzM.mul_mem (suzM.mul_mem hg hn) (suzM.inv_mem hg)
  · have e : (g : Equiv.Perm (Fin 1782)) * n * (g : Equiv.Perm (Fin 1782))⁻¹ =
        suzV⁻¹ * ((suzV * g) * n * (suzV * g)⁻¹) * suzV := by group
    rw [e, suzV_inv]
    have := suzV_conj_mem (suzM.mul_mem (suzM.mul_mem hg hn) (suzM.inv_mem hg))
    rwa [suzV_inv] at this

theorem suzM_index_T :
    (suzM.subgroupOf suzT).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨suzV, suzV_mem_suzT⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  change Xor ((b : Equiv.Perm (Fin 1782)) * suzV ∈ suzM) ((b : Equiv.Perm (Fin 1782)) ∈ suzM)
  rcases (mem_suzT_iff b).1 b.2 with hb | hb
  · right
    refine ⟨hb, fun hbv => suzV_not_mem ?_⟩
    have := suzM.mul_mem (suzM.inv_mem hb) hbv
    rwa [inv_mul_cancel_left] at this
  · left
    refine ⟨?_, fun hbm => suzV_not_mem ?_⟩
    · have e : (b : Equiv.Perm (Fin 1782)) * suzV = suzV * (suzV * b) * suzV⁻¹ := by
        rw [show suzV * (suzV * b) * suzV⁻¹ = (suzV * suzV) * b * suzV⁻¹ by group, suzV_sq,
          one_mul, suzV_inv]
      rw [e]
      exact suzV_conj_mem hb
    · have := suzM.mul_mem hb (suzM.inv_mem hbm)
      rwa [mul_inv_cancel_right] at this

theorem suzT_card :
    Nat.card suzT = 896690995200 := by
  have h := (suzM.subgroupOf suzT).card_mul_index
  rw [suzM_index_T, Nat.card_congr (Subgroup.subgroupOfEquivOfLe suzM_le_suzT).toEquiv,
    suzM_card_chain] at h
  omega

end CFSG.Sporadic.SuzOddCore
