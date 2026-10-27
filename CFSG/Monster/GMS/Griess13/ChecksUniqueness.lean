module

public import CFSG.Monster.GMS.Griess13.ChecksGlue
public import CFSG.Monster.GMS.Griess13.ChecksOrbit
public import CFSG.Monster.GMS.Griess13.Gluing
public import Certificates.Certificate10035
public meta import CFSG.Monster.GMS.Griess13.Data
public meta import Mathlib
public import CFSG.Sporadic.Suz.Setup

public section

namespace CFSG.Monster.GMS.Griess13.Co1Data

open scoped Matrix
open Finset

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem iotaChar_apply
    (v : Fin 6 → ZMod 3) : iotaChar v = iota v := rfl

theorem conjAct_of_conjMat
    {x : G} {A : Matrix (Fin 6) (Fin 6) (ZMod 3)} (h : ConjMat x A) :
    ConjAct iotaChar x Aᵀ where
  isUnit := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro v v' hvv
    have h1 : v ᵥ* A = v' ᵥ* A := by simpa only [Matrix.mulVec_transpose] using hvv
    have h2 : x * iota v * x⁻¹ = x * iota v' * x⁻¹ := by rw [h v, h v', h1]
    exact iota_injective (mul_left_cancel (mul_right_cancel h2))
  conj v := by
    rw [iotaChar_apply, Matrix.mulVec_transpose, iotaChar_apply]
    exact h v

theorem exists_iota_ne_one
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hρ : ρ ≠ 1) : ∃ v, ρ (iotaChar v) ≠ 1 := by
  by_contra hcon
  have hcon' : ∀ v, ρ (iotaChar v) = 1 := fun v => not_not.1 (fun h => hcon ⟨v, h⟩)
  have : IsSimpleGroup G := CFSG.Sporadic.Co1.isSimpleGroup_Co1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker ρ) with h | h
  · have hv : (Pi.single 0 1 : Fin 6 → ZMod 3) ≠ 0 := fun h0 => by simpa using congrFun h0 0
    have h1 : iota (Pi.single 0 1) ∈ MonoidHom.ker ρ := hcon' _
    rw [h, Subgroup.mem_bot] at h1
    exact iota_ne_one hv h1
  · refine hρ (MonoidHom.ext fun x => ?_)
    have hx : x ∈ MonoidHom.ker ρ := by rw [h]; exact Subgroup.mem_top x
    exact hx

theorem co1Act_iota_ne_one :
    ∃ v, CFSG.Monster.GMS.co1Act (iotaChar v) ≠ 1 := by
  refine ⟨Pi.single 0 1, fun h => ?_⟩
  have hv : (Pi.single 0 1 : Fin 6 → ZMod 3) ≠ 0 := fun h0 => by simpa using congrFun h0 0
  apply iota_ne_one hv
  apply mat_injective
  rw [mat_one]
  have h2 : Matrix.mulVecLin (mat (iota (Pi.single 0 1))) =
      Matrix.mulVecLin (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
    rw [Matrix.mulVecLin_one]
    exact h
  exact Matrix.toLin'.injective h2

theorem horbit_orbitIndexR :
    ∀ w ∈ lineReps, ∀ w' ∈ lineReps, orbitIndexR w = orbitIndexR w' →
      Relation.EqvGen (fun a b : F3Vec =>
        ∃ s : Fin 2, ∃ c : ZMod 3, c ≠ 0 ∧ Matrix.vecMul b (actN s)ᵀ = c • a) w w' := by
  intro w hw w' hw' h
  have hw0 := isLineReps_lineReps.ne_zero w hw
  have hw0' := isLineReps_lineReps.ne_zero w' hw'
  have hRel : ∀ s : Fin 2, ∀ v : F3Vec, v ≠ 0 → (fun a b : F3Vec =>
      ∃ s : Fin 2, ∃ c : ZMod 3, c ≠ 0 ∧ Matrix.vecMul b (actN s)ᵀ = c • a) (actN s *ᵥ v) v :=
    fun s v _ => ⟨s, 1, one_ne_zero, by rw [Matrix.vecMul_transpose, one_smul]⟩
  have h1 := eqvGen_to_rep (fun a b : F3Vec =>
    ∃ s : Fin 2, ∃ c : ZMod 3, c ≠ 0 ∧ Matrix.vecMul b (actN s)ᵀ = c • a) hRel hw0
  have h2 := eqvGen_to_rep (fun a b : F3Vec =>
    ∃ s : Fin 2, ∃ c : ZMod 3, c ≠ 0 ∧ Matrix.vecMul b (actN s)ᵀ = c • a) hRel hw0'
  rw [orbitClassR_eq_of_orbitIndexR_eq hw0 hw0' h] at h1
  exact h1.trans _ _ _ h2.symm

theorem card_lineReps_filter_orbitIndexR
    (k : Fin 3) (m n : ℕ)
    (hk : (univ.filter fun w : F3Vec => w ≠ 0 ∧ orbitIndexR w = k).card = m) (hmn : m = 2 * n) :
    (lineReps.filter fun w => orbitIndexR w = k).card = n := by
  have h := isLineReps_lineReps.two_mul_card_filter (fun w => orbitIndexR w = k)
    (fun w => Iff.of_eq (congrArg (fun x => x = k) (orbitIndexR_neg w)))
  have key : 2 * (lineReps.filter fun w => orbitIndexR w = k).card = m := h.trans hk
  omega

theorem repw_injective : Function.Injective repw :=
  Certificates.certificate10035.1

theorem repw_mem_lineReps : ∀ k : Fin 12, repw k ∈ lineReps := by
  have h : ∀ k : Fin 12, ∃ i : Fin 6, repw k i = 1 ∧ ∀ j : Fin 6, j < i → repw k j = 0 :=
    Certificates.certificate10035.2.1
  intro k
  exact mem_lineReps.2 (h k)

theorem exists_cr : ∃ cr : Fin 12 → ZMod 3, (∀ k, cr k ≠ 0) ∧
    ∀ k, Matrix.vecMul (repw k) (actR k)ᵀ = cr k • w1 := by
  choose cr hcr hw using actR_repw
  exact ⟨cr, hcr, fun k => by rw [Matrix.vecMul_transpose]; exact hw k⟩

theorem w1_dotProduct_v0_ne_zero : w1 ⬝ᵥ v0 ≠ 0 := by
  rw [w1_dotProduct_v0]
  exact one_ne_zero

theorem scal2_vecMul_w1 : Matrix.vecMul w1 scal2ᵀ = (2 : ZMod 3) • w1 := by
  rw [Matrix.vecMul_transpose]
  funext i
  simp [Matrix.mulVec, dotProduct, scal2]

theorem P_le_stabSubgroup :
    P ≤ stabSubgroup iotaChar w1 := by
  have hm : ∀ i : Fin 2, m i ∈ stabSubgroup iotaChar w1 := fun i =>
    (mem_stabSubgroup iotaChar).2 ⟨(actP i)ᵀ, conjAct_of_conjMat (conj_iota_m i), by
      rw [Matrix.vecMul_transpose]
      exact actP_w1 i⟩
  show Subgroup.closure {m 0, m 1} ≤ _
  rw [Subgroup.closure_le]
  rintro x (rfl | hx)
  · exact hm 0
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hm 1

private theorem decSigma_const :
    ∀ (s : Fin 2) (k : Fin 12) (j : Fin 2),
    decSigma s k j = decSigma s k 0 :=
  Certificates.certificate10035.2.2

theorem dec_spec'
    (s : Fin 2) (k : Fin 12) (j : Fin 2) :
    nGen s * r k * iotaChar v0 ^ (j : ℕ) =
      r (decSigma s k 0) * iotaChar (decU s k j) * tau ^ decEps s k j * decP s k j := by
  have h := dec_spec s k j
  rw [decSigma_const s k j] at h
  exact h

theorem huniq_co1 :
    ∀ M : Module.End (ZMod 2) (Fin 24 → ZMod 2),
    (∀ k : Fin 3, M * CFSG.Monster.GMS.co1Act (xGen k) =
      CFSG.Monster.GMS.co1Act (g * xGen k * g⁻¹) * M) →
      IsUnit M → M ^ 7 = 1 → M = CFSG.Monster.GMS.co1Act g :=
  fun M hM hu h7 => huniq_of_matrix CFSG.Monster.GMS.co1Act mat (fun _ => rfl) xGen g
    (fun M hM _ h7 => glue_unique M hM h7) M hM hu h7

theorem range_nGen : Set.range nGen = {n1, n2} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, nGen, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  exact or_congr eq_comm eq_comm

theorem xGen_mem_closure
    (k : Fin 3) : xGen k ∈ Subgroup.closure (Set.range nGen) := by
  rw [range_nGen]
  exact xGen_mem k

theorem conj_xGen_mem_closure
    (k : Fin 3) :
    g * xGen k * g⁻¹ ∈ Subgroup.closure (Set.range nGen) := by
  rw [g_conj_x k, range_nGen]
  exact yGen_mem k

theorem closure_range_nGen_union :
    Subgroup.closure (Set.range nGen ∪ {g}) = ⊤ := by
  have h : Set.range nGen ∪ {g} = ({n1, n2, g} : Set G) := by
    rw [range_nGen]
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]
  rw [h]
  exact closure_n1_n2_g

theorem co1_module_uniqueness :
    CFSG.Monster.GMS.Co1ModuleUniqueness := by
  intro V _ _ hV ρ hρ
  obtain ⟨cr, hcr, hwA⟩ := exists_cr
  have hw1R : w1 ∈ lineReps := by
    rw [← repw_zero]
    exact repw_mem_lineReps 0
  have h0 : (lineReps.filter fun w => orbitIndexR w = 0).card = 12 :=
    card_lineReps_filter_orbitIndexR 0 24 12 card_orbitIndexR_zero (by norm_num)
  have h1 : (lineReps.filter fun w => orbitIndexR w = 1).card = 132 :=
    card_lineReps_filter_orbitIndexR 1 264 132 card_orbitIndexR_one (by norm_num)
  have h2 : (lineReps.filter fun w => orbitIndexR w = 2).card = 220 :=
    card_lineReps_filter_orbitIndexR 2 440 220 card_orbitIndexR_two (by norm_num)
  exact exists_equiv_of_block_data ρ CFSG.Monster.GMS.co1Act iotaChar hV (by simp)
    (exists_iota_ne_one ρ hρ) co1Act_iota_ne_one nGen (fun s => (actN s)ᵀ)
    (fun s => conjAct_of_conjMat (conj_iota_n s)) isLineReps_lineReps orbitIndexR h0 h1 h2
    horbit_orbitIndexR repw repw_injective repw_mem_lineReps orbitIndexR_repw hw1R orbitIndexR_w1
    w1_dotProduct_v0_ne_zero r (fun k => (actR k)ᵀ) cr
    (fun k => conjAct_of_conjMat (conj_iota_r k)) hcr hwA tau scal2ᵀ 2
    (conjAct_of_conjMat conjMat_tau) tau_sq (by decide) scal2_vecMul_w1 P P_le_stabSubgroup
    P_le_commutator (fun s k => decSigma s k 0) decU decEps decP dec_spec' decP_mem g_pow_seven
    xGen xGen_mem_closure conj_xGen_mem_closure huniq_co1 closure_range_nGen_union

end CFSG.Monster.GMS.Griess13.Co1Data

namespace CFSG.Monster.GMS

theorem co1ModuleUniqueness :
    Co1ModuleUniqueness := Griess13.Co1Data.co1_module_uniqueness

end CFSG.Monster.GMS
