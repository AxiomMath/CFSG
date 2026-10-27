module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement
open scoped Classical

section

variable {X : Type} [Group X] [Finite X] [Fintype (Subgroup.center X)]
private theorem comm_mem_center (hcl : commutator X ≤ Subgroup.center X) (a b : X) :
    ⁅a, b⁆ ∈ Subgroup.center X :=
  hcl (by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
private noncomputable def cent (hcl : commutator X ≤ Subgroup.center X) (a b : X) :
    Subgroup.center X :=
  ⟨⁅a, b⁆, comm_mem_center hcl a b⟩

@[simp] private theorem coe_cent (hcl : commutator X ≤ Subgroup.center X) (a b : X) :
    ((cent hcl a b : Subgroup.center X) : X) = ⁅a, b⁆ := rfl
private theorem cent_eq_one (hcl : commutator X ≤ Subgroup.center X) (a b : X) :
    cent hcl a b = 1 ↔ ⁅a, b⁆ = 1 := by
  constructor
  · intro h
    have := congrArg (fun z : Subgroup.center X => (z : X)) h
    simpa using this
  · intro h
    exact Subtype.ext (by simpa using h)
private noncomputable def eps (z : Subgroup.center X) : ZMod 2 :=
  if z = 1 then 0 else 1
private theorem eps_eq_zero_iff (z : Subgroup.center X) : eps z = 0 ↔ z = 1 := by
  unfold eps
  by_cases h : z = 1 <;> simp [h]
private theorem card_center_sq_eq_one_le_two (hcyc : IsCyclic (Subgroup.center X)) :
    (Finset.univ.filter (fun z : Subgroup.center X => z ^ 2 = 1)).card ≤ 2 := by
  haveI := hcyc
  exact IsCyclic.card_pow_eq_one_le (α := Subgroup.center X) (n := 2) (by norm_num)
private theorem mul_eq_one_of_sq_eq_one_of_ne_one (hcyc : IsCyclic (Subgroup.center X))
    {u v : Subgroup.center X} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) : u * v = 1 := by
  by_contra huv
  have hcard := card_center_sq_eq_one_le_two (X := X) hcyc
  have huv' : u ≠ v := by
    intro h
    exact huv (by rw [h]; simpa [pow_two] using hv)
  have hsub : ({1, u, v} : Finset (Subgroup.center X)) ⊆
      Finset.univ.filter (fun z : Subgroup.center X => z ^ 2 = 1) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simp [hu, hv]
  have h3 : ({1, u, v} : Finset (Subgroup.center X)).card = 3 := by
    have h1u : (1 : Subgroup.center X) ≠ u := fun h => hu1 h.symm
    have h1v : (1 : Subgroup.center X) ≠ v := fun h => hv1 h.symm
    rw [Finset.card_insert_of_notMem (by simp [h1u, h1v]),
        Finset.card_insert_of_notMem (by simp [huv']), Finset.card_singleton]
  have := Finset.card_le_card hsub
  omega
private theorem eps_mul_of_sq_eq_one (hcyc : IsCyclic (Subgroup.center X))
    (u v : Subgroup.center X) (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) :
    eps (u * v) = eps u + eps v := by
  by_cases hu1 : u = 1
  · rw [hu1]; simp [eps]
  by_cases hv1 : v = 1
  · rw [hv1]; simp [eps]
  have huv : u * v = 1 := mul_eq_one_of_sq_eq_one_of_ne_one hcyc hu hv hu1 hv1
  have h1 : eps (u * v) = 0 := by rw [huv]; simp [eps]
  have hu' : eps u = 1 := by simp [eps, hu1]
  have hv' : eps v = 1 := by simp [eps, hv1]
  rw [h1, hu', hv']
  decide
private theorem cent_sq_eq_one (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (a b : X) : cent hcl a b ^ 2 = 1 := by
  apply Subtype.ext
  have hcomm : Commute a ⁅a, b⁆ := Subgroup.mem_center_iff.1 (comm_mem_center hcl a b) a
  have h2 : ⁅a, b⁆ ^ 2 = 1 := by
    rw [hcomm.commutatorElement_pow_left 2, commutatorElement_eq_one_iff_mul_comm]
    exact ((Subgroup.mem_center_iff.1 (hsq a)) b).symm
  simpa using h2
private noncomputable def commVal (hcl : commutator X ≤ Subgroup.center X) (a b : X) :
    ZMod 2 :=
  eps (cent hcl a b)
private theorem commVal_mul_left (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (hcyc : IsCyclic (Subgroup.center X))
    (a b c : X) : commVal hcl (a * b) c = commVal hcl a c + commVal hcl b c := by
  have h1 : cent hcl (a * b) c = cent hcl b c * cent hcl a c := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_cent]
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hz : ⁅b, c⁆ ∈ Subgroup.center X := comm_mem_center hcl b c
    have e : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ := by
      rw [Subgroup.mem_center_iff.1 hz a]; simp
    rw [e]
  calc commVal hcl (a * b) c
      = eps (cent hcl b c * cent hcl a c) := by rw [commVal, h1]
    _ = eps (cent hcl b c) + eps (cent hcl a c) :=
          eps_mul_of_sq_eq_one hcyc (cent hcl b c) (cent hcl a c)
            (cent_sq_eq_one hcl hsq b c) (cent_sq_eq_one hcl hsq a c)
    _ = commVal hcl a c + commVal hcl b c := by
          rw [commVal, commVal]
          exact add_comm _ _
private theorem commVal_mul_right (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (hcyc : IsCyclic (Subgroup.center X))
    (a b c : X) : commVal hcl a (b * c) = commVal hcl a b + commVal hcl a c := by
  have h1 : cent hcl a (b * c) = cent hcl a b * cent hcl a c := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_cent]
    rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅a, b⁆ b]
    have hz : ⁅a, c⁆ ∈ Subgroup.center X := comm_mem_center hcl a c
    have e : b * ⁅a, c⁆ = ⁅a, c⁆ * b := Subgroup.mem_center_iff.1 hz b
    rw [e]
    simp [mul_assoc]
  calc commVal hcl a (b * c)
      = eps (cent hcl a b * cent hcl a c) := by rw [commVal, h1]
    _ = eps (cent hcl a b) + eps (cent hcl a c) :=
          eps_mul_of_sq_eq_one hcyc (cent hcl a b) (cent hcl a c)
            (cent_sq_eq_one hcl hsq a b) (cent_sq_eq_one hcl hsq a c)
    _ = commVal hcl a b + commVal hcl a c := by simp only [commVal]
private theorem commVal_center_left (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (hcyc : IsCyclic (Subgroup.center X))
    {z : X} (hz : z ∈ Subgroup.center X) (b : X) : commVal hcl z b = 0 := by
  simp only [commVal]
  rw [eps_eq_zero_iff, cent_eq_one]
  exact commutatorElement_eq_one_iff_commute.2 (Subgroup.mem_center_iff.1 hz b).symm
private theorem commVal_center_right (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (hcyc : IsCyclic (Subgroup.center X))
    (a : X) {z : X} (hz : z ∈ Subgroup.center X) : commVal hcl a z = 0 := by
  simp only [commVal]
  rw [eps_eq_zero_iff, cent_eq_one, commutatorElement_eq_one_iff_mul_comm]
  exact Subgroup.mem_center_iff.1 hz a
private theorem commVal_congr_left (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (hcyc : IsCyclic (Subgroup.center X))
    {a a' : X} (ha : a⁻¹ * a' ∈ Subgroup.center X) (b : X) :
    commVal hcl a b = commVal hcl a' b := by
  have h := commVal_mul_left hcl hsq hcyc a (a⁻¹ * a') b
  rw [mul_inv_cancel_left, commVal_center_left hcl hsq hcyc ha b] at h
  simpa using h.symm
private theorem commVal_congr_right (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (hcyc : IsCyclic (Subgroup.center X))
    (a : X) {b b' : X} (hb : b⁻¹ * b' ∈ Subgroup.center X) :
    commVal hcl a b = commVal hcl a b' := by
  have h := commVal_mul_right hcl hsq hcyc a b (b⁻¹ * b')
  rw [mul_inv_cancel_left, commVal_center_right hcl hsq hcyc a hb] at h
  simpa using h.symm
private abbrev QSpace (X : Type*) [Group X] : Type _ :=
  Additive (X ⧸ Subgroup.center X)
private theorem qspace_two_nsmul_eq_zero (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X)
    (x : QSpace X) : (2 : ℕ) • x = 0 := by
  induction x using Additive.rec with | _ a => ?_
  induction a using QuotientGroup.induction_on with | _ a => ?_
  show Additive.ofMul (((a : X ⧸ Subgroup.center X)) ^ 2) = Additive.ofMul 1
  congr 1
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).2 (hsq a)
@[instance_reducible]
private noncomputable def addCommGroupQSpace (hcl : commutator X ≤ Subgroup.center X) :
    AddCommGroup (QSpace X) :=
  { (inferInstance : AddGroup (QSpace X)) with
    add_comm := by
      intro a b
      induction a using Additive.rec with | _ a => ?_
      induction b using Additive.rec with | _ b => ?_
      induction a using QuotientGroup.induction_on with | _ a => ?_
      induction b using QuotientGroup.induction_on with | _ b => ?_
      show Additive.ofMul ((a : X ⧸ Subgroup.center X) * b) =
        Additive.ofMul ((b : X ⧸ Subgroup.center X) * a)
      congr 1
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have := comm_mem_center hcl b⁻¹ a⁻¹
      simpa [commutatorElement_def, mul_assoc] using this }

private noncomputable instance instAddCommGroupQSpace [Fact (commutator X ≤ Subgroup.center X)] :
    AddCommGroup (QSpace X) :=
  addCommGroupQSpace Fact.out
private noncomputable instance instModuleQSpace [Fact (commutator X ≤ Subgroup.center X)]
    [Fact (∀ x : X, x ^ 2 ∈ Subgroup.center X)] : Module (ZMod 2) (QSpace X) :=
  AddCommGroup.zmodModule (qspace_two_nsmul_eq_zero Fact.out)
private noncomputable def pair (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (hcyc : IsCyclic (Subgroup.center X))
    (x y : QSpace X) : ZMod 2 :=
  Quotient.liftOn₂' (s₁ := QuotientGroup.leftRel (Subgroup.center X))
    (s₂ := QuotientGroup.leftRel (Subgroup.center X))
    (Additive.toMul x : X ⧸ Subgroup.center X) (Additive.toMul y : X ⧸ Subgroup.center X)
    (commVal hcl) (by
      intro a b a' b' ha hb
      rw [QuotientGroup.leftRel_apply] at ha hb
      rw [commVal_congr_left hcl hsq hcyc ha, commVal_congr_right hcl hsq hcyc a' hb])

section

variable [Fact (commutator X ≤ Subgroup.center X)]
variable [Fact (∀ x : X, x ^ 2 ∈ Subgroup.center X)]
private theorem pair_add_left (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (hcyc : IsCyclic (Subgroup.center X))
    (x x' y : QSpace X) :
    pair hcl hsq hcyc (x + x') y = pair hcl hsq hcyc x y + pair hcl hsq hcyc x' y := by
  induction x using Additive.rec with | _ a => ?_
  induction x' using Additive.rec with | _ a' => ?_
  induction y using Additive.rec with | _ b => ?_
  induction a using QuotientGroup.induction_on with | _ a => ?_
  induction a' using QuotientGroup.induction_on with | _ a' => ?_
  induction b using QuotientGroup.induction_on with | _ b => ?_
  exact commVal_mul_left hcl hsq hcyc a a' b
private theorem pair_add_right (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (hcyc : IsCyclic (Subgroup.center X))
    (x y y' : QSpace X) :
    pair hcl hsq hcyc x (y + y') = pair hcl hsq hcyc x y + pair hcl hsq hcyc x y' := by
  induction x using Additive.rec with | _ a => ?_
  induction y using Additive.rec with | _ b => ?_
  induction y' using Additive.rec with | _ b' => ?_
  induction a using QuotientGroup.induction_on with | _ a => ?_
  induction b using QuotientGroup.induction_on with | _ b => ?_
  induction b' using QuotientGroup.induction_on with | _ b' => ?_
  exact commVal_mul_right hcl hsq hcyc a b b'
private noncomputable def form (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (hcyc : IsCyclic (Subgroup.center X)) :
    LinearMap.BilinForm (ZMod 2) (QSpace X) :=
  LinearMap.mk₂ (ZMod 2) (pair hcl hsq hcyc) (pair_add_left hcl hsq hcyc)
    (fun c x y => by
      have h0 : pair hcl hsq hcyc 0 y = 0 := by
        have := pair_add_left hcl hsq hcyc 0 0 y
        simpa using this
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · rw [zero_smul, zero_smul]; exact h0
      · simp)
    (pair_add_right hcl hsq hcyc)
    (fun c x y => by
      have h0 : pair hcl hsq hcyc x 0 = 0 := by
        have := pair_add_right hcl hsq hcyc x 0 0
        simpa using this
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · rw [zero_smul, zero_smul]; exact h0
      · simp)
private theorem form_mk (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (hcyc : IsCyclic (Subgroup.center X))
    (a b : X) :
    form hcl hsq hcyc (Additive.ofMul (a : X ⧸ Subgroup.center X))
      (Additive.ofMul (b : X ⧸ Subgroup.center X)) = commVal hcl a b := rfl
private theorem form_alt (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (hcyc : IsCyclic (Subgroup.center X)) :
    (form hcl hsq hcyc).IsAlt := by
  intro x
  induction x using Additive.rec with | _ a => ?_
  induction a using QuotientGroup.induction_on with | _ a => ?_
  rw [form_mk, commVal]
  have h : cent hcl a a = 1 := by
    apply Subtype.ext
    simp [cent, commutatorElement_self]
  rw [h]
  simp [eps]
private theorem form_separating_left (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (hcyc : IsCyclic (Subgroup.center X)) :
    (form hcl hsq hcyc).SeparatingLeft := by
  intro x hx
  induction x using Additive.rec with | _ a => ?_
  induction a using QuotientGroup.induction_on with | _ a => ?_
  have hc : a ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := hx (Additive.ofMul (g : X ⧸ Subgroup.center X))
    rw [form_mk, commVal, eps_eq_zero_iff, cent_eq_one] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  have h2 : (a : X ⧸ Subgroup.center X) = 1 := (QuotientGroup.eq_one_iff a).2 hc
  rw [h2]
  rfl
private theorem form_nondegenerate (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (hcyc : IsCyclic (Subgroup.center X)) :
    (form hcl hsq hcyc).Nondegenerate := by
  refine ⟨form_separating_left hcl hsq hcyc, ?_⟩
  intro y hy
  exact form_separating_left hcl hsq hcyc y
    (fun x => (form_alt hcl hsq hcyc).isRefl x y (hy x))
private noncomputable def pi : X →* Multiplicative (QSpace X) where
  toFun x := Multiplicative.ofAdd (Additive.ofMul (x : X ⧸ Subgroup.center X))
  map_one' := rfl
  map_mul' := by
    intro x y
    simp only [QuotientGroup.mk_mul, ofMul_mul, ofAdd_add]

@[simp] private theorem pi_apply (x : X) :
    pi x = Multiplicative.ofAdd (Additive.ofMul (x : X ⧸ Subgroup.center X)) := rfl

@[simp] private theorem toAdd_pi (x : X) :
    Multiplicative.toAdd (pi x) = Additive.ofMul (x : X ⧸ Subgroup.center X) := rfl
private theorem pi_surjective : Function.Surjective (pi : X →* Multiplicative (QSpace X)) := by
  intro m
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul m.toAdd)
  refine ⟨x, ?_⟩
  rw [pi_apply, hx]
  rfl
private theorem pi_ker : (pi : X →* Multiplicative (QSpace X)).ker = Subgroup.center X := by
  ext x
  rw [MonoidHom.mem_ker, pi_apply]
  constructor
  · intro h
    have h' : (x : X ⧸ Subgroup.center X) = 1 := by
      have h2 : Additive.ofMul (x : X ⧸ Subgroup.center X) = 0 := by
        have := congrArg Multiplicative.toAdd h
        simpa using this
      have h3 := congrArg Additive.toMul h2
      simpa using h3
    exact (QuotientGroup.eq_one_iff x).1 h'
  · intro h
    rw [(QuotientGroup.eq_one_iff x).2 h]
    rfl

end
private theorem exists_sympForm (hcl : commutator X ≤ Subgroup.center X)
    (hsq : ∀ x : X, x ^ 2 ∈ Subgroup.center X) (hcyc : IsCyclic (Subgroup.center X)) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (B : LinearMap.BilinForm (ZMod 2) W) (π : X →* Multiplicative W),
      B.Nondegenerate ∧ B.IsAlt ∧ Function.Surjective π ∧ π.ker = Subgroup.center X ∧
      ∀ x y : X, B (Multiplicative.toAdd (π x)) (Multiplicative.toAdd (π y)) = 0 ↔
        ⁅x, y⁆ = 1 := by
  haveI : Fact (commutator X ≤ Subgroup.center X) := ⟨hcl⟩
  haveI : Fact (∀ x : X, x ^ 2 ∈ Subgroup.center X) := ⟨hsq⟩
  refine ⟨QSpace X, inferInstance, inferInstance, inferInstance,
    form hcl hsq hcyc, pi, ?_, ?_, ?_, ?_, ?_⟩
  · exact form_nondegenerate hcl hsq hcyc
  · exact form_alt hcl hsq hcyc
  · exact pi_surjective
  · exact pi_ker
  · intro x y
    change form hcl hsq hcyc (Additive.ofMul (x : X ⧸ Subgroup.center X))
        (Additive.ofMul (y : X ⧸ Subgroup.center X)) = 0 ↔ ⁅x, y⁆ = 1
    rw [form_mk, commVal, eps_eq_zero_iff, cent_eq_one]

end
theorem sympForm_holds : SympForm := by
  intro X _ _ _ hcl hsq hcyc
  haveI : Fintype (Subgroup.center X) := Fintype.ofFinite (Subgroup.center X)
  exact exists_sympForm hcl hsq hcyc

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
