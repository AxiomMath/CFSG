module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixTenThree
import CFSG.GroupTheory.CommutingProductFixedSubgroup
import CFSG.LocalAnalysis.UniquenessCase.UC6S9
public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
public import CFSG.LocalAnalysis.UniquenessCase.UC6R

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.UC6
open scoped Matrix MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

private noncomputable def prodMulEquivOfIsComplement'
    {E : Type*} [Group E] {A B : Subgroup E} (hcomm : ∀ a b : E, a * b = b * a)
    (h : A.IsComplement' B) : A × B ≃* E := by
  letI : CommGroup E := { mul_comm := hcomm }
  refine MulEquiv.ofBijective
    ({ toFun := fun x => (x.1 : E) * (x.2 : E)
       map_one' := by simp
       map_mul' := fun x y => by
         simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
         ac_rfl } : A × B →* E)
    (show Function.Bijective (fun x : A × B => (x.1 : E) * (x.2 : E)) from h)

private noncomputable def coordTwo {p : ℕ} {A B : Type*} [Group A] [Group B]
    (eA : A ≃* Multiplicative (Fin 1 → ZMod p)) (eB : B ≃* Multiplicative (Fin 1 → ZMod p)) :
    A × B ≃* Multiplicative (Fin 2 → ZMod p) where
  toFun x := Multiplicative.ofAdd
    (fun i => if i = 0 then Multiplicative.toAdd (eA x.1) 0 else Multiplicative.toAdd (eB x.2) 0)
  invFun y := (eA.symm (Multiplicative.ofAdd (fun _ : Fin 1 => Multiplicative.toAdd y 0)),
    eB.symm (Multiplicative.ofAdd (fun _ : Fin 1 => Multiplicative.toAdd y 1)))
  left_inv x := by
    obtain ⟨a, b⟩ := x
    apply Prod.ext
    · apply eA.injective
      rw [eA.apply_symm_apply]
      apply Multiplicative.toAdd.injective
      funext j
      fin_cases j
      rfl
    · apply eB.injective
      rw [eB.apply_symm_apply]
      apply Multiplicative.toAdd.injective
      funext j
      fin_cases j
      rfl
  right_inv y := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
  map_mul' x y := by
    obtain ⟨a, b⟩ := x
    obtain ⟨c, d⟩ := y
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp [map_mul]

private theorem exists_adapted_coord' {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    (hEel : CFSG.Open.IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {A B : Subgroup G} (hAE : A ≤ E) (hBE : B ≤ E)
    (hA : Nat.card A = p) (hB : Nat.card B = p) (hne : A ≠ B) :
    ∃ (e : ↥E ≃* Multiplicative (Fin 2 → ZMod p)) (a₀ b₀ : ↥E),
      a₀ ∈ A.subgroupOf E ∧ b₀ ∈ B.subgroupOf E ∧
      e a₀ = Multiplicative.ofAdd (Pi.single 0 1) ∧
      e b₀ = Multiplicative.ofAdd (Pi.single 1 1) ∧
      (∀ a : ↥E, a ∈ A.subgroupOf E → Multiplicative.toAdd (e a) 1 = 0) ∧
      (∀ b : ↥E, b ∈ B.subgroupOf E → Multiplicative.toAdd (e b) 0 = 0) := by
  have hcommE : ∀ a b : ↥E, a * b = b * a := hEel.1.is_comm.comm
  have hpowE : ∀ a : ↥E, a ^ p = 1 := fun a => Subtype.ext (hEel.2 a a.2)
  have hAB : A ⊓ B = ⊥ := by
    have hdvd : Nat.card ↥(A ⊓ B) ∣ p := by
      have h1 : Nat.card ↥((A ⊓ B).subgroupOf A) ∣ Nat.card ↥A :=
        Subgroup.card_subgroup_dvd_card ((A ⊓ B).subgroupOf A)
      have h2 : Nat.card ↥((A ⊓ B).subgroupOf A) = Nat.card ↥(A ⊓ B) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      rwa [h2, hA] at h1
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h1 | hp
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hp, hA])
      have hBA : A ≤ B := by rw [← heq]; exact inf_le_right
      exact hne (Subgroup.eq_of_le_of_card_ge hBA (by rw [hA, hB]))
  let A' : Subgroup ↥E := A.subgroupOf E
  let B' : Subgroup ↥E := B.subgroupOf E
  have hA' : Nat.card A' = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE).toEquiv, hA]
  have hB' : Nat.card B' = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBE).toEquiv, hB]
  have hdisj : Disjoint A' B' := by
    rw [disjoint_iff]
    change A.subgroupOf E ⊓ B.subgroupOf E = ⊥
    rw [← Subgroup.comap_subtype A E, ← Subgroup.comap_subtype B E, ← Subgroup.comap_inf]
    rw [show A ⊓ B = ⊥ from hAB]
    simp
  have hcomp : A'.IsComplement' B' := by
    refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ hdisj
    rw [hA', hB', hEcard]
    ring
  obtain ⟨eA⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := ↥A') (p := p)
    (n := 1) (fun a b => Subtype.ext (hcommE a.1 b.1)) (fun a => Subtype.ext (hpowE a.1))
    (by rw [hA', pow_one])
  obtain ⟨eB⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := ↥B') (p := p)
    (n := 1) (fun a b => Subtype.ext (hcommE a.1 b.1)) (fun a => Subtype.ext (hpowE a.1))
    (by rw [hB', pow_one])
  let eAB := prodMulEquivOfIsComplement' hcommE hcomp
  let e : ↥E ≃* Multiplicative (Fin 2 → ZMod p) := eAB.symm.trans (coordTwo eA eB)
  let aA : ↥A' := eA.symm (Multiplicative.ofAdd (fun _ : Fin 1 => (1 : ZMod p)))
  let bB : ↥B' := eB.symm (Multiplicative.ofAdd (fun _ : Fin 1 => (1 : ZMod p)))
  have hvalA : e (aA : ↥E) = Multiplicative.ofAdd (Pi.single 0 1) := by
    have h1 : eAB (aA, 1) = (aA : ↥E) := by
      show (aA : ↥E) * (1 : ↥E) = (aA : ↥E)
      simp
    have h2 : eAB.symm (aA : ↥E) = (aA, 1) := by
      rw [MulEquiv.symm_apply_eq]; exact h1.symm
    show coordTwo eA eB (eAB.symm (aA : ↥E)) = _
    rw [h2]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp [coordTwo, aA, eA.apply_symm_apply]
  have hvalB : e (bB : ↥E) = Multiplicative.ofAdd (Pi.single 1 1) := by
    have h1 : eAB (1, bB) = (bB : ↥E) := by
      show (1 : ↥E) * (bB : ↥E) = (bB : ↥E)
      simp
    have h2 : eAB.symm (bB : ↥E) = (1, bB) := by
      rw [MulEquiv.symm_apply_eq]; exact h1.symm
    show coordTwo eA eB (eAB.symm (bB : ↥E)) = _
    rw [h2]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp [coordTwo, bB, eB.apply_symm_apply]
  refine ⟨e, (aA : ↥E), (bB : ↥E), aA.2, bB.2, hvalA, hvalB, ?_, ?_⟩
  · intro a ha
    have key : Multiplicative.toAdd (coordTwo eA eB ((⟨a, ha⟩ : ↥A'), 1)) 1 = 0 := by
      simp [coordTwo]
    have h2 : eAB.symm a = ((⟨a, ha⟩ : ↥A'), 1) := by
      have h1 : eAB ((⟨a, ha⟩ : ↥A'), 1) = a := by
        show (⟨a, ha⟩ : ↥A').1 * (1 : ↥E) = a
        simp
      rw [MulEquiv.symm_apply_eq]; exact h1.symm
    simpa [e, MulEquiv.trans_apply, h2] using key
  · intro b hb
    have key : Multiplicative.toAdd (coordTwo eA eB (1, (⟨b, hb⟩ : ↥B'))) 0 = 0 := by
      simp [coordTwo]
    have h2 : eAB.symm b = (1, (⟨b, hb⟩ : ↥B')) := by
      have h1 : eAB (1, (⟨b, hb⟩ : ↥B')) = b := by
        show (1 : ↥E) * (⟨b, hb⟩ : ↥B').1 = b
        simp
      rw [MulEquiv.symm_apply_eq]; exact h1.symm
    simpa [e, MulEquiv.trans_apply, h2] using key

private lemma matrix_eq_transvection_of_mulVec {F : Type*} [Field F] {M : Matrix (Fin 2) (Fin 2) F}
    {c : F} (h0 : M *ᵥ (Pi.single 0 1 : Fin 2 → F) = Pi.single 0 1)
    (h1 : M *ᵥ (Pi.single 1 1 : Fin 2 → F) =
      Pi.single 1 1 + c • (Pi.single 0 1 : Fin 2 → F)) :
    M = Matrix.transvection (0 : Fin 2) (1 : Fin 2) c := by
  have e00 : M 0 0 = 1 := by
    have := congrFun h0 0
    simpa [Matrix.mulVec_single_one] using this
  have e10 : M 1 0 = 0 := by
    have := congrFun h0 1
    simpa [Matrix.mulVec_single_one] using this
  have e01 : M 0 1 = c := by
    have := congrFun h1 0
    simpa [Matrix.mulVec_single_one] using this
  have e11 : M 1 1 = 1 := by
    have := congrFun h1 1
    simpa [Matrix.mulVec_single_one] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.single, Pi.single_apply, e00, e01, e10, e11]

private theorem elemAutEquivGL_transvection_form {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    {e : ↥E ≃* Multiplicative (Fin 2 → ZMod p)}
    {A' : Subgroup ↥E} {a₀ b₀ : ↥E}
    (ha₀ : a₀ ∈ A')
    (hea₀ : e a₀ = Multiplicative.ofAdd (Pi.single 0 1))
    (heb₀ : e b₀ = Multiplicative.ofAdd (Pi.single 1 1))
    (hAe : ∀ a : ↥E, a ∈ A' → Multiplicative.toAdd (e a) 1 = 0)
    {α : MulAut ↥E}
    (hfixA : ∀ a ∈ A', α a = a)
    (hquot : ∀ x : ↥E, α x * x⁻¹ ∈ A') :
    ∃ c : ZMod p,
      ((CFSG.SectionRank.Ccomm.elemAutEquivGL e α : GL (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) = Matrix.transvection (0 : Fin 2) (1 : Fin 2) c := by
  set M : Matrix (Fin 2) (Fin 2) (ZMod p) :=
    ((CFSG.SectionRank.Ccomm.elemAutEquivGL e α : GL (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p))
  have h0 : M *ᵥ (Pi.single 0 1 : Fin 2 → ZMod p) = Pi.single 0 1 := by
    have h := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e α a₀
    rw [hfixA a₀ ha₀, hea₀] at h
    simpa [M] using h
  have h1 : M *ᵥ (Pi.single 1 1 : Fin 2 → ZMod p) =
      Pi.single 1 1 + (M *ᵥ (Pi.single 1 1)) 0 • (Pi.single 0 1 : Fin 2 → ZMod p) := by
    have h := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e α b₀
    have hw : Multiplicative.toAdd (e (α b₀ * b₀⁻¹)) =
        (Multiplicative.toAdd (e (α b₀ * b₀⁻¹)) 0) • (Pi.single 0 1 : Fin 2 → ZMod p) := by
      funext i
      fin_cases i
      · simp
      · simpa using hAe (α b₀ * b₀⁻¹) (hquot b₀)
    have hsplit : Multiplicative.toAdd (e (α b₀)) =
        Multiplicative.toAdd (e (α b₀ * b₀⁻¹)) + (Pi.single 1 1 : Fin 2 → ZMod p) := by
      conv_lhs => rw [show α b₀ = (α b₀ * b₀⁻¹) * b₀ by group, map_mul, toAdd_mul, heb₀]
      rfl
    rw [heb₀, hsplit, hw] at h
    simp only [toAdd_ofAdd, M] at h ⊢
    rw [h]
    simp
    abel
  exact ⟨(M *ᵥ (Pi.single 1 1)) 0, matrix_eq_transvection_of_mulVec h0 h1⟩

private noncomputable def conjE' {E P : Subgroup G}
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) (p : ↥P) : MulAut ↥E :=
  ((MulAut.conj (p : G)).subgroupMap E).trans
    (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPE p.2)))

private theorem conjE'_coe {E P : Subgroup G}
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) (p : ↥P) (x : ↥E) :
    ((conjE' hPE p x : ↥E) : G) = (p : G) * (x : G) * (p : G)⁻¹ := rfl

private noncomputable def conjHomE {E P : Subgroup G}
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) : ↥P →* MulAut ↥E where
  toFun := conjE' hPE
  map_one' := by
    ext x
    simp [conjE'_coe]
  map_mul' := by
    intro p q
    ext x
    simp only [conjE'_coe, MulAut.mul_apply, Subgroup.coe_mul]
    group

private lemma matrix_eq_transvection10_of_mulVec {F : Type*} [Field F] {M : Matrix (Fin 2) (Fin 2) F}
    {c : F} (h1 : M *ᵥ (Pi.single 1 1 : Fin 2 → F) = Pi.single 1 1)
    (h0 : M *ᵥ (Pi.single 0 1 : Fin 2 → F) =
      Pi.single 0 1 + c • (Pi.single 1 1 : Fin 2 → F)) :
    M = Matrix.transvection (1 : Fin 2) (0 : Fin 2) c := by
  have e00 : M 0 0 = 1 := by
    have := congrFun h0 0
    simpa [Matrix.mulVec_single_one] using this
  have e10 : M 1 0 = c := by
    have := congrFun h0 1
    simpa [Matrix.mulVec_single_one] using this
  have e01 : M 0 1 = 0 := by
    have := congrFun h1 0
    simpa [Matrix.mulVec_single_one] using this
  have e11 : M 1 1 = 1 := by
    have := congrFun h1 1
    simpa [Matrix.mulVec_single_one] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.single, Pi.single_apply, e00, e01, e10, e11]

private theorem elemAutEquivGL_transvection_form' {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    {e : ↥E ≃* Multiplicative (Fin 2 → ZMod p)}
    {B' : Subgroup ↥E} {a₀ b₀ : ↥E}
    (hb₀ : b₀ ∈ B')
    (hea₀ : e a₀ = Multiplicative.ofAdd (Pi.single 0 1))
    (heb₀ : e b₀ = Multiplicative.ofAdd (Pi.single 1 1))
    (hBe : ∀ b : ↥E, b ∈ B' → Multiplicative.toAdd (e b) 0 = 0)
    {α : MulAut ↥E}
    (hfixB : ∀ b ∈ B', α b = b)
    (hquot : ∀ x : ↥E, α x * x⁻¹ ∈ B') :
    ∃ c : ZMod p,
      ((CFSG.SectionRank.Ccomm.elemAutEquivGL e α : GL (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) = Matrix.transvection (1 : Fin 2) (0 : Fin 2) c := by
  set M : Matrix (Fin 2) (Fin 2) (ZMod p) :=
    ((CFSG.SectionRank.Ccomm.elemAutEquivGL e α : GL (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p))
  have h1 : M *ᵥ (Pi.single 1 1 : Fin 2 → ZMod p) = Pi.single 1 1 := by
    have h := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e α b₀
    rw [hfixB b₀ hb₀, heb₀] at h
    simpa [M] using h
  have h0 : M *ᵥ (Pi.single 0 1 : Fin 2 → ZMod p) =
      Pi.single 0 1 + (M *ᵥ (Pi.single 0 1)) 1 • (Pi.single 1 1 : Fin 2 → ZMod p) := by
    have h := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e α a₀
    have hw : Multiplicative.toAdd (e (α a₀ * a₀⁻¹)) =
        (Multiplicative.toAdd (e (α a₀ * a₀⁻¹)) 1) • (Pi.single 1 1 : Fin 2 → ZMod p) := by
      funext i
      fin_cases i
      · simpa using hBe (α a₀ * a₀⁻¹) (hquot a₀)
      · simp
    have hsplit : Multiplicative.toAdd (e (α a₀)) =
        Multiplicative.toAdd (e (α a₀ * a₀⁻¹)) + (Pi.single 0 1 : Fin 2 → ZMod p) := by
      conv_lhs => rw [show α a₀ = (α a₀ * a₀⁻¹) * a₀ by group, map_mul, toAdd_mul, hea₀]
      rfl
    rw [hea₀, hsplit, hw] at h
    simp only [toAdd_ofAdd, M] at h ⊢
    rw [h]
    simp
    abel
  exact ⟨(M *ᵥ (Pi.single 0 1)) 1, matrix_eq_transvection10_of_mulVec h1 h0⟩

private lemma transvection_pow {F : Type*} [Field F] {i j : Fin 2} (hij : i ≠ j) (c : F)
    (n : ℕ) :
    (Matrix.SpecialLinearGroup.transvection hij c) ^ n =
      Matrix.SpecialLinearGroup.transvection hij ((n : F) * c) := by
  induction n with
  | zero => simp [Matrix.SpecialLinearGroup.transvection_coeff_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← Matrix.SpecialLinearGroup.transvection_add]
    congr 1
    push_cast
    ring

private theorem exists_sl2_map {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {E : Subgroup G}
    (hEel : CFSG.Open.IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {A B : Subgroup G} (hAE : A ≤ E) (hBE : B ≤ E)
    (hA : Nat.card A = p) (hB : Nat.card B = p) (hne : A ≠ B)
    {H R Q : Subgroup G} (hHN : H ≤ Subgroup.normalizer (E : Set G))
    (hRH : R ≤ H) (hQH : Q ≤ H) (hsup : R ⊔ Q = H)
    (hRfixA : ∀ r : ↥R, ∀ a : ↥E, a ∈ A.subgroupOf E →
      conjHomE hHN (⟨r, hRH r.2⟩ : ↥H) a = a)
    (hRquot : ∀ r : ↥R, ∀ x : ↥E,
      conjHomE hHN (⟨r, hRH r.2⟩ : ↥H) x * x⁻¹ ∈ A.subgroupOf E)
    (hQfixB : ∀ q : ↥Q, ∀ b : ↥E, b ∈ B.subgroupOf E →
      conjHomE hHN (⟨q, hQH q.2⟩ : ↥H) b = b)
    (hQquot : ∀ q : ↥Q, ∀ x : ↥E,
      conjHomE hHN (⟨q, hQH q.2⟩ : ↥H) x * x⁻¹ ∈ B.subgroupOf E)
    (hRne : ∃ r : ↥R, conjHomE hHN (⟨r, hRH r.2⟩ : ↥H) ≠ 1)
    (hQne : ∃ q : ↥Q, conjHomE hHN (⟨q, hQH q.2⟩ : ↥H) ≠ 1) :
    ∃ φ : ↥H →* SL(2, ZMod p), Function.Surjective φ ∧
      φ.ker = (Subgroup.centralizer (E : Set G)).subgroupOf H := by
  obtain ⟨e, a₀, b₀, ha₀, hb₀, hea₀, heb₀, hAe, hBe⟩ :=
    exists_adapted_coord' hEel hEcard hAE hBE hA hB hne
  let ρ : ↥H →* MulAut ↥E := conjHomE hHN
  let ψ : ↥H →* GL (Fin 2) (ZMod p) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp ρ
  let T : Subgroup (SL(2, ZMod p)) := ψ.range.comap Matrix.SpecialLinearGroup.toGL
  have hupper : ∀ c : ZMod p,
      Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c ∈ T := by
    intro c
    obtain ⟨r₀, hr₀⟩ := hRne
    obtain ⟨c₀, hc₀⟩ := elemAutEquivGL_transvection_form (A' := A.subgroupOf E) ha₀ hea₀ heb₀
      hAe (hfixA := hRfixA r₀) (hquot := hRquot r₀)
    have hc₀ne : c₀ ≠ 0 := by
      intro h0
      apply hr₀
      apply (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective
      apply Units.ext
      rw [hc₀, h0, Matrix.transvection_zero]
      simp
    have hψ₀ : ψ (⟨r₀, hRH r₀.2⟩ : ↥H) =
        Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c₀) := by
      apply Units.ext
      exact hc₀
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ZMod p) * c₀ = c :=
      ⟨(c * c₀⁻¹).val, by rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hc₀ne, mul_one]⟩
    refine ⟨(⟨r₀, hRH r₀.2⟩ : ↥H) ^ k, ?_⟩
    rw [map_pow, hψ₀, ← map_pow, transvection_pow, hk]
  have hlower : ∀ c : ZMod p,
      Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c ∈ T := by
    intro c
    obtain ⟨q₀, hq₀⟩ := hQne
    obtain ⟨c₀, hc₀⟩ := elemAutEquivGL_transvection_form' (B' := B.subgroupOf E) hb₀ hea₀ heb₀
      hBe (hfixB := hQfixB q₀) (hquot := hQquot q₀)
    have hc₀ne : c₀ ≠ 0 := by
      intro h0
      apply hq₀
      apply (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective
      apply Units.ext
      rw [hc₀, h0, Matrix.transvection_zero]
      simp
    have hψ₀ : ψ (⟨q₀, hQH q₀.2⟩ : ↥H) =
        Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c₀) := by
      apply Units.ext
      exact hc₀
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ZMod p) * c₀ = c :=
      ⟨(c * c₀⁻¹).val, by rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hc₀ne, mul_one]⟩
    refine ⟨(⟨q₀, hQH q₀.2⟩ : ↥H) ^ k, ?_⟩
    rw [map_pow, hψ₀, ← map_pow, transvection_pow, hk]
  have hT : T = ⊤ := by
    refine eq_top_iff.2 fun A _ => ?_
    refine Matrix.SL2.transvection_induction (fun g => g ∈ T) ?_ (fun _ _ => T.mul_mem) A
    intro i j hij c
    fin_cases i
    · obtain rfl : j = 1 := by fin_cases j <;> tauto
      exact hupper c
    · obtain rfl : j = 0 := by fin_cases j <;> tauto
      exact hlower c
  have hK : ∀ h : ↥H, ψ h ∈ Matrix.SpecialLinearGroup.toGL.range := by
    have hle : (⊤ : Subgroup ↥H) ≤
        (Matrix.SpecialLinearGroup.toGL : SL(2, ZMod p) →* GL (Fin 2) (ZMod p)).range.comap ψ := by
      have hsup' : R.subgroupOf H ⊔ Q.subgroupOf H = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hRH hQH, hsup, Subgroup.subgroupOf_self]
      rw [← hsup']
      refine sup_le ?_ ?_
      · intro r hr
        obtain ⟨c, hc⟩ := elemAutEquivGL_transvection_form (A' := A.subgroupOf E) ha₀ hea₀ heb₀
          hAe (hfixA := hRfixA ⟨r, hr⟩) (hquot := hRquot ⟨r, hr⟩)
        exact ⟨Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c,
          (by apply Units.ext; exact hc.symm)⟩
      · intro q hq
        obtain ⟨c, hc⟩ := elemAutEquivGL_transvection_form' (B' := B.subgroupOf E) hb₀ hea₀ heb₀
          hBe (hfixB := hQfixB ⟨q, hq⟩) (hquot := hQquot ⟨q, hq⟩)
        exact ⟨Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c,
          (by apply Units.ext; exact hc.symm)⟩
    intro h
    exact hle (Subgroup.mem_top h)
  have hsurj : Matrix.SpecialLinearGroup.toGL.range ≤ ψ.range := by
    intro x hx
    obtain ⟨A, rfl⟩ := hx
    exact (show A ∈ T from by rw [hT]; trivial)
  let eK : SL(2, ZMod p) ≃* Matrix.SpecialLinearGroup.toGL.range :=
    MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective
  let φ₀ : ↥H →* Matrix.SpecialLinearGroup.toGL.range := ψ.codRestrict _ hK
  let φ : ↥H →* SL(2, ZMod p) := eK.symm.toMonoidHom.comp φ₀
  have hρ : ρ.ker = (Subgroup.centralizer (E : Set G)).subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hh x hx
      have h2 : (h : G) * x * (h : G)⁻¹ = x := by
        have h3 := congrArg (fun f : MulAut ↥E => ((f ⟨x, hx⟩ : ↥E) : G)) hh
        change ((conjE' hHN h) ⟨x, hx⟩ : G) = ((1 : MulAut ↥E) ⟨x, hx⟩ : G) at h3
        rw [conjE'_coe] at h3
        simpa using h3
      have h2' : (h : G) * x = x * (h : G) := by
        calc (h : G) * x = (h : G) * x * (h : G)⁻¹ * (h : G) := by group
          _ = x * (h : G) := by rw [h2]
      exact h2'.symm
    · intro hh
      ext x
      change ((conjE' hHN h) x : G) = ((1 : MulAut ↥E) x : G)
      rw [conjE'_coe]
      have hx : (h : G) * x = x * (h : G) := by
        have h := hh x x.2
        rw [eq_comm] at h
        exact h
      rw [hx]
      group
      rfl
  have hKle : ψ.range ≤ Matrix.SpecialLinearGroup.toGL.range := by
    rintro x ⟨h, rfl⟩
    exact hK h
  have hrange : ψ.range = Matrix.SpecialLinearGroup.toGL.range := le_antisymm hKle hsurj
  refine ⟨φ, ?_, ?_⟩
  · intro x
    have hx : Matrix.SpecialLinearGroup.toGL x ∈ ψ.range := by
      rw [hrange]; exact ⟨x, rfl⟩
    obtain ⟨h, hh⟩ := hx
    refine ⟨h, ?_⟩
    show eK.symm (φ₀ h) = x
    rw [show φ₀ h = eK x from Subtype.ext hh, eK.symm_apply_apply]
  · have h1 : φ.ker = φ₀.ker := by
      ext h
      show eK.symm (φ₀ h) = 1 ↔ φ₀ h = 1
      exact eK.symm.map_eq_one_iff
    have h2 : φ₀.ker = ψ.ker := by
      ext h
      simp only [MonoidHom.mem_ker]
      constructor
      · intro hh; exact Subtype.ext_iff.1 hh
      · intro hh; exact Subtype.ext hh
    have h3 : ψ.ker = ρ.ker := by
      ext h
      show (CFSG.SectionRank.Ccomm.elemAutEquivGL e) (ρ h) = 1 ↔ ρ h = 1
      exact (CFSG.SectionRank.Ccomm.elemAutEquivGL e).map_eq_one_iff
    rw [h1, h2, h3, hρ]

private theorem gamma_normalizer_le_of_le_nontrivial {p : ℕ} (hp : p.Prime) {Y K Z : Subgroup G}
    (hΓ : rankThreeGamma 1 p Y ≤ K) (hZY : Z ≤ Y) (hZ : 1 ≤ CFSG.Open.pRank p Z) :
    Subgroup.normalizer (Z : Set G) ≤ K :=
  (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 p Y K).1 hΓ Z hZY hZ

private theorem gamma_le_of_le {p : ℕ} (hp : p.Prime) {Y Y₁ K : Subgroup G}
    (hΓ : rankThreeGamma 1 p Y ≤ K) (hY₁ : Y₁ ≤ Y) :
    rankThreeGamma 1 p Y₁ ≤ K := by
  refine (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 p Y₁ K).2 ?_
  intro Z hZ hZrank
  exact gamma_normalizer_le_of_le_nontrivial hp hΓ (hZ.trans hY₁) hZrank

private theorem gamma_le_uniqueFourConj {p : ℕ} (hp : p.Prime) {Y K : Subgroup G} (g : G)
    (hΓ : rankThreeGamma 1 p Y ≤ K) :
    rankThreeGamma 1 p (uniqueFourConj g Y) ≤ uniqueFourConj g K := by
  refine (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 p (uniqueFourConj g Y)
    (uniqueFourConj g K)).2 ?_
  intro Z hZ hZrank
  have hZ' : uniqueFourConj g⁻¹ Z ≤ Y := by
    have := uniqueFourConj_mono hZ g⁻¹
    rwa [uniqueFourConj_inv_conj] at this
  have hrank' : 1 ≤ CFSG.Open.pRank p (uniqueFourConj g⁻¹ Z) := by
    rw [UC6.pRank_uniqueFourConj p hp Z g⁻¹]
    exact hZrank
  have hN := gamma_normalizer_le_of_le_nontrivial hp hΓ hZ' hrank'
  rw [show Z = uniqueFourConj g (uniqueFourConj g⁻¹ Z) from (uniqueFourConj_conj_inv).symm,
    ← uniqueFourConj_normalizer]
  exact uniqueFourConj_mono hN g

private theorem uniqueMax_conj {M E : Subgroup G} (h : UniqueMax M E) (g : G) :
    UniqueMax (uniqueFourConj g M) (uniqueFourConj g E) := by
  have hMmem : M ∈ calMOf E := by rw [h]; exact Set.mem_singleton M
  ext N
  constructor
  · rintro ⟨hN, hEN⟩
    have hmem : uniqueFourConj g⁻¹ N ∈ calMOf E := by
      refine ⟨UC6.isMaxTwoLocal_conj hN g⁻¹, ?_⟩
      have := uniqueFourConj_mono hEN g⁻¹
      rwa [uniqueFourConj_inv_conj] at this
    rw [h] at hmem
    rw [Set.mem_singleton_iff] at hmem ⊢
    rw [← hmem, uniqueFourConj_conj_inv]
  · rintro rfl
    exact ⟨UC6.isMaxTwoLocal_conj hMmem.1 g, uniqueFourConj_mono hMmem.2 g⟩

private def Has63 (K : Subgroup G) : Prop :=
  ∀ {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {E : Subgroup G} (hE : E ≤ K)
    (hEel : CFSG.Open.IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
    (hΓ : rankThreeGamma 1 r E ≤ K), UniqueMax K E

private theorem has63_conj (D : Data G) (h63 : UC6.R6_3 D) (x : G) :
    Has63 (uniqueFourConj x D.M) := by
  intro r hr hr2 E hE hEel hEcard hΓ
  have hE' : uniqueFourConj x⁻¹ E ≤ D.M := by
    have h := uniqueFourConj_mono hE x⁻¹
    rwa [uniqueFourConj_inv_conj] at h
  have hEel' : CFSG.Open.IsElemAbelian r (uniqueFourConj x⁻¹ E) := by
    have h := IsElemAbelian.map hEel (MulAut.conj x).toMonoidHom
    simpa [uniqueFourConj] using h
  have hEcard' : Nat.card (uniqueFourConj x⁻¹ E) = r ^ 2 := by
    rw [card_uniqueFourConj, hEcard]
  have hΓ' : rankThreeGamma 1 r (uniqueFourConj x⁻¹ E) ≤ D.M := by
    have h := gamma_le_uniqueFourConj hr x⁻¹ hΓ
    rwa [uniqueFourConj_inv_conj] at h
  have h := uniqueMax_conj (h63 r hr hr2 (uniqueFourConj x⁻¹ E) hE' hEel' hEcard' hΓ') x
  rwa [uniqueFourConj_conj_inv] at h

private theorem exists_elemAbelian_sq_of_isPGroup_exp {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (hH : IsPGroup p H) (hexp : ∀ x ∈ H, x ^ p = 1) (hcard : p ^ 2 ≤ Nat.card H) :
    ∃ E : Subgroup G, E ≤ H ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ^ 2 ∣ Nat.card ↥H := by
    obtain ⟨k, hk⟩ := hH.exists_card_eq
    have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 (by rw [← hk]; exact hcard)
    rw [hk]
    exact pow_dvd_pow p hk2
  obtain ⟨K, hKcard, -⟩ := Sylow.exists_subgroup_card_pow_prime_le (G := ↥H) p (n := 0) (m := 2)
    hdvd ⊥ (by simp) (by norm_num)
  refine ⟨K.map H.subtype, Subgroup.map_subtype_le K, ?_, ?_⟩
  · have hKel : CFSG.Open.IsElemAbelian p K := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => ?_⟩
      · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := ↥K) hKcard).is_comm.comm a b
      · apply Subtype.ext
        exact hexp (x : G) ((x : ↥H).2)
    exact hKel.map H.subtype
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hKcard

private theorem inf_centralizer_ne_bot_of_normal {p : ℕ} (hp : p.Prime) {S N : Subgroup G}
    (hS : IsPGroup p S) (hN : N ≤ S) (hNnormal : (N.subgroupOf S).Normal) (hNne : N ≠ ⊥) :
    N ⊓ Subgroup.centralizer (S : Set G) ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hNnormal
  have hN'ne : N.subgroupOf S ≠ ⊥ := by
    intro hb
    rw [Subgroup.subgroupOf_eq_bot] at hb
    rw [disjoint_iff] at hb
    exact hNne (by rw [← inf_eq_left.mpr hN, hb])
  have hcenter : (N.subgroupOf S) ⊓ Subgroup.center ↥S ≠ ⊥ :=
    hS.isNilpotent.inf_center_ne_bot_of_normal hN'ne
  have hmap : ((N.subgroupOf S) ⊓ Subgroup.center ↥S).map S.subtype ≠ ⊥ := by
    intro hb
    have hb' : (N.subgroupOf S) ⊓ Subgroup.center ↥S = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := (N.subgroupOf S) ⊓ Subgroup.center ↥S) S.subtype_injective).1 hb
    exact hcenter hb'
  have hle : ((N.subgroupOf S) ⊓ Subgroup.center ↥S).map S.subtype ≤
      N ⊓ Subgroup.centralizer (S : Set G) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨hy.1, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun s hs => by
      have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hy.2 ⟨s, hs⟩)
      simpa using h2)
  intro hbot
  exact hmap (le_bot_iff.1 (hle.trans (le_of_eq hbot)))

private theorem key_step {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K K' : Subgroup G} (hK : rankThreeIsMaxTwoLocal K) (hK' : rankThreeIsMaxTwoLocal K')
    (hKK' : K ≠ K') (h63K : Has63 K) (h63K' : Has63 K')
    {P₁ : Sylow p G} (hP₁K' : (P₁ : Subgroup G) ≤ K')
    {Y₁ : Subgroup G} (hY₁P₁ : Y₁ ≤ (P₁ : Subgroup G))
    (hY₁norm : (Y₁.subgroupOf (P₁ : Subgroup G)).Normal)
    (hY₁nc : ¬ IsCyclic Y₁) (hY₁exp : ∀ y ∈ Y₁, y ^ p = 1)
    (hΓY₁ : rankThreeGamma 1 p Y₁ ≤ K')
    {X₁ : Subgroup G} (hX₁ne : X₁ ≠ ⊥) (hX₁p : IsPGroup p X₁)
    (hX₁K : X₁ ≤ K) (hX₁K' : X₁ ≤ K') (hNX₁ : normalizer (X₁ : Set G) ≤ K) :
    ∃ c ∈ K', (∀ c' ∈ K', CFSG.Open.pRank p (uniqueFourConj c' Y₁ ⊓ K) ≤ 1) ∧
      X₁ ≤ uniqueFourConj c (P₁ : Subgroup G) ∧
      Nat.card ↥(uniqueFourConj c Y₁ ⊓ centralizer (X₁ : Set G)) = p ∧
      uniqueFourConj c Y₁ ⊓ centralizer (X₁ : Set G) = uniqueFourConj c Y₁ ⊓ K ∧
      uniqueFourConj c Y₁ ⊓ centralizer (X₁ : Set G) ≤
        Subgroup.centralizer (uniqueFourConj c (P₁ : Subgroup G) : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hP₁top : CFSG.ABGLocalTools.IsSylowOf p (P₁ : Subgroup G) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, P₁.isPGroup', by simpa using P₁.not_dvd_index⟩
  have hP₁ : CFSG.ABGLocalTools.IsSylowOf p (P₁ : Subgroup G) K' := hP₁top.of_le hP₁K' le_top
  obtain ⟨k, hkK', hk⟩ := UC6.exists_conj_le_of_isSylowOf hP₁ hX₁K' hX₁p
  have hboundAll : ∀ c ∈ K', CFSG.Open.pRank p (uniqueFourConj c Y₁ ⊓ K) ≤ 1 := by
    intro c hc
    by_contra h
    have h2 : 2 ≤ CFSG.Open.pRank p (uniqueFourConj c Y₁ ⊓ K) := by omega
    obtain ⟨E₁, hE₁le, hE₁el, hE₁card⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (k := 2) h2
    have hE₁Y : E₁ ≤ uniqueFourConj c Y₁ := hE₁le.trans inf_le_left
    have hE₁K : E₁ ≤ K := hE₁le.trans inf_le_right
    have hE₁P : E₁ ≤ uniqueFourConj c (P₁ : Subgroup G) :=
      hE₁Y.trans (uniqueFourConj_mono hY₁P₁ c)
    have hE₁K' : E₁ ≤ K' := by
      have h1 : E₁ ≤ uniqueFourConj c K' := hE₁P.trans (uniqueFourConj_mono hP₁K' c)
      rwa [uniqueFourConj_eq_self_iff (H := K').mpr (Subgroup.le_normalizer hc)] at h1
    have hΓc : rankThreeGamma 1 p (uniqueFourConj c Y₁) ≤ K' := by
      have h1 := gamma_le_uniqueFourConj hp c hΓY₁
      rwa [uniqueFourConj_eq_self_iff (H := K').mpr (Subgroup.le_normalizer hc)] at h1
    have hΓE₁ : rankThreeGamma 1 p E₁ ≤ K' := gamma_le_of_le hp hΓc hE₁Y
    have h63E₁ : UniqueMax K' E₁ := h63K' hp hp2 hE₁K' hE₁el hE₁card hΓE₁
    have hKmem : K ∈ calMOf E₁ := ⟨hK, hE₁K⟩
    rw [h63E₁] at hKmem
    exact hKK' (by simpa using hKmem)
  have hbound : CFSG.Open.pRank p (uniqueFourConj k⁻¹ Y₁ ⊓ K) ≤ 1 := hboundAll k⁻¹ (K'.inv_mem hkK')
  have hY₁ne : Y₁ ≠ ⊥ := fun h => hY₁nc (h ▸ (inferInstance : IsCyclic (⊥ : Subgroup G)))
  have hY₁cne : uniqueFourConj k⁻¹ Y₁ ≠ ⊥ := uniqueFourConj_ne_bot hY₁ne k⁻¹
  have hPp : IsPGroup p (uniqueFourConj k⁻¹ (P₁ : Subgroup G)) :=
    isPGroup_uniqueFourConj P₁.isPGroup' k⁻¹
  have hNnormal : ((uniqueFourConj k⁻¹ Y₁).subgroupOf
      (uniqueFourConj k⁻¹ (P₁ : Subgroup G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (uniqueFourConj_mono hY₁P₁ k⁻¹)]
    calc uniqueFourConj k⁻¹ (P₁ : Subgroup G)
        ≤ uniqueFourConj k⁻¹ (Subgroup.normalizer (Y₁ : Set G)) :=
          uniqueFourConj_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hY₁P₁).1 hY₁norm) k⁻¹
      _ = Subgroup.normalizer (uniqueFourConj k⁻¹ Y₁ : Set G) :=
          uniqueFourConj_normalizer Y₁ k⁻¹
  have hZ₀ne : uniqueFourConj k⁻¹ Y₁ ⊓
      Subgroup.centralizer (uniqueFourConj k⁻¹ (P₁ : Subgroup G) : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot_of_normal hp hPp (uniqueFourConj_mono hY₁P₁ k⁻¹) hNnormal hY₁cne
  set YcK : Subgroup G := uniqueFourConj k⁻¹ Y₁ ⊓ K with hYcKdef
  have hHexp : ∀ x ∈ YcK, x ^ p = 1 := by
    intro x hx
    rw [hYcKdef] at hx
    have hx' : k⁻¹ * x * k ∈ Y₁ := by
      have h := (mem_uniqueFourConj_iff (H := Y₁) (g := k⁻¹)).1 hx.1
      simpa using h
    have e : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    rw [e, conj_pow, hY₁exp (k⁻¹ * x * k) hx']
    simp
  have hHp : IsPGroup p YcK := hPp.to_le (by rw [hYcKdef]; exact inf_le_left.trans (uniqueFourConj_mono hY₁P₁ k⁻¹))
  have hcardbound : Nat.card YcK ≤ p := by
    by_contra hle
    have hcard : p ^ 2 ≤ Nat.card YcK := by
      obtain ⟨n, hn⟩ := hHp.exists_card_eq
      rw [hn] at hle
      have hn2 : 2 ≤ n := by
        by_contra h
        have h1 : n ≤ 1 := by omega
        interval_cases n
        · rw [pow_zero] at hle
          exact hle hp.one_le
        · rw [pow_one] at hle
          exact hle le_rfl
      rw [hn]
      exact Nat.pow_le_pow_right hp.pos hn2
    obtain ⟨E₂, hE₂le, hE₂el, hE₂card⟩ :=
      exists_elemAbelian_sq_of_isPGroup_exp hp hHp hHexp hcard
    have h2 := UC6.le_pRank_of_elemAbelian hp hE₂le hE₂el hE₂card
    omega
  have hX₁P : X₁ ≤ uniqueFourConj k⁻¹ (P₁ : Subgroup G) := by
    intro x hx
    rw [mem_uniqueFourConj_iff]
    simpa using hk x hx
  set B₁ : Subgroup G := uniqueFourConj k⁻¹ Y₁ ⊓ centralizer (X₁ : Set G) with hB₁def
  set Z₀ : Subgroup G := uniqueFourConj k⁻¹ Y₁ ⊓
    Subgroup.centralizer (uniqueFourConj k⁻¹ (P₁ : Subgroup G) : Set G) with hZ₀def
  have hZ₀leB : Z₀ ≤ B₁ := by
    rw [hZ₀def, hB₁def]
    refine inf_le_inf_left _ ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro x hx
    exact hz x (hX₁P hx)
  have hBne : B₁ ≠ ⊥ := fun hbot => hZ₀ne (le_bot_iff.1 (hZ₀leB.trans (le_of_eq hbot)))
  have hBleK : B₁ ≤ YcK := by
    rw [hYcKdef, hB₁def]
    refine inf_le_inf_left _ ?_
    exact (Subgroup.centralizer_le_normalizer _).trans hNX₁
  have hBcard : Nat.card B₁ = p := by
    have h1 : Nat.card B₁ ≤ p := (Subgroup.card_le_of_le hBleK).trans hcardbound
    have h2 : p ≤ Nat.card B₁ := by
      obtain ⟨n, hn⟩ := (hHp.to_le hBleK).exists_card_eq
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hn
        exact hBne (Subgroup.card_eq_one.mp hn)
      rw [hn]
      exact Nat.le_self_pow hn0 p
    exact le_antisymm h1 h2
  have hBeq : B₁ = uniqueFourConj k⁻¹ Y₁ ⊓ K := by
    rw [← hYcKdef]
    exact Subgroup.eq_of_le_of_card_ge hBleK (by rw [hBcard]; exact hcardbound)
  have hZ₀card : Nat.card Z₀ = p := by
    have hdvd : Nat.card Z₀ ∣ Nat.card B₁ := by
      have h1 := Subgroup.card_subgroup_dvd_card (Z₀.subgroupOf B₁)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ₀leB).toEquiv] at h1
    rw [hBcard] at hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
    · exact absurd (Subgroup.card_eq_one.mp h1) hZ₀ne
    · exact hp'
  have hZ₀eqB : Z₀ = B₁ :=
    Subgroup.eq_of_le_of_card_ge hZ₀leB (by rw [hBcard, hZ₀card])
  refine ⟨k⁻¹, K'.inv_mem hkK', hboundAll, hX₁P, hBcard, hBeq, ?_⟩
  change B₁ ≤ Subgroup.centralizer (uniqueFourConj k⁻¹ (P₁ : Subgroup G) : Set G)
  rw [← hZ₀eqB]
  exact inf_le_right

private theorem not_isCyclic_uniqueFourConj {Y : Subgroup G} (h : ¬ IsCyclic Y) (g : G) :
    ¬ IsCyclic (uniqueFourConj g Y) := by
  intro hc
  apply h
  have e : Y ≃* uniqueFourConj g Y :=
    Subgroup.equivMapOfInjective Y (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  exact e.isCyclic.mpr hc

private theorem uniqueFourConj_exp {p : ℕ} {Y : Subgroup G}
    (hexp : ∀ y ∈ Y, y ^ p = 1) (g : G) :
    ∀ y ∈ uniqueFourConj g Y, y ^ p = 1 := by
  intro y hy
  have hy' : g * y * g⁻¹ ∈ Y := (mem_uniqueFourConj_iff).1 hy
  have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
  rw [e]
  rw [show g⁻¹ * (g * y * g⁻¹) * g = (g⁻¹) * (g * y * g⁻¹) * (g⁻¹)⁻¹ by group,
    conj_pow, hexp _ hy']
  simp

private theorem normal_subgroupOf_uniqueFourConj {Y P : Subgroup G} (hYP : Y ≤ P)
    (h : (Y.subgroupOf P).Normal) (g : G) :
    ((uniqueFourConj g Y).subgroupOf (uniqueFourConj g P)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (uniqueFourConj_mono hYP g)]
  calc uniqueFourConj g P ≤ uniqueFourConj g (Subgroup.normalizer (Y : Set G)) :=
        uniqueFourConj_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hYP).1 h) g
    _ = Subgroup.normalizer (uniqueFourConj g Y : Set G) := uniqueFourConj_normalizer Y g

private theorem uniqueFourConj_mul (a b : G) (Y : Subgroup G) :
    uniqueFourConj a (uniqueFourConj b Y) = uniqueFourConj (b * a) Y := by
  ext x
  rw [mem_uniqueFourConj_iff, mem_uniqueFourConj_iff, mem_uniqueFourConj_iff]
  rw [show b * (a * x * a⁻¹) * b⁻¹ = (b * a) * x * (b * a)⁻¹ by group]

private theorem isPGroup_of_exp {p : ℕ} {Y : Subgroup G} (hexp : ∀ y ∈ Y, y ^ p = 1) :
    IsPGroup p Y := fun y => ⟨1, by rw [pow_one]; exact Subtype.ext (hexp y y.2)⟩

private theorem one_le_pRank_of_exp {p : ℕ} (hp : p.Prime) {Y : Subgroup G}
    (hexp : ∀ y ∈ Y, y ^ p = 1) (hYne : Y ≠ ⊥) : 1 ≤ CFSG.Open.pRank p Y := by
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne
  have hdvd : orderOf (y : G) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hexp y y.2)
  have hne : orderOf (y : G) ≠ 1 :=
    fun h1 => hy1 (Subtype.ext (orderOf_eq_one_iff.mp h1))
  have hord : orderOf (y : G) = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf (y : G)) hdvd with h | h
    · exact absurd h hne
    · exact h
  refine UC6.le_pRank_of_elemAbelian hp (Subgroup.zpowers_le.mpr y.2)
    (isElemAbelian_zpowers (hexp y y.2)) ?_
  rw [Nat.card_zpowers, hord, pow_one]

private theorem part1_E {p : ℕ} (hp : p.Prime) {A B : Subgroup G}
    (hA : Nat.card A = p) (hB : Nat.card B = p) (hne : A ≠ B)
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) :
    A ⊓ B = ⊥ ∧ CFSG.Open.IsElemAbelian p (A ⊔ B) ∧ Nat.card ↥(A ⊔ B) = p ^ 2 := by
  have hdisj : A ⊓ B = ⊥ := by
    have hdvd : Nat.card ↥(A ⊓ B) ∣ p := by
      rw [← hA]
      have h1 := Subgroup.card_subgroup_dvd_card ((A ⊓ B).subgroupOf A)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
    rcases hp.eq_one_or_self_of_dvd (Nat.card ↥(A ⊓ B)) hdvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hA])
      have hBA : A ≤ B := by rw [← heq]; exact inf_le_right
      exact hne (Subgroup.eq_of_le_of_card_ge hBA (by rw [hA, hB]))
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 (hAB ha) b hb).symm
  have hel : CFSG.Open.IsElemAbelian p (A ⊔ B) :=
    CFSG.Open.IsElemAbelian.sup_of_commute (isElemAbelian_of_card_prime hp hA)
      (isElemAbelian_of_card_prime hp hB) hcomm
  have hcard : Nat.card ↥(A ⊔ B) = p ^ 2 := by
    have hcomp : (A.subgroupOf (A ⊔ B)).IsComplement' (B.subgroupOf (A ⊔ B)) := by
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · rw [disjoint_iff]
        change A.subgroupOf (A ⊔ B) ⊓ B.subgroupOf (A ⊔ B) = ⊥
        rw [← Subgroup.comap_subtype A (A ⊔ B), ← Subgroup.comap_subtype B (A ⊔ B),
          ← Subgroup.comap_inf, hdisj]
        simp
      · ext x
        constructor
        · intro _; trivial
        · intro _
          obtain ⟨a, ha, b, hb, hab⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm x.2
          exact ⟨⟨a, Subgroup.mem_sup_left ha⟩, ha, ⟨b, Subgroup.mem_sup_right hb⟩, hb, Subtype.ext hab⟩
    have h1 := hcomp.card_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ B)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : B ≤ A ⊔ B)).toEquiv,
      hA, hB] at h1
    rw [← h1]; ring
  exact ⟨hdisj, hel, hcard⟩

private theorem exists_conj_le_of_le_centralizer {p : ℕ} (hp : p.Prime) {B R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf p R ⊤)
    (hRB : R ≤ Subgroup.centralizer (B : Set G))
    {E : Subgroup G} (hE : IsPGroup p E) (hEB : E ≤ Subgroup.centralizer (B : Set G)) :
    ∃ d ∈ Subgroup.centralizer (B : Set G), E ≤ uniqueFourConj d R := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf p R (Subgroup.centralizer (B : Set G)) :=
    hR.of_le hRB le_top
  obtain ⟨k, hk, hkE⟩ := UC6.exists_conj_le_of_isSylowOf hRsyl hEB hE
  refine ⟨k⁻¹, Subgroup.inv_mem _ hk, fun x hx => ?_⟩
  rw [mem_uniqueFourConj_iff]
  simpa [inv_inv] using hkE x hx

private theorem part2_of {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {E A B H R Q : Subgroup G}
    (hEel : CFSG.Open.IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hAE : A ≤ E) (hBE : B ≤ E) (hA : Nat.card A = p) (hB : Nat.card B = p) (hne : A ≠ B)
    (hHN : H ≤ Subgroup.normalizer (E : Set G))
    (hRH : R ≤ H) (hQH : Q ≤ H) (hsup : R ⊔ Q = H)
    (hRfixA : ∀ r ∈ R, ∀ a ∈ A, r * a * r⁻¹ = a)
    (hRquot : ∀ r ∈ R, ∀ x ∈ E, r * x * r⁻¹ * x⁻¹ ∈ A)
    (hQfixB : ∀ q ∈ Q, ∀ b ∈ B, q * b * q⁻¹ = b)
    (hQquot : ∀ q ∈ Q, ∀ x ∈ E, q * x * q⁻¹ * x⁻¹ ∈ B)
    (hRne : ∃ r : ↥R, conjHomE hHN (⟨r, hRH r.2⟩ : ↥H) ≠ 1)
    (hQne : ∃ q : ↥Q, conjHomE hHN (⟨q, hQH q.2⟩ : ↥H) ≠ 1) :
    ∃ φ : ↥H →* SL(2, ZMod p), Function.Surjective φ ∧
      φ.ker = (Subgroup.centralizer (E : Set G)).subgroupOf H := by
  refine exists_sl2_map hp2 hEel hEcard hAE hBE hA hB hne hHN hRH hQH hsup
    ?_ ?_ ?_ ?_ hRne hQne
  · intro r a ha
    apply Subtype.ext
    show r * (a : G) * r⁻¹ = (a : G)
    exact hRfixA r r.2 (a : G) (Subgroup.mem_subgroupOf.mp ha)
  · intro r x
    rw [Subgroup.mem_subgroupOf]
    show r * (x : G) * r⁻¹ * (x : G)⁻¹ ∈ A
    exact hRquot r r.2 x x.2
  · intro q b hb
    apply Subtype.ext
    show q * (b : G) * q⁻¹ = (b : G)
    exact hQfixB q q.2 (b : G) (Subgroup.mem_subgroupOf.mp hb)
  · intro q x
    rw [Subgroup.mem_subgroupOf]
    show q * (x : G) * q⁻¹ * (x : G)⁻¹ ∈ B
    exact hQquot q q.2 x x.2

private theorem exists_mem_normalizer_of_lt_pGroup {p : ℕ} [Fact p.Prime] {H P : Subgroup G}
    (hP : IsPGroup p P) (hHP : H < P) :
    ∃ x ∈ P, x ∉ H ∧ x ∈ Subgroup.normalizer (H : Set G) := by
  set IP : Subgroup P := H.subgroupOf P with hIP
  have hIPlt : IP < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hHP.ne (le_antisymm hHP.le fun x hx => ?_)
    have : (⟨x, hx⟩ : P) ∈ IP := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : IP < Subgroup.normalizer (IP : Set P) :=
    Group.normalizerCondition_of_isNilpotent IP hIPlt
  obtain ⟨x, hxN, hxnot⟩ := SetLike.exists_of_lt hlt
  refine ⟨x, x.2, fun hx => hxnot (Subgroup.mem_subgroupOf.mpr hx), ?_⟩
  have hxsub : x ∈ (Subgroup.normalizer (H : Set G)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hHP.le]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

private theorem inf_normalizer_not_le_of_not_le {p : ℕ} [Fact p.Prime] {P E H : Subgroup G}
    (hP : IsPGroup p P) (hEP : E ≤ P) (hHP : H ≤ P)
    (hHnorm : P ≤ Subgroup.normalizer (H : Set G)) (hHE : ¬ H ≤ E) :
    ¬ H ⊓ Subgroup.normalizer (E : Set G) ≤ E := by
  intro hle
  have hlt : E < E ⊔ H :=
    lt_of_le_of_ne le_sup_left fun h => hHE fun x hx => h.symm ▸ Subgroup.mem_sup_right hx
  obtain ⟨x, hxsup, hxE, hxN⟩ :=
    exists_mem_normalizer_of_lt_pGroup (hP.to_le (sup_le hEP hHP)) hlt
  have hmem : x ∈ (E : Set G) * (H : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right E H (hEP.trans hHnorm)]
    exact hxsup
  obtain ⟨e, he, y, hy, hey⟩ := Set.mem_mul.mp hmem
  have hyN : y ∈ Subgroup.normalizer (E : Set G) := by
    have : y = e⁻¹ * x := by rw [← hey]; group
    rw [this]
    exact (Subgroup.normalizer (E : Set G)).mul_mem
      ((Subgroup.normalizer (E : Set G)).inv_mem (Subgroup.le_normalizer he)) hxN
  exact hxE (hey ▸ E.mul_mem he (hle ⟨hy, hyN⟩))

private theorem mem_centralizer_of_conjHomE_eq_one {E H R : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (E : Set G)) (hRH : R ≤ H) {r : ↥R}
    (h : conjHomE hHN (⟨r, hRH r.2⟩ : ↥H) = 1) :
    (r : G) ∈ Subgroup.centralizer (E : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : conjE' hHN (⟨r, hRH r.2⟩ : ↥H) ⟨x, hx⟩ = ⟨x, hx⟩ := by
    have := congrArg (fun f : MulAut ↥E => f ⟨x, hx⟩) h
    simpa [conjHomE] using this
  have h2 : (r : G) * x * (r : G)⁻¹ = x := by
    have := congrArg (fun y : ↥E => (y : G)) h1
    rwa [conjE'_coe] at this
  calc x * (r : G) = ((r : G) * x * (r : G)⁻¹) * (r : G) := by rw [h2]
    _ = (r : G) * x := by group

private theorem card_le_prime_of_pRank_le_one {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (hHp : IsPGroup p H) (hexp : ∀ x ∈ H, x ^ p = 1) (hrank : CFSG.Open.pRank p H ≤ 1) :
    Nat.card H ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hle
  have hcard : p ^ 2 ≤ Nat.card H := by
    obtain ⟨n, hn⟩ := hHp.exists_card_eq
    rw [hn] at hle
    have hn2 : 2 ≤ n := by
      by_contra h
      have h1 : n ≤ 1 := by omega
      interval_cases n
      · rw [pow_zero] at hle
        exact hle hp.one_le
      · rw [pow_one] at hle
        exact hle le_rfl
    rw [hn]
    exact Nat.pow_le_pow_right hp.pos hn2
  obtain ⟨E, hEH, hEel, hEcard⟩ := exists_elemAbelian_sq_of_isPGroup_exp hp hHp hexp hcard
  have h2 := UC6.le_pRank_of_elemAbelian hp hEH hEel hEcard
  omega

private theorem ne_of_inf_centralizer_eq {p : ℕ} (hp : p.Prime) {Y B A : Subgroup G}
    (hYp : IsPGroup p Y) (hYne : Y ≠ ⊥) (hYnc : ¬ IsCyclic Y)
    (hA : A = Y ⊓ Subgroup.centralizer (B : Set G)) (hAcard : Nat.card A = p)
    (hBcard : Nat.card B = p) : A ≠ B := by
  intro hAB
  haveI : Fact p.Prime := ⟨hp⟩
  have hCB : Y ⊓ Subgroup.centralizer (B : Set G) = B := by rw [← hA, hAB]
  have hBY : B ≤ Y := hCB.symm ▸ inf_le_left
  have hZYne : Y ⊓ Subgroup.centralizer (Y : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot_of_normal hp hYp le_rfl
      (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top) hYne
  have hZYleB : Y ⊓ Subgroup.centralizer (Y : Set G) ≤ B := by
    rw [← hCB]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBY))
  have hZYdvd : Nat.card ↥(Y ⊓ Subgroup.centralizer (Y : Set G)) ∣ p := by
    have h1 := Subgroup.card_subgroup_dvd_card
      ((Y ⊓ Subgroup.centralizer (Y : Set G)).subgroupOf B)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZYleB).toEquiv, hBcard] at h1
  have hZYcard : Nat.card ↥(Y ⊓ Subgroup.centralizer (Y : Set G)) = p := by
    rcases hp.eq_one_or_self_of_dvd _ hZYdvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hZYne
    · exact h1
  have hZYeqB : Y ⊓ Subgroup.centralizer (Y : Set G) = B :=
    Subgroup.eq_of_le_of_card_ge hZYleB (by rw [hBcard, hZYcard])
  have hBleCY : B ≤ Subgroup.centralizer (Y : Set G) := hZYeqB ▸ inf_le_right
  have hYleCB : Y ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.le_centralizer_iff.mpr hBleCY
  have hAY : A = Y := by rw [hA, inf_eq_left.mpr hYleCB]
  exact hYnc (isCyclic_of_prime_card (by rw [← hAY, hAcard]))

theorem r6_10_of_r6_3 (D : Data G) (h63 : UC6.R6_3 D) : UC6.R6_10 D := by
  intro p hp hp2 P Y hYP hYnorm hYnc hYexp hΓ X hXM hXp hNX g hg hXMg
  haveI : Fact p.Prime := ⟨hp⟩
  have hYne : Y ≠ ⊥ := fun h => hYnc (h ▸ (inferInstance : IsCyclic (⊥ : Subgroup G)))
  have hPleM : (P : Subgroup G) ≤ D.M := by
    have hPY : (P : Subgroup G) ≤ Subgroup.normalizer (Y : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYP).1 hYnorm
    have hNY : Subgroup.normalizer (Y : Set G) ≤ rankThreeGamma 1 p Y :=
      CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 p Y Y le_rfl
        (one_le_pRank_of_exp hp hYexp hYne)
    exact hPY.trans (hNY.trans hΓ)
  have hNM : Subgroup.normalizer (D.M : Set G) = D.M := UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal
  have hXne : X ≠ ⊥ := by
    intro h
    have htop : Subgroup.normalizer (X : Set G) = ⊤ := by
      rw [h]
      exact Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)
    exact hg (hNX (by rw [htop]; trivial))
  have h63Mg : Has63 (uniqueFourConj g D.M) := has63_conj D h63 g
  have hMMg : D.M ≠ uniqueFourConj g D.M := by
    intro heq
    exact hg (by rw [← hNM]; exact uniqueFourConj_eq_self_iff.mp heq.symm)
  have h63M : Has63 D.M := by
    intro r hr hr2 E hE hEel hEcard hΓ
    exact h63 r hr hr2 E hE hEel hEcard hΓ
  let Pg : Sylow p G := g⁻¹ • P
  have hPgcoe : (Pg : Subgroup G) = uniqueFourConj g (P : Subgroup G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.sylow_conjugate_eq_map p P g⁻¹
  obtain ⟨c₁, hc₁K', hbnd₁, hc₁P, hBcard₁, hBeq₁, hBcent₁⟩ :=
    key_step hp hp2 D.maxLocal (UC6.isMaxTwoLocal_conj D.maxLocal g) hMMg h63M h63Mg
      (by rw [hPgcoe]; exact uniqueFourConj_mono hPleM g)
      (by rw [hPgcoe]; exact uniqueFourConj_mono hYP g)
      (by rw [hPgcoe]; exact normal_subgroupOf_uniqueFourConj hYP hYnorm g)
      (not_isCyclic_uniqueFourConj hYnc g) (uniqueFourConj_exp hYexp g)
      (gamma_le_uniqueFourConj hp g hΓ) hXne hXp hXM hXMg hNX
  have hbM : g * c₁ * g⁻¹ ∈ D.M := by
    have := hc₁K'
    rw [mem_uniqueFourConj_iff] at this
    simpa [mul_assoc] using this
  have hgc₁ : g * c₁ = (g * c₁ * g⁻¹) * g := by group
  have hYc₁ : uniqueFourConj c₁ (uniqueFourConj g Y) = uniqueFourConj (g * c₁ * g⁻¹ * g) Y := by
    rw [uniqueFourConj_mul, show g * c₁ * g⁻¹ * g = g * c₁ by group]
  have hNMg : Subgroup.normalizer (uniqueFourConj g D.M : Set G) = uniqueFourConj g D.M :=
    UC6.normalizer_eq_of_isMaxTwoLocal (UC6.isMaxTwoLocal_conj D.maxLocal g)
  have hc₁N : c₁ ∈ Subgroup.normalizer (uniqueFourConj g D.M : Set G) := by
    rw [hNMg]; exact hc₁K'
  let Yc : Subgroup G := uniqueFourConj c₁ (uniqueFourConj g Y)
  let B : Subgroup G := Yc ⊓ D.M
  have hBeqX : B = Yc ⊓ Subgroup.centralizer (X : Set G) := hBeq₁.symm
  have hBcard : Nat.card ↥B = p := by rw [hBeqX]; exact hBcard₁
  have hBne : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hBcard
    exact hp.ne_one hBcard.symm
  have hBleYc : B ≤ Yc := inf_le_left
  have hBleM : B ≤ D.M := inf_le_right
  have hYcp : IsPGroup p Yc := isPGroup_of_exp (uniqueFourConj_exp (uniqueFourConj_exp hYexp g) c₁)
  have hBp : IsPGroup p B := hYcp.to_le hBleYc
  have hYcP : Yc ≤ uniqueFourConj c₁ (uniqueFourConj g (P : Subgroup G)) :=
    uniqueFourConj_mono (uniqueFourConj_mono hYP g) c₁
  have hPbgMg : uniqueFourConj (g * c₁) (P : Subgroup G) ≤ uniqueFourConj g D.M := by
    calc uniqueFourConj (g * c₁) P = uniqueFourConj c₁ (uniqueFourConj g P) :=
          (uniqueFourConj_mul c₁ g P).symm
      _ ≤ uniqueFourConj c₁ (uniqueFourConj g D.M) :=
          uniqueFourConj_mono (uniqueFourConj_mono hPleM g) c₁
      _ = uniqueFourConj g D.M := uniqueFourConj_eq_self_iff.mpr hc₁N
  have hc₁PMg : uniqueFourConj c₁ (uniqueFourConj g (P : Subgroup G)) ≤ uniqueFourConj g D.M := by
    rw [uniqueFourConj_mul]; exact hPbgMg
  have hBleMg : B ≤ uniqueFourConj g D.M := hBleYc.trans (hYcP.trans hc₁PMg)
  have hBcent : B ≤ Subgroup.centralizer (uniqueFourConj (g * c₁) (P : Subgroup G) : Set G) := by
    rw [← uniqueFourConj_mul]
    rw [show B = Yc ⊓ Subgroup.centralizer (X : Set G) from hBeq₁.symm]
    exact hBcent₁
  have hΓYc : rankThreeGamma 1 p Yc ≤ uniqueFourConj g D.M := by
    have hΓYg : rankThreeGamma 1 p (uniqueFourConj g Y) ≤ uniqueFourConj g D.M :=
      gamma_le_uniqueFourConj hp g hΓ
    have := gamma_le_uniqueFourConj hp c₁ hΓYg
    rwa [uniqueFourConj_eq_self_iff.mpr hc₁N] at this
  have hBrank : 1 ≤ CFSG.Open.pRank p B :=
    UC6.le_pRank_of_elemAbelian hp le_rfl (isElemAbelian_of_card_prime hp hBcard)
      (by rw [hBcard, pow_one])
  have hNYc : Subgroup.normalizer (B : Set G) ≤ uniqueFourConj g D.M :=
    gamma_normalizer_le_of_le_nontrivial hp hΓYc hBleYc hBrank
  obtain ⟨a, haM, hbnd₂, hBa, hAcard, hAeq, hAcent⟩ :=
    key_step hp hp2 (UC6.isMaxTwoLocal_conj D.maxLocal g) D.maxLocal hMMg.symm h63Mg h63M
      hPleM hYP hYnorm hYnc hYexp hΓ hBne hBp hBleMg hBleM hNYc
  let Ya : Subgroup G := uniqueFourConj a Y
  let A : Subgroup G := Ya ⊓ Subgroup.centralizer (B : Set G)
  have haN : a ∈ Subgroup.normalizer (D.M : Set G) := by rw [hNM]; exact haM
  have hYaM : Ya ≤ D.M := by
    calc Ya ≤ uniqueFourConj a (P : Subgroup G) := uniqueFourConj_mono hYP a
      _ ≤ uniqueFourConj a D.M := uniqueFourConj_mono hPleM a
      _ = D.M := uniqueFourConj_eq_self_iff.mpr haN
  have hYaPa : Ya ≤ uniqueFourConj a (P : Subgroup G) := uniqueFourConj_mono hYP a
  have hPaP : IsPGroup p (uniqueFourConj a (P : Subgroup G)) := isPGroup_uniqueFourConj P.isPGroup' a
  have hYap : IsPGroup p Ya := hPaP.to_le hYaPa
  have hYane : Ya ≠ ⊥ := uniqueFourConj_ne_bot hYne a
  have hYanc : ¬ IsCyclic Ya := not_isCyclic_uniqueFourConj hYnc a
  have hAleYa : A ≤ Ya := inf_le_left
  have hAleCB : A ≤ Subgroup.centralizer (B : Set G) := inf_le_right
  have hAleMg : A ≤ uniqueFourConj g D.M := by
    rw [show A = Ya ⊓ uniqueFourConj g D.M from hAeq]
    exact inf_le_right
  have hAleM : A ≤ D.M := hAleYa.trans hYaM
  have hΓYa : rankThreeGamma 1 p Ya ≤ D.M := by
    have := gamma_le_uniqueFourConj hp a hΓ
    rwa [uniqueFourConj_eq_self_iff.mpr haN] at this
  have hArank : 1 ≤ CFSG.Open.pRank p A :=
    UC6.le_pRank_of_elemAbelian hp le_rfl (isElemAbelian_of_card_prime hp hAcard)
      (by rw [hAcard, pow_one])
  have hNA : Subgroup.normalizer (A : Set G) ≤ D.M :=
    gamma_normalizer_le_of_le_nontrivial hp hΓYa hAleYa hArank
  have hne : A ≠ B := ne_of_inf_centralizer_eq hp hYap hYane hYanc rfl hAcard hBcard
  obtain ⟨hABbot, hEel, hEcard⟩ := part1_E hp hAcard hBcard hne hAleCB
  let E : Subgroup G := A ⊔ B
  have hAleE : A ≤ E := le_sup_left
  have hBleE : B ≤ E := le_sup_right
  have hE_le_Pa : E ≤ uniqueFourConj a (P : Subgroup G) := sup_le (hAleYa.trans hYaPa) hBa
  have hE_le_Mg : E ≤ uniqueFourConj g D.M := sup_le hAleMg hBleMg
  have hE_le_M : E ≤ D.M := sup_le hAleM hBleM
  have hBleCB : B ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr (isElemAbelian_of_card_prime hp hBcard).1
  have hEB : E ≤ Subgroup.centralizer (B : Set G) := sup_le hAleCB hBleCB
  let Pbg : Sylow p G := (g * c₁)⁻¹ • P
  have hPbgcoe : (Pbg : Subgroup G) = uniqueFourConj (g * c₁) (P : Subgroup G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.sylow_conjugate_eq_map p P (g * c₁)⁻¹
  have hRtop : CFSG.ABGLocalTools.IsSylowOf p (Pbg : Subgroup G) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, Pbg.isPGroup', by simpa using Pbg.not_dvd_index⟩
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf p
      (uniqueFourConj (g * c₁) (P : Subgroup G)) ⊤ := hPbgcoe ▸ hRtop
  have hRB : uniqueFourConj (g * c₁) (P : Subgroup G) ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.le_centralizer_iff.mpr hBcent
  have hEp : IsPGroup p E := hPaP.to_le hE_le_Pa
  obtain ⟨d, hdCB, hEd⟩ := exists_conj_le_of_le_centralizer hp hRsyl hRB hEp hEB
  have hdMg : d ∈ uniqueFourConj g D.M := hNYc ((Subgroup.centralizer_le_normalizer _) hdCB)
  have hgdM : g * d * g⁻¹ ∈ D.M := (mem_uniqueFourConj_iff).1 hdMg
  let b' : G := (g * c₁ * g⁻¹) * (g * d * g⁻¹)
  have hb'M : b' ∈ D.M := by
    show (g * c₁ * g⁻¹) * (g * d * g⁻¹) ∈ D.M
    exact D.M.mul_mem hbM hgdM
  have hdNMg : d ∈ Subgroup.normalizer (uniqueFourConj g D.M : Set G) := by
    rw [hNMg]; exact hdMg
  have hconj_b' : ∀ X : Subgroup G,
      uniqueFourConj (b' * g) X = uniqueFourConj d (uniqueFourConj (g * c₁) X) := by
    intro X
    rw [uniqueFourConj_mul]
    congr 1
    show (g * c₁ * g⁻¹) * (g * d * g⁻¹) * g = (g * c₁) * d
    group
  have hBd : uniqueFourConj d B = B :=
    uniqueFourConj_eq_self_iff.mpr ((Subgroup.centralizer_le_normalizer _) hdCB)
  have hBleYc' : B ≤ uniqueFourConj (g * c₁) Y := by
    rw [← uniqueFourConj_mul]; exact hBleYc
  have hBleYb' : B ≤ uniqueFourConj (b' * g) Y := by
    rw [hconj_b' Y]
    calc B = uniqueFourConj d B := hBd.symm
      _ ≤ uniqueFourConj d (uniqueFourConj (g * c₁) Y) := uniqueFourConj_mono hBleYc' d
  have hbnd₁' : CFSG.Open.pRank p (uniqueFourConj (c₁ * d) (uniqueFourConj g Y) ⊓ D.M) ≤ 1 :=
    hbnd₁ (c₁ * d) ((uniqueFourConj g D.M).mul_mem hc₁K' hdMg)
  have hYb'3 : uniqueFourConj (b' * g) Y = uniqueFourConj (c₁ * d) (uniqueFourConj g Y) := by
    rw [hconj_b' Y]
    conv_lhs => rw [uniqueFourConj_mul]
    conv_rhs => rw [uniqueFourConj_mul]
    congr 1
    group
  have hrankYbM : CFSG.Open.pRank p (uniqueFourConj (b' * g) Y ⊓ D.M) ≤ 1 := by
    rw [hYb'3]; exact hbnd₁'
  have hYb'exp : ∀ y ∈ uniqueFourConj (b' * g) Y, y ^ p = 1 :=
    uniqueFourConj_exp hYexp (b' * g)
  have hYb'p : IsPGroup p (uniqueFourConj (b' * g) Y) := isPGroup_of_exp hYb'exp
  have hcardYbM : Nat.card ↥(uniqueFourConj (b' * g) Y ⊓ D.M) ≤ p :=
    card_le_prime_of_pRank_le_one hp (hYb'p.to_le inf_le_left)
      (fun x hx => hYb'exp x hx.1) hrankYbM
  have hYb'M : uniqueFourConj (b' * g) Y ⊓ D.M = B :=
    (Subgroup.eq_of_le_of_card_ge (H := B) (K := uniqueFourConj (b' * g) Y ⊓ D.M)
      (le_inf hBleYb' hBleM) (by rw [hBcard]; exact hcardYbM)).symm
  have hE_Pb'g : E ≤ uniqueFourConj (b' * g) (P : Subgroup G) := by
    rw [hconj_b' P]; exact hEd
  have hPb'gMg : uniqueFourConj (b' * g) (P : Subgroup G) ≤ uniqueFourConj g D.M := by
    rw [hconj_b' P]
    calc uniqueFourConj d (uniqueFourConj (g * c₁) P) ≤ uniqueFourConj d (uniqueFourConj g D.M) :=
          uniqueFourConj_mono hPbgMg d
      _ = uniqueFourConj g D.M := uniqueFourConj_eq_self_iff.mpr hdNMg
  have hYb'Mg : uniqueFourConj (b' * g) Y ≤ uniqueFourConj g D.M :=
    (uniqueFourConj_mono hYP (b' * g)).trans hPb'gMg
  have hΓYc' : rankThreeGamma 1 p (uniqueFourConj (g * c₁) Y) ≤ uniqueFourConj g D.M := by
    rw [← uniqueFourConj_mul]; exact hΓYc
  have hΓYb' : rankThreeGamma 1 p (uniqueFourConj (b' * g) Y) ≤ uniqueFourConj g D.M := by
    rw [hconj_b' Y]
    have := gamma_le_uniqueFourConj hp d hΓYc'
    rwa [uniqueFourConj_eq_self_iff.mpr hdNMg] at this
  have hBcent' : B ≤ Subgroup.centralizer (uniqueFourConj (b' * g) (P : Subgroup G) : Set G) := by
    rw [hconj_b' P]
    exact Subgroup.le_centralizer_iff.mpr (by
      calc uniqueFourConj d (uniqueFourConj (g * c₁) (P : Subgroup G))
          ≤ uniqueFourConj d (Subgroup.centralizer (B : Set G)) :=
            uniqueFourConj_mono (Subgroup.le_centralizer_iff.mpr hBcent) d
        _ = Subgroup.centralizer (B : Set G) :=
            uniqueFourConj_eq_self_iff.mpr (Subgroup.le_normalizer hdCB))
  let R : Subgroup G := Ya ⊓ Subgroup.normalizer (E : Set G)
  let Q : Subgroup G := uniqueFourConj (b' * g) Y ⊓ Subgroup.normalizer (E : Set G)
  let H : Subgroup G := R ⊔ Q
  have hRH : R ≤ H := le_sup_left
  have hQH : Q ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (E : Set G) := sup_le inf_le_right inf_le_right
  have hPaN : uniqueFourConj a (P : Subgroup G) ≤ Subgroup.normalizer (Ya : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYaPa).mp
      (normal_subgroupOf_uniqueFourConj hYP hYnorm a)
  have hPa'bN : uniqueFourConj (b' * g) (P : Subgroup G) ≤
      Subgroup.normalizer (uniqueFourConj (b' * g) Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (uniqueFourConj_mono hYP (b' * g))).mp
      (normal_subgroupOf_uniqueFourConj hYP hYnorm (b' * g))
  have hYanotleE : ¬ Ya ≤ E := by
    intro hYE
    have hYaMg : Ya ≤ uniqueFourConj g D.M := hYE.trans hE_le_Mg
    have hAYa : A = Ya := by
      rw [show A = Ya ⊓ uniqueFourConj g D.M from hAeq, inf_eq_left.mpr hYaMg]
    exact hYanc (isCyclic_of_prime_card (p := p) (by rw [← hAYa]; exact hAcard))
  have hRnotleE : ¬ R ≤ E :=
    inf_normalizer_not_le_of_not_le hPaP hE_le_Pa hYaPa hPaN hYanotleE
  have hYb'notleE : ¬ uniqueFourConj (b' * g) Y ≤ E := by
    intro hYE
    have hYb'M' : uniqueFourConj (b' * g) Y ≤ D.M := hYE.trans hE_le_M
    have hBeq : B = uniqueFourConj (b' * g) Y := by rw [hYb'M.symm, inf_eq_left.mpr hYb'M']
    exact not_isCyclic_uniqueFourConj hYnc (b' * g)
      (isCyclic_of_prime_card (p := p) (by rw [← hBeq]; exact hBcard))
  have hQnotleE : ¬ Q ≤ E :=
    inf_normalizer_not_le_of_not_le (isPGroup_uniqueFourConj P.isPGroup' (b' * g))
      hE_Pb'g (uniqueFourConj_mono hYP (b' * g)) hPa'bN hYb'notleE
  have hRfixA : ∀ r ∈ R, ∀ b ∈ A, r * b * r⁻¹ = b := by
    intro r hr b hb
    have hrPa : r ∈ uniqueFourConj a (P : Subgroup G) := (inf_le_left.trans hYaPa) hr
    have hcomm := Subgroup.mem_centralizer_iff.mp (hAcent hb) r hrPa
    rw [hcomm]; group
  have hRquot : ∀ r ∈ R, ∀ x ∈ E, r * x * r⁻¹ * x⁻¹ ∈ A := by
    intro r hr x hx
    have hrN : r ∈ Subgroup.normalizer (E : Set G) :=
      (inf_le_right : R ≤ Subgroup.normalizer (E : Set G)) hr
    have hrYa : r ∈ Ya := (inf_le_left : R ≤ Ya) hr
    have hxPa : x ∈ uniqueFourConj a (P : Subgroup G) := hE_le_Pa hx
    have hYaE : Ya ⊓ E = A := by
      apply le_antisymm
      · intro z hz
        rw [show A = Ya ⊓ uniqueFourConj g D.M from hAeq]
        exact ⟨hz.1, hE_le_Mg hz.2⟩
      · exact le_inf hAleYa hAleE
    have hxrYa : x * r⁻¹ * x⁻¹ ∈ Ya :=
      (Subgroup.mem_normalizer_iff.mp (hPaN hxPa) r⁻¹).1 (Ya.inv_mem hrYa)
    have h1 : r * x * r⁻¹ * x⁻¹ ∈ Ya := by
      have := Ya.mul_mem hrYa hxrYa
      simpa only [mul_assoc] using this
    have h2 : r * x * r⁻¹ * x⁻¹ ∈ E := by
      have h3 : r * x * r⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hrN x).1 hx
      exact E.mul_mem h3 (E.inv_mem hx)
    exact hYaE ▸ ⟨h1, h2⟩
  have hBleQE : B ≤ Subgroup.normalizer (E : Set G) :=
    (hBcent'.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hE_Pb'g))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hBleQ : B ≤ Q := le_inf hBleYb' hBleQE
  have hQfixB : ∀ q ∈ Q, ∀ b ∈ B, q * b * q⁻¹ = b := by
    intro q hq b hb
    have hqPb'g : q ∈ uniqueFourConj (b' * g) (P : Subgroup G) :=
      (inf_le_left.trans (uniqueFourConj_mono hYP (b' * g))) hq
    have hcomm := Subgroup.mem_centralizer_iff.mp (hBcent' hb) q hqPb'g
    rw [hcomm]; group
  have hQquot : ∀ q ∈ Q, ∀ x ∈ E, q * x * q⁻¹ * x⁻¹ ∈ B := by
    intro q hq x hx
    have hqN : q ∈ Subgroup.normalizer (E : Set G) :=
      (inf_le_right : Q ≤ Subgroup.normalizer (E : Set G)) hq
    have hqYb' : q ∈ uniqueFourConj (b' * g) Y :=
      (inf_le_left : Q ≤ uniqueFourConj (b' * g) Y) hq
    have hxPb'g : x ∈ uniqueFourConj (b' * g) (P : Subgroup G) := hE_Pb'g hx
    have hYb'E : uniqueFourConj (b' * g) Y ⊓ E = B := by
      apply le_antisymm
      · intro z hz
        rw [show B = uniqueFourConj (b' * g) Y ⊓ D.M from hYb'M.symm]
        exact ⟨hz.1, hE_le_M hz.2⟩
      · exact le_inf hBleYb' hBleE
    have hxqYb' : x * q⁻¹ * x⁻¹ ∈ uniqueFourConj (b' * g) Y :=
      (Subgroup.mem_normalizer_iff.mp (hPa'bN hxPb'g) q⁻¹).1
        ((uniqueFourConj (b' * g) Y).inv_mem hqYb')
    have h1 : q * x * q⁻¹ * x⁻¹ ∈ uniqueFourConj (b' * g) Y := by
      have := (uniqueFourConj (b' * g) Y).mul_mem hqYb' hxqYb'
      simpa only [mul_assoc] using this
    have h2 : q * x * q⁻¹ * x⁻¹ ∈ E := by
      have h3 : q * x * q⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hqN x).1 hx
      exact E.mul_mem h3 (E.inv_mem hx)
    exact hYb'E ▸ ⟨h1, h2⟩
  have hRnotleCE : ¬ R ≤ Subgroup.centralizer (E : Set G) := by
    intro hRc
    apply hRnotleE
    calc R ≤ A := le_inf inf_le_left
          (hRc.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBleE)))
      _ ≤ E := hAleE
  have hQnotleCE : ¬ Q ≤ Subgroup.centralizer (E : Set G) := by
    intro hQc
    apply hQnotleE
    calc Q ≤ uniqueFourConj (b' * g) Y ⊓ D.M :=
          le_inf inf_le_left
            ((hQc.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAleE))).trans
              ((Subgroup.centralizer_le_normalizer _).trans hNA))
      _ = B := hYb'M
      _ ≤ E := hBleE
  have hRne : ∃ r : ↥R, conjHomE hHN (⟨r, hRH r.2⟩ : ↥H) ≠ 1 := by
    by_contra h
    push Not at h
    exact hRnotleCE fun r hr => mem_centralizer_of_conjHomE_eq_one hHN hRH (h ⟨r, hr⟩)
  have hQne : ∃ q : ↥Q, conjHomE hHN (⟨q, hQH q.2⟩ : ↥H) ≠ 1 := by
    by_contra h
    push Not at h
    exact hQnotleCE fun q hq => mem_centralizer_of_conjHomE_eq_one hHN hQH (h ⟨q, hq⟩)
  obtain ⟨φ, hφsurj, hφker⟩ :=
    part2_of hp2 hEel hEcard hAleE hBleE hAcard hBcard hne hHN hRH hQH rfl
      hRfixA hRquot hQfixB hQquot hRne hQne
  have hRA : ⁅R, E⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro r hr x hx
    exact hRquot r hr x hx
  have hQB : ⁅Q, E⁆ ≤ B := by
    rw [Subgroup.commutator_le]
    intro q hq x hx
    exact hQquot q hq x hx
  have hRexp : ∀ x ∈ R, x ^ p = 1 := fun x hx =>
    uniqueFourConj_exp hYexp a x ((inf_le_left : R ≤ Ya) hx)
  have hRp : IsPGroup p R := hPaP.to_le (inf_le_left.trans hYaPa)
  have hQexp : ∀ x ∈ Q, x ^ p = 1 := fun x hx =>
    uniqueFourConj_exp hYexp (b' * g) x
      ((inf_le_left : Q ≤ uniqueFourConj (b' * g) Y) hx)
  have hQp : IsPGroup p Q :=
    (isPGroup_uniqueFourConj P.isPGroup' (b' * g)).to_le
      (inf_le_left.trans (uniqueFourConj_mono hYP (b' * g)))
  have hAleR : A ≤ R := le_inf hAleYa (hAleE.trans (Subgroup.le_normalizer : E ≤ _))
  have hRneA : R ≠ A := fun h => hRnotleE (h ▸ hAleE)
  have hRltA : A < R := lt_of_le_of_ne hAleR (fun h => hRneA h.symm)
  have hRcard2 : p ^ 2 ≤ Nat.card R := by
    have hlt : Nat.card A < Nat.card R := Subgroup.card_lt_of_lt hRltA
    rw [hAcard] at hlt
    obtain ⟨n, hn⟩ := hRp.exists_card_eq
    rw [hn] at hlt
    have hn2 : 2 ≤ n := by
      by_contra h
      have h1 : n ≤ 1 := by omega
      interval_cases n
      · rw [pow_zero] at hlt
        exact absurd hlt (not_lt.mpr hp.one_le)
      · rw [pow_one] at hlt
        exact absurd hlt (lt_irrefl p)
    rw [hn]
    exact Nat.pow_le_pow_right hp.pos hn2
  have hRloc : ∀ L : Subgroup G, IsTwoLocal L → R ≤ L → L ≤ D.M := by
    intro L hL hRL
    obtain ⟨E₁, hE₁R, hE₁el, hE₁card⟩ :=
      exists_elemAbelian_sq_of_isPGroup_exp hp hRp hRexp hRcard2
    have hE₁Ya : E₁ ≤ Ya := hE₁R.trans inf_le_left
    have hE₁M : E₁ ≤ D.M := hE₁Ya.trans hYaM
    have hΓE₁ : rankThreeGamma 1 p E₁ ≤ D.M := gamma_le_of_le hp hΓYa hE₁Ya
    have h63E₁ : UniqueMax D.M E₁ := h63 p hp hp2 E₁ hE₁M hE₁el hE₁card hΓE₁
    obtain ⟨N, hNmax, hNL⟩ := UC6.exists_rankThreeIsMaxTwoLocal_ge_uc6 hL
    have hNE₁ : N ∈ calMOf E₁ := ⟨hNmax, hE₁R.trans (hRL.trans hNL)⟩
    rw [h63E₁, Set.mem_singleton_iff] at hNE₁
    exact hNL.trans (le_of_eq hNE₁)
  have hBltQ : B < Q :=
    lt_of_le_of_ne hBleQ fun h => hQnotleE (h ▸ hBleE)
  have hQcard2 : p ^ 2 ≤ Nat.card Q := by
    have hlt : Nat.card B < Nat.card Q := Subgroup.card_lt_of_lt hBltQ
    rw [hBcard] at hlt
    obtain ⟨n, hn⟩ := hQp.exists_card_eq
    rw [hn] at hlt
    have hn2 : 2 ≤ n := by
      by_contra h
      have h1 : n ≤ 1 := by omega
      interval_cases n
      · rw [pow_zero] at hlt
        exact absurd hlt (not_lt.mpr hp.one_le)
      · rw [pow_one] at hlt
        exact absurd hlt (lt_irrefl p)
    rw [hn]
    exact Nat.pow_le_pow_right hp.pos hn2
  have hQloc : ∀ L : Subgroup G, IsTwoLocal L → Q ≤ L → L ≤ uniqueFourConj g D.M := by
    intro L hL hQL
    obtain ⟨E₁, hE₁Q, hE₁el, hE₁card⟩ :=
      exists_elemAbelian_sq_of_isPGroup_exp hp hQp hQexp hQcard2
    have hE₁Yb' : E₁ ≤ uniqueFourConj (b' * g) Y := hE₁Q.trans inf_le_left
    have hE₁Mg : E₁ ≤ uniqueFourConj g D.M := hE₁Yb'.trans hYb'Mg
    have hΓE₁ : rankThreeGamma 1 p E₁ ≤ uniqueFourConj g D.M := gamma_le_of_le hp hΓYb' hE₁Yb'
    have h63E₁ : UniqueMax (uniqueFourConj g D.M) E₁ :=
      h63Mg hp hp2 hE₁Mg hE₁el hE₁card hΓE₁
    obtain ⟨N, hNmax, hNL⟩ := UC6.exists_rankThreeIsMaxTwoLocal_ge_uc6 hL
    have hNE₁ : N ∈ calMOf E₁ := ⟨hNmax, hE₁Q.trans (hQL.trans hNL)⟩
    rw [h63E₁, Set.mem_singleton_iff] at hNE₁
    exact hNL.trans (le_of_eq hNE₁)
  have hQM : Q ⊓ D.M ≤ Subgroup.centralizer (E : Set G) := by
    calc Q ⊓ D.M ≤ uniqueFourConj (b' * g) Y ⊓ D.M := inf_le_inf inf_le_left le_rfl
      _ = B := hYb'M
      _ ≤ E := hBleE
      _ ≤ Subgroup.centralizer (E : Set G) :=
          Subgroup.le_centralizer_iff_isMulCommutative.mpr hEel.1
  refine ⟨?_, ?_⟩
  · refine ⟨a, haM, b', hb'M, A, B, E, hAcard, hBcard, hAleYa, hBleYb', hEel, hEcard, rfl, ?_,
      φ, hφsurj, hφker⟩
    rw [← hAeq, hYb'M, show E = A ⊔ B from rfl]
  · intro V hV hVg
    exact r6_10_part3 D hp (g := g) hEel hEcard hAcard hBcard hAleE hBleE hne
      hRp hQp inf_le_right inf_le_right hRA hQB hRnotleCE hQnotleCE
      hRloc hQloc hNA hQM hV hVg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
