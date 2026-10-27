module

public import CFSG.Milestones.ASVolI.F429.C6Sp4
public import CFSG.Quasithin.H13.U4ParOuter
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Gen
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitAut

public section

namespace CFSG.ASVolI

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.Sec53F.Unit

section Q2Mat

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

@[expose] noncomputable def burnsideF429_q2Mat (α β δ : K) : Matrix Ix Ix K :=
  1 + single ie1 if1 α + single ie1 if2 β + single ie2 if1 (h.bar β) + single ie2 if2 δ

theorem burnsideF429_q2Mat_apply (α β δ : K) (i j : Ix) :
    burnsideF429_q2Mat h α β δ i j = (1 : Matrix Ix Ix K) i j +
      (if ie1 = i ∧ if1 = j then α else 0) + (if ie1 = i ∧ if2 = j then β else 0) +
      (if ie2 = i ∧ if1 = j then h.bar β else 0) + (if ie2 = i ∧ if2 = j then δ else 0) := by
  simp only [burnsideF429_q2Mat, Matrix.add_apply, Matrix.single_apply]

theorem burnsideF429_U4_q2_sq {q : hypSU h 2 0} (hq : q ∈ radQ2 h) : q * q = 1 := by
  have := h.charP
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hq
  apply hypSU_ext h
  rw [coe_mul_hypSU]
  ext i j
  rw [mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, one_apply, CharTwo.add_self_eq_zero]

theorem burnsideF429_U4_q2_herm {q : hypSU h 2 0} (hq : q ∈ radQ2 h) :
    h.bar (((q : GL Ix K) : Matrix Ix Ix K) ie1 if1) = ((q : GL Ix K) : Matrix Ix Ix K) ie1 if1 ∧
      h.bar (((q : GL Ix K) : Matrix Ix Ix K) ie2 if2) =
        ((q : GL Ix K) : Matrix Ix Ix K) ie2 if2 ∧
      ((q : GL Ix K) : Matrix Ix Ix K) ie2 if1 = h.bar (((q : GL Ix K) : Matrix Ix Ix K) ie1 if2) := by
  have hinv : q⁻¹ = q := inv_eq_of_mul_eq_one_right (burnsideF429_U4_q2_sq h hq)
  have e : ∀ a b, ((q : GL Ix K) : Matrix Ix Ix K) a b =
      h.bar (((q : GL Ix K) : Matrix Ix Ix K) (hypPartner b) (hypPartner a)) := by
    intro a b
    have := inv_apply h q a b
    rwa [hinv] at this
  refine ⟨(e ie1 if1).symm, (e ie2 if2).symm, e ie2 if1⟩

theorem burnsideF429_q2_eq {q : hypSU h 2 0} (hq : q ∈ radQ2 h) :
    ((q : GL Ix K) : Matrix Ix Ix K) = burnsideF429_q2Mat h (((q : GL Ix K) : Matrix Ix Ix K) ie1 if1)
      (((q : GL Ix K) : Matrix Ix Ix K) ie1 if2) (((q : GL Ix K) : Matrix Ix Ix K) ie2 if2) := by
  obtain ⟨-, -, h21⟩ := burnsideF429_U4_q2_herm h hq
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hq
  ext i j
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [burnsideF429_q2Mat_apply, one_apply, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
      h21]

theorem burnsideF429_q2_ext {q q' : hypSU h 2 0} (hq : q ∈ radQ2 h) (hq' : q' ∈ radQ2 h)
    (h11 : ((q : GL Ix K) : Matrix Ix Ix K) ie1 if1 = ((q' : GL Ix K) : Matrix Ix Ix K) ie1 if1)
    (h12 : ((q : GL Ix K) : Matrix Ix Ix K) ie1 if2 = ((q' : GL Ix K) : Matrix Ix Ix K) ie1 if2)
    (h22 : ((q : GL Ix K) : Matrix Ix Ix K) ie2 if2 = ((q' : GL Ix K) : Matrix Ix Ix K) ie2 if2) :
    q = q' := by
  apply hypSU_ext h
  rw [burnsideF429_q2_eq h hq, burnsideF429_q2_eq h hq', h11, h12, h22]

theorem burnsideF429_U4_isElemAbelian_q2 : CFSG.Open.IsElemAbelian 2 (radQ2 h) := by
  refine ⟨isMulCommutative_iff_of_setLike.mpr fun a ha b hb => radQ2_comm h ha hb, fun x hx => ?_⟩
  rw [pow_two]
  exact burnsideF429_U4_q2_sq h hx

theorem burnsideF429_U4_q2_le_U : radQ2 h ≤ hypUnitriangular h 2 0 := by
  intro q hq
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hq
  refine mem_hypUnitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
  · rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
      simp_all [fullPos_ie1, fullPos_ie2, fullPos_if1, fullPos_if2]
  · rcases ix_cases i with rfl | rfl | rfl | rfl <;> assumption

theorem burnsideF429_U4_conj_q2 (g : hypSU h 2 0) {q : hypSU h 2 0} (hq : q ∈ radQ2 h) {a b : Ix}
    (hab : a ≠ b) :
    (((g * q * g⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) a b =
      ((g : GL Ix K) : Matrix Ix Ix K) a ie1 * ((q : GL Ix K) : Matrix Ix Ix K) ie1 if1 *
          h.bar (((g : GL Ix K) : Matrix Ix Ix K) (hypPartner b) ie1) +
        ((g : GL Ix K) : Matrix Ix Ix K) a ie1 * ((q : GL Ix K) : Matrix Ix Ix K) ie1 if2 *
          h.bar (((g : GL Ix K) : Matrix Ix Ix K) (hypPartner b) ie2) +
        ((g : GL Ix K) : Matrix Ix Ix K) a ie2 * h.bar (((q : GL Ix K) : Matrix Ix Ix K) ie1 if2) *
          h.bar (((g : GL Ix K) : Matrix Ix Ix K) (hypPartner b) ie1) +
        ((g : GL Ix K) : Matrix Ix Ix K) a ie2 * ((q : GL Ix K) : Matrix Ix Ix K) ie2 if2 *
          h.bar (((g : GL Ix K) : Matrix Ix Ix K) (hypPartner b) ie2) := by
  set N : Matrix Ix Ix K :=
    single ie1 if1 (((q : GL Ix K) : Matrix Ix Ix K) ie1 if1) +
      single ie1 if2 (((q : GL Ix K) : Matrix Ix Ix K) ie1 if2) +
      single ie2 if1 (h.bar (((q : GL Ix K) : Matrix Ix Ix K) ie1 if2)) +
      single ie2 if2 (((q : GL Ix K) : Matrix Ix Ix K) ie2 if2) with hN
  have hq' : ((q : GL Ix K) : Matrix Ix Ix K) = 1 + N := by
    rw [hN, ← add_assoc, ← add_assoc, ← add_assoc]
    exact burnsideF429_q2_eq h hq
  have hgg : ((g : GL Ix K) : Matrix Ix Ix K) * (((g⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      1 := by
    rw [← coe_mul_hypSU, mul_inv_cancel]
    rfl
  have e : (((g * q * g⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      1 + ((g : GL Ix K) : Matrix Ix Ix K) * N *
        (((g⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) := by
    rw [coe_mul_hypSU, coe_mul_hypSU, hq', Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hgg]
  rw [e, Matrix.add_apply, one_apply_ne hab, zero_add, mul_apply, sum_ix]
  simp only [mul_apply, sum_ix, hN, Matrix.add_apply, Matrix.single_apply, inv_apply h g]
  rcases ix_cases b with rfl | rfl | rfl | rfl <;>
    simp [ie1, ie2, if1, if2, hypPartner] <;> ring

theorem burnsideF429_U4_fieldAut_mem_q2 (σ : K ≃+* K) {q : hypSU h 2 0} (hq : q ∈ radQ2 h) :
    fieldAut h σ q ∈ radQ2 h := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hq
  show IsQ2Mat (((fieldHom h σ q : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K)
  rw [mat_fieldHom]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.map_apply, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]

theorem burnsideF429_U4_fieldAut_apply (σ : K ≃+* K) (g : hypSU h 2 0) (a b : Ix) :
    (((fieldAut h σ g : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) a b =
      σ (((g : GL Ix K) : Matrix Ix Ix K) a b) := by
  show (((fieldHom h σ g : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) a b = _
  rw [mat_fieldHom]
  rfl

end Q2Mat

section Counting

variable {F : Type} [Field F] [Finite F]

theorem burnsideF429_card_le_mixed (σ₁ σ₂ σ₃ : F ≃+* F) {l₁ l₂ l₃ : F} (hl₁ : l₁ ≠ 0)
    (hl₂ : l₂ ≠ 0) (hl₃ : l₃ ≠ 0) (β₁ : F → F) (β₂ : F × F → F) (S : Set ((F × F) × F))
    (hS : ∀ p ∈ S, l₁ * σ₁ p.1.1 = p.1.1 ∧ l₂ * σ₂ p.1.2 + β₁ p.1.1 = p.1.2 ∧
      l₃ * σ₃ p.2 + β₂ p.1 = p.2) :
    Nat.card S ≤ Nat.card {a : F // σ₁ a = a} * Nat.card {a : F // σ₂ a = a} *
      Nat.card {a : F // σ₃ a = a} := by
  have h1 := burnsideF429_card_fiber_le σ₃ hl₃ β₂ S fun p hp => (hS p hp).2.2
  have h2 := burnsideF429_card_fiber_le σ₂ hl₂ β₁ (Prod.fst '' S) (by
    rintro _ ⟨p, hp, rfl⟩
    exact (hS p hp).2.1)
  have h3 := burnsideF429_card_twisted_le σ₁ hl₁ (Prod.fst '' (Prod.fst '' S)) (by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact (hS p hp).1)
  calc Nat.card S ≤ Nat.card (Prod.fst '' S) * Nat.card {a : F // σ₃ a = a} := h1
    _ ≤ (Nat.card (Prod.fst '' (Prod.fst '' S)) * Nat.card {a : F // σ₂ a = a}) *
          Nat.card {a : F // σ₃ a = a} := Nat.mul_le_mul_right _ h2
    _ ≤ (Nat.card {a : F // σ₁ a = a} * Nat.card {a : F // σ₂ a = a}) *
          Nat.card {a : F // σ₃ a = a} :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)

end Counting

section FixQ2

variable {m : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 m K)

theorem burnsideF429_U4_card_fix_q2 (g : hypSU h 2 0)
    (hg21 : ((g : GL Ix K) : Matrix Ix Ix K) ie2 ie1 = 0)
    (hg11 : ((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1 ≠ 0)
    (hg22 : ((g : GL Ix K) : Matrix Ix Ix K) ie2 ie2 ≠ 0) (σ : K ≃+* K)
    {X : Subgroup (hypSU h 2 0)} (hX : X ≤ radQ2 h)
    (hfix : ∀ x ∈ X, g * fieldAut h σ x * g⁻¹ = x) :
    Nat.card X ≤ Nat.card {a : K // barEquiv h a = a} * Nat.card {a : K // σ a = a} *
      Nat.card {a : K // barEquiv h a = a} := by
  let co : hypSU h 2 0 → (K × K) × K := fun x =>
    ((((x : GL Ix K) : Matrix Ix Ix K) ie2 if2, ((x : GL Ix K) : Matrix Ix Ix K) ie1 if2),
      ((x : GL Ix K) : Matrix Ix Ix K) ie1 if1)
  let S : Set ((K × K) × K) := co '' (X : Set (hypSU h 2 0))
  have hinj : Set.InjOn co (X : Set (hypSU h 2 0)) := by
    intro x hx y hy hxy
    simp only [co, Prod.mk.injEq] at hxy
    exact burnsideF429_q2_ext h (hX hx) (hX hy) hxy.2 hxy.1.2 hxy.1.1
  have hcard : Nat.card X = Nat.card S := (Nat.card_image_of_injOn hinj).symm
  rw [hcard]
  have hbar : ∀ c, barEquiv h c = h.bar c := barEquiv_apply h
  have hl : ((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1 *
      h.bar (((g : GL Ix K) : Matrix Ix Ix K) ie2 ie2) ≠ 0 :=
    mul_ne_zero hg11 (fun h0 => hg22 ((map_eq_zero_iff h.bar h.bar.injective).mp h0))
  refine burnsideF429_card_le_mixed (barEquiv h) σ (barEquiv h) one_ne_zero hl one_ne_zero
    (fun d => ((g : GL Ix K) : Matrix Ix Ix K) ie1 ie2 * σ d *
      h.bar (((g : GL Ix K) : Matrix Ix Ix K) ie2 ie2)) (fun _ => 0) S ?_
  rintro _ ⟨x, hx, rfl⟩
  have hxq := hX hx
  have hσq := burnsideF429_U4_fieldAut_mem_q2 h σ hxq
  obtain ⟨hx11, hx22, -⟩ := burnsideF429_U4_q2_herm h hxq
  have hfx := hfix x hx
  have e12 := burnsideF429_U4_conj_q2 h g hσq (a := ie1) (b := if2) (by simp)
  rw [hfx] at e12
  simp only [hypPartner_if2, hg21, map_zero, mul_zero, zero_add, burnsideF429_U4_fieldAut_apply,
    add_zero] at e12
  refine ⟨?_, ?_, ?_⟩
  · simp only [co, one_mul, hbar]
    exact hx22
  · simp only [co]
    linear_combination -e12
  · simp only [co, one_mul, add_zero, hbar]
    exact hx11

end FixQ2

section UGroup

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem burnsideF429_U4_U_entries {u : hypSU h 2 0} (hu : u ∈ hypUnitriangular h 2 0) :
    ((u : GL Ix K) : Matrix Ix Ix K) ie1 ie1 = 1 ∧ ((u : GL Ix K) : Matrix Ix Ix K) ie2 ie2 = 1 ∧
      ((u : GL Ix K) : Matrix Ix Ix K) ie2 ie1 = 0 ∧ ((u : GL Ix K) : Matrix Ix Ix K) if1 ie2 = 0 ∧
      ((u : GL Ix K) : Matrix Ix Ix K) if2 ie2 = 0 := by
  obtain ⟨hT, hd⟩ := mem_hypUnitriangular.mp hu
  exact ⟨hd ie1, hd ie2, hT (by simp), hT (by simp), hT (by simp)⟩

@[expose] noncomputable def burnsideF429_U4_psi : ↥(hypUnitriangular h 2 0) →* Multiplicative K where
  toFun u := Multiplicative.ofAdd ((((u : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 ie2)
  map_one' := by
    show Multiplicative.ofAdd ((1 : Matrix Ix Ix K) ie1 ie2) = 1
    rw [one_apply_ne (by simp)]
    rfl
  map_mul' u u' := by
    obtain ⟨h1, -, -, -, -⟩ := burnsideF429_U4_U_entries h u.2
    obtain ⟨-, h2', -, h3', h4'⟩ := burnsideF429_U4_U_entries h u'.2
    show Multiplicative.ofAdd ((((u * u' : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 ie2) = _
    rw [coe_mul_hypSU, mul_apply, sum_ix, h1, h2', h3', h4', ← ofAdd_add]
    congr 1
    ring

theorem burnsideF429_U4_psi_apply (u : ↥(hypUnitriangular h 2 0)) :
    burnsideF429_U4_psi h u =
      Multiplicative.ofAdd ((((u : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 ie2) :=
  rfl

theorem burnsideF429_U4_mem_q2_of_psi {u : hypSU h 2 0} (hu : u ∈ hypUnitriangular h 2 0)
    (ha : ((u : GL Ix K) : Matrix Ix Ix K) ie1 ie2 = 0) : u ∈ radQ2 h := by
  obtain ⟨h1, h2, h3, -, -⟩ := burnsideF429_U4_U_entries h hu
  have huP : u ∈ parP2 h := by
    have := hypUnitriangular_le_hypBorel h hu
    rw [← burnsideF4gU4Inv_parP_inf_parP2] at this
    exact this.2
  refine mem_radQ2_of_rho2 h huP ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho2, h1, h2, h3, ha]

theorem burnsideF429_U4_card_q2_ge [Finite K] : (2 ^ m) ^ 4 ≤ Nat.card (radQ2 h) := by
  haveI : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have hU := card_hypUnitriangular h (r := 2) (ε := 0) (by norm_num)
  norm_num at hU
  have hker : Nat.card (burnsideF429_U4_psi h).ker ≤ Nat.card (radQ2 h) := by
    refine Nat.card_le_card_of_injective (fun u => ⟨(u : ↥(hypUnitriangular h 2 0)), ?_⟩) ?_
    · have hu := u.2
      rw [MonoidHom.mem_ker, burnsideF429_U4_psi_apply] at hu
      exact burnsideF429_U4_mem_q2_of_psi h (u : ↥(hypUnitriangular h 2 0)).2
        (Multiplicative.ofAdd.injective hu)
    · intro u v huv
      have e := congrArg Subtype.val huv
      exact Subtype.ext (Subtype.ext e)
  have hran : Nat.card (burnsideF429_U4_psi h).range ≤ (2 ^ m) ^ 2 := by
    calc Nat.card (burnsideF429_U4_psi h).range ≤ Nat.card (Multiplicative K) :=
          Subgroup.card_le_card_group _
      _ = (2 ^ m) ^ 2 := by
          show Nat.card K = _
          rw [h.card]
          ring
  have hprod := Subgroup.card_ker_mul_card_range (burnsideF429_U4_psi h)
  rw [hU] at hprod
  have hpos : 0 < (2 ^ m) ^ 2 := by positivity
  by_contra hlt
  push Not at hlt
  have : Nat.card (burnsideF429_U4_psi h).ker * Nat.card (burnsideF429_U4_psi h).range <
      (2 ^ m) ^ 4 * (2 ^ m) ^ 2 :=
    calc _ ≤ Nat.card (radQ2 h) * (2 ^ m) ^ 2 := Nat.mul_le_mul hker hran
      _ < (2 ^ m) ^ 4 * (2 ^ m) ^ 2 := Nat.mul_lt_mul_of_pos_right hlt hpos
  rw [hprod] at this
  have e : (2 ^ m) ^ 4 * (2 ^ m) ^ 2 = (2 ^ m) ^ 6 := by ring
  omega

omit [Field K] in
theorem burnsideF429_U4_card_barFix_le {K : Type} [Field K] (h : UnitaryFieldData 2 m K) :
    Nat.card {x : K // barEquiv h x = x} ≤ 2 ^ m := by
  have h1q : 1 < 2 ^ m := Nat.one_lt_two_pow (by have := h.one_le; omega)
  exact CFSG.SeitzReduction.natCard_le_of_forall_pow_eq_self h1q {x : K | barEquiv h x = x}
    fun x hx => by
      have hx' : barEquiv h x = x := hx
      rwa [barEquiv_apply, h.bar_apply] at hx'

theorem burnsideF429_U4_rel_of_comm {b q : hypSU h 2 0} (hb : b ∈ hypUnitriangular h 2 0)
    (hq : q ∈ radQ2 h) (hc : b * q * b⁻¹ = q) :
    ((b : GL Ix K) : Matrix Ix Ix K) ie1 ie2 * ((q : GL Ix K) : Matrix Ix Ix K) ie2 if2 = 0 ∧
      ((q : GL Ix K) : Matrix Ix Ix K) ie1 if2 * h.bar (((b : GL Ix K) : Matrix Ix Ix K) ie1 ie2) +
        ((b : GL Ix K) : Matrix Ix Ix K) ie1 ie2 *
          h.bar (((q : GL Ix K) : Matrix Ix Ix K) ie1 if2) +
        ((b : GL Ix K) : Matrix Ix Ix K) ie1 ie2 * h.bar (((b : GL Ix K) : Matrix Ix Ix K) ie1 ie2) *
          ((q : GL Ix K) : Matrix Ix Ix K) ie2 if2 = 0 := by
  obtain ⟨h11, h22, h21, -, -⟩ := burnsideF429_U4_U_entries h hb
  have e12 := burnsideF429_U4_conj_q2 h b hq (a := ie1) (b := if2) (by simp)
  have e11 := burnsideF429_U4_conj_q2 h b hq (a := ie1) (b := if1) (by simp)
  rw [hc] at e12 e11
  simp only [hypPartner_if2, hypPartner_if1, h11, h22, h21, map_zero, map_one, mul_zero,
    zero_mul, zero_add, add_zero, mul_one, one_mul] at e12 e11
  exact ⟨by linear_combination -e12, by linear_combination -e11⟩

theorem burnsideF429_U4_card_elemAb_le [Finite K] {B : Subgroup (hypSU h 2 0)}
    (hBU : B ≤ hypUnitriangular h 2 0) (hB : CFSG.Open.IsElemAbelian 2 B)
    (hBQ : ¬ B ≤ radQ2 h) : Nat.card B ≤ (2 ^ m) ^ 3 := by
  have := h.charP
  haveI : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hcomm := isMulCommutative_iff_of_setLike.mp hB.1
  have hbarK : ∀ c, barEquiv h c = h.bar c := barEquiv_apply h
  let aa : hypSU h 2 0 → K := fun b => ((b : GL Ix K) : Matrix Ix Ix K) ie1 ie2
  let ψB : ↥B →* Multiplicative K := (burnsideF429_U4_psi h).comp (Subgroup.inclusion hBU)
  have hψB : ∀ b : B, ψB b = Multiplicative.ofAdd (aa b) := fun b => rfl
  have hkerQ : ∀ u : ψB.ker, ((u : B) : hypSU h 2 0) ∈ radQ2 h := by
    intro u
    have hu := u.2
    rw [MonoidHom.mem_ker, hψB] at hu
    exact burnsideF429_U4_mem_q2_of_psi h (hBU (u : B).2) (Multiplicative.ofAdd.injective hu)
  have hrel : ∀ b ∈ B, ∀ q ∈ B, q ∈ radQ2 h → _ := fun b hb q hqB hq =>
    burnsideF429_U4_rel_of_comm h (hBU hb) hq (by rw [hcomm b hb q hqB, mul_inv_cancel_right])
  obtain ⟨b₀, hb₀B, hb₀Q⟩ := SetLike.not_le_iff_exists.mp hBQ
  have ha₀ : aa b₀ ≠ 0 := fun h0 => hb₀Q (burnsideF429_U4_mem_q2_of_psi h (hBU hb₀B) h0)
  have hba₀ : h.bar (aa b₀) ≠ 0 := fun h0 => ha₀ ((map_eq_zero_iff h.bar h.bar.injective).mp h0)
  have hδ : ∀ q ∈ B, q ∈ radQ2 h → ((q : GL Ix K) : Matrix Ix Ix K) ie2 if2 = 0 := fun q hqB hq =>
    (mul_eq_zero.mp (hrel b₀ hb₀B q hqB hq).1).resolve_left ha₀
  have hβ : ∀ b ∈ B, ∀ q ∈ B, q ∈ radQ2 h →
      ((q : GL Ix K) : Matrix Ix Ix K) ie1 if2 * h.bar (aa b) +
        aa b * h.bar (((q : GL Ix K) : Matrix Ix Ix K) ie1 if2) = 0 := by
    intro b hb q hqB hq
    have := (hrel b hb q hqB hq).2
    rw [hδ q hqB hq, mul_zero, add_zero] at this
    exact this
  have hcard := Subgroup.card_ker_mul_card_range ψB
  have hq1 : Nat.card {x : K // barEquiv h x = x} ≤ 2 ^ m := burnsideF429_U4_card_barFix_le h
  by_cases hcase : ∀ b ∈ B, h.bar (aa b / aa b₀) = aa b / aa b₀
  ·
    have hran : Nat.card ψB.range ≤ 2 ^ m := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun x : ψB.range => (⟨Multiplicative.toAdd (x : Multiplicative K) / aa b₀, ?_⟩ :
          {x : K // barEquiv h x = x})) ?_) hq1
      · obtain ⟨b, hb⟩ := x.2
        rw [hbarK, ← hb, hψB, toAdd_ofAdd]
        exact hcase b b.2
      · intro x y hxy
        have e : Multiplicative.toAdd (x : Multiplicative K) / aa b₀ =
            Multiplicative.toAdd (y : Multiplicative K) / aa b₀ := congrArg Subtype.val hxy
        exact Subtype.ext (Multiplicative.toAdd.injective ((div_left_inj' ha₀).mp e))
    have hker : Nat.card ψB.ker ≤ (2 ^ m) ^ 2 := by
      let S : Set (K × K) := {p | (aa b₀ / h.bar (aa b₀)) * barEquiv h p.1 = p.1 ∧
        1 * barEquiv h p.2 + 0 = p.2}
      have hmem : ∀ u : ψB.ker, ((((((u : B) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 if2,
          ((((u : B) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 if1) ∈ S) := by
        intro u
        have hq := hkerQ u
        obtain ⟨h11, -, -⟩ := burnsideF429_U4_q2_herm h hq
        have hb := hβ b₀ hb₀B _ (u : B).2 hq
        refine ⟨?_, by rw [one_mul, add_zero, hbarK]; exact h11⟩
        show aa b₀ / h.bar (aa b₀) * barEquiv h _ = _
        rw [hbarK, div_mul_eq_mul_div, div_eq_iff hba₀]
        linear_combination hb - (((((u : B) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 if2 *
          h.bar (aa b₀)) * h2
      refine le_trans (Nat.card_le_card_of_injective (fun u => (⟨_, hmem u⟩ : S)) ?_) ?_
      · intro u v huv
        have e := congrArg Subtype.val huv
        simp only [Prod.mk.injEq] at e
        have hu := hkerQ u
        have hv := hkerQ v
        exact Subtype.ext (Subtype.ext (burnsideF429_q2_ext h hu hv e.2 e.1
          (by rw [hδ _ (u : B).2 hu, hδ _ (v : B).2 hv])))
      · refine (burnsideF429_card_twisted_le_sq (barEquiv h)
          (div_ne_zero ha₀ hba₀) one_ne_zero (fun _ => 0) S fun p hp => hp).trans ?_
        exact Nat.pow_le_pow_left hq1 2
    rw [← hcard]
    calc Nat.card ψB.ker * Nat.card ψB.range ≤ (2 ^ m) ^ 2 * 2 ^ m := Nat.mul_le_mul hker hran
      _ = (2 ^ m) ^ 3 := by ring
  ·
    push Not at hcase
    obtain ⟨b₁, hb₁B, hne⟩ := hcase
    have hβ0 : ∀ q ∈ B, q ∈ radQ2 h → ((q : GL Ix K) : Matrix Ix Ix K) ie1 if2 = 0 := by
      intro q hqB hq
      by_contra hβne
      apply hne
      have e0 := hβ b₀ hb₀B q hqB hq
      have e1 := hβ b₁ hb₁B q hqB hq
      set β := ((q : GL Ix K) : Matrix Ix Ix K) ie1 if2
      have key : β * (aa b₁ * h.bar (aa b₀) + aa b₀ * h.bar (aa b₁)) = 0 := by
        linear_combination (aa b₁) * e0 - (aa b₀) * e1 + (β * aa b₀ * h.bar (aa b₁)) * h2
      have key' : aa b₁ * h.bar (aa b₀) = aa b₀ * h.bar (aa b₁) := by
        have := (mul_eq_zero.mp key).resolve_left hβne
        linear_combination this - (aa b₀ * h.bar (aa b₁)) * h2
      rw [map_div₀, div_eq_div_iff hba₀ ha₀]
      linear_combination -key'
    have hker : Nat.card ψB.ker ≤ 2 ^ m := by
      refine le_trans (Nat.card_le_card_of_injective (fun u : ψB.ker =>
        (⟨((((u : B) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 if1, ?_⟩ :
          {x : K // barEquiv h x = x})) ?_) hq1
      · rw [hbarK]
        exact (burnsideF429_U4_q2_herm h (hkerQ u)).1
      · intro u v huv
        have e : ((((u : B) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 if1 =
            ((((v : B) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 if1 :=
          congrArg Subtype.val huv
        have hu := hkerQ u
        have hv := hkerQ v
        exact Subtype.ext (Subtype.ext (burnsideF429_q2_ext h hu hv e
          (by rw [hβ0 _ (u : B).2 hu, hβ0 _ (v : B).2 hv])
          (by rw [hδ _ (u : B).2 hu, hδ _ (v : B).2 hv])))
    have hran : Nat.card ψB.range ≤ (2 ^ m) ^ 2 := by
      calc Nat.card ψB.range ≤ Nat.card (Multiplicative K) := Subgroup.card_le_card_group _
        _ = (2 ^ m) ^ 2 := by
            show Nat.card K = _
            rw [h.card]
            ring
    rw [← hcard]
    calc Nat.card ψB.ker * Nat.card ψB.range ≤ 2 ^ m * (2 ^ m) ^ 2 := Nat.mul_le_mul hker hran
      _ = (2 ^ m) ^ 3 := by ring

end UGroup

end CFSG.ASVolI
