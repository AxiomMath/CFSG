module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.S46TypeLin

public section

namespace CFSG.Quasithin.MS93.S46.I466b

open CFSG.Quasithin
open scoped Matrix

variable {F : Type} [Field F]

theorem mem_plane_iff {P : Submodule F (Fin 3 → F)} (hP : Module.finrank F P = 2)
    {r r' : Fin 3 → F} (hr : r ∈ P) (hr' : r' ∈ P) (hr0 : r ≠ 0) (hrr' : r' ∉ F ∙ r)
    {p : Fin 3 → F} (hp : p ∈ P) : ∃ a c : F, p = a • r + c • r' := by
  have hle : F ∙ r ⊔ F ∙ r' ≤ P :=
    sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hr)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hr')
  have hlt : F ∙ r < F ∙ r ⊔ F ∙ r' := lt_of_le_of_ne le_sup_left fun h =>
    hrr' (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self r'))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_span_singleton hr0] at h1
  have h2 := Submodule.finrank_mono hle
  have heq : F ∙ r ⊔ F ∙ r' = P := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  rw [← heq] at hp
  obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hp
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu'
  exact ⟨a, c, rfl⟩

theorem exists_mem_not_mem_span {P : Submodule F (Fin 3 → F)} (hP : Module.finrank F P = 2)
    (r : Fin 3 → F) : ∃ r' ∈ P, r' ∉ F ∙ r := by
  by_contra! hall
  have hle : P ≤ F ∙ r := fun x hx => hall x hx
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank F (F ∙ r) ≤ 1 := by
    by_cases hr0 : r = 0
    · rw [hr0, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
      omega
    · rw [finrank_span_singleton hr0]
  omega

theorem exists_flag_conj {P : Submodule F (Fin 3 → F)} (hP : Module.finrank F P = 2)
    {r : Fin 3 → F} (hr : r ∈ P) (hr0 : r ≠ 0) :
    ∃ y : SL3 F, (y : Matrix (Fin 3) (Fin 3) F) *ᵥ r = ![1, 0, 0] ∧
      (∀ p ∈ P, ((y : Matrix (Fin 3) (Fin 3) F) *ᵥ p) 1 = 0) ∧
      ∀ w : Fin 3 → F, w 1 = 0 → ((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ P := by
  obtain ⟨r', hr'P, hr'⟩ := exists_mem_not_mem_span hP r
  obtain ⟨w, hw⟩ := exists_not_mem_of_finrank_eq_two hP
  set M : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => ![r, w, r'] j i with hMdef
  have hMv : ∀ x : Fin 3 → F, M *ᵥ x = x 0 • r + x 1 • w + x 2 • r' := by
    intro x
    funext i
    simp [hMdef, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  have hMinj : Function.Injective M.mulVec := by
    intro x x' hxx
    have h0 : M *ᵥ (x - x') = 0 := by rw [Matrix.mulVec_sub, hxx, sub_self]
    rw [hMv] at h0
    set z := x - x' with hz
    have hz1 : z 1 = 0 := by
      by_contra hne
      apply hw
      have e : z 1 • w = -(z 0 • r + z 2 • r') := by
        rw [eq_neg_iff_add_eq_zero, ← h0]; abel
      have : w = (z 1)⁻¹ • (-(z 0 • r + z 2 • r')) := by
        rw [← e, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact P.smul_mem _ (P.neg_mem (P.add_mem (P.smul_mem _ hr) (P.smul_mem _ hr'P)))
    have hz2 : z 2 = 0 := by
      by_contra hne
      apply hr'
      have e : z 2 • r' = -(z 0 • r) := by
        rw [eq_neg_iff_add_eq_zero, ← h0, hz1, zero_smul, add_zero]; abel
      have : r' = (z 2)⁻¹ • (-(z 0 • r)) := by
        rw [← e, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.neg_mem _
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self r)))
    have hz0 : z 0 = 0 := by
      rw [hz1, hz2, zero_smul, add_zero, zero_smul, add_zero] at h0
      exact (smul_eq_zero.mp h0).resolve_right hr0
    have : z = 0 := by
      funext i
      fin_cases i
      · exact hz0
      · exact hz1
      · exact hz2
    exact sub_eq_zero.mp this
  have hdet : M.det ≠ 0 := by
    have := Matrix.mulVec_injective_iff_isUnit.mp hMinj
    rw [Matrix.isUnit_iff_isUnit_det] at this
    exact this.ne_zero
  set d := M.det with hd
  set M' : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => ![r, d⁻¹ • w, r'] j i with hM'def
  have hM'det : M'.det = 1 := by
    have e : M'.det = d⁻¹ * M.det := by
      rw [Matrix.det_fin_three, Matrix.det_fin_three]
      simp [hM'def, hMdef]
      ring
    rw [e, ← hd, inv_mul_cancel₀ hdet]
  have hM'v : ∀ x : Fin 3 → F, M' *ᵥ x = x 0 • r + x 1 • (d⁻¹ • w) + x 2 • r' := by
    intro x
    funext i
    simp [hM'def, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  set m : SL3 F := ⟨M', hM'det⟩ with hmdef
  have hm : ∀ x : Fin 3 → F, (m : Matrix (Fin 3) (Fin 3) F) *ᵥ x =
      x 0 • r + x 1 • (d⁻¹ • w) + x 2 • r' := hM'v
  refine ⟨m⁻¹, ?_, ?_, ?_⟩
  · have e : r = (m : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] := by rw [hm]; simp
    rw [e, inv_mulVec_mulVec_SL3]
  · intro p hp
    obtain ⟨a, c, rfl⟩ := mem_plane_iff hP hr hr'P hr0 hr' hp
    have e : a • r + c • r' = (m : Matrix (Fin 3) (Fin 3) F) *ᵥ ![a, 0, c] := by
      rw [hm]; simp
    rw [e, inv_mulVec_mulVec_SL3]
    rfl
  · intro x hx
    rw [inv_inv, hm, hx, zero_smul, add_zero]
    exact P.add_mem (P.smul_mem _ hr) (P.smul_mem _ hr'P)

@[expose] def axisGroup (P : Submodule F (Fin 3 → F)) : Subgroup (SL3 F) where
  carrier := {B | (∀ p ∈ P, ((B : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p = p) ∧
    ∀ x, ((B : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ P}
  mul_mem' := by
    rintro B C ⟨hB1, hB2⟩ ⟨hC1, hC2⟩
    refine ⟨fun p hp => ?_, fun x => ?_⟩
    · rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, hC1 p hp, hB1 p hp]
    · rw [coe_mul_SL3, ← Matrix.mulVec_mulVec]
      have e : (B : Matrix (Fin 3) (Fin 3) F) *ᵥ ((C : Matrix (Fin 3) (Fin 3) F) *ᵥ x) - x =
          ((B : Matrix (Fin 3) (Fin 3) F) *ᵥ ((C : Matrix (Fin 3) (Fin 3) F) *ᵥ x) -
            (C : Matrix (Fin 3) (Fin 3) F) *ᵥ x) +
          ((C : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x) := by abel
      rw [e]
      exact P.add_mem (hB2 _) (hC2 x)
  one_mem' := ⟨fun p _ => by rw [coe_one_SL3, Matrix.one_mulVec], fun x => by
    rw [coe_one_SL3, Matrix.one_mulVec, sub_self]; exact P.zero_mem⟩
  inv_mem' := by
    rintro B ⟨hB1, hB2⟩
    refine ⟨fun p hp => ?_, fun x => ?_⟩
    · have h := congrArg (((B⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ·) (hB1 p hp)
      simp only [inv_mulVec_mulVec_SL3] at h
      exact h.symm
    · have h := hB2 (((B⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)
      rw [mulVec_inv_mulVec_SL3] at h
      have h' := hB1 _ h
      rw [Matrix.mulVec_sub, mulVec_inv_mulVec_SL3] at h'
      have e : ((B⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x =
          -(x - ((B⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) := by abel
      rw [e]
      exact P.neg_mem h

theorem card_axisGroup_le [Finite F] {P : Submodule F (Fin 3 → F)}
    (hP : Module.finrank F P = 2) : Nat.card (axisGroup P) ≤ Nat.card F ^ 2 := by
  have hfix : P ≤ fixN (axisGroup P) := fun p hp B hB => hB.1 p hp
  have hcomm : commN (axisGroup P) ≤ P := by
    rw [commN, Submodule.span_le]
    rintro _ ⟨B, hB, x, rfl⟩
    exact hB.2 x
  have h1 := Submodule.finrank_mono hfix
  have h2 := Submodule.finrank_mono hcomm
  have h3 := Submodule.finrank_le (fixN (axisGroup P))
  rw [Module.finrank_fin_fun] at h3
  have hq : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  calc Nat.card (axisGroup P) ≤ Nat.card F ^ ((3 - Module.finrank F (fixN (axisGroup P))) *
        Module.finrank F (commN (axisGroup P))) := card_le_pow_finrank _
    _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_right hq (by
        have : 3 - Module.finrank F (fixN (axisGroup P)) ≤ 1 := by omega
        calc (3 - Module.finrank F (fixN (axisGroup P))) *
              Module.finrank F (commN (axisGroup P)) ≤ 1 * 2 := Nat.mul_le_mul this (by omega)
          _ = 2 := by norm_num)

theorem inv_mulVec_mem_of_le {P : Submodule F (Fin 3 → F)} [FiniteDimensional F P] {A : SL3 F}
    (hA : ∀ p ∈ P, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ p ∈ P) {p : Fin 3 → F} (hp : p ∈ P) :
    ((A⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p ∈ P := by
  set e := (Matrix.SpecialLinearGroup.toLin' A : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) with he
  have hle : P.map (e : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hA x hx
  have heq : P.map (e : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) = P :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq e P)
  rw [← heq] at hp
  obtain ⟨x, hx, hxp⟩ := hp
  have e1 : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ x = p := hxp
  rw [← e1, inv_mulVec_mulVec_SL3]
  exact hx

theorem conj_mem_axisGroup {P : Submodule F (Fin 3 → F)} [FiniteDimensional F P] {A B : SL3 F}
    (hA : ∀ p ∈ P, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ p ∈ P) (hB : B ∈ axisGroup P) :
    A * B * A⁻¹ ∈ axisGroup P := by
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨fun p hp => ?_, fun x => ?_⟩
  · rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hB1 _ (inv_mulVec_mem_of_le hA hp), mulVec_inv_mulVec_SL3]
  · rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have e : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ ((B : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (((A⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)) - x =
        (A : Matrix (Fin 3) (Fin 3) F) *ᵥ ((B : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (((A⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) -
          ((A⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) := by
      rw [Matrix.mulVec_sub, mulVec_inv_mulVec_SL3]
    rw [e]
    exact hA _ (hB2 _)

section CharTwo

variable [CharP F 2]

@[expose] def rot02 : SL3 F :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 1], by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩

theorem rot02_mulVec (x : Fin 3 → F) :
    ((rot02 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = ![x 2, x 1, x 0 + x 2] := by
  funext i
  fin_cases i <;> simp [rot02, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem rot02_pow_three : (rot02 : SL3 F) ^ 3 = 1 := by
  apply Subtype.ext
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [pow_three, coe_mul_SL3, coe_mul_SL3,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rot02_mulVec, rot02_mulVec, rot02_mulVec,
    coe_one_SL3, Matrix.one_mulVec]
  funext k
  fin_cases i <;> fin_cases k <;> simp [CharTwo.add_self_eq_zero]

theorem rot02_pow_mod (n : ℕ) : (rot02 : SL3 F) ^ n = rot02 ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, rot02_pow_three, one_pow, one_mul]

theorem exists_rot_of_plane {P : Submodule F (Fin 3 → F)} (hP : Module.finrank F P = 2)
    {r : Fin 3 → F} (hr : r ∈ P) (hr0 : r ≠ 0) :
    ∃ B : SL3 F, B ^ 3 = 1 ∧ (∀ x, (B : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ P) ∧
      ∀ n : ℕ, ¬ 3 ∣ n → ((B ^ n : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ r ∉ F ∙ r := by
  obtain ⟨y, hyr, -, hyP⟩ := exists_flag_conj hP hr hr0
  refine ⟨y⁻¹ * rot02 * y, ?_, fun x => ?_, fun n hn => ?_⟩
  · rw [show y⁻¹ * rot02 * y = y⁻¹ * rot02 * y⁻¹⁻¹ by rw [inv_inv], conj_pow,
      rot02_pow_three]
    group
  · have e : ((y⁻¹ * rot02 * y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x =
        ((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (((rot02 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ((y : Matrix (Fin 3) (Fin 3) F) *ᵥ x)
            - (y : Matrix (Fin 3) (Fin 3) F) *ᵥ x) := by
      rw [Matrix.mulVec_sub, inv_mulVec_mulVec_SL3, coe_mul_SL3, coe_mul_SL3,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [e]
    refine hyP _ ?_
    rw [rot02_mulVec]
    simp
  · have hpow : (y⁻¹ * rot02 * y) ^ n = y⁻¹ * rot02 ^ (n % 3) * y := by
      rw [← rot02_pow_mod, show y⁻¹ * rot02 * y = y⁻¹ * rot02 * y⁻¹⁻¹ by group, conj_pow]
      group
    rw [hpow]
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have h2 := congrArg ((y : Matrix (Fin 3) (Fin 3) F) *ᵥ ·) hc
    simp only [Matrix.mulVec_smul, hyr, coe_mul_SL3, ← Matrix.mulVec_mulVec,
      mulVec_inv_mulVec_SL3] at h2
    have hmod : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hmod with h | h
    · rw [h, pow_one, rot02_mulVec] at h2
      have := congrFun h2 2
      simp at this
    · rw [h, sq, coe_mul_SL3, ← Matrix.mulVec_mulVec, rot02_mulVec, rot02_mulVec] at h2
      have := congrFun h2 2
      simp at this

end CharTwo

theorem exists_transv_of_plane [Finite F] {P : Submodule F (Fin 3 → F)}
    (hP : Module.finrank F P = 2) {S : AddSubgroup (Fin 3 → F)} (hSP : ∀ s ∈ S, s ∈ P)
    (hS : Nat.card S ≤ Nat.card F) {v : Fin 3 → F} (hv : v ∈ S) (hv0 : v ≠ 0) :
    ∃ (A : SL3 F) (e : Fin 3 → F), (∀ x, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ F ∙ e) ∧
      (∀ p ∈ P, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ p ∈ P) ∧
      (A : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∉ S := by
  obtain ⟨y, hyv, -, hyP⟩ := exists_flag_conj hP (hSP v hv) hv0
  set w₂ := ((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] with hw₂
  have hw₂P : w₂ ∈ P := hyP _ (by simp)
  have hyw₂ : (y : Matrix (Fin 3) (Fin 3) F) *ᵥ w₂ = ![0, 0, 1] := mulVec_inv_mulVec_SL3 y _
  obtain ⟨t, ht⟩ : ∃ t : F, t • w₂ ∉ S := by
    by_contra! hall
    have hinj : Function.Injective (fun o : Option F => (match o with
        | none => (⟨v, hv⟩ : S)
        | some t => ⟨t • w₂, hall t⟩ : S)) := by
      have hw0 : w₂ ≠ 0 := by
        intro h0
        rw [h0, Matrix.mulVec_zero] at hyw₂
        have := congrFun hyw₂ 2
        simp at this
      have hvw : ∀ t : F, t • w₂ ≠ v := by
        intro t htv
        have h1 := congrArg ((y : Matrix (Fin 3) (Fin 3) F) *ᵥ ·) htv
        simp only [Matrix.mulVec_smul, hyw₂, hyv] at h1
        have := congrFun h1 0
        simp at this
      rintro (_ | t) (_ | t') h
      · rfl
      · exact absurd (congrArg Subtype.val h).symm (hvw t')
      · exact absurd (congrArg Subtype.val h) (hvw t)
      · have h1 : t • w₂ = t' • w₂ := congrArg Subtype.val h
        rw [← sub_eq_zero, ← sub_smul, smul_eq_zero] at h1
        rw [sub_eq_zero.mp (h1.resolve_right hw0)]
    have hcard := Nat.card_le_card_of_injective _ hinj
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card (α := Option F), Fintype.card_option,
      ← Nat.card_eq_fintype_card] at hcard
    omega
  refine ⟨y⁻¹ * rootElt 2 0 t * y, w₂, fun x => ?_, fun p hp => ?_, fun hmem => ht ?_⟩
  · have e : ((y⁻¹ * rootElt 2 0 t * y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x =
        (t * ((y : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 0) • w₂ := by
      rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        rootElt_mulVec (by decide), Matrix.mulVec_add, inv_mulVec_mulVec_SL3, add_sub_cancel_left,
        hw₂, ← Matrix.mulVec_smul]
      congr 1
      funext k
      fin_cases k <;> simp
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w₂)
  · have e : ((y⁻¹ * rootElt 2 0 t * y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p =
        p + (t * ((y : Matrix (Fin 3) (Fin 3) F) *ᵥ p) 0) • w₂ := by
      rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        rootElt_mulVec (by decide), Matrix.mulVec_add, inv_mulVec_mulVec_SL3, hw₂,
        ← Matrix.mulVec_smul]
      congr 2
      funext k
      fin_cases k <;> simp
    rw [e]
    exact P.add_mem hp (P.smul_mem _ hw₂P)
  · have e : ((y⁻¹ * rootElt 2 0 t * y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
        v + t • w₂ := by
      rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        rootElt_mulVec (by decide), Matrix.mulVec_add, inv_mulVec_mulVec_SL3, hw₂,
        ← Matrix.mulVec_smul, hyv]
      congr 2
      funext k
      fin_cases k <;> simp
    rw [e] at hmem
    have := S.sub_mem hmem hv
    rwa [add_sub_cancel_left] at this

end CFSG.Quasithin.MS93.S46.I466b
