module

public import CFSG.Monster.B.Fischer.HexadDiag
public import CFSG.Monster.B.TwoA.Census.NatCert
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public meta import CFSG.Monster.B.Fischer.HexadDiag
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public import CFSG.Monster.B.Fischer.HexadAffineInputs
public import Certificates.Certificate3032
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3017
public import Certificates.Certificate3029

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu
  groupCohomology CFSG.Monster.B.TwoA.Census

theorem closure_range_gKB :
    Subgroup.closure (Set.range gKB) = ⊤ := by
  apply Subgroup.map_injective KB.subtype_injective
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact closure_gKB

theorem kb_induction
    {P : KB → Prop}
    (hgen : ∀ i, P (gKB i)) (h1 : P 1)
    (hmul : ∀ x y, P x → P y → P (x * y)) (hinv : ∀ x, P x → P x⁻¹) (k : KB) : P k := by
  have hk : k ∈ Subgroup.closure (Set.range gKB) := closure_range_gKB ▸ Subgroup.mem_top k
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hgen i
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul x y hx hy
  | inv x _ hx => exact hinv x hx

theorem add_self_Q (x : Q₀) : x + x = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem neg_Q (x : Q₀) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, add_self_Q]

theorem sub_Q (x y : Q₀) : x - y = x + y := by rw [sub_eq_add_neg, neg_Q]

@[expose] def IsAffineAction
    (A : KB →* Equiv.Perm Q₀) : Prop :=
  ∀ k q v, A k (q + v) = A k q + rhoQ k v

@[expose] def IsTranslationIso (A A' : KB →* Equiv.Perm Q₀) (t : Q₀) : Prop :=
  ∀ k q, A' k (q + t) = A k q + t

theorem rhoQ_inv_apply (k : KB)
    (q : Q₀) : rhoQ k⁻¹ (rhoQ k q) = q := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem rhoQ_apply_inv (k : KB)
    (q : Q₀) : rhoQ k (rhoQ k⁻¹ q) = q := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

@[expose] noncomputable def affLin :
    KB →* Equiv.Perm Q₀ where
  toFun k := ⟨rhoQ k, rhoQ k⁻¹, rhoQ_inv_apply k, rhoQ_apply_inv k⟩
  map_one' := Equiv.ext fun q => by simp
  map_mul' k l := Equiv.ext fun q => by simp [map_mul]

theorem affLin_apply (k : KB) (q : Q₀)
    : affLin k q = rhoQ k q := rfl

@[expose] noncomputable def affA :
    KB
    →* Equiv.Perm Q₀ :=
  qEquiv.permCongrHom.toMonoidHom.comp affCode

theorem affA_apply
    (k : KB) (q : Q₀) :
    affA k q = qEquiv (affCode k (qEquiv.symm q)) := rfl

theorem qEquiv_symm_qv {m : ℕ} (hm : m < 32) : qEquiv.symm (qv m) = ⟨m, hm⟩ := by
  rw [Equiv.symm_apply_eq, qEquiv_apply]

theorem affA_gKB_qv
    (i : Fin 3)
    {m : ℕ} (hm : m < 32) : affA (gKB i) (qv m) = qv (alpha i m) := by
  rw [affA_apply, qEquiv_symm_qv hm, qEquiv_apply, affCode_gKB_apply i hm]

theorem affA_gKB
    (i : Fin 3) (q : Q₀)
    : affA (gKB i) q = rhoQ (gKB i) q + qv (cval i) := by
  obtain ⟨m, hm, rfl⟩ := qv_surj q
  rw [affA_gKB_qv i hm, alpha, qv_xor, rhoQ_qv i hm]

theorem isAffineAction_affLin :
    IsAffineAction affLin := fun k q v => by
  simp only [affLin_apply, map_add]

theorem isAffineAction_affA :
    IsAffineAction affA := by
  intro k
  refine kb_induction (P := fun k => ∀ q v, affA k (q + v) = affA k q + rhoQ k v) ?_ ?_ ?_ ?_ k
  · intro i q v
    rw [affA_gKB, affA_gKB, map_add]
    abel
  · intro q v
    simp
  · intro x y hx hy q v
    rw [map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hy, hx, map_mul,
      Module.End.mul_apply]
  · intro x hx q v
    apply (affA x).injective
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply, hx,
      ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply,
      rhoQ_apply_inv]

@[expose] noncomputable def transl (A : KB →* Equiv.Perm Q₀) (k : KB) : Q₀ := A k 0

variable {A A' : KB →* Equiv.Perm Q₀}

theorem affine_apply
    (hA : IsAffineAction A) (k : KB) (q : Q₀) :
    A k q = rhoQ k q + transl A k := by
  have := hA k 0 q
  rw [zero_add] at this
  rw [this, add_comm]
  rfl

theorem transl_mul
    (hA : IsAffineAction A) (k l : KB) :
    transl A (k * l) = rhoQ k (transl A l) + transl A k := by
  rw [transl, map_mul, Equiv.Perm.mul_apply, affine_apply hA]
  rfl

theorem transl_mem
    (hA : IsAffineAction A) : transl A ∈ cocycles₁ (Rep.of rhoQ) := by
  rw [mem_cocycles₁_iff]
  intro g h
  exact transl_mul hA g h

theorem char2_iff (a b c : Q₀) : a = b + c ↔ a + b = c := by
  constructor
  · rintro rfl
    rw [add_comm b c, add_assoc, add_self_Q, add_zero]
  · rintro rfl
    rw [add_comm a b, ← add_assoc, add_self_Q, zero_add]

theorem isTranslationIso_iff
    (hA : IsAffineAction A) (hA' : IsAffineAction A') (t : Q₀) :
    IsTranslationIso A A' t ↔ ∀ k, transl A' k = transl A k + (rhoQ k t + t) := by
  constructor
  · intro h k
    have h1 := h k 0
    rw [zero_add, affine_apply hA', affine_apply hA, map_zero, zero_add] at h1
    calc transl A' k = rhoQ k t + transl A' k + rhoQ k t := by
          rw [add_comm (rhoQ k t), add_assoc, add_self_Q, add_zero]
      _ = transl A k + t + rhoQ k t := by rw [h1]
      _ = transl A k + (rhoQ k t + t) := by abel
  · intro h k q
    rw [affine_apply hA', affine_apply hA, map_add, h k]
    have : rhoQ k q + rhoQ k t + (transl A k + (rhoQ k t + t)) =
        rhoQ k q + transl A k + t + (rhoQ k t + rhoQ k t) := by abel
    rw [this, add_self_Q, add_zero]

theorem isTranslationIso_iff_d₀₁
    (hA : IsAffineAction A) (hA' : IsAffineAction A') (t : Q₀) :
    IsTranslationIso A A' t ↔ transl A' - transl A = (d₀₁ (Rep.of rhoQ)).hom t := by
  rw [isTranslationIso_iff hA hA', funext_iff]
  refine forall_congr' fun k => ?_
  rw [Pi.sub_apply, d₀₁_hom_apply, sub_Q, sub_Q, char2_iff]

theorem d₀₁_injective :
    Function.Injective (d₀₁ (Rep.of rhoQ)).hom := by
  rw [← LinearMap.ker_eq_bot, d₀₁_ker_eq_invariants]
  exact invariants_rhoQ

theorem finrank_coboundaries₁ :
    Module.finrank (ZMod 2) (coboundaries₁ (Rep.of rhoQ)) = 5 := by
  rw [coboundaries₁, LinearMap.finrank_range_of_inj d₀₁_injective]
  exact finrank_Q₀

theorem transl_affA_gKB
    (i : Fin 3) :
    transl affA (gKB i) = qv (cval i) := by
  rw [transl, affA_gKB, map_zero, zero_add]

theorem not_coboundary_check : ∀ m < 32, linQ 1 m = m → linQ 2 m = m → linQ 0 m ^^^ m ≠ 9 := by
  decide +kernel

theorem transl_affA_not_mem :
    transl
    affA ∉ coboundaries₁ (Rep.of rhoQ) := by
  rintro ⟨x, hx⟩
  obtain ⟨m, hm, rfl⟩ := qv_surj x
  have hk : ∀ i : Fin 3, qv (linQ i m ^^^ m) = qv (cval i) := by
    intro i
    rw [← transl_affA_gKB, ← hx, d₀₁_hom_apply, qv_xor, sub_Q]
    rw [← rhoQ_qv i hm]
  have hlt : ∀ i : Fin 3, linQ i m ^^^ m < 32 := fun i =>
    Nat.xor_lt_two_pow (n := 5) (linQ_lt i i.2 m hm) hm
  have hc : ∀ i : Fin 3, cval i < 32 := by decide
  have e : ∀ i : Fin 3, linQ i m ^^^ m = cval i := fun i => qv_inj (hlt i) (hc i) (hk i)
  have e1 : linQ 1 m = m := by
    have h1 : linQ 1 m ^^^ m = 0 := e 1
    have := congrArg (· ^^^ m) h1
    simpa [Nat.xor_assoc] using this
  have e2 : linQ 2 m = m := by
    have h1 : linQ 2 m ^^^ m = 0 := e 2
    have := congrArg (· ^^^ m) h1
    simpa [Nat.xor_assoc] using this
  exact not_coboundary_check m hm e1 e2 (e 0)

@[expose] def powSum (T : ℕ → ℕ) (y : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => T (powSum T y n) ^^^ y

@[expose] def relOK (m₁ m₂ m₃ : ℕ) : Bool :=
  powSum (linQ 0) m₁ 2 == 0 && powSum (linQ 1) m₂ 2 == 0 && powSum (linQ 2) m₃ 2 == 0 &&
    powSum (fun v => linQ 0 (linQ 1 v)) (linQ 0 m₂ ^^^ m₁) 6 == 0 &&
    powSum (fun v => linQ 0 (linQ 2 v)) (linQ 0 m₃ ^^^ m₁) 4 == 0 &&
    powSum (fun v => linQ 1 (linQ 2 v)) (linQ 1 m₃ ^^^ m₂) 5 == 0

@[expose] def freeCheck : Bool :=
  (List.range 32).all fun m₁ => m₁.testBit 1 || m₁.testBit 3 ||
    (List.range 32).all fun m₂ => m₂.testBit 1 || m₂.testBit 2 ||
      (List.range 32).all fun m₃ => m₃.testBit 3 || m₃.testBit 4 ||
        !relOK m₁ m₂ m₃ || (m₁ == 0 && m₂ == 0 && m₃ == 0)

theorem freeCheck_eq : freeCheck = true := by decide +kernel

theorem relOK_check : ∀ m₁ < 32, m₁.testBit 1 = false → m₁.testBit 3 = false →
    ∀ m₂ < 32, m₂.testBit 1 = false → m₂.testBit 2 = false →
    ∀ m₃ < 32, m₃.testBit 3 = false → m₃.testBit 4 = false →
    relOK m₁ m₂ m₃ = true → m₁ = 0 ∧ m₂ = 0 ∧ m₃ = 0 := by
  intro m₁ h₁ a₁ b₁ m₂ h₂ a₂ b₂ m₃ h₃ a₃ b₃ hr
  have h := freeCheck_eq
  simp only [freeCheck, List.all_eq_true, List.mem_range] at h
  have := h m₁ h₁ |> fun h => h
  simp only [a₁, b₁, Bool.false_or, List.all_eq_true, List.mem_range] at this
  have := this m₂ h₂
  simp only [a₂, b₂, Bool.false_or, List.all_eq_true, List.mem_range] at this
  have := this m₃ h₃
  simp only [a₃, b₃, hr, Bool.false_or, Bool.not_true, Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem rel_sq : ∀ i : Fin 3, gKB i ^ 2 = 1 := by
  intro i
  apply Subtype.ext; apply Subtype.ext; apply Equiv.ext
  revert i
  decide +kernel

theorem rel_12 : (gKB 0 * gKB 1) ^ 6 = 1 := by
  apply Subtype.ext; apply Subtype.ext; apply Equiv.ext
  decide +kernel

theorem rel_13 : (gKB 0 * gKB 2) ^ 4 = 1 := by
  apply Subtype.ext; apply Subtype.ext; apply Equiv.ext
  decide +kernel

theorem rel_23 : (gKB 1 * gKB 2) ^ 5 = 1 := by
  apply Subtype.ext; apply Subtype.ext; apply Equiv.ext
  decide +kernel

theorem linQ_comp_lt (i j : Fin 3) : ∀ m < 32, linQ i (linQ j m) < 32 :=
  fun m hm => linQ_lt i i.2 _ (linQ_lt j j.2 m hm)

theorem rhoQ_mul_qv (i j : Fin 3)
    {m : ℕ} (hm : m < 32) :
    rhoQ (gKB i * gKB j) (qv m) = qv (linQ i (linQ j m)) := by
  rw [map_mul, Module.End.mul_apply, rhoQ_qv j hm, rhoQ_qv i (linQ_lt j j.2 m hm)]

section Cocycle

variable {c : KB → Q₀}
  (hc : ∀ g h, c (g * h) = rhoQ g (c h) + c g)
include hc

theorem cocycle_one : c 1 = 0 := by
  have := hc 1 1
  rw [mul_one, map_one, Module.End.one_apply] at this
  exact (add_left_cancel (this.symm.trans (add_zero _).symm))

theorem cocycle_pow {x : KB}
    {T : ℕ → ℕ} (hT : ∀ m < 32, rhoQ x (qv m) = qv (T m))
    (hTlt : ∀ m < 32, T m < 32) {y : ℕ} (hy : y < 32) (hcx : c x = qv y) :
    ∀ n, c (x ^ n) = qv (powSum T y n) ∧ powSum T y n < 32
  | 0 => ⟨by rw [pow_zero, cocycle_one hc, powSum, qv_zero], by simp [powSum]⟩
  | n + 1 => by
    obtain ⟨ih, hlt⟩ := cocycle_pow hT hTlt hy hcx n
    refine ⟨?_, Nat.xor_lt_two_pow (n := 5) (hTlt _ hlt) hy⟩
    rw [pow_succ', hc, ih, hT _ hlt, hcx, powSum, qv_xor]

theorem cocycle_eq_zero
    (h0 : ∀ i, c (gKB i) = 0) : c = 0 := by
  funext k
  refine kb_induction (P := fun k => c k = 0) h0 (cocycle_one hc) ?_ ?_ k
  · intro x y hx hy
    rw [hc, hx, hy, map_zero, add_zero]
  · intro x hx
    have := hc x⁻¹ x
    rw [inv_mul_cancel, cocycle_one hc, hx, map_zero, zero_add] at this
    exact this.symm

theorem relOK_of_cocycle
    {m : Fin 3 → ℕ} (hm : ∀ i, m i < 32) (hcm : ∀ i, c (gKB i) = qv (m i)) :
    relOK (m 0) (m 1) (m 2) = true := by
  have sq : ∀ i : Fin 3, powSum (linQ i) (m i) 2 = 0 := by
    intro i
    obtain ⟨h1, h2⟩ := cocycle_pow hc (x := gKB i) (fun m' hm' => rhoQ_qv i hm')
      (fun m' hm' => linQ_lt i i.2 m' hm') (hm i) (hcm i) 2
    rw [rel_sq, cocycle_one hc] at h1
    exact (qv_eq_zero_iff h2).1 h1.symm
  have pr : ∀ i j : Fin 3, ∀ n : ℕ, (gKB i * gKB j) ^ n = 1 →
      powSum (fun v => linQ i (linQ j v)) (linQ i (m j) ^^^ m i) n = 0 := by
    intro i j n hn
    have hy : linQ i (m j) ^^^ m i < 32 :=
      Nat.xor_lt_two_pow (n := 5) (linQ_lt i i.2 _ (hm j)) (hm i)
    have hcx : c (gKB i * gKB j) = qv (linQ i (m j) ^^^ m i) := by
      rw [hc, hcm, hcm, rhoQ_qv i (hm j), qv_xor]
    obtain ⟨h1, h2⟩ := cocycle_pow hc (x := gKB i * gKB j) (fun m' hm' => rhoQ_mul_qv i j hm')
      (linQ_comp_lt i j) hy hcx n
    rw [hn, cocycle_one hc] at h1
    exact (qv_eq_zero_iff h2).1 h1.symm
  have h12 := pr 0 1 6 rel_12
  have h13 := pr 0 2 4 rel_13
  have h23 := pr 1 2 5 rel_23
  simp only [relOK, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨sq 0, sq 1⟩, sq 2⟩, h12⟩, h13⟩, h23⟩

end Cocycle

theorem repr_qv (m : ℕ) (t : Fin 5) : bQ.repr (qv m) t = if m.testBit t then 1 else 0 := by
  have : qv m =
      ∑ s : Fin 5, (fun s : Fin 5 => if m.testBit s then (1 : ZMod 2) else 0) s • bQ s := by
    rw [qv_eq_sum_bQ]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : m.testBit s <;> simp [h]
  rw [this, Module.Basis.repr_sum_self]

@[expose] def freeGen : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

@[expose] def freeBit : Fin 6 → Fin 5 := ![1, 3, 1, 2, 3, 4]

@[expose] noncomputable def freeCoords
    :
    cocycles₁ (Rep.of rhoQ) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  LinearMap.pi fun s => (bQ.coord (freeBit s)).comp
    ((LinearMap.proj (R := ZMod 2) (φ := fun _ : KB => Q₀) (gKB (freeGen s))).comp
      (cocycles₁ (Rep.of rhoQ)).subtype)

theorem freeCoords_apply
    (c : cocycles₁ (Rep.of rhoQ)) (s : Fin 6) :
    freeCoords c s = bQ.repr ((c : KB → Q₀) (gKB (freeGen s))) (freeBit s) := rfl

theorem testBit_false_of_repr {m : ℕ} {t : Fin 5} (h : bQ.repr (qv m) t = 0) :
    m.testBit t = false := by
  rw [repr_qv] at h
  by_contra h'
  rw [Bool.not_eq_false] at h'
  rw [h'] at h
  exact absurd h (by decide)

theorem freeCoords_injective :
    Function.Injective freeCoords := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro c hc
  rw [LinearMap.mem_ker] at hc
  rw [Submodule.mem_bot]
  have hcoc : ∀ g h, (c : KB → Q₀) (g * h) = rhoQ g ((c : KB → Q₀) h) + (c : KB → Q₀) g :=
    (mem_cocycles₁_iff _).1 c.2
  choose m hm hcm using fun i : Fin 3 => qv_surj ((c : KB → Q₀) (gKB i))
  have hrel := relOK_of_cocycle hcoc hm fun i => (hcm i).symm
  have hz : ∀ s : Fin 6, bQ.repr (qv (m (freeGen s))) (freeBit s) = 0 := fun s => by
    rw [hcm]
    exact congrFun hc s
  obtain ⟨e1, e2, e3⟩ := relOK_check (m 0) (hm 0) (testBit_false_of_repr (hz 0))
    (testBit_false_of_repr (hz 1)) (m 1) (hm 1) (testBit_false_of_repr (hz 2))
    (testBit_false_of_repr (hz 3)) (m 2) (hm 2) (testBit_false_of_repr (hz 4))
    (testBit_false_of_repr (hz 5)) hrel
  have h0 : (c : KB → Q₀) = 0 := cocycle_eq_zero hcoc fun i => by
    rw [← hcm i]
    match i with
    | 0 => rw [e1, qv_zero]
    | 1 => rw [e2, qv_zero]
    | 2 => rw [e3, qv_zero]
  exact Subtype.ext h0

theorem finrank_cocycles₁_le :
    Module.finrank (ZMod 2) (cocycles₁ (Rep.of rhoQ)) ≤ 6 := by
  have := LinearMap.finrank_le_finrank_of_injective freeCoords_injective
  rwa [Module.finrank_fin_fun] at this

theorem transl_affA_ne_zero :
    transl
    affA ≠ 0 := fun h =>
  transl_affA_not_mem (h ▸ Submodule.zero_mem _)

theorem finrank_sup_transl :
    Module.finrank (ZMod 2)
      ↥(coboundaries₁ (Rep.of rhoQ) ⊔ Submodule.span (ZMod 2) {transl affA}) = 6 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (coboundaries₁ (Rep.of rhoQ))
    (Submodule.span (ZMod 2) {transl affA})
  have hdisj : coboundaries₁ (Rep.of rhoQ) ⊓ Submodule.span (ZMod 2) {transl affA} = ⊥ :=
    disjoint_iff.1 ((Submodule.disjoint_span_singleton' transl_affA_ne_zero).2
      transl_affA_not_mem)
  rw [hdisj, finrank_bot, add_zero, finrank_coboundaries₁,
    finrank_span_singleton transl_affA_ne_zero] at h
  exact h

theorem sup_transl_le :
    coboundaries₁ (Rep.of rhoQ) ⊔ Submodule.span (ZMod 2) {transl affA} ≤
      cocycles₁ (Rep.of rhoQ) :=
  sup_le (coboundaries₁_le_cocycles₁ _)
    ((Submodule.span_singleton_le_iff_mem _ _).2 (transl_mem isAffineAction_affA))

theorem finrank_cocycles₁ :
    Module.finrank (ZMod 2) (cocycles₁ (Rep.of rhoQ)) = 6 :=
  le_antisymm finrank_cocycles₁_le (finrank_sup_transl ▸ Submodule.finrank_mono sup_transl_le)

theorem cocycles₁_eq :
    cocycles₁ (Rep.of rhoQ) =
      coboundaries₁ (Rep.of rhoQ) ⊔ Submodule.span (ZMod 2) {transl affA} :=
  (Submodule.eq_of_le_of_finrank_eq sup_transl_le
    (by rw [finrank_sup_transl, finrank_cocycles₁])).symm

theorem transl_affLin :
    transl affLin = 0 := by
  funext k
  rw [transl, affLin_apply, map_zero]
  rfl

theorem zmod2_cases' : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem affine_classification
    (hA : IsAffineAction A) :
    (∃ t, IsTranslationIso affLin A t) ∨ (∃ t, IsTranslationIso affA A t) := by
  have hmem := transl_mem hA
  rw [cocycles₁_eq] at hmem
  obtain ⟨b, hb, y, hy, hby⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨x, rfl⟩ := hb
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rcases zmod2_cases' μ with rfl | rfl
  · left
    refine ⟨x, (isTranslationIso_iff_d₀₁ isAffineAction_affLin hA x).2 ?_⟩
    rw [transl_affLin, sub_zero, ← hby, zero_smul, add_zero]
  · right
    refine ⟨x, (isTranslationIso_iff_d₀₁ isAffineAction_affA hA x).2 ?_⟩
    rw [← hby, one_smul, add_sub_cancel_right]

theorem not_isTranslationIso_affLin_affA
    (t : Q₀) : ¬IsTranslationIso affLin affA t := by
  intro h
  rw [isTranslationIso_iff_d₀₁ isAffineAction_affLin isAffineAction_affA, transl_affLin,
    sub_zero] at h
  exact transl_affA_not_mem ⟨t, h.symm⟩

theorem isTranslationIso_unique
    (hA : IsAffineAction A) (hA' : IsAffineAction A') {t t' : Q₀}
    (ht : IsTranslationIso A A' t) (ht' : IsTranslationIso A A' t') : t = t' := by
  rw [isTranslationIso_iff_d₀₁ hA hA'] at ht ht'
  have := d₀₁_injective (ht.symm.trans ht')
  exact this

@[expose] def affOrbit (A : KB →* Equiv.Perm Q₀) (q : Q₀) : Set Q₀ := Set.range fun k => A k q

@[expose] def affGens (A : KB →* Equiv.Perm Q₀) (k : ℕ) : Equiv.Perm Q₀ :=
  if h : k < 3 then A (gKB ⟨k, h⟩) else 1

theorem closure_affGens
    (A : KB →* Equiv.Perm Q₀) :
    Subgroup.closure (affGens A '' {k | k < 3}) = A.range := by
  rw [MonoidHom.range_eq_map, ← closure_range_gKB, MonoidHom.map_closure]
  congr 1
  ext σ
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨gKB ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩, by simp [affGens, hk]⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, i.2, by simp [affGens, i.2]⟩

theorem affOrbit_eq
    (A : KB →* Equiv.Perm Q₀) (q : Q₀) :
    affOrbit A q = MulAction.orbit (Subgroup.closure (affGens A '' {k | k < 3})) q := by
  rw [closure_affGens]
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨A k, k, rfl⟩, rfl⟩
  · rintro ⟨⟨σ, k, rfl⟩, rfl⟩
    exact ⟨k, rfl⟩

theorem orbCert_ok : ∀ b : Bool, ∀ r ∈ [0, 1, 3],
    natCertOK (fun k m => if b then alpha k m else linQ k m) 3 (fun m => decide (m < 32)) r
      (orbCert b r) = true :=
  Certificates.certificate3032.1

theorem orbCert_size :
    (orbCert false 0).pts.size = 1 ∧ (orbCert false 3).pts.size = 15 ∧
      (orbCert false 1).pts.size = 16 ∧ (orbCert true 0).pts.size = 6 ∧
      (orbCert true 3).pts.size = 10 ∧ (orbCert true 1).pts.size = 16 :=
  Certificates.certificate3032.2.1

theorem orbCert_cover : ∀ b : Bool, ∀ m < 32,
    m ∈ (orbCert b 0).pts.toList ∨ m ∈ (orbCert b 3).pts.toList ∨
      m ∈ (orbCert b 1).pts.toList :=
  Certificates.certificate3032.2.2

theorem affGens_act
    (b : Bool) :
    ∀ k < 3, ∀ m, decide (m < 32) = true →
      qv ((fun k m => if b then alpha k m else linQ k m) k m) =
        affGens (if b then affA else affLin) k • qv m := by
  intro k hk m hm
  have hm' : m < 32 := of_decide_eq_true hm
  change _ = affGens (if b then affA else affLin) k (qv m)
  simp only [affGens, hk, ↓reduceDIte]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [affLin_apply, rhoQ_qv ⟨k, hk⟩ hm']
  · simp only [↓reduceIte]
    rw [affA_gKB_qv ⟨k, hk⟩ hm']

theorem qv_inj' : ∀ a b : ℕ, decide (a < 32) = true → decide (b < 32) = true → qv a = qv b →
    a = b := fun _ _ ha hb h => qv_inj (of_decide_eq_true ha) (of_decide_eq_true hb) h

theorem ncard_affOrbit
    (b : Bool) {r : ℕ} (hr : r ∈ [0, 1, 3]) :
    (affOrbit (if b then affA else affLin) (qv r)).ncard = (orbCert b r).pts.size := by
  rw [affOrbit_eq]
  exact ncard_orbit_of_natCertOK (orbCert_ok b r hr) (affGens_act b) qv_inj'

theorem mem_affOrbit
    (b : Bool) {r : ℕ} (hr : r ∈ [0, 1, 3]) {m : ℕ}
    (hm : m ∈ (orbCert b r).pts.toList) : qv m ∈ affOrbit (if b then affA else affLin) (qv r) := by
  rw [affOrbit_eq, orbit_of_natCertOK (orbCert_ok b r hr) (affGens_act b)]
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  refine ⟨i, by simpa using hi, ?_⟩
  simp [getElem!_pos (orbCert b r).pts i (by simpa using hi)]

theorem affOrbit_cover
    (b : Bool) (q : Q₀) :
    q ∈ affOrbit (if b then affA else affLin) (qv 0) ∨
      q ∈ affOrbit (if b then affA else affLin) (qv 3) ∨
      q ∈ affOrbit (if b then affA else affLin) (qv 1) := by
  obtain ⟨m, hm, rfl⟩ := qv_surj q
  rcases orbCert_cover b m hm with h | h | h
  · exact Or.inl (mem_affOrbit b (by simp) h)
  · exact Or.inr (Or.inl (mem_affOrbit b (by simp) h))
  · exact Or.inr (Or.inr (mem_affOrbit b (by simp) h))

theorem affOrbits_affLin :
    (affOrbit affLin (qv 0)).ncard = 1 ∧ (affOrbit affLin (qv 3)).ncard = 15 ∧
      (affOrbit affLin (qv 1)).ncard = 16 ∧
      ∀ q, q ∈ affOrbit affLin (qv 0) ∨ q ∈ affOrbit affLin (qv 3) ∨
        q ∈ affOrbit affLin (qv 1) := by
  obtain ⟨h0, h3, h1, -, -, -⟩ := orbCert_size
  exact ⟨(ncard_affOrbit false (by simp)).trans h0, (ncard_affOrbit false (by simp)).trans h3,
    (ncard_affOrbit false (by simp)).trans h1, affOrbit_cover false⟩

theorem affOrbits_affA :
    (affOrbit affA (qv 0)).ncard = 6 ∧ (affOrbit affA (qv 3)).ncard = 10 ∧
      (affOrbit affA (qv 1)).ncard = 16 ∧
      ∀ q, q ∈ affOrbit affA (qv 0) ∨ q ∈ affOrbit affA (qv 3) ∨ q ∈ affOrbit affA (qv 1) := by
  obtain ⟨-, -, -, h0, h3, h1⟩ := orbCert_size
  exact ⟨(ncard_affOrbit true (by simp)).trans h0, (ncard_affOrbit true (by simp)).trans h3,
    (ncard_affOrbit true (by simp)).trans h1, affOrbit_cover true⟩

theorem qv_nine : qv 9 = bQ 0 + bQ 3 := by
  rw [qv_eq_sum_bQ, Fin.sum_univ_five]
  have h : ∀ t : Fin 5, (9 : ℕ).testBit t = decide (t = 0 ∨ t = 3) := by decide
  simp only [h]
  simp

theorem range_gKB :
    (Set.range fun i : Fin 3 => (gKB i : CFSG.Blueprint.NativeSporadic.M22)) = {g₁, g₂, g₃} := by
  ext g
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    match i with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inr (Or.inl rfl)
    | 2 => exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

theorem pinned_M22_hexad_affine_cocycle_classification :
    B₀ ∈ ℬ₀ ∧ Nat.card KB = 5760 ∧ Module.finrank (ZMod 2) U₀ = 5 ∧
    (∀ t, bQ t = U₀.mkQ (K₀.mkQ (e ⟨basisCoord t, basisCoord_mem t⟩))) ∧
    g₁ = wordM22 [-1, 2, 2, 1] ∧ g₂ = wordM22 [-2, -1, -2, -1, -2, 1, 2, 1, 2, 1, 2] ∧
    g₃ = wordM22 [-2, -1, -2, -1, 2, 2, 1, 2, 1, 2] ∧
    g₁ = m22a⁻¹ * m22b ^ 2 * m22a ∧ g₂ = (m22b⁻¹ * m22a⁻¹) ^ 2 * m22b⁻¹ * (m22a * m22b) ^ 3 ∧
    g₃ = (m22b⁻¹ * m22a⁻¹) ^ 2 * m22b ^ 2 * (m22a * m22b) ^ 2 ∧
    Subgroup.closure {g₁, g₂, g₃} = KB ∧
    (∀ t : Fin 5, rhoQ (gKB 0) (bQ t) =
      ∑ s : Fin 5, if ([11, 8, 7, 2, 16].getD t 0).testBit s then bQ s else 0) ∧
    (∀ t : Fin 5, rhoQ (gKB 1) (bQ t) =
      ∑ s : Fin 5, if ([7, 4, 2, 8, 21].getD t 0).testBit s then bQ s else 0) ∧
    (∀ t : Fin 5, rhoQ (gKB 2) (bQ t) =
      ∑ s : Fin 5, if ([8, 2, 25, 1, 13].getD t 0).testBit s then bQ s else 0) ∧
    rhoQ.invariants = ⊥ ∧
    Module.finrank (ZMod 2) (cocycles₁ (Rep.of rhoQ)) = 6 ∧
    Module.finrank (ZMod 2) (coboundaries₁ (Rep.of rhoQ)) = 5 ∧
    IsAffineAction affLin ∧ IsAffineAction affA ∧
    (∀ q, affA (gKB 0) q = rhoQ (gKB 0) q + (bQ 0 + bQ 3)) ∧
    (∀ q, affA (gKB 1) q = rhoQ (gKB 1) q) ∧ (∀ q, affA (gKB 2) q = rhoQ (gKB 2) q) ∧
    (∀ A, IsAffineAction A →
      (∃ t, IsTranslationIso affLin A t) ∨ (∃ t, IsTranslationIso affA A t)) ∧
    (∀ t, ¬IsTranslationIso affLin affA t) ∧
    (∀ A A', IsAffineAction A → IsAffineAction A' → ∀ t t',
      IsTranslationIso A A' t → IsTranslationIso A A' t' → t = t') ∧
    ((affOrbit affLin (qv 0)).ncard = 1 ∧ (affOrbit affLin (qv 3)).ncard = 15 ∧
      (affOrbit affLin (qv 1)).ncard = 16 ∧
      ∀ q, q ∈ affOrbit affLin (qv 0) ∨ q ∈ affOrbit affLin (qv 3) ∨
        q ∈ affOrbit affLin (qv 1)) ∧
    ((affOrbit affA (qv 0)).ncard = 6 ∧ (affOrbit affA (qv 3)).ncard = 10 ∧
      (affOrbit affA (qv 1)).ncard = 16 ∧
      ∀ q, q ∈ affOrbit affA (qv 0) ∨ q ∈ affOrbit affA (qv 3) ∨ q ∈ affOrbit affA (qv 1)) := by
  refine ⟨B₀_mem_ℬ₀, natCard_KB, finrank_U₀, bQ_apply, rfl, rfl, rfl, g₁_eq, g₂_eq, g₃_eq,
    range_gKB ▸ closure_gKB, rhoQ_bQ 0, rhoQ_bQ 1, rhoQ_bQ 2, invariants_rhoQ, finrank_cocycles₁,
    finrank_coboundaries₁, isAffineAction_affLin, isAffineAction_affA, fun q => ?_, fun q => ?_,
    fun q => ?_, fun _ hA => affine_classification hA, not_isTranslationIso_affLin_affA,
    fun _ _ hA hA' _ _ ht ht' => isTranslationIso_unique hA hA' ht ht', affOrbits_affLin,
    affOrbits_affA⟩
  · rw [affA_gKB, ← qv_nine]
    rfl
  · rw [affA_gKB, show cval ((1 : Fin 3) : ℕ) = 0 from rfl, qv_zero, add_zero]
  · rw [affA_gKB, show cval ((2 : Fin 3) : ℕ) = 0 from rfl, qv_zero, add_zero]

end CFSG.Monster.B.Fischer
