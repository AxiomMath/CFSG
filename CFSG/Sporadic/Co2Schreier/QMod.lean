module

public import CFSG.Sporadic.Co2Schreier.QExtra
public import CFSG.Sporadic.Co2Schreier.SylowLemmas

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixed
open scoped Matrix

instance qcModule :
    Module (ZMod 2) (Additive (Abelianization (locQ.subgroupOf locC))) :=
  CFSG.GroupTheory.extraspecialQuotientModule qc_extraspecial

abbrev QV : Type := Additive (Abelianization (locQ.subgroupOf locC))

@[expose] def qπ (x : locQ.subgroupOf locC) : QV := Additive.ofMul (Abelianization.of x)

theorem qπ_mul (x y : locQ.subgroupOf locC) : qπ (x * y) = qπ x + qπ y := by
  simp only [qπ, map_mul, ofMul_mul]

theorem qπ_one : qπ 1 = 0 := by
  simp only [qπ, map_one, ofMul_one]

theorem qπ_inv (x : locQ.subgroupOf locC) : qπ x⁻¹ = -qπ x := by
  simp only [qπ, map_inv, ofMul_inv]

theorem qπ_eq_zero_iff
    (x : locQ.subgroupOf locC) :
    qπ x = 0 ↔ x ∈ Subgroup.center (locQ.subgroupOf locC) := by
  rw [qπ, ofMul_eq_zero, ← MonoidHom.mem_ker, Abelianization.ker_of, commutator_qc]

theorem qπ_zQc :
    qπ zQc = 0 := (qπ_eq_zero_iff _).2 zQc_mem_center

theorem qπ_surjective : Function.Surjective qπ := fun v => exists_ofMul_of v

@[expose] def qVec (k : Fin 8) : QV := qπ (qcGen k)


@[expose] def qcCoord : (Fin 8 → ZMod 2) →ₗ[ZMod 2] QV := Fintype.linearCombination (ZMod 2) qVec

theorem qcCoord_apply (f : Fin 8 → ZMod 2) : qcCoord f = ∑ k, f k • qVec k := rfl

theorem qcCoord_single (l : Fin 8) : qcCoord (Pi.single l 1) = qπ (qcGen l) := by
  rw [qcCoord, Fintype.linearCombination_apply_single, one_smul]
  rfl

theorem qπ_mem_span
    (x : locQ.subgroupOf locC) :
    qπ x ∈ Submodule.span (ZMod 2) (Set.range qVec) := by
  have hx : x ∈ Subgroup.closure qcGens := qcGens_closure ▸ Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := mem_qcGens hx
    exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
  | one =>
    rw [qπ_one]
    exact Submodule.zero_mem _
  | mul x y _ _ hx hy =>
    rw [qπ_mul]
    exact Submodule.add_mem _ hx hy
  | inv x _ hx =>
    rw [qπ_inv]
    exact Submodule.neg_mem _ hx

theorem qcCoord_surjective :
    Function.Surjective qcCoord := by
  rw [← LinearMap.range_eq_top, qcCoord, Fintype.range_linearCombination, eq_top_iff]
  intro v _
  obtain ⟨x, rfl⟩ := qπ_surjective v
  exact qπ_mem_span x

theorem card_QV :
    Nat.card QV = 256 := by
  have h := (commutator (locQ.subgroupOf locC)).card_eq_card_quotient_mul_card_subgroup
  have h2 : Nat.card (commutator (locQ.subgroupOf locC)) = 2 := by
    rw [commutator_qc, card_center_qc]
  rw [card_qc, h2] at h
  change Nat.card (locQ.subgroupOf locC ⧸ commutator (locQ.subgroupOf locC)) = 256
  omega

theorem qcCoord_bijective :
    Function.Bijective qcCoord := by
  refine (Nat.bijective_iff_surjective_and_card _).2 ⟨qcCoord_surjective, ?_⟩
  rw [card_QV, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

@[expose] def qcEquiv :
    (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] QV :=
  LinearEquiv.ofBijective qcCoord qcCoord_bijective

theorem qcEquiv_apply
    (f : Fin 8 → ZMod 2) : qcEquiv f = qcCoord f := rfl

theorem finrank_QV :
    Module.finrank (ZMod 2) QV = 8 := by
  rw [← qcEquiv.finrank_eq, Module.finrank_fin_fun]

theorem exists_toVecD (f : Fin 8 → ZMod 2) : ∃ a < 256, toVecD 8 a = f := by
  refine ⟨ofBits 8 fun k => if h : k < 8 then decide (f ⟨k, h⟩ = 1) else false,
    ofBits_lt 8 _, funext fun j => ?_⟩
  rw [toVecD_ofBits]
  simp only [j.2, ↓reduceDIte, Fin.eta]
  rcases zmod_two_cases (f j) with h | h <;> simp [h]

theorem exists_qcCoord
    (v : QV) : ∃ a < 256, qcCoord (toVecD 8 a) = v := by
  obtain ⟨f, rfl⟩ := qcCoord_surjective v
  obtain ⟨a, ha, rfl⟩ := exists_toVecD f
  exact ⟨a, ha, rfl⟩

theorem qcCoord_toVecD_injective
    {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (h : qcCoord (toVecD 8 a) = qcCoord (toVecD 8 b)) : a = b :=
  toVecD_injective (d := 8) ha hb (qcCoord_bijective.1 h)

theorem prodList_mem_Q (l : List ℕ) : prodList qTuple l ∈ locQ :=
  prodList_mem (fun _ hg => Subgroup.subset_closure hg) l

theorem qπ_prodList (l : List ℕ) :
    qπ (toQc (prodList qTuple l) (prodList_mem_Q l)) = (l.map fun k => qπ (qcGen k)).sum := by
  induction l with
  | nil =>
    have h1 : toQc (prodList qTuple []) (prodList_mem_Q []) = 1 :=
      Subtype.ext (Subtype.ext rfl)
    rw [h1, qπ_one]
    simp
  | cons k l ih =>
    rw [List.map_cons, List.sum_cons, ← ih, ← qπ_mul]
    rfl

theorem sum_filter_range {M : Type*} [AddCommMonoid M] (p : ℕ → Bool) (v : ℕ → M) :
    ∀ n, (((List.range n).filter p).map v).sum = ∑ k ∈ Finset.range n, if p k then v k else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append,
      sum_filter_range p v n, Finset.sum_range_succ]
    congr 1
    by_cases h : p n <;> simp [h]

theorem qcCoord_toVecD (w : ℕ) :
    qcCoord (toVecD 8 w) = ((bits8 w).map fun k => qπ (qcGen k)).sum := by
  rw [bits8, sum_filter_range, qcCoord_apply, Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [toVecD_apply, qVec]
  split_ifs <;> simp

theorem qπ_prod_bits8 (w : ℕ) :
    qπ (toQc (prodList qTuple (bits8 w)) (prodList_mem_Q _)) = qcCoord (toVecD 8 w) := by
  rw [qπ_prodList, qcCoord_toVecD]

theorem conjEnd_qπ (g : locC) (x : locQ.subgroupOf locC) :
    conjEnd (Q := locQ.subgroupOf locC) g (qπ x) = qπ (MulAut.conjNormal g x) := rfl

theorem coe_conjNormal_qc (g : locC) (x : locQ.subgroupOf locC) :
    (((MulAut.conjNormal g x : locQ.subgroupOf locC) : locC) : Equiv.Perm (Fin 2300)) =
      (g : Equiv.Perm (Fin 2300)) * ((x : locC) : Equiv.Perm (Fin 2300)) *
        (g : Equiv.Perm (Fin 2300))⁻¹ := by
  rw [MulAut.conjNormal_apply]
  rfl

theorem rep_conj_qcGen
    {i l : ℕ} (hi : i < 2) (hl : l < 8) :
    Rep 2300 (compA 2300 (compA 2300 cArrs[i]! qArrs[l]!) (invCand 2300 cArrs[i]!))
      (((MulAut.conjNormal (cGen i) (qcGen l) : locQ.subgroupOf locC) : locC) :
        Equiv.Perm (Fin 2300)) := by
  have hc := repTuple_c.rep (show i < cTuple.length by rw [cTuple_length]; exact hi)
  have hcinv := rep_inv_of_isInvA hc (allInv_spec wordFacts.invC (wordFacts.sizeC ▸ hi))
  rw [coe_conjNormal_qc]
  exact rep_compA (rep_compA hc (rep_qcGen hl)) hcinv

theorem conjEnd_qVec
    {i l : ℕ} (hi : i < 2) (hl : l < 8) :
    conjEnd (Q := locQ.subgroupOf locC) (cGen i) (qπ (qcGen l)) =
      qcCoord (toVecD 8 (qCol witRec i l)) := by
  rw [conjEnd_qπ, ← qπ_prod_bits8]
  have h := (qmod_conj hi hl).2
  have hrep := rep_conj_qcGen hi hl
  have hp := rep_prodArr repTuple_q (l := bits8 (qCol witRec i l)) (fun k hk => by
    rw [qTuple_length]
    exact List.mem_range.1 (List.mem_filter.1 hk).1)
  rw [isProdOrZ, qProdArr, Bool.or_eq_true] at h
  rcases h with h | h
  · congr 1
    exact Subtype.ext (Subtype.ext (eq_of_eqA hrep hp h))
  · have he : MulAut.conjNormal (cGen i) (qcGen l) =
        toQc (prodList qTuple (bits8 (qCol witRec i l))) (prodList_mem_Q _) * zQc :=
      Subtype.ext (Subtype.ext (eq_of_eqA hrep (rep_compA hp rep_z) h))
    rw [he, qπ_mul, qπ_zQc, add_zero]

@[expose] def qMat (i : ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 2) := rowsMatrix 8 (qActRows witRec i)

theorem qMat_mulVec_single (i : ℕ) (l : Fin 8) :
    qMat i *ᵥ Pi.single l 1 = toVecD 8 (qCol witRec i l) := by
  rw [Matrix.mulVec_single_one]
  change (qMat i)ᵀ l = _
  rw [qMat, ← rowsMatrix_transposeRows]
  rfl

theorem qcCoord_mulVec
    {i : ℕ} (hi : i < 2) (f : Fin 8 → ZMod 2) :
    qcCoord (qMat i *ᵥ f) = conjEnd (Q := locQ.subgroupOf locC) (cGen i) (qcCoord f) := by
  have key : qcCoord ∘ₗ (qMat i).mulVecLin =
      conjEnd (Q := locQ.subgroupOf locC) (cGen i) ∘ₗ qcCoord := by
    refine (Pi.basisFun (ZMod 2) (Fin 8)).ext fun l => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Pi.basisFun_apply, Matrix.mulVecLin_apply,
      qMat_mulVec_single, qcCoord_single, conjEnd_qVec hi l.2]
  exact LinearMap.congr_fun key f

theorem qcCoord_vecMulN
    {i : ℕ} (hi : i < 2) (a : ℕ) :
    qcCoord (toVecD 8 (vecMulN 8 (qActCols witRec i) a)) =
      conjEnd (Q := locQ.subgroupOf locC) (cGen i) (qcCoord (toVecD 8 a)) := by
  rw [qActCols, ← rowsMatrix_mulVec, ← qcCoord_mulVec hi]
  rfl

@[expose] def BitsIn (P : ℕ → Prop) (S : ℕ) : Prop := ∀ a, S.testBit a = true → P a

theorem foldl_invariant {α β : Type*} (I : β → Prop) (f : β → α → β)
    (hf : ∀ b a, I b → I (f b a)) : ∀ (l : List α) (b : β), I b → I (l.foldl f b)
  | [], _, hb => hb
  | a :: l, b, hb => foldl_invariant I f hf l (f b a) (hf b a hb)

theorem bitsIn_or {P : ℕ → Prop} {S y : ℕ} (hS : BitsIn P S) (hy : P y) :
    BitsIn P (S ||| (1 <<< y)) := by
  intro a ha
  rw [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow,
    decide_eq_true_eq] at ha
  rcases ha with ha | ha
  · exact hS a ha
  · exact ha ▸ hy

theorem bitsIn_one {P : ℕ → Prop} (h0 : P 0) : BitsIn P 1 := by
  intro a ha
  rw [show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow, decide_eq_true_eq] at ha
  exact ha ▸ h0

theorem bitsIn_full {P : ℕ → Prop} (h : BitsIn P (2 ^ 256 - 1)) {a : ℕ} (ha : a < 256) : P a :=
  h a (by rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]; exact ha)

section BitSpan

variable {P : ℕ → Prop} (hxor : ∀ a b, P a → P b → P (a ^^^ b))
include hxor

theorem bitsIn_spanIns {S x : ℕ} (hS : BitsIn P S) (hx : P x) : BitsIn P (spanIns S x) := by
  unfold spanIns
  split_ifs
  · exact hS
  · refine foldl_invariant (BitsIn P) _ (fun acc a hacc => ?_) _ S hS
    split_ifs with ha
    · exact bitsIn_or hacc (hxor a x (hS a ha) hx)
    · exact hacc

theorem bitsIn_spanStep {T0 T1 : Array ℕ} (h0 : ∀ a, P a → P (vecMulN 8 T0 a))
    (h1 : ∀ a, P a → P (vecMulN 8 T1 a)) {S : ℕ} (hS : BitsIn P S) :
    BitsIn P (spanStep T0 T1 S) := by
  unfold spanStep
  refine foldl_invariant (BitsIn P) _ (fun acc a hacc => ?_) _ S hS
  split_ifs with ha
  · exact bitsIn_spanIns hxor (bitsIn_spanIns hxor hacc (h0 a (hS a ha))) (h1 a (hS a ha))
  · exact hacc

theorem bitsIn_spanIter {T0 T1 : Array ℕ} (h0 : ∀ a, P a → P (vecMulN 8 T0 a))
    (h1 : ∀ a, P a → P (vecMulN 8 T1 a)) :
    ∀ (n : ℕ) {S : ℕ}, BitsIn P S → BitsIn P (spanIter T0 T1 n S)
  | 0, _, hS => hS
  | n + 1, _, hS => bitsIn_spanIter h0 h1 n (bitsIn_spanStep hxor h0 h1 hS)

end BitSpan

theorem qmod_irreducible
    (W : Submodule (ZMod 2) QV)
    (hW0 : ∀ w ∈ W, conjEnd (Q := locQ.subgroupOf locC) (cGen 0) w ∈ W)
    (hW1 : ∀ w ∈ W, conjEnd (Q := locQ.subgroupOf locC) (cGen 1) w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨a, ha, rfl⟩ := exists_qcCoord w
  set P : ℕ → Prop := fun b => qcCoord (toVecD 8 b) ∈ W with hP
  have hxor : ∀ b c, P b → P c → P (b ^^^ c) := fun b c hb hc => by
    simp only [hP, toVecD_xor, map_add] at hb hc ⊢
    exact W.add_mem hb hc
  have hT : ∀ i < 2, ∀ b, P b → P (vecMulN 8 (qActCols witRec i) b) := fun i hi b hb => by
    simp only [hP] at hb ⊢
    rw [qcCoord_vecMulN hi]
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact hW0 _ hb
    · exact hW1 _ hb
  have h0 : P 0 := by
    simp only [hP, toVecD_zero, map_zero]
    exact W.zero_mem
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [toVecD_zero, map_zero])
  obtain ⟨v, rfl⟩ : ∃ v, a = v + 1 := ⟨a - 1, by omega⟩
  have hfull := bitsIn_spanIter hxor (hT 0 (by norm_num)) (hT 1 (by norm_num)) 8
    (bitsIn_spanIns hxor (bitsIn_one h0) hwW)
  rw [qmod_span (by omega)] at hfull
  refine eq_top_iff.2 fun u _ => ?_
  obtain ⟨b, hb, rfl⟩ := exists_qcCoord u
  exact bitsIn_full hfull hb

@[expose] def thetaV : Module.End (ZMod 2) QV :=
  1 + conjEnd (Q := locQ.subgroupOf locC) (cGen 0) + conjEnd (Q := locQ.subgroupOf locC) (cGen 1)

theorem thetaV_qcCoord
    (a : ℕ) :
    thetaV (qcCoord (toVecD 8 a)) = qcCoord (toVecD 8 (thetaN witRec a)) := by
  rw [thetaN, toVecD_xor, toVecD_xor, map_add, map_add, qcCoord_vecMulN (i := 0) (by norm_num),
    qcCoord_vecMulN (i := 1) (by norm_num), thetaV, LinearMap.add_apply, LinearMap.add_apply,
    Module.End.one_apply]

@[expose] def kV : QV := qcCoord (toVecD 8 218)

theorem kV_ne_zero :
    kV ≠ 0 := by
  intro h
  have : qcCoord (toVecD 8 218) = qcCoord (toVecD 8 0) := by
    rw [toVecD_zero, map_zero]
    exact h
  exact absurd (qcCoord_toVecD_injective (by norm_num) (by norm_num) this) (by norm_num)

theorem thetaV_kV :
    thetaV kV = 0 := by
  rw [kV, thetaV_qcCoord, qmod_theta218, toVecD_zero, map_zero]

theorem eq_of_thetaV_eq_zero
    {v : QV} (hv : thetaV v = 0) : v = 0 ∨ v = kV := by
  obtain ⟨a, ha, rfl⟩ := exists_qcCoord v
  rw [thetaV_qcCoord] at hv
  have h1 : qcCoord (toVecD 8 (thetaN witRec a)) = qcCoord (toVecD 8 0) := by
    rw [toVecD_zero, map_zero]
    exact hv
  rcases qmod_theta ha (qcCoord_toVecD_injective (qmod_theta_lt ha) (by norm_num) h1) with
    rfl | rfl
  · left
    rw [toVecD_zero, map_zero]
  · right
    rfl

theorem eq_zero_of_commute_of_kV
    {Y : Module.End (ZMod 2) QV}
    (h0 : Y * conjEnd (Q := locQ.subgroupOf locC) (cGen 0) =
      conjEnd (Q := locQ.subgroupOf locC) (cGen 0) * Y)
    (h1 : Y * conjEnd (Q := locQ.subgroupOf locC) (cGen 1) =
      conjEnd (Q := locQ.subgroupOf locC) (cGen 1) * Y) (hk : Y kV = 0) : Y = 0 := by
  have hinv : ∀ i < 2, ∀ w ∈ LinearMap.ker Y,
      conjEnd (Q := locQ.subgroupOf locC) (cGen i) w ∈ LinearMap.ker Y := by
    intro i hi w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [← Module.End.mul_apply]
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [h0, Module.End.mul_apply, hw, map_zero]
    · rw [h1, Module.End.mul_apply, hw, map_zero]
  rcases qmod_irreducible (LinearMap.ker Y) (hinv 0 (by norm_num)) (hinv 1 (by norm_num)) with
    h | h
  · exact absurd (h ▸ LinearMap.mem_ker.2 hk : kV ∈ (⊥ : Submodule (ZMod 2) QV))
      (by rw [Submodule.mem_bot]; exact kV_ne_zero)
  · exact LinearMap.ker_eq_top.1 h

theorem qmod_commutant
    (X : Module.End (ZMod 2) QV)
    (h0 : X * conjEnd (Q := locQ.subgroupOf locC) (cGen 0) =
      conjEnd (Q := locQ.subgroupOf locC) (cGen 0) * X)
    (h1 : X * conjEnd (Q := locQ.subgroupOf locC) (cGen 1) =
      conjEnd (Q := locQ.subgroupOf locC) (cGen 1) * X) : X = 0 ∨ X = 1 := by
  have hθ : X * thetaV = thetaV * X := by
    rw [thetaV, mul_add, mul_add, add_mul, add_mul, h0, h1, mul_one, one_mul]
  have hXk : thetaV (X kV) = 0 := by
    rw [← Module.End.mul_apply, ← hθ, Module.End.mul_apply, thetaV_kV, map_zero]
  rcases eq_of_thetaV_eq_zero hXk with h | h
  · exact Or.inl (eq_zero_of_commute_of_kV h0 h1 h)
  · right
    have hY := eq_zero_of_commute_of_kV (Y := X - 1)
      (by rw [sub_mul, mul_sub, h0, mul_one, one_mul])
      (by rw [sub_mul, mul_sub, h1, mul_one, one_mul])
      (by rw [LinearMap.sub_apply, h, Module.End.one_apply, sub_self])
    exact sub_eq_zero.1 hY

theorem qπ_qcGen_zero : qπ (qcGen 0) = qcCoord (toVecD 8 1) := by
  rw [qcCoord_toVecD, show bits8 1 = [0] by decide]
  simp

theorem conjEnd_conj (g c : locC) (v : QV) :
    conjEnd (Q := locQ.subgroupOf locC) g (conjEnd (Q := locQ.subgroupOf locC) c v) =
      conjEnd (Q := locQ.subgroupOf locC) (g * c * g⁻¹)
        (conjEnd (Q := locQ.subgroupOf locC) g v) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]

theorem qmod_commutator_span :
    Submodule.span (ZMod 2) {w : QV | ∃ (c : locC) (v : QV),
      w = conjEnd (Q := locQ.subgroupOf locC) c v - v} = ⊤ := by
  set U := Submodule.span (ZMod 2) {w : QV | ∃ (c : locC) (v : QV),
      w = conjEnd (Q := locQ.subgroupOf locC) c v - v} with hU
  have hinv : ∀ g : locC, ∀ w ∈ U, conjEnd (Q := locQ.subgroupOf locC) g w ∈ U := by
    intro g w hw
    have hle : U ≤ U.comap (conjEnd (Q := locQ.subgroupOf locC) g) := by
      rw [hU, Submodule.span_le]
      rintro _ ⟨c, v, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, conjEnd_conj]
      exact Submodule.subset_span ⟨_, _, rfl⟩
    exact hle hw
  rcases qmod_irreducible U (hinv _) (hinv _) with h | h
  · exfalso
    have hmem : conjEnd (Q := locQ.subgroupOf locC) (cGen 0) (qπ (qcGen 0)) - qπ (qcGen 0) ∈ U :=
      Submodule.subset_span ⟨_, _, rfl⟩
    rw [h, Submodule.mem_bot, sub_eq_zero, conjEnd_qVec (i := 0) (l := 0) (by norm_num)
      (by norm_num), qmod_col00, qπ_qcGen_zero] at hmem
    exact absurd (qcCoord_toVecD_injective (by norm_num) (by norm_num) hmem) (by norm_num)
  · exact h

end CFSG.Sporadic.Co2Schreier
