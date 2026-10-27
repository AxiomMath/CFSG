module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5

open Subgroup

open scoped IsMulCommutative commutatorElement

private theorem sz5e1_lcm_comm_mem {D : Type} [Group D] (P : Subgroup D) [P.Normal]
    (Z : Subgroup (D ⧸ P)) (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (a b : D) (ha : (a : D ⧸ P) ∈ Z) (hb : (b : D ⧸ P) ∈ Z) :
    ⁅a, b⁆ ∈ P := by
  rw [← QuotientGroup.eq_one_iff]
  change QuotientGroup.mk' P ⁅a, b⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (hZc _ ha _ hb)

private theorem sz5e1_lcm_comm_sq {D : Type} [Group D] (P : Subgroup D) [P.Normal]
    (hPc : ∀ p ∈ P, ∀ d : D, p * d = d * p)
    (Z : Subgroup (D ⧸ P)) (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hZ2 : ∀ a ∈ Z, a ^ 2 = 1)
    (a b : D) (ha : (a : D ⧸ P) ∈ Z) (hb : (b : D ⧸ P) ∈ Z) :
    ⁅a, b⁆ ^ 2 = 1 := by
  have hmem : ⁅a, b⁆ ∈ P := sz5e1_lcm_comm_mem P Z hZc a b ha hb
  have ha2 : a ^ 2 ∈ P := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' P (a ^ 2) = 1
    rw [map_pow]
    simpa using hZ2 _ ha
  have h1 : ⁅a ^ 2, b⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hPc (a^2) ha2 b
  have hc : Commute a ⁅a, b⁆ := by
    rw [commute_iff_eq]
    exact (hPc ⁅a, b⁆ hmem a).symm
  rw [Commute.commutatorElement_pow_left hc 2, h1]

private lemma sz5e1_lcm_indicator {D : Type} [Group D] (P : Subgroup D) [DecidableEq P]
    (hΩ : ∀ p ∈ P, ∀ q ∈ P, p ^ 2 = 1 → q ^ 2 = 1 → p = 1 ∨ q = 1 ∨ p = q)
    {x y : P} (hx : (x : D) ^ 2 = 1) (hy : (y : D) ^ 2 = 1) :
    (if x * y = 1 then (0 : ZMod 2) else 1)
      = (if x = 1 then 0 else 1) + (if y = 1 then 0 else 1) := by
  classical
  by_cases hx1 : x = 1
  · subst hx1; simp
  by_cases hy1 : y = 1
  · subst hy1; simp
  have hxy : x = y := by
    rcases hΩ (x : D) x.2 (y : D) y.2 hx hy with h | h | h
    · exact absurd (Subtype.ext h) hx1
    · exact absurd (Subtype.ext h) hy1
    · exact Subtype.ext h
  subst hxy
  have hx2 : x * x = 1 := Subtype.ext (by simpa [pow_two] using hy)
  rw [hx2]
  simp only [if_true, hx1, if_false]
  decide

private theorem sz5e1_lcm_form {D : Type} [Group D] [Finite D] (P : Subgroup D) [P.Normal]
    (hPc : ∀ p ∈ P, ∀ d : D, p * d = d * p)
    (hΩ : ∀ p ∈ P, ∀ q ∈ P, p ^ 2 = 1 → q ^ 2 = 1 → p = 1 ∨ q = 1 ∨ p = q)
    (Z : Subgroup (D ⧸ P)) (hZ8 : Nat.card Z = 8)
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZ2 : ∀ a ∈ Z, a ^ 2 = 1)
    (yb : D ⧸ P) (hy7 : orderOf yb = 7) (hyZ : ∀ z ∈ Z, yb * z * yb⁻¹ ∈ Z)
    (hyf : ∀ z ∈ Z, yb * z * yb⁻¹ = z → z = 1) :
    ∀ a b : D, (a : D ⧸ P) ∈ Z → (b : D ⧸ P) ∈ Z → a * b = b * a := by
  classical
  have hQ : Finite (D ⧸ P) :=
    Finite.of_surjective (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
  have hcomm_mem : ∀ a b : D, (a : D ⧸ P) ∈ Z → (b : D ⧸ P) ∈ Z → ⁅a, b⁆ ∈ P :=
    fun a b ha hb => sz5e1_lcm_comm_mem P Z hZc a b ha hb
  have hcomm_sq : ∀ a b : D, (a : D ⧸ P) ∈ Z → (b : D ⧸ P) ∈ Z → ⁅a, b⁆ ^ 2 = 1 :=
    fun a b ha hb => sz5e1_lcm_comm_sq P hPc Z hZc hZ2 a b ha hb
  let sec : Z → D := fun z => Classical.choose (QuotientGroup.mk'_surjective P (z : D ⧸ P))
  have hsec : ∀ z : Z, ((sec z : D) : D ⧸ P) = (z : D ⧸ P) :=
    fun z => Classical.choose_spec (QuotientGroup.mk'_surjective P (z : D ⧸ P))
  let y0 : D := Classical.choose (QuotientGroup.mk'_surjective P yb)
  have hy0 : ((y0 : D) : D ⧸ P) = yb :=
    Classical.choose_spec (QuotientGroup.mk'_surjective P yb)
  have ind1 : ∀ (a a' b : D), (a : D ⧸ P) = (a' : D ⧸ P) → ⁅a, b⁆ = ⁅a', b⁆ := by
    intro a a' b h
    have hp : a⁻¹ * a' ∈ P := by
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' P (a⁻¹ * a') = 1
      rw [map_mul, map_inv, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, h]
      simp
    have ha' : a' = a * (a⁻¹ * a') := by group
    rw [ha', commutatorElement_mul_left_eq_conj_mul]
    have h1 : ⁅a⁻¹ * a', b⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hPc _ hp b)
    rw [h1]; simp
  have ind2 : ∀ (a b b' : D), (b : D ⧸ P) = (b' : D ⧸ P) → ⁅a, b⁆ = ⁅a, b'⁆ := by
    intro a b b' h
    have hq : b⁻¹ * b' ∈ P := by
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' P (b⁻¹ * b') = 1
      rw [map_mul, map_inv, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, h]
      simp
    have hb' : b' = b * (b⁻¹ * b') := by group
    rw [hb', commutatorElement_mul_right_eq_mul_conj]
    have h1 : ⁅a, b⁻¹ * b'⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hPc _ hq a).symm
    rw [h1]; simp
  have hmemc : ∀ z w : Z, ⁅sec z, sec w⁆ ∈ P := fun z w =>
    hcomm_mem (sec z) (sec w) (by rw [hsec z]; exact (z:Z).2) (by rw [hsec w]; exact (w:Z).2)
  let cval : Z → Z → P := fun z w => ⟨⁅sec z, sec w⁆, hmemc z w⟩
  have cval_coe : ∀ z w : Z, (cval z w : D) = ⁅sec z, sec w⁆ := fun _ _ => rfl
  have hval : ∀ (a b : D) (z w : Z), (a : D ⧸ P) = (z : D ⧸ P) → (b : D ⧸ P) = (w : D ⧸ P) →
      ⁅a, b⁆ = (cval z w : D) := by
    intro a b z w haz hbw
    have h1 : ⁅a, sec w⁆ = ⁅sec z, sec w⁆ := ind1 a (sec z) (sec w) (by rw [haz, hsec z])
    have h2 : ⁅a, b⁆ = ⁅a, sec w⁆ := ind2 a b (sec w) (by rw [hbw, hsec w])
    rw [h2, h1]
  have cval_sq : ∀ z w : Z, (cval z w : D) ^ 2 = 1 := fun z w =>
    hcomm_sq (sec z) (sec w) (by rw [hsec z]; exact (z:Z).2) (by rw [hsec w]; exact (w:Z).2)
  let phi : Z → Z → ZMod 2 := fun z w => if cval z w = 1 then 0 else 1
  have phi_def : ∀ z w : Z, phi z w = if cval z w = 1 then 0 else 1 := fun _ _ => rfl
  have phi_eq_zero_iff : ∀ z w : Z, phi z w = 0 ↔ cval z w = 1 := by
    intro z w
    rw [phi_def]
    by_cases h : cval z w = 1
    · simp [h]
    · simp [h]
  have cval_comm : ∀ z w : Z, cval z w = cval w z := by
    intro z w
    apply Subtype.ext
    change ⁅sec z, sec w⁆ = ⁅sec w, sec z⁆
    have h2 : (cval z w : D) * (cval z w : D) = 1 := by
      rw [← pow_two]; exact cval_sq z w
    have hinv : ⁅sec w, sec z⁆ = (⁅sec z, sec w⁆)⁻¹ := (commutatorElement_inv (sec z) (sec w)).symm
    rw [hinv]
    exact (inv_eq_of_mul_eq_one_right h2).symm
  have phi_symm : ∀ z w : Z, phi z w = phi w z := by
    intro z w
    rw [phi_def, phi_def, cval_comm]
  have hsec1 : (sec 1 : D) ∈ P := by
    rw [← QuotientGroup.eq_one_iff, hsec 1]
    rfl
  have phi_one_left : ∀ w : Z, phi 1 w = 0 := by
    intro w
    have h : cval 1 w = 1 := by
      apply Subtype.ext
      change ⁅sec 1, sec w⁆ = (1 : D)
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hPc _ hsec1 (sec w))
    rw [phi_eq_zero_iff]; exact h
  have phi_one_right : ∀ z : Z, phi z 1 = 0 := by
    intro z
    have h : cval z 1 = 1 := by
      apply Subtype.ext
      change ⁅sec z, sec 1⁆ = (1 : D)
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hPc _ hsec1 (sec z)).symm
    rw [phi_eq_zero_iff]; exact h
  have phi_alt : ∀ z : Z, phi z z = 0 := by
    intro z
    have h : cval z z = 1 := by
      apply Subtype.ext
      change ⁅sec z, sec z⁆ = (1 : D)
      rw [commutatorElement_self]
    rw [phi_eq_zero_iff]; exact h
  have cval_mul_left : ∀ z w v : Z, cval (z * w) v = cval w v * cval z v := by
    intro z w v
    apply Subtype.ext
    change ⁅sec (z * w), sec v⁆ = ⁅sec w, sec v⁆ * ⁅sec z, sec v⁆
    have hsame : ((sec (z * w) : D) : D ⧸ P) = ((sec z * sec w : D) : D ⧸ P) := by
      rw [hsec]
      rw [show ((z * w : Z) : D ⧸ P) = (z : D ⧸ P) * (w : D ⧸ P) from rfl]
      rw [show ((sec z * sec w : D) : D ⧸ P) = ((sec z : D) : D ⧸ P) * ((sec w : D) : D ⧸ P) from rfl]
      rw [hsec z, hsec w]
    rw [ind1 _ _ _ hsame, commutatorElement_mul_left_eq_conj_mul]
    have hcw : ⁅sec w, sec v⁆ ∈ P := hmemc w v
    rw [show sec z * ⁅sec w, sec v⁆ * (sec z)⁻¹ = ⁅sec w, sec v⁆ by
          rw [(hPc _ hcw (sec z)).symm]; group]
  have cval_mul_right : ∀ z w v : Z, cval z (w * v) = cval z w * cval z v := by
    intro z w v
    apply Subtype.ext
    change ⁅sec z, sec (w * v)⁆ = ⁅sec z, sec w⁆ * ⁅sec z, sec v⁆
    have hsame : ((sec (w * v) : D) : D ⧸ P) = ((sec w * sec v : D) : D ⧸ P) := by
      rw [hsec]
      rw [show ((w * v : Z) : D ⧸ P) = (w : D ⧸ P) * (v : D ⧸ P) from rfl]
      rw [show ((sec w * sec v : D) : D ⧸ P) = ((sec w : D) : D ⧸ P) * ((sec v : D) : D ⧸ P) from rfl]
      rw [hsec w, hsec v]
    rw [ind2 _ _ _ hsame, commutatorElement_mul_right_eq_mul_conj]
    have hcv : ⁅sec z, sec v⁆ ∈ P := hmemc z v
    have hcen : sec w * ⁅sec z, sec v⁆ * (sec w)⁻¹ = ⁅sec z, sec v⁆ := by
      rw [(hPc _ hcv (sec w)).symm]; group
    rw [show ⁅sec z, sec w⁆ * sec w * ⁅sec z, sec v⁆ * (sec w)⁻¹
          = ⁅sec z, sec w⁆ * (sec w * ⁅sec z, sec v⁆ * (sec w)⁻¹) by group, hcen]
  have phi_mul_left : ∀ z w v : Z, phi (z * w) v = phi z v + phi w v := by
    intro z w v
    rw [phi_def, phi_def, phi_def, cval_mul_left, add_comm]
    exact sz5e1_lcm_indicator P hΩ (cval_sq w v) (cval_sq z v)
  have phi_mul_right : ∀ z w v : Z, phi z (w * v) = phi z w + phi z v := by
    intro z w v
    rw [phi_def, phi_def, phi_def, cval_mul_right]
    exact sz5e1_lcm_indicator P hΩ (cval_sq z w) (cval_sq z v)
  have phi_pow_left : ∀ (z : Z) (n : ℕ) (w : Z), phi (z ^ n) w = n • phi z w := by
    intro z n w
    induction n with
    | zero => simp [phi_one_left]
    | succ n ih => rw [pow_succ, phi_mul_left, ih]; rfl
  have phi_inv_left : ∀ z w : Z, phi z⁻¹ w = phi z w := by
    intro z w
    have h := phi_mul_left z z⁻¹ w
    rw [mul_inv_cancel, phi_one_left] at h
    have h' : phi z w + phi z⁻¹ w = 0 := h.symm
    exact add_left_cancel (h'.trans (CharTwo.add_self_eq_zero (phi z w)).symm)
  have phi_inv_right : ∀ z w : Z, phi z w⁻¹ = phi z w := by
    intro z w
    have h := phi_mul_right z w w⁻¹
    rw [mul_inv_cancel, phi_one_right] at h
    have h' : phi z w + phi z w⁻¹ = 0 := h.symm
    exact add_left_cancel (h'.trans (CharTwo.add_self_eq_zero (phi z w)).symm)
  let Sr : Z → Subgroup Z := fun z =>
    { carrier := {w | phi z w = 0}
      one_mem' := phi_one_right z
      mul_mem' := fun {a b} ha hb => show phi z (a * b) = 0 by rw [phi_mul_right, ha, hb, add_zero]
      inv_mem' := fun {a} ha => show phi z a⁻¹ = 0 by rw [phi_inv_right, ha] }
  let R : Subgroup Z :=
    { carrier := {z | ∀ w, phi z w = 0}
      one_mem' := phi_one_left
      mul_mem' := fun {a b} ha hb w => show phi (a * b) w = 0 by rw [phi_mul_left, ha w, hb w, add_zero]
      inv_mem' := fun {a} ha w => show phi a⁻¹ w = 0 by rw [phi_inv_left, ha w] }
  have : IsMulCommutative Z :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (hZc _ a.2 _ b.2))
  have : Fintype Z := Fintype.ofFinite Z
  have : Module (ZMod 2) (Additive Z) :=
    AddCommGroup.zmodModule (fun x => by
      apply Additive.ext
      rw [toMul_nsmul, toMul_zero]
      exact Subtype.ext (by simpa using hZ2 (x.toMul : D ⧸ P) (x.toMul).2))
  have hfin : Module.finrank (ZMod 2) (Additive Z) = 3 := by
    have hc : Nat.card (Additive Z) = 2 ^ Module.finrank (ZMod 2) (Additive Z) := by
      simpa using Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive Z)
    have h8 : 2 ^ Module.finrank (ZMod 2) (Additive Z) = 2 ^ 3 := by
      rw [← hc, ← Nat.card_congr Additive.ofMul, hZ8]
      norm_num
    exact Nat.pow_right_injective (by norm_num) h8
  let B : Module.Basis (Fin 3) (ZMod 2) (Additive Z) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive Z) hfin
  let x : Fin 3 → Z := fun i => (B i).toMul
  have hxgen : Subgroup.closure (Set.range x) = ⊤ := by
    have hspan : Submodule.span (ZMod 2) (Set.range B) ≤
        AddSubgroup.toZModSubmodule 2 (Subgroup.closure (Set.range x)).toAddSubgroup := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change B i ∈ AddSubgroup.toZModSubmodule 2 (Subgroup.closure (Set.range x)).toAddSubgroup
      rw [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have htop : (⊤ : Submodule (ZMod 2) (Additive Z)) ≤
        AddSubgroup.toZModSubmodule 2 (Subgroup.closure (Set.range x)).toAddSubgroup := by
      rw [← Module.Basis.span_eq B]
      exact hspan
    apply eq_top_iff.mpr
    intro y _
    have hmem : Additive.ofMul y ∈
        AddSubgroup.toZModSubmodule 2 (Subgroup.closure (Set.range x)).toAddSubgroup := htop trivial
    rw [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup] at hmem
    simpa using hmem
  have hyZinv : ∀ z ∈ Z, yb⁻¹ * z * yb ∈ Z := by
    intro z hz
    let f : Z → Z := fun w => ⟨yb * (w : D ⧸ P) * yb⁻¹, hyZ w w.2⟩
    have hfinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      exact (MulAut.conj yb).injective (Subtype.ext_iff.mp hab)
    have hfsurj : Function.Surjective f := Finite.surjective_of_injective hfinj
    obtain ⟨w, hw⟩ := hfsurj ⟨z, hz⟩
    have hw' : yb * (w : D ⧸ P) * yb⁻¹ = z := congrArg Subtype.val hw
    have : (w : D ⧸ P) = yb⁻¹ * z * yb := by rw [← hw']; group
    rw [← this]; exact w.2
  let conj : Z → Z := fun z => ⟨yb * (z : D ⧸ P) * yb⁻¹, hyZ _ z.2⟩
  let conjInv : Z → Z := fun z => ⟨yb⁻¹ * (z : D ⧸ P) * yb, hyZinv _ z.2⟩
  have hconj_inj : Function.Injective conj := by
    intro a b hab
    apply Subtype.ext
    exact (MulAut.conj yb).injective (Subtype.ext_iff.mp hab)
  have hconj_inv : ∀ z : Z, conj (conjInv z) = z := by
    intro z; apply Subtype.ext; change yb * (yb⁻¹ * (z:D⧸P) * yb) * yb⁻¹ = (z:D⧸P); group
  have hconj_inv' : ∀ z : Z, conjInv (conj z) = z := by
    intro z; apply Subtype.ext; change yb⁻¹ * (yb * (z:D⧸P) * yb⁻¹) * yb = (z:D⧸P); group
  have hphi_conj : ∀ z w : Z, phi (conj z) (conj w) = phi z w := by
    intro z w
    have hcv : cval (conj z) (conj w) = cval z w := by
      have h1 : ⁅y0 * (sec z : D) * y0⁻¹, y0 * (sec w : D) * y0⁻¹⁆ =
          (cval (conj z) (conj w) : D) :=
        hval _ _ (conj z) (conj w)
          (by show (y0 : D ⧸ P) * ((sec z : D) : D ⧸ P) * (y0 : D ⧸ P)⁻¹
                    = yb * (z : D ⧸ P) * yb⁻¹
              rw [hsec z, hy0])
          (by show (y0 : D ⧸ P) * ((sec w : D) : D ⧸ P) * (y0 : D ⧸ P)⁻¹
                    = yb * (w : D ⧸ P) * yb⁻¹
              rw [hsec w, hy0])
      have h2 : ⁅y0 * (sec z : D) * y0⁻¹, y0 * (sec w : D) * y0⁻¹⁆ = (cval z w : D) := by
        rw [← conjugate_commutatorElement]
        have hmem : ⁅sec z, sec w⁆ ∈ P := hmemc z w
        rw [show y0 * ⁅sec z, sec w⁆ * y0⁻¹ = ⁅sec z, sec w⁆ by
              rw [(hPc _ hmem y0).symm]; group]
      exact Subtype.ext (h1.symm.trans h2)
    rw [phi_def, phi_def, hcv]
  have hphi_conj_inv : ∀ z w : Z, phi (conj z) w = phi z (conjInv w) := by
    intro z w
    have h : conj (conjInv w) = w := hconj_inv w
    conv_lhs => rw [← h]
    exact hphi_conj z (conjInv w)
  have hRinv : ∀ z : Z, z ∈ R → conj z ∈ R := by
    intro z hz
    show ∀ w, phi (conj z) w = 0
    intro w
    rw [hphi_conj_inv]
    exact hz (conjInv w)
  by_cases hzero : ∀ i j : Fin 3, phi (x i) (x j) = 0
  · have hRtop : R = ⊤ := by
      have hSr_top : ∀ i : Fin 3, Sr (x i) = ⊤ := by
        intro i
        have hle : Subgroup.closure (Set.range x) ≤ Sr (x i) :=
          (closure_le (K := Sr (x i)) (k := Set.range x)).mpr (by rintro _ ⟨j, rfl⟩; exact hzero i j)
        rw [hxgen] at hle
        exact eq_top_iff.mpr hle
      have hxR : ∀ i : Fin 3, x i ∈ R := by
        intro i
        show ∀ w, phi (x i) w = 0
        intro w
        have htop := hSr_top i
        rw [eq_top_iff] at htop
        exact htop trivial
      apply eq_top_iff.mpr
      intro z _
      have hle : Subgroup.closure (Set.range x) ≤ R :=
        (closure_le (K := R) (k := Set.range x)).mpr (by rintro _ ⟨i, rfl⟩; exact hxR i)
      rw [hxgen] at hle
      exact hle trivial
    have hphi0 : ∀ z w : Z, phi z w = 0 := by
      intro z w
      have : z ∈ R := by rw [hRtop]; trivial
      exact this w
    intro a b ha hb
    have h1 : ⁅a, b⁆ = (cval ⟨(a:D⧸P), ha⟩ ⟨(b:D⧸P), hb⟩ : D) :=
      hval a b ⟨(a:D⧸P), ha⟩ ⟨(b:D⧸P), hb⟩ rfl rfl
    have h2 : cval ⟨(a:D⧸P), ha⟩ ⟨(b:D⧸P), hb⟩ = 1 :=
      (phi_eq_zero_iff _ _).mp (hphi0 _ _)
    have h3 : ⁅a, b⁆ = 1 := by rw [h1, h2]; rfl
    exact commutatorElement_eq_one_iff_mul_comm.mp h3
  · let e : Fin 3 → ZMod 2 := ![phi (x 1) (x 2), phi (x 0) (x 2), phi (x 0) (x 1)]
    let r : Z := x 0 ^ (e 0).val * x 1 ^ (e 1).val * x 2 ^ (e 2).val
    have he0 : e 0 = phi (x 1) (x 2) := rfl
    have he1 : e 1 = phi (x 0) (x 2) := rfl
    have he2 : e 2 = phi (x 0) (x 1) := rfl
    have hr_eq : ∀ j : Fin 3, phi r (x j) =
        e 0 * phi (x 0) (x j) + e 1 * phi (x 1) (x j) + e 2 * phi (x 2) (x j) := by
      intro j
      rw [show r = x 0 ^ (e 0).val * x 1 ^ (e 1).val * x 2 ^ (e 2).val from rfl,
          phi_mul_left, phi_mul_left, phi_pow_left, phi_pow_left, phi_pow_left]
      simp only [nsmul_eq_mul, ZMod.natCast_zmod_val]
    have hxSr0 : phi r (x 0) = 0 := by
      rw [hr_eq 0, phi_alt (x 0), mul_zero, zero_add,
          phi_symm (x 1) (x 0), he2.symm, phi_symm (x 2) (x 0), he1.symm]
      rw [mul_comm (e 2) (e 1)]
      exact CharTwo.add_self_eq_zero (e 1 * e 2)
    have hxSr1 : phi r (x 1) = 0 := by
      rw [hr_eq 1, phi_alt (x 1), mul_zero, add_zero,
          he2.symm, phi_symm (x 2) (x 1), he0.symm]
      rw [mul_comm (e 2) (e 0)]
      exact CharTwo.add_self_eq_zero (e 0 * e 2)
    have hxSr2 : phi r (x 2) = 0 := by
      rw [hr_eq 2, phi_alt (x 2), mul_zero, add_zero, he1.symm, he0.symm]
      rw [mul_comm (e 1) (e 0)]
      exact CharTwo.add_self_eq_zero (e 0 * e 1)
    have hxSr : ∀ j : Fin 3, phi r (x j) = 0 := by
      intro j
      fin_cases j
      · simpa using hxSr0
      · simpa using hxSr1
      · simpa using hxSr2
    have hr_mem : r ∈ R := by
      show ∀ w, phi r w = 0
      have hSr_top : Sr r = ⊤ := by
        have hle : Subgroup.closure (Set.range x) ≤ Sr r :=
          (closure_le (K := Sr r) (k := Set.range x)).mpr (by rintro _ ⟨j, rfl⟩; exact hxSr j)
        rw [hxgen] at hle
        exact eq_top_iff.mpr hle
      intro w
      have htop := hSr_top
      rw [eq_top_iff] at htop
      exact htop trivial
    have he_ne : e ≠ 0 := by
      intro he
      have h0 : e 0 = 0 := by simp [he]
      have h1 : e 1 = 0 := by simp [he]
      have h2 : e 2 = 0 := by simp [he]
      apply hzero
      intro i j
      fin_cases i <;> fin_cases j
      · exact phi_alt (x 0)
      · rw [← he2]; exact h2
      · rw [← he1]; exact h1
      · rw [phi_symm, ← he2]; exact h2
      · exact phi_alt (x 1)
      · rw [← he0]; exact h0
      · rw [phi_symm, ← he1]; exact h1
      · rw [phi_symm, ← he0]; exact h0
      · exact phi_alt (x 2)
    have hr_ne : r ≠ 1 := by
      intro hr1
      have hofm : Additive.ofMul r = ∑ i : Fin 3, e i • B i := by
        have hprod : r = ∏ i : Fin 3, x i ^ (e i).val := by rw [Fin.prod_univ_three]
        have hxi : ∀ i : Fin 3, Additive.ofMul (x i) = B i := fun i => ofMul_toMul (B i)
        rw [hprod, ofMul_prod]
        simp only [ofMul_pow, hxi]
        exact Finset.sum_congr rfl fun i _ => by
          rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2), ZMod.natCast_zmod_val]
      have hsum : (∑ i : Fin 3, e i • B i) = 0 := by
        rw [← hofm, hr1]
        rfl
      have hcoef := Fintype.linearIndependent_iff.mp B.linearIndependent e hsum
      exact he_ne (funext hcoef)
    have hRne : R ≠ ⊥ := by
      intro hbot
      have hmem : r ∈ R := hr_mem
      rw [hbot] at hmem
      exact hr_ne (Subgroup.mem_bot.mp hmem)
    obtain ⟨z0R, hz0Rne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
    let z0 : Z := z0R
    have hz0R : z0 ∈ R := z0R.2
    have hz0ne : z0 ≠ 1 := fun h => hz0Rne (Subtype.ext h)
    have hconj_pow_val : ∀ n : ℕ,
        ((conj^[n]) z0 : D ⧸ P) = yb^n * (z0 : D ⧸ P) * (yb^n)⁻¹ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        change yb * (↑((conj^[n]) z0) : D ⧸ P) * yb⁻¹
          = yb ^ (n+1) * ↑z0 * (yb ^ (n+1))⁻¹
        rw [ih, pow_succ']
        group
    have hy7pow : yb^7 = 1 := by rw [← hy7]; exact pow_orderOf_eq_one yb
    have hstab : ∀ d : ℕ, 0 < d → d < 7 → (conj^[d]) z0 ≠ z0 := by
      intro d hd0 hd7 hfix
      have hfixD : yb^d * (z0 : D⧸P) * (yb^d)⁻¹ = (z0 : D⧸P) := by
        have h := congrArg Subtype.val hfix
        rwa [hconj_pow_val d] at h
      have hpow_ne : yb^d ≠ 1 := by
        intro h
        have hdvd : 7 ∣ d := by
          rw [← hy7]
          exact orderOf_dvd_iff_pow_eq_one.mpr h
        omega
      have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      have hord : orderOf (yb^d) = 7 := by
        apply orderOf_eq_prime
        · rw [← pow_mul, mul_comm, pow_mul, hy7pow, one_pow]
        · exact hpow_ne
      have hzp : Subgroup.zpowers (yb^d) = Subgroup.zpowers yb := by
        apply Subgroup.eq_of_le_of_card_ge
        · rw [Subgroup.zpowers_le]
          exact Subgroup.mem_zpowers_iff.mpr ⟨(d : ℤ), by rw [zpow_natCast]⟩
        · rw [Nat.card_zpowers, Nat.card_zpowers, hord, hy7]
      have hyb_zp : yb ∈ Subgroup.zpowers (yb^d) := by
        rw [hzp]
        exact Subgroup.mem_zpowers yb
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hyb_zp
      have hcomm : Commute (yb^d) (z0 : D⧸P) := by
        rw [← commutatorElement_eq_one_iff_commute, commutatorElement_def, hfixD]
        group
      have hcommm : Commute ((yb^d)^m) (z0 : D⧸P) := hcomm.zpow_left m
      have hfixm : (yb^d)^m * (z0:D⧸P) * ((yb^d)^m)⁻¹ = (z0:D⧸P) := by
        rw [hcommm.eq]; group
      rw [hm] at hfixm
      exact hz0ne (Subtype.ext (hyf z0 z0.2 hfixm))
    have hconj_pow_mem : ∀ n : ℕ, (conj^[n]) z0 ∈ R := by
      intro n
      induction n with
      | zero => simpa using hz0R
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hRinv _ ih
    let w : Fin 7 → Z := fun k => (conj^[(k:ℕ)]) z0
    have hwR : ∀ k : Fin 7, w k ∈ R := by
      intro k
      exact hconj_pow_mem (k:ℕ)
    have hw_ne : ∀ k : Fin 7, w k ≠ 1 := by
      intro k hk
      have h : ((conj^[(k:ℕ)]) z0 : D⧸P) = 1 := by
        change ((w k : Z) : D ⧸ P) = 1
        rw [hk]; rfl
      rw [hconj_pow_val (k:ℕ)] at h
      have hz : (z0 : D⧸P) = 1 := by
        have := congrArg (fun x => (yb ^ (k:ℕ))⁻¹ * x * yb ^ (k:ℕ)) h
        simpa [mul_assoc] using this
      exact hz0ne (Subtype.ext hz)
    have hw_inj : Function.Injective w := by
      intro k l hkl
      by_contra hne
      have hk : (k:ℕ) < (l:ℕ) ∨ (l:ℕ) < (k:ℕ) := by
        rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
        · exact Or.inl h
        · exact Or.inr h
      rcases hk with hlt | hgt
      · have hd0 : 0 < (l:ℕ) - (k:ℕ) := Nat.sub_pos_of_lt hlt
        have hd7 : (l:ℕ) - (k:ℕ) < 7 := by omega
        have hstep : (conj^[(l:ℕ) - (k:ℕ)]) z0 = z0 := by
          have hkl' : (conj^[(l:ℕ)]) z0 = (conj^[(k:ℕ)]) ((conj^[(l:ℕ)-(k:ℕ)]) z0) := by
            rw [← Function.iterate_add_apply]
            congr 1
            omega
          have hkl'' : (conj^[(k:ℕ)]) z0 = (conj^[(l:ℕ)]) z0 := hkl
          have hinj := Function.Injective.iterate hconj_inj (k:ℕ)
          exact (hinj (by rw [← hkl', hkl''])).symm
        exact hstab _ hd0 hd7 hstep
      · have hd0 : 0 < (k:ℕ) - (l:ℕ) := Nat.sub_pos_of_lt hgt
        have hd7 : (k:ℕ) - (l:ℕ) < 7 := by omega
        have hstep : (conj^[(k:ℕ) - (l:ℕ)]) z0 = z0 := by
          have hkl' : (conj^[(k:ℕ)]) z0 = (conj^[(l:ℕ)]) ((conj^[(k:ℕ)-(l:ℕ)]) z0) := by
            rw [← Function.iterate_add_apply]
            congr 1
            omega
          have hkl'' : (conj^[(k:ℕ)]) z0 = (conj^[(l:ℕ)]) z0 := hkl
          have hinj := Function.Injective.iterate hconj_inj (l:ℕ)
          exact (hinj (by rw [← hkl', hkl''])).symm
        exact hstab _ hd0 hd7 hstep
    have hcard8 : Nat.card R = 8 := by
      have hle : 8 ≤ Nat.card R := by
        have hinj : Function.Injective (fun o : Option (Fin 7) =>
            match o with
            | none => (⟨1, R.one_mem⟩ : R)
            | some k => (⟨w k, hwR k⟩ : R)) := by
          intro o p hop
          rcases o with _ | k <;> rcases p with _ | l
          · rfl
          · exact absurd (Subtype.ext_iff.mp hop).symm (hw_ne l)
          · exact absurd (Subtype.ext_iff.mp hop) (hw_ne k)
          · exact congrArg some (hw_inj (Subtype.ext_iff.mp hop))
        have := Nat.card_le_card_of_injective _ hinj
        simpa using this
      have hge : Nat.card R ≤ 8 := by
        have h := Nat.card_le_card_of_injective (fun x : R => (x : Z)) Subtype.val_injective
        rw [hZ8] at h
        exact h
      omega
    have hRtop : R = ⊤ := Subgroup.eq_top_of_card_eq R (by rw [hcard8, hZ8])
    have hphi0 : ∀ z w : Z, phi z w = 0 := by
      intro z w
      have : z ∈ R := by rw [hRtop]; trivial
      exact this w
    intro a b ha hb
    have h1 : ⁅a, b⁆ = (cval ⟨(a:D⧸P), ha⟩ ⟨(b:D⧸P), hb⟩ : D) :=
      hval a b ⟨(a:D⧸P), ha⟩ ⟨(b:D⧸P), hb⟩ rfl rfl
    have h2 : cval ⟨(a:D⧸P), ha⟩ ⟨(b:D⧸P), hb⟩ = 1 :=
      (phi_eq_zero_iff _ _).mp (hphi0 _ _)
    have h3 : ⁅a, b⁆ = 1 := by rw [h1, h2]; rfl
    exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem sz5e1_lift_comm {D : Type} [Group D] [Finite D] (P : Subgroup D) [P.Normal]
    (hPc : ∀ p ∈ P, ∀ d : D, p * d = d * p)
    (hΩ : ∀ p ∈ P, ∀ q ∈ P, p ^ 2 = 1 → q ^ 2 = 1 → p = 1 ∨ q = 1 ∨ p = q)
    (Z : Subgroup (D ⧸ P)) (hZ8 : Nat.card Z = 8)
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZ2 : ∀ a ∈ Z, a ^ 2 = 1)
    (yb : D ⧸ P) (hy7 : orderOf yb = 7) (hyZ : ∀ z ∈ Z, yb * z * yb⁻¹ ∈ Z)
    (hyf : ∀ z ∈ Z, yb * z * yb⁻¹ = z → z = 1) :
    ∀ a b : D, (a : D ⧸ P) ∈ Z → (b : D ⧸ P) ∈ Z → a * b = b * a := by
  exact sz5e1_lcm_form P hPc hΩ Z hZ8 hZc hZ2 yb hy7 hyZ hyf

theorem sz5e1_lift {D : Type} [Group D] [Finite D] (P : Subgroup D) [P.Normal]
    (hPc : ∀ p ∈ P, ∀ d : D, p * d = d * p) (hP2 : IsPGroup 2 P)
    (hΩ : ∀ p ∈ P, ∀ q ∈ P, p ^ 2 = 1 → q ^ 2 = 1 → p = 1 ∨ q = 1 ∨ p = q)
    (Z : Subgroup (D ⧸ P)) (hZ8 : Nat.card Z = 8)
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZ2 : ∀ a ∈ Z, a ^ 2 = 1)
    (yb : D ⧸ P) (hy7 : orderOf yb = 7) (hyZ : ∀ z ∈ Z, yb * z * yb⁻¹ ∈ Z)
    (hyf : ∀ z ∈ Z, yb * z * yb⁻¹ = z → z = 1) :
    ∃ (E : Subgroup D) (y : D), Nat.card E = 8 ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
      (∀ a ∈ E, a ^ 2 = 1) ∧ E ⊓ P = ⊥ ∧ E.map (QuotientGroup.mk' P) = Z ∧
      orderOf y = 7 ∧ (∀ e ∈ E, y * e * y⁻¹ ∈ E) ∧ (∀ e ∈ E, y * e * y⁻¹ = e → e = 1) := by
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective P yb
  set m : ℕ := orderOf (y₀ ^ 7) with hmdef
  have hm_ne : m ≠ 0 := (orderOf_pos _).ne'
  have hy07P : y₀ ^ 7 ∈ P := by
    rw [← QuotientGroup.eq_one_iff]
    show (QuotientGroup.mk' P) (y₀ ^ 7) = 1
    rw [map_pow, hy₀, ← hy7]
    exact pow_orderOf_eq_one yb
  have h7dvd : 7 ∣ orderOf y₀ := by
    have := orderOf_map_dvd (QuotientGroup.mk' P) y₀
    rw [hy₀, hy7] at this
    exact this
  have hmdvd : m ∣ orderOf y₀ := orderOf_pow_dvd (x := y₀) 7
  have hm_coprime : Nat.Coprime 7 m := by
    obtain ⟨j, hj⟩ := hP2 ⟨y₀ ^ 7, hy07P⟩
    have hm2dvd : m ∣ 2 ^ j := by
      rw [hmdef, ← Subgroup.orderOf_mk (y₀ ^ 7) hy07P, orderOf_dvd_iff_pow_eq_one]
      exact hj
    exact (Nat.Coprime.pow_right j (by decide : Nat.Coprime 7 2)).coprime_dvd_right hm2dvd
  have hord : orderOf y₀ = 7 * m := by
    apply Nat.dvd_antisymm
    · rw [orderOf_dvd_iff_pow_eq_one, show y₀ ^ (7 * m) = (y₀ ^ 7) ^ m by rw [← pow_mul],
        hmdef]
      exact pow_orderOf_eq_one (y₀ ^ 7)
    · exact hm_coprime.mul_dvd_of_dvd_of_dvd h7dvd hmdvd
  set k : ℕ := (m⁻¹ : ZMod 7).val with hkdef
  have hkm : m * k ≡ 1 [MOD 7] := by
    have h : ((m * k : ℕ) : ZMod 7) = 1 := by
      rw [hkdef, Nat.cast_mul]
      exact ZMod.mul_val_inv (n := 7) hm_coprime.symm
    exact (ZMod.natCast_eq_natCast_iff (m * k) 1 7).mp h
  set y : D := y₀ ^ (m * k) with hydef
  have hyq : (y : D ⧸ P) = yb := by
    rw [hydef, ← QuotientGroup.mk'_apply, map_pow, hy₀]
    rw [pow_eq_pow_mod (m * k) (pow_orderOf_eq_one yb), hy7]
    rw [Nat.ModEq] at hkm
    rw [hkm, Nat.mod_eq_of_lt (by norm_num : 1 < 7), pow_one]
  have hy7_pow : y ^ 7 = 1 := by
    rw [hydef, ← pow_mul]
    rw [show m * k * 7 = 7 * m * k by ring]
    rw [pow_mul]
    rw [show y₀ ^ (7 * m) = 1 by rw [← hord]; exact pow_orderOf_eq_one y₀]
    rw [one_pow]
  have hy_ne : y ≠ 1 := by
    intro h
    have h1 : yb = 1 := by rw [← hyq, h]; rfl
    have : orderOf yb = 1 := by rw [h1]; exact orderOf_one
    omega
  have hord_y : orderOf y = 7 := by
    have hdvd : orderOf y ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hy7_pow
    have hne1 : orderOf y ≠ 1 := by
      intro h
      exact hy_ne (orderOf_eq_one_iff.mp h)
    exact ((Nat.prime_seven.dvd_iff_eq hne1).mp hdvd).symm
  set Ê : Subgroup D := Z.comap (QuotientGroup.mk' P) with hÊdef
  have hÊ_comm : ∀ a b : D, a ∈ Ê → b ∈ Ê → a * b = b * a := by
    intro a b ha hb
    exact sz5e1_lift_comm P hPc hΩ Z hZ8 hZc hZ2 yb hy7 hyZ hyf a b ha hb
  have hyq' : (QuotientGroup.mk' P) y = yb := by
    rw [QuotientGroup.mk'_apply]
    exact hyq
  have hP_le_Ê : P ≤ Ê := by
    intro p hp
    rw [Subgroup.mem_comap]
    rw [show (QuotientGroup.mk' P) p = 1 from (QuotientGroup.eq_one_iff p).mpr hp]
    exact Z.one_mem
  have hyÊ : ∀ a ∈ Ê, y * a * y⁻¹ ∈ Ê := by
    intro a ha
    rw [Subgroup.mem_comap] at ha ⊢
    have hcoe : (QuotientGroup.mk' P) (y * a * y⁻¹) = yb * (a : D ⧸ P) * yb⁻¹ := by
      rw [map_mul, map_mul, map_inv, hyq']
      rfl
    rw [hcoe]
    exact hyZ _ ha
  let τ : Ê →* D := MonoidHom.mk' (fun a : Ê => y * (a : D) * y⁻¹ * (a : D)⁻¹) (by
    intro a b
    have hb : y * (b : D) * y⁻¹ ∈ Ê := hyÊ (b : D) b.2
    have h1 : (a : D)⁻¹ * (y * (b : D) * y⁻¹) = (y * (b : D) * y⁻¹) * (a : D)⁻¹ :=
      hÊ_comm _ _ (inv_mem a.2) hb
    have h2 : (a : D)⁻¹ * (b : D)⁻¹ = (b : D)⁻¹ * (a : D)⁻¹ :=
      hÊ_comm _ _ (inv_mem a.2) (inv_mem b.2)
    apply Eq.symm
    show y * (a : D) * y⁻¹ * (a : D)⁻¹ * (y * (b : D) * y⁻¹ * (b : D)⁻¹)
        = y * ((a * b : Ê) : D) * y⁻¹ * ((a * b : Ê) : D)⁻¹
    rw [show ((a * b : Ê) : D) = (a : D) * (b : D) from rfl, mul_inv_rev]
    calc y * (a : D) * y⁻¹ * (a : D)⁻¹ * (y * (b : D) * y⁻¹ * (b : D)⁻¹)
        = y * (a : D) * y⁻¹ * ((a : D)⁻¹ * (y * (b : D) * y⁻¹)) * (b : D)⁻¹ := by group
      _ = y * (a : D) * y⁻¹ * ((y * (b : D) * y⁻¹) * (a : D)⁻¹) * (b : D)⁻¹ := by rw [h1]
      _ = y * (a : D) * (y⁻¹ * y) * (b : D) * y⁻¹ * (a : D)⁻¹ * (b : D)⁻¹ := by group
      _ = y * (a : D) * (b : D) * y⁻¹ * (a : D)⁻¹ * (b : D)⁻¹ := by group
      _ = y * (a : D) * (b : D) * y⁻¹ * ((a : D)⁻¹ * (b : D)⁻¹) := by group
      _ = y * (a : D) * (b : D) * y⁻¹ * ((b : D)⁻¹ * (a : D)⁻¹) := by rw [h2]
      _ = y * ((a : D) * (b : D)) * y⁻¹ * ((b : D)⁻¹ * (a : D)⁻¹) := by group)
  let E : Subgroup D := τ.range
  have hτ_mem : ∀ a : Ê, τ a ∈ Ê := by
    intro a
    show y * (a : D) * y⁻¹ * (a : D)⁻¹ ∈ Ê
    exact mul_mem (hyÊ _ a.2) (inv_mem a.2)
  have hE_le_Ê : E ≤ Ê := by
    intro e he
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp he
    exact hτ_mem a
  have hE_ab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    exact hÊ_comm a b (hE_le_Ê ha) (hE_le_Ê hb)
  have hτ_sq : ∀ a : Ê, τ a ^ 2 = 1 := by
    intro a
    have ha2P : (a : D) ^ 2 ∈ P := by
      rw [← QuotientGroup.eq_one_iff]
      simpa using hZ2 (a : D ⧸ P) a.2
    have hc : (a : D)⁻¹ * (y * (a : D) * y⁻¹) = (y * (a : D) * y⁻¹) * (a : D)⁻¹ :=
      hÊ_comm _ _ (inv_mem a.2) (hyÊ _ a.2)
    have hcen : y * (a : D) ^ 2 * y⁻¹ = (a : D) ^ 2 := by
      rw [← hPc ((a : D) ^ 2) ha2P y]; group
    show (y * (a : D) * y⁻¹ * (a : D)⁻¹) ^ 2 = 1
    calc (y * (a : D) * y⁻¹ * (a : D)⁻¹) ^ 2
        = y * (a : D) * y⁻¹ * ((a : D)⁻¹ * (y * (a : D) * y⁻¹)) * (a : D)⁻¹ := by
          simp only [pow_two]; group
      _ = y * (a : D) * y⁻¹ * ((y * (a : D) * y⁻¹) * (a : D)⁻¹) * (a : D)⁻¹ := by rw [hc]
      _ = y * (a : D) * y⁻¹ * y * (a : D) * y⁻¹ * (a : D)⁻¹ * (a : D)⁻¹ := by group
      _ = y * (a : D) ^ 2 * y⁻¹ * ((a : D) ^ 2)⁻¹ := by simp only [pow_two]; group
      _ = (a : D) ^ 2 * ((a : D) ^ 2)⁻¹ := by rw [hcen]
      _ = 1 := by group
  have hE_sq : ∀ a ∈ E, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ha
    exact hτ_sq b
  have hE_inf_P : E ⊓ P = ⊥ := by
    apply le_antisymm _ bot_le
    rintro e ⟨heE, heP⟩
    rw [Subgroup.mem_bot]
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp heE
    have heq : y * (a : D) * y⁻¹ = τ a * (a : D) := by
      show y * (a : D) * y⁻¹ = (y * (a : D) * y⁻¹ * (a : D)⁻¹) * (a : D)
      group
    have hτsq : τ a ^ 2 = 1 := hτ_sq a
    have hfix2 : y ^ 2 * (a : D) * (y ^ 2)⁻¹ = (a : D) := by
      calc y ^ 2 * (a : D) * (y ^ 2)⁻¹
          = y * (y * (a : D) * y⁻¹) * y⁻¹ := by simp only [pow_two]; group
        _ = y * (τ a * (a : D)) * y⁻¹ := by rw [heq]
        _ = (y * τ a * y⁻¹) * (y * (a : D) * y⁻¹) := by group
        _ = τ a * (τ a * (a : D)) := by
              rw [show y * τ a * y⁻¹ = τ a from by rw [← hPc (τ a) heP y]; group, heq]
        _ = τ a ^ 2 * (a : D) := by simp only [pow_two]; group
        _ = (a : D) := by rw [hτsq, one_mul]
    have hy_eq : y = (y ^ 2) ^ 4 := by
      rw [show (y ^ 2) ^ 4 = y ^ (2 * 4) from (pow_mul y 2 4).symm,
        show 2 * 4 = 7 + 1 by norm_num, pow_add, hy7_pow, one_mul, pow_one]
    have hcomm2 : Commute (y ^ 2) (a : D) := by
      rw [commute_iff_eq]
      have := congrArg (fun t => t * y ^ 2) hfix2
      simpa [mul_assoc] using this
    have hcomm_y : Commute y (a : D) := by
      rw [hy_eq]
      exact hcomm2.pow_left 4
    have hfix1 : y * (a : D) * y⁻¹ = (a : D) := by
      rw [hcomm_y.eq]; group
    show τ a = 1
    show y * (a : D) * y⁻¹ * (a : D)⁻¹ = 1
    rw [hfix1]; group
  let δ : Z →* Z := MonoidHom.mk' (fun z : Z => ⟨yb * (z : D ⧸ P) * yb⁻¹ * (z : D ⧸ P)⁻¹,
      mul_mem (hyZ _ z.2) (inv_mem z.2)⟩) (by
    intro z w
    have h1 : (z : D ⧸ P)⁻¹ * (yb * (w : D ⧸ P) * yb⁻¹) =
        (yb * (w : D ⧸ P) * yb⁻¹) * (z : D ⧸ P)⁻¹ :=
      hZc _ (inv_mem z.2) _ (hyZ _ w.2)
    have h2 : (z : D ⧸ P)⁻¹ * (w : D ⧸ P)⁻¹ = (w : D ⧸ P)⁻¹ * (z : D ⧸ P)⁻¹ :=
      hZc _ (inv_mem z.2) _ (inv_mem w.2)
    apply Eq.symm
    apply Subtype.ext
    show yb * (z : D ⧸ P) * yb⁻¹ * (z : D ⧸ P)⁻¹ *
          (yb * (w : D ⧸ P) * yb⁻¹ * (w : D ⧸ P)⁻¹)
        = yb * ((z * w : Z) : D ⧸ P) * yb⁻¹ * ((z * w : Z) : D ⧸ P)⁻¹
    rw [show ((z * w : Z) : D ⧸ P) = (z : D ⧸ P) * (w : D ⧸ P) from rfl, mul_inv_rev]
    calc yb * (z : D ⧸ P) * yb⁻¹ * (z : D ⧸ P)⁻¹ *
          (yb * (w : D ⧸ P) * yb⁻¹ * (w : D ⧸ P)⁻¹)
        = yb * (z : D ⧸ P) * yb⁻¹ * ((z : D ⧸ P)⁻¹ * (yb * (w : D ⧸ P) * yb⁻¹)) *
            (w : D ⧸ P)⁻¹ := by group
      _ = yb * (z : D ⧸ P) * yb⁻¹ * ((yb * (w : D ⧸ P) * yb⁻¹) * (z : D ⧸ P)⁻¹) *
            (w : D ⧸ P)⁻¹ := by rw [h1]
      _ = yb * (z : D ⧸ P) * yb⁻¹ * yb * (w : D ⧸ P) * yb⁻¹ * (z : D ⧸ P)⁻¹ *
            (w : D ⧸ P)⁻¹ := by group
      _ = yb * (z : D ⧸ P) * (w : D ⧸ P) * yb⁻¹ * (z : D ⧸ P)⁻¹ * (w : D ⧸ P)⁻¹ := by group
      _ = yb * (z : D ⧸ P) * (w : D ⧸ P) * yb⁻¹ *
            ((z : D ⧸ P)⁻¹ * (w : D ⧸ P)⁻¹) := by group
      _ = yb * (z : D ⧸ P) * (w : D ⧸ P) * yb⁻¹ *
            ((w : D ⧸ P)⁻¹ * (z : D ⧸ P)⁻¹) := by rw [h2]
      _ = yb * ((z : D ⧸ P) * (w : D ⧸ P)) * yb⁻¹ *
            ((w : D ⧸ P)⁻¹ * (z : D ⧸ P)⁻¹) := by group)
  have hδ_ker : δ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hz' : yb * (z : D ⧸ P) * yb⁻¹ * (z : D ⧸ P)⁻¹ = 1 := by
      change (δ z : D ⧸ P) = 1
      rw [hz]
      rfl
    have hfix : yb * (z : D ⧸ P) * yb⁻¹ = (z : D ⧸ P) := mul_inv_eq_one.mp hz'
    exact Subtype.ext (hyf _ z.2 hfix)
  have hδ_inj : Function.Injective δ := (MonoidHom.ker_eq_bot_iff δ).mp hδ_ker
  have hδ_surj : Function.Surjective δ := Finite.surjective_of_injective hδ_inj
  have hE_map : E.map (QuotientGroup.mk' P) = Z := by
    apply le_antisymm
    · rintro z ⟨e, he, rfl⟩
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp he
      show (QuotientGroup.mk' P) (τ a) ∈ Z
      have hcoe : (QuotientGroup.mk' P) (τ a) =
          yb * (a : D ⧸ P) * yb⁻¹ * (a : D ⧸ P)⁻¹ := by
        show (QuotientGroup.mk' P) (y * (a : D) * y⁻¹ * (a : D)⁻¹) = _
        rw [map_mul, map_mul, map_inv, map_mul, map_inv, hyq']; rfl
      rw [hcoe]
      exact mul_mem (hyZ _ a.2) (inv_mem a.2)
    · intro z hz
      obtain ⟨w, hw⟩ := hδ_surj ⟨z, hz⟩
      obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective P (w : D ⧸ P)
      have haÊ : a ∈ Ê := by
        rw [Subgroup.mem_comap]
        rw [ha]
        exact w.2
      refine Subgroup.mem_map.mpr ⟨τ ⟨a, haÊ⟩, MonoidHom.mem_range.mpr ⟨⟨a, haÊ⟩, rfl⟩, ?_⟩
      have hcoe : (QuotientGroup.mk' P) (τ ⟨a, haÊ⟩) =
          yb * (a : D ⧸ P) * yb⁻¹ * (a : D ⧸ P)⁻¹ := by
        show (QuotientGroup.mk' P) (y * (a : D) * y⁻¹ * (a : D)⁻¹) = _
        rw [map_mul, map_mul, map_inv, map_mul, map_inv, hyq']; rfl
      rw [hcoe, show (a : D ⧸ P) = (w : D ⧸ P) from ha]
      exact congrArg Subtype.val hw
  have hcard : Nat.card E = 8 := by
    have hri : P.relIndex E = Nat.card (E.map (QuotientGroup.mk' P)) := by
      have := Subgroup.relIndex_ker (QuotientGroup.mk' P) (K := E)
      rwa [QuotientGroup.ker_mk'] at this
    have hcard := Subgroup.relIndex_mul_card (H := P) (K := E)
    rw [hri, hE_map, hZ8] at hcard
    have hbot : P ⊓ E = ⊥ := by rw [inf_comm]; exact hE_inf_P
    rw [hbot, Subgroup.card_bot, mul_one] at hcard
    exact hcard.symm
  have hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E := by
    intro e he
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp he
    refine ⟨⟨y * (a : D) * y⁻¹, hyÊ _ a.2⟩, ?_⟩
    show y * (y * (a : D) * y⁻¹) * y⁻¹ * (y * (a : D) * y⁻¹)⁻¹
        = y * (y * (a : D) * y⁻¹ * (a : D)⁻¹) * y⁻¹
    group
  have hyfix : ∀ e ∈ E, y * e * y⁻¹ = e → e = 1 := by
    intro e he hefix
    have heZ : (e : D ⧸ P) ∈ Z := hE_le_Ê he
    have hfixZ : yb * (e : D ⧸ P) * yb⁻¹ = (e : D ⧸ P) := by
      have h1 : (QuotientGroup.mk' P) (y * e * y⁻¹) = (QuotientGroup.mk' P) e := by rw [hefix]
      rw [map_mul, map_mul, map_inv, hyq'] at h1
      exact h1
    have heP : e ∈ P := by
      rw [← QuotientGroup.eq_one_iff]
      exact hyf _ heZ hfixZ
    have hmem : e ∈ E ⊓ P := ⟨he, heP⟩
    rw [hE_inf_P, Subgroup.mem_bot] at hmem
    exact hmem
  exact ⟨E, y, hcard, hE_ab, hE_sq, hE_inf_P, hE_map, hord_y, hyE, hyfix⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5
