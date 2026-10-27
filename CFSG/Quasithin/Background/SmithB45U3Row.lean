module

public import CFSG.Quasithin.Background.HSU3
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj

public section

namespace CFSG.Quasithin

namespace B45U3

open CFSG.Open CFSG.Quasithin.H CFSG.Quasithin.H.SU3 Matrix
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem two_mul_rk_le_rkIdx (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Subgroup (MulAut (StdMod (Fin 3) K))} (hAN : A ≤ natNorm (StatedSU 3 (2 ^ n) K))
    (hA1 : A ≠ ⊥) (hAel : IsElemAbelian2 A) : 2 * rk ↥A ≤ rkIdx (fixV A) := by
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hΓ := hasScalarCommutant' (by omega : 1 ≤ n) hK
  have hrk2 : rk ↥A ≤ n + 1 := (rk_le_pRank le_rfl hAel).trans (pRank_le (by omega) hK hAN)
  have hcardA : Nat.card A = 2 ^ rk ↥A :=
    card_eq_two_pow_of_isPGroup (E3.isPGroup_of_isElemAbelian2 hAel)
  have hmono : ∀ a ∈ A, rkIdx (fixV (Subgroup.zpowers a)) ≤ rkIdx (fixV A) := fun a ha =>
    rkIdx_anti (fun v hv y hy => hv y ((Subgroup.zpowers_le).mpr ha hy))
  by_cases hlin : A ≤ linSub
  · have h1 := card_inf_linSub_le (by omega) hK hAN hAel
    rw [inf_eq_left.mpr hlin, hcardA] at h1
    have hrk : rk ↥A ≤ n := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    have hoa : orderOf (a : MulAut (StdMod (Fin 3) K)) = 2 :=
      orderOf_eq_prime (hAel.2 a a.2) (fun h => ha1 (Subtype.ext h))
    have h2 := le_rkIdx_fixV_of_involution (by omega) hK hAN a.2 hoa
    have h3 := hmono a a.2
    omega
  · obtain ⟨a, haA, ha⟩ : ∃ a ∈ A, a ∉ linSub := by
      by_contra h
      push Not at h
      exact hlin h
    have hsl := isSemilinear_fieldAut hΓ ⟨a, hAN haA⟩
    have hσ : fieldAut hΓ ⟨a, hAN haA⟩ ≠ RingEquiv.refl K := by
      intro h
      apply ha
      have := hsl
      rw [h] at this
      exact this
    have h2 : rkIdx (fixV (Subgroup.zpowers a)) = 3 * n :=
      rkIdx_fixV_of_semilinear_involution (by omega) hK hsl hσ (hAel.2 a haA)
    have h3 := hmono a haA
    omega

@[expose] def rootMat (c : K) : Matrix (Fin 3) (Fin 3) K := !![1 + c, c, 0; c, 1 + c, 0; 0, 0, 1]

omit [Finite K] [CharP K 2] in
theorem rootMat_mulVec (c : K) (v : Fin 3 → K) :
    rootMat c *ᵥ v = ![v 0 + c * (v 0 + v 1), v 1 + c * (v 0 + v 1), v 2] := by
  ext i
  fin_cases i <;> simp [rootMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

omit [Finite K] in
theorem det_rootMat (c : K) : (rootMat c).det = 1 := by
  rw [rootMat, Matrix.det_fin_three]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
    cons_val_fin_one, head_cons, tail_cons, head_fin_const]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (c) * h2

omit [Finite K] in
theorem rootMat_mul (c d : K) : rootMat c * rootMat d = rootMat (c + d) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination (c * d) * h2

omit [Finite K] [CharP K 2] in
theorem rootMat_zero : rootMat (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat]

omit [Finite K] in
theorem rootMat_one : rootMat (1 : K) = swapMat := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat, swapMat, h2]

omit [Finite K] in
theorem rootMat_unitary {c : K} (hc : c ^ 2 ^ n = c) :
    ((rootMat c).map (· ^ 2 ^ n))ᵀ * rootMat c = 1 := by
  have h1 : (1 + c) ^ 2 ^ n = 1 + c := by
    rw [add_pow_char_pow, one_pow, hc]
  have hmap : (rootMat c).map (· ^ 2 ^ n) = rootMat c := by
    have hq : 2 ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rootMat, h1, hc, zero_pow hq]
  have htr : (rootMat c)ᵀ = rootMat c := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hmap, htr, rootMat_mul, CharTwo.add_self_eq_zero, rootMat_zero]

@[expose] noncomputable def rootSU (c : K) (hc : c ^ 2 ^ n = c) : ↥(StatedSU 3 (2 ^ n) K) :=
  ⟨glOfDetOne (rootMat c) (det_rootMat c),
    mem_statedSU (A := glOfDetOne (rootMat c) (det_rootMat c))
      (by rw [coe_glOfDetOne]; exact det_rootMat c)
      (by rw [coe_glOfDetOne]; exact rootMat_unitary hc)⟩

omit [Finite K] in
theorem coe_rootSU (c : K) (hc : c ^ 2 ^ n = c) :
    (((rootSU c hc : ↥(StatedSU 3 (2 ^ n) K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      rootMat c :=
  coe_glOfDetOne _ (det_rootMat c)

variable (K n) in
@[expose] noncomputable def rootSub : Subgroup ↥(StatedSU 3 (2 ^ n) K) where
  carrier := {g | ∃ c : K, c ^ 2 ^ n = c ∧
    ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = rootMat c}
  mul_mem' := by
    rintro g h ⟨c, hc, hg⟩ ⟨d, hd, hh⟩
    refine ⟨c + d, by rw [add_pow_char_pow, hc, hd], ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hg, hh, rootMat_mul]
  one_mem' := ⟨0, by rw [zero_pow (pow_ne_zero _ two_ne_zero)], by
    rw [Subgroup.coe_one, Units.val_one, rootMat_zero]⟩
  inv_mem' := by
    rintro g ⟨c, hc, hg⟩
    refine ⟨c, hc, ?_⟩
    have h1 : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [hg, rootMat_mul, CharTwo.add_self_eq_zero, rootMat_zero]
    have h2 : ((g⁻¹ : ↥(StatedSU 3 (2 ^ n) K)) : GL (Fin 3) K) = (g : GL (Fin 3) K) := by
      rw [Subgroup.coe_inv, inv_eq_iff_mul_eq_one]
      exact Units.ext h1
    rw [h2, hg]

variable (K n) in
@[expose] noncomputable def rootImage : Subgroup (MulAut (StdMod (Fin 3) K)) :=
  (rootSub K n).map (natAut (StatedSU 3 (2 ^ n) K))

omit [Finite K] in
theorem rootImage_le_natImage : rootImage K n ≤ natImage (StatedSU 3 (2 ^ n) K) :=
  Subgroup.map_le_range _ _

variable (n) in
@[expose] noncomputable def rootElt (c : K) (hc : c ^ 2 ^ n = c) : MulAut (StdMod (Fin 3) K) :=
  natAut (StatedSU 3 (2 ^ n) K) (rootSU c hc)

omit [Finite K] in
theorem toAddMap_rootElt (c : K) (hc : c ^ 2 ^ n = c) (v : Fin 3 → K) :
    toAddMap (rootElt n c hc) v = rootMat c *ᵥ v := by
  rw [rootElt, toAddMap_natAut, coe_rootSU]

omit [Finite K] in
theorem rootElt_mem {c : K} (hc : c ^ 2 ^ n = c) : rootElt n c hc ∈ rootImage K n :=
  ⟨rootSU c hc, ⟨c, hc, coe_rootSU c hc⟩, rfl⟩

omit [Finite K] in
theorem mem_rootImage_iff {g : MulAut (StdMod (Fin 3) K)} :
    g ∈ rootImage K n ↔ ∃ c : K, c ^ 2 ^ n = c ∧ ∀ v, toAddMap g v = rootMat c *ᵥ v := by
  constructor
  · rintro ⟨γ, ⟨c, hc, hγ⟩, rfl⟩
    exact ⟨c, hc, fun v => by rw [toAddMap_natAut, hγ]⟩
  · rintro ⟨c, hc, hg⟩
    refine ⟨rootSU c hc, ⟨c, hc, coe_rootSU c hc⟩, toAddMap_injective fun v => ?_⟩
    rw [toAddMap_natAut, coe_rootSU, hg]

omit [Finite K] in
theorem mem_fixV_rootImage_iff {x : StdMod (Fin 3) K} :
    x ∈ fixV (rootImage K n) ↔ Multiplicative.toAdd x 0 = Multiplicative.toAdd x 1 := by
  have h2 : ∀ y : K, y + y = 0 := CharTwo.add_self_eq_zero
  constructor
  · intro hx
    have h := hx _ (rootElt_mem (K := K) (n := n) (one_pow _))
    have h' : toAddMap (rootElt (K := K) (n := n) 1 (one_pow _)) (Multiplicative.toAdd x) =
        Multiplicative.toAdd x := congrArg Multiplicative.toAdd h
    rw [toAddMap_rootElt, rootMat_one, swapMat_mulVec] at h'
    simpa using congrFun h' 1
  · intro hx g hg
    obtain ⟨c, -, hgc⟩ := mem_rootImage_iff.mp hg
    apply Multiplicative.toAdd.injective
    change toAddMap g (Multiplicative.toAdd x) = _
    rw [hgc, rootMat_mulVec]
    ext i
    fin_cases i <;> simp [hx, h2]

omit [Finite K] in
theorem fixV_rootImage :
    fixV (rootImage K n) = fixV (Subgroup.zpowers (tSwap (K := K) n)) := by
  ext x
  rw [mem_fixV_rootImage_iff, mem_fixV_zpowers_iff]
  constructor
  · intro hx
    apply Multiplicative.toAdd.injective
    change toAddMap (tSwap (K := K) n) (Multiplicative.toAdd x) = _
    rw [toAddMap_tSwap]
    ext i
    fin_cases i <;> simp [hx]
  · intro h
    have h' : toAddMap (tSwap (K := K) n) (Multiplicative.toAdd x) = Multiplicative.toAdd x :=
      congrArg Multiplicative.toAdd h
    rw [toAddMap_tSwap] at h'
    simpa using congrFun h' 1

theorem rkIdx_fixV_rootImage (hK : Nat.card K = (2 ^ n) ^ 2) :
    rkIdx (fixV (rootImage K n)) = 2 * n := by
  rw [fixV_rootImage, rkIdx_fixV_tSwap hK]

omit [Finite K] in
theorem isElemAbelian2_rootImage : IsElemAbelian2 (rootImage K n) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨c, -, hxc⟩ := mem_rootImage_iff.mp hx
    obtain ⟨d, -, hyd⟩ := mem_rootImage_iff.mp hy
    refine toAddMap_injective fun v => ?_
    rw [toAddMap_mul, toAddMap_mul, hxc, hyd, hxc, hyd, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, rootMat_mul, rootMat_mul, add_comm]
  · obtain ⟨c, -, hxc⟩ := mem_rootImage_iff.mp hx
    refine toAddMap_injective fun v => ?_
    rw [sq, toAddMap_mul, hxc, hxc, Matrix.mulVec_mulVec, rootMat_mul,
      CharTwo.add_self_eq_zero, rootMat_zero, Matrix.one_mulVec, toAddMap_one]

omit [Finite K] in
theorem rootImage_ne_bot : rootImage K n ≠ ⊥ := by
  intro h
  have hmem : tSwap (K := K) n ∈ rootImage K n :=
    mem_rootImage_iff.mpr ⟨1, one_pow _, fun v => by rw [toAddMap_tSwap, rootMat_one,
      swapMat_mulVec]⟩
  rw [h, Subgroup.mem_bot] at hmem
  have := orderOf_tSwap (K := K) (n := n)
  rw [hmem, orderOf_one] at this
  omega

omit [Finite K] in
theorem isQuadratic_rootImage : IsQuadratic (rootImage K n) := by
  unfold IsQuadratic commV
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, x, rfl⟩
  obtain ⟨c, -, hgc⟩ := mem_rootImage_iff.mp hg
  rw [SetLike.mem_coe, mem_fixV_rootImage_iff]
  have e : Multiplicative.toAdd (g x * x⁻¹) =
      toAddMap g (Multiplicative.toAdd x) - Multiplicative.toAdd x := by
    rw [toAdd_mul, toAdd_inv, sub_eq_add_neg]
    rfl
  rw [e, hgc, rootMat_mulVec]
  simp

theorem two_pow_le_card_fixed (hK : Nat.card K = (2 ^ n) ^ 2) :
    2 ^ n ≤ Nat.card {c : K // c ^ 2 ^ n = c} := by
  have hfrob : ∀ x : K, (x ^ 2 ^ n) ^ 2 ^ n = x := fun x => by
    have := Fintype.ofFinite K
    rw [← pow_mul, ← pow_two, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  let tr : K →+ K :=
    { toFun := fun x => x + x ^ 2 ^ n
      map_zero' := by simp
      map_add' := fun x y => by rw [add_pow_char_pow]; ring }
  have hker : ∀ x, x ∈ tr.ker ↔ x ^ 2 ^ n = x := by
    intro x
    rw [AddMonoidHom.mem_ker]
    change x + x ^ 2 ^ n = 0 ↔ _
    constructor
    · intro h
      have := congrArg (· + x) h
      simp only [zero_add] at this
      rw [add_comm, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] at this
      exact this
    · intro h
      rw [h, CharTwo.add_self_eq_zero]
  have hle : tr.range ≤ tr.ker := by
    rintro _ ⟨x, rfl⟩
    rw [hker]
    change (x + x ^ 2 ^ n) ^ 2 ^ n = x + x ^ 2 ^ n
    rw [add_pow_char_pow, hfrob, add_comm]
  have hcard : Nat.card K = Nat.card tr.ker * Nat.card tr.range := by
    rw [← AddSubgroup.card_mul_index tr.ker, AddSubgroup.index_ker]
  have hr : Nat.card tr.range ≤ Nat.card tr.ker := AddSubgroup.card_le_of_le hle
  have hkc : Nat.card tr.ker = Nat.card {c : K // c ^ 2 ^ n = c} :=
    Nat.card_congr (Equiv.subtypeEquivRight hker)
  rw [← hkc]
  by_contra hlt
  push Not at hlt
  have h1 : Nat.card K < (2 ^ n) ^ 2 := by
    rw [hcard, sq]
    calc Nat.card tr.ker * Nat.card tr.range ≤ Nat.card tr.ker * Nat.card tr.ker :=
          Nat.mul_le_mul_left _ hr
      _ < 2 ^ n * 2 ^ n := Nat.mul_self_lt_mul_self hlt
  omega

theorem le_rk_rootImage (hK : Nat.card K = (2 ^ n) ^ 2) : n ≤ rk ↥(rootImage K n) := by
  have hcard : 2 ^ n ≤ Nat.card ↥(rootImage K n) := by
    refine (two_pow_le_card_fixed hK).trans (Nat.card_le_card_of_injective
      (fun c => ⟨natAut (StatedSU 3 (2 ^ n) K) (rootSU c.1 c.2),
        mem_rootImage_iff.mpr ⟨c.1, c.2, fun v => by rw [toAddMap_natAut, coe_rootSU]⟩⟩) ?_)
    intro c d h
    have h1 := congrArg (fun g : ↥(rootImage K n) =>
      toAddMap (g : MulAut (StdMod (Fin 3) K)) (Pi.single 1 1) 0) h
    simp only [toAddMap_natAut, coe_rootSU, rootMat_mulVec] at h1
    apply Subtype.ext
    simpa using h1
  have hp := card_eq_two_pow_of_isPGroup
    (E3.isPGroup_of_isElemAbelian2 (isElemAbelian2_rootImage (K := K) (n := n)))
  rw [hp] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard

end B45U3

open B45U3 H in
theorem B45U3.qOf_qhatOf_eq_two {V : Type} [CommGroup V] [Finite V]
    {G L : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V))) {n : ℕ} (hn : 2 ≤ n)
    (hL : BinaryNaturalSU3 L ⊤ ⊥ n) :
    qOf G = ((2 : ℚ) : WithTop ℚ) ∧ qhatOf G = ((2 : ℚ) : WithTop ℚ) := by
  obtain ⟨K, _, _, hK, hreal⟩ := hL
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ 2 * n) (SU3.card_eq_two_pow hK)
  obtain ⟨e, h1, h2⟩ := exists_transport_natural hreal hLG hGN
  have : Finite (StdMod (Fin 3) K) := Finite.of_equiv V e.toEquiv
  have hq : qOf G = qOf (G.map (congrHom e)) := (H13.kq_map_congr e G 2).symm
  have hqh : qhatOf G = qhatOf (G.map (congrHom e)) := (H13.kq_map_congr e G 3).symm
  set X := G.map (congrHom e) with hX
  have hlow : ((2 : ℚ) : WithTop ℚ) ≤ qhatOf X := by
    refine le_kq_iff.mpr fun A hA _ => ?_
    have h := two_mul_rk_le_rkIdx hn hK (hA.1.trans h2) hA.2.1 hA.2.2
    have hmul := hA.rAV_mul
    have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hA.rk_pos
    have h' : (2 : ℚ) * (rk ↥A : ℚ) ≤ (rkIdx (fixV A) : ℚ) := by exact_mod_cast h
    rw [← hmul] at h'
    exact le_of_mul_le_mul_right h' hpos
  have hup : qOf X ≤ ((2 : ℚ) : WithTop ℚ) := by
    refine kq_le_iff.mpr ⟨rootImage K n, ⟨rootImage_le_natImage.trans h1, rootImage_ne_bot,
      isElemAbelian2_rootImage⟩, (isQuadratic_iff_commSeries_two _).mp
        isQuadratic_rootImage, ?_⟩
    have hrk := le_rk_rootImage (K := K) hK
    have hpos : (0 : ℚ) < (rk ↥(rootImage K n) : ℚ) := by
      have : 0 < n := by omega
      exact_mod_cast (lt_of_lt_of_le this hrk)
    unfold rAV
    rw [rkIdx_fixV_rootImage hK, div_le_iff₀ hpos]
    have : (n : ℚ) ≤ (rk ↥(rootImage K n) : ℚ) := by exact_mod_cast hrk
    push_cast
    linarith
  have hle := qhatOf_le_qOf X
  have hq2 : qOf X = ((2 : ℚ) : WithTop ℚ) := le_antisymm hup (hlow.trans hle)
  have hqh2 : qhatOf X = ((2 : ℚ) : WithTop ℚ) := le_antisymm (hle.trans hup) hlow
  exact ⟨hq.trans hq2, hqh.trans hqh2⟩

end CFSG.Quasithin
