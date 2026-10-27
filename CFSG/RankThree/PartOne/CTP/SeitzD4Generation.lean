module

public import CFSG.RankThree.PartOne.CTP.SeitzD4Data
public import CFSG.ClassicalGroups.Orthogonal.OddOrder
public import CFSG.RankThree.PartOne.CTP.SeitzOrthKernel
public import CFSG.ClassicalGroups.Orthogonal.BasisCheck

public section

namespace CFSG.RankThree.PartOne.CTP.D4Two

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.RankThree.Classical2 (orthDerived)

noncomputable abbrev Qf : QuadraticForm (K2) Vec := quadPlus 4 (K2)

theorem Qf_apply (v : Vec) : Qf v = qf v := quadPlus_apply 4 (K2) v

theorem polar_Qf (v w : Vec) : polar Qf v w = pf v w := polar_quadPlus 4 (K2) v w

@[expose] def glOf (M M' : Matrix Idx Idx (K2)) (h : M * M' = 1) (h' : M' * M = 1) :
    GL Idx (K2) := ⟨M, M', h, h'⟩

@[expose] noncomputable def linOf (M M' : Matrix Idx Idx (K2)) (h : M * M' = 1) (h' : M' * M = 1) :
    Vec ≃ₗ[K2] Vec := toLinEquiv Idx (K2) (glOf M M' h h')

theorem linOf_apply (M M' : Matrix Idx Idx (K2)) (h : M * M' = 1) (h' : M' * M = 1) (v : Vec) :
    linOf M M' h h' v = M.mulVec v := rfl

theorem linOf_mem_orthogonalGroup {M M' : Matrix Idx Idx (K2)} (h : M * M' = 1)
    (h' : M' * M = 1) (hI : IsIsom M) :
    linOf M M' h h' ∈ TauCeti.QuadraticMap.orthogonalGroup Qf := by
  refine mem_orthogonalGroup_of_basis Qf _ (fun i => ?_) (fun i j => ?_)
  · rw [Qf_apply, Qf_apply, linOf_apply]
    exact hI.1 i
  · have e1 := polar_Qf (linOf M M' h h' (Pi.single i 1)) (linOf M M' h h' (Pi.single j 1))
    have e2 := polar_Qf (Pi.single i 1) (Pi.single j 1)
    refine e1.trans (Eq.trans ?_ e2.symm)
    rw [linOf_apply, linOf_apply]
    exact hI.2 i j

theorem mX1_mul : mX1 * mX1 ^ 4 = 1 := by rw [← pow_succ']; exact mX1_pow
theorem mX1_mul' : mX1 ^ 4 * mX1 = 1 := by rw [← pow_succ]; exact mX1_pow
theorem mX2_mul : mX2 * mX2 ^ 4 = 1 := by rw [← pow_succ']; exact mX2_pow
theorem mX2_mul' : mX2 ^ 4 * mX2 = 1 := by rw [← pow_succ]; exact mX2_pow

@[expose] noncomputable def lX1 : Vec ≃ₗ[K2] Vec := linOf mX1 (mX1 ^ 4) mX1_mul mX1_mul'
@[expose] noncomputable def lX2 : Vec ≃ₗ[K2] Vec := linOf mX2 (mX2 ^ 4) mX2_mul mX2_mul'
@[expose] noncomputable def lY1 : Vec ≃ₗ[K2] Vec := linOf mY1 mY1i mY1_mul_inv mY1_inv_mul
@[expose] noncomputable def lY2 : Vec ≃ₗ[K2] Vec := linOf mY2 mY2i mY2_mul_inv mY2_inv_mul
@[expose] noncomputable def lY1i : Vec ≃ₗ[K2] Vec := linOf mY1i mY1 mY1_inv_mul mY1_mul_inv
@[expose] noncomputable def lY2i : Vec ≃ₗ[K2] Vec := linOf mY2i mY2 mY2_inv_mul mY2_mul_inv

theorem lX1_apply (v : Vec) : lX1 v = mX1.mulVec v := rfl
theorem lX2_apply (v : Vec) : lX2 v = mX2.mulVec v := rfl
theorem lY1_apply (v : Vec) : lY1 v = mY1.mulVec v := rfl
theorem lY2_apply (v : Vec) : lY2 v = mY2.mulVec v := rfl
theorem lY1i_apply (v : Vec) : lY1i v = mY1i.mulVec v := rfl
theorem lY2i_apply (v : Vec) : lY2i v = mY2i.mulVec v := rfl

theorem lX1_mem : lX1 ∈ TauCeti.QuadraticMap.orthogonalGroup Qf :=
  linOf_mem_orthogonalGroup _ _ isIsom_mX1
theorem lX2_mem : lX2 ∈ TauCeti.QuadraticMap.orthogonalGroup Qf :=
  linOf_mem_orthogonalGroup _ _ isIsom_mX2
theorem lY1_mem : lY1 ∈ TauCeti.QuadraticMap.orthogonalGroup Qf :=
  linOf_mem_orthogonalGroup _ _ isIsom_mY1
theorem lY2_mem : lY2 ∈ TauCeti.QuadraticMap.orthogonalGroup Qf :=
  linOf_mem_orthogonalGroup _ _ isIsom_mY2
theorem lY1i_mem : lY1i ∈ TauCeti.QuadraticMap.orthogonalGroup Qf :=
  linOf_mem_orthogonalGroup _ _ isIsom_mY1i
theorem lY2i_mem : lY2i ∈ TauCeti.QuadraticMap.orthogonalGroup Qf :=
  linOf_mem_orthogonalGroup _ _ isIsom_mY2i

section PairHom

variable {G : Type*} [Group G]

@[expose] def pairHom (a b : G) (hab : Commute a b) (ha : a ^ 5 = 1) (hb : b ^ 5 = 1) :
    Multiplicative (ZMod 5 × ZMod 5) →* G where
  toFun x := a ^ (Multiplicative.toAdd x).1.val * b ^ (Multiplicative.toAdd x).2.val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
    rw [← pow_eq_pow_mod _ ha, ← pow_eq_pow_mod _ hb, pow_add, pow_add]
    exact (((hab.pow_pow (Multiplicative.toAdd y).1.val
      (Multiplicative.toAdd x).2.val).symm).mul_mul_mul_comm _ _).symm

theorem pairHom_apply (a b : G) (hab : Commute a b) (ha : a ^ 5 = 1) (hb : b ^ 5 = 1)
    (x : Multiplicative (ZMod 5 × ZMod 5)) :
    pairHom a b hab ha hb x =
      a ^ (Multiplicative.toAdd x).1.val * b ^ (Multiplicative.toAdd x).2.val :=
  rfl

end PairHom

@[expose] def gX1 : GL Idx (K2) := glOf mX1 (mX1 ^ 4) mX1_mul mX1_mul'
@[expose] def gX2 : GL Idx (K2) := glOf mX2 (mX2 ^ 4) mX2_mul mX2_mul'

theorem gX1_val : (gX1 : Matrix Idx Idx (K2)) = mX1 := rfl
theorem gX2_val : (gX2 : Matrix Idx Idx (K2)) = mX2 := rfl

theorem gX1_pow : gX1 ^ 5 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, gX1_val, Units.val_one]; exact mX1_pow)
theorem gX2_pow : gX2 ^ 5 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, gX2_val, Units.val_one]; exact mX2_pow)
theorem gX_comm : Commute gX1 gX2 :=
  Units.ext (by rw [Units.val_mul, Units.val_mul, gX1_val, gX2_val]; exact mX_comm)

@[expose] noncomputable def ΦGL : Multiplicative (ZMod 5 × ZMod 5) →* GL Idx (K2) :=
  pairHom gX1 gX2 gX_comm gX1_pow gX2_pow

theorem ΦGL_val (x : Multiplicative (ZMod 5 × ZMod 5)) :
    ((ΦGL x : GL Idx (K2)) : Matrix Idx Idx (K2)) =
      mX (Multiplicative.toAdd x).1.val (Multiplicative.toAdd x).2.val := by
  simp [ΦGL, pairHom_apply, mX, gX1_val, gX2_val, Units.val_pow_eq_pow_val]

@[expose] noncomputable def Φ : Multiplicative (ZMod 5 × ZMod 5) →* (Vec ≃ₗ[K2] Vec) :=
  (toLinEquiv Idx (K2)).toMonoidHom.comp ΦGL

theorem Φ_injective : Function.Injective Φ := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : ΦGL x = 1 := (toLinEquiv Idx (K2)).injective (by simpa [Φ] using hx)
  have h2 := congrArg (fun g : GL Idx (K2) => (g : Matrix Idx Idx (K2))) h1
  simp only [ΦGL_val, Units.val_one] at h2
  obtain ⟨hi, hj⟩ := mX_inj _ _ h2
  have : Multiplicative.toAdd x = 0 := Prod.ext hi hj
  exact toAdd_eq_zero.mp this

@[expose] noncomputable def E₀ : Subgroup (Vec ≃ₗ[K2] Vec) := Φ.range

theorem card_E₀ : Nat.card E₀ = 25 := by
  have := Nat.card_congr (MonoidHom.ofInjective Φ_injective).toEquiv.symm
  rw [E₀, this, Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 5 × ZMod 5) ≃ _),
    Nat.card_prod, Nat.card_zmod]

theorem two_eq_zero_F2 : (2 : K2) = 0 := by decide

theorem orthDerived_eq_elementary : orthDerived Qf = elementaryGroup Qf :=
  commutator_orthogonalGroup_quadPlus (K := K2) (n := 4) (by norm_num)

theorem mem_Ω_of_pow {g : Vec ≃ₗ[K2] Vec} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Qf)
    {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) : g ∈ orthDerived Qf := by
  rw [orthDerived_eq_elementary]
  exact mem_elementaryGroup_quadPlus_of_odd_pow two_eq_zero_F2 (by norm_num) hg hm hgm

theorem linOf_pow_eq_one {M M' : Matrix Idx Idx (K2)} {h : M * M' = 1} {h' : M' * M = 1}
    {n : ℕ} (hn : M ^ n = 1) : linOf M M' h h' ^ n = 1 := by
  unfold linOf
  rw [← map_pow]
  have : glOf M M' h h' ^ n = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val]
    exact hn)
  rw [this, map_one]

theorem lX1_pow : lX1 ^ 5 = 1 := linOf_pow_eq_one mX1_pow
theorem lX2_pow : lX2 ^ 5 = 1 := linOf_pow_eq_one mX2_pow
theorem lY1_pow : lY1 ^ 15 = 1 := linOf_pow_eq_one mY1_pow
theorem lY2_pow : lY2 ^ 15 = 1 := linOf_pow_eq_one mY2_pow
theorem lY1i_pow : lY1i ^ 15 = 1 := linOf_pow_eq_one mY1i_pow
theorem lY2i_pow : lY2i ^ 15 = 1 := linOf_pow_eq_one mY2i_pow

theorem lX1_mem_Ω : lX1 ∈ orthDerived Qf := mem_Ω_of_pow lX1_mem (by decide) lX1_pow
theorem lX2_mem_Ω : lX2 ∈ orthDerived Qf := mem_Ω_of_pow lX2_mem (by decide) lX2_pow
theorem lY1_mem_Ω : lY1 ∈ orthDerived Qf := mem_Ω_of_pow lY1_mem (by decide) lY1_pow
theorem lY2_mem_Ω : lY2 ∈ orthDerived Qf := mem_Ω_of_pow lY2_mem (by decide) lY2_pow
theorem lY1i_mem_Ω : lY1i ∈ orthDerived Qf := mem_Ω_of_pow lY1i_mem (by decide) lY1i_pow
theorem lY2i_mem_Ω : lY2i ∈ orthDerived Qf := mem_Ω_of_pow lY2i_mem (by decide) lY2i_pow

theorem Φ_apply (x : Multiplicative (ZMod 5 × ZMod 5)) :
    Φ x = lX1 ^ (Multiplicative.toAdd x).1.val * lX2 ^ (Multiplicative.toAdd x).2.val := by
  simp only [Φ, ΦGL, pairHom_apply, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    map_mul, map_pow]
  rfl

theorem Φ_mem_Ω (x : Multiplicative (ZMod 5 × ZMod 5)) : Φ x ∈ orthDerived Qf := by
  rw [Φ_apply]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ lX1_mem_Ω _) (Subgroup.pow_mem _ lX2_mem_Ω _)

theorem E₀_le_Ω : E₀ ≤ orthDerived Qf := by
  rintro _ ⟨x, rfl⟩
  exact Φ_mem_Ω x

@[expose] noncomputable def E₀Ω : Subgroup (orthDerived Qf) := E₀.subgroupOf (orthDerived Qf)

theorem card_E₀Ω : Nat.card E₀Ω = 25 := by
  rw [E₀Ω, Nat.card_congr (Subgroup.subgroupOfEquivOfLe E₀_le_Ω).toEquiv, card_E₀]

theorem map_E₀Ω : E₀Ω.map (orthDerived Qf).subtype = E₀ :=
  Subgroup.map_subgroupOf_eq_of_le E₀_le_Ω

@[expose] noncomputable def H : Subgroup (Vec ≃ₗ[K2] Vec) := orthCentralizerSpan Qf E₀Ω

theorem H_le_O : H ≤ TauCeti.QuadraticMap.orthogonalGroup Qf :=
  orthCentralizerSpan_le_orthogonalGroup E₀Ω

theorem mem_H_of_comm {g : Vec ≃ₗ[K2] Vec} (hg : g ∈ orthDerived Qf)
    (a : Multiplicative (ZMod 5 × ZMod 5)) (ha : a ≠ 1) (hc : g * Φ a = Φ a * g) : g ∈ H := by
  refine Subgroup.subset_closure ⟨hg, Φ a, ⟨⟨Φ a, Φ_mem_Ω a⟩, ?_, rfl⟩, ?_, hc⟩
  · exact (Subgroup.mem_subgroupOf).2 ⟨a, rfl⟩
  · intro h
    exact ha (Φ_injective (h.trans (map_one Φ).symm))

theorem comm_Φ_of_matrix {M M' : Matrix Idx Idx K2} {h : M * M' = 1} {h' : M' * M = 1}
    (a : Multiplicative (ZMod 5 × ZMod 5))
    (hc : M * mX (Multiplicative.toAdd a).1.val (Multiplicative.toAdd a).2.val =
      mX (Multiplicative.toAdd a).1.val (Multiplicative.toAdd a).2.val * M) :
    linOf M M' h h' * Φ a = Φ a * linOf M M' h h' := by
  have e1 : linOf M M' h h' * Φ a = toLinEquiv Idx K2 (glOf M M' h h' * ΦGL a) := by
    rw [map_mul]
    rfl
  have e2 : Φ a * linOf M M' h h' = toLinEquiv Idx K2 (ΦGL a * glOf M M' h h') := by
    rw [map_mul]
    rfl
  rw [e1, e2]
  exact congrArg (toLinEquiv Idx K2)
    (Units.ext (by rw [Units.val_mul, Units.val_mul, ΦGL_val]; exact hc))

@[expose] def a01 : Multiplicative (ZMod 5 × ZMod 5) :=
  Multiplicative.ofAdd ((0 : ZMod 5), (1 : ZMod 5))

@[expose] def a13 : Multiplicative (ZMod 5 × ZMod 5) :=
  Multiplicative.ofAdd ((1 : ZMod 5), (3 : ZMod 5))

@[expose] def a12 : Multiplicative (ZMod 5 × ZMod 5) :=
  Multiplicative.ofAdd ((1 : ZMod 5), (2 : ZMod 5))

theorem a01_ne : a01 ≠ 1 := by decide
theorem a13_ne : a13 ≠ 1 := by decide
theorem a12_ne : a12 ≠ 1 := by decide

theorem lX2_eq : lX2 = Φ a01 := by
  rw [Φ_apply]
  have h0 : (0 : ZMod 5).val = 0 := rfl
  have h1 : (1 : ZMod 5).val = 1 := rfl
  simp [a01, h0, h1]

theorem lX2_mem_E₀ : lX2 ∈ E₀ := ⟨a01, lX2_eq.symm⟩

theorem lY1_mem_H : lY1 ∈ H :=
  mem_H_of_comm lY1_mem_Ω a13 a13_ne (comm_Φ_of_matrix a13 mY1_comm)
theorem lY1i_mem_H : lY1i ∈ H :=
  mem_H_of_comm lY1i_mem_Ω a13 a13_ne (comm_Φ_of_matrix a13 mY1i_comm)
theorem lY2_mem_H : lY2 ∈ H :=
  mem_H_of_comm lY2_mem_Ω a12 a12_ne (comm_Φ_of_matrix a12 mY2_comm)
theorem lY2i_mem_H : lY2i ∈ H :=
  mem_H_of_comm lY2i_mem_Ω a12 a12_ne (comm_Φ_of_matrix a12 mY2i_comm)

theorem eichler_mem_H_of_fix {u w : Vec} (hu : mX2.mulVec u = u) (hw : mX2.mulVec w = w) :
    eichler Qf u w ∈ H := by
  have hx : (⟨lX2, lX2_mem_Ω⟩ : orthDerived Qf) ∈ E₀Ω :=
    Subgroup.mem_subgroupOf.2 lX2_mem_E₀
  have hx1 : (⟨lX2, lX2_mem_Ω⟩ : orthDerived Qf) ≠ 1 := by
    intro h
    exact a01_ne (Φ_injective
      ((lX2_eq.symm.trans (congrArg Subtype.val h)).trans (map_one Φ).symm))
  exact eichler_mem_orthCentralizerSpan_of_fix (orthDerived_eq_elementary ▸ le_rfl) hx hx1 hu hw

theorem polar_eq_sum (v w : Vec) : polar Qf v w = ∑ c, w c * polar Qf v (Pi.single c 1) := by
  have h := LinearMap.pi_apply_eq_sum_univ (polarBilin Qf v) w
  simp only [polarBilin_apply_apply, smul_eq_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

theorem span_apply {w : Vec} (hw : polar Qf (bitVec 11) w = 0) :
    spanCols.mulVec (spanCoords.mulVec w) = w := by
  have h1 := congrArg (fun M => M.mulVec w) span_identity
  simp only [← Matrix.mulVec_mulVec] at h1
  rw [h1, Matrix.add_mulVec, Matrix.one_mulVec]
  have h2 : (Matrix.vecMulVec (bitVec 250) (fun c => pf (bitVec 11) (Pi.single c 1))).mulVec w =
      0 := by
    have : (fun c => pf (bitVec 11) (Pi.single c 1)) ⬝ᵥ w = 0 := by
      rw [dotProduct, ← hw, polar_eq_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [polar_Qf, mul_comm]
    rw [Matrix.vecMulVec_mulVec, this, MulOpposite.op_zero, zero_smul]
  rw [h2, add_zero]

theorem eRoot : IsRootCenter Qf H (bitVec 11) := by
  have hHO := H_le_O
  have p116 : eichler Qf (bitVec 11) (bitVec 116) ∈ H :=
    eichler_mem_H_of_fix mX2_fix_11 mX2_fix_116
  have p162 : eichler Qf (bitVec 11) (bitVec 162) ∈ H :=
    eichler_mem_H_of_fix mX2_fix_11 mX2_fix_162
  have w49 : eichler Qf (bitVec 11) (bitVec 49) ∈ H := by
    have h := eichler_mem_of_conj hHO lY1_mem_H (eichler_mem_of_conj hHO lY2_mem_H p116)
    simp only [lY1_apply, lY2_apply] at h
    rw [word3.1, word3.2] at h
    exact h
  have w53 : eichler Qf (bitVec 11) (bitVec 53) ∈ H := by
    have h := eichler_mem_of_conj hHO lY2_mem_H (eichler_mem_of_conj hHO lY1i_mem_H
      (eichler_mem_H_of_fix mX2_fix_111 mX2_fix_169))
    simp only [lY1i_apply, lY2_apply] at h
    rw [word4.1, word4.2] at h
    exact h
  have w77 : eichler Qf (bitVec 11) (bitVec 77) ∈ H := by
    have h := eichler_mem_of_conj hHO lY1i_mem_H (eichler_mem_of_conj hHO lY2_mem_H
      (eichler_mem_H_of_fix mX2_fix_111 mX2_fix_27))
    simp only [lY1i_apply, lY2_apply] at h
    rw [word5.1, word5.2] at h
    exact h
  have w71 : eichler Qf (bitVec 11) (bitVec 71) ∈ H := by
    have h := eichler_mem_of_conj hHO lY2i_mem_H (eichler_mem_of_conj hHO lY1i_mem_H
      (eichler_mem_H_of_fix mX2_fix_11 mX2_fix_214))
    simp only [lY1i_apply, lY2i_apply] at h
    rw [word6.1, word6.2] at h
    exact h
  have hpe := pf_e_w
  refine IsRootCenter.of_span e_ne_zero (by rw [Qf_apply]; exact qf_e)
    {bitVec 116, bitVec 162, bitVec 49, bitVec 53, bitVec 77, bitVec 71} ?_ ?_
  · rintro w (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨by rw [polar_Qf]; exact hpe.1, p116⟩
    · exact ⟨by rw [polar_Qf]; exact hpe.2.1, p162⟩
    · exact ⟨by rw [polar_Qf]; exact hpe.2.2.1, w49⟩
    · exact ⟨by rw [polar_Qf]; exact hpe.2.2.2.1, w53⟩
    · exact ⟨by rw [polar_Qf]; exact hpe.2.2.2.2.1, w77⟩
    · exact ⟨by rw [polar_Qf]; exact hpe.2.2.2.2.2, w71⟩
  · intro w hw
    have key := span_apply hw
    have hmv : ∀ c : Fin 7 → K2, spanCols.mulVec c =
        ∑ j, c j • bitVec (![11, 116, 162, 49, 53, 77, 71] j) := by
      intro c
      funext r
      simp [Matrix.mulVec, dotProduct, spanCols, bitVec, Finset.sum_apply, mul_comm]
    rw [← key, hmv]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    have hb : bitVec (![11, 116, 162, 49, 53, 77, 71] j) ∈ AddSubgroup.closure
        ({bitVec 116, bitVec 162, bitVec 49, bitVec 53, bitVec 77, bitVec 71} ∪ {bitVec 11} :
          Set Vec) := by
      refine AddSubgroup.subset_closure ?_
      fin_cases j <;> simp
    have hc : ∀ c : K2, c = 0 ∨ c = 1 := by decide
    rcases hc ((spanCoords.mulVec w) j) with h | h
    · rw [h, zero_smul]
      exact AddSubgroup.zero_mem _
    · rw [h, one_smul]
      exact hb

@[expose] def hypPairEF : HypPair Qf where
  e := bitVec 11
  f := bitVec 250
  Q_e := by rw [Qf_apply]; exact qf_e
  Q_f := by rw [Qf_apply]; exact qf_f
  polar_ef := by rw [polar_Qf]; exact pf_ef

theorem fRoot : IsRootCenter Qf H (bitVec 250) := by
  have h := IsRootCenter.map H_le_O eRoot lY1_mem_H
  rw [lY1_apply, mY1_e] at h
  exact h

theorem elementaryGroup_le_H : elementaryGroup Qf ≤ H :=
  elementaryGroup_le_of_hypPair (nondegenerate_polarBilin_quadPlus 4 K2) H_le_O hypPairEF eRoot
    fRoot

theorem closure_centralizers_E₀Ω :
    Subgroup.closure {h : orthDerived Qf | ∃ x ∈ E₀Ω, x ≠ 1 ∧ h * x = x * h} = ⊤ :=
  closure_centralizers_eq_top_of_le E₀Ω (orthDerived_eq_elementary ▸ elementaryGroup_le_H)

end CFSG.RankThree.PartOne.CTP.D4Two
