module

public import CFSG.Monster.Griess.Invariance.Diagonal
public import CFSG.Monster.Griess.Invariance.TwoCoord.Triangle
public import CFSG.Monster.Griess.TrilinearData

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice Matrix

namespace TwoCoordInvariance

open DiagonalInvariance

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

@[expose] def pc (p : LtPair) (μ : ZMod 2) : ShortIdx :=
  if μ = 0 then labelIdx (.inl p) else labelIdx (.inr (.inl p))

theorem pc_zero (p : LtPair) : pc p 0 = labelIdx (.inl p) := ite_eq_left rfl

theorem pc_one (p : LtPair) : pc p 1 = labelIdx (.inr (.inl p)) := ite_eq_right (by decide)

theorem pc_fst (p : LtPair) (μ : ZMod 2) : (pc p μ).1 = (μ • ΩC, deltaPair p.1.1 p.1.2) := by
  rcases zmod2_cases μ with rfl | rfl
  · rw [pc_zero, zero_smul]
    exact coordOf_rMinus p.1.1 p.1.2
  · rw [pc_one, one_smul]
    refine (coordOf_rPlus p.1.1 p.1.2).trans ?_
    rw [thetaD_ΩC, zero_add]

theorem pc_inj {p q : LtPair} {μ ν : ZMod 2} : pc p μ = pc q ν ↔ p = q ∧ μ = ν := by
  constructor
  · intro h
    rcases zmod2_cases μ with rfl | rfl <;> rcases zmod2_cases ν with rfl | rfl <;>
      simp only [pc_zero, pc_one] at h <;> have h' := labelIdx_injective h <;> simp_all
  · rintro ⟨rfl, rfl⟩
    rfl

theorem pc_zero_ne_one (p q : LtPair) : pc p 0 ≠ pc q 1 := fun h =>
  absurd (pc_inj.1 h).2 (by decide)

theorem pc_one_ne_zero (p q : LtPair) : pc p 1 ≠ pc q 0 := fun h =>
  absurd (pc_inj.1 h).2 (by decide)

abbrev Ap (p : LtPair) : symMat := basisA (ltEdge p)

@[expose] def xv (p : LtPair) (s : ℚ) : SpaceX := Pi.single (pc p 0) 1 + s • Pi.single (pc p 1) 1

theorem tbasis_pair_zero' (p : LtPair) : tbasis (.inr (.inl (p, 0))) = inA (Ap p) :=
  tbasis_pair_zero p

theorem tbasis_pair_one' (p : LtPair) : tbasis (.inr (.inl (p, 1))) = inX (xv p (-1)) := by
  have hXm : Xlift (rMinus p.1.1 p.1.2) = Pi.single (labelIdx (.inl p)) 1 :=
    Xlift_labelElt (.inl p)
  have hXp : Xlift (rPlus p.1.1 p.1.2) = Pi.single (labelIdx (.inr (.inl p))) 1 :=
    Xlift_labelElt (.inr (.inl p))
  rw [tbasis_pair_one, hXm, hXp, xv, pc_zero, pc_one, neg_one_smul, ← sub_eq_add_neg]

theorem tbasis_pair_two' (p : LtPair) : tbasis (.inr (.inl (p, 2))) = inX (xv p 1) := by
  have hXm : Xlift (rMinus p.1.1 p.1.2) = Pi.single (labelIdx (.inl p)) 1 :=
    Xlift_labelElt (.inl p)
  have hXp : Xlift (rPlus p.1.1 p.1.2) = Pi.single (labelIdx (.inr (.inl p))) 1 :=
    Xlift_labelElt (.inr (.inl p))
  rw [tbasis_pair_two, hXm, hXp, xv, pc_zero, pc_one, one_smul]

theorem inX_add (x y : SpaceX) : inX (x + y) = inX x + inX y :=
  Prod.ext (zero_add (0 : symMat)).symm (Prod.ext rfl (zero_add (0 : SpaceW)).symm)

theorem qf_add (c : ShortIdx) (M N : Matrix (Fin 24) (Fin 24) ℚ) :
    qf c (M + N) = qf c M + qf c N := by
  simp only [qf, add_mulVec, dotProduct_add]

theorem qf_Ap (c : ShortIdx) (p : LtPair) : qf c (Ap p) = 2 * (uQ c p.1.1 * uQ c p.1.2) := by
  rw [Ap, coe_basisA_ltPair, qf_add, qf_single, qf_single]
  ring

theorem vMinus_mul_vMinus {a b i j : Fin 24} (hab : a < b) (hij : i < j) :
    vMinus a b i * vMinus a b j = if i = a ∧ j = b then -16 else 0 := by
  rw [vMinus_apply, vMinus_apply]
  by_cases h1 : i = a
  · subst h1
    have hji : j ≠ i := (ne_of_lt hij).symm
    by_cases h2 : j = b
    · subst h2
      simp [hji, (ne_of_lt hab)]
    · simp [hji, h2]
  · by_cases h3 : i = b
    · subst h3
      have hja : j ≠ a := fun h => lt_asymm hab (h ▸ hij)
      have hjb : j ≠ i := (ne_of_lt hij).symm
      simp [h1, hja, hjb]
    · simp [h1, h3]

theorem vPlus_mul_vPlus {a b i j : Fin 24} (hab : a < b) (hij : i < j) :
    vPlus a b i * vPlus a b j = if i = a ∧ j = b then 16 else 0 := by
  rw [vPlus_apply, vPlus_apply]
  by_cases h1 : i = a
  · subst h1
    have hji : j ≠ i := (ne_of_lt hij).symm
    by_cases h2 : j = b
    · subst h2
      simp [hji, (ne_of_lt hab)]
    · simp [hji, h2]
  · by_cases h3 : i = b
    · subst h3
      have hja : j ≠ a := fun h => lt_asymm hab (h ▸ hij)
      have hjb : j ≠ i := (ne_of_lt hij).symm
      simp [h1, hja, hjb]
    · simp [h1, h3]

theorem ltPair_eq_iff (p q : LtPair) : (p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) ↔ p = q :=
  ⟨fun h => ltPair_eq h.1 h.2, fun h => h ▸ ⟨rfl, rfl⟩⟩

theorem qf_pc_zero_Ap (q p : LtPair) : qf (pc q 0) (Ap p) = if p = q then -32 else 0 := by
  rw [qf_Ap, pc_zero, uQ_mul_uQ_labelIdx]
  change 2 * ((vMinus q.1.1 q.1.2 p.1.1 * vMinus q.1.1 q.1.2 p.1.2 : ℤ) : ℚ) = _
  rw [vMinus_mul_vMinus q.2 p.2]
  by_cases h : p = q
  · rw [ite_eq_left ((ltPair_eq_iff p q).2 h), ite_eq_left h]
    norm_num
  · rw [ite_eq_right (fun h' => h ((ltPair_eq_iff p q).1 h')), ite_eq_right h]
    norm_num

theorem qf_pc_one_Ap (q p : LtPair) : qf (pc q 1) (Ap p) = if p = q then 32 else 0 := by
  rw [qf_Ap, pc_one, uQ_mul_uQ_labelIdx]
  change 2 * ((vPlus q.1.1 q.1.2 p.1.1 * vPlus q.1.1 q.1.2 p.1.2 : ℤ) : ℚ) = _
  rw [vPlus_mul_vPlus q.2 p.2]
  by_cases h : p = q
  · rw [ite_eq_left ((ltPair_eq_iff p q).2 h), ite_eq_left h]
    norm_num
  · rw [ite_eq_right (fun h' => h ((ltPair_eq_iff p q).1 h')), ite_eq_right h]
    norm_num

theorem T_inX_single3 (c₁ c₂ c₃ : ShortIdx) :
    T (inX (Pi.single c₁ 1)) (inX (Pi.single c₂ 1)) (inX (Pi.single c₃ 1)) = tau c₁ c₂ c₃ := by
  have h := sum3_single c₁ c₂ c₃ 1 1 1
  simp only [one_smul, one_mul] at h
  rw [T_XXX, h]

theorem T_inX_single2_inA (a b : ShortIdx) (A : symMat) :
    T (inX (Pi.single a 1)) (inX (Pi.single b 1)) (inA A) = if b = a then qf a A / 8 else 0 := by
  have h := sum_single_mul_single a b 1 1 (fun c => qf c A)
  simp only [one_smul, one_mul] at h
  rw [T_XXA, h]
  split_ifs <;> ring

theorem ΩC_ne_zero : ΩC ≠ 0 := fun h => by
  have h' := congrArg μ₀ h
  rw [μ₀_ΩC, map_zero] at h'
  exact absurd h' (by decide)

theorem tau_pc (p q r : LtPair) (μ₁ μ₂ μ₃ : ZMod 2) :
    tau (pc p μ₁) (pc q μ₂) (pc r μ₃) = if μ₃ = μ₁ + μ₂ ∧ IsPairTriangle p q r then 1 else 0 := by
  have hc : (pc r μ₃).1 = (pc p μ₁).1 + (pc q μ₂).1 ↔ μ₃ = μ₁ + μ₂ ∧ IsPairTriangle p q r := by
    rw [pc_fst, pc_fst, pc_fst, Prod.mk_add_mk, Prod.mk.injEq, ← add_smul,
      smul_left_inj ΩC_ne_zero, deltaPair_eq_add_iff]
  unfold tau
  by_cases h : μ₃ = μ₁ + μ₂ ∧ IsPairTriangle p q r
  · rw [ite_eq_left (hc.2 h), ite_eq_left h, pc_fst q μ₂, pc_fst p μ₁]
    change sgn (pair (μ₂ • ΩC) (deltaPair p.1.1 p.1.2)) = 1
    rw [pair_smul_left, pair_ΩC_deltaPair, mul_zero, sgn_zero]
  · rw [ite_eq_right (fun h' => h (hc.1 h')), ite_eq_right h]

theorem tau_pc_of_eq (p q r : LtPair) {μ₁ μ₂ μ₃ : ZMod 2} (h : μ₃ = μ₁ + μ₂) :
    tau (pc p μ₁) (pc q μ₂) (pc r μ₃) = if IsPairTriangle p q r then 1 else 0 := by
  rw [tau_pc]
  by_cases ht : IsPairTriangle p q r
  · rw [ite_eq_left ⟨h, ht⟩, ite_eq_left ht]
  · rw [ite_eq_right (fun h' => ht h'.2), ite_eq_right ht]

theorem tau_pc_of_ne (p q r : LtPair) {μ₁ μ₂ μ₃ : ZMod 2} (h : μ₃ ≠ μ₁ + μ₂) :
    tau (pc p μ₁) (pc q μ₂) (pc r μ₃) = 0 := by
  rw [tau_pc, ite_eq_right (fun h' => h h'.1)]

theorem T_Ap3 (p q r : LtPair) :
    T (inA (Ap p)) (inA (Ap q)) (inA (Ap r)) = if IsPairTriangle p q r then 4 else 0 := by
  rw [T_AAA, trace_basisA_mul3]
  split_ifs <;> ring

theorem T_xv2_Ap (p q r : LtPair) (s s' : ℚ) :
    T (inX (xv q s)) (inX (xv r s')) (inA (Ap p)) =
      if p = q ∧ q = r then 4 * (s * s' - 1) else 0 := by
  simp only [xv, inX_add, smul_inX, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    T_inX_single2_inA, smul_eq_mul]
  rw [ite_eq_right (pc_zero_ne_one r q), ite_eq_right (pc_one_ne_zero r q)]
  by_cases hrq : r = q
  · subst hrq
    rw [ite_eq_left rfl, ite_eq_left rfl, qf_pc_zero_Ap, qf_pc_one_Ap]
    by_cases hp : p = r
    · rw [ite_eq_left hp, ite_eq_left hp, ite_eq_left ⟨hp, rfl⟩]
      ring
    · rw [ite_eq_right hp, ite_eq_right hp, ite_eq_right (fun h => hp h.1)]
      ring
  · have h0 : ¬ pc r 0 = pc q 0 := fun h => hrq (pc_inj.1 h).1
    have h1 : ¬ pc r 1 = pc q 1 := fun h => hrq (pc_inj.1 h).1
    rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right (fun h => hrq (h.2.symm))]
    ring

theorem T_xv3 (p q r : LtPair) (s₁ s₂ s₃ : ℚ) :
    T (inX (xv p s₁)) (inX (xv q s₂)) (inX (xv r s₃)) =
      if IsPairTriangle p q r then 1 + s₁ * s₂ + s₁ * s₃ + s₂ * s₃ else 0 := by
  have t000 := tau_pc_of_eq p q r (μ₁ := 0) (μ₂ := 0) (μ₃ := 0) (by decide)
  have t001 := tau_pc_of_ne p q r (μ₁ := 0) (μ₂ := 0) (μ₃ := 1) (by decide)
  have t010 := tau_pc_of_ne p q r (μ₁ := 0) (μ₂ := 1) (μ₃ := 0) (by decide)
  have t011 := tau_pc_of_eq p q r (μ₁ := 0) (μ₂ := 1) (μ₃ := 1) (by decide)
  have t100 := tau_pc_of_ne p q r (μ₁ := 1) (μ₂ := 0) (μ₃ := 0) (by decide)
  have t101 := tau_pc_of_eq p q r (μ₁ := 1) (μ₂ := 0) (μ₃ := 1) (by decide)
  have t110 := tau_pc_of_eq p q r (μ₁ := 1) (μ₂ := 1) (μ₃ := 0) (by decide)
  have t111 := tau_pc_of_ne p q r (μ₁ := 1) (μ₂ := 1) (μ₃ := 1) (by decide)
  simp only [xv, inX_add, smul_inX, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    T_inX_single3, smul_eq_mul, t000, t001, t010, t011, t100, t101, t110, t111]
  split_ifs <;> ring

theorem T_inA_inX_inA (A A' : symMat) (x : SpaceX) : T (inA A) (inX x) (inA A') = 0 := by
  rw [T_swap23, T_AAX]

theorem T_inX_inA_inA (A A' : symMat) (x : SpaceX) : T (inX x) (inA A) (inA A') = 0 := by
  rw [T_cycle, T_AAX]

theorem T_Ap_xv2 (p q r : LtPair) (s s' : ℚ) :
    T (inA (Ap p)) (inX (xv q s)) (inX (xv r s')) =
      if p = q ∧ q = r then 4 * (s * s' - 1) else 0 := by
  rw [T_cycle, T_xv2_Ap]

theorem T_xv_Ap_xv (p q r : LtPair) (s s' : ℚ) :
    T (inX (xv p s)) (inA (Ap q)) (inX (xv r s')) =
      if p = q ∧ q = r then 4 * (s * s' - 1) else 0 := by
  rw [T_swap23, T_xv2_Ap]
  exact ite_cond_congr (propext ⟨fun h => ⟨h.1.symm, h.1.trans h.2⟩,
    fun h => ⟨h.1.symm, h.1.trans h.2⟩⟩)

theorem T_xv2_Ap' (p q r : LtPair) (s s' : ℚ) :
    T (inX (xv p s)) (inX (xv q s')) (inA (Ap r)) =
      if p = q ∧ q = r then 4 * (s * s' - 1) else 0 := by
  rw [T_xv2_Ap]
  refine ite_cond_congr (propext ⟨fun h => ⟨h.2, h.2.symm.trans h.1.symm⟩, fun h => ⟨?_, h.1⟩⟩)
  exact (h.1.trans h.2).symm

theorem T_diag_tbasis (k : Fin 24) (y z : TIdx) :
    T (tbasis (.inl k)) (tbasis y) (tbasis z) = diagEig k y * (if y = z then tnorm y else 0) := by
  have e : tbasis (.inl k) = inA (basisA s(k, k)) := tbasis_diag k
  calc T (tbasis (.inl k)) (tbasis y) (tbasis z) =
        bform (gmul (inA (basisA s(k, k))) (tbasis y)) (tbasis z) := by rw [e]; rfl
    _ = diagEig k y * (if y = z then tnorm y else 0) := by
        rw [gmul_Ekk_tbasis, map_smul, LinearMap.smul_apply, bform_tbasis, smul_eq_mul]

end TwoCoordInvariance

end CFSG.Monster.Griess
