module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.RankThree.PartTwo.Sec4.LThreePiRank

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130Res6Proof

open Matrix CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedScalars)

variable {K : Type} [Field K]

theorem sub_smul_one_mul_sub_smul_one (x : Matrix (Fin 3) (Fin 3) K) (a b : K) :
    (x - a • 1) * (x - b • 1) = x * x - (a + b) • x + (a * b) • 1 := by
  rw [sub_mul, mul_sub, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, smul_smul, add_smul]
  abel

theorem eq_zero_of_forall_mulVec {M : Matrix (Fin 3) (Fin 3) K} (hM : ∀ v, M *ᵥ v = 0) :
    M = 0 := by
  ext i j
  have := congrFun (hM (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem eq_smul_one_or_eq_smul_one {x y : Matrix (Fin 3) (Fin 3) K}
    (hirr : ∀ W : Submodule K (Fin 3 → K), (∀ v ∈ W, y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hxy : x * y = y * x) {α β : K} (h : (x - α • 1) * (x - β • 1) = 0) :
    x = α • 1 ∨ x = β • 1 := by
  have hcomm : (x - α • 1) * y = y * (x - α • 1) := by
    rw [sub_mul, mul_sub, hxy, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  rcases hirr (LinearMap.ker (Matrix.mulVecLin (x - α • 1))) (fun v hv => by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
      rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]) with
    hbot | htop
  · right
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_mulVec fun v => ?_
    have hmem : (x - β • 1) *ᵥ v ∈ LinearMap.ker (Matrix.mulVecLin (x - α • 1)) := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h,
        Matrix.zero_mulVec]
    rw [hbot] at hmem
    exact (Submodule.mem_bot K).mp hmem
  · left
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_mulVec fun v => ?_
    have hmem : v ∈ LinearMap.ker (Matrix.mulVecLin (x - α • 1)) := by
      rw [htop]
      trivial
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hmem

theorem mem_statedScalars_of_commute_of_sq {y w : GL (Fin 3) K}
    (hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hwy : w * y = y * w) (hw2 : w ^ 2 ∈ StatedScalars (Fin 3) K) :
    w ∈ StatedScalars (Fin 3) K := by
  obtain ⟨s, hs⟩ := hw2
  have hd2 : GeneralLinearGroup.det w ^ 2 = s ^ 3 := by
    have h1 := congrArg GeneralLinearGroup.det hs
    rw [map_pow, GeneralLinearGroup.det_scalar, Fintype.card_fin] at h1
    exact h1.symm
  set t : Kˣ := GeneralLinearGroup.det w * s⁻¹ with ht
  have ht2 : t ^ 2 = s := by
    rw [ht, mul_pow, hd2]
    group
  have hww : (w : Matrix (Fin 3) (Fin 3) K) * w = (s : K) • 1 := by
    have h1 := congrArg Units.val hs
    rw [coe_scalar_eq_smul, Units.val_pow_eq_pow_val, sq] at h1
    exact h1.symm
  have hts : (t : K) * (t : K) = s := by
    rw [← sq, ← Units.val_pow_eq_pow_val, ht2]
  have hrel : ((w : Matrix (Fin 3) (Fin 3) K) - (t : K) • 1) *
      ((w : Matrix (Fin 3) (Fin 3) K) - (-(t : K)) • 1) = 0 := by
    rw [sub_smul_one_mul_sub_smul_one, hww, add_neg_cancel, zero_smul, sub_zero, mul_neg, hts,
      neg_smul, add_neg_cancel]
  have hwy' : (w : Matrix (Fin 3) (Fin 3) K) * y = y * w := by
    rw [← Units.val_mul, hwy, Units.val_mul]
  rcases eq_smul_one_or_eq_smul_one hirr hwy' hrel with h | h
  · exact mem_statedScalars_of_eq_smul h t.ne_zero
  · exact mem_statedScalars_of_eq_smul h (neg_ne_zero.mpr t.ne_zero)

variable {π : Bool} {p f : ℕ}

theorem false_of_type2_of_commMod (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x y : GL (Fin 3) K} (hx : Type123 π (p ^ f) K x 2)
    (hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hyx : y * x * y⁻¹ * x⁻¹ ∈ StatedScalars (Fin 3) K) : False := by
  obtain ⟨lam, hlam⟩ := hyx
  have hyx' : y * x * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * x := by
    rw [hlam]
    group
  have hlam1 : lam = 1 := by
    by_contra h
    exact trace_ne_zero_of_type2 hK hq hx (trace_eq_zero_of_conj_eq_scalar_mul h hyx')
  rw [hlam1, map_one, one_mul] at hyx'
  obtain ⟨e, he3, he1, z, hz, g, -, hD⟩ := hx
  have he1' : (e : K) ≠ 1 := fun h => he1 (Units.ext h)
  have hzc := commute_of_mem_statedScalars (mem_statedScalars_of_mem_zPi hK hq he3 he1' hz)
  have hx'y : ((x * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * y = y * (x * z : GL (Fin 3) K)
      := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    calc x * z * y = x * (y * z) := by rw [mul_assoc, ← hzc y]
      _ = y * x * y⁻¹ * (y * z) := by rw [hyx']
      _ = y * (x * z) := by group
  have hx' : x * z = g * diagE e * g⁻¹ := by
    rw [← hD]
    group
  set D : Matrix (Fin 3) (Fin 3) K := diagonal ![(e : K), 1, 1] with hDdef
  have hgg : (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hconj : ∀ a : K, ((x * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - a • 1 =
      g * (D - a • 1) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro a
    rw [hx', Units.val_mul, Units.val_mul, coe_diagE, mul_sub, sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hgg]
  have hDrel : (D - (e : K) • 1) * (D - (1 : K) • 1) = 0 := by
    rw [hDdef]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.one_apply]
  have hrel : (((x * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - (e : K) • 1) *
      (((x * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - (1 : K) • 1) = 0 := by
    rw [hconj, hconj]
    calc g * (D - (e : K) • 1) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (g * (D - (1 : K) • 1) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
        g * ((D - (e : K) • 1) * (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g) *
          (D - (1 : K) • 1)) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one, hDrel,
            Matrix.mul_zero, Matrix.zero_mul]
  have hDx : D = ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((x * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g := by
    rw [hx', hDdef, ← coe_diagE, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  rcases eq_smul_one_or_eq_smul_one hirr hx'y hrel with h | h
  · rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one] at hDx
    have h11 : (1 : K) = e := by simpa [hDdef] using congrFun (congrFun hDx 1) 1
    exact he1' h11.symm
  · rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_smul] at hDx
    have h00 : (e : K) = 1 := by simpa [hDdef] using congrFun (congrFun hDx 0) 0
    exact he1' h00

theorem offDiag_eq_zero_of_sq (h2 : (2 : K) ≠ 0) {a b c e a' b' c' e' : K}
    (h12 : a * b + b * e = 0) (h21 : c * a + e * c = 0) (h12' : a' * b' + b' * e' = 0)
    (h21' : c' * a' + e' * c' = 0) (hc12 : a * b' + b * e' = a' * b + b' * e)
    (hc21 : c * a' + e * c' = c' * a + e' * c) :
    (b = 0 ∧ c = 0) ∨ (b' = 0 ∧ c' = 0) ∨ (a * b' + b * e' = 0 ∧ c * a' + e * c' = 0) := by
  by_cases hbc : b = 0 ∧ c = 0
  · exact Or.inl hbc
  by_cases hbc' : b' = 0 ∧ c' = 0
  · exact Or.inr (Or.inl hbc')
  right
  right
  have htr : a + e = 0 := by
    by_contra h
    apply hbc
    constructor
    · have : b * (a + e) = 0 := by linear_combination h12
      exact (mul_eq_zero.mp this).resolve_right h
    · have : c * (a + e) = 0 := by linear_combination h21
      exact (mul_eq_zero.mp this).resolve_right h
  have htr' : a' + e' = 0 := by
    by_contra h
    apply hbc'
    constructor
    · have : b' * (a' + e') = 0 := by linear_combination h12'
      exact (mul_eq_zero.mp this).resolve_right h
    · have : c' * (a' + e') = 0 := by linear_combination h21'
      exact (mul_eq_zero.mp this).resolve_right h
  have he : e = -a := by linear_combination htr
  have he' : e' = -a' := by linear_combination htr'
  subst he he'
  constructor
  · have : 2 * (a * b' + b * -a') = 0 := by linear_combination hc12
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : 2 * (c * a' + -a * c') = 0 := by linear_combination hc21
    exact (mul_eq_zero.mp this).resolve_left h2

theorem entry_eq_zero_of_commute_diagonal {m : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K}
    (h : m * diagonal d = diagonal d * m) {r s : Fin 3} (hrs : d r ≠ d s) : m r s = 0 := by
  have h1 := congrFun (congrFun h r) s
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have h2 : (d s - d r) * m r s = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hrs))

theorem eq_or_eq_or_eq_of_distinct :
    ∀ i j k r : Fin 3, i ≠ j → i ≠ k → j ≠ k → r = i ∨ r = j ∨ r = k := by
  decide

theorem mul_apply_of_distinct (m n : Matrix (Fin 3) (Fin 3) K) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (r s : Fin 3) :
    (m * n) r s = m r i * n i s + m r j * n j s + m r k * n k s := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring

theorem isDiag_or_of_block (h2 : (2 : K) ≠ 0) {m n : Matrix (Fin 3) (Fin 3) K} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {s s' : K} (hm : m * m = s • 1) (hn : n * n = s' • 1)
    (hmn : m * n = n * m) (hm0 : m i j = 0 ∧ m i k = 0 ∧ m j i = 0 ∧ m k i = 0)
    (hn0 : n i j = 0 ∧ n i k = 0 ∧ n j i = 0 ∧ n k i = 0) :
    m.IsDiag ∨ n.IsDiag ∨ (m * n).IsDiag := by
  obtain ⟨mij, mik, mji, mki⟩ := hm0
  obtain ⟨nij, nik, nji, nki⟩ := hn0
  have e := fun (a b : Matrix (Fin 3) (Fin 3) K) r s => mul_apply_of_distinct a b hij hik hjk r s
  have hmjk := congrFun (congrFun hm j) k
  have hmkj := congrFun (congrFun hm k) j
  have hnjk := congrFun (congrFun hn j) k
  have hnkj := congrFun (congrFun hn k) j
  have hcjk := congrFun (congrFun hmn j) k
  have hckj := congrFun (congrFun hmn k) j
  rw [e] at hmjk hmkj hnjk hnkj hcjk hckj
  rw [e] at hcjk hckj
  simp only [Matrix.smul_apply, Matrix.one_apply_ne hjk, Matrix.one_apply_ne (Ne.symm hjk),
    smul_zero, mji, mki, nji, nki, zero_mul, zero_add] at hmjk hmkj hnjk hnkj hcjk hckj
  have hdiag : ∀ x : Matrix (Fin 3) (Fin 3) K, x i j = 0 → x i k = 0 → x j i = 0 → x k i = 0 →
      x j k = 0 → x k j = 0 → x.IsDiag := by
    intro x xij xik xji xki xjk xkj r t hrt
    rcases eq_or_eq_or_eq_of_distinct i j k r hij hik hjk with rfl | rfl | rfl <;>
      rcases eq_or_eq_or_eq_of_distinct _ _ _ t hij hik hjk with rfl | rfl | rfl <;>
      first | exact absurd rfl hrt | assumption
  rcases offDiag_eq_zero_of_sq h2 hmjk hmkj hnjk hnkj hcjk hckj with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ |
      ⟨h1, h1'⟩
  · exact Or.inl (hdiag m mij mik mji mki h1 h1')
  · exact Or.inr (Or.inl (hdiag n nij nik nji nki h1 h1'))
  · refine Or.inr (Or.inr (hdiag (m * n) ?_ ?_ ?_ ?_ ?_ ?_))
    · rw [e]
      simp [mij, mik, nij]
    · rw [e]
      simp [mij, mik, nik]
    · rw [e]
      simp [mji, nji, nki]
    · rw [e]
      simp [mki, nji, nki]
    · rw [e]
      simpa [mji, nik] using h1
    · rw [e]
      simpa [mki, nij] using h1'

theorem isDiag_or_of_commute_diagonal (h2 : (2 : K) ≠ 0) {d : Fin 3 → K}
    (hd : ¬ (d 0 = d 1 ∧ d 1 = d 2)) {m n : Matrix (Fin 3) (Fin 3) K} {s s' : K}
    (hm : m * m = s • 1) (hn : n * n = s' • 1) (hmn : m * n = n * m)
    (hmd : m * diagonal d = diagonal d * m) (hnd : n * diagonal d = diagonal d * n) :
    m.IsDiag ∨ n.IsDiag ∨ (m * n).IsDiag := by
  have zm := fun {r s : Fin 3} (h : d r ≠ d s) => entry_eq_zero_of_commute_diagonal hmd h
  have zn := fun {r s : Fin 3} (h : d r ≠ d s) => entry_eq_zero_of_commute_diagonal hnd h
  by_cases h01 : d 0 = d 1
  · have h12 : d 1 ≠ d 2 := fun h => hd ⟨h01, h⟩
    have h02 : d 0 ≠ d 2 := by rwa [h01]
    exact isDiag_or_of_block h2 (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)
      hm hn hmn ⟨zm (Ne.symm h02), zm (Ne.symm h12), zm h02, zm h12⟩
      ⟨zn (Ne.symm h02), zn (Ne.symm h12), zn h02, zn h12⟩
  · by_cases h12 : d 1 = d 2
    · have h02 : d 0 ≠ d 2 := by rwa [← h12]
      exact isDiag_or_of_block h2 (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
        hm hn hmn ⟨zm h01, zm h02, zm (Ne.symm h01), zm (Ne.symm h02)⟩
        ⟨zn h01, zn h02, zn (Ne.symm h01), zn (Ne.symm h02)⟩
    · by_cases h02 : d 0 = d 2
      ·
        have h10 : d 1 ≠ d 0 := Ne.symm h01
        have h12' : d 1 ≠ d 2 := h12
        exact isDiag_or_of_block h2 (i := 1) (j := 0) (k := 2) (by decide) (by decide)
          (by decide) hm hn hmn ⟨zm h10, zm h12', zm h01, zm (Ne.symm h12')⟩
          ⟨zn h10, zn h12', zn h01, zn (Ne.symm h12')⟩
      ·
        left
        intro r t hrt
        refine zm ?_
        have cover : ∀ r : Fin 3, r = 0 ∨ r = 1 ∨ r = 2 := by decide
        rcases cover r with rfl | rfl | rfl <;> rcases cover t with rfl | rfl | rfl <;>
          first | exact absurd rfl hrt | exact h01 | exact Ne.symm h01 | exact h12 |
            exact Ne.symm h12 | exact h02 | exact Ne.symm h02

end CFSG.RankThree.PartTwo.Sec21.Item2130Res6Proof
