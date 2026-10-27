module

public import CFSG.Monster.AxisCount.DenseApplyW

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.B.Rep4371 Matrix

@[expose] def finOf (n : ℕ) : Fin 24 := Fin.ofNat 24 n

theorem finOf_val (n : ℕ) (h : n < 24) : (finOf n : ℕ) = n := by
  simp [finOf, Nat.mod_eq_of_lt h]

theorem finOf_fin (i : Fin 24) : finOf (i : ℕ) = i := Fin.ext (finOf_val _ i.2)

@[expose] noncomputable def zOf (z : ℕ) : PairIdx :=
  s(finOf (Native.aPos z).1, finOf (Native.aPos z).2)

theorem aPos_lt
    (z : ℕ) (hz : z < 300) : (Native.aPos z).1 < 24 ∧ (Native.aPos z).2 < 24 := by
  unfold Native.aPos
  by_cases h : z < 24
  · rw [ite_eq_left h]
    exact ⟨h, h⟩
  · rw [ite_eq_right h]
    obtain ⟨h1, h2, -⟩ := Native.pairTab_spec (z - 24) (by omega)
    exact ⟨lt_trans h1 h2, h2⟩

theorem aIdx_aPos (z : ℕ) (hz : z < 300) :
    Native.aIdx (Native.aPos z).1 (Native.aPos z).2 = z := by
  unfold Native.aPos
  by_cases h : z < 24
  · rw [ite_eq_left h]
    simp [Native.aIdx]
  · rw [ite_eq_right h]
    obtain ⟨h1, h2, h3⟩ := Native.pairTab_spec (z - 24) (by omega)
    have hne : ¬ (Native.pairTab[z - 24]!).1 = (Native.pairTab[z - 24]!).2 := by omega
    unfold Native.aIdx
    rw [ite_eq_right hne, min_eq_left h1.le, max_eq_right h1.le, h3]
    omega

theorem zOf_aIdx
    (i j : Fin 24) : zOf (Native.aIdx i j) = s(i, j) := by
  obtain ⟨-, hpos⟩ := Native.aIdx_spec i j i.2 j.2
  unfold zOf
  rw [hpos]
  rcases le_total (i : ℕ) j with hij | hji
  · rw [min_eq_left hij, max_eq_right hij, finOf_fin, finOf_fin]
  · rw [min_eq_right hji, max_eq_left hji, finOf_fin, finOf_fin, Sym2.eq_swap]

theorem zOf_inj
    (z z' : ℕ) (hz : z < 300) (hz' : z' < 300) (h : zOf z = zOf z') : z = z' := by
  have e1 := aIdx_aPos z hz
  have e2 := aIdx_aPos z' hz'
  obtain ⟨a1, a2⟩ := aPos_lt z hz
  obtain ⟨b1, b2⟩ := aPos_lt z' hz'
  unfold zOf at h
  rw [Sym2.eq_iff] at h
  rw [← e1, ← e2]
  have c1 := finOf_val _ a1
  have c2 := finOf_val _ a2
  have c3 := finOf_val _ b1
  have c4 := finOf_val _ b2
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← c1, h1, c3, ← c2, h2, c4]
  · rw [← c1, h1, c4, ← c2, h2, c3, Native.aIdx_comm]

@[expose] noncomputable def avec (z : ℕ) : SpaceB := inA (basisA (zOf z))

@[expose] noncomputable def xvec (p : ℕ) : SpaceB :=
  inX (Xlift (pauliQ (false, (keyOf p).1, (keyOf p).2)))

private theorem rep_pair_key (k : ℕ × ℕ) : rep (toC k.1, toD k.2) = pauliQ (false, k.1, k.2) := rfl

theorem xvec_eq
    (p : Fin 98280) : xvec p = inX (Pi.single (shortOf p) 1) := by
  have h : rep (shortOf p).1 = pauliQ (false, (keyOf p).1, (keyOf p).2) := rep_pair_key (keyOf p)
  unfold xvec
  rw [← h, Xlift_rep]

@[expose] noncomputable def wvecB (r j : ℕ) : SpaceB :=
  inW (tensor (Pi.single (spinOfRow r) 1) (Pi.single (finOf j) 1))

@[expose] noncomputable def fbasis (k : ℕ) : SpaceB :=
  if k < 300 then avec k
  else if k < 98580 then xvec (k - 300)
  else wvecB ((k - 98580) / 24) ((k - 98580) % 24)

theorem fbasis_A (k : ℕ) (hk : k < 300) : fbasis k = avec k := by
  rw [fbasis, ite_eq_left hk]

theorem fbasis_X (p : ℕ) (hp : p < 98280) : fbasis (300 + p) = xvec p := by
  rw [fbasis, ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem fbasis_W (r j : ℕ) (hj : j < 24) : fbasis (98580 + 24 * r + j) = wvecB r j := by
  rw [fbasis, ite_eq_right (by omega), ite_eq_right (by omega)]
  have e1 : (98580 + 24 * r + j - 98580) / 24 = r := by omega
  have e2 : (98580 + 24 * r + j - 98580) % 24 = j := by omega
  rw [e1, e2]

@[expose] noncomputable def tm (c : ℕ → ℚ) (k : ℕ) : SpaceB := c k • fbasis k

@[expose] def cf (v : Native.DVec) (k : ℕ) : ℚ := (v.D.getD k 0 : ℚ) / 2 ^ v.e

theorem sum_range_split {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ k ∈ Finset.range 196884, F k = ∑ k ∈ Finset.range 300, F k +
      ∑ k ∈ Finset.range 98280, F (300 + k) + ∑ k ∈ Finset.range 98304, F (98580 + k) := by
  have h1 : ∑ k ∈ Finset.range 196884, F k = ∑ k ∈ Finset.range (300 + (98280 + 98304)), F k := rfl
  have h2 : ∀ x : ℕ, 300 + (98280 + x) = 98580 + x := fun x => by omega
  rw [h1, Finset.sum_range_add, Finset.sum_range_add (fun x => F (300 + x)) 98280 98304,
    add_assoc]
  simp only [h2]

theorem sum_inX {ι : Type*} (s : Finset ι) (f : ι → SpaceX) :
    ∑ i ∈ s, inX (f i) = inX (∑ i ∈ s, f i) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [Prod.fst_sum, Prod.snd_sum]

theorem sum_inA {ι : Type*} (s : Finset ι) (f : ι → symMat) :
    ∑ i ∈ s, inA (f i) = inA (∑ i ∈ s, f i) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [Prod.fst_sum, Prod.snd_sum]

theorem sum_inW {ι : Type*} (s : Finset ι) (f : ι → SpaceW) :
    ∑ i ∈ s, inW (f i) = inW (∑ i ∈ s, f i) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [Prod.fst_sum, Prod.snd_sum]

theorem smul_inA (c : ℚ) (A : symMat) : c • inA A = inA (c • A) := by
  simp [Prod.smul_mk]

theorem smul_inX (c : ℚ) (x : SpaceX) : c • inX x = inX (c • x) := by
  simp [Prod.smul_mk]

theorem smul_inW (c : ℚ) (N : SpaceW) : c • inW N = inW (c • N) := by
  simp [Prod.smul_mk]

theorem flat_A (c : ℕ → ℚ) :
    ∑ k ∈ Finset.range 300, tm c k =
      inA (⟨Matrix.of fun i j : Fin 24 => c (Native.aIdx i j), by
        rw [mem_symMat]
        ext i j
        simp only [transpose_apply, of_apply]
        rw [Native.aIdx_comm]⟩ : symMat) := by
  have h1 : ∑ k ∈ Finset.range 300, tm c k =
      ∑ k ∈ Finset.range 300, inA (c k • basisA (zOf k)) :=
    Finset.sum_congr rfl fun k hk => by
      rw [tm, fbasis_A k (Finset.mem_range.1 hk), avec, smul_inA]
  rw [h1, sum_inA]
  congr 1
  apply Subtype.ext
  ext i j
  rw [Submodule.coe_sum, Matrix.sum_apply]
  simp only [Submodule.coe_smul, Matrix.smul_apply, basisA_apply, smul_eq_mul, of_apply]
  rw [Finset.sum_eq_single (Native.aIdx i j)]
  · rw [zOf_aIdx, ite_eq_left rfl, mul_one]
  · intro k hk hne
    have hk' := Finset.mem_range.1 hk
    have : ¬ s(i, j) = zOf k := fun h =>
      hne (zOf_inj k _ hk' (Native.aIdx_spec i j i.2 j.2).1 (by rw [← h, zOf_aIdx]))
    rw [ite_eq_right this, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (Native.aIdx_spec i j i.2 j.2).1) h

theorem flat_X (c : ℕ → ℚ) :
    ∑ k ∈ Finset.range 98280, tm c (300 + k) =
      inX (fun c' : ShortIdx => c (300 + posOf c')) := by
  rw [Finset.sum_range]
  have h1 : ∀ k : Fin 98280, tm c (300 + k) =
      inX (c (300 + posOf (shortEquiv k)) • (Pi.single (shortEquiv k) 1 : SpaceX)) := fun k => by
    rw [tm, fbasis_X k k.2, xvec_eq, smul_inX, shortEquiv_apply, posOf_shortOf]
  rw [Finset.sum_congr rfl fun k _ => h1 k]
  rw [Equiv.sum_comp shortEquiv (fun c' : ShortIdx =>
    inX (c (300 + posOf c') • (Pi.single c' 1 : SpaceX))), sum_inX]
  have := (Pi.basisFun ℚ ShortIdx).sum_repr (fun c' : ShortIdx => c (300 + posOf c'))
  simp only [Pi.basisFun_repr, Pi.basisFun_apply] at this
  exact congrArg inX this

theorem flat_W (c : ℕ → ℚ) :
    ∑ k ∈ Finset.range 98304, tm c (98580 + k) =
      inW (Matrix.of fun (s : SpinIdx) (j : Fin 24) => c (98580 + 24 * rowOf s + j)) := by
  rw [show (98304 : ℕ) = 4096 * 24 from rfl, sum_range_mul24 (fun k => tm c (98580 + k))]
  have h1 : ∀ a ∈ Finset.range 4096, ∑ j ∈ Finset.range 24, tm c (98580 + (a * 24 + j)) =
      ∑ j ∈ Finset.range 24, inW (c (98580 + (a * 24 + j)) •
        tensor (Pi.single (spinOfRow a) 1) (Pi.single (finOf j) 1)) := fun a _ =>
    Finset.sum_congr rfl fun j hj => by
      rw [show 98580 + (a * 24 + j) = 98580 + 24 * a + j by ring, tm,
        fbasis_W a j (Finset.mem_range.1 hj), wvecB, smul_inW]
  rw [Finset.sum_congr rfl h1]
  simp only [sum_inW]
  refine congrArg inW ?_
  ext s' j'
  simp only [Matrix.sum_apply, Matrix.smul_apply, tensor, vecMulVec_apply, of_apply]
  have hrs := rowOf_lt s'
  rw [Finset.sum_eq_single (rowOf s')]
  · rw [Finset.sum_eq_single (j' : ℕ)]
    · have e : 98580 + (rowOf s' * 24 + (j' : ℕ)) = 98580 + 24 * rowOf s' + (j' : ℕ) := by ring
      rw [e, Pi.single_apply, Pi.single_apply, ite_eq_left (spinOfRow_rowOf s').symm,
        ite_eq_left (finOf_fin j').symm, smul_eq_mul, mul_one, mul_one]
    · intro b hb hne
      have hb' := Finset.mem_range.1 hb
      have : ¬ j' = finOf b := fun h => hne (by
        have := congrArg Fin.val h
        rw [finOf_val b hb'] at this
        omega)
      rw [Pi.single_apply (finOf b) (1 : ℚ) j', ite_eq_right this, mul_zero, smul_zero]
    · intro h
      exact absurd (Finset.mem_range.2 j'.2) h
  · intro a ha hne
    have ha' := Finset.mem_range.1 ha
    have : ¬ s' = spinOfRow a := fun h => hne (by
      have := congrArg rowOf h
      rw [rowOf_spinOfRow ha'] at this
      exact this.symm)
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Pi.single_apply (spinOfRow a) (1 : ℚ) s', ite_eq_right this, zero_mul, smul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 hrs) h

theorem interp_eq_sum (v : Native.DVec) :
    interp v = ∑ k ∈ Finset.range 196884, tm (cf v) k := by
  have hs := sum_range_split (tm (cf v))
  have hA := flat_A (cf v)
  have hX := flat_X (cf v)
  have hW := flat_W (cf v)
  refine Eq.trans ?_ hs.symm
  refine Eq.trans ?_ (congrArg₂ (· + ·) (congrArg₂ (· + ·) hA.symm hX.symm) hW.symm)
  simp only [Prod.mk_add_mk, add_zero, zero_add]
  rfl

end CFSG.Monster.AxisCount
