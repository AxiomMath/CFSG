module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagNormalXBlk
public import CFSG.LocalAnalysis.StandardType.PhanEResOrbit

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.ClassicalInvolution.Phan.PhanE.Flag

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

@[expose] noncomputable def swap22 (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3).permMatrix K

private def pls22_pi : Equiv.Perm (Fin 4) := Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3

private theorem pls22_pi_zero : pls22_pi 0 = (2 : Fin 4) := rfl
private theorem pls22_pi_one : pls22_pi 1 = (3 : Fin 4) := rfl
private theorem pls22_pi_two : pls22_pi 2 = (0 : Fin 4) := rfl
private theorem pls22_pi_three : pls22_pi 3 = (1 : Fin 4) := rfl

private theorem pls22_pi_symm : pls22_pi.symm = pls22_pi := by
  apply Equiv.ext
  intro i
  rw [Equiv.symm_apply_eq]
  fin_cases i <;> rfl

private theorem pls22_pi_mul_self : pls22_pi * pls22_pi = (1 : Equiv.Perm (Fin 4)) := by
  apply Equiv.ext
  intro i
  fin_cases i <;> decide

private theorem pls22_conj_apply (M : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    (swap22 K * M * swap22 K) i j = M (pls22_pi i) (pls22_pi j) := by
  rw [show swap22 K = pls22_pi.toPEquiv.toMatrix from rfl,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, pls22_pi_symm]
  rfl

private theorem pls22_BDA_cross {A : Matrix (Fin 4) (Fin 4) K}
    (hA : BlockDiag [0, 2, 4] A) :
    A 0 2 = 0 ∧ A 0 3 = 0 ∧ A 1 2 = 0 ∧ A 1 3 = 0 ∧
      A 2 0 = 0 ∧ A 3 0 = 0 ∧ A 2 1 = 0 ∧ A 3 1 = 0 := by
  have h0 := hA 0 (by decide)
  exact ⟨(h0 0 2 (by decide) (by decide)).1, (h0 0 3 (by decide) (by decide)).1,
    (h0 1 2 (by decide) (by decide)).1, (h0 1 3 (by decide) (by decide)).1,
    (h0 0 2 (by decide) (by decide)).2, (h0 0 3 (by decide) (by decide)).2,
    (h0 1 2 (by decide) (by decide)).2, (h0 1 3 (by decide) (by decide)).2⟩

private theorem pls22_blockDiag_conj {A : Matrix (Fin 4) (Fin 4) K}
    (hA : BlockDiag [0, 2, 4] A) :
    BlockDiag [0, 2, 4] (swap22 K * A.map (sg K f) * swap22 K) := by
  obtain ⟨h02, h03, h12, h13, h20, h30, h21, h31⟩ := pls22_BDA_cross hA
  have hd0 : ([0, 2, 4] : List ℕ).getD 0 0 = 0 := by decide
  have hd01 : ([0, 2, 4] : List ℕ).getD (0 + 1) 0 = 2 := by decide
  have hd1 : ([0, 2, 4] : List ℕ).getD 1 0 = 2 := by decide
  have hd11 : ([0, 2, 4] : List ℕ).getD (1 + 1) 0 = 4 := by decide
  have hentry : ∀ i j : Fin 4, (swap22 K * A.map (sg K f) * swap22 K) i j =
      sg K f (A (pls22_pi i) (pls22_pi j)) := by
    intro i j
    rw [pls22_conj_apply, Matrix.map_apply]
  intro b hb i j hi hj
  have hb3 : b + 1 < 3 := by simpa using hb
  have hb' : b = 0 ∨ b = 1 := by omega
  constructor
  · rw [hentry]
    rcases hb' with rfl | rfl
    · rw [hd0, hd01] at hi hj
      fin_cases i <;> fin_cases j <;>
        simp_all [pls22_pi_zero, pls22_pi_one, pls22_pi_two, pls22_pi_three,
          h02, h03, h12, h13, h20, h30, h21, h31]
    · rw [hd1, hd11] at hi hj
      fin_cases i <;> fin_cases j <;>
        simp_all [pls22_pi_zero, pls22_pi_one, pls22_pi_two, pls22_pi_three,
          h02, h03, h12, h13, h20, h30, h21, h31]
  · rw [hentry]
    rcases hb' with rfl | rfl
    · rw [hd0, hd01] at hi hj
      fin_cases i <;> fin_cases j <;>
        simp_all [pls22_pi_zero, pls22_pi_one, pls22_pi_two, pls22_pi_three,
          h02, h03, h12, h13, h20, h30, h21, h31]
    · rw [hd1, hd11] at hi hj
      fin_cases i <;> fin_cases j <;>
        simp_all [pls22_pi_zero, pls22_pi_one, pls22_pi_two, pls22_pi_three,
          h02, h03, h12, h13, h20, h30, h21, h31]

theorem swap22_mul_self (K : Type) [Field K] : swap22 K * swap22 K = 1 := by
  calc swap22 K * swap22 K = pls22_pi.permMatrix K * pls22_pi.permMatrix K := rfl
    _ = (pls22_pi * pls22_pi).permMatrix K := (Matrix.permMatrix_mul _ _).symm
    _ = 1 := by rw [pls22_pi_mul_self, Matrix.permMatrix_one]

private theorem pls22_jShiftInv_mulVec {A B : Matrix (Fin 4) (Fin 4) K}
    (hA : BlockDiag [0, 2, 4] A)
    (hB : ∀ i j, B i j = sg K f (A (pls22_pi i) (pls22_pi j))) (v : Fin 4 → K) :
    jShiftInv K f (A *ᵥ v) = B *ᵥ jShiftInv K f v := by
  obtain ⟨h02, h03, h12, h13, h20, h21, h30, h31⟩ := pls22_BDA_cross hA
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four, hB, pls22_pi_zero, pls22_pi_one,
      pls22_pi_two, pls22_pi_three, h02, h03, h12, h13, h20, h21, h30, h31, jShiftInv,
      map_add, map_mul] <;>
    ring

private theorem pls22_jShift_mulVec {A B : Matrix (Fin 4) (Fin 4) K}
    (hA : BlockDiag [0, 2, 4] A)
    (hB : ∀ i j, B i j = sg K f (A (pls22_pi i) (pls22_pi j))) (v : Fin 4 → K) :
    jShift K f (A *ᵥ v) = B *ᵥ jShift K f v := by
  obtain ⟨h02, h03, h12, h13, h20, h21, h30, h31⟩ := pls22_BDA_cross hA
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four, hB, pls22_pi_zero, pls22_pi_one,
      pls22_pi_two, pls22_pi_three, h02, h03, h12, h13, h20, h21, h30, h31, jShift,
      map_add, map_mul] <;>
    ring

private theorem pls22_jShiftInv_smul (c : K) (v : Fin 4 → K) :
    jShiftInv K f (c • v) = sg K f c • jShiftInv K f v := by
  funext i; fin_cases i <;> simp [jShiftInv, map_mul]

private theorem pls22_jShiftInv_e2 :
    jShiftInv K f (Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K) =
      (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by
  funext i; fin_cases i <;> simp [jShiftInv]

private theorem pls22_span_jShiftInv_Vsub3 (hK : Nat.card K = (2 ^ f) ^ 2) :
    Submodule.span K (jShiftInv K f '' (Vsub (K := K) 4 3 : Set (Fin 4 → K))) =
      Vsub (K := K) 4 1 := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w ⟨v, hv, rfl⟩
    have hv3 : v 3 = 0 := hv 3 (by norm_num)
    intro j hj
    fin_cases j <;> simp_all [jShiftInv]
  · intro w hw
    have hw1 : w 1 = 0 := hw 1 (by norm_num)
    have hw2 : w 2 = 0 := hw 2 (by norm_num)
    have hw3 : w 3 = 0 := hw 3 (by norm_num)
    refine Submodule.subset_span
      ⟨sg K f (w 0) • (Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K), ?_, ?_⟩
    · intro j hj
      fin_cases j <;> simp_all [Pi.single_apply]
    · rw [pls22_jShiftInv_smul, pls22_jShiftInv_e2, sg_sg hK]
      funext j
      fin_cases j <;> simp [Pi.smul_apply, Pi.single_apply, hw1, hw2, hw3]

private theorem pls22_span_jShift_Vsub1 :
    Submodule.span K (jShift K f '' (Vsub (K := K) 4 1 : Set (Fin 4 → K))) =
      Submodule.span K {(Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K)} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w ⟨v, hv, rfl⟩
    have hv1 : v 1 = 0 := hv 1 (by norm_num)
    have hval : jShift K f v =
        sg K f (v 0) • (Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K) := by
      funext j
      fin_cases j <;> simp [jShift, Pi.single_apply, hv1]
    rw [hval]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine Submodule.subset_span ?_
    refine ⟨(Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K), ?_, ?_⟩
    · intro j hj
      fin_cases j <;> simp_all [Pi.single_apply]
    · funext j
      fin_cases j <;> simp [jShift, Pi.single_apply]

private theorem pls22_sup_Vsub2_span_e2 :
    Vsub (K := K) 4 2 ⊔
        Submodule.span K {(Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K)} =
      Vsub (K := K) 4 3 := by
  apply le_antisymm
  · refine sup_le (Vsub_mono (by norm_num)) ?_
    rw [Submodule.span_le, Set.singleton_subset_iff]
    intro j hj
    fin_cases j <;> simp_all [Pi.single_apply]
  · intro v hv
    have hv3 : v 3 = 0 := hv 3 (by norm_num)
    have hdecomp : v = (v 0) • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) +
        (v 1) • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) +
          (v 2) • (Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K) := by
      funext j
      fin_cases j <;> simp_all [Pi.single_apply]
    have h0 : (v 0) • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) ∈
        Vsub (K := K) 4 2 := by
      intro j hj
      fin_cases j
      · exact absurd hj (by norm_num)
      · exact absurd hj (by norm_num)
      · simp [Pi.smul_apply, Pi.single_apply]
      · simp [Pi.smul_apply, Pi.single_apply]
    have h1 : (v 1) • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) ∈
        Vsub (K := K) 4 2 := by
      intro j hj
      fin_cases j
      · exact absurd hj (by norm_num)
      · exact absurd hj (by norm_num)
      · simp [Pi.smul_apply, Pi.single_apply]
      · simp [Pi.smul_apply, Pi.single_apply]
    rw [hdecomp]
    exact Submodule.mem_sup.mpr
      ⟨(v 0) • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) +
        (v 1) • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K), Submodule.add_mem _ h0 h1,
        (v 2) • (Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K),
        Submodule.smul_mem _ (v 2) (Submodule.mem_span_singleton_self _), rfl⟩

private theorem pls22_kapMat_mat (P : SpecialLinearGroup (Fin 4) K)
    (hP : (P : Matrix (Fin 4) (Fin 4) K) = swap22 K) (A : SpecialLinearGroup (Fin 4) K) :
    ((SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) false P A) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) =
      swap22 K * ((SpecialLinearGroup.toGL A : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K).map (sg K f : K →+* K) * swap22 K := by
  have h1 : kapMat (sg K f : K →+* K) false P A =
      P * SpecialLinearGroup.map (sg K f : K →+* K) A * P⁻¹ := by
    simp [kapMat]
  have hPP : P * P = 1 := by
    apply Subtype.ext
    show (P : Matrix (Fin 4) (Fin 4) K) * P = 1
    rw [hP, swap22_mul_self]
  have hPinv : P⁻¹ = P := inv_eq_of_mul_eq_one_right hPP
  have hmid : ((SpecialLinearGroup.map (sg K f : K →+* K) A :
      SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K).map (sg K f : K →+* K) := by
    rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  rw [h1, hPinv]
  simp only [map_mul, GeneralLinearGroup.coe_mul, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.coe_mul, hP, hmid]

private theorem pls22_flagAct_E (g : GL (Fin 4) K) (x : FlagK K 4) (j : ℕ) :
    (flagAct g x).E j = (x.E j).map (glLin g).toLinearMap :=
  flagMap_E (glLin g) x j

theorem flagPsiX_flagAct (hK : Nat.card K = (2 ^ f) ^ 2) (g g' : GL (Fin 4) K)
    (hg : BlockDiag [0, 2, 4] (g : Matrix (Fin 4) (Fin 4) K))
    (hgg' : (g' : Matrix (Fin 4) (Fin 4) K) =
      swap22 K * (g : Matrix (Fin 4) (Fin 4) K).map (sg K f : K →+* K) * swap22 K)
    {x : FlagK K 4} (hx : x ∈ refSet K 4 [0, 2, 4]) :
    flagPsiX hK (flagAct g x) = flagAct g' (flagPsiX hK x) := by
  have hd : IsCut 4 [0, 2, 4] := isCut_22
  have hg' : BlockDiag [0, 2, 4] ((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [hgg']; exact pls22_blockDiag_conj hg
  have hy : flagAct g x ∈ refSet K 4 [0, 2, 4] :=
    flagMap_mem_refSet (glLin g) (fun i hi => BlockDiag.stabV hd hg i hi) hx
  have hz : flagPsiX hK x ∈ refSet K 4 [0, 2, 4] := flagPsiX_mem hK hx
  have hz' : flagAct g' (flagPsiX hK x) ∈ refSet K 4 [0, 2, 4] :=
    flagMap_mem_refSet (glLin g') (fun i hi => BlockDiag.stabV hd hg' i hi) hz
  have hentry : ∀ i j : Fin 4, ((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j =
      sg K f (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) (pls22_pi i)
        (pls22_pi j)) := by
    intro i j
    rw [hgg', pls22_conj_apply, Matrix.map_apply]
    rfl
  have hA : ∀ v : Fin 4 → K,
      jShiftInv K f (glLin g v) = glLin g' (jShiftInv K f v) := by
    intro v
    rw [glLin_apply, glLin_apply]
    exact pls22_jShiftInv_mulVec hg hentry v
  have hB : ∀ v : Fin 4 → K, jShift K f (glLin g v) = glLin g' (jShift K f v) := by
    intro v
    rw [glLin_apply, glLin_apply]
    exact pls22_jShift_mulVec hg hentry v
  have hstab : (Vsub (K := K) 4 2).map (glLin g').toLinearMap = Vsub (K := K) 4 2 := by
    simpa using BlockDiag.stabV hd hg' 1 (by decide)
  apply FlagK.ext4
  · rw [flagPsiX_E_one hK hy, pls22_flagAct_E g x 3,
      pls22_flagAct_E g' (flagPsiX hK x) 1, flagPsiX_E_one hK hx, Submodule.map_span]
    have hset : jShiftInv K f '' ↑((x.E 3).map (glLin g).toLinearMap) =
        (glLin g').toLinearMap '' (jShiftInv K f '' ↑(x.E 3)) := by
      ext w
      constructor
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp hu
        exact ⟨jShiftInv K f u', ⟨u', hu', rfl⟩, (hA u').symm⟩
      · rintro ⟨u, hu, rfl⟩
        rcases hu with ⟨u', hu', rfl⟩
        exact ⟨glLin g u', Submodule.mem_map.mpr ⟨u', hu', rfl⟩, hA u'⟩
    rw [hset]
  · rw [show (flagPsiX hK (flagAct g x)).E 2 = Vsub (K := K) 4 2 from by
          simpa using flagPsiX_mem hK hy 1 (by decide),
        show (flagAct g' (flagPsiX hK x)).E 2 = Vsub (K := K) 4 2 from by
          simpa using hz' 1 (by decide)]
  · rw [flagPsiX_E_three hK hy, pls22_flagAct_E g x 1,
      pls22_flagAct_E g' (flagPsiX hK x) 3, flagPsiX_E_three hK hx,
      Submodule.map_sup, Submodule.map_span, hstab]
    have hset : jShift K f '' ↑((x.E 1).map (glLin g).toLinearMap) =
        (glLin g').toLinearMap '' (jShift K f '' ↑(x.E 1)) := by
      ext w
      constructor
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp hu
        exact ⟨jShift K f u', ⟨u', hu', rfl⟩, (hB u').symm⟩
      · rintro ⟨u, hu, rfl⟩
        rcases hu with ⟨u', hu', rfl⟩
        exact ⟨glLin g u', Submodule.mem_map.mpr ⟨u', hu', rfl⟩, hB u'⟩
    rw [hset]

theorem flagPsiX_stdFlag (hK : Nat.card K = (2 ^ f) ^ 2) :
    flagPsiX hK (stdFlag K 4) = stdFlag K 4 := by
  have hd : IsCut 4 [0, 2, 4] := isCut_22
  have hstd : stdFlag K 4 ∈ refSet K 4 [0, 2, 4] := stdFlag_mem_refSet hd
  have hψ := flagPsiX_mem hK hstd
  apply FlagK.ext4
  · rw [flagPsiX_E_one hK hstd]
    exact pls22_span_jShiftInv_Vsub3 hK
  · rw [show (flagPsiX hK (stdFlag K 4)).E 2 = Vsub (K := K) 4 2 from by
          simpa using hψ 1 (by decide),
        show (stdFlag K 4).E 2 = (Vsub (K := K) 4 2 : Submodule K (Fin 4 → K)) from rfl]
  · rw [flagPsiX_E_three hK hstd]
    change Vsub (K := K) 4 2 ⊔
        Submodule.span K (jShift K f '' (Vsub (K := K) 4 1 : Set (Fin 4 → K))) =
      Vsub (K := K) 4 3
    rw [pls22_span_jShift_Vsub1, pls22_sup_Vsub2_span_e2]

theorem flagAct_kapMat_stdFlag_22x (hK : Nat.card K = (2 ^ f) ^ 2) (N : GL (Fin 4) K)
    (P : SpecialLinearGroup (Fin 4) K)
    (hP : (P : Matrix (Fin 4) (Fin 4) K) = swap22 K)
    {A : SpecialLinearGroup (Fin 4) K} (hA : A ∈ blockSL K 3 [0, 2, 4]) :
    flagAct N (flagAct (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) false P A))
        (stdFlag K 4)) =
      flagAct N (flagPsiX hK (flagAct (SpecialLinearGroup.toGL A) (stdFlag K 4))) := by
  have hd : IsCut 4 [0, 2, 4] := isCut_22
  have hstd : stdFlag K 4 ∈ refSet K 4 [0, 2, 4] := stdFlag_mem_refSet hd
  have hkey := flagPsiX_flagAct hK (SpecialLinearGroup.toGL A)
    (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) false P A))
    (blockSL_blockDiag hd hA) (pls22_kapMat_mat P hP A) hstd
  rw [hkey, flagPsiX_stdFlag hK]

theorem exists_chart_22x {I C : Type} (X : ChamberSystem I C) (hK : Nat.card K = (2 ^ f) ^ 2)
    (S : Set C) (ψ : C → C) (Θ₀ : ChamberIso X (flagSys K 3)) (N : GL (Fin 4) K)
    (hN : StabV 4 [0, 2, 4] N)
    (hS : ∀ c, c ∈ S ↔ Θ₀.Φ c ∈ refSet K 4 [0, 2, 4])
    (hψS : ∀ c ∈ S, ψ c ∈ S) (hψψ : ∀ c ∈ S, ψ (ψ c) = c)
    (P : SpecialLinearGroup (Fin 4) K) (hP : (P : Matrix (Fin 4) (Fin 4) K) = swap22 K)
    (hψ : ∀ A ∈ blockSL K 3 [0, 2, 4], ∀ c ∈ S,
      Θ₀.Φ c = flagAct (SpecialLinearGroup.toGL A) (stdFlag K 4) →
        Θ₀.Φ (ψ c) = flagAct N (flagAct
          (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) false P A)) (stdFlag K 4))) :
    ∃ Θ : ChamberIso X (flagSys K 3), (∀ c, c ∈ S ↔ Θ.Φ c ∈ refSet K 4 [0, 2, 4]) ∧
      ∀ c ∈ S, Θ.Φ (ψ c) = flagPsiX hK (Θ.Φ c) := by
  have hd : IsCut 4 [0, 2, 4] := isCut_22
  have hkey : ∀ c ∈ S, Θ₀.Φ (ψ c) = flagAct N (flagPsiX hK (Θ₀.Φ c)) := by
    intro c hc
    obtain ⟨A, hA, hAx⟩ := exists_blockSL_of_mem_refSet hd ((hS c).mp hc)
    rw [hψ A hA c hc hAx, hAx]
    exact flagAct_kapMat_stdFlag_22x hK N P hP hA
  have hinv : ∀ x ∈ refSet K 4 [0, 2, 4],
      flagAct N (flagPsiX hK (flagAct N (flagPsiX hK x))) = x := by
    intro x hx
    obtain ⟨c, rfl⟩ : ∃ c, Θ₀.Φ c = x := ⟨Θ₀.Φ.symm x, Θ₀.Φ.apply_symm_apply x⟩
    have hcS : c ∈ S := (hS c).mpr hx
    have h1 := hkey c hcS
    have h2 := hkey (ψ c) (hψS c hcS)
    rw [hψψ c hcS, h1] at h2
    exact h2.symm
  obtain ⟨e, he, heq⟩ := exists_normalForm_flagPsiX hK hN hinv
  let Θ : ChamberIso X (flagSys K 3) := Θ₀.trans (flagMapIso (glLin e))
  have hΘ : ∀ c, Θ.Φ c = flagAct e (Θ₀.Φ c) := fun c => rfl
  have himg := flagMap_image_refSet (glLin e) he
  have hiff : ∀ x : FlagK K 4,
      flagAct e x ∈ refSet K 4 [0, 2, 4] ↔ x ∈ refSet K 4 [0, 2, 4] := by
    intro x
    constructor
    · intro hx
      have hx' : flagMap (glLin e) x ∈ flagMap (glLin e) '' refSet K 4 [0, 2, 4] := by
        rw [himg]; exact hx
      obtain ⟨z, hz, hzx⟩ := hx'
      have hzx' : z = x := flagMap_injective (glLin e) hzx
      rwa [hzx'] at hz
    · intro hx
      have hx' : flagMap (glLin e) x ∈ flagMap (glLin e) '' refSet K 4 [0, 2, 4] :=
        Set.mem_image_of_mem _ hx
      rwa [himg] at hx'
  refine ⟨Θ, ?_, ?_⟩
  · intro c
    rw [hS c, hΘ c]
    exact (hiff (Θ₀.Φ c)).symm
  · intro c hc
    have hxmem : Θ₀.Φ c ∈ refSet K 4 [0, 2, 4] := (hS c).mp hc
    have hxemem : flagAct e (Θ₀.Φ c) ∈ refSet K 4 [0, 2, 4] := (hiff (Θ₀.Φ c)).mpr hxmem
    have hn := heq (flagAct e (Θ₀.Φ c)) hxemem
    rw [flagAct_inv_flagAct] at hn
    rw [hΘ (ψ c), hΘ c, hkey c hc]
    exact hn

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
