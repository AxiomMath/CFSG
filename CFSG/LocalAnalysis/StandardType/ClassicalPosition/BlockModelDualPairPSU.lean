module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDualPair
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPSLRoot
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.DualPairEquivPSU

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open CFSG.StandardType.TableCRes

private noncomputable def bmDPU_v₁ {n g k : ℕ} (P : Matrix (Fin n) (Fin (k + 1)) (PSUF g)) :
    Fin n → PSUF g :=
  Matrix.mulVec P (Pi.single (0 : Fin (k + 1)) 1)

private noncomputable def bmDPU_w₁ {n g k : ℕ} (Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)) :
    Fin n → PSUF g :=
  Matrix.mulVec Q (Pi.single (Fin.last k) 1)

private noncomputable def bmDPU_v₂ {n g k : ℕ} (P : Matrix (Fin n) (Fin (k + 1)) (PSUF g)) :
    Fin n → PSUF g :=
  Matrix.mulVec P (Pi.single (Fin.last k) 1)

private noncomputable def bmDPU_w₂ {n g k : ℕ} (Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)) :
    Fin n → PSUF g :=
  Matrix.mulVec Q (Pi.single (0 : Fin (k + 1)) 1)

private theorem bmDPU_mem_GUsub {n g : ℕ} {S : Set (GL (Fin n) (PSUF g))}
    (hSU : ∀ s ∈ S, Unitary.conjTr (PSUσ g) (s : Matrix (Fin n) (Fin n) (PSUF g)) *
      Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (PSUF g)) = Unitary.antidiag n) :
    ∀ s ∈ S, s ∈ GUsub (PSUσ g) n := by
  intro s hs
  exact mem_GUsub_iff.mpr (hSU s hs)

private theorem bmDPU_dim {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W) (hk : 1 ≤ k) : 4 ≤ n := by
  have hinj : Function.Injective (LinearMap.coprod P.mulVecLin Q.mulVecLin) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ hxy
    have hxy' : P.mulVec x + Q.mulVec y = 0 := by
      simpa only [LinearMap.coprod_apply, Matrix.mulVecLin_apply] using hxy
    have hx : x = 0 := by
      have h := congrArg (Matrix.mulVec R) hxy'
      simp only [Matrix.mulVec_add, Matrix.mulVec_zero, Matrix.mulVec_mulVec, hD.rp, hD.rq,
        Matrix.one_mulVec, Matrix.zero_mulVec, add_zero] at h
      exact h
    have hy : y = 0 := by
      have h := congrArg (Matrix.mulVec W) hxy'
      simp only [Matrix.mulVec_add, Matrix.mulVec_zero, Matrix.mulVec_mulVec, hD.wp, hD.wq,
        Matrix.zero_mulVec, Matrix.one_mulVec, zero_add] at h
      exact h
    exact Prod.ext hx hy
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_fin] at hle
  omega

private theorem bmDPU_fong (n g : ℕ) (S : Set (GL (Fin n) (PSUF g)))
    (hSU : ∀ s ∈ S, Unitary.conjTr (PSUσ g) (s : Matrix (Fin n) (Fin n) (PSUF g)) *
      Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (PSUF g)) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (PSUF g)}
    (he : IsPrimIdemIn (Algebra.adjoin (PSUF g) (Units.val '' S)) e)
    (hpair : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e ≠ e)
    (hdeg : blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e < 2)
    {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer (PSUj n g) S
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e),
      glBlockCentralizer (PSUj n g) S
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e)⁆) :
    ∃ (k : ℕ) (P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g))
      (R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)) (hD : PSUDualData g n (k + 1) P Q R W),
      PSUDualPairModel n g S e P Q R W hD ∧ 1 ≤ k ∧ (dualPairEmbSU hD).range = J' ∧ 4 ≤ n := by
  classical
  have hSU' : ∀ s ∈ S, s ∈ GUsub (PSUσ g) n := bmDPU_mem_GUsub hSU
  obtain ⟨P, Q, R, W, hD, hM, hrank, hrange, _⟩ :=
    exists_blockModel_dualPair_PSU_explicit n g S hSU' hS he hpair hdeg hJe
  generalize hre : Matrix.rank e = r at *
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have hk1 : 1 ≤ k := by omega
  exact ⟨k, P, Q, R, W, hD, hM, hk1, hrange, bmDPU_dim hD hk1⟩

private theorem bmDPU_mulVec_dotProduct {g m k : ℕ}
    (A : Matrix (Fin m) (Fin k) (PSUF g)) (x : Fin k → PSUF g) (y : Fin m → PSUF g) :
    (Matrix.mulVec A x) ⬝ᵥ y = x ⬝ᵥ (Matrix.mulVec (Matrix.transpose A) y) := by
  have h := Matrix.dotProduct_transpose_mulVec (Matrix.transpose A) y x
  rw [Matrix.transpose_transpose] at h
  rw [dotProduct_comm (Matrix.mulVec A x) y]
  exact h

private theorem bmDPU_map_single_same {g k : ℕ} (p : Fin (k + 1)) :
    PSUσ g (((Pi.single p (1 : PSUF g)) : Fin (k + 1) → PSUF g) p) =
      ((Pi.single p (1 : PSUF g)) : Fin (k + 1) → PSUF g) p := by
  have h1 : ((Pi.single p (1 : PSUF g)) : Fin (k + 1) → PSUF g) p = 1 :=
    Pi.single_eq_same (M := fun _ : Fin (k + 1) => PSUF g) p (1 : PSUF g)
  rw [h1, map_one]

private theorem bmDPU_map_single_ne {g k : ℕ} {p i : Fin (k + 1)} (h : i ≠ p) :
    PSUσ g (((Pi.single p (1 : PSUF g)) : Fin (k + 1) → PSUF g) i) =
      ((Pi.single p (1 : PSUF g)) : Fin (k + 1) → PSUF g) i := by
  have h1 : ((Pi.single p (1 : PSUF g)) : Fin (k + 1) → PSUF g) i = 0 :=
    Pi.single_eq_of_ne (M := fun _ : Fin (k + 1) => PSUF g) h (1 : PSUF g)
  rw [h1, map_zero]

private theorem bmDPU_map_single {g k : ℕ} (p : Fin (k + 1)) :
    (fun i : Fin (k + 1) =>
      PSUσ g (((Pi.single p (1 : PSUF g)) : Fin (k + 1) → PSUF g) i)) =
      ((Pi.single p (1 : PSUF g)) : Fin (k + 1) → PSUF g) := by
  funext i
  by_cases h : i = p
  · rw [h]
    exact bmDPU_map_single_same p
  · exact bmDPU_map_single_ne h

private theorem bmDPU_std_dotProduct {g k : ℕ} (p q : Fin (k + 1)) :
    (Pi.single p (1 : PSUF g)) ⬝ᵥ (Pi.single q (1 : PSUF g)) = if p = q then 1 else 0 := by
  simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq', eq_comm]

private theorem bmDPU_vecMul_adj {n g k : ℕ}
    (M : Matrix (Fin n) (Fin (k + 1)) (PSUF g)) (u : Fin (k + 1) → PSUF g)
    (w : Fin n → PSUF g) :
    Matrix.vecMul (fun i => PSUσ g (Matrix.mulVec M u i)) (Unitary.antidiag n) ⬝ᵥ w =
      (fun i => PSUσ g (u i)) ⬝ᵥ
        (Matrix.mulVec (tcConjTr (PSUσ g) M * Unitary.antidiag n) w) := by
  have h1 : (fun i => PSUσ g (Matrix.mulVec M u i)) =
      Matrix.mulVec (M.map (PSUσ g)) (fun i => PSUσ g (u i)) := by
    funext i
    exact RingHom.map_mulVec (PSUσ g).toRingHom M u i
  rw [h1, ← Matrix.dotProduct_mulVec]
  rw [bmDPU_mulVec_dotProduct (M.map (PSUσ g)) (fun i => PSUσ g (u i))
    (Matrix.mulVec (Unitary.antidiag n) w)]
  rw [Matrix.mulVec_mulVec]
  rfl

private theorem bmDPU_pair_eq {n g k : ℕ}
    {M : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {A : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    {N : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    (hM : tcConjTr (PSUσ g) M * Unitary.antidiag n = A) (hAN : A * N = 1)
    (p q : Fin (k + 1)) :
    Matrix.vecMul (fun i => PSUσ g (Matrix.mulVec M (Pi.single p (1 : PSUF g)) i))
      (Unitary.antidiag n) ⬝ᵥ (Matrix.mulVec N (Pi.single q (1 : PSUF g))) =
      if p = q then 1 else 0 := by
  rw [bmDPU_vecMul_adj M (Pi.single p (1 : PSUF g))
    (Matrix.mulVec N (Pi.single q (1 : PSUF g))), hM, Matrix.mulVec_mulVec, hAN,
    Matrix.one_mulVec]
  rw [bmDPU_map_single (g := g) p]
  exact bmDPU_std_dotProduct p q

private theorem bmDPU_pair_zero {n g k : ℕ}
    {M : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {A : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    {N : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    (hM : tcConjTr (PSUσ g) M * Unitary.antidiag n = A) (hAN : A * N = 0)
    (p q : Fin (k + 1)) :
    Matrix.vecMul (fun i => PSUσ g (Matrix.mulVec M (Pi.single p (1 : PSUF g)) i))
      (Unitary.antidiag n) ⬝ᵥ (Matrix.mulVec N (Pi.single q (1 : PSUF g))) = 0 := by
  rw [bmDPU_vecMul_adj M (Pi.single p (1 : PSUF g))
    (Matrix.mulVec N (Pi.single q (1 : PSUF g))), hM, Matrix.mulVec_mulVec, hAN,
    Matrix.zero_mulVec]
  simp

private theorem bmDPU_pairings {n g k : ℕ} (hk : 1 ≤ k)
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W) :
    Matrix.vecMul (fun i => PSUσ g (bmDPU_v₁ P i)) (Unitary.antidiag n) ⬝ᵥ bmDPU_w₂ Q = 1 ∧
    Matrix.vecMul (fun i => PSUσ g (bmDPU_w₁ Q i)) (Unitary.antidiag n) ⬝ᵥ bmDPU_v₂ P = 1 ∧
    (Matrix.vecMul (fun i => PSUσ g (bmDPU_v₁ P i)) (Unitary.antidiag n) ⬝ᵥ bmDPU_v₁ P = 0 ∧
      Matrix.vecMul (fun i => PSUσ g (bmDPU_w₁ Q i)) (Unitary.antidiag n) ⬝ᵥ bmDPU_w₁ Q = 0 ∧
      Matrix.vecMul (fun i => PSUσ g (bmDPU_v₂ P i)) (Unitary.antidiag n) ⬝ᵥ bmDPU_v₂ P = 0 ∧
      Matrix.vecMul (fun i => PSUσ g (bmDPU_w₂ Q i)) (Unitary.antidiag n) ⬝ᵥ bmDPU_w₂ Q = 0 ∧
      Matrix.vecMul (fun i => PSUσ g (bmDPU_v₁ P i)) (Unitary.antidiag n) ⬝ᵥ bmDPU_w₁ Q = 0 ∧
      Matrix.vecMul (fun i => PSUσ g (bmDPU_v₁ P i)) (Unitary.antidiag n) ⬝ᵥ bmDPU_v₂ P = 0 ∧
      Matrix.vecMul (fun i => PSUσ g (bmDPU_w₁ Q i)) (Unitary.antidiag n) ⬝ᵥ bmDPU_w₂ Q = 0 ∧
      Matrix.vecMul (fun i => PSUσ g (bmDPU_v₂ P i)) (Unitary.antidiag n) ⬝ᵥ bmDPU_w₂ Q = 0) := by
  have hlast : (Fin.last k : Fin (k + 1)) ≠ 0 := Fin.last_ne_zero (by omega)
  have h0 : (0 : Fin (k + 1)) ≠ Fin.last k := hlast.symm
  have h1 := bmDPU_pair_eq (M := P) (A := W) (N := Q) hD.pj hD.wq (0 : Fin (k+1)) 0
  have h2 := bmDPU_pair_eq (M := Q) (A := R) (N := P) hD.qj hD.rp (Fin.last k) (Fin.last k)
  have h3 := bmDPU_pair_zero (M := P) (A := W) (N := P) hD.pj hD.wp (0 : Fin (k+1)) 0
  have h4 := bmDPU_pair_zero (M := Q) (A := R) (N := Q) hD.qj hD.rq (Fin.last k) (Fin.last k)
  have h5 := bmDPU_pair_zero (M := P) (A := W) (N := P) hD.pj hD.wp (Fin.last k) (Fin.last k)
  have h6 := bmDPU_pair_zero (M := Q) (A := R) (N := Q) hD.qj hD.rq (0 : Fin (k+1)) 0
  have h7 := bmDPU_pair_eq (M := P) (A := W) (N := Q) hD.pj hD.wq (0 : Fin (k+1)) (Fin.last k)
  have h8 := bmDPU_pair_zero (M := P) (A := W) (N := P) hD.pj hD.wp (0 : Fin (k+1)) (Fin.last k)
  have h9 := bmDPU_pair_zero (M := Q) (A := R) (N := Q) hD.qj hD.rq (Fin.last k) (0 : Fin (k+1))
  have h10 := bmDPU_pair_eq (M := P) (A := W) (N := Q) hD.pj hD.wq (Fin.last k) (0 : Fin (k+1))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [bmDPU_v₁, bmDPU_w₂] using h1
  · simpa [bmDPU_w₁, bmDPU_v₂] using h2
  · simpa [bmDPU_v₁] using h3
  · simpa [bmDPU_w₁] using h4
  · simpa [bmDPU_v₂] using h5
  · simpa [bmDPU_w₂] using h6
  · simpa [bmDPU_v₁, bmDPU_w₁, h0] using h7
  · simpa [bmDPU_v₁, bmDPU_v₂] using h8
  · simpa [bmDPU_w₁, bmDPU_w₂] using h9
  · simpa [bmDPU_v₂, bmDPU_w₂, hlast] using h10

private theorem bmDPU_map_SU_eq {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin (k + 1)) (PSUF g))) :
    (H.map (dualPairEmbSU hD)).map (Unitary.SU (PSUσ g) n).subtype =
      (H.map Matrix.SpecialLinearGroup.toGL).map (dualPairEmbGL hD) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy
    exact Subgroup.mem_map.mpr ⟨Matrix.SpecialLinearGroup.toGL z,
      Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, (coe_dualPairEmbSU hD z).symm⟩
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy
    exact Subgroup.mem_map.mpr ⟨dualPairEmbSU hD z,
      Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, coe_dualPairEmbSU hD z⟩

private noncomputable def bmDPU_transv {g k : ℕ} (i j : Fin (k + 1)) (c : PSUF g) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g) :=
  1 + c • Matrix.vecMulVec (Pi.single i (1 : PSUF g)) (Pi.single j (1 : PSUF g))

private theorem bmDPU_transv_mul_self {g k : ℕ} {i j : Fin (k + 1)} (hij : i ≠ j)
    (c : PSUF g) : bmDPU_transv i j c * bmDPU_transv i j c = 1 := by
  let N : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g) :=
    Matrix.vecMulVec (Pi.single i (1 : PSUF g)) (Pi.single j (1 : PSUF g))
  have hdot : dotProduct (Pi.single j (1 : PSUF g)) (Pi.single i (1 : PSUF g)) = 0 := by
    rw [bmDPU_std_dotProduct]
    simp [Ne.symm hij]
  have hNN : N * N = 0 := by
    change Matrix.vecMulVec (Pi.single i (1 : PSUF g)) (Pi.single j (1 : PSUF g)) *
      Matrix.vecMulVec (Pi.single i (1 : PSUF g)) (Pi.single j (1 : PSUF g)) = 0
    rw [Matrix.vecMulVec_mul_vecMulVec, hdot]
    simp
  have hcc : c + c = 0 := by
    have h2 : (2 : PSUF g) = 0 := CharP.cast_eq_zero (PSUF g) 2
    calc c + c = (2 : PSUF g) * c := by ring
      _ = 0 := by simp [h2]
  have hccN : c • N + c • N = 0 := by rw [← add_smul, hcc, zero_smul]
  have hNNc : (c • N) * (c • N) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul]
    simp [hNN]
  change (1 + c • N) * (1 + c • N) = 1
  have h1 : (1 + c • N) * (1 + c • N) =
      1 + (c • N + c • N) + (c • N) * (c • N) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [h1, hccN, hNNc]
  simp

private noncomputable def bmDPU_transvGL {g k : ℕ} {i j : Fin (k + 1)} (hij : i ≠ j)
    (c : PSUF g) : GL (Fin (k + 1)) (PSUF g) :=
  ⟨bmDPU_transv i j c, bmDPU_transv i j c, bmDPU_transv_mul_self hij c,
    bmDPU_transv_mul_self hij c⟩

private theorem bmDPU_transv_tcConjTr {g k : ℕ} (i j : Fin (k + 1)) (c : PSUF g) :
    tcConjTr (PSUσ g) (bmDPU_transv i j c) = bmDPU_transv j i (PSUσ g c) := by
  let N : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g) :=
    Matrix.vecMulVec (Pi.single i (1 : PSUF g)) (Pi.single j (1 : PSUF g))
  have hNmap : N.map (PSUσ g) = N := by
    ext a b
    simp only [N, Matrix.map_apply, Matrix.vecMulVec_apply]
    rw [map_mul, congrFun (bmDPU_map_single i) a, congrFun (bmDPU_map_single j) b]
  have hN : tcConjTr (PSUσ g) N =
      Matrix.vecMulVec (Pi.single j (1 : PSUF g)) (Pi.single i (1 : PSUF g)) := by
    unfold tcConjTr
    rw [hNmap, Matrix.transpose_vecMulVec]
  have hsmul : tcConjTr (PSUσ g) (c • N) =
      PSUσ g c • tcConjTr (PSUσ g) N := by
    unfold tcConjTr
    have hmap : (c • N).map (PSUσ g) = PSUσ g c • N.map (PSUσ g) := by
      ext a b
      simp only [Matrix.map_apply, Matrix.smul_apply, map_mul, smul_eq_mul]
    rw [hmap, Matrix.transpose_smul]
  change tcConjTr (PSUσ g) (1 + c • N) = 1 + PSUσ g c •
    Matrix.vecMulVec (Pi.single j (1 : PSUF g)) (Pi.single i (1 : PSUF g))
  rw [tcConjTr_add, tcConjTr_one, hsmul, hN]

private theorem bmDPU_vecMul_single_R {n g k : ℕ}
    {Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hqj : tcConjTr (PSUσ g) Q * Unitary.antidiag n = R) (j : Fin (k + 1)) :
    Matrix.vecMul (Pi.single j (1 : PSUF g)) R =
      Matrix.vecMul (fun l : Fin n => PSUσ g (Matrix.mulVec Q (Pi.single j (1 : PSUF g)) l))
        (Unitary.antidiag n) := by
  calc Matrix.vecMul (Pi.single j (1 : PSUF g)) R
      = Matrix.vecMul (Pi.single j (1 : PSUF g))
          (tcConjTr (PSUσ g) Q * Unitary.antidiag n) := by
          rw [← hqj]
          rfl
    _ = Matrix.vecMul
          (Matrix.vecMul (Pi.single j (1 : PSUF g)) (tcConjTr (PSUσ g) Q))
          (Unitary.antidiag n) := (Matrix.vecMul_vecMul _ _ _).symm
    _ = Matrix.vecMul
          (Matrix.mulVec (Q.map (PSUσ g)) (Pi.single j (1 : PSUF g)))
          (Unitary.antidiag n) := by
          rw [show tcConjTr (PSUσ g) Q = Matrix.transpose (Q.map (PSUσ g)) from rfl,
            Matrix.vecMul_transpose]
    _ = Matrix.vecMul
          (fun l : Fin n => PSUσ g (Matrix.mulVec Q (Pi.single j (1 : PSUF g)) l))
          (Unitary.antidiag n) := by
          have hmap : (fun l : Fin n =>
                PSUσ g (Matrix.mulVec Q (Pi.single j (1 : PSUF g)) l)) =
              Matrix.mulVec (Q.map (PSUσ g)) (Pi.single j (1 : PSUF g)) := by
            funext l
            refine (RingHom.map_mulVec (PSUσ g).toRingHom Q
              (Pi.single j (1 : PSUF g)) l).trans ?_
            congr 1
            funext l'
            exact congrFun (bmDPU_map_single j) l'
          rw [hmap]

private theorem bmDPU_vecMul_single_W {n g k : ℕ}
    {P : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hpj : tcConjTr (PSUσ g) P * Unitary.antidiag n = W) (i : Fin (k + 1)) :
    Matrix.vecMul (Pi.single i (1 : PSUF g)) W =
      Matrix.vecMul (fun l : Fin n => PSUσ g (Matrix.mulVec P (Pi.single i (1 : PSUF g)) l))
        (Unitary.antidiag n) := by
  calc Matrix.vecMul (Pi.single i (1 : PSUF g)) W
      = Matrix.vecMul (Pi.single i (1 : PSUF g))
          (tcConjTr (PSUσ g) P * Unitary.antidiag n) := by
          rw [← hpj]
          rfl
    _ = Matrix.vecMul
          (Matrix.vecMul (Pi.single i (1 : PSUF g)) (tcConjTr (PSUσ g) P))
          (Unitary.antidiag n) := (Matrix.vecMul_vecMul _ _ _).symm
    _ = Matrix.vecMul
          (Matrix.mulVec (P.map (PSUσ g)) (Pi.single i (1 : PSUF g)))
          (Unitary.antidiag n) := by
          rw [show tcConjTr (PSUσ g) P = Matrix.transpose (P.map (PSUσ g)) from rfl,
            Matrix.vecMul_transpose]
    _ = Matrix.vecMul
          (fun l : Fin n => PSUσ g (Matrix.mulVec P (Pi.single i (1 : PSUF g)) l))
          (Unitary.antidiag n) := by
          have hmap : (fun l : Fin n =>
                PSUσ g (Matrix.mulVec P (Pi.single i (1 : PSUF g)) l)) =
              Matrix.mulVec (P.map (PSUσ g)) (Pi.single i (1 : PSUF g)) := by
            funext l
            refine (RingHom.map_mulVec (PSUσ g).toRingHom P
              (Pi.single i (1 : PSUF g)) l).trans ?_
            congr 1
            funext l'
            exact congrFun (bmDPU_map_single i) l'
          rw [hmap]

private theorem bmDPU_transv_mul_R {n g k : ℕ}
    (P : Matrix (Fin n) (Fin (k + 1)) (PSUF g))
    (R : Matrix (Fin (k + 1)) (Fin n) (PSUF g)) (i j : Fin (k + 1)) :
    P * Matrix.vecMulVec (Pi.single i (1 : PSUF g)) (Pi.single j (1 : PSUF g)) * R =
      Matrix.vecMulVec (Matrix.mulVec P (Pi.single i (1 : PSUF g)))
        (Matrix.vecMul (Pi.single j (1 : PSUF g)) R) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

private theorem bmDPU_transv_mul_W {n g k : ℕ}
    (Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g))
    (W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)) (i j : Fin (k + 1)) :
    Q * Matrix.vecMulVec (Pi.single j (1 : PSUF g)) (Pi.single i (1 : PSUF g)) * W =
      Matrix.vecMulVec (Matrix.mulVec Q (Pi.single j (1 : PSUF g)))
        (Matrix.vecMul (Pi.single i (1 : PSUF g)) W) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

private theorem bmDPU_dpEmb_transv_expand {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    {i j : Fin (k + 1)} (c : PSUF g) :
    dpEmb P Q R W (bmDPU_transv i j c) (bmDPU_transv j i (PSUσ g c)) =
      1 + c • Matrix.vecMulVec (Matrix.mulVec P (Pi.single i (1 : PSUF g)))
            (Matrix.vecMul (Pi.single j (1 : PSUF g)) R) -
          PSUσ g c • Matrix.vecMulVec (Matrix.mulVec Q (Pi.single j (1 : PSUF g)))
            (Matrix.vecMul (Pi.single i (1 : PSUF g)) W) := by
  have hR : P * bmDPU_transv i j c * R =
      P * R + c • Matrix.vecMulVec (Matrix.mulVec P (Pi.single i (1 : PSUF g)))
        (Matrix.vecMul (Pi.single j (1 : PSUF g)) R) := by
    unfold bmDPU_transv
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      bmDPU_transv_mul_R]
  have hW : Q * bmDPU_transv j i (PSUσ g c) * W =
      Q * W + PSUσ g c • Matrix.vecMulVec (Matrix.mulVec Q (Pi.single j (1 : PSUF g)))
        (Matrix.vecMul (Pi.single i (1 : PSUF g)) W) := by
    unfold bmDPU_transv
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      bmDPU_transv_mul_W]
  have hneg : -(PSUσ g c • Matrix.vecMulVec (Matrix.mulVec Q (Pi.single j (1 : PSUF g)))
        (Matrix.vecMul (Pi.single i (1 : PSUF g)) W)) =
      PSUσ g c • Matrix.vecMulVec (Matrix.mulVec Q (Pi.single j (1 : PSUF g)))
        (Matrix.vecMul (Pi.single i (1 : PSUF g)) W) := by
    rw [← neg_smul, CharTwo.neg_eq]
  unfold dpEmb
  rw [hR, hW]
  simp only [sub_eq_add_neg]
  rw [hneg]
  abel

private theorem bmDPU_transv_dpEmb {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    {i j : Fin (k + 1)} (c : PSUF g) :
    dpEmb P Q R W (bmDPU_transv i j c) (bmDPU_transv j i (PSUσ g c)) =
      1 + c • Matrix.vecMulVec (Matrix.mulVec P (Pi.single i (1 : PSUF g)))
            (Matrix.vecMul (fun l : Fin n => PSUσ g (Matrix.mulVec Q (Pi.single j (1 : PSUF g)) l))
              (Unitary.antidiag n)) -
          PSUσ g c • Matrix.vecMulVec (Matrix.mulVec Q (Pi.single j (1 : PSUF g)))
            (Matrix.vecMul (fun l : Fin n => PSUσ g (Matrix.mulVec P (Pi.single i (1 : PSUF g)) l))
              (Unitary.antidiag n)) := by
  rw [bmDPU_dpEmb_transv_expand c, bmDPU_vecMul_single_R hD.qj j,
    bmDPU_vecMul_single_W hD.pj i]

private theorem bmDPU_transv_image {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    {i j : Fin (k + 1)} (hij : i ≠ j) (c : PSUF g)
    (u : GL (Fin (k + 1)) (PSUF g)) (hu : (u : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
      bmDPU_transv i j c) :
    ((dualPairEmbGL hD u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) =
      1 + c • Matrix.vecMulVec (Matrix.mulVec P (Pi.single i (1 : PSUF g)))
            (Matrix.vecMul (fun l : Fin n => PSUσ g (Matrix.mulVec Q (Pi.single j (1 : PSUF g)) l))
              (Unitary.antidiag n)) -
          PSUσ g c • Matrix.vecMulVec (Matrix.mulVec Q (Pi.single j (1 : PSUF g)))
            (Matrix.vecMul (fun l : Fin n => PSUσ g (Matrix.mulVec P (Pi.single i (1 : PSUF g)) l))
              (Unitary.antidiag n)) := by
  have huu : u * u = 1 := Units.ext (by
    rw [Units.val_mul, hu]
    change bmDPU_transv i j c * bmDPU_transv i j c =
      (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g))
    exact bmDPU_transv_mul_self hij c)
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hinvmat : ((u⁻¹ : GL (Fin (k + 1)) (PSUF g)) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) = bmDPU_transv i j c := by
    rw [hinv, hu]
  rw [coe_dualPairEmbGL hD u, hu, hinvmat, bmDPU_transv_tcConjTr i j c,
    bmDPU_transv_dpEmb hD]

private theorem bmDPU_matTransv_map {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (i j : Fin (k + 1)) (hij : i ≠ j) :
    (matTransvGroup (Pi.single i (1 : PSUF g)) (Pi.single j (1 : PSUF g))).map
        (dualPairEmbGL hD) =
      unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n)
        (Matrix.mulVec P (Pi.single i (1 : PSUF g)))
        (Matrix.mulVec Q (Pi.single j (1 : PSUF g))) := by
  rw [matTransvGroup, MonoidHom.map_closure]
  congr 1
  ext h
  constructor
  · intro hh
    simp only [Set.mem_image] at hh
    obtain ⟨u, hu, rfl⟩ := hh
    obtain ⟨c, hc⟩ := hu
    exact ⟨c, bmDPU_transv_image hD hij c u hc⟩
  · rintro ⟨c, hc⟩
    simp only [Set.mem_image]
    refine ⟨bmDPU_transvGL hij c, ⟨c, rfl⟩, ?_⟩
    exact Units.ext (by
      rw [bmDPU_transv_image hD hij c (bmDPU_transvGL hij c) rfl, hc]
      rfl)

private theorem bmDPU_root_config {n g k : ℕ} (hk : 1 ≤ k)
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W) :
    ∃ (β : Fin k → ℤ) (u : Matrix.SpecialLinearGroup (Fin (k + 1)) (PSUF g)),
      β ∈ (SpecialLinear.rootDatum k (PSUF g)).roots ∧
      GGLongRoot (SpecialLinear.rootDatum k (PSUF g)) β ∧
      ((((SpecialLinear.rootDatum k (PSUF g)).rootGroup β).map
          ((dualPairEmbSU hD).comp (MulAut.conj u).toMonoidHom)).map
        (Unitary.SU (PSUσ g) n).subtype) =
        unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) (bmDPU_v₁ P) (bmDPU_w₁ Q) ∧
      ((((SpecialLinear.rootDatum k (PSUF g)).rootGroup (-β)).map
          ((dualPairEmbSU hD).comp (MulAut.conj u).toMonoidHom)).map
        (Unitary.SU (PSUσ g) n).subtype) =
        unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) (bmDPU_v₂ P) (bmDPU_w₂ Q) := by
  have hlast : (Fin.last k : Fin (k + 1)) ≠ 0 := Fin.last_ne_zero (by omega)
  have h0 : (0 : Fin (k + 1)) ≠ Fin.last k := hlast.symm
  obtain ⟨β, hβ, hlong, u, hroot1, hroot2⟩ :=
    exists_conj_rootGroup_eq_matTransvGroup_PSL k (PSUF g) hk
      (Pi.single (0 : Fin (k + 1)) (1 : PSUF g))
      (Pi.single (Fin.last k) (1 : PSUF g))
      (Pi.single (Fin.last k) (1 : PSUF g))
      (Pi.single (0 : Fin (k + 1)) (1 : PSUF g))
      (by rw [bmDPU_std_dotProduct]; simp [hlast])
      (by rw [bmDPU_std_dotProduct]; simp [h0])
      (by rw [bmDPU_std_dotProduct]; simp)
      (by rw [bmDPU_std_dotProduct]; simp)
  let β' : Fin k → ℤ := β
  have hβ' : β' ∈ (SpecialLinear.rootDatum k (PSUF g)).roots := hβ
  have hlong' : GGLongRoot (SpecialLinear.rootDatum k (PSUF g)) β' := hlong
  have hroot1' : (((SpecialLinear.rootDatum k (PSUF g)).rootGroup β').map
      (MulAut.conj u).toMonoidHom).map Matrix.SpecialLinearGroup.toGL =
      matTransvGroup (Pi.single 0 1) (Pi.single (Fin.last k) 1) := hroot1
  have hroot2' : (((SpecialLinear.rootDatum k (PSUF g)).rootGroup (-β')).map
      (MulAut.conj u).toMonoidHom).map Matrix.SpecialLinearGroup.toGL =
      matTransvGroup (Pi.single (Fin.last k) 1) (Pi.single 0 1) := hroot2
  refine ⟨β', u, hβ', hlong', ?_, ?_⟩
  · rw [← Subgroup.map_map]
    rw [bmDPU_map_SU_eq hD (((SpecialLinear.rootDatum k (PSUF g)).rootGroup β').map
        (MulAut.conj u).toMonoidHom), hroot1']
    exact bmDPU_matTransv_map hD (0 : Fin (k + 1)) (Fin.last k) h0
  · rw [← Subgroup.map_map]
    rw [bmDPU_map_SU_eq hD (((SpecialLinear.rootDatum k (PSUF g)).rootGroup (-β')).map
        (MulAut.conj u).toMonoidHom), hroot2']
    exact bmDPU_matTransv_map hD (Fin.last k) (0 : Fin (k + 1)) hlast

private theorem bmDPU_center {n g k : ℕ}
    {S : Set (GL (Fin n) (PSUF g))} {e : Matrix (Fin n) (Fin n) (PSUF g)}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (hM : PSUDualPairModel n g S e P Q R W hD)
    (u : Matrix.SpecialLinearGroup (Fin (k + 1)) (PSUF g)) :
    ∀ y : Matrix.SpecialLinearGroup (Fin (k + 1)) (PSUF g),
      (dualPairEmbSU hD) (u * y * u⁻¹) ∈ Subgroup.center ↥(Unitary.SU (PSUσ g) n) →
      y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (k + 1)) (PSUF g)) := by
  intro y hy
  rw [Subgroup.mem_center_iff]
  intro z
  have hA : u * y * u⁻¹ ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (k + 1)) (PSUF g)) :=
    hM.center (u * y * u⁻¹) hy
  have h1 := (Subgroup.mem_center_iff.mp hA) (u * z * u⁻¹)
  calc z * y = u⁻¹ * ((u * z * u⁻¹) * (u * y * u⁻¹)) * u := by group
    _ = u⁻¹ * ((u * y * u⁻¹) * (u * z * u⁻¹)) * u := by rw [h1]
    _ = y * z := by group

private theorem bmDPU_range_conj {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (u : Matrix.SpecialLinearGroup (Fin (k + 1)) (PSUF g)) :
    ((dualPairEmbSU hD).comp (MulAut.conj u).toMonoidHom).range = (dualPairEmbSU hD).range := by
  rw [MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (MulAut.conj u).surjective, Subgroup.map_top]

private lemma bmDPU_vecMulVec_eq_of_indep {F : Type} [Field F] {n : ℕ} {x y a b : Fin n → F}
    (hlin : LinearIndependent F ![x, y])
    (h : Matrix.vecMulVec x a = Matrix.vecMulVec y b) : a = 0 ∧ b = 0 := by
  have key : ∀ (p q : F), p • x + q • y = 0 → p = 0 ∧ q = 0 := by
    intro p q hpq
    have hg : (∑ i : Fin 2, (![p, q] : Fin 2 → F) i • ![x, y] i) = 0 := by
      simpa [Fin.sum_univ_two] using hpq
    have h0 := (Fintype.linearIndependent_iff.mp hlin) ![p, q] hg
    exact ⟨by simpa using h0 0, by simpa using h0 1⟩
  have hcol : ∀ j, a j • x = b j • y := by
    intro j
    funext i
    have hi := congrFun (congrFun h i) j
    simp only [Matrix.vecMulVec_apply] at hi
    simp only [Pi.smul_apply]
    calc a j * x i = x i * a j := mul_comm _ _
      _ = y i * b j := hi
      _ = b j * y i := mul_comm _ _
  have hzero : ∀ j, a j = 0 ∧ b j = 0 := by
    intro j
    have h1 : a j • x + (-(b j)) • y = 0 := by
      rw [neg_smul, ← sub_eq_add_neg, hcol j, sub_self]
    exact ⟨(key _ _ h1).1, neg_eq_zero.mp (key _ _ h1).2⟩
  exact ⟨funext fun j => (hzero j).1, funext fun j => (hzero j).2⟩

private lemma bmDPU_anti_symm {F : Type} [Field F] (r : ℕ) :
    Matrix.transpose (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) = Unitary.antidiag r := by
  ext i j
  simp only [Matrix.transpose_apply, Unitary.antidiag, Matrix.of_apply]
  by_cases h : i = Fin.rev j
  · have h' : j = Fin.rev i := by rw [h, Fin.rev_rev]
    rw [if_pos h, if_pos h']
  · have h' : j ≠ Fin.rev i := fun hh => h (by rw [hh, Fin.rev_rev])
    rw [if_neg h, if_neg h']

private lemma bmDPU_anti_vecMul {F : Type} [Field F] {r : ℕ} (v : Fin r → F) :
    Matrix.vecMul v (Unitary.antidiag r) =
      Matrix.mulVec (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) v := by
  ext j
  simp only [Matrix.vecMul_apply, Matrix.mulVec_apply, dotProduct, Matrix.col_apply,
    Matrix.row_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsymm : (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) i j =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) j i := by
    have h := congrFun (congrFun (bmDPU_anti_symm (F := F) r) j) i
    simpa [Matrix.transpose_apply] using h
  rw [hsymm, mul_comm]

private lemma bmDPU_map_dotProduct {F : Type} [Field F] {ι : Type} [Fintype ι] (σ : F →+* F)
    (x y : ι → F) :
    σ (x ⬝ᵥ y) = (fun i => σ (x i)) ⬝ᵥ (fun i => σ (y i)) := by
  simp only [dotProduct]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_mul])

private lemma bmDPU_vecMul_Utranspose_apply {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    (U : Matrix (Fin n) (Fin r) F) (v : Fin r → F) (i : Fin n) :
    Matrix.vecMul (fun i => σ (v i)) (Matrix.transpose (U.map σ.toRingHom)) i =
      σ (Matrix.mulVec U v i) := by
  simp only [Matrix.vecMul, Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply]
  rw [show σ ((fun j => U i j) ⬝ᵥ v) = (fun j => σ (U i j)) ⬝ᵥ (fun j => σ (v j)) from
    bmDPU_map_dotProduct σ.toRingHom _ _]
  rw [dotProduct_comm]
  rfl

private lemma bmDPU_vecMul_Utranspose {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    (U : Matrix (Fin n) (Fin r) F) (v : Fin r → F) :
    Matrix.vecMul (fun i => σ (v i)) (Matrix.transpose (U.map σ.toRingHom)) =
      fun i => σ (Matrix.mulVec U v i) := by
  funext i
  exact bmDPU_vecMul_Utranspose_apply σ U v i

private lemma bmDPU_one_sub_vec_of_vecMul_one_sub {g n : ℕ} (σ : PSUF g ≃+* PSUF g)
    {e : Matrix (Fin n) (Fin n) (PSUF g)}
    (hadj : Matrix.transpose (e.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n)
      (PSUF g)) = (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) * e)
    {v : Fin n → PSUF g}
    (h : Matrix.vecMul (Matrix.vecMul (fun i => σ (v i))
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g))) (1 - e) = 0) :
    Matrix.mulVec (1 - e) v = 0 := by
  have hGdet : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have hA1e : Matrix.vecMul (fun i => σ ((Matrix.mulVec (1 - e) v) i))
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) = 0 := by
    have h' : Matrix.vecMul (fun i => σ (v i))
        ((Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - e)) = 0 := by
      rw [← Matrix.vecMul_vecMul]
      exact h
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.vecMul_sub, ← hadj, ← Matrix.vecMul_vecMul,
      bmDPU_vecMul_Utranspose] at h'
    rw [bmDPU_anti_vecMul, bmDPU_anti_vecMul, ← Matrix.mulVec_sub] at h'
    have hf : (fun i => σ (v i)) - (fun i => σ (Matrix.mulVec e v i)) =
        fun i => σ (Matrix.mulVec (1 - e) v i) := by
      funext i
      rw [Pi.sub_apply, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, map_sub]
    rw [hf] at h'
    rw [← bmDPU_anti_vecMul] at h'
    exact h'
  have hmul : Matrix.mulVec (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g))
      (fun i => σ ((Matrix.mulVec (1 - e) v) i)) = 0 := by
    rw [← bmDPU_anti_vecMul]
    exact hA1e
  have hσw : (fun i => σ ((Matrix.mulVec (1 - e) v) i)) = 0 :=
    (Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det (Unitary.antidiag n)).mpr hGdet))
      (by rw [hmul, Matrix.mulVec_zero])
  funext i
  exact σ.injective ((congrFun hσw i).trans (map_zero σ).symm)

private lemma bmDPU_form_swap {g n : ℕ} (x y : Fin n → PSUF g) :
    Matrix.vecMul (fun i => PSUσ g (y i)) (Unitary.antidiag n) ⬝ᵥ x =
      PSUσ g (Matrix.vecMul (fun i => PSUσ g (x i)) (Unitary.antidiag n) ⬝ᵥ y) := by
  have hmap : (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)).map
      (PSUσ g).toRingHom = Unitary.antidiag n := by
    have h := congrArg Matrix.transpose (PSUantidiag_transpose_map n g)
    simpa [Matrix.transpose_transpose, bmDPU_anti_symm n] using h
  have hvec : Matrix.vecMul (fun i => PSUσ g (x i)) (Unitary.antidiag n) =
      fun j => PSUσ g (Matrix.vecMul (fun i => x i) (Unitary.antidiag n) j) := by
    funext j
    simp only [Matrix.vecMul_apply, dotProduct]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    congr 1
    exact (congrFun (congrFun hmap i) j).symm
  rw [bmDPU_anti_vecMul, dotProduct_comm, Matrix.dotProduct_mulVec]
  conv_rhs => rw [hvec]
  simp only [dotProduct]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, PSUσ_involutive]

private lemma bmDPU_eps_adj {n g k : ℕ}
    {S : Set (GL (Fin n) (PSUF g))} {e : Matrix (Fin n) (Fin n) (PSUF g)}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    {hD : PSUDualData g n (k + 1) P Q R W} (hM : PSUDualPairModel n g S e P Q R W hD) :
    Matrix.transpose (((e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e).map
        (PSUσ g).toRingHom)) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) *
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e) := by
  have hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)).det :=
    PSUantidiag_isUnit_det n g
  have hGh : Matrix.transpose ((Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)).map
      (PSUσ g).toRingHom) = Unitary.antidiag n := PSUantidiag_transpose_map n g
  have hε : formAdj (PSUσ g).toRingHom (Unitary.antidiag n)
      (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e) =
      e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e := by
    rw [Geo.formAdj_add,
      Geo.formAdj_formAdj (PSUσ g).toRingHom (PSUσ_involutive g) hG hGh e, hM.adj_eq, add_comm]
  have hε' : (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g))⁻¹ *
      Matrix.transpose (((e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e).map
        (PSUσ g).toRingHom)) * (Unitary.antidiag n) =
      e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e := by
    simpa only [formAdj] using hε
  have h1 : (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) *
      ((Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g))⁻¹ *
        Matrix.transpose (((e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e).map
          (PSUσ g).toRingHom)) * (Unitary.antidiag n)) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) *
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e) := by rw [hε']
  rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG,
    Matrix.one_mul] at h1

private lemma bmDPU_pair_mem_block {n g k : ℕ}
    {S : Set (GL (Fin n) (PSUF g))} {e : Matrix (Fin n) (Fin n) (PSUF g)}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (hM : PSUDualPairModel n g S e P Q R W hD)
    {v₀ w₀ : Fin n → PSUF g} (hv0 : Matrix.vecMul (fun i => PSUσ g (v₀ i))
      (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hw0 : Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hvw : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hli : LinearIndependent (PSUF g) ![v₀, w₀])
    (hle : unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      (dualPairEmbSU hD).range.map (Unitary.SU (PSUσ g) n).subtype) :
    Matrix.mulVec (1 - (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e)) v₀ = 0 ∧
      Matrix.mulVec (1 - (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e)) w₀ = 0 := by
  classical
  let J : Matrix (Fin n) (Fin n) (PSUF g) := Unitary.antidiag n
  let ε : Matrix (Fin n) (Fin n) (PSUF g) := e + formAdj (PSUσ g).toRingHom J e
  let A : Fin n → PSUF g := Matrix.vecMul (fun i => PSUσ g (w₀ i)) J
  let B : Fin n → PSUF g := Matrix.vecMul (fun i => PSUσ g (v₀ i)) J
  have hAv : A ⬝ᵥ v₀ = 0 := by
    show Matrix.vecMul (fun i => PSUσ g (w₀ i)) J ⬝ᵥ v₀ = 0
    exact (bmDPU_form_swap v₀ w₀).trans (by rw [hvw, map_zero])
  have hAw : A ⬝ᵥ w₀ = 0 := hw0
  have hBv : B ⬝ᵥ v₀ = 0 := hv0
  have hBw : B ⬝ᵥ w₀ = 0 := hvw
  let M : Matrix (Fin n) (Fin n) (PSUF g) := Matrix.vecMulVec v₀ A - Matrix.vecMulVec w₀ B
  have hM2 : M * M = 0 := by
    simp only [M, Matrix.sub_mul, Matrix.mul_sub, Matrix.vecMulVec_mul_vecMulVec, hAv, hAw,
      hBv, hBw, zero_smul]
    abel
  have h1 : (1 + M) * (1 - M) = 1 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hM2]
    abel
  have h2 : (1 - M) * (1 + M) = 1 := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hM2]
    abel
  let gU : GL (Fin n) (PSUF g) := ⟨1 + M, 1 - M, h1, h2⟩
  have hgmem : gU ∈ unitPairGroup (PSUσ g).toRingHom J v₀ w₀ := by
    refine Subgroup.subset_closure ⟨1, ?_⟩
    show (gU : Matrix (Fin n) (Fin n) (PSUF g)) = 1 + (1 : PSUF g) •
        Matrix.vecMulVec v₀ (Matrix.vecMul (fun i => PSUσ g (w₀ i)) J) -
        PSUσ g (1 : PSUF g) •
        Matrix.vecMulVec w₀ (Matrix.vecMul (fun i => PSUσ g (v₀ i)) J)
    rw [map_one, one_smul, one_smul]
    show (1 : Matrix (Fin n) (Fin n) (PSUF g)) + M =
      1 + Matrix.vecMulVec v₀ A - Matrix.vecMulVec w₀ B
    rw [show M = Matrix.vecMulVec v₀ A - Matrix.vecMulVec w₀ B from rfl]
    abel
  obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp (hle hgmem)
  have hGG : ⁅glBlockCentralizer (PSUj n g) S ε, glBlockCentralizer (PSUj n g) S ε⁆ ≤
      glBlockCentralizer (PSUj n g) S ε := by
    refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_)
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have huG : u ∈ glBlockCentralizer (PSUj n g) S ε := by
    apply hGG
    rw [hM.derived]
    exact hu
  have hfix := (mem_glBlockCentralizer_PSU_iff.mp huG).2
  have hfix' : (gU : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - ε) = 1 - ε := by
    rw [← hueq]
    exact hfix
  have hMfix : M * (1 - ε) = 0 := by
    rw [show (gU : Matrix (Fin n) (Fin n) (PSUF g)) = 1 + M from rfl, Matrix.add_mul,
      Matrix.one_mul] at hfix'
    exact add_left_cancel (hfix'.trans (add_zero (1 - ε)).symm)
  have hrel : Matrix.vecMulVec v₀ (Matrix.vecMul A (1 - ε)) =
      Matrix.vecMulVec w₀ (Matrix.vecMul B (1 - ε)) := by
    have h := hMfix
    rw [show M = Matrix.vecMulVec v₀ A - Matrix.vecMulVec w₀ B from rfl, Matrix.sub_mul,
      Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, sub_eq_zero] at h
    exact h
  obtain ⟨hA1e, hB1e⟩ := bmDPU_vecMulVec_eq_of_indep hli hrel
  have hw : Matrix.mulVec (1 - ε) w₀ = 0 :=
    bmDPU_one_sub_vec_of_vecMul_one_sub (PSUσ g) (bmDPU_eps_adj hM) hA1e
  have hv : Matrix.mulVec (1 - ε) v₀ = 0 :=
    bmDPU_one_sub_vec_of_vecMul_one_sub (PSUσ g) (bmDPU_eps_adj hM) hB1e
  exact ⟨hv, hw⟩

private lemma bmDPU_pair_decomp {n g k : ℕ}
    {S : Set (GL (Fin n) (PSUF g))} {e : Matrix (Fin n) (Fin n) (PSUF g)}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (hM : PSUDualPairModel n g S e P Q R W hD)
    {v₀ w₀ : Fin n → PSUF g}
    (hv0 : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hw0 : Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hvw : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hli : LinearIndependent (PSUF g) ![v₀, w₀])
    (hle : unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      (dualPairEmbSU hD).range.map (Unitary.SU (PSUσ g) n).subtype) :
    ∃ x y x' y' : Fin (k + 1) → PSUF g,
      v₀ = Matrix.mulVec P x + Matrix.mulVec Q y ∧
      w₀ = Matrix.mulVec P x' + Matrix.mulVec Q y' := by
  obtain ⟨hv, hw⟩ := bmDPU_pair_mem_block hD hM hv0 hw0 hvw hli hle
  have hε : e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e = P * R + Q * W := by
    rw [← hM.e_eq, hM.adj_eq]
  refine ⟨Matrix.mulVec R v₀, Matrix.mulVec W v₀, Matrix.mulVec R w₀,
    Matrix.mulVec W w₀, ?_, ?_⟩
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    conv_lhs => rw [hv]
    rw [hε, Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hw
    conv_lhs => rw [hw]
    rw [hε, Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

private lemma bmDPU_dpEmb_mul_P {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (a a'' : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) :
    dpEmb P Q R W a a'' * P = P * a := by
  unfold dpEmb
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hD.rp, hD.wp,
    Matrix.mul_one, Matrix.mul_zero, add_zero]
  abel

private lemma bmDPU_dpEmb_mul_Q {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (a a'' : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) :
    dpEmb P Q R W a a'' * Q = Q * a'' := by
  unfold dpEmb
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hD.rq, hD.wq,
    Matrix.mul_one, Matrix.mul_zero, zero_add, add_zero]
  abel

private lemma bmDPU_one_sub_mulVec_decomp {n g k : ℕ}
    {P : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W) (x y : Fin (k + 1) → PSUF g) :
    Matrix.mulVec (1 - P * R) (Matrix.mulVec P x + Matrix.mulVec Q y) =
      Matrix.mulVec Q y := by
  have hx : Matrix.mulVec (P * R) (Matrix.mulVec P x) = Matrix.mulVec P x := by
    rw [← Matrix.mulVec_mulVec (Matrix.mulVec P x) P R, Matrix.mulVec_mulVec x R P,
      hD.rp, Matrix.one_mulVec]
  have hy : Matrix.mulVec (P * R) (Matrix.mulVec Q y) = 0 := by
    rw [← Matrix.mulVec_mulVec (Matrix.mulVec Q y) P R, Matrix.mulVec_mulVec y R Q,
      hD.rq, Matrix.zero_mulVec, Matrix.mulVec_zero]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, hx, hy]
  abel

private lemma bmDPU_vecMul_decomp_mul_P {n g k : ℕ}
    {P : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W) (x y : Fin (k + 1) → PSUF g) :
    Matrix.vecMul (Matrix.vecMul
        (fun i => PSUσ g ((Matrix.mulVec P x + Matrix.mulVec Q y) i)) (Unitary.antidiag n)) P =
      fun i => PSUσ g (y i) := by
  have h1 : (fun i => PSUσ g ((Matrix.mulVec P x + Matrix.mulVec Q y) i)) =
      Matrix.mulVec (P.map (PSUσ g).toRingHom) ((PSUσ g).toRingHom ∘ x) +
      Matrix.mulVec (Q.map (PSUσ g).toRingHom) ((PSUσ g).toRingHom ∘ y) := by
    funext i
    simp only [Pi.add_apply]
    rw [map_add, ← RingHom.map_mulVec (PSUσ g).toRingHom P x i,
      ← RingHom.map_mulVec (PSUσ g).toRingHom Q y i]
    rfl
  rw [h1, Matrix.add_vecMul, Matrix.vecMul_mulVec, Matrix.vecMul_mulVec,
    show (P.map (PSUσ g).toRingHom).transpose *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) = W from hD.pj,
    show (Q.map (PSUσ g).toRingHom).transpose *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) = R from hD.qj,
    Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hD.wp, hD.rp,
    Matrix.vecMul_zero, Matrix.vecMul_one, zero_add]
  rfl

private lemma bmDPU_one_sub_mulVec_decomp_W {n g k : ℕ}
    {P : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W) (x y : Fin (k + 1) → PSUF g) :
    Matrix.mulVec (1 - Q * W) (Matrix.mulVec P x + Matrix.mulVec Q y) =
      Matrix.mulVec P x := by
  have hx : Matrix.mulVec (Q * W) (Matrix.mulVec P x) = 0 := by
    rw [← Matrix.mulVec_mulVec (Matrix.mulVec P x) Q W, Matrix.mulVec_mulVec x W P,
      hD.wp, Matrix.zero_mulVec, Matrix.mulVec_zero]
  have hy : Matrix.mulVec (Q * W) (Matrix.mulVec Q y) = Matrix.mulVec Q y := by
    rw [← Matrix.mulVec_mulVec (Matrix.mulVec Q y) Q W, Matrix.mulVec_mulVec y W Q,
      hD.wq, Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, hx, hy]
  abel

private lemma bmDPU_vecMul_decomp_mul_Q {n g k : ℕ}
    {P : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W) (x y : Fin (k + 1) → PSUF g) :
    Matrix.vecMul (Matrix.vecMul
        (fun i => PSUσ g ((Matrix.mulVec P x + Matrix.mulVec Q y) i)) (Unitary.antidiag n)) Q =
      fun i => PSUσ g (x i) := by
  have h1 : (fun i => PSUσ g ((Matrix.mulVec P x + Matrix.mulVec Q y) i)) =
      Matrix.mulVec (P.map (PSUσ g).toRingHom) ((PSUσ g).toRingHom ∘ x) +
      Matrix.mulVec (Q.map (PSUσ g).toRingHom) ((PSUσ g).toRingHom ∘ y) := by
    funext i
    simp only [Pi.add_apply]
    rw [map_add, ← RingHom.map_mulVec (PSUσ g).toRingHom P x i,
      ← RingHom.map_mulVec (PSUσ g).toRingHom Q y i]
    rfl
  rw [h1, Matrix.add_vecMul, Matrix.vecMul_mulVec, Matrix.vecMul_mulVec,
    show (P.map (PSUσ g).toRingHom).transpose *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) = W from hD.pj,
    show (Q.map (PSUσ g).toRingHom).transpose *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) = R from hD.qj,
    Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hD.wq, hD.rq,
    Matrix.vecMul_one, Matrix.vecMul_zero, add_zero]
  rfl

private lemma bmDPU_pair_relations {n g k : ℕ}
    {S : Set (GL (Fin n) (PSUF g))} {e : Matrix (Fin n) (Fin n) (PSUF g)}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (hM : PSUDualPairModel n g S e P Q R W hD)
    {v₀ w₀ : Fin n → PSUF g} {x y x' y' : Fin (k + 1) → PSUF g}
    (hv0 : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hw0 : Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hvw : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hv : v₀ = Matrix.mulVec P x + Matrix.mulVec Q y)
    (hw : w₀ = Matrix.mulVec P x' + Matrix.mulVec Q y')
    (hle : unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      (dualPairEmbSU hD).range.map (Unitary.SU (PSUσ g) n).subtype) :
    Matrix.vecMulVec y (fun i => PSUσ g (y' i)) =
      Matrix.vecMulVec y' (fun i => PSUσ g (y i)) ∧
    Matrix.vecMulVec x (fun i => PSUσ g (x' i)) =
      Matrix.vecMulVec x' (fun i => PSUσ g (x i)) := by
  classical
  let J : Matrix (Fin n) (Fin n) (PSUF g) := Unitary.antidiag n
  let A : Fin n → PSUF g := Matrix.vecMul (fun i => PSUσ g (w₀ i)) J
  let B : Fin n → PSUF g := Matrix.vecMul (fun i => PSUσ g (v₀ i)) J
  have hAv : A ⬝ᵥ v₀ = 0 := by
    show Matrix.vecMul (fun i => PSUσ g (w₀ i)) J ⬝ᵥ v₀ = 0
    exact (bmDPU_form_swap v₀ w₀).trans (by rw [hvw, map_zero])
  have hAw : A ⬝ᵥ w₀ = 0 := hw0
  have hBv : B ⬝ᵥ v₀ = 0 := hv0
  have hBw : B ⬝ᵥ w₀ = 0 := hvw
  let M : Matrix (Fin n) (Fin n) (PSUF g) := Matrix.vecMulVec v₀ A - Matrix.vecMulVec w₀ B
  have hM2 : M * M = 0 := by
    simp only [M, Matrix.sub_mul, Matrix.mul_sub, Matrix.vecMulVec_mul_vecMulVec, hAv, hAw,
      hBv, hBw, zero_smul]
    abel
  have h1 : (1 + M) * (1 - M) = 1 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hM2]
    abel
  have h2 : (1 - M) * (1 + M) = 1 := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hM2]
    abel
  let gU : GL (Fin n) (PSUF g) := ⟨1 + M, 1 - M, h1, h2⟩
  have hgmem : gU ∈ unitPairGroup (PSUσ g).toRingHom J v₀ w₀ := by
    refine Subgroup.subset_closure ⟨1, ?_⟩
    show (gU : Matrix (Fin n) (Fin n) (PSUF g)) = 1 + (1 : PSUF g) •
        Matrix.vecMulVec v₀ (Matrix.vecMul (fun i => PSUσ g (w₀ i)) J) -
        PSUσ g (1 : PSUF g) •
        Matrix.vecMulVec w₀ (Matrix.vecMul (fun i => PSUσ g (v₀ i)) J)
    rw [map_one, one_smul, one_smul]
    show (1 : Matrix (Fin n) (Fin n) (PSUF g)) + M =
      1 + Matrix.vecMulVec v₀ A - Matrix.vecMulVec w₀ B
    rw [show M = Matrix.vecMulVec v₀ A - Matrix.vecMulVec w₀ B from rfl]
    abel
  obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp (hle hgmem)
  have hGG : ⁅glBlockCentralizer (PSUj n g) S
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e),
      glBlockCentralizer (PSUj n g) S
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e)⁆ ≤
      glBlockCentralizer (PSUj n g) S
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e) := by
    refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_)
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have huG : u ∈ glBlockCentralizer (PSUj n g) S
      (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e) := by
    apply hGG
    rw [hM.derived]
    exact hu
  obtain ⟨a, haσ, hueq2⟩ := (hM.blockGroup u).mp huG
  have hg_eq : (gU : Matrix (Fin n) (Fin n) (PSUF g)) =
      dpEmb P Q R W (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g))
        (tcConjTr (PSUσ g) (((a⁻¹ : GL (Fin (k + 1)) (PSUF g))) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g))) := by
    have hGL : gU = dualPairEmbGL hD a := hueq.symm.trans hueq2
    rw [hGL, coe_dualPairEmbGL]
  have hgP : (gU : Matrix (Fin n) (Fin n) (PSUF g)) * P =
      P * (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) := by
    rw [hg_eq, bmDPU_dpEmb_mul_P hD (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) _]
  have hPRv : Matrix.mulVec (1 - P * R) v₀ = Matrix.mulVec Q y := by
    rw [hv]; exact bmDPU_one_sub_mulVec_decomp hD x y
  have hPRw : Matrix.mulVec (1 - P * R) w₀ = Matrix.mulVec Q y' := by
    rw [hw]; exact bmDPU_one_sub_mulVec_decomp hD x' y'
  have hAP : Matrix.vecMul A P = fun i => PSUσ g (y' i) := by
    show Matrix.vecMul (Matrix.vecMul (fun i => PSUσ g (w₀ i)) J) P = _
    rw [hw]; exact bmDPU_vecMul_decomp_mul_P hD x' y'
  have hBP : Matrix.vecMul B P = fun i => PSUσ g (y i) := by
    show Matrix.vecMul (Matrix.vecMul (fun i => PSUσ g (v₀ i)) J) P = _
    rw [hv]; exact bmDPU_vecMul_decomp_mul_P hD x y
  have hP0 : (1 - P * R) * P = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hD.rp, Matrix.mul_one, sub_self]
  have hMv : (1 - P * R) * M = Matrix.vecMulVec (Matrix.mulVec Q y) A -
      Matrix.vecMulVec (Matrix.mulVec Q y') B := by
    rw [show M = Matrix.vecMulVec v₀ A - Matrix.vecMulVec w₀ B from rfl, Matrix.mul_sub,
      Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, hPRv, hPRw]
  have hexpP : (1 - P * R) * ((gU : Matrix (Fin n) (Fin n) (PSUF g)) * P) =
      Q * (Matrix.vecMulVec y (fun i => PSUσ g (y' i)) -
           Matrix.vecMulVec y' (fun i => PSUσ g (y i))) := by
    rw [show (gU : Matrix (Fin n) (Fin n) (PSUF g)) = 1 + M from rfl, ← Matrix.mul_assoc,
      Matrix.mul_add, Matrix.mul_one, hMv, Matrix.add_mul, hP0, zero_add, Matrix.sub_mul,
      Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, hAP, hBP, ← Matrix.mul_vecMulVec,
      ← Matrix.mul_vecMulVec, ← Matrix.mul_sub]
  have hzeroP : (1 - P * R) * ((gU : Matrix (Fin n) (Fin n) (PSUF g)) * P) = 0 := by
    rw [hgP, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hD.rp,
      Matrix.mul_one, sub_self, Matrix.zero_mul]
  have hQinj : ∀ D : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g), Q * D = 0 → D = 0 := by
    intro D hDq
    have h := congrArg (fun Z : Matrix (Fin n) (Fin (k + 1)) (PSUF g) => W * Z) hDq
    rw [Matrix.mul_zero, ← Matrix.mul_assoc, hD.wq, Matrix.one_mul] at h
    exact h
  have hPinj : ∀ D : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g), P * D = 0 → D = 0 := by
    intro D hDp
    have h := congrArg (fun Z : Matrix (Fin n) (Fin (k + 1)) (PSUF g) => R * Z) hDp
    rw [Matrix.mul_zero, ← Matrix.mul_assoc, hD.rp, Matrix.one_mul] at h
    exact h
  have hrel1 : Matrix.vecMulVec y (fun i => PSUσ g (y' i)) =
      Matrix.vecMulVec y' (fun i => PSUσ g (y i)) :=
    sub_eq_zero.mp (hQinj _ (by rw [← hexpP]; exact hzeroP))
  have hWQv : Matrix.mulVec (1 - Q * W) v₀ = Matrix.mulVec P x := by
    rw [hv]; exact bmDPU_one_sub_mulVec_decomp_W hD x y
  have hWQw : Matrix.mulVec (1 - Q * W) w₀ = Matrix.mulVec P x' := by
    rw [hw]; exact bmDPU_one_sub_mulVec_decomp_W hD x' y'
  have hAQ : Matrix.vecMul A Q = fun i => PSUσ g (x' i) := by
    show Matrix.vecMul (Matrix.vecMul (fun i => PSUσ g (w₀ i)) J) Q = _
    rw [hw]; exact bmDPU_vecMul_decomp_mul_Q hD x' y'
  have hBQ : Matrix.vecMul B Q = fun i => PSUσ g (x i) := by
    show Matrix.vecMul (Matrix.vecMul (fun i => PSUσ g (v₀ i)) J) Q = _
    rw [hv]; exact bmDPU_vecMul_decomp_mul_Q hD x y
  have hQ0 : (1 - Q * W) * Q = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hD.wq, Matrix.mul_one, sub_self]
  have hMvQ : (1 - Q * W) * M = Matrix.vecMulVec (Matrix.mulVec P x) A -
      Matrix.vecMulVec (Matrix.mulVec P x') B := by
    rw [show M = Matrix.vecMulVec v₀ A - Matrix.vecMulVec w₀ B from rfl, Matrix.mul_sub,
      Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, hWQv, hWQw]
  have hexpQ : (1 - Q * W) * ((gU : Matrix (Fin n) (Fin n) (PSUF g)) * Q) =
      P * (Matrix.vecMulVec x (fun i => PSUσ g (x' i)) -
           Matrix.vecMulVec x' (fun i => PSUσ g (x i))) := by
    rw [show (gU : Matrix (Fin n) (Fin n) (PSUF g)) = 1 + M from rfl, ← Matrix.mul_assoc,
      Matrix.mul_add, Matrix.mul_one, hMvQ, Matrix.add_mul, hQ0, zero_add, Matrix.sub_mul,
      Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, hAQ, hBQ, ← Matrix.mul_vecMulVec,
      ← Matrix.mul_vecMulVec, ← Matrix.mul_sub]
  have hgQ : (gU : Matrix (Fin n) (Fin n) (PSUF g)) * Q =
      Q * (tcConjTr (PSUσ g) (((a⁻¹ : GL (Fin (k + 1)) (PSUF g))) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g))) := by
    rw [hg_eq, bmDPU_dpEmb_mul_Q hD (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) _]
  have hzeroQ : (1 - Q * W) * ((gU : Matrix (Fin n) (Fin n) (PSUF g)) * Q) = 0 := by
    rw [hgQ, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hD.wq,
      Matrix.mul_one, sub_self, Matrix.zero_mul]
  have hrel2 : Matrix.vecMulVec x (fun i => PSUσ g (x' i)) =
      Matrix.vecMulVec x' (fun i => PSUσ g (x i)) :=
    sub_eq_zero.mp (hPinj _ (by rw [← hexpQ]; exact hzeroQ))
  exact ⟨hrel1, hrel2⟩

private lemma bmDPU_pair_range_le {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    {v₀ w₀ : Fin n → PSUF g}
    (hle : unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      (dualPairEmbSU hD).range.map (Unitary.SU (PSUσ g) n).subtype) :
    unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      (dualPairEmbGL hD).range := by
  rintro g hg
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp (hle hg)
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hu
  exact ⟨Matrix.SpecialLinearGroup.toGL a, coe_dualPairEmbSU hD a⟩

private noncomputable def bmDPU_pair_N {n g : ℕ} (v₀ w₀ : Fin n → PSUF g) (c : PSUF g) :
    Matrix (Fin n) (Fin n) (PSUF g) :=
  c • Matrix.vecMulVec v₀ (Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n)) -
    PSUσ g c • Matrix.vecMulVec w₀ (Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n))

private lemma bmDPU_pair_N_nilpotent {n g : ℕ} (v₀ w₀ : Fin n → PSUF g) (c : PSUF g)
    (hv0 : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hw0 : Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hvw : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0) :
    bmDPU_pair_N v₀ w₀ c * bmDPU_pair_N v₀ w₀ c = 0 := by
  have hA0 : Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0 :=
    (bmDPU_form_swap v₀ w₀).trans (by rw [hvw, map_zero])
  unfold bmDPU_pair_N
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.vecMulVec_mul_vecMulVec, hA0, hw0, hv0, hvw]
  simp

private lemma bmDPU_pair_N_preimage {n g k : ℕ} (c : PSUF g)
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    {v₀ w₀ : Fin n → PSUF g} {x y x' y' : Fin (k + 1) → PSUF g}
    (hv : v₀ = Matrix.mulVec P x + Matrix.mulVec Q y)
    (hw : w₀ = Matrix.mulVec P x' + Matrix.mulVec Q y') :
    R * (1 + bmDPU_pair_N v₀ w₀ c) * P =
      1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
        PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i)) := by
  have hRv : Matrix.mulVec R v₀ = x := by
    rw [hv, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD.rp, hD.rq,
      Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
  have hRw : Matrix.mulVec R w₀ = x' := by
    rw [hw, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD.rp, hD.rq,
      Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
  have hAP : Matrix.vecMul (Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n)) P =
      fun i => PSUσ g (y' i) := by
    rw [hw]; exact bmDPU_vecMul_decomp_mul_P hD x' y'
  have hBP : Matrix.vecMul (Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n)) P =
      fun i => PSUσ g (y i) := by
    rw [hv]; exact bmDPU_vecMul_decomp_mul_P hD x y
  unfold bmDPU_pair_N
  rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, hRv, hRw]
  rw [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, hD.rp,
    Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, hAP, hBP]
  abel

private lemma bmDPU_pair_N_gen_mem {n g : ℕ} (v₀ w₀ : Fin n → PSUF g) (c : PSUF g)
    (hv0 : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hw0 : Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hvw : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0) :
    ∃ u : GL (Fin n) (PSUF g),
      u ∈ unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ∧
      (u : Matrix (Fin n) (Fin n) (PSUF g)) = 1 + bmDPU_pair_N v₀ w₀ c := by
  have hsq : bmDPU_pair_N v₀ w₀ c * bmDPU_pair_N v₀ w₀ c = 0 :=
    bmDPU_pair_N_nilpotent v₀ w₀ c hv0 hw0 hvw
  refine ⟨⟨1 + bmDPU_pair_N v₀ w₀ c, 1 - bmDPU_pair_N v₀ w₀ c, ?_, ?_⟩,
    Subgroup.subset_closure ⟨c, ?_⟩, rfl⟩
  · rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hsq, add_zero]
    abel
  · rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hsq, add_zero]
    abel
  · simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    unfold bmDPU_pair_N
    abel

private lemma bmDPU_pair_generators_mem {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    {v₀ w₀ : Fin n → PSUF g} {x y x' y' : Fin (k + 1) → PSUF g}
    (hv0 : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hw0 : Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hvw : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hv : v₀ = Matrix.mulVec P x + Matrix.mulVec Q y)
    (hw : w₀ = Matrix.mulVec P x' + Matrix.mulVec Q y')
    (hle : unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      (dualPairEmbSU hD).range.map (Unitary.SU (PSUσ g) n).subtype) :
    ∀ c : PSUF g, ∃ a ∈ (unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀).comap
        (dualPairEmbGL hD),
      (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
        1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
          PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i)) := by
  intro c
  obtain ⟨gg, hgmem, hgval⟩ := bmDPU_pair_N_gen_mem v₀ w₀ c hv0 hw0 hvw
  have hrange : gg ∈ (dualPairEmbGL hD).range := bmDPU_pair_range_le hD hle hgmem
  obtain ⟨a, ha⟩ := hrange
  refine ⟨a, ?_, ?_⟩
  · rw [Subgroup.mem_comap, ha]; exact hgmem
  · have hmat : (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
        R * (gg : Matrix (Fin n) (Fin n) (PSUF g)) * P := by
      calc (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g))
          = R * ((dualPairEmbGL hD a : GL (Fin n) (PSUF g)) :
              Matrix (Fin n) (Fin n) (PSUF g)) * P := by
            rw [coe_dualPairEmbGL]
            exact (R_dpEmb_P hD.rp hD.rq (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g))
              (tcConjTr (PSUσ g) ((a⁻¹ : GL (Fin (k + 1)) (PSUF g)) :
                Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)))).symm
        _ = R * (gg : Matrix (Fin n) (Fin n) (PSUF g)) * P := by rw [ha]
    rw [hmat, hgval, bmDPU_pair_N_preimage c hD hv hw]

private lemma bmDPU_pair_dualPairEmbGL_injective {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W) :
    Function.Injective (dualPairEmbGL hD) := by
  intro s t hst
  apply Units.ext
  have hs : (s : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
      R * ((dualPairEmbGL hD s : GL (Fin n) (PSUF g)) :
        Matrix (Fin n) (Fin n) (PSUF g)) * P := by
    rw [coe_dualPairEmbGL]
    exact (R_dpEmb_P hD.rp hD.rq _ _).symm
  have ht : (t : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
      R * ((dualPairEmbGL hD t : GL (Fin n) (PSUF g)) :
        Matrix (Fin n) (Fin n) (PSUF g)) * P := by
    rw [coe_dualPairEmbGL]
    exact (R_dpEmb_P hD.rp hD.rq _ _).symm
  rw [hs, ht, hst]

private lemma bmDPU_pair_comap_eq_closure_of_mem {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    {v₀ w₀ : Fin n → PSUF g} {x y x' y' : Fin (k + 1) → PSUF g}
    (hv : v₀ = Matrix.mulVec P x + Matrix.mulVec Q y)
    (hw : w₀ = Matrix.mulVec P x' + Matrix.mulVec Q y')
    (hle : unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      (dualPairEmbSU hD).range.map (Unitary.SU (PSUσ g) n).subtype)
    (hS : ∀ c : PSUF g, ∃ a ∈ (unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀).comap
        (dualPairEmbGL hD),
      (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
        1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
          PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))) :
    (unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀).comap
        (dualPairEmbGL hD) =
      Subgroup.closure {a : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
            PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} := by
  have hinj : Function.Injective (dualPairEmbGL hD) :=
    bmDPU_pair_dualPairEmbGL_injective hD
  have hrange_le : unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      (dualPairEmbGL hD).range := bmDPU_pair_range_le hD hle
  have hmap_le : (Subgroup.closure {a : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
            PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))}).map
        (dualPairEmbGL hD) ≤
      unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ := by
    rw [Subgroup.map_le_iff_le_comap]
    rw [Subgroup.closure_le]
    rintro b ⟨c, hbc⟩
    obtain ⟨a, ha, ha_mat⟩ := hS c
    have hba : b = a := Units.ext (hbc.trans ha_mat.symm)
    rwa [hba]
  have hK_le : unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      (Subgroup.closure {a : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
            PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))}).map
        (dualPairEmbGL hD) := by
    unfold unitPairGroup
    rw [Subgroup.closure_le]
    rintro u ⟨c, huc⟩
    obtain ⟨t, ht⟩ := hrange_le (Subgroup.subset_closure ⟨c, huc⟩)
    refine ⟨t, Subgroup.subset_closure ⟨c, ?_⟩, ht⟩
    have ht' : (t : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
        R * (u : Matrix (Fin n) (Fin n) (PSUF g)) * P := by
      rw [← ht, coe_dualPairEmbGL]
      exact (R_dpEmb_P hD.rp hD.rq _ _).symm
    rw [ht']
    have huN : (u : Matrix (Fin n) (Fin n) (PSUF g)) =
        1 + bmDPU_pair_N v₀ w₀ c := by
      rw [huc]
      unfold bmDPU_pair_N
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      abel
    rw [huN, bmDPU_pair_N_preimage c hD hv hw]
  have hK : unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ =
      (Subgroup.closure {a : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
            PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))}).map
        (dualPairEmbGL hD) := le_antisymm hK_le hmap_le
  rw [hK]
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨b, hb, hbfx⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hx)
    have hxb : b = x := hinj hbfx
    rwa [← hxb]
  · intro x hx
    exact Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

private lemma bmDPU_pair_comap_eq_closure {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    {v₀ w₀ : Fin n → PSUF g} {x y x' y' : Fin (k + 1) → PSUF g}
    (hv0 : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hw0 : Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hvw : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hv : v₀ = Matrix.mulVec P x + Matrix.mulVec Q y)
    (hw : w₀ = Matrix.mulVec P x' + Matrix.mulVec Q y')
    (hle : unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      (dualPairEmbSU hD).range.map (Unitary.SU (PSUσ g) n).subtype) :
    (unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀).comap
        (dualPairEmbGL hD) =
      Subgroup.closure {a : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
            PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} := by
  exact bmDPU_pair_comap_eq_closure_of_mem hD hv hw hle
    (bmDPU_pair_generators_mem hD hv0 hw0 hvw hv hw hle)

private lemma bmDPU_pair_closure_matTransv_rank_one {g k : ℕ}
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)}
    {a φ : Fin (k + 1) → PSUF g} (hM : M = Matrix.vecMulVec a φ) :
    Subgroup.closure {b : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) = 1 + c • M} =
      matTransvGroup a φ := by
  rw [hM]
  unfold matTransvGroup
  rfl

private lemma bmDPU_pair_closure_matTransv_zero_left_data {g k : ℕ}
    {y x' : Fin (k + 1) → PSUF g}
    (hx' : x' ≠ 0) (hy : (fun i => PSUσ g (y i)) ≠ 0)
    (hiso : (fun i => PSUσ g (y i)) ⬝ᵥ x' = 0) :
    ∃ a φ : Fin (k + 1) → PSUF g, a ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ a = 0 ∧
      Matrix.vecMulVec x' (fun i => PSUσ g (y i)) = Matrix.vecMulVec a φ :=
  ⟨x', (fun i => PSUσ g (y i)), hx', hy, hiso, rfl⟩

private lemma bmDPU_pair_closure_matTransv_zero_left_gen {g k : ℕ}
    {x y x' y' : Fin (k + 1) → PSUF g}
    (hA : Matrix.vecMulVec x (fun i => PSUσ g (y' i)) = 0) :
    Subgroup.closure {b : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
            PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} =
      Subgroup.closure {b : GL (Fin (k + 1)) (PSUF g) | ∃ d : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + d • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} := by
  have hS : {b : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
            PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} =
      {b : GL (Fin (k + 1)) (PSUF g) | ∃ d : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + d • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} := by
    ext b
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨PSUσ g c, ?_⟩
      rw [hA, smul_zero, add_zero] at hc
      rw [hc, sub_eq_add_neg, ← neg_smul]
      simp only [CharTwo.neg_eq]
    · rintro ⟨d, hd⟩
      obtain ⟨c, hc⟩ := (PSUσ g).surjective d
      refine ⟨c, ?_⟩
      rw [hA, smul_zero, add_zero, hd, hc, sub_eq_add_neg, ← neg_smul]
      simp only [CharTwo.neg_eq]
  rw [hS]

private lemma bmDPU_pair_closure_matTransv_zero_left {g k : ℕ}
    {x y x' y' : Fin (k + 1) → PSUF g}
    (hA : Matrix.vecMulVec x (fun i => PSUσ g (y' i)) = 0)
    (hx' : x' ≠ 0) (hy : (fun i => PSUσ g (y i)) ≠ 0)
    (hiso : (fun i => PSUσ g (y i)) ⬝ᵥ x' = 0) :
    ∃ (a φ : Fin (k + 1) → PSUF g), a ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ a = 0 ∧
      Subgroup.closure {b : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
            PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} =
        matTransvGroup a φ := by
  obtain ⟨a, φ, ha, hφ, hφa, hB⟩ :=
    bmDPU_pair_closure_matTransv_zero_left_data hx' hy hiso
  refine ⟨a, φ, ha, hφ, hφa, ?_⟩
  rw [bmDPU_pair_closure_matTransv_zero_left_gen hA]
  rw [hB]
  exact bmDPU_pair_closure_matTransv_rank_one rfl

private lemma bmDPU_pair_closure_matTransv_zero_right_gen {g k : ℕ}
    {x y x' y' : Fin (k + 1) → PSUF g}
    (hB : Matrix.vecMulVec x' (fun i => PSUσ g (y i)) = 0) :
    Subgroup.closure {b : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
            PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} =
      Subgroup.closure {b : GL (Fin (k + 1)) (PSUF g) | ∃ d : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + d • Matrix.vecMulVec x (fun i => PSUσ g (y' i))} := by
  have hS : {b : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
            PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} =
      {b : GL (Fin (k + 1)) (PSUF g) | ∃ d : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + d • Matrix.vecMulVec x (fun i => PSUσ g (y' i))} := by
    ext b
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hB] at hc; simpa using hc⟩
    · rintro ⟨d, hd⟩
      exact ⟨d, by rw [hB]; simpa using hd⟩
  rw [hS]

private lemma bmDPU_pair_closure_matTransv_zero_right_data {g k : ℕ}
    {x y' : Fin (k + 1) → PSUF g}
    (hx : x ≠ 0) (hy' : (fun i => PSUσ g (y' i)) ≠ 0)
    (hiso' : (fun i => PSUσ g (y' i)) ⬝ᵥ x = 0) :
    ∃ a φ : Fin (k + 1) → PSUF g, a ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ a = 0 ∧
      Matrix.vecMulVec x (fun i => PSUσ g (y' i)) = Matrix.vecMulVec a φ :=
  ⟨x, (fun i => PSUσ g (y' i)), hx, hy', hiso', rfl⟩

private lemma bmDPU_pair_closure_matTransv_zero_right {g k : ℕ}
    {x y x' y' : Fin (k + 1) → PSUF g}
    (hB : Matrix.vecMulVec x' (fun i => PSUσ g (y i)) = 0)
    (hx : x ≠ 0) (hy' : (fun i => PSUσ g (y' i)) ≠ 0)
    (hiso' : (fun i => PSUσ g (y' i)) ⬝ᵥ x = 0) :
    ∃ (a φ : Fin (k + 1) → PSUF g), a ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ a = 0 ∧
      Subgroup.closure {b : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
            PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} =
        matTransvGroup a φ := by
  obtain ⟨a, φ, ha, hφ, hφa, hA⟩ :=
    bmDPU_pair_closure_matTransv_zero_right_data hx hy' hiso'
  refine ⟨a, φ, ha, hφ, hφa, ?_⟩
  rw [bmDPU_pair_closure_matTransv_zero_right_gen hB]
  rw [hA]
  exact bmDPU_pair_closure_matTransv_rank_one rfl

private lemma bmDPU_pair_closure_matTransv_prop_gen {g k : ℕ}
    {x y x' y' : Fin (k + 1) → PSUF g} {lam : PSUF g}
    (hAB : Matrix.vecMulVec x (fun i => PSUσ g (y' i)) =
      lam • Matrix.vecMulVec x' (fun i => PSUσ g (y i)))
    (hsurj : Function.Surjective (fun c => c * lam - PSUσ g c)) :
    Subgroup.closure {b : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
            PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} =
      Subgroup.closure {b : GL (Fin (k + 1)) (PSUF g) | ∃ d : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + d • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} := by
  have hS : {b : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
            PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} =
      {b : GL (Fin (k + 1)) (PSUF g) | ∃ d : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + d • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} := by
    ext b
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c * lam - PSUσ g c, ?_⟩
      rw [hAB] at hc
      rw [hc]
      simp only [smul_smul, sub_smul]
      abel
    · rintro ⟨d, hd⟩
      obtain ⟨c, hc⟩ := hsurj d
      refine ⟨c, ?_⟩
      rw [hAB, hd, ← hc]
      simp only [smul_smul, sub_smul]
      abel
  rw [hS]

private lemma bmDPU_pair_closure_matTransv_prop_data {g k : ℕ}
    {x' y : Fin (k + 1) → PSUF g}
    (hx' : x' ≠ 0) (hy : (fun i => PSUσ g (y i)) ≠ 0)
    (hiso : (fun i => PSUσ g (y i)) ⬝ᵥ x' = 0) :
    ∃ a φ : Fin (k + 1) → PSUF g, a ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ a = 0 ∧
      Matrix.vecMulVec x' (fun i => PSUσ g (y i)) = Matrix.vecMulVec a φ :=
  ⟨x', (fun i => PSUσ g (y i)), hx', hy, hiso, rfl⟩

private lemma bmDPU_pair_closure_matTransv_prop {g k : ℕ}
    {x y x' y' : Fin (k + 1) → PSUF g}
    (hprop : ∃ lam : PSUF g, lam ≠ 0 ∧
      Matrix.vecMulVec x (fun i => PSUσ g (y' i)) =
        lam • Matrix.vecMulVec x' (fun i => PSUσ g (y i)) ∧
      Function.Surjective (fun c => c * lam - PSUσ g c))
    (hx' : x' ≠ 0) (hy : (fun i => PSUσ g (y i)) ≠ 0)
    (hiso : (fun i => PSUσ g (y i)) ⬝ᵥ x' = 0) :
    ∃ (a φ : Fin (k + 1) → PSUF g), a ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ a = 0 ∧
      Subgroup.closure {b : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
            PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} =
        matTransvGroup a φ := by
  obtain ⟨lam, hlam, hAB, hsurj⟩ := hprop
  obtain ⟨a, φ, ha, hφ, hφa, hB⟩ :=
    bmDPU_pair_closure_matTransv_prop_data hx' hy hiso
  refine ⟨a, φ, ha, hφ, hφa, ?_⟩
  rw [bmDPU_pair_closure_matTransv_prop_gen hAB hsurj]
  rw [hB]
  exact bmDPU_pair_closure_matTransv_rank_one rfl

private lemma bmDPU_pair_closure_matTransv {g k : ℕ}
    {x y x' y' : Fin (k + 1) → PSUF g}
    (hscal :
      (Matrix.vecMulVec x (fun i => PSUσ g (y' i)) = 0 ∧ x' ≠ 0 ∧
        (fun i => PSUσ g (y i)) ≠ 0 ∧ (fun i => PSUσ g (y i)) ⬝ᵥ x' = 0) ∨
      (Matrix.vecMulVec x' (fun i => PSUσ g (y i)) = 0 ∧ x ≠ 0 ∧
        (fun i => PSUσ g (y' i)) ≠ 0 ∧ (fun i => PSUσ g (y' i)) ⬝ᵥ x = 0) ∨
      (∃ lam : PSUF g, lam ≠ 0 ∧
        Matrix.vecMulVec x (fun i => PSUσ g (y' i)) =
          lam • Matrix.vecMulVec x' (fun i => PSUσ g (y i)) ∧
        Function.Surjective (fun c => c * lam - PSUσ g c) ∧
        x' ≠ 0 ∧ (fun i => PSUσ g (y i)) ≠ 0 ∧
        (fun i => PSUσ g (y i)) ⬝ᵥ x' = 0)) :
    ∃ (a φ : Fin (k + 1) → PSUF g), a ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ a = 0 ∧
      Subgroup.closure {b : GL (Fin (k + 1)) (PSUF g) | ∃ c : PSUF g,
        (b : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) =
          1 + c • Matrix.vecMulVec x (fun i => PSUσ g (y' i)) -
            PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (y i))} =
        matTransvGroup a φ := by
  rcases hscal with ⟨hA, hx', hy, hiso⟩ | ⟨hB, hx, hy', hiso'⟩ |
    ⟨lam, hlam, hAB, hsurj, hx', hy, hiso⟩
  · exact bmDPU_pair_closure_matTransv_zero_left hA hx' hy hiso
  · exact bmDPU_pair_closure_matTransv_zero_right hB hx hy' hiso'
  · exact bmDPU_pair_closure_matTransv_prop
      ⟨lam, hlam, hAB, hsurj⟩ hx' hy hiso

private lemma bmDPU_pair_relations_scalar {n g k : ℕ}
    {S : Set (GL (Fin n) (PSUF g))} {e : Matrix (Fin n) (Fin n) (PSUF g)}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (hM : PSUDualPairModel n g S e P Q R W hD)
    {v₀ w₀ : Fin n → PSUF g} {x y x' y' : Fin (k + 1) → PSUF g}
    (hv0 : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hw0 : Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hvw : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hv : v₀ = Matrix.mulVec P x + Matrix.mulVec Q y)
    (hw : w₀ = Matrix.mulVec P x' + Matrix.mulVec Q y')
    (hle : unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      (dualPairEmbSU hD).range.map (Unitary.SU (PSUσ g) n).subtype) (c : PSUF g) :
    c • Matrix.vecMulVec y (fun i => PSUσ g (y' i)) =
      PSUσ g c • Matrix.vecMulVec y' (fun i => PSUσ g (y i)) ∧
    c • Matrix.vecMulVec x (fun i => PSUσ g (x' i)) =
      PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (x i)) := by
  classical
  let A : Fin n → PSUF g := Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n)
  let B : Fin n → PSUF g := Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n)
  have hAv : A ⬝ᵥ v₀ = 0 := by
    show Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0
    exact (bmDPU_form_swap v₀ w₀).trans (by rw [hvw, map_zero])
  have hAw : A ⬝ᵥ w₀ = 0 := hw0
  have hBv : B ⬝ᵥ v₀ = 0 := hv0
  have hBw : B ⬝ᵥ w₀ = 0 := hvw
  let Nc : Matrix (Fin n) (Fin n) (PSUF g) := bmDPU_pair_N v₀ w₀ c
  have hNc2 : Nc * Nc = 0 := bmDPU_pair_N_nilpotent v₀ w₀ c hv0 hw0 hvw
  have h1 : (1 + Nc) * (1 - Nc) = 1 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hNc2]
    abel
  have h2 : (1 - Nc) * (1 + Nc) = 1 := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hNc2]
    abel
  let gU : GL (Fin n) (PSUF g) := ⟨1 + Nc, 1 - Nc, h1, h2⟩
  obtain ⟨gg, hgmem, hgval⟩ := bmDPU_pair_N_gen_mem v₀ w₀ c hv0 hw0 hvw
  have hgu : gU = gg := Units.ext (by
    rw [show (gU : Matrix (Fin n) (Fin n) (PSUF g)) = 1 + bmDPU_pair_N v₀ w₀ c from rfl,
      hgval])
  have hgmem' : gU ∈ unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ := by
    rw [hgu]; exact hgmem
  obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp (hle hgmem')
  have hGG : ⁅glBlockCentralizer (PSUj n g) S
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e),
      glBlockCentralizer (PSUj n g) S
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e)⁆ ≤
      glBlockCentralizer (PSUj n g) S
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e) := by
    refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_)
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have huG : u ∈ glBlockCentralizer (PSUj n g) S
      (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e) := by
    apply hGG
    rw [hM.derived]
    exact hu
  obtain ⟨a, haσ, hueq2⟩ := (hM.blockGroup u).mp huG
  have hg_eq : (gU : Matrix (Fin n) (Fin n) (PSUF g)) =
      dpEmb P Q R W (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g))
        (tcConjTr (PSUσ g) (((a⁻¹ : GL (Fin (k + 1)) (PSUF g))) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g))) := by
    have hGL : gU = dualPairEmbGL hD a := hueq.symm.trans hueq2
    rw [hGL, coe_dualPairEmbGL]
  have hgP : (gU : Matrix (Fin n) (Fin n) (PSUF g)) * P =
      P * (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) := by
    rw [hg_eq, bmDPU_dpEmb_mul_P hD (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) _]
  have hPRv : Matrix.mulVec (1 - P * R) v₀ = Matrix.mulVec Q y := by
    rw [hv]; exact bmDPU_one_sub_mulVec_decomp hD x y
  have hPRw : Matrix.mulVec (1 - P * R) w₀ = Matrix.mulVec Q y' := by
    rw [hw]; exact bmDPU_one_sub_mulVec_decomp hD x' y'
  have hAP : Matrix.vecMul A P = fun i => PSUσ g (y' i) := by
    show Matrix.vecMul (Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n)) P = _
    rw [hw]; exact bmDPU_vecMul_decomp_mul_P hD x' y'
  have hBP : Matrix.vecMul B P = fun i => PSUσ g (y i) := by
    show Matrix.vecMul (Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n)) P = _
    rw [hv]; exact bmDPU_vecMul_decomp_mul_P hD x y
  have hP0 : (1 - P * R) * P = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hD.rp, Matrix.mul_one, sub_self]
  have hNc_eq : Nc = c • Matrix.vecMulVec v₀ A - PSUσ g c • Matrix.vecMulVec w₀ B := rfl
  have hMv : (1 - P * R) * Nc = c • Matrix.vecMulVec (Matrix.mulVec Q y) A -
      PSUσ g c • Matrix.vecMulVec (Matrix.mulVec Q y') B := by
    rw [hNc_eq, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_vecMulVec,
      Matrix.mul_vecMulVec, hPRv, hPRw]
  have hexpP : (1 - P * R) * ((gU : Matrix (Fin n) (Fin n) (PSUF g)) * P) =
      Q * (c • Matrix.vecMulVec y (fun i => PSUσ g (y' i)) -
           PSUσ g c • Matrix.vecMulVec y' (fun i => PSUσ g (y i))) := by
    rw [show (gU : Matrix (Fin n) (Fin n) (PSUF g)) = 1 + Nc from rfl, ← Matrix.mul_assoc,
      Matrix.mul_add, Matrix.mul_one, hMv, Matrix.add_mul, hP0, zero_add, Matrix.sub_mul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, hAP, hBP,
      ← Matrix.mul_vecMulVec, ← Matrix.mul_vecMulVec, ← Matrix.mul_smul, ← Matrix.mul_smul,
      ← Matrix.mul_sub]
  have hzeroP : (1 - P * R) * ((gU : Matrix (Fin n) (Fin n) (PSUF g)) * P) = 0 := by
    rw [hgP, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hD.rp,
      Matrix.mul_one, sub_self, Matrix.zero_mul]
  have hQinj : ∀ D : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g), Q * D = 0 → D = 0 := by
    intro D hDq
    have h := congrArg (fun Z : Matrix (Fin n) (Fin (k + 1)) (PSUF g) => W * Z) hDq
    rw [Matrix.mul_zero, ← Matrix.mul_assoc, hD.wq, Matrix.one_mul] at h
    exact h
  have hPinj : ∀ D : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g), P * D = 0 → D = 0 := by
    intro D hDp
    have h := congrArg (fun Z : Matrix (Fin n) (Fin (k + 1)) (PSUF g) => R * Z) hDp
    rw [Matrix.mul_zero, ← Matrix.mul_assoc, hD.rp, Matrix.one_mul] at h
    exact h
  have hrel1 : c • Matrix.vecMulVec y (fun i => PSUσ g (y' i)) =
      PSUσ g c • Matrix.vecMulVec y' (fun i => PSUσ g (y i)) :=
    sub_eq_zero.mp (hQinj _ (by rw [← hexpP]; exact hzeroP))
  have hWQv : Matrix.mulVec (1 - Q * W) v₀ = Matrix.mulVec P x := by
    rw [hv]; exact bmDPU_one_sub_mulVec_decomp_W hD x y
  have hWQw : Matrix.mulVec (1 - Q * W) w₀ = Matrix.mulVec P x' := by
    rw [hw]; exact bmDPU_one_sub_mulVec_decomp_W hD x' y'
  have hAQ : Matrix.vecMul A Q = fun i => PSUσ g (x' i) := by
    show Matrix.vecMul (Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n)) Q = _
    rw [hw]; exact bmDPU_vecMul_decomp_mul_Q hD x' y'
  have hBQ : Matrix.vecMul B Q = fun i => PSUσ g (x i) := by
    show Matrix.vecMul (Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n)) Q = _
    rw [hv]; exact bmDPU_vecMul_decomp_mul_Q hD x y
  have hQ0 : (1 - Q * W) * Q = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hD.wq, Matrix.mul_one, sub_self]
  have hMvQ : (1 - Q * W) * Nc = c • Matrix.vecMulVec (Matrix.mulVec P x) A -
      PSUσ g c • Matrix.vecMulVec (Matrix.mulVec P x') B := by
    rw [hNc_eq, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_vecMulVec,
      Matrix.mul_vecMulVec, hWQv, hWQw]
  have hexpQ : (1 - Q * W) * ((gU : Matrix (Fin n) (Fin n) (PSUF g)) * Q) =
      P * (c • Matrix.vecMulVec x (fun i => PSUσ g (x' i)) -
           PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (x i))) := by
    rw [show (gU : Matrix (Fin n) (Fin n) (PSUF g)) = 1 + Nc from rfl, ← Matrix.mul_assoc,
      Matrix.mul_add, Matrix.mul_one, hMvQ, Matrix.add_mul, hQ0, zero_add, Matrix.sub_mul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, hAQ, hBQ,
      ← Matrix.mul_vecMulVec, ← Matrix.mul_vecMulVec, ← Matrix.mul_smul, ← Matrix.mul_smul,
      ← Matrix.mul_sub]
  have hgQ : (gU : Matrix (Fin n) (Fin n) (PSUF g)) * Q =
      Q * (tcConjTr (PSUσ g) (((a⁻¹ : GL (Fin (k + 1)) (PSUF g))) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g))) := by
    rw [hg_eq, bmDPU_dpEmb_mul_Q hD (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)) _]
  have hzeroQ : (1 - Q * W) * ((gU : Matrix (Fin n) (Fin n) (PSUF g)) * Q) = 0 := by
    rw [hgQ, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hD.wq,
      Matrix.mul_one, sub_self, Matrix.zero_mul]
  have hrel2 : c • Matrix.vecMulVec x (fun i => PSUσ g (x' i)) =
      PSUσ g c • Matrix.vecMulVec x' (fun i => PSUσ g (x i)) :=
    sub_eq_zero.mp (hPinj _ (by rw [← hexpQ]; exact hzeroQ))
  exact ⟨hrel1, hrel2⟩

private lemma bmDPU_pair_relations_zero {n g k : ℕ}
    {S : Set (GL (Fin n) (PSUF g))} {e : Matrix (Fin n) (Fin n) (PSUF g)}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (hM : PSUDualPairModel n g S e P Q R W hD)
    {v₀ w₀ : Fin n → PSUF g} {x y x' y' : Fin (k + 1) → PSUF g}
    (hv0 : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hw0 : Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hvw : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hv : v₀ = Matrix.mulVec P x + Matrix.mulVec Q y)
    (hw : w₀ = Matrix.mulVec P x' + Matrix.mulVec Q y')
    (hle : unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      (dualPairEmbSU hD).range.map (Unitary.SU (PSUσ g) n).subtype) :
    Matrix.vecMulVec y (fun i => PSUσ g (y' i)) = 0 ∧
    Matrix.vecMulVec x (fun i => PSUσ g (x' i)) = 0 := by
  obtain ⟨h1y, h1x⟩ := bmDPU_pair_relations_scalar hD hM hv0 hw0 hvw hv hw hle 1
  simp only [one_smul, map_one] at h1y h1x
  obtain ⟨ω, hω⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_ne
    (K := PSUF g) (p := 2) (f := g + 1) (card_PSUF g)
  obtain ⟨hωy, hωx⟩ := bmDPU_pair_relations_scalar hD hM hv0 hw0 hvw hv hw hle ω
  have hωne : ω - PSUσ g ω ≠ 0 := sub_ne_zero.mpr hω.symm
  have hy : Matrix.vecMulVec y (fun i => PSUσ g (y' i)) = 0 := by
    have h : (ω - PSUσ g ω) • Matrix.vecMulVec y (fun i => PSUσ g (y' i)) = 0 := by
      rw [sub_smul, hωy, ← h1y, sub_self]
    exact (smul_eq_zero.mp h).resolve_left hωne
  have hx : Matrix.vecMulVec x (fun i => PSUσ g (x' i)) = 0 := by
    have h : (ω - PSUσ g ω) • Matrix.vecMulVec x (fun i => PSUσ g (x' i)) = 0 := by
      rw [sub_smul, hωx, ← h1x, sub_self]
    exact (smul_eq_zero.mp h).resolve_left hωne
  exact ⟨hy, hx⟩

private lemma bmDPU_pair_pairing_coords {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    {v₀ w₀ : Fin n → PSUF g} {x y x' y' : Fin (k + 1) → PSUF g}
    (hv : v₀ = Matrix.mulVec P x + Matrix.mulVec Q y)
    (hw : w₀ = Matrix.mulVec P x' + Matrix.mulVec Q y') :
    Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ =
      (fun i => PSUσ g (y i)) ⬝ᵥ x' + (fun i => PSUσ g (x i)) ⬝ᵥ y' := by
  rw [hv, hw, dotProduct_add, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
    bmDPU_vecMul_decomp_mul_P hD x y, bmDPU_vecMul_decomp_mul_Q hD x y]

private lemma bmDPU_pair_transv_scalars_strong {n g k : ℕ}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {v₀ w₀ : Fin n → PSUF g} {x y x' y' : Fin (k + 1) → PSUF g}
    (hli : LinearIndependent (PSUF g) ![v₀, w₀])
    (hvw : (fun i => PSUσ g (y i)) ⬝ᵥ x' + (fun i => PSUσ g (x i)) ⬝ᵥ y' = 0)
    (hv : v₀ = Matrix.mulVec P x + Matrix.mulVec Q y)
    (hw : w₀ = Matrix.mulVec P x' + Matrix.mulVec Q y')
    (hyy' : Matrix.vecMulVec y (fun i => PSUσ g (y' i)) = 0)
    (hxx' : Matrix.vecMulVec x (fun i => PSUσ g (x' i)) = 0) :
    (Matrix.vecMulVec x (fun i => PSUσ g (y' i)) = 0 ∧ x' ≠ 0 ∧
        (fun i => PSUσ g (y i)) ≠ 0 ∧ (fun i => PSUσ g (y i)) ⬝ᵥ x' = 0) ∨
      (Matrix.vecMulVec x' (fun i => PSUσ g (y i)) = 0 ∧ x ≠ 0 ∧
        (fun i => PSUσ g (y' i)) ≠ 0 ∧ (fun i => PSUσ g (y' i)) ⬝ᵥ x = 0) ∨
      (∃ lam : PSUF g, lam ≠ 0 ∧
        Matrix.vecMulVec x (fun i => PSUσ g (y' i)) =
          lam • Matrix.vecMulVec x' (fun i => PSUσ g (y i)) ∧
        Function.Surjective (fun c => c * lam - PSUσ g c) ∧
        x' ≠ 0 ∧ (fun i => PSUσ g (y i)) ≠ 0 ∧
        (fun i => PSUσ g (y i)) ⬝ᵥ x' = 0) := by
  have hv0ne : v₀ ≠ 0 := by simpa using hli.ne_zero 0
  have hw0ne : w₀ ≠ 0 := by simpa using hli.ne_zero 1
  have hσinj : Function.Injective (PSUσ g) := (PSUσ g).injective
  have hσvec : ∀ y' : Fin (k + 1) → PSUF g,
      (fun i => PSUσ g (y' i)) = 0 → y' = 0 := by
    intro y' h
    funext i
    exact hσinj (by simpa using congrFun h i)
  have hσvec_ne : ∀ y' : Fin (k + 1) → PSUF g,
      y' ≠ 0 → (fun i => PSUσ g (y' i)) ≠ 0 := by
    intro y' hy' h
    exact hy' (hσvec y' h)
  by_cases hx0 : x = 0
  · have hy0 : y ≠ 0 := by
      intro hy
      apply hv0ne
      rw [hv, hx0, hy, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
    have hσy'0 : (fun i => PSUσ g (y' i)) = 0 := by
      rcases (Matrix.vecMulVec_eq_zero.mp hyy') with hy | hy'
      · exact absurd hy hy0
      · exact hy'
    have hy'0 : y' = 0 := hσvec y' hσy'0
    have hx'ne : x' ≠ 0 := by
      intro hx'
      apply hw0ne
      rw [hw, hx', hy'0, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
    have hσy_ne : (fun i => PSUσ g (y i)) ≠ 0 := hσvec_ne y hy0
    have hvec : Matrix.vecMulVec x (fun i => PSUσ g (y' i)) = 0 := by
      rw [hx0]; exact Matrix.zero_vecMulVec _
    have hdot : (fun i => PSUσ g (y i)) ⬝ᵥ x' = 0 := by
      have hσx0 : (fun i => PSUσ g (x i)) = 0 := by funext i; simp [hx0]
      rw [hσx0, zero_dotProduct, add_zero] at hvw
      exact hvw
    exact Or.inl ⟨hvec, hx'ne, hσy_ne, hdot⟩
  · have hx'0 : (fun i => PSUσ g (x' i)) = 0 := by
      rcases (Matrix.vecMulVec_eq_zero.mp hxx') with h | h
      · exact absurd h hx0
      · exact h
    have hx'0' : x' = 0 := hσvec x' hx'0
    have hy0 : y = 0 := by
      rcases (Matrix.vecMulVec_eq_zero.mp hyy') with hy | hy'
      · exact hy
      · exfalso
        have hy'0 : y' = 0 := hσvec y' hy'
        apply hw0ne
        rw [hw, hx'0', hy'0, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
    have hy'ne : y' ≠ 0 := by
      intro hy'
      apply hw0ne
      rw [hw, hx'0', hy', Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
    have hσy'ne : (fun i => PSUσ g (y' i)) ≠ 0 := hσvec_ne y' hy'ne
    have hvec : Matrix.vecMulVec x' (fun i => PSUσ g (y i)) = 0 := by
      rw [hx'0']; exact Matrix.zero_vecMulVec _
    have hdot : (fun i => PSUσ g (y' i)) ⬝ᵥ x = 0 := by
      have h1 : (fun i => PSUσ g (x i)) ⬝ᵥ y' = 0 := by
        rw [hx'0', dotProduct_zero, zero_add] at hvw
        exact hvw
      have h2 : x ⬝ᵥ (fun i => PSUσ g (y' i)) = 0 := by
        have hmap := RingHom.map_dotProduct (PSUσ g).toRingHom
          (fun i => PSUσ g (x i)) y'
        rw [h1, map_zero] at hmap
        have hcomp : ((PSUσ g).toRingHom ∘ (fun i => PSUσ g (x i))) = x := by
          funext i; exact PSUσ_involutive g (x i)
        rw [hcomp] at hmap
        exact hmap.symm
      rwa [dotProduct_comm] at h2
    exact Or.inr (Or.inl ⟨hvec, hx0, hσy'ne, hdot⟩)

private lemma bmDPU_pair_comap_transv {n g k : ℕ}
    {S : Set (GL (Fin n) (PSUF g))} {e : Matrix (Fin n) (Fin n) (PSUF g)}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (hM : PSUDualPairModel n g S e P Q R W hD)
    {v₀ w₀ : Fin n → PSUF g} {x y x' y' : Fin (k + 1) → PSUF g}
    (hli : LinearIndependent (PSUF g) ![v₀, w₀])
    (hv0 : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hw0 : Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hvw : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hv : v₀ = Matrix.mulVec P x + Matrix.mulVec Q y)
    (hw : w₀ = Matrix.mulVec P x' + Matrix.mulVec Q y')
    (hle : unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      (dualPairEmbSU hD).range.map (Unitary.SU (PSUσ g) n).subtype) :
    ∃ (a φ : Fin (k + 1) → PSUF g), a ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ a = 0 ∧
      (unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀).comap
        (dualPairEmbGL hD) = matTransvGroup a φ := by
  obtain ⟨hyy', hxx'⟩ := bmDPU_pair_relations_zero hD hM hv0 hw0 hvw hv hw hle
  have hvw' := (bmDPU_pair_pairing_coords hD hv hw).symm.trans hvw
  obtain ⟨a, φ, ha, hφ, hφa, hK⟩ :=
    bmDPU_pair_closure_matTransv
      (bmDPU_pair_transv_scalars_strong hli hvw' hv hw hyy' hxx')
  refine ⟨a, φ, ha, hφ, hφa, ?_⟩
  rw [bmDPU_pair_comap_eq_closure hD hv0 hw0 hvw hv hw hle, hK]

private lemma bmDPU_pair_transv {n g k : ℕ}
    {S : Set (GL (Fin n) (PSUF g))} {e : Matrix (Fin n) (Fin n) (PSUF g)}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (hM : PSUDualPairModel n g S e P Q R W hD)
    {v₀ w₀ : Fin n → PSUF g} {x y x' y' : Fin (k + 1) → PSUF g}
    (hli : LinearIndependent (PSUF g) ![v₀, w₀])
    (hv0 : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hw0 : Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hvw : Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hv : v₀ = Matrix.mulVec P x + Matrix.mulVec Q y)
    (hw : w₀ = Matrix.mulVec P x' + Matrix.mulVec Q y')
    (hle : unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      (dualPairEmbSU hD).range.map (Unitary.SU (PSUσ g) n).subtype) :
    ∃ (a φ : Fin (k + 1) → PSUF g), a ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ a = 0 ∧
      (matTransvGroup a φ).map (dualPairEmbGL hD) =
        unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ := by
  obtain ⟨a, φ, ha, hφ, hφa, hK⟩ :=
    bmDPU_pair_comap_transv hD hM hli hv0 hw0 hvw hv hw hle
  refine ⟨a, φ, ha, hφ, hφa, ?_⟩
  have hleq := bmDPU_pair_range_le hD hle
  have hmap : ((unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀).comap
      (dualPairEmbGL hD)).map (dualPairEmbGL hD) =
      unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ := by
    exact Subgroup.map_comap_eq_self hleq
  rw [hK] at hmap
  exact hmap

private lemma bmDPU_transv_root {n g k : ℕ} (hk : 1 ≤ k)
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    {v₀ w₀ : Fin n → PSUF g} {a φ : Fin (k + 1) → PSUF g}
    (ha : a ≠ 0) (hφ : φ ≠ 0) (hφa : φ ⬝ᵥ a = 0)
    (heq : (matTransvGroup a φ).map (dualPairEmbGL hD) =
      unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀) :
    ∃ (β : Fin k → ℤ) (u : Matrix.SpecialLinearGroup (Fin (k + 1)) (PSUF g)),
      β ∈ (SpecialLinear.rootDatum k (PSUF g)).roots ∧
      GGLongRoot (SpecialLinear.rootDatum k (PSUF g)) β ∧
      ((((SpecialLinear.rootDatum k (PSUF g)).rootGroup β).map
          (MulAut.conj u).toMonoidHom).map (dualPairEmbSU hD)).map
        (Unitary.SU (PSUσ g) n).subtype =
        unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ := by
  obtain ⟨i0, hi0⟩ : ∃ i0, a i0 ≠ 0 := Function.ne_iff.mp ha
  have hex : ∃ j, j ≠ i0 ∧ φ j ≠ 0 := by
    by_contra h
    push Not at h
    have hφi0 : φ i0 ≠ 0 := by
      by_contra h0
      apply hφ
      funext j
      by_cases hj : j = i0
      · subst hj; exact h0
      · exact h j hj
    have hdot : φ ⬝ᵥ a = φ i0 * a i0 := by
      rw [dotProduct]
      exact Finset.sum_eq_single i0
        (fun j _ hj => by rw [h j hj, zero_mul])
        (fun hi => absurd (Finset.mem_univ i0) hi)
    rw [hdot] at hφa
    exact mul_ne_zero hφi0 hi0 hφa
  obtain ⟨j, hji, hφj⟩ := hex
  let v' : Fin (k + 1) → PSUF g := Pi.single j (φ j)⁻¹
  let φ' : Fin (k + 1) → PSUF g := Pi.single i0 (a i0)⁻¹
  have hφv' : φ ⬝ᵥ v' = 1 := by
    rw [dotProduct]
    have h := Finset.sum_eq_single (s := Finset.univ) (f := fun i => φ i * v' i) j
      (fun i _ hi => by rw [show v' i = 0 from Pi.single_eq_of_ne hi _, mul_zero])
      (fun hj => absurd (Finset.mem_univ j) hj)
    rw [h]
    simp only [v', Pi.single_eq_same, mul_inv_cancel₀ hφj]
  have hφ'a : φ' ⬝ᵥ a = 1 := by
    rw [dotProduct]
    have h := Finset.sum_eq_single (s := Finset.univ) (f := fun i => φ' i * a i) i0
      (fun i _ hi => by rw [show φ' i = 0 from Pi.single_eq_of_ne hi _, zero_mul])
      (fun hi => absurd (Finset.mem_univ i0) hi)
    rw [h]
    simp only [φ', Pi.single_eq_same, inv_mul_cancel₀ hi0]
  have hφ'v' : φ' ⬝ᵥ v' = 0 := by
    rw [dotProduct]
    have h := Finset.sum_eq_single (s := Finset.univ) (f := fun i => φ' i * v' i) i0
      (fun i _ hi => by rw [show φ' i = 0 from Pi.single_eq_of_ne hi _, zero_mul])
      (fun hi => absurd (Finset.mem_univ i0) hi)
    rw [h]
    simp only [φ', v', Pi.single_eq_same, Pi.single_eq_of_ne hji.symm, mul_zero]
  obtain ⟨β, hβ, hlong, u, hroot, _⟩ :=
    exists_conj_rootGroup_eq_matTransvGroup_PSL k (PSUF g) hk a φ v' φ'
      hφa hφ'v' hφv' hφ'a
  refine ⟨β, u, hβ, hlong, ?_⟩
  rw [bmDPU_map_SU_eq hD (((SpecialLinear.rootDatum k (PSUF g)).rootGroup β).map
      (MulAut.conj u).toMonoidHom), hroot, heq]

private theorem bmDPU_closure {n g k : ℕ} (hk : 1 ≤ k)
    {S : Set (GL (Fin n) (PSUF g))} {e : Matrix (Fin n) (Fin n) (PSUF g)}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (hM : PSUDualPairModel n g S e P Q R W hD) :
    ∀ v₀ w₀ : Fin n → PSUF g, v₀ ≠ 0 → w₀ ≠ 0 → LinearIndependent (PSUF g) ![v₀, w₀] →
      Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0 →
      Matrix.vecMul (fun i => PSUσ g (w₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0 →
      Matrix.vecMul (fun i => PSUσ g (v₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0 →
      unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ ≤
        (dualPairEmbSU hD).range.map (Unitary.SU (PSUσ g) n).subtype →
      ∃ (β : Fin k → ℤ) (u : Matrix.SpecialLinearGroup (Fin (k + 1)) (PSUF g)),
        β ∈ (SpecialLinear.rootDatum k (PSUF g)).roots ∧
        GGLongRoot (SpecialLinear.rootDatum k (PSUF g)) β ∧
        ((((SpecialLinear.rootDatum k (PSUF g)).rootGroup β).map
            (MulAut.conj u).toMonoidHom).map (dualPairEmbSU hD)).map
          (Unitary.SU (PSUσ g) n).subtype =
          unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) v₀ w₀ := by
  intro v₀ w₀ hv hw hli hv0 hw0 hvw hle
  obtain ⟨x, y, x', y', hvdec, hwdec⟩ := bmDPU_pair_decomp hD hM hv0 hw0 hvw hli hle
  obtain ⟨hrel1, hrel2⟩ := bmDPU_pair_relations hD hM hv0 hw0 hvw hvdec hwdec hle
  obtain ⟨a, φ, ha, hφ, hφa, heq⟩ :=
    bmDPU_pair_transv hD hM hli hv0 hw0 hvw hvdec hwdec hle
  exact bmDPU_transv_root hk hD ha hφ hφa heq

private lemma bmDPU_rank {n g k : ℕ}
    {S : Set (GL (Fin n) (PSUF g))} {e : Matrix (Fin n) (Fin n) (PSUF g)}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (hM : PSUDualPairModel n g S e P Q R W hD) :
    k + 1 = Module.finrank (PSUF g) (LinearMap.range (Matrix.toLin' e)) := by
  have hRP : (Matrix.toLin' R).comp (Matrix.toLin' P) = LinearMap.id := by
    rw [← Matrix.toLin'_mul, hD.rp, Matrix.toLin'_one]
  have hP_inj : Function.Injective (Matrix.toLin' P) := by
    intro x y hxy
    have h := congrArg (Matrix.toLin' R) hxy
    have h2 : ((Matrix.toLin' R).comp (Matrix.toLin' P)) x =
        ((Matrix.toLin' R).comp (Matrix.toLin' P)) y := by
      simpa only [LinearMap.comp_apply] using h
    simpa only [hRP, LinearMap.id_apply] using h2
  have hrange : LinearMap.range (Matrix.toLin' e) = LinearMap.range (Matrix.toLin' P) := by
    apply le_antisymm
    · rw [hM.e_eq, Matrix.toLin'_mul]
      exact LinearMap.range_comp_le_range _ _
    · have hcomp : (Matrix.toLin' e).comp (Matrix.toLin' P) = Matrix.toLin' P := by
        calc (Matrix.toLin' e).comp (Matrix.toLin' P)
            = (Matrix.toLin' (P * R)).comp (Matrix.toLin' P) := by rw [hM.e_eq]
          _ = ((Matrix.toLin' P).comp (Matrix.toLin' R)).comp (Matrix.toLin' P) := by
                rw [Matrix.toLin'_mul]
          _ = (Matrix.toLin' P).comp ((Matrix.toLin' R).comp (Matrix.toLin' P)) := by
                rw [LinearMap.comp_assoc]
          _ = (Matrix.toLin' P).comp LinearMap.id := by rw [hRP]
          _ = Matrix.toLin' P := by rw [LinearMap.comp_id]
      intro y hy
      obtain ⟨x, rfl⟩ := hy
      exact ⟨Matrix.toLin' P x, by rw [← LinearMap.comp_apply, hcomp]⟩
  rw [hrange, LinearMap.finrank_range_of_inj hP_inj, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

private lemma bmDPU_equivariance {n g k : ℕ}
    {S : Set (GL (Fin n) (PSUF g))} {e : Matrix (Fin n) (Fin n) (PSUF g)}
    {P Q : Matrix (Fin n) (Fin (k + 1)) (PSUF g)}
    {R W : Matrix (Fin (k + 1)) (Fin n) (PSUF g)}
    (hD : PSUDualData g n (k + 1) P Q R W)
    (hM : PSUDualPairModel n g S e P Q R W hD)
    (γ : GL (Fin n) (PSUF g))
    (hγ : Unitary.conjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * Unitary.antidiag n *
      (γ : Matrix (Fin n) (Fin n) (PSUF g)) = Unitary.antidiag n)
    (hcomm : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * e =
      e * (γ : Matrix (Fin n) (Fin n) (PSUF g))) :
    ∃ a : GL (Fin (k + 1)) (PSUF g),
      ∀ x : Matrix.SpecialLinearGroup (Fin (k + 1)) (PSUF g),
        ∃ x' : Matrix.SpecialLinearGroup (Fin (k + 1)) (PSUF g),
          Matrix.SpecialLinearGroup.toGL x' = a * Matrix.SpecialLinearGroup.toGL x * a⁻¹ ∧
          γ * dualPairEmbGL hD (Matrix.SpecialLinearGroup.toGL x) * γ⁻¹ =
            dualPairEmbGL hD (Matrix.SpecialLinearGroup.toGL x') := by
  have hγP : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (P * R) =
      P * R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) := by
    rw [← hM.e_eq]; exact hcomm
  obtain ⟨a, ha⟩ := dualPairEmbGL_conj_of_commute hD hγ hγP
  refine ⟨a, fun x => ?_⟩
  let M : Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g) :=
    ((a * Matrix.SpecialLinearGroup.toGL x * a⁻¹ : GL (Fin (k + 1)) (PSUF g)) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g))
  have hMdet : M.det = 1 := by
    show ((a * Matrix.SpecialLinearGroup.toGL x * a⁻¹ : GL (Fin (k + 1)) (PSUF g)) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) (PSUF g)).det = 1
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    have h : Matrix.GeneralLinearGroup.det
        (a * Matrix.SpecialLinearGroup.toGL x * a⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, Matrix.SpecialLinearGroup.coeToGL_det]
      group
    rw [h, Units.val_one]
  let x' : Matrix.SpecialLinearGroup (Fin (k + 1)) (PSUF g) := ⟨M, hMdet⟩
  have hx' : Matrix.SpecialLinearGroup.toGL x' =
      a * Matrix.SpecialLinearGroup.toGL x * a⁻¹ := Units.ext rfl
  exact ⟨x', hx', by rw [hx']; exact ha (Matrix.SpecialLinearGroup.toGL x)⟩

theorem exists_blockModel_dualPair_PSU_explicitModel
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hSU : ∀ s ∈ S, Unitary.conjTr
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
    (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hpair : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e ≠ e)
      (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2)
    {J' : Subgroup
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S (e + formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e),
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S
        (e + formAdj
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) e)⁆) :
    ∃ (k : ℕ)
      (ι : (ggU .PSL (k + 1) (2 * (g + 1))).K →*
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n))
      (β₀ : Fin (ggU .PSL (k + 1) (2 * (g + 1))).D.rank → ℤ), k + 1 = Module.finrank (GaloisField 2
          (2 * (g + 1))) (LinearMap.range (Matrix.toLin' e)) ∧
      (∀ γ : GL (Fin n) (GaloisField 2 (2 * (g + 1))),
        Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g
            + 1))
          (γ : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
          (γ : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n →
        (γ : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * e = e * (γ : Matrix (Fin n)
            (Fin n) (GaloisField 2 (2 * (g + 1)))) →
        ∃ a : GL (Fin (k + 1)) (GaloisField 2 (2 * (g + 1))), ∀ x : (ggU .PSL (k + 1) (2 * (g +
            1))).K,
          ∃ x' : (ggU .PSL (k + 1) (2 * (g + 1))).K,
            Matrix.SpecialLinearGroup.toGL x' = a * Matrix.SpecialLinearGroup.toGL x * a⁻¹ ∧
            γ * ((ι x : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
                (g + 1))) 2 (g + 1)) n)) : GL (Fin n) (GaloisField 2 (2 * (g + 1)))) =
              ((ι x' : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g
                  + 1))) 2 (g + 1)) n)) : GL (Fin n) (GaloisField 2 (2 * (g + 1)))) * γ) ∧
      GGLongRoot (ggU .PSL (k + 1) (2 * (g + 1))).D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center
        ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n) → y ∈
        Subgroup.center (ggU .PSL (k + 1) (2 * (g + 1))).K) ∧ ι.range = J' ∧
      4 ≤ n ∧ ∃ v₁ w₁ v₂ w₂ : Fin n → (GaloisField 2 (2 * (g + 1))), Matrix.vecMul
        (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        (v₁ i)) (Unitary.antidiag n) ⬝ᵥ w₂ = 1 ∧
        Matrix.vecMul
          (fun i =>
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (w₁ i))
          (Unitary.antidiag n) ⬝ᵥ v₂ = 1 ∧
        (Matrix.vecMul
          (fun i =>
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v₁ i))
          (Unitary.antidiag n) ⬝ᵥ v₁ = 0 ∧ Matrix.vecMul
          (fun i =>
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (w₁ i))
          (Unitary.antidiag n) ⬝ᵥ w₁ = 0 ∧
          Matrix.vecMul
            (fun i =>
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
            (v₂ i)) (Unitary.antidiag n) ⬝ᵥ v₂ = 0 ∧ Matrix.vecMul
            (fun i =>
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
            (w₂ i)) (Unitary.antidiag n) ⬝ᵥ w₂ = 0 ∧
          Matrix.vecMul
            (fun i =>
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
            (v₁ i)) (Unitary.antidiag n) ⬝ᵥ w₁ = 0 ∧ Matrix.vecMul
            (fun i =>
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
            (v₁ i)) (Unitary.antidiag n) ⬝ᵥ v₂ = 0 ∧
          Matrix.vecMul
            (fun i =>
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
            (w₁ i)) (Unitary.antidiag n) ⬝ᵥ w₂ = 0 ∧ Matrix.vecMul
            (fun i =>
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
            (v₂ i)) (Unitary.antidiag n) ⬝ᵥ w₂ = 0) ∧
        (((ggU .PSL (k + 1) (2 * (g + 1))).D.rootGroup β₀).map ι).map
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) = unitPairGroup
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) v₁ w₁ ∧
        (((ggU .PSL (k + 1) (2 * (g + 1))).D.rootGroup (-β₀)).map ι).map
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) = unitPairGroup
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) v₂ w₂ := by
  classical
  obtain ⟨k, P, Q, R, W, hD, hM, hk, hrange, h4⟩ :=
    bmDPU_fong n g S hSU hS he hpair hdeg hJe
  obtain ⟨β, u, hβ, hlong, hroot1, hroot2⟩ := bmDPU_root_config hk hD
  let ι : (ggU .PSL (k + 1) (2 * (g + 1))).K →* ↥(Unitary.SU (PSUσ g) n) :=
    (dualPairEmbSU hD).comp (MulAut.conj u).toMonoidHom
  refine ⟨k, ι, β, bmDPU_rank hD hM, ?_, hlong, ?_, ?_, h4, ?_⟩
  · intro γ hγ hcomm
    obtain ⟨a, ha⟩ := bmDPU_equivariance hD hM γ hγ hcomm
    refine ⟨(Matrix.SpecialLinearGroup.toGL u)⁻¹ * a * Matrix.SpecialLinearGroup.toGL u, ?_⟩
    intro x
    let y : Matrix.SpecialLinearGroup (Fin (k + 1)) (PSUF g) := x
    obtain ⟨x0, hx0, hγx0⟩ := ha (u * y * u⁻¹)
    refine ⟨u⁻¹ * x0 * u, ?_, ?_⟩
    · have hxu : Matrix.SpecialLinearGroup.toGL (u * y * u⁻¹) =
          Matrix.SpecialLinearGroup.toGL u * Matrix.SpecialLinearGroup.toGL y *
            (Matrix.SpecialLinearGroup.toGL u)⁻¹ := by
        simp only [map_mul, map_inv]
      rw [map_mul, map_mul, map_inv, hx0, hxu]
      simp only [y]
      group
    · have hux : u * (u⁻¹ * x0 * u) * u⁻¹ = x0 := by group
      change γ * ((dualPairEmbSU hD (u * y * u⁻¹) : ↥(Unitary.SU (PSUσ g) n)) :
          GL (Fin n) (PSUF g)) =
        ((dualPairEmbSU hD (u * (u⁻¹ * x0 * u) * u⁻¹) : ↥(Unitary.SU (PSUσ g) n)) :
          GL (Fin n) (PSUF g)) * γ
      rw [hux, coe_dualPairEmbSU, coe_dualPairEmbSU]
      calc γ * dualPairEmbGL hD (Matrix.SpecialLinearGroup.toGL (u * y * u⁻¹))
          = γ * dualPairEmbGL hD (Matrix.SpecialLinearGroup.toGL (u * y * u⁻¹)) * γ⁻¹ * γ := by
            group
        _ = dualPairEmbGL hD (Matrix.SpecialLinearGroup.toGL x0) * γ := by rw [hγx0]
  · intro y hy
    exact bmDPU_center hD hM u y hy
  · exact (bmDPU_range_conj hD u).trans hrange
  · obtain ⟨hp1, hp2, hpX⟩ := bmDPU_pairings hk hD
    refine ⟨bmDPU_v₁ P, bmDPU_w₁ Q, bmDPU_v₂ P, bmDPU_w₂ Q, hp1, hp2, hpX, ?_, ?_⟩
    · change ((((SpecialLinear.rootDatum k (PSUF g)).rootGroup β).map
          ((dualPairEmbSU hD).comp (MulAut.conj u).toMonoidHom)).map
          (Unitary.SU (PSUσ g) n).subtype) =
          unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) (bmDPU_v₁ P) (bmDPU_w₁ Q)
      exact hroot1
    · change ((((SpecialLinear.rootDatum k (PSUF g)).rootGroup (-β)).map
          ((dualPairEmbSU hD).comp (MulAut.conj u).toMonoidHom)).map
          (Unitary.SU (PSUσ g) n).subtype) =
          unitPairGroup (PSUσ g).toRingHom (Unitary.antidiag n) (bmDPU_v₂ P) (bmDPU_w₂ Q)
      exact hroot2

theorem exists_blockModelClosure_dualPair_PSU_explicitModel
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hSU : ∀ s ∈ S, Unitary.conjTr
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
    (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hpair : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e ≠ e)
      (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2)
    {J' : Subgroup
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S (e + formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e),
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S
        (e + formAdj
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) e)⁆) :
    ∃ (k : ℕ) (ι : (ggU .PSL (k + 1) (2 * (g + 1))).K →* ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)),
      k + 1 = Module.finrank (GaloisField 2 (2 * (g + 1))) (LinearMap.range (Matrix.toLin' e)) ∧
      (∀ y, ι y ∈ Subgroup.center ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n) → y ∈ Subgroup.center (ggU .PSL (k + 1) (2 *
              (g + 1))).K) ∧
      ι.range = J' ∧
      (∀ v₀ w₀ : Fin n → GaloisField 2 (2 * (g + 1)), v₀ ≠ 0 → w₀ ≠ 0 → LinearIndependent
          (GaloisField 2 (2 * (g + 1))) ![v₀, w₀] → Matrix.vecMul (fun i =>
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v₀
          i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0 → Matrix.vecMul (fun i =>
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (w₀
          i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0 → Matrix.vecMul (fun i =>
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v₀
          i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0 → unitPairGroup
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g +
          1)).toRingHom (Unitary.antidiag n) v₀ w₀ ≤ J'.map (Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
          n).subtype →
        ∃ (β : Fin (ggU .PSL (k + 1) (2 * (g + 1))).D.rank → ℤ) (u : (ggU .PSL (k + 1) (2 * (g +
            1))).K), β ∈ (ggU .PSL (k + 1) (2 * (g + 1))).D.roots ∧
            GGLongRoot (ggU .PSL (k + 1) (2 * (g + 1))).D β ∧
          ((((ggU .PSL (k + 1) (2 * (g + 1))).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
              ι).map (Unitary.SU
              (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
              n).subtype = unitPairGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2
              (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag n) v₀ w₀) := by
  classical
  obtain ⟨k, P, Q, R, W, hD, hM, hk, hrange, _⟩ :=
    bmDPU_fong n g S hSU hS he hpair hdeg hJe
  refine ⟨k, dualPairEmbSU hD, bmDPU_rank hD hM, ?_, hrange, ?_⟩
  · intro y hy
    exact hM.center y hy
  · intro v₀ w₀ hv hw hli hv0 hw0 hvw hle
    exact bmDPU_closure hk hD hM v₀ w₀ hv hw hli hv0 hw0 hvw
      (by simpa only [hrange] using hle)

end CFSG.StandardType.ClassicalPosition
