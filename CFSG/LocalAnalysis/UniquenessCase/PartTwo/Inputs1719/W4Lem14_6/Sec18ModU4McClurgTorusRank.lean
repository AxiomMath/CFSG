module

public import CFSG.HardMathSupport.U4FF.ClassSingle
import all CFSG.HardMathSupport.U4FF.ClassLocData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg

open CFSG.HardMathSupport.U4FF
open scoped MatrixGroups


theorem rank_Tmod_conj {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {k : Type} [Field k]
    [CharP k 2] [Algebra K k] (l : Lbl n) (t g : SU4 K n) :
    (Tmod K l k (t * g * t⁻¹) - 1).rank = (Tmod K l k g - 1).rank := by
  classical
  have hAC : Tmod K l k t * Tmod K l k t⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have h1 : Tmod K l k (t * g * t⁻¹) =
      Tmod K l k t * Tmod K l k g * Tmod K l k t⁻¹ := by
    rw [map_mul, map_mul]
  have h2 : Tmod K l k (t * g * t⁻¹) - 1 =
      Tmod K l k t * (Tmod K l k g - 1) * Tmod K l k t⁻¹ := by
    rw [h1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAC]
  rw [h2]
  exact CFSG.QuasithinUnique.Setup.X7b.rank_conj_eq _ _ _
    (by rw [← map_mul, inv_mul_cancel, map_one])

abbrev AmbI : Type := Fin (ambDim (fsOf true false true))
abbrev LocI : Type := Fin (locM true false true)

private def fst16 (x : AmbI) : Fin 4 :=
  (ambEq [FK.N, FK.S]).symm x ⟨0, by decide⟩
private def snd16 (x : AmbI) : Fin 4 :=
  (ambEq [FK.N, FK.S]).symm x ⟨1, by decide⟩

private theorem fst16_eq (x : AmbI) :
    fst16 x = ⟨(x : ℕ) % 4, Nat.mod_lt _ (by norm_num)⟩ := by
  fin_cases x <;> decide +kernel

private theorem snd16_eq (x : AmbI) :
    snd16 x = ⟨(x : ℕ) / 4, by
      have h : (x : ℕ) < ambDim (fsOf true false true) := x.isLt
      have hd : ambDim (fsOf true false true) = 16 := rfl
      omega⟩ := by
  fin_cases x <;> decide +kernel

private def maskArr : MCols :=
  #[16384, 8192, 4096, 2048, 1025, 512, 256, 128, 64, 33, 16, 8, 4, 2]

private def dvec {k : Type} [Field k] (w : k) : Fin 4 → k := ![w, w⁻¹, w⁻¹, w]
private def vv {k : Type} [Field k] (w : k) (x : AmbI) : k :=
  dvec w (fst16 x) * (dvec w (snd16 x))⁻¹

private def dExp : Fin 4 → ℤ := ![1, -1, -1, 1]
private def xExp (x : AmbI) : ℤ := dExp (fst16 x) - dExp (snd16 x)
private def cExp (c : LocI) : ℤ :=
  ([-2, -2, 0, 2, 0, 0, 2, 2, 0, 0, 2, 0, -2, -2] : List ℤ).getD (c : ℕ) 0
private def lam {k : Type} [Field k] (w : k) (c : LocI) : k := w ^ (cExp c)

private def BkMat {k : Type} [Field k] [CharP k 2] : Matrix AmbI LocI k :=
  Matrix.of fun x c => if (maskArr.getD (c : ℕ) 0).testBit (x : ℕ) then 1 else 0

private theorem Bk_eq {k : Type} [Field k] [CharP k 2] :
    (locSpec true false true (locValid true false true).1).Bk k = BkMat := by
  change ((locData true false true).bcols.toMat (ambDim (fsOf true false true))
    (locM true false true)).map (f2 k) = BkMat
  rw [show (locData true false true).bcols = maskArr from rfl]
  ext x c
  simp [BkMat, MCols.toMat, bitF, Matrix.of_apply]

private theorem vv_eq_zpow {k : Type} [Field k] (w : k) (hw0 : w ≠ 0) (x : AmbI) :
    vv w x = w ^ (xExp x) := by
  fin_cases x <;>
    simp [vv, dvec, xExp, dExp, fst16_eq, snd16_eq, zpow_neg_one, zpow_add₀ hw0,
      pow_two, mul_inv_cancel₀ hw0, inv_mul_cancel₀ hw0, ← mul_inv_rev]

private theorem amb_diag {k : Type} [Field k] [CharP k 2] (D : SL(4, k)) (w : k)
    (hD : (D : Matrix (Fin 4) (Fin 4) k) = Matrix.diagonal (dvec w)) :
    ambRepF k (fsOf true false true) D = Matrix.diagonal (fun x : AmbI => vv w x) := by
  conv_lhs => change ambRepF k [FK.N, FK.S] D
  rw [ambRepF_diag [FK.N, FK.S] D (dvec w) hD]
  congr 1
  funext x
  change (∏ f : Fin 2, diagFac (dvec w) ([FK.N, FK.S].get f)
    ((ambEq [FK.N, FK.S]).symm x f)) = vv w x
  rw [Fin.prod_univ_two]
  simp only [diagFac, vv, fst16, snd16, List.get_cons_zero, List.get_cons_succ, Fin.isValue]
  rfl

private theorem eigen {k : Type} [Field k] [CharP k 2] (D : SL(4, k)) (w : k)
    (hw0 : w ≠ 0)
    (hD : (D : Matrix (Fin 4) (Fin 4) k) = Matrix.diagonal (dvec w)) :
    ambRepF k (fsOf true false true) D * (BkMat (k := k)) =
      (BkMat (k := k)) * Matrix.diagonal (lam (k := k) w) := by
  rw [amb_diag D w hD]
  ext x c
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [BkMat, Matrix.of_apply]
  by_cases h : (maskArr.getD (c : ℕ) 0).testBit (x : ℕ) = true
  · simp only [if_pos h, mul_one, one_mul]
    rw [vv_eq_zpow w hw0 x]
    congr 1
    fin_cases x <;> fin_cases c <;>
      simp [xExp, cExp, dExp, fst16_eq, snd16_eq, maskArr] at h ⊢ <;>
      first | decide +kernel | contradiction
  · simp only [if_neg h, mul_zero, zero_mul]

theorem eight_le_rank_locR101_diag {k : Type} [Field k] [CharP k 2] (D : SL(4, k)) (w : k)
    (hw : w ^ 2 ≠ 1)
    (hD : (D : Matrix (Fin 4) (Fin 4) k) = Matrix.diagonal ![w, w⁻¹, w⁻¹, w]) :
    8 ≤ (locR true false true k D - 1).rank := by
  classical
  have hD' : (D : Matrix (Fin 4) (Fin 4) k) = Matrix.diagonal (dvec w) := hD
  have hdet : w * w⁻¹ * w⁻¹ * w = 1 := by
    have h := D.det_coe
    rw [hD', Matrix.det_diagonal, Fin.prod_univ_four] at h
    simpa [dvec] using h
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0] at hdet
    norm_num at hdet
  have hw2 : w * w ≠ 1 := by simpa [pow_two] using hw
  have hwneg : w ^ (-2 : ℤ) ≠ 1 := by
    rw [zpow_neg]
    exact fun h => hw2 (by simpa [zpow_natCast, pow_two] using inv_eq_one.mp h)
  set S := locSpec true false true (locValid true false true).1 with hS
  have hB : S.Bk k = (BkMat (k := k)) := Bk_eq (k := k)
  have hPmB : S.Pmk k * (BkMat (k := k)) = 1 := by
    rw [← hB]
    exact S.Pmk_Bk k
  have hloc : S.locMat k D = Matrix.diagonal (lam (k := k) w) := by
    calc S.locMat k D = S.Pmk k * (ambRepF k (fsOf true false true) D * S.Bk k) := rfl
      _ = S.Pmk k * (ambRepF k (fsOf true false true) D * (BkMat (k := k))) := by rw [hB]
      _ = S.Pmk k * ((BkMat (k := k)) * Matrix.diagonal (lam (k := k) w)) := by
            rw [eigen (k := k) D w hw0 hD']
      _ = (S.Pmk k * (BkMat (k := k))) * Matrix.diagonal (lam (k := k) w) := by
            rw [Matrix.mul_assoc]
      _ = Matrix.diagonal (lam (k := k) w) := by rw [hPmB, Matrix.one_mul]
  rw [show (locR true false true k) D = Matrix.diagonal (lam (k := k) w) from by
    rw [show (locR true false true k) D = S.locMat k D from rfl]
    exact hloc]
  have hsub : (Matrix.diagonal (lam (k := k) w) - 1 : Matrix LocI LocI k) =
      Matrix.diagonal (fun c => lam (k := k) w c - 1) := by
    rw [show (1 : Matrix LocI LocI k) = Matrix.diagonal (fun _ => 1) from
      (Matrix.diagonal_one (n := LocI) (α := k)).symm, Matrix.diagonal_sub]
  rw [hsub, Matrix.rank_diagonal, Fintype.card_subtype]
  let good : Finset LocI := Finset.univ.filter (fun c => (c : ℕ) ∈ [0, 1, 3, 6, 7, 10, 12, 13])
  have hgoodcard : good.card = 8 := by decide +kernel
  have hsubgood : good ⊆ Finset.univ.filter (fun c : LocI => lam (k := k) w c - 1 ≠ 0) := by
    intro c hc
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    fin_cases c <;> simp [lam, cExp, zpow_neg, zpow_natCast] at hc ⊢ <;>
      first
      | (simpa [sub_ne_zero, zpow_neg, zpow_natCast] using hwneg)
      | (simpa [sub_ne_zero, pow_two] using hw2)
      | contradiction
  have hle := Finset.card_le_card hsubgood
  rw [hgoodcard] at hle
  exact hle


private def e6 : Fin 6 → ℕ := ![0, 0, 2, 3, 0, 0]

private abbrev κ6 : Fin 2 → Type := fun _ => Fin 6

private def dvecK {K : Type} [Field K] (w : K) : Fin 4 → K := ![w, w⁻¹, w⁻¹, w]

private lemma compound2_diag0 {k : Type} [Field k] [CharP k 2] {w : k} (hw5 : w ^ 5 = 1) :
    compound2 (Matrix.diagonal (dvecK w)) =
      Matrix.diagonal (fun I : Fin 6 => w ^ e6 I) := by
  rw [compound2_diagonal]
  congr 1
  funext I
  have hw4 : w⁻¹ = w ^ 4 := inv_eq_of_mul_eq_one_right (by
    rw [← pow_succ']
    exact hw5)
  fin_cases I <;> simp [dvecK, e6, pair6, hw4]
  all_goals
    first
    | rfl
    | (rw [pow_two])
    | (rw [← pow_succ]; norm_num; rw [hw5])
    | (rw [← pow_succ']; norm_num; rw [hw5])
    | (rw [← pow_add]; norm_num; rw [pow_eq_pow_mod _ hw5]; try norm_num)

private lemma compound2_diag_sq {k : Type} [Field k] [CharP k 2] {w : k} (hw5 : w ^ 5 = 1) :
    compound2 (Matrix.diagonal (fun j => (dvecK w j) ^ 2)) =
      Matrix.diagonal (fun I : Fin 6 => (w ^ e6 I) ^ 2) := by
  rw [show (fun j => (dvecK w j) ^ 2) = fun j => dvecK w j * dvecK w j by
    funext j; rw [pow_two]]
  rw [← Matrix.diagonal_mul_diagonal, compound2_mul, compound2_diag0 hw5,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext I
  rw [pow_two]

private lemma twist0_eq {K : Type} [Field K] [Finite K] [CharP K 2] {k : Type} [Field k] [CharP k 2]
    [Algebra K k] {g : SU4 K 2} {w : K}
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal (dvecK w)) :
    ((twistHom 2 (frobTw K k 0) g : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) =
      Matrix.diagonal (dvecK (algebraMap K k w)) := by
  rw [twistHom_val, hg]
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp [Matrix.map_apply, frobTw_apply, dvecK, map_inv₀]
  · simp [Matrix.map_apply, frobTw_apply, dvecK, hij]

private lemma twist1_eq {K : Type} [Field K] [Finite K] [CharP K 2] {k : Type} [Field k] [CharP k 2]
    [Algebra K k] {g : SU4 K 2} {w : K}
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal (dvecK w)) :
    ((twistHom 2 (frobTw K k 1) g : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) =
      Matrix.diagonal (fun j => (dvecK (algebraMap K k w) j) ^ 2) := by
  rw [twistHom_val, hg]
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp [Matrix.map_apply, frobTw_apply, dvecK, map_inv₀, map_pow]
  · simp [Matrix.map_apply, frobTw_apply, dvecK, hij]

private lemma label_omega2_eq (l : Lbl 2)
    (hl : ∀ i, l.a i = false ∧ l.b i = true ∧ l.c i = false) :
    l = ⟨fun _ => false, fun _ => true, fun _ => false⟩ := by
  cases l with
  | mk a b c =>
    have ha : a = fun _ => false := funext fun i => (hl i).1
    have hb : b = fun _ => true := funext fun i => (hl i).2.1
    have hc : c = fun _ => false := funext fun i => (hl i).2.2
    subst ha hb hc
    rfl

private theorem tmod_rank_diag {K : Type} [Field K] [Finite K] [CharP K 2] {k : Type} [Field k]
    [CharP k 2] [Algebra K k] (l : Lbl 2)
    (hl : ∀ i, l.a i = false ∧ l.b i = true ∧ l.c i = false) (g : SU4 K 2) (w : K)
    (hw1 : w ≠ 1) (hw5 : w ^ 5 = 1)
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal (dvecK w)) :
    (Tmod K l k g - 1).rank =
      (Matrix.diagonal (fun x : (i : Fin 2) → Fin 6 =>
        (algebraMap K k w) ^ (e6 (x 0) + 2 * e6 (x 1))) - 1).rank := by
  classical
  obtain rfl := label_omega2_eq l hl
  let wk : k := algebraMap K k w
  have hw5k : wk ^ 5 = 1 := by
    rw [show wk = algebraMap K k w from rfl, ← map_pow, hw5, map_one]
  have hw1k : wk ≠ 1 := by
    intro h
    have h' : algebraMap K k w = algebraMap K k (1 : K) := by
      rw [map_one]
      simpa [wk] using h
    exact hw1 ((algebraMap K k).injective h')
  let z : (i : Fin 2) → Matrix (Fin 6) (Fin 6) k :=
    fun i => locRW k (twistHom 2 (frobTw K k i) g)
  let δ : Fin 2 → Fin 6 → k := fun i I => if i = 0 then wk ^ e6 I else wk ^ (2 * e6 I)
  change (kronDep κ6 z - 1).rank =
    (Matrix.diagonal (fun x : (i : Fin 2) → Fin 6 =>
      wk ^ (e6 (x 0) + 2 * e6 (x 1))) - 1).rank
  obtain ⟨B, hB⟩ := locR_W_iso (k := k)
  have hdiag : (fun i : Fin 2 => compound2 (((twistHom 2 (frobTw K k i) g : SL(4, k)) :
      Matrix (Fin 4) (Fin 4) k))) = fun i => Matrix.diagonal (δ i) := by
    funext i
    fin_cases i
    · show compound2 (((twistHom 2 (frobTw K k 0) g : SL(4, k)) : Matrix (Fin 4) (Fin 4) k)) =
        Matrix.diagonal (δ 0)
      rw [twist0_eq (k := k) hg, compound2_diag0 hw5k]
      congr 1
    · show compound2 (((twistHom 2 (frobTw K k 1) g : SL(4, k)) : Matrix (Fin 4) (Fin 4) k)) =
        Matrix.diagonal (δ 1)
      rw [twist1_eq (k := k) hg, compound2_diag_sq hw5k]
      congr 1
      funext I
      simp [δ, pow_two, pow_mul, mul_comm, mul_pow]
  have hBz : ∀ i, (B : Matrix (Fin 6) (Fin 6) k) * z i =
      Matrix.diagonal (δ i) * (B : Matrix (Fin 6) (Fin 6) k) := by
    intro i
    have h := hB (twistHom 2 (frobTw K k i) g)
    have hi := congrFun hdiag i
    rw [hi] at h
    simpa [z] using h
  let P : Matrix ((i : Fin 2) → Fin 6) ((i : Fin 2) → Fin 6) k :=
    kronDep κ6 (fun _ => (B : Matrix (Fin 6) (Fin 6) k))
  let Q : Matrix ((i : Fin 2) → Fin 6) ((i : Fin 2) → Fin 6) k :=
    kronDep κ6 (fun _ => ((B⁻¹ : GL (Fin 6) k) : Matrix (Fin 6) (Fin 6) k))
  have hPQ : P * Q = 1 := by
    rw [show P * Q = kronDep κ6 (fun _ =>
      (B : Matrix (Fin 6) (Fin 6) k) * ((B⁻¹ : GL (Fin 6) k) : Matrix (Fin 6) (Fin 6) k)) by
      rw [kronDep_mul]]
    simp [kronDep_one]
  have hQP : Q * P = 1 := by
    rw [show Q * P = kronDep κ6 (fun _ =>
      ((B⁻¹ : GL (Fin 6) k) : Matrix (Fin 6) (Fin 6) k) * (B : Matrix (Fin 6) (Fin 6) k)) by
      rw [kronDep_mul]]
    simp [kronDep_one]
  have hPz : P * kronDep κ6 z =
      kronDep κ6 (fun i => Matrix.diagonal (δ i)) * P := by
    rw [← kronDep_mul]
    rw [show (fun i => (B : Matrix (Fin 6) (Fin 6) k) * z i) =
        fun i => Matrix.diagonal (δ i) * (B : Matrix (Fin 6) (Fin 6) k) from funext hBz]
    rw [kronDep_mul]
  have hPzQ : P * (kronDep κ6 z - 1) * Q =
      kronDep κ6 (fun i => Matrix.diagonal (δ i)) - 1 := by
    calc P * (kronDep κ6 z - 1) * Q
        = P * kronDep κ6 z * Q - P * Q := by
            rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      _ = (kronDep κ6 (fun i => Matrix.diagonal (δ i)) * P) * Q - 1 := by
            rw [hPz, hPQ]
      _ = kronDep κ6 (fun i => Matrix.diagonal (δ i)) * (P * Q) - 1 := by
            rw [Matrix.mul_assoc]
      _ = kronDep κ6 (fun i => Matrix.diagonal (δ i)) - 1 := by
            rw [hPQ, Matrix.mul_one]
  have hrank : (kronDep κ6 z - 1).rank =
      (kronDep κ6 (fun i => Matrix.diagonal (δ i)) - 1).rank := by
    rw [← CFSG.QuasithinUnique.Setup.X7b.rank_conj_eq (M := kronDep κ6 z - 1)
      (P := P) (Q := Q) hQP, hPzQ]
  have hkron : kronDep κ6 (fun i => Matrix.diagonal (δ i)) =
      Matrix.diagonal (fun x : (i : Fin 2) → Fin 6 =>
        wk ^ (e6 (x 0) + 2 * e6 (x 1))) := by
    rw [kronDep_diagonal]
    congr 1
    funext x
    rw [Fin.prod_univ_two]
    simp [δ]
    rw [← pow_add]
  rw [hrank, hkron]

theorem seventeen_le_rank_Tmod_omega2_pair {K : Type} [Field K] [Finite K] [CharP K 2] {k : Type}
    [Field k] [CharP k 2] [Algebra K k] (l : Lbl 2)
    (hl : ∀ i, l.a i = false ∧ l.b i = true ∧ l.c i = false) (g : SU4 K 2) (w : K)
    (hw1 : w ≠ 1) (hw5 : w ^ 5 = 1)
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![w, w⁻¹, w⁻¹, w]) :
    17 ≤ (Tmod K l k g - 1).rank := by
  classical
  rw [tmod_rank_diag (k := k) l hl g w hw1 hw5 hg]
  let wk : k := algebraMap K k w
  have hw5k : wk ^ 5 = 1 := by
    rw [show wk = algebraMap K k w from rfl, ← map_pow, hw5, map_one]
  have hw1k : wk ≠ 1 := by
    intro h
    have h' : algebraMap K k w = algebraMap K k (1 : K) := by
      rw [map_one]
      simpa [wk] using h
    exact hw1 ((algebraMap K k).injective h')
  have hsub : (Matrix.diagonal (fun x : (i : Fin 2) → Fin 6 =>
      wk ^ (e6 (x 0) + 2 * e6 (x 1))) - 1 :
        Matrix ((i : Fin 2) → Fin 6) ((i : Fin 2) → Fin 6) k) =
      Matrix.diagonal (fun x => wk ^ (e6 (x 0) + 2 * e6 (x 1)) - 1) := by
    rw [show (1 : Matrix ((i : Fin 2) → Fin 6) ((i : Fin 2) → Fin 6) k) =
      Matrix.diagonal (fun _ => 1) from
      (Matrix.diagonal_one (n := (i : Fin 2) → Fin 6) (α := k)).symm, Matrix.diagonal_sub]
  rw [hsub, Matrix.rank_diagonal, Fintype.card_subtype]
  let good : Finset ((i : Fin 2) → Fin 6) :=
    Finset.univ.filter (fun x => (e6 (x 0) + 2 * e6 (x 1)) % 5 ≠ 0)
  have hgoodcard : good.card = 20 := by decide +kernel
  have hsubgood : good ⊆ Finset.univ.filter (fun x : (i : Fin 2) → Fin 6 =>
      wk ^ (e6 (x 0) + 2 * e6 (x 1)) - 1 ≠ 0) := by
    intro x hx
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have hnotdvd : ¬ 5 ∣ (e6 (x 0) + 2 * e6 (x 1)) := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact hx
    have hne : wk ^ (e6 (x 0) + 2 * e6 (x 1)) ≠ 1 := by
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have hord : orderOf wk = 5 := orderOf_eq_prime hw5k hw1k
      intro h1
      have hdvd : orderOf wk ∣ e6 (x 0) + 2 * e6 (x 1) :=
        orderOf_dvd_iff_pow_eq_one.mpr h1
      rw [hord] at hdvd
      exact hnotdvd hdvd
    simpa [sub_ne_zero] using hne
  have hle := Finset.card_le_card hsubgood
  rw [hgoodcard] at hle
  omega


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg
