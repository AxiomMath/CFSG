module

public import CFSG.RankThree.PartOne.KE.E7ThreeArith
public import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.RankThree.Classical2.TwistedE6Phi3Torus
public import Certificates.Certificate14976
public import Certificates.Certificate14977

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix Polynomial CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2 CFSG.RankThree.Chevalley
open scoped Matrix

variable {L : Type} [Field L]

theorem rootChar_scalar_sub_E7 {q : ℕ} (M : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ)
    (b : Fin Tag.E7.rank → Lˣ) (μ : Fin Tag.E7.rank → ℤ) :
    rootChar b ((Matrix.scalar (Fin Tag.E7.rank) (q : ℤ) - M) *ᵥ μ) =
      rootChar b μ ^ q * (rootChar b (M *ᵥ μ))⁻¹ := by
  rw [Matrix.sub_mulVec, rootChar_sub]
  have : (Matrix.scalar (Fin Tag.E7.rank) (q : ℤ)) *ᵥ μ = (q : ℤ) • μ := by
    ext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [this, rootChar_zsmul, zpow_natCast]

theorem mem_ker_monomialHom_iff_forall_E7 (N : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ)
    (b : Fin Tag.E7.rank → Lˣ) :
    b ∈ (CFSG.LocalAnalysis.ComponentInitial.monomialHom (G := Lˣ) Nᵀ).ker ↔ ∀ μ, rootChar b (N *ᵥ μ) = 1 := by
  have hcol : ∀ j, rootChar b (N *ᵥ Pi.single j 1) =
      (CFSG.LocalAnalysis.ComponentInitial.monomialHom (G := Lˣ) Nᵀ b) j := fun j => by
    rw [CFSG.LocalAnalysis.ComponentInitial.monomialHom_apply, rootChar]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Matrix.mulVec_single, Matrix.transpose_apply]
  rw [MonoidHom.mem_ker]
  constructor
  · intro h μ
    have hμ : μ = ∑ j, μ j • (Pi.single j 1 : Fin Tag.E7.rank → ℤ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hμ, Matrix.mulVec_sum, rootChar_sum]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Matrix.mulVec_smul, rootChar_zsmul, hcol, h, Pi.one_apply, _root_.one_zpow]
  · intro h
    funext j
    rw [← hcol, h, Pi.one_apply]

theorem e7T3_mem_fixed_iff_ker {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (M : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ) (a : Fin Tag.E7.rank → Lˣ) :
    a ∈ fixedCharTuples M Fr ↔
      a ∈ (CFSG.LocalAnalysis.ComponentInitial.monomialHom (G := Lˣ) (Matrix.scalar (Fin Tag.E7.rank) (q : ℤ) - M)ᵀ).ker := by
  rw [mem_ker_monomialHom_iff_forall_E7, mem_fixedCharTuples_iff]
  refine forall_congr' fun μ => ?_
  rw [rootChar_scalar_sub_E7, CTTorus.map_units_eq_pow hFr]
  constructor
  · intro h
    rw [h, mul_inv_cancel]
  · intro h
    exact (mul_inv_eq_one.1 h).symm

theorem charpoly_e7T3W :
    e7T3W.charpoly = (X - 1) * (X ^ 2 + X + 1) ^ 3 := by
  have hnat : ((X - 1) * (X ^ 2 + X + 1) ^ 3 : ℤ[X]).natDegree ≤ 7 := by compute_degree
  refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq
    ((Finset.range 8).image (fun n : ℕ => (n : ℤ))) ?_ ?_ ?_
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range,
      Matrix.charpoly_degree_eq_dim]
    change ((7 : ℕ) : WithBot ℕ) < ((8 : ℕ) : WithBot ℕ)
    exact WithBot.coe_lt_coe.2 (by norm_num)
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hnat)
      (WithBot.coe_lt_coe.2 (by norm_num))
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
    rw [Matrix.eval_charpoly]
    have h := (Certificates.certificate14977) ⟨n, Finset.mem_range.1 hn⟩
    rw [CFSG.LieType.Chevalley.laplaceDet_eq_det] at h
    have e : Matrix.scalar (Fin Tag.E7.rank) (n : ℤ) - e7T3W =
        (Matrix.of fun i j : Fin 7 => if i = j then ((n : ℕ) : ℤ) else 0) -
          toMat 7 e7T3WList := by
      rw [e7T3W_eq]
      ext i j
      simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
      rfl
    rw [e]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_sub]
    exact h

theorem det_scalar_sub_smul_e7T3W {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (q : ℕ) :
    (Matrix.scalar (Fin Tag.E7.rank) (q : ℤ) - ε • e7T3W).det =
      ((q : ℤ) - ε) * ((q : ℤ) ^ 2 + ε * q + 1) ^ 3 := by
  have hee : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have h1 : Matrix.scalar (Fin Tag.E7.rank) (q : ℤ) - ε • e7T3W =
      ε • (Matrix.scalar (Fin Tag.E7.rank) (ε * (q : ℤ)) - e7T3W) := by
    rw [smul_sub]
    congr 1
    ext i j
    simp only [Matrix.scalar_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs
    · rw [← mul_assoc, hee, one_mul]
    · simp
  have h2 := congrArg (Polynomial.eval (ε * (q : ℤ))) charpoly_e7T3W
  rw [Matrix.eval_charpoly] at h2
  rw [h1, Matrix.det_smul, Fintype.card_fin, h2]
  have h7 : ε ^ Tag.E7.rank = ε := by
    rcases hε with rfl | rfl
    · exact one_pow _
    · exact Odd.neg_one_pow (by decide)
  rw [h7]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_sub]
  rcases hε with rfl | rfl <;> ring

theorem natCard_e7T3Fixed [IsAlgClosed L] {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (hq : ℓ ∣ q) :
    Nat.card (fixedCharTuples (ε • e7T3W) Fr) = e7T3Order q ε := by
  have hq0 : (q : L) = 0 := (CharP.cast_eq_zero_iff L ℓ q).2 hq
  have hdet := det_scalar_sub_smul_e7T3W hε q
  have hne : (((Matrix.scalar (Fin Tag.E7.rank) (q : ℤ) - ε • e7T3W)ᵀ).det : L) ≠ 0 := by
    rw [Matrix.det_transpose, hdet]
    push_cast
    rw [hq0]
    rcases hε with rfl | rfl <;> norm_num
  have h := natCard_ker_monomialHom (Ω := L)
    (Matrix.scalar (Fin Tag.E7.rank) (q : ℤ) - ε • e7T3W)ᵀ hne
  have hker : fixedCharTuples (ε • e7T3W) Fr =
      (CFSG.LocalAnalysis.ComponentInitial.monomialHom (G := Lˣ) (Matrix.scalar (Fin Tag.E7.rank) (q : ℤ) -
        ε • e7T3W)ᵀ).ker := Subgroup.ext fun a => e7T3_mem_fixed_iff_ker hFr _ a
  rw [hker, h, Matrix.det_transpose, hdet, Int.natAbs_mul, Int.natAbs_pow, e7T3Order]

theorem e7T3_twistedTorus [IsAlgClosed L] {ε : ℤ} (n : ModGL Tag.E7 L)
    (hnm : n ∈ monomialSubgroup Tag.E7 L)
    (hnW : ∀ u : Fin Tag.E7.rank → ℤ, weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • u = (ε • e7T3W) *ᵥ u)
    (Fr : L →+* L) :
    twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples (ε • e7T3W) Fr).map (rootDiagUnitHom Tag.E7 L) := by
  rw [← twistedFixedTuples_eq_fixedCharTuples hnW Fr]
  exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr

section TwoTorsion

theorem e7T3_rootChar_W {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {a : Fin Tag.E7.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (ε • e7T3W) Fr) (u : Fin Tag.E7.rank → ℤ) :
    rootChar a (e7T3W *ᵥ u) = rootChar a u ^ (ε * (q : ℤ)) := by
  have h := ha u
  rw [Matrix.smul_mulVec, rootChar_zsmul, CTTorus.map_units_eq_pow hFr] at h
  have hee : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  calc rootChar a (e7T3W *ᵥ u) = rootChar a (e7T3W *ᵥ u) ^ (ε * ε) := by rw [hee, zpow_one]
    _ = (rootChar a (e7T3W *ᵥ u) ^ ε) ^ ε := by rw [_root_.zpow_mul]
    _ = rootChar a u ^ (ε * (q : ℤ)) := by
      rw [h, ← zpow_natCast, ← _root_.zpow_mul, mul_comm]

theorem zpow_odd_of_sq_eq_one {x : Lˣ} (hx : x ^ 2 = 1) {n : ℤ} (hn : Odd n) : x ^ n = x := by
  obtain ⟨k, rfl⟩ := hn
  have hx' : x ^ (2 : ℤ) = 1 := by exact_mod_cast hx
  rw [_root_.zpow_add, zpow_one, _root_.zpow_mul, hx', _root_.one_zpow, one_mul]

theorem e7T3_rel_of_list {b : List ℤ} {c : ℤ}
    (h : vadd Tag.E7.rank (vadd Tag.E7.rank (lmulVec Tag.E7.rank e7T3WList
      (lmulVec Tag.E7.rank e7T3WList b)) (lmulVec Tag.E7.rank e7T3WList b)) b =
        vsmul Tag.E7.rank c e7T3FList) :
    e7T3W *ᵥ (e7T3W *ᵥ toVec Tag.E7.rank b) + e7T3W *ᵥ toVec Tag.E7.rank b +
      toVec Tag.E7.rank b = c • toVec Tag.E7.rank e7T3FList := by
  have h1 := congrArg (toVec Tag.E7.rank) h
  simp only [toVec_vadd, toVec_vsmul, toVec_lmulVec, ← e7T3W_eq] at h1
  exact h1

theorem e7T3_rel1 : e7T3W *ᵥ (e7T3W *ᵥ toVec Tag.E7.rank e7T3B1List) +
    e7T3W *ᵥ toVec Tag.E7.rank e7T3B1List + toVec Tag.E7.rank e7T3B1List =
      (0 : ℤ) • toVec Tag.E7.rank e7T3FList :=
  e7T3_rel_of_list (by decide +kernel)

theorem e7T3_rel2 : e7T3W *ᵥ (e7T3W *ᵥ toVec Tag.E7.rank e7T3B2List) +
    e7T3W *ᵥ toVec Tag.E7.rank e7T3B2List + toVec Tag.E7.rank e7T3B2List =
      (1 : ℤ) • toVec Tag.E7.rank e7T3FList :=
  e7T3_rel_of_list (by decide +kernel)

theorem e7T3_rel3 : e7T3W *ᵥ (e7T3W *ᵥ toVec Tag.E7.rank e7T3B3List) +
    e7T3W *ᵥ toVec Tag.E7.rank e7T3B3List + toVec Tag.E7.rank e7T3B3List =
      (1 : ℤ) • toVec Tag.E7.rank e7T3FList :=
  e7T3_rel_of_list (by decide +kernel)

theorem e7T3_two_torsion_block {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {a : Fin Tag.E7.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (ε • e7T3W) Fr) (ha2 : ∀ i, a i ^ 2 = 1)
    {b f : Fin Tag.E7.rank → ℤ} {c : ℤ}
    (hrel : e7T3W *ᵥ (e7T3W *ᵥ b) + e7T3W *ᵥ b + b = c • f) :
    rootChar a b = rootChar a f ^ c := by
  have hsq : ∀ u, rootChar a u ^ 2 = 1 := fun u => CTTorus.rootChar_pow_eq_one ha2 u
  have h1 := congrArg (rootChar a) hrel
  rw [rootChar_add, rootChar_add, rootChar_zsmul, e7T3_rootChar_W hε hFr ha,
    e7T3_rootChar_W hε hFr ha] at h1
  set e : ℤ := ε * (q : ℤ) with he
  have hodd : Odd (e * e + e + 1) := by
    have : Even (e * (e + 1)) := Int.even_mul_succ_self e
    have h2 : e * e + e + 1 = e * (e + 1) + 1 := by ring
    rw [h2]
    exact this.add_one
  have h3 : rootChar a b ^ (e * e + e + 1) = rootChar a f ^ c := by
    rw [← h1, _root_.zpow_add, _root_.zpow_add, zpow_one, ← _root_.zpow_mul]
  rwa [zpow_odd_of_sq_eq_one (hsq b) hodd] at h3

theorem rootChar_mulVec_cols {τ : Tag} (a : Fin τ.rank → Lˣ) (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (y : Fin τ.rank → ℤ) :
    rootChar a (M *ᵥ y) = ∏ k, rootChar a (fun i => M i k) ^ y k := by
  have h : M *ᵥ y = ∑ k, y k • (fun i => M i k) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [h, rootChar_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [rootChar_zsmul]

theorem e7T3_eq_of_cols {a b : Fin Tag.E7.rank → Lˣ}
    (h : ∀ k : Fin Tag.E7.rank,
      rootChar a (fun i => toMat Tag.E7.rank (lcols Tag.E7.rank e7T3ColsList) i k) =
        rootChar b (fun i => toMat Tag.E7.rank (lcols Tag.E7.rank e7T3ColsList) i k)) :
    a = b := by
  have hinv : lmul Tag.E7.rank (lcols Tag.E7.rank e7T3ColsList) e7T3BinvList = lid Tag.E7.rank :=
    (Certificates.certificate14976).2.1
  have hx : ∀ x : Fin Tag.E7.rank → ℤ, rootChar a x = rootChar b x := by
    intro x
    have hxe : x = toMat Tag.E7.rank (lcols Tag.E7.rank e7T3ColsList) *ᵥ
        (toMat Tag.E7.rank e7T3BinvList *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← toMat_lmul, hinv, toMat_lid, Matrix.one_mulVec]
    rw [hxe, rootChar_mulVec_cols, rootChar_mulVec_cols]
    exact Finset.prod_congr rfl fun k _ => by rw [h k]
  funext i
  rw [← CTTorus.rootChar_single a i, ← CTTorus.rootChar_single b i, hx]

@[expose] def e7T3ColVal (e : ℤ) (x : Lˣ) (k : Fin Tag.E7.rank) : Lˣ :=
  match k.val with
  | 0 => x
  | 1 => 1
  | 2 => 1
  | 3 => x
  | 4 => x ^ e
  | 5 => x
  | _ => x ^ e

theorem e7T3_col_val {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {a : Fin Tag.E7.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (ε • e7T3W) Fr) (ha2 : ∀ i, a i ^ 2 = 1)
    (k : Fin Tag.E7.rank) :
    rootChar a (fun i => toMat Tag.E7.rank (lcols Tag.E7.rank e7T3ColsList) i k) =
      e7T3ColVal (ε * (q : ℤ)) (rootChar a (toVec Tag.E7.rank e7T3FList)) k := by
  have hk : (fun i => toMat Tag.E7.rank (lcols Tag.E7.rank e7T3ColsList) i k) =
      toVec Tag.E7.rank (e7T3ColsList.getD k []) := by
    funext i
    rw [toMat_lcols]
    rfl
  rw [hk]
  have b1 := e7T3_two_torsion_block hε hFr ha ha2 e7T3_rel1
  have b2 := e7T3_two_torsion_block hε hFr ha ha2 e7T3_rel2
  have b3 := e7T3_two_torsion_block hε hFr ha ha2 e7T3_rel3
  have hW : ∀ b : List ℤ, rootChar a (toVec Tag.E7.rank (lmulVec Tag.E7.rank e7T3WList b)) =
      rootChar a (toVec Tag.E7.rank b) ^ (ε * (q : ℤ)) := fun b => by
    rw [toVec_lmulVec, ← e7T3W_eq, e7T3_rootChar_W hε hFr ha]
  fin_cases k
  · rfl
  · show rootChar a (toVec Tag.E7.rank e7T3B1List) = _
    rw [b1]
    simp [e7T3ColVal]
  · show rootChar a (toVec Tag.E7.rank (lmulVec Tag.E7.rank e7T3WList e7T3B1List)) = _
    rw [hW, b1]
    simp [e7T3ColVal]
  · show rootChar a (toVec Tag.E7.rank e7T3B2List) = _
    rw [b2]
    simp [e7T3ColVal]
  · show rootChar a (toVec Tag.E7.rank (lmulVec Tag.E7.rank e7T3WList e7T3B2List)) = _
    rw [hW, b2]
    simp [e7T3ColVal]
  · show rootChar a (toVec Tag.E7.rank e7T3B3List) = _
    rw [b3]
    simp [e7T3ColVal]
  · show rootChar a (toVec Tag.E7.rank (lmulVec Tag.E7.rank e7T3WList e7T3B3List)) = _
    rw [hW, b3]
    simp [e7T3ColVal]

theorem e7T3_card_two_torsion_le_two {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {Γ : Subgroup (Fin Tag.E7.rank → Lˣ)} (hΓ : Γ ≤ fixedCharTuples (ε • e7T3W) Fr) :
    Finite {a : Γ // a ^ 2 = 1} ∧ Nat.card {a : Γ // a ^ 2 = 1} ≤ 2 := by
  have hsq : ∀ a : Γ, a ^ 2 = 1 → ∀ i, (a : Fin Tag.E7.rank → Lˣ) i ^ 2 = 1 := by
    intro a ha i
    have h := congrFun (congrArg Subtype.val ha) i
    simpa using h
  let φ : {a : Γ // a ^ 2 = 1} → rootsOfUnity 2 L := fun a =>
    ⟨rootChar (a.1 : Fin Tag.E7.rank → Lˣ) (toVec Tag.E7.rank e7T3FList),
      (mem_rootsOfUnity 2 _).2 (CTTorus.rootChar_pow_eq_one (hsq a.1 a.2) _)⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : rootChar (a.1 : Fin Tag.E7.rank → Lˣ) (toVec Tag.E7.rank e7T3FList) =
        rootChar (b.1 : Fin Tag.E7.rank → Lˣ) (toVec Tag.E7.rank e7T3FList) :=
      congrArg (fun x : rootsOfUnity 2 L => ((x : Lˣ))) hab
    refine Subtype.ext (Subtype.ext (e7T3_eq_of_cols fun k => ?_))
    rw [e7T3_col_val hε hFr (hΓ a.1.2) (hsq a.1 a.2) k, e7T3_col_val hε hFr (hΓ b.1.2)
      (hsq b.1 b.2) k, h1]
  refine ⟨Finite.of_injective φ hφ, ?_⟩
  calc Nat.card {a : Γ // a ^ 2 = 1} ≤ Nat.card (rootsOfUnity 2 L) :=
        Nat.card_le_card_of_injective φ hφ
    _ ≤ 2 := card_rootsOfUnity L 2

end TwoTorsion

end CFSG.RankThree.PartOne.KE
