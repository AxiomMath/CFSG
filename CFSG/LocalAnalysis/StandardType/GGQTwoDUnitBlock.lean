module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
import CFSG.ClassicalInvolution.Phan.Center
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux5
import CFSG.LocalAnalysis.StandardType.GGQTwoBlockAsmPair
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg Matrix

open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}

private theorem qtwoDU4_coordBlockSU_conj_le (σ : Equiv.Perm (Fin n)) (J : Finset (Fin n)) :
    (coordBlockSU K 2 f J).map
        ((MulAut.conj (ggPhanNSAPairAux_permElt (f := f) σ)).toMonoidHom) ≤
      coordBlockSU K 2 f (J.map σ.toEmbedding) := by
  rintro x ⟨y, hy, rfl⟩
  refine (mem_coordBlockSU_iff (K := K) (p := 2) (f := f)
    (J := J.map σ.toEmbedding)).mpr ?_
  intro i j hij
  change ((((ggPhanNSAPairAux_permElt (f := f) σ * y *
      (ggPhanNSAPairAux_permElt (f := f) σ)⁻¹ : Su K 2 f n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) i j = (if i = j then 1 else 0)
  rw [ggPhanNSAPairAux_permElt_conj_matrix (f := f) σ y, Matrix.submatrix_apply]
  have hy' := (mem_coordBlockSU_iff (K := K) (p := 2) (f := f) (J := J)).mp hy
  have hpre : σ⁻¹ i ∉ J ∨ σ⁻¹ j ∉ J := by
    rcases hij with hi | hj
    · refine Or.inl fun hJ => hi ?_
      rw [Finset.mem_map]
      exact ⟨σ⁻¹ i, hJ, by simp⟩
    · refine Or.inr fun hJ => hj ?_
      rw [Finset.mem_map]
      exact ⟨σ⁻¹ j, hJ, by simp⟩
  rw [hy' _ _ hpre]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg h, if_neg (fun hh => h (σ⁻¹.injective hh))]

theorem ggQTwoDUnit_coordBlockSU_conj (σ : Equiv.Perm (Fin n)) (J : Finset (Fin n)) :
    (coordBlockSU K 2 f J).map
        ((MulAut.conj (ggPhanNSAPairAux_permElt (f := f) σ)).toMonoidHom) =
      coordBlockSU K 2 f (J.map σ.toEmbedding) := by
  apply le_antisymm
  · exact qtwoDU4_coordBlockSU_conj_le (K := K) (f := f) σ J
  · intro x hx
    have hPinv : ggPhanNSAPairAux_permElt (K := K) (f := f) σ⁻¹ =
        (ggPhanNSAPairAux_permElt (K := K) (f := f) σ)⁻¹ := by
      apply Subtype.ext
      show Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) (σ⁻¹)⁻¹) =
        (Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ⁻¹))⁻¹
      rw [← map_inv, ggPermSL_inv]
    have hle := qtwoDU4_coordBlockSU_conj_le (K := K) (f := f) σ⁻¹ (J.map σ.toEmbedding)
    have hmap : (J.map σ.toEmbedding).map (σ⁻¹).toEmbedding = J := by
      ext i
      constructor
      · intro hi
        rw [Finset.mem_map] at hi
        obtain ⟨b, hb, hbi⟩ := hi
        rw [Finset.mem_map] at hb
        obtain ⟨c, hc, hcb⟩ := hb
        rw [Equiv.toEmbedding_apply] at hcb hbi
        rw [← hcb] at hbi
        have hci : c = i := by simpa using hbi
        simpa [hci] using hc
      · intro hi
        refine Finset.mem_map.mpr ⟨σ i, ?_, ?_⟩
        · exact Finset.mem_map.mpr ⟨i, hi, rfl⟩
        · simp
    have hw : (MulAut.conj (ggPhanNSAPairAux_permElt (K := K) (f := f) σ⁻¹)) x ∈
        coordBlockSU K 2 f J := by
      have := hle ⟨x, hx, rfl⟩
      simpa [hmap] using this
    refine ⟨(MulAut.conj (ggPhanNSAPairAux_permElt (K := K) (f := f) σ⁻¹)) x, hw, ?_⟩
    change MulAut.conj (ggPhanNSAPairAux_permElt (K := K) (f := f) σ)
      ((MulAut.conj (ggPhanNSAPairAux_permElt (K := K) (f := f) σ⁻¹)) x) = x
    rw [hPinv]
    simp only [MulAut.conj_apply, inv_inv]
    group

theorem ggQTwoDUnit_range_blockEmb_zero {k : ℕ} (hk : 0 + k ≤ n) :
    (blockEmb K 2 f n k 0 hk).range =
      coordBlockSU K 2 f (Finset.univ.filter fun i : Fin n => (i : ℕ) < k) := by
  set J : Finset (Fin n) := Finset.univ.filter fun i : Fin n => (i : ℕ) < k with hJdef
  have hJmem : ∀ i : Fin n, i ∈ J ↔ (i : ℕ) < k := by
    intro i; rw [hJdef]; simp
  apply le_antisymm
  · rintro x ⟨g, rfl⟩
    refine (mem_coordBlockSU_iff (K := K) (p := 2) (f := f) (J := J)).mpr ?_
    intro i j hij
    rw [coe_coe_blockEmb, blockMat_apply]
    rw [dif_neg (fun h => by
      rcases hij with hi | hj
      · exact hi ((hJmem i).mpr (by omega))
      · exact hj ((hJmem j).mpr (by omega)))]
    exact Matrix.one_apply
  · intro M hM
    have hM1 : ∀ i j : Fin n, (i ∉ J ∨ j ∉ J) →
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
          (1 : Matrix (Fin n) (Fin n) K) i j := by
      intro i j hij
      rw [(mem_coordBlockSU_iff (K := K) (p := 2) (f := f) (J := J)).mp hM i j hij,
        Matrix.one_apply]
    have hM1inv : ∀ i j : Fin n, (i ∉ J ∨ j ∉ J) →
        ((((M⁻¹ : Su K 2 f n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) i j =
          (1 : Matrix (Fin n) (Fin n) K) i j := by
      intro i j hij
      rw [(mem_coordBlockSU_iff (K := K) (p := 2) (f := f) (J := J)).mp
        ((coordBlockSU K 2 f J).inv_mem hM) i j hij, Matrix.one_apply]
    have hoff : ∀ j : Fin n, k ≤ j.val → j ∉ J := by
      intro j hj
      rw [hJmem]
      omega
    let Amat : Matrix (Fin k) (Fin k) K := fun x y =>
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (blockIdx 0 hk x) (blockIdx 0 hk y)
    let Bmat : Matrix (Fin k) (Fin k) K := fun x y =>
      ((((M⁻¹ : Su K 2 f n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)
        (blockIdx 0 hk x) (blockIdx 0 hk y)
    have heqA : blockMat n 0 Amat = ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      ext j l
      rw [blockMat_apply (F := K) (i := 0) (k := k)]
      by_cases hj : 0 ≤ j.val ∧ j.val < 0 + k
      · by_cases hl : 0 ≤ l.val ∧ l.val < 0 + k
        · rw [dif_pos ⟨hj, hl⟩]
          show ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
              (blockIdx 0 hk ⟨j.val - 0, by omega⟩)
              (blockIdx 0 hk ⟨l.val - 0, by omega⟩) =
            ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j l
          rw [show blockIdx 0 hk ⟨j.val - 0, by omega⟩ = j from
                Fin.ext (by simp only [blockIdx_val]; omega),
              show blockIdx 0 hk ⟨l.val - 0, by omega⟩ = l from
                Fin.ext (by simp only [blockIdx_val]; omega)]
        · rw [dif_neg (fun hh => hl hh.2)]
          exact (hM1 j l (Or.inr (hoff l (by omega)))).symm
      · rw [dif_neg (fun hh => hj hh.1)]
        exact (hM1 j l (Or.inl (hoff j (by omega)))).symm
    have heqB : blockMat n 0 Bmat =
        (((M⁻¹ : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      ext j l
      rw [blockMat_apply (F := K) (i := 0) (k := k)]
      by_cases hj : 0 ≤ j.val ∧ j.val < 0 + k
      · by_cases hl : 0 ≤ l.val ∧ l.val < 0 + k
        · rw [dif_pos ⟨hj, hl⟩]
          show ((((M⁻¹ : Su K 2 f n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)
              (blockIdx 0 hk ⟨j.val - 0, by omega⟩)
              (blockIdx 0 hk ⟨l.val - 0, by omega⟩) =
            ((((M⁻¹ : Su K 2 f n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) j l
          rw [show blockIdx 0 hk ⟨j.val - 0, by omega⟩ = j from
                Fin.ext (by simp only [blockIdx_val]; omega),
              show blockIdx 0 hk ⟨l.val - 0, by omega⟩ = l from
                Fin.ext (by simp only [blockIdx_val]; omega)]
        · rw [dif_neg (fun hh => hl hh.2)]
          exact (hM1inv j l (Or.inr (hoff l (by omega)))).symm
      · rw [dif_neg (fun hh => hj hh.1)]
        exact (hM1inv j l (Or.inl (hoff j (by omega)))).symm
    have hmul1 : Amat * Bmat = 1 := by
      apply blockMat_injective (k := k) hk
      rw [blockMat_mul (F := K) (i := 0) (k := k) hk, heqA, heqB, Subgroup.coe_inv,
        ← Units.val_mul, mul_inv_cancel, blockMat_one]
      rfl
    have hmul2 : Bmat * Amat = 1 := by
      apply blockMat_injective (k := k) hk
      rw [blockMat_mul (F := K) (i := 0) (k := k) hk, heqB, heqA, Subgroup.coe_inv,
        ← Units.val_mul, inv_mul_cancel, blockMat_one]
      rfl
    let Agl : GL (Fin k) K := ⟨Amat, Bmat, hmul1, hmul2⟩
    have hAglval : ((Agl : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = Amat := rfl
    have hblk : Agl ∈ SUid (unitaryInvolution K 2 f) k := by
      rw [mem_SUid]
      refine ⟨?_, ?_⟩
      · rw [hAglval, ← det_blockMat (F := K) hk Amat, heqA]
        exact (mem_SUid.mp M.2).1
      · have hMu := (mem_SUid.mp M.2).2
        rw [← heqA] at hMu
        rw [conjTr_blockMat, ← blockMat_mul (F := K) (m := n) (i := 0) (k := k) hk] at hMu
        have h2 : conjTr (unitaryInvolution K 2 f) Amat * Amat = 1 :=
          blockMat_injective (k := k) hk
            (hMu.trans (blockMat_one (F := K) (m := n) (i := 0) (k := k)).symm)
        rwa [hAglval]
    exact ⟨⟨Agl, hblk⟩, Subtype.ext (Units.ext heqA)⟩

theorem ggQTwoDUnit_coordBlockSU_comm {I J : Finset (Fin n)} (hIJ : Disjoint I J)
    {u v : Su K 2 f n} (hu : u ∈ coordBlockSU K 2 f I) (hv : v ∈ coordBlockSU K 2 f J) :
    u * v = v * u := by
  classical
  let P : Matrix (Fin n) (Fin n) K := ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1
  let Q : Matrix (Fin n) (Fin n) K := ((v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1
  have hP : ∀ i j : Fin n, ¬ (i ∈ I ∧ j ∈ I) → P i j = 0 := by
    intro i j hij
    have h1 : ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
        (1 : Matrix (Fin n) (Fin n) K) i j := by
      rw [(mem_coordBlockSU_iff.mp hu) i j (by tauto), Matrix.one_apply]
    simp only [P, Matrix.sub_apply, h1, sub_self]
  have hQ : ∀ i j : Fin n, ¬ (i ∈ J ∧ j ∈ J) → Q i j = 0 := by
    intro i j hij
    have h1 : ((v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
        (1 : Matrix (Fin n) (Fin n) K) i j := by
      rw [(mem_coordBlockSU_iff.mp hv) i j (by tauto), Matrix.one_apply]
    simp only [Q, Matrix.sub_apply, h1, sub_self]
  have hPQ : P * Q = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ I
    · have hkJ : k ∉ J := fun hkJ => (Finset.disjoint_left.mp hIJ) hk hkJ
      rw [hQ k j (fun h => hkJ h.1), mul_zero]
    · rw [hP i k (fun h => hk h.2), zero_mul]
  have hQP : Q * P = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ J
    · have hkI : k ∉ I := fun hkI => (Finset.disjoint_left.mp hIJ) hkI hk
      rw [hP k j (fun h => hkI h.1), mul_zero]
    · rw [hQ i k (fun h => hk h.2), zero_mul]
  have hum : ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + P := by
    dsimp only [P]; abel
  have hvm : ((v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + Q := by
    dsimp only [Q]; abel
  have hkey : ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [hum, hvm]
    have hdiff : (1 + P) * (1 + Q) - (1 + Q) * (1 + P) = P * Q - Q * P := by
      noncomm_ring
    rw [hPQ, hQP, sub_zero] at hdiff
    exact sub_eq_zero.mp hdiff
  apply Subtype.ext
  apply Units.ext
  exact hkey

theorem ggQTwoDUnit_eq_one_of_mem_center_coordBlockSU (hK : Nat.card K = 4) {n : ℕ}
    (hn : 3 ≤ n) {J : Finset (Fin n)} (hJ : J.card < n) {z : Su K 2 1 n}
    (hz : z ∈ Subgroup.center (Su K 2 1 n)) (hzJ : z ∈ coordBlockSU K 2 1 J) : z = 1 := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (K := K) (p := 2)
      (f := 1) hK') hn hz
  have hlt : J.card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact hJ
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have h1 : ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) k k = 1 := by
    rw [(mem_coordBlockSU_iff.mp hzJ) k k (Or.inl hk), if_pos rfl]
  have h2 := scalar_eq_one_of_apply_eq_one hu h1
  exact Subtype.ext (Units.ext h2)

theorem ggQTwoDUnit_injective_coordBlockSU (hK : Nat.card K = 4) {G : Type} [Group G]
    (ψ : Su K 2 1 n →* G) (hker : ψ.ker ≤ Subgroup.center (Su K 2 1 n)) (hn : 3 ≤ n)
    {J : Finset (Fin n)} (hJ : J.card < n) :
    Function.Injective (ψ.comp (coordBlockSU K 2 1 J).subtype) := by
  intro x y hxy
  have hz : (x : Su K 2 1 n) * (y : Su K 2 1 n)⁻¹ ∈ Subgroup.center (Su K 2 1 n) := by
    apply hker
    rw [MonoidHom.mem_ker]
    have hxy' : ψ (x : Su K 2 1 n) = ψ (y : Su K 2 1 n) := hxy
    rw [map_mul, map_inv, hxy', mul_inv_cancel]
  have hzS : (x : Su K 2 1 n) * (y : Su K 2 1 n)⁻¹ ∈ coordBlockSU K 2 1 J :=
    Subgroup.mul_mem _ x.2 (Subgroup.inv_mem _ y.2)
  exact Subtype.ext (mul_inv_eq_one.mp
    (ggQTwoDUnit_eq_one_of_mem_center_coordBlockSU hK hn hJ hz hzS))

theorem ggQTwoDUnit_card_map_coordBlockSU_three (hK : Nat.card K = 4) {G : Type} [Group G]
    (ψ : Su K 2 1 n →* G) (hker : ψ.ker ≤ Subgroup.center (Su K 2 1 n)) (hn : 4 ≤ n)
    {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Nat.card ↥((coordBlockSU K 2 1 {a, b, c}).map ψ) = 216 := by
  have hJcard : ({a, b, c} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  let S := coordBlockSU K 2 1 ({a, b, c} : Finset (Fin n))
  let φ : ↥S →* G := ψ.comp S.subtype
  have hφinj : Function.Injective φ :=
    ggQTwoDUnit_injective_coordBlockSU hK ψ hker (by omega) (by omega)
  have hrange : φ.range = S.map ψ := by
    ext z
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨(y : Su K 2 1 n), y.2, hy⟩
    · rintro ⟨y, hy, hzy⟩
      exact ⟨⟨y, hy⟩, hzy⟩
  have hcard : Nat.card ↥(S.map ψ) = Nat.card ↥S := by
    rw [← hrange, MonoidHom.range_eq_map φ, Subgroup.card_map_of_injective hφinj,
      Subgroup.card_top]
  calc Nat.card ↥((coordBlockSU K 2 1 {a, b, c}).map ψ) = Nat.card ↥(S.map ψ) := rfl
    _ = Nat.card ↥S := hcard
    _ = Nat.card (Su K 2 1 ({a, b, c} : Finset (Fin n)).card) := natCard_coordBlockSU _
    _ = Nat.card (Su K 2 1 3) := by rw [hJcard]
    _ = 216 := qTwoS34_card_Su_three hK

theorem ggQTwoDUnit_stdPair {G : Type} [Group G] (ψ : Su K 2 f n →* G)
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) (hn : 3 ≤ n) {x y z : Fin n}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    UnitaryBlockStandardPair K 2 f ((coordBlockSU K 2 f {x, y, z}).map ψ)
      ((ggSuPairBlock K 2 f n x y).map ψ) ((ggSuPairBlock K 2 f n y z).map ψ) := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  obtain ⟨σ, hσ0, hσ1, hσ2⟩ :=
    ggPhanNSAPairAux_exists_perm_three (a := i0) (b := i1) (c := i2) (i := x) (j := y) (k := z)
      (by simp [i0, i1, Fin.ext_iff]) (by simp [i0, i2, Fin.ext_iff])
      (by simp [i1, i2, Fin.ext_iff]) hxy hxz hyz
  let P : Su K 2 f n := ggPhanNSAPairAux_permElt (f := f) σ
  let θ : Su K 2 f 3 →* Su K 2 f n :=
    (MulAut.conj P).toMonoidHom.comp (blockEmb K 2 f n 3 0 (by omega))
  have hθinj : Function.Injective θ := by
    intro u v huv
    have h1 : blockEmb K 2 f n 3 0 (by omega) u =
        blockEmb K 2 f n 3 0 (by omega) v := by
      have := congrArg (fun w : Su K 2 f n => P⁻¹ * w * P) huv
      simpa [θ, MonoidHom.comp_apply, MulAut.conj_apply, mul_assoc] using this
    exact blockEmb_injective (by omega) h1
  have hU : (B12 K 2 f).map θ = ggSuPairBlock K 2 f n x y := by
    have hcomp : (θ.comp (embSUid (unitaryInvolution K 2 f) 2)) =
        (MulAut.conj P).toMonoidHom.comp (blockEmb K 2 f n 2 0 (by omega)) := by
      refine MonoidHom.ext fun A => ?_
      change MulAut.conj P (blockEmb K 2 f n 3 0 (by omega)
          (embSUid (unitaryInvolution K 2 f) 2 A)) =
        MulAut.conj P (blockEmb K 2 f n 2 0 (by omega) A)
      rw [embSUid_two_eq_blockEmb]
      exact congrArg (MulAut.conj P) (blockEmb_comp_apply _ _ A)
    rw [B12, ← MonoidHom.range_comp, hcomp, MonoidHom.range_comp,
      ggPhanNSAPairAux_range_blockEmb2 (p := 2) (f := f) (i := 0) (by omega),
      ggPhanNSAPairAux_suPairBlock_conj, hσ0, hσ1]
  have hV : (B23 K 2 f).map θ = ggSuPairBlock K 2 f n y z := by
    have hcomp : (θ.comp (embSUid (unitaryInvolution K 2 f) 0)) =
        (MulAut.conj P).toMonoidHom.comp (blockEmb K 2 f n 2 1 (by omega)) := by
      refine MonoidHom.ext fun A => ?_
      change MulAut.conj P (blockEmb K 2 f n 3 0 (by omega)
          (embSUid (unitaryInvolution K 2 f) 0 A)) =
        MulAut.conj P (blockEmb K 2 f n 2 1 (by omega) A)
      rw [embSUid_zero_eq_blockEmb]
      exact congrArg (MulAut.conj P) (blockEmb_comp_apply _ _ A)
    rw [B23, ← MonoidHom.range_comp, hcomp, MonoidHom.range_comp,
      ggPhanNSAPairAux_range_blockEmb2 (p := 2) (f := f) (i := 1) (by omega),
      ggPhanNSAPairAux_suPairBlock_conj, hσ1, hσ2]
  have hmap : (Finset.univ.filter fun i : Fin n => (i : ℕ) < 3).map σ.toEmbedding =
      {x, y, z} := by
    have h012 : (Finset.univ.filter fun i : Fin n => (i : ℕ) < 3) = {i0, i1, i2} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hi
        have hi' : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
        rcases hi' with h | h | h
        · left; exact Fin.ext (by simpa [i0] using h)
        · right; left; exact Fin.ext (by simpa [i1] using h)
        · right; right; exact Fin.ext (by simpa [i2] using h)
      · rintro (h | h | h)
        · rw [h]; simp [i0]
        · rw [h]; simp [i1]
        · rw [h]; simp [i2]
    rw [h012]
    simp only [Finset.map_insert, Finset.map_singleton, Equiv.toEmbedding_apply]
    rw [hσ0, hσ1, hσ2]
  have hθrange : θ.range = coordBlockSU K 2 f {x, y, z} := by
    change ((MulAut.conj P).toMonoidHom.comp (blockEmb K 2 f n 3 0 (by omega))).range =
      coordBlockSU K 2 f {x, y, z}
    rw [MonoidHom.range_comp, ggQTwoDUnit_range_blockEmb_zero (k := 3) (by omega),
      ggQTwoDUnit_coordBlockSU_conj, hmap]
  have hkerθ : (ψ.comp θ).ker ≤ Subgroup.center (Su K 2 f 3) := by
    intro g hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg
    have hcen : θ g ∈ Subgroup.center (Su K 2 f n) := hker hg
    rw [Subgroup.mem_center_iff] at hcen ⊢
    intro h
    apply hθinj
    rw [map_mul, map_mul]
    exact hcen (θ h)
  have hθrange' : (ψ.comp θ).range = (coordBlockSU K 2 f {x, y, z}).map ψ := by
    rw [MonoidHom.range_comp, hθrange]
  have hpair := CFSG.GH74.L5U5.unitaryBlockStandardPair_of_blocks (θ := ψ.comp θ) hkerθ
    (U := (ggSuPairBlock K 2 f n x y).map ψ) (V := (ggSuPairBlock K 2 f n y z).map ψ) ?_ ?_
  · rwa [hθrange'] at hpair
  · rw [← Subgroup.map_map, hU]
  · rw [← Subgroup.map_map, hV]

end CFSG.StandardType.QTwo

end
