module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamDefs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.SylowIndex
public import CFSG.LocalAnalysis.SectionRank.OddCover.CubicCyclic
public import CFSG.RankThree.PartOne.LIT.RankPSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.ABGLocalTools (IsSylowOf)

private theorem k330c_three_dvd_add_one {Q : ℕ} (hQ : Q % 3 = 2) : 3 ∣ Q + 1 := by
  obtain ⟨m, hm⟩ : ∃ m, Q = 3 * m + 2 := by
    refine ⟨Q / 3, ?_⟩
    have := Nat.mod_add_div Q 3
    omega
  exact ⟨m + 1, by omega⟩

private theorem k330c_not_three_dvd_sub_one {Q : ℕ} (hQ : Q % 3 = 2) : ¬ 3 ∣ Q - 1 := by
  obtain ⟨m, hm⟩ : ∃ m, Q = 3 * m + 2 := by
    refine ⟨Q / 3, ?_⟩
    have := Nat.mod_add_div Q 3
    omega
  rintro ⟨k, hk⟩
  omega

private theorem k330c_nine_dvd_sq_sub_one_sq {Q : ℕ} (hQ : Q % 3 = 2) :
    9 ∣ (Q ^ 2 - 1) ^ 2 := by
  obtain ⟨m, hm⟩ : ∃ m, Q = 3 * m + 2 := by
    refine ⟨Q / 3, ?_⟩
    have := Nat.mod_add_div Q 3
    omega
  have h : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
    have h1 := Nat.sq_sub_sq Q 1
    rw [one_pow] at h1
    rw [mul_comm] at h1
    exact h1
  have hq : Q + 1 = 3 * (m + 1) := by omega
  refine ⟨(Q - 1) ^ 2 * (m + 1) ^ 2, ?_⟩
  rw [h, hq, mul_pow]
  ring

private theorem k330c_isMulCommutative_of_mulEquiv {M N : Type} [Group M] [Group N]
    (e : M ≃* N) (h : IsMulCommutative N) : IsMulCommutative M := by
  rw [isMulCommutative_iff] at h ⊢
  intro a b
  exact e.injective (by rw [map_mul, map_mul, h])

private theorem k330c_range_isMulCommutative {M N : Type} [Group M] [Group N] (f : M →* N)
    (h : IsMulCommutative M) : IsMulCommutative f.range := by
  rw [isMulCommutative_iff] at h ⊢
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨a', rfl⟩ := (MonoidHom.mem_range).1 ha
  obtain ⟨b', rfl⟩ := (MonoidHom.mem_range).1 hb
  exact Subtype.ext (by simpa only [Subgroup.coe_mul, map_mul] using congrArg f (h a' b'))

private theorem k330c_map_isMulCommutative {G N : Type} [Group G] [Group N] (f : G →* N)
    {S : Subgroup G} (h : IsMulCommutative S) : IsMulCommutative (S.map f) := by
  rw [isMulCommutative_iff] at h ⊢
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨a', ha', rfl⟩ := (Subgroup.mem_map).1 ha
  obtain ⟨b', hb', rfl⟩ := (Subgroup.mem_map).1 hb
  have hc := congrArg (fun z : ↥S => f (z : G)) (h ⟨a', ha'⟩ ⟨b', hb'⟩)
  exact Subtype.ext (by simpa only [Subgroup.coe_mul, map_mul] using hc)

private theorem k330c_card_map_mul_card_subgroupOf_ker {G N : Type} [Group G] [Group N]
    (f : G →* N) (T : Subgroup G) :
    Nat.card (T.map f) * Nat.card ((f.ker).subgroupOf T) = Nat.card T := by
  have h := Subgroup.card_ker_mul_card_range (f.comp T.subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
  have hker : (f.comp T.subtype).ker = (f.ker).subgroupOf T := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  rw [hker] at h
  rw [mul_comm] at h
  exact h

private def k330c_subgroupOfToSub {G : Type} [Group G] (N S : Subgroup G) :
    (N.subgroupOf S) →* N where
  toFun x := ⟨(x.1 : G), x.2⟩
  map_one' := by ext; rfl
  map_mul' x y := by ext; rfl

private theorem k330c_subgroupOfToSub_injective {G : Type} [Group G] (N S : Subgroup G) :
    Function.Injective (k330c_subgroupOfToSub N S) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : N => (z : G)) h))

private def k330c_blk5 {R : Type} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) (c : R) :
    Matrix (Fin 5) (Fin 5) R :=
  Matrix.of ![![A 0 0, A 0 1, 0, 0, 0], ![A 1 0, A 1 1, 0, 0, 0],
    ![0, 0, B 0 0, B 0 1, 0], ![0, 0, B 1 0, B 1 1, 0], ![0, 0, 0, 0, c]]

private theorem k330c_blk5_mul {R : Type} [CommRing R] (A B A' B' : Matrix (Fin 2) (Fin 2) R)
    (c c' : R) :
    k330c_blk5 A B c * k330c_blk5 A' B' c' = k330c_blk5 (A * A') (B * B') (c * c') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k330c_blk5, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two]

private theorem k330c_blk5_one {R : Type} [CommRing R] :
    k330c_blk5 (1 : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [k330c_blk5]

private theorem k330c_det_blk5 {R : Type} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R)
    (c : R) : (k330c_blk5 A B c).det = A.det * B.det * c := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, k330c_blk5, Fin.succAbove]
  ring

private theorem k330c_blk5_injective {R : Type} [CommRing R] {A B A' B' : Matrix (Fin 2) (Fin 2) R}
    {c c' : R} (h : k330c_blk5 A B c = k330c_blk5 A' B' c') : A = A' ∧ B = B' := by
  have e : ∀ i j : Fin 5, k330c_blk5 A B c i j = k330c_blk5 A' B' c' i j := fun i j => by rw [h]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [k330c_blk5] using e 0 0
    · simpa [k330c_blk5] using e 0 1
    · simpa [k330c_blk5] using e 1 0
    · simpa [k330c_blk5] using e 1 1
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [k330c_blk5] using e 2 2
    · simpa [k330c_blk5] using e 2 3
    · simpa [k330c_blk5] using e 3 2
    · simpa [k330c_blk5] using e 3 3

private def k330c_uu {K : Type} [Field K] (p : GL (Fin 2) K × GL (Fin 2) K) : Kˣ :=
  (Matrix.GeneralLinearGroup.det p.1 * Matrix.GeneralLinearGroup.det p.2)⁻¹

private theorem k330c_uu_mul {K : Type} [Field K] (p q : GL (Fin 2) K × GL (Fin 2) K) :
    k330c_uu (p * q) = k330c_uu p * k330c_uu q := by
  simp only [k330c_uu, Prod.fst_mul, Prod.snd_mul, map_mul]
  rw [mul_mul_mul_comm, mul_inv]

private def k330c_embGL5 {K : Type} [Field K] :
    GL (Fin 2) K × GL (Fin 2) K →* GL (Fin 5) K :=
  MonoidHom.mk' (fun p =>
    { val := k330c_blk5 (p.1 : Matrix (Fin 2) (Fin 2) K) (p.2 : Matrix (Fin 2) (Fin 2) K)
        ((k330c_uu p : Kˣ) : K)
      inv := k330c_blk5 ((p.1⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        ((p.2⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) (((k330c_uu p)⁻¹ : Kˣ) : K)
      val_inv := by
        rw [k330c_blk5_mul, Units.mul_inv, Units.mul_inv, Units.mul_inv, k330c_blk5_one]
      inv_val := by
        rw [k330c_blk5_mul, Units.inv_mul, Units.inv_mul, Units.inv_mul, k330c_blk5_one] })
    (fun p q => Units.ext (by
      show k330c_blk5 ((p * q).1 : Matrix (Fin 2) (Fin 2) K)
          ((p * q).2 : Matrix (Fin 2) (Fin 2) K) ((k330c_uu (p * q) : Kˣ) : K) =
        k330c_blk5 (p.1 : Matrix (Fin 2) (Fin 2) K) (p.2 : Matrix (Fin 2) (Fin 2) K)
            ((k330c_uu p : Kˣ) : K) *
          k330c_blk5 (q.1 : Matrix (Fin 2) (Fin 2) K) (q.2 : Matrix (Fin 2) (Fin 2) K)
            ((k330c_uu q : Kˣ) : K)
      simp only [k330c_blk5_mul, Prod.fst_mul, Prod.snd_mul, Units.val_mul, k330c_uu_mul]))

private theorem k330c_coe_embGL5 {K : Type} [Field K] (p : GL (Fin 2) K × GL (Fin 2) K) :
    ((k330c_embGL5 (K := K) p : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      k330c_blk5 (p.1 : Matrix (Fin 2) (Fin 2) K) (p.2 : Matrix (Fin 2) (Fin 2) K)
        ((k330c_uu p : Kˣ) : K) := rfl

private theorem k330c_embGL5_injective {K : Type} [Field K] :
    Function.Injective (k330c_embGL5 (K := K)) := by
  intro p q h
  have h1 := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K)) h
  obtain ⟨hA, hB⟩ := k330c_blk5_injective h1
  exact Prod.ext (Units.ext hA) (Units.ext hB)

private theorem k330c_det_embGL5 {K : Type} [Field K] (p : GL (Fin 2) K × GL (Fin 2) K) :
    ((k330c_embGL5 (K := K) p : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
  rw [k330c_coe_embGL5, k330c_det_blk5, ← Matrix.GeneralLinearGroup.val_det_apply,
    ← Matrix.GeneralLinearGroup.val_det_apply, ← Units.val_mul, ← Units.val_mul]
  have h : Matrix.GeneralLinearGroup.det p.1 * Matrix.GeneralLinearGroup.det p.2 * k330c_uu p =
      1 := mul_inv_cancel _
  rw [h, Units.val_one]

private def k330c_embSL5 {K : Type} [Field K] :
    GL (Fin 2) K × GL (Fin 2) K →* StatedSL 5 K :=
  (k330c_embGL5 (K := K)).codRestrict (StatedSL 5 K)
    (fun p => CFSG.Open.StatedAPI.mem_statedSL_of_det (k330c_det_embGL5 p))

private theorem k330c_embSL5_injective {K : Type} [Field K] :
    Function.Injective (k330c_embSL5 (K := K)) := by
  intro x y h
  have h1 : k330c_embGL5 (K := K) x = k330c_embGL5 (K := K) y := by
    simpa [k330c_embSL5, MonoidHom.codRestrict_apply] using congrArg Subtype.val h
  exact k330c_embGL5_injective h1

private def k330c_detProd {K : Type} [Field K] :
    GL (Fin 2) K × GL (Fin 2) K →* Kˣ where
  toFun p := Matrix.GeneralLinearGroup.det p.1 * Matrix.GeneralLinearGroup.det p.2
  map_one' := by simp
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    ac_rfl

private theorem k330c_diagGLHom_injective {K : Type} [Field K] :
    Function.Injective (CFSG.GH74.L5U5.diagGLHom K) := by
  intro p q h
  exact Prod.ext (CFSG.GH74.L5U5.diagGL_inj h).1 (CFSG.GH74.L5U5.diagGL_inj h).2

private def k330c_embSL4 {K : Type} [Field K] :
    (k330c_detProd (K := K)).ker →* StatedSL 4 K where
  toFun x :=
    ⟨CFSG.GH74.L5U5.diagGLHom K (x.1 : GL (Fin 2) K × GL (Fin 2) K),
      CFSG.Open.StatedAPI.mem_statedSL_of_det (by
        change ((CFSG.GH74.L5U5.diagGL (x.1 : GL (Fin 2) K × GL (Fin 2) K).1
          (x.1 : GL (Fin 2) K × GL (Fin 2) K).2 : GL (Fin 4) K) :
            Matrix (Fin 4) (Fin 4) K).det = 1
        rw [CFSG.GH74.L5U5.det_diagGL, ← Matrix.GeneralLinearGroup.val_det_apply,
          ← Matrix.GeneralLinearGroup.val_det_apply, ← Units.val_mul]
        have hx : Matrix.GeneralLinearGroup.det (x.1 : GL (Fin 2) K × GL (Fin 2) K).1 *
            Matrix.GeneralLinearGroup.det (x.1 : GL (Fin 2) K × GL (Fin 2) K).2 = 1 :=
          (MonoidHom.mem_ker).1 x.2
        rw [hx, Units.val_one])⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [Subgroup.coe_mul, map_mul])

private theorem k330c_embSL4_injective {K : Type} [Field K] :
    Function.Injective (k330c_embSL4 (K := K)) := by
  intro x y h
  have h1 : CFSG.GH74.L5U5.diagGLHom K (x.1 : GL (Fin 2) K × GL (Fin 2) K) =
      CFSG.GH74.L5U5.diagGLHom K (y.1 : GL (Fin 2) K × GL (Fin 2) K) := by
    simpa [k330c_embSL4] using congrArg Subtype.val h
  exact Subtype.ext (k330c_diagGLHom_injective h1)

private theorem k330c_pow_card_scalar {K : Type} [Field K] {n : ℕ} {c : Kˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSL n K) : c ^ n = 1 := by
  have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSL hc
  rw [← Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  exact Units.ext (by simpa using hdet)

private theorem k330c_torusBig_of_abelian {G : Type} [Group G] [Finite G] {L : ℕ}
    {H : Subgroup G} (hcomm : IsMulCommutative H) (hidx : ¬ 3 ∣ H.index)
    (hcard : L ≤ Nat.card H) : TorusBig G L := by
  intro Z hZ hZ9
  obtain ⟨x, hx⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.exists_conj_le_of_not_dvd_index
      Nat.prime_three H hidx Z hZ.isPGroup
  let H' : Subgroup G := H.map (MulAut.conj x⁻¹).toMonoidHom
  have hZH' : Z ≤ H' := by
    intro z hz
    refine Subgroup.mem_map.2 ⟨x * z * x⁻¹, hx z hz, ?_⟩
    show (MulAut.conj x⁻¹) (x * z * x⁻¹) = z
    rw [MulAut.conj_apply]
    group
  have hH'comm : IsMulCommutative H' := k330c_map_isMulCommutative _ hcomm
  have hH'cen : H' ≤ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact hZH'.trans (Subgroup.le_centralizer_iff_isMulCommutative.2 hH'comm)
  have hH'norm : H' ≤ Subgroup.normalizer (Z : Set G) :=
    hH'cen.trans (Subgroup.centralizer_le_normalizer _)
  calc L ≤ Nat.card H := hcard
    _ = Nat.card H' := (Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective).symm
    _ ≤ Nat.card (Subgroup.normalizer (Z : Set G)) := Subgroup.card_le_of_le hH'norm

private theorem k330c_torusBig_of_abelian_card {G : Type} [Group G] [Finite G] {L : ℕ}
    {H : Subgroup G} (hcomm : IsMulCommutative H) (h9 : 9 ∣ Nat.card H)
    (hcard : L ≤ Nat.card H) : TorusBig G L := by
  by_cases hsep : ∃ Z : Subgroup G, IsSylowOf 3 Z ⊤ ∧ Nat.card Z = 9
  · obtain ⟨Z₀, hZ₀, hZ₀9⟩ := hsep
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hG3 : (Nat.card G).factorization 3 = 2 := by
      have h1 : Nat.card Z₀ = 3 ^ (Nat.card (⊤ : Subgroup G)).factorization 3 := hZ₀.card_eq
      rw [hZ₀9, Subgroup.card_top] at h1
      have h2 : 3 ^ (Nat.card G).factorization 3 = 3 ^ 2 := by
        rw [← h1]
        norm_num
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h2
    have hHle : (Nat.card H).factorization 3 ≤ (Nat.card G).factorization 3 :=
      ((Nat.factorization_le_iff_dvd (Nat.card_pos (α := ↥H)).ne'
        (Nat.card_pos (α := G)).ne').2
        (Subgroup.card_subgroup_dvd_card H)) 3
    have hHge : 2 ≤ (Nat.card H).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization (k := 2)
        (Nat.card_pos (α := ↥H)).ne').1
        (by simpa using h9)
    have hH3 : (Nat.card H).factorization 3 = 2 := by
      rw [hG3] at hHle
      omega
    have hidx : ¬ 3 ∣ H.index := by
      intro h3
      have hne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hge : 1 ≤ H.index.factorization 3 :=
        (Nat.prime_three.dvd_iff_one_le_factorization hne).1 h3
      have hfac : (Nat.card G).factorization 3 =
          (Nat.card H).factorization 3 + H.index.factorization 3 := by
        have h1 := congrArg (fun f : ℕ →₀ ℕ => f 3)
          (Nat.factorization_mul (Nat.card_pos (α := ↥H)).ne' hne)
        rw [Subgroup.card_mul_index H] at h1
        exact h1
      rw [hG3, hH3] at hfac
      omega
    exact k330c_torusBig_of_abelian hcomm hidx hcard
  · intro Z hZ hZ9
    exact absurd ⟨Z, hZ, hZ9⟩ hsep

private theorem k330c_torusBig_psl4 {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hK : Nat.card K = p ^ f) (hq : p ^ f % 3 = 2) {J : Type} [Group J] [Finite J]
    (e : J ≃* StatedProj (StatedSL 4 K)) : TorusBig J ((p ^ f - 1) ^ 3 / 4) := by
  obtain ⟨C, hCcyc, hCcard⟩ := CFSG.SectionRank.OddCover.exists_isCyclic_card_GL K 2
  haveI : IsCyclic C := hCcyc
  have hqK : Nat.card K % 3 = 2 := by rw [hK]; exact hq
  have hq2 : 2 ≤ p ^ f := by
    rcases Nat.eq_zero_or_pos (p ^ f) with h0 | hpos
    · rw [h0] at hq
      exact absurd hq (by norm_num)
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hpos) with h1 | h2
      · rw [← h1] at hq
        exact absurd hq (by norm_num)
      · omega
  let D : Subgroup (GL (Fin 2) K × GL (Fin 2) K) := C.prod C
  have hDcomm : IsMulCommutative D :=
    k330c_isMulCommutative_of_mulEquiv (Subgroup.prodEquiv C C)
      (IsMulCommutative.of_comm fun a b => Prod.ext (mul_comm' a.1 b.1) (mul_comm' a.2 b.2))
  have hDcard : Nat.card D = (Nat.card K ^ 2 - 1) ^ 2 := by
    have h1 : Nat.card D = Nat.card (C × C) :=
      Nat.card_congr (Subgroup.prodEquiv C C).toEquiv
    rw [h1, Nat.card_prod, hCcard]
    exact (pow_two (Nat.card K ^ 2 - 1)).symm
  let fdet : GL (Fin 2) K × GL (Fin 2) K →* Kˣ := k330c_detProd (K := K)
  let g : D →* Kˣ := fdet.comp D.subtype
  let A : Subgroup D := g.ker
  have hA : Nat.card A * Nat.card g.range = Nat.card D :=
    Subgroup.card_ker_mul_card_range g
  have hAD : Nat.card A * Nat.card g.range = (Nat.card K ^ 2 - 1) ^ 2 := by
    rw [hA, hDcard]
  have hrange_le : Nat.card g.range ≤ Nat.card K - 1 := by
    calc Nat.card g.range ≤ Nat.card (⊤ : Subgroup Kˣ) := Subgroup.card_le_of_le le_top
      _ = Nat.card Kˣ := Subgroup.card_top
      _ = Nat.card K - 1 := Nat.card_units K
  have hrange3 : ¬ 3 ∣ Nat.card g.range := by
    intro h3
    have hdvd : Nat.card g.range ∣ Nat.card K - 1 := by
      have h := Subgroup.card_subgroup_dvd_card (g.range)
      rwa [Nat.card_units K] at h
    exact k330c_not_three_dvd_sub_one hqK (h3.trans hdvd)
  have hAcard : (Nat.card K - 1) ^ 3 ≤ Nat.card A := by
    have hsq : (Nat.card K ^ 2 - 1) ^ 2 =
        (Nat.card K - 1) ^ 2 * (Nat.card K + 1) ^ 2 := by
      have h : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
        simpa using Nat.sq_sub_sq (Nat.card K) 1
      rw [h, mul_pow]
      ring
    have hle : (Nat.card K - 1) ^ 2 ≤ (Nat.card K + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega : Nat.card K - 1 ≤ Nat.card K + 1) 2
    have h4 : (Nat.card K - 1) ^ 4 ≤ (Nat.card K ^ 2 - 1) ^ 2 := by
      rw [hsq, show (Nat.card K - 1) ^ 4 =
        (Nat.card K - 1) ^ 2 * (Nat.card K - 1) ^ 2 by ring]
      exact Nat.mul_le_mul_left _ hle
    have h1 : (Nat.card K - 1) ^ 3 * (Nat.card K - 1) ≤
        Nat.card A * (Nat.card K - 1) := by
      calc (Nat.card K - 1) ^ 3 * (Nat.card K - 1) = (Nat.card K - 1) ^ 4 := by ring
        _ ≤ (Nat.card K ^ 2 - 1) ^ 2 := h4
        _ = Nat.card A * Nat.card g.range := hAD.symm
        _ ≤ Nat.card A * (Nat.card K - 1) := Nat.mul_le_mul_left _ hrange_le
    exact Nat.le_of_mul_le_mul_right h1 (by omega)
  have h9A : 9 ∣ Nat.card A := by
    have h9D : 9 ∣ (Nat.card K ^ 2 - 1) ^ 2 := k330c_nine_dvd_sq_sub_one_sq hqK
    have hcop : Nat.Coprime 9 (Nat.card g.range) := by
      rw [show 9 = 3 ^ 2 by norm_num]
      exact (Nat.coprime_pow_left_iff (by norm_num) 3 (Nat.card g.range)).2
        ((Nat.prime_three.coprime_iff_not_dvd).2 hrange3)
    have h9prod : 9 ∣ Nat.card A * Nat.card g.range := by
      rw [hAD]
      exact h9D
    exact hcop.dvd_of_dvd_mul_right h9prod
  have hAcomm : IsMulCommutative A := by
    haveI : IsMulCommutative D := hDcomm
    exact IsMulCommutative.of_comm fun x y => Subtype.ext (mul_comm' x.1 y.1)
  let φA : A →* (k330c_detProd (K := K)).ker :=
    { toFun := fun x => ⟨(x.1 : D), (MonoidHom.mem_ker).2 (by
        have hx := (MonoidHom.mem_ker).1 x.2
        change fdet (x.1 : D) = 1 at hx
        exact hx)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [Subgroup.coe_mul]) }
  have hφA_inj : Function.Injective φA := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : (k330c_detProd (K := K)).ker =>
      (z : GL (Fin 2) K × GL (Fin 2) K)) h))
  let φ : A →* StatedSL 4 K := (k330c_embSL4 (K := K)).comp φA
  have hφ_inj : Function.Injective φ := (k330c_embSL4_injective).comp hφA_inj
  let T0 : Subgroup (StatedSL 4 K) := φ.range
  have hTcard : Nat.card T0 = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hφ_inj).toEquiv).symm
  have hTcomm : IsMulCommutative T0 := k330c_range_isMulCommutative φ hAcomm
  let π : StatedSL 4 K →* StatedProj (StatedSL 4 K) :=
    QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K))
  let H : Subgroup (StatedProj (StatedSL 4 K)) := T0.map π
  have hHcomm : IsMulCommutative H := k330c_map_isMulCommutative π hTcomm
  have hsplit : Nat.card H * Nat.card ((π.ker).subgroupOf T0) = Nat.card T0 :=
    k330c_card_map_mul_card_subgroupOf_ker π T0
  have hker_le : Nat.card π.ker ≤ 4 := by
    rw [QuotientGroup.ker_mk']
    have hcen : ∀ q ∈ StatedSL 4 K, q ∈ Subgroup.center (GL (Fin 4) K) → q ^ 4 = 1 := by
      intro q hq hc
      have hqdet := CFSG.Open.StatedAPI.det_of_mem_statedSL hq
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
      obtain ⟨c, hc⟩ := hc
      rw [← hc] at hqdet ⊢
      rw [← Matrix.GeneralLinearGroup.val_det_apply,
        Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hqdet
      have hc4 : c ^ 4 = 1 := Units.ext (by simpa using hqdet)
      rw [← map_pow, hc4, map_one]
    have h := CFSG.RankThree.PartOne.LIT.card_scalars_le (K := K) (ι := Fin 4) (m := 4)
      (by norm_num) (StatedSL 4 K) hcen
    rwa [← CFSG.Open.StatedAPI.statedScalars_eq_center] at h
  have hker3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [QuotientGroup.ker_mk']
    refine CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf (M := StatedSL 4 K)
      Nat.prime_three (by norm_num : ¬ 3 ∣ 4) ?_
    intro c hc
    exact k330c_pow_card_scalar hc
  have hk_le : Nat.card ((π.ker).subgroupOf T0) ≤ 4 :=
    le_trans (Nat.card_le_card_of_injective (k330c_subgroupOfToSub π.ker T0)
      (k330c_subgroupOfToSub_injective π.ker T0)) hker_le
  have hk_dvd : Nat.card ((π.ker).subgroupOf T0) ∣ Nat.card π.ker := by
    have h := Subgroup.card_subgroup_dvd_card (k330c_subgroupOfToSub π.ker T0).range
    have hcardrange : Nat.card (k330c_subgroupOfToSub π.ker T0).range =
        Nat.card ((π.ker).subgroupOf T0) :=
      (Nat.card_congr (MonoidHom.ofInjective
        (k330c_subgroupOfToSub_injective π.ker T0)).toEquiv).symm
    rwa [hcardrange] at h
  have hk3 : ¬ 3 ∣ Nat.card ((π.ker).subgroupOf T0) :=
    fun h => hker3 (h.trans hk_dvd)
  have hHcard : (Nat.card K - 1) ^ 3 / 4 ≤ Nat.card H := by
    apply Nat.div_le_of_le_mul
    calc (Nat.card K - 1) ^ 3 ≤ Nat.card A := hAcard
      _ = Nat.card T0 := hTcard.symm
      _ = Nat.card H * Nat.card ((π.ker).subgroupOf T0) := hsplit.symm
      _ ≤ Nat.card H * 4 := Nat.mul_le_mul_left _ hk_le
      _ = 4 * Nat.card H := Nat.mul_comm _ _
  have h9T0 : 9 ∣ Nat.card T0 := by rw [hTcard]; exact h9A
  have h9H : 9 ∣ Nat.card H := by
    have hHfac : (Nat.card H).factorization 3 = (Nat.card T0).factorization 3 := by
      have h1 : (Nat.card H * Nat.card ((π.ker).subgroupOf T0)).factorization 3 =
          (Nat.card H).factorization 3 + (Nat.card ((π.ker).subgroupOf T0)).factorization 3 :=
        congrArg (fun f : ℕ →₀ ℕ => f 3)
          (Nat.factorization_mul (Nat.card_pos (α := ↥H)).ne'
            (Nat.card_pos (α := ↥((π.ker).subgroupOf T0))).ne')
      rw [hsplit] at h1
      rw [Nat.factorization_eq_zero_of_not_dvd hk3, add_zero] at h1
      exact h1.symm
    have h2T : 2 ≤ (Nat.card T0).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization (k := 2)
        (Nat.card_pos (α := ↥T0)).ne').1
        (by simpa using h9T0)
    have : 3 ^ 2 ∣ Nat.card H := by
      rw [Nat.prime_three.pow_dvd_iff_le_factorization (k := 2)
        (Nat.card_pos (α := ↥H)).ne']
      rw [hHfac]
      exact h2T
    simpa using this
  let HJ : Subgroup J := H.map e.symm.toMonoidHom
  have hHJcard : Nat.card HJ = Nat.card H :=
    Subgroup.card_map_of_injective e.symm.injective
  have hHJcomm : IsMulCommutative HJ := k330c_map_isMulCommutative e.symm.toMonoidHom hHcomm
  have hHJ9 : 9 ∣ Nat.card HJ := by rw [hHJcard]; exact h9H
  have hHJcardL : (p ^ f - 1) ^ 3 / 4 ≤ Nat.card HJ := by
    rw [hHJcard, ← hK]
    exact hHcard
  exact k330c_torusBig_of_abelian_card hHJcomm hHJ9 hHJcardL

private theorem k330c_torusBig_psl5 {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hK : Nat.card K = p ^ f) (hq : p ^ f % 3 = 2) {J : Type} [Group J] [Finite J]
    (e : J ≃* StatedProj (StatedSL 5 K)) : TorusBig J (((p ^ f) ^ 2 - 1) ^ 2 / 5) := by
  obtain ⟨C, hCcyc, hCcard⟩ := CFSG.SectionRank.OddCover.exists_isCyclic_card_GL K 2
  haveI : IsCyclic C := hCcyc
  have hqK : Nat.card K % 3 = 2 := by rw [hK]; exact hq
  let D : Subgroup (GL (Fin 2) K × GL (Fin 2) K) := C.prod C
  have hDcomm : IsMulCommutative D :=
    k330c_isMulCommutative_of_mulEquiv (Subgroup.prodEquiv C C)
      (IsMulCommutative.of_comm fun a b => Prod.ext (mul_comm' a.1 b.1) (mul_comm' a.2 b.2))
  have hDcard : Nat.card D = (Nat.card K ^ 2 - 1) ^ 2 := by
    have h1 : Nat.card D = Nat.card (C × C) :=
      Nat.card_congr (Subgroup.prodEquiv C C).toEquiv
    rw [h1, Nat.card_prod, hCcard]
    exact (pow_two (Nat.card K ^ 2 - 1)).symm
  let φ : D →* StatedSL 5 K := (k330c_embSL5 (K := K)).comp D.subtype
  have hφ_inj : Function.Injective φ :=
    (k330c_embSL5_injective).comp D.subtype_injective
  let T0 : Subgroup (StatedSL 5 K) := φ.range
  have hTcard : Nat.card T0 = Nat.card D :=
    (Nat.card_congr (MonoidHom.ofInjective hφ_inj).toEquiv).symm
  have hTcomm : IsMulCommutative T0 := k330c_range_isMulCommutative φ hDcomm
  let π : StatedSL 5 K →* StatedProj (StatedSL 5 K) :=
    QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf (StatedSL 5 K))
  let H : Subgroup (StatedProj (StatedSL 5 K)) := T0.map π
  have hHcomm : IsMulCommutative H := k330c_map_isMulCommutative π hTcomm
  have hsplit : Nat.card H * Nat.card ((π.ker).subgroupOf T0) = Nat.card T0 :=
    k330c_card_map_mul_card_subgroupOf_ker π T0
  have hker_le : Nat.card π.ker ≤ 5 := by
    rw [QuotientGroup.ker_mk']
    have hcen : ∀ q ∈ StatedSL 5 K, q ∈ Subgroup.center (GL (Fin 5) K) → q ^ 5 = 1 := by
      intro q hq hc
      have hqdet := CFSG.Open.StatedAPI.det_of_mem_statedSL hq
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
      obtain ⟨c, hc⟩ := hc
      rw [← hc] at hqdet ⊢
      rw [← Matrix.GeneralLinearGroup.val_det_apply,
        Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hqdet
      have hc5 : c ^ 5 = 1 := Units.ext (by simpa using hqdet)
      rw [← map_pow, hc5, map_one]
    have h := CFSG.RankThree.PartOne.LIT.card_scalars_le (K := K) (ι := Fin 5) (m := 5)
      (by norm_num) (StatedSL 5 K) hcen
    rwa [← CFSG.Open.StatedAPI.statedScalars_eq_center] at h
  have hker3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [QuotientGroup.ker_mk']
    refine CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf (M := StatedSL 5 K)
      Nat.prime_three (by norm_num : ¬ 3 ∣ 5) ?_
    intro c hc
    exact k330c_pow_card_scalar hc
  have hk_le : Nat.card ((π.ker).subgroupOf T0) ≤ 5 :=
    le_trans (Nat.card_le_card_of_injective (k330c_subgroupOfToSub π.ker T0)
      (k330c_subgroupOfToSub_injective π.ker T0)) hker_le
  have hk_dvd : Nat.card ((π.ker).subgroupOf T0) ∣ Nat.card π.ker := by
    have h := Subgroup.card_subgroup_dvd_card (k330c_subgroupOfToSub π.ker T0).range
    have hcardrange : Nat.card (k330c_subgroupOfToSub π.ker T0).range =
        Nat.card ((π.ker).subgroupOf T0) :=
      (Nat.card_congr (MonoidHom.ofInjective
        (k330c_subgroupOfToSub_injective π.ker T0)).toEquiv).symm
    rwa [hcardrange] at h
  have hk3 : ¬ 3 ∣ Nat.card ((π.ker).subgroupOf T0) :=
    fun h => hker3 (h.trans hk_dvd)
  have hHcard : (Nat.card K ^ 2 - 1) ^ 2 / 5 ≤ Nat.card H := by
    apply Nat.div_le_of_le_mul
    calc (Nat.card K ^ 2 - 1) ^ 2 = Nat.card D := hDcard.symm
      _ = Nat.card T0 := hTcard.symm
      _ = Nat.card H * Nat.card ((π.ker).subgroupOf T0) := hsplit.symm
      _ ≤ Nat.card H * 5 := Nat.mul_le_mul_left _ hk_le
      _ = 5 * Nat.card H := Nat.mul_comm _ _
  have h9T0 : 9 ∣ Nat.card T0 := by
    rw [hTcard, hDcard]
    exact k330c_nine_dvd_sq_sub_one_sq hqK
  have h9H : 9 ∣ Nat.card H := by
    have hHfac : (Nat.card H).factorization 3 = (Nat.card T0).factorization 3 := by
      have h1 : (Nat.card H * Nat.card ((π.ker).subgroupOf T0)).factorization 3 =
          (Nat.card H).factorization 3 + (Nat.card ((π.ker).subgroupOf T0)).factorization 3 :=
        congrArg (fun f : ℕ →₀ ℕ => f 3)
          (Nat.factorization_mul (Nat.card_pos (α := ↥H)).ne'
            (Nat.card_pos (α := ↥((π.ker).subgroupOf T0))).ne')
      rw [hsplit] at h1
      rw [Nat.factorization_eq_zero_of_not_dvd hk3, add_zero] at h1
      exact h1.symm
    have h2T : 2 ≤ (Nat.card T0).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization (k := 2)
        (Nat.card_pos (α := ↥T0)).ne').1
        (by simpa using h9T0)
    have : 3 ^ 2 ∣ Nat.card H := by
      rw [Nat.prime_three.pow_dvd_iff_le_factorization (k := 2)
        (Nat.card_pos (α := ↥H)).ne']
      rw [hHfac]
      exact h2T
    simpa using this
  let HJ : Subgroup J := H.map e.symm.toMonoidHom
  have hHJcard : Nat.card HJ = Nat.card H :=
    Subgroup.card_map_of_injective e.symm.injective
  have hHJcomm : IsMulCommutative HJ := k330c_map_isMulCommutative e.symm.toMonoidHom hHcomm
  have hHJ9 : 9 ∣ Nat.card HJ := by rw [hHJcard]; exact h9H
  have hHJcardL : ((p ^ f) ^ 2 - 1) ^ 2 / 5 ≤ Nat.card HJ := by
    rw [hHJcard, ← hK]
    exact hHcard
  exact k330c_torusBig_of_abelian_card hHJcomm hHJ9 hHJcardL

theorem torusBig_PSL (n : ℕ) (hn : n = 4 ∨ n = 5) {J : Type} [Group J] [Finite J] {p f : ℕ}
    (e : LieModel J .PSL n p f) (hq : p ^ f % 3 = 2) : TorusBig J (torusLow n (p ^ f)) := by
  rcases hn with rfl | rfl
  · obtain ⟨-, K, hfield, hfinite, hK, ⟨eiso⟩⟩ :=
      e.statedClassicalModel_of_ne_zero (by norm_num)
    letI : Field K := hfield
    letI : Finite K := hfinite
    change TorusBig J ((p ^ f - 1) ^ 3 / 4)
    exact k330c_torusBig_psl4 hK hq eiso
  · obtain ⟨-, K, hfield, hfinite, hK, ⟨eiso⟩⟩ :=
      e.statedClassicalModel_of_ne_zero (by norm_num)
    letI : Field K := hfield
    letI : Finite K := hfinite
    change TorusBig J (((p ^ f) ^ 2 - 1) ^ 2 / 5)
    exact k330c_torusBig_psl5 hK hq eiso

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
