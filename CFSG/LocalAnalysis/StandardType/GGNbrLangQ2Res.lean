module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorJInputs
public import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.StandardType.KGLangTorusSpan
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCentralLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGBstarAbelianPreimageJLinResInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
      ∀ (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (d : ℕ) (K : Type) [Field K] [Finite K]
        (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
        p ∣ d → p ∣ Nat.card K - 1 →
        IsMulCommutative
          ((((ggBsAut hN).range).map (kgInducedAut θ)).comap (TableB.linConjAut (Fin d) K))

private lemma l02qj9_linConjAut_eq_one_scalar {d : ℕ} (hd : 2 ≤ d) {K : Type} [Field K]
    {A : GL (Fin d) K} (hA : TableB.linConjAut (Fin d) K A = 1) :
    A ∈ (Matrix.GeneralLinearGroup.scalar (Fin d)).range := by
  classical
  have hsingle : ∀ i j : Fin d, i ≠ j →
      (A : Matrix (Fin d) (Fin d) K) * Matrix.single i j (1 : K) =
        Matrix.single i j (1 : K) * (A : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    let T : LargeEvenSLGroup (Fin d) K :=
      ⟨Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij (1 : K)), by
        rw [LargeEvenSLGroup, MonoidHom.mem_ker]
        apply Units.ext
        change (Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.transvection hij (1 : K)) : Matrix (Fin d) (Fin d) K).det = (1 : K)
        rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
          Matrix.SpecialLinearGroup.transvection_coe]
        simpa [Matrix.transvection] using Matrix.det_transvection_of_ne i j hij (1 : K)⟩
    let N : Subgroup (LargeEvenSLGroup (Fin d) K) :=
      (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSLGroup (Fin d) K)
    have h1 : TableB.linConjAut (Fin d) K A
        (T : LargeEvenProj (LargeEvenSLGroup (Fin d) K)) =
        (T : LargeEvenProj (LargeEvenSLGroup (Fin d) K)) := by
      simpa using DFunLike.congr_fun hA (T : LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    rw [TableB.linConjAut_mk] at h1
    let z : LargeEvenSLGroup (Fin d) K := (MulAut.conjNormal A T)⁻¹ * T
    have hzN : z ∈ N := by
      have hq := (QuotientGroup.eq (s := N)).mp h1
      simpa [z] using hq
    have hz : MulAut.conjNormal A T * z = T := by
      change MulAut.conjNormal A T * ((MulAut.conjNormal A T)⁻¹ * T) = T
      group
    have hzS : (z : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K :=
      Subgroup.mem_subgroupOf.mp hzN
    have hzcenter : (z : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K) := by
      rw [← CFSG.Open.StatedAPI.statedScalars_eq_center]
      exact hzS
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hzcenter
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hzcenter
    have hzGL : ((MulAut.conjNormal A T : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) *
        (z : GL (Fin d) K) = (T : GL (Fin d) K) := by
      simpa using congrArg Subtype.val hz
    rw [MulAut.conjNormal_apply] at hzGL
    rw [← hu] at hzGL
    have hAT : A * (T : GL (Fin d) K) * A⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin d) u⁻¹ * (T : GL (Fin d) K) := by
      calc A * (T : GL (Fin d) K) * A⁻¹
          = (A * (T : GL (Fin d) K) * A⁻¹ *
              Matrix.GeneralLinearGroup.scalar (Fin d) u) *
              (Matrix.GeneralLinearGroup.scalar (Fin d) u)⁻¹ := by group
        _ = (T : GL (Fin d) K) * (Matrix.GeneralLinearGroup.scalar (Fin d) u)⁻¹ := by
              rw [hzGL]
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) u⁻¹ * (T : GL (Fin d) K) := by
              rw [map_inv]
              exact (Matrix.GeneralLinearGroup.scalar_commute u⁻¹ (T : GL (Fin d) K)).symm
    have hTmat : ((T : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        1 + Matrix.single i j 1 := by
      change (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection hij (1 : K)) : Matrix (Fin d) (Fin d) K) = _
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        Matrix.SpecialLinearGroup.transvection_coe]
    have hAinv : (A : Matrix (Fin d) (Fin d) K) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    have hAinvA : ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        (A : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    let e : Matrix (Fin d) (Fin d) K := Matrix.single i j (1 : K)
    let R : Matrix (Fin d) (Fin d) K :=
      (A : Matrix (Fin d) (Fin d) K) * e *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
    have hATm : (A : Matrix (Fin d) (Fin d) K) * (1 + e) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        Matrix.scalar (Fin d) ((u⁻¹ : Kˣ) : K) * (1 + e) := by
      have h := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) hAT
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv, hTmat,
        Matrix.GeneralLinearGroup.coe_scalar] at h
      simpa [e] using h
    have hsplit : (A : Matrix (Fin d) (Fin d) K) * (1 + e) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + R := by
      rw [mul_add, mul_one, add_mul, hAinv]
    have hRexp : R = Matrix.scalar (Fin d) (((u⁻¹ : Kˣ) : K) - 1) +
        Matrix.scalar (Fin d) ((u⁻¹ : Kˣ) : K) * e := by
      have h := hATm
      rw [hsplit] at h
      have hR : R = Matrix.scalar (Fin d) ((u⁻¹ : Kˣ) : K) * (1 + e) - 1 := by
        rw [← h]
        abel
      rw [hR, mul_add, mul_one]
      rw [show Matrix.scalar (Fin d) (((u⁻¹ : Kˣ) : K) - 1) =
          Matrix.scalar (Fin d) ((u⁻¹ : Kˣ) : K) - 1 by
        rw [map_sub, map_one]]
      abel
    have he2 : e * e = 0 := by
      dsimp [e]
      rw [Matrix.single_mul_single_of_ne (h := hij.symm)]
    have hR2 : R * R = 0 := by
      simp only [R]
      calc (A : Matrix (Fin d) (Fin d) K) * e *
            ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
            ((A : Matrix (Fin d) (Fin d) K) * e *
              ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
          = (A : Matrix (Fin d) (Fin d) K) * e *
              (((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
                (A : Matrix (Fin d) (Fin d) K)) * e *
              ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
              noncomm_ring
        _ = (A : Matrix (Fin d) (Fin d) K) * e * 1 * e *
              ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
              rw [hAinvA]
        _ = (A : Matrix (Fin d) (Fin d) K) * (e * e) *
              ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
              noncomm_ring
        _ = 0 := by
              rw [he2, Matrix.mul_zero, Matrix.zero_mul]
    have hRentry : ∀ k : Fin d, R j k =
        (((u⁻¹ : Kˣ) : K) - 1) * (if j = k then 1 else 0) := by
      intro k
      rw [hRexp, Matrix.add_apply, Matrix.mul_apply]
      have hsum : (∑ l : Fin d, Matrix.scalar (Fin d) ((u⁻¹ : Kˣ) : K) j l *
          Matrix.single i j (1 : K) l k) = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        by_cases hli : l = i
        · rw [hli]
          have hji : ¬ j = i := fun h => hij h.symm
          simp [Matrix.scalar_apply, hji]
        · have hil : ¬ i = l := fun h => hli h.symm
          simp [Matrix.single_apply, hil]
      rw [hsum, add_zero]
      by_cases hjk : j = k
      · rw [hjk]
        simp [Matrix.scalar_apply]
      · simp [Matrix.scalar_apply, hjk]
    have hsq : (((u⁻¹ : Kˣ) : K) - 1) ^ 2 = 0 := by
      have h := congrFun (congrFun hR2 j) j
      rw [Matrix.mul_apply] at h
      have hsum : (∑ k : Fin d, R j k * R k j) = R j j * R j j := by
        refine Finset.sum_eq_single j ?_ ?_
        · intro k _ hk
          rw [hRentry k]
          have hkj : ¬ j = k := fun h => hk h.symm
          simp [hkj]
        · intro hj
          exact absurd (Finset.mem_univ j) hj
      rw [hsum, hRentry j] at h
      simpa [pow_two] using h
    have hu1 : ((u⁻¹ : Kˣ) : K) = 1 := by
      have hsub : ((u⁻¹ : Kˣ) : K) - 1 = 0 := by
        have h := hsq
        rw [pow_two] at h
        exact mul_self_eq_zero.mp h
      exact sub_eq_zero.mp hsub
    have hu1' : u⁻¹ = 1 := Units.ext hu1
    have hATm1 : (A : Matrix (Fin d) (Fin d) K) * (1 + e) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + e := by
      rw [hATm, hu1]
      simp
    have hAe : (A : Matrix (Fin d) (Fin d) K) * e *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = e := by
      rw [hsplit, add_left_cancel_iff] at hATm1
      simpa [R] using hATm1
    have hcomm : (A : Matrix (Fin d) (Fin d) K) * e = e * (A : Matrix (Fin d) (Fin d) K) := by
      have h := congrArg (fun M => M * (A : Matrix (Fin d) (Fin d) K)) hAe
      simpa [Matrix.mul_assoc, hAinvA] using h
    simpa [e] using hcomm
  have hpair : Pairwise fun i j : Fin d =>
      Commute (Matrix.single i j 1) (A : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    exact (hsingle i j hij).symm
  have hrange : (A : Matrix (Fin d) (Fin d) K) ∈
      Set.range (Matrix.scalar (Fin d)) :=
    Matrix.mem_range_scalar_of_commute_single hpair
  obtain ⟨a, ha⟩ := hrange
  have ha0 : a ≠ 0 := by
    intro h0
    have hzero : (A : Matrix (Fin d) (Fin d) K) = 0 := by
      rw [← ha, h0, map_zero]
    have hAinv2 : (A : Matrix (Fin d) (Fin d) K) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    have hentry := congrFun (congrFun hAinv2 (⟨0, by omega⟩ : Fin d)) (⟨0, by omega⟩ : Fin d)
    simp [Matrix.mul_apply, hzero] at hentry
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  exact ha

theorem linConjAut_ker_le_center {d : ℕ} (hd : 2 ≤ d) {K : Type} [Field K] :
    (TableB.linConjAut (Fin d) K).ker ≤ Subgroup.center (GL (Fin d) K) := by
  intro A hA
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact l02qj9_linConjAut_eq_one_scalar hd (MonoidHom.mem_ker.mp hA)

theorem q2Lin_commutative_fullPreimage {d : ℕ} (hd : 2 ≤ d) {K : Type} [Field K]
    (V : Subgroup (GL (Fin d) K)) (hV : IsMulCommutative ↥V) :
    IsMulCommutative
      ((V.map (TableB.linConjAut (Fin d) K)).comap (TableB.linConjAut (Fin d) K)) := by
  apply IsMulCommutative.of_comm
  intro x y
  apply Subtype.ext
  exact CFSG.LocalAnalysis.GorensteinLyons.commute_of_mem_comap_map
    (fun a ha b hb => by
      haveI : IsMulCommutative ↥V := hV
      exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥V) (⟨b, hb⟩ : ↥V)))
    (TableB.linConjAut (Fin d) K) (linConjAut_ker_le_center hd) x.2 y.2

private lemma l02qj9_pairing_pdiv {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hd : 2 ≤ d) (hpd : p ∣ d) (hK : ¬ p ∣ Nat.card K - 1)
    {x y : GL (Fin d) K} {c : Kˣ}
    (hxy : x * y = Matrix.GeneralLinearGroup.scalar (Fin d) c * (y * x))
    {μ : Kˣ} (hxp : x ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) μ) :
    x * y = y * x := by
  have hd0 : d ≠ 0 := by omega
  have hcd : c ^ d = 1 := by
    have h := congrArg Matrix.GeneralLinearGroup.det hxy
    simp only [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h
    rw [mul_comm (Matrix.GeneralLinearGroup.det y) (Matrix.GeneralLinearGroup.det x)] at h
    exact mul_right_cancel (show c ^ d *
        (Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det y) =
        1 * (Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det y) by
      rw [h.symm, one_mul])
  have hcp : c ^ p = 1 := by
    letI : Bracket (GL (Fin d) K) (GL (Fin d) K) := commutatorElement
    have hcomm : ⁅x, y⁆ = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
      rw [commutatorElement_def, hxy]; group
    have hcx : Commute x ⁅x, y⁆ := by
      rw [hcomm]; exact (Matrix.GeneralLinearGroup.scalar_commute c x).symm
    have hpow := Commute.commutatorElement_pow_left hcx p
    have hcommμ : ⁅Matrix.GeneralLinearGroup.scalar (Fin d) μ, y⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_commute]
      exact Matrix.GeneralLinearGroup.scalar_commute μ y
    rw [hxp, hcommμ, hcomm] at hpow
    have hscalar : Matrix.GeneralLinearGroup.scalar (Fin d) (c ^ p) = 1 := by
      rw [map_pow]; exact hpow
    haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd0⟩⟩
    apply Units.ext
    have hmat : Matrix.scalar (Fin d) ((c ^ p : Kˣ) : K) = Matrix.scalar (Fin d) (1 : K) := by
      have h := congrArg (fun u : GL (Fin d) K => (u : Matrix (Fin d) (Fin d) K)) hscalar
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_one] at h
      rw [← map_one (Matrix.scalar (Fin d))] at h
      exact h
    exact Matrix.scalar_inj.mp hmat
  have hcK : c ^ (Nat.card K - 1) = 1 := by
    letI : Fintype K := Fintype.ofFinite K
    have h := FiniteField.pow_card_sub_one_eq_one (c : K) (Units.ne_zero c)
    rw [Nat.card_eq_fintype_card]
    apply Units.ext
    push_cast
    exact h
  have hc : c = 1 :=
    (pow_eq_one_iff_of_coprime (hp.coprime_iff_not_dvd.2 hK)).mp ⟨hcp, hcK⟩
  simpa [hc] using hxy

theorem ggBstarAbelianPreimageJLin_comm_of_not_dvd {d p : ℕ} (hp : p.Prime) {K : Type} [Field K]
    [Finite K] (hnot : ¬ (p ∣ d ∧ p ∣ Nat.card K - 1))
    (M : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))))
    (hM : IsElemAbelian p M) :
    IsMulCommutative (M.comap (TableB.linConjAut (Fin d) K)) := by
  classical
  let f := TableB.linConjAut (Fin d) K
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  by_cases hd1 : d ≤ 1
  · have hd01 : d = 0 ∨ d = 1 := by omega
    rcases hd01 with rfl | rfl
    · exact Subsingleton.elim _ _
    · ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, mul_comm]
  · have hd : 2 ≤ d := by omega
    have hcommM : f (a : GL (Fin d) K) * f (b : GL (Fin d) K) =
        f (b : GL (Fin d) K) * f (a : GL (Fin d) K) := by
      haveI : IsMulCommutative M := hM.1
      exact congrArg Subtype.val
        (mul_comm' (⟨f (a : GL (Fin d) K), a.2⟩ : M)
          ⟨f (b : GL (Fin d) K), b.2⟩)
    have hker : f ((a : GL (Fin d) K) * (b : GL (Fin d) K) *
        (a : GL (Fin d) K)⁻¹ * (b : GL (Fin d) K)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcommM]
      group
    obtain ⟨c, hc⟩ := l02qj9_linConjAut_eq_one_scalar hd hker
    have hxy : (a : GL (Fin d) K) * (b : GL (Fin d) K) =
        Matrix.GeneralLinearGroup.scalar (Fin d) c * ((b : GL (Fin d) K) * (a : GL (Fin d) K)) := by
      rw [hc]
      group
    have hap : (f (a : GL (Fin d) K)) ^ p = 1 := hM.2 (f (a : GL (Fin d) K)) a.2
    have hkerp : f ((a : GL (Fin d) K) ^ p) = 1 := by
      rw [map_pow, hap]
    obtain ⟨μ, hμ⟩ := l02qj9_linConjAut_eq_one_scalar hd hkerp
    have hμ' : (a : GL (Fin d) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) μ := hμ.symm
    by_cases hpd : p ∣ d
    · have hK : ¬ p ∣ Nat.card K - 1 := fun hK => hnot ⟨hpd, hK⟩
      exact l02qj9_pairing_pdiv hp hd hpd hK hxy hμ'
    · exact kgLangC_pairing hp hpd hxy hμ'

theorem ggBstarAbelianPreimageJLinInput_of_res (hres : GGBstarAbelianPreimageJLinResInput) :
    GGBstarAbelianPreimageJLinInput := by
  intro G _ _ p B Bs x L D J hcfg hID hN d K _ _ θ
  by_cases hdiv : p ∣ d ∧ p ∣ Nat.card K - 1
  · exact hres G p B Bs x L D J hcfg hID hN d K θ hdiv.1 hdiv.2
  · have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
    have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
    exact ggBstarAbelianPreimageJLin_comm_of_not_dvd hp hdiv _
      (CFSG.Open.IsElemAbelian.map (ggBsAut_range_isElemAbelian hBs hN) (kgInducedAut θ))

end CFSG.StandardType
