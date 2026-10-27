module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Cover
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2LinBlock
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorLinLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


private lemma l02qq2lr_linConjAut_eq_one_scalar {d : ℕ} (hd : 2 ≤ d) {K : Type} [Field K]
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

private lemma l02qq2lr_orderOf_linConjAut_odd {N p n : ℕ} {K : Type} [Field K] [Finite K]
    (hN : 2 ≤ N) (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {g : GL (Fin N) K}
    {u : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K))}
    (hgu : u = TableB.linConjAut (Fin N) K g) (huord : orderOf u = p)
    (hp : p.Prime) (hp2 : p ≠ 2) : Odd (orderOf g) := by
  classical
  have hker : TableB.linConjAut (Fin N) K (g ^ p) = 1 := by
    rw [map_pow, ← hgu, ← huord, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := l02qq2lr_linConjAut_eq_one_scalar hN hker
  have hgp : (g ^ p) ^ (2 ^ n - 1) = 1 := by
    rw [← hc, ← map_pow]
    have hcunit : c ^ (2 ^ n - 1) = 1 := by
      haveI : Fintype Kˣ := Fintype.ofFinite Kˣ
      have hcard : Fintype.card Kˣ = 2 ^ n - 1 := by
        rw [← Nat.card_eq_fintype_card, Nat.card_units, hK]
      have := pow_card_eq_one (x := c)
      rwa [hcard] at this
    rw [hcunit, map_one]
  have hgpow : g ^ (p * (2 ^ n - 1)) = 1 := by
    rw [pow_mul]; exact hgp
  have hdvd : orderOf g ∣ p * (2 ^ n - 1) := orderOf_dvd_iff_pow_eq_one.mpr hgpow
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hnodd : Odd (2 ^ n - 1) := by
    have h2n : 2 ≤ 2 ^ n := by
      have := Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by norm_num) hn
      simpa using this
    obtain ⟨k, hk⟩ := Nat.even_pow.mpr ⟨even_two, Nat.one_le_iff_ne_zero.mp hn⟩
    exact ⟨k - 1, by omega⟩
  exact (hpodd.mul hnodd).of_dvd_nat hdvd

theorem q2RToral_tagA {N n p : ℕ} (hN : 2 ≤ N) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hnot : ¬(p ∣ N ∧ p ∣ 2 ^ n - 1)) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    {A : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K)))} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ g : GL (Fin N) K, a = TableB.linConjAut (Fin N) K g)
    {u : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K))} (hu : u ∈ A) (hou : orderOf u = p)
    {J : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) K))}
    (hJ : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u))
    (hAJ : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J)
    (M : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)))
    (hM : ∀ α ∈ M, ∃ a ∈ A, ∀ j j' : ↥J,
      (j' : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) = a (j : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) →
        α (QuotientGroup.mk j) = QuotientGroup.mk j') :
    Q2LinearLift M := by
  classical
  haveI : CharP K 2 := charP_two_of_card hK
  obtain ⟨g_u, hgu⟩ := hAI u hu
  have hgodd : Odd (orderOf g_u) :=
    l02qq2lr_orderOf_linConjAut_odd hN hn hK hgu hou hp hp2
  have hJc : CFSG.Open.IsComponentOf J
      (ggAutFixedSubgroup (TableB.linConjAut (Fin N) K g_u)) := by
    rwa [← hgu]
  obtain ⟨C, hC, hCSL, hJeq⟩ := q1TorLin_component_lift hN g_u J hJc
  obtain ⟨m, D, iD, iFin, ψ, π, hsquare⟩ := q2Lin_block hN g_u hgodd C hC hCSL J hJeq
  let H : Subgroup (GL (Fin N) K) := A.comap (TableB.linConjAut (Fin N) K)
  have hnot' : ¬ (p ∣ N ∧ p ∣ Nat.card K - 1) := by
    rintro ⟨h1, h2⟩
    exact hnot ⟨h1, by rwa [hK] at h2⟩
  have hHcomm : IsMulCommutative H :=
    ggBstarAbelianPreimageJLin_comm_of_not_dvd hp hnot' A hA
  have hguH : g_u ∈ H := by
    change TableB.linConjAut (Fin N) K g_u ∈ A
    rw [← hgu]; exact hu
  haveI : IsMulCommutative H := hHcomm
  let Cc : Subgroup (GL (Fin N) K) := Subgroup.centralizer ({g_u} : Set (GL (Fin N) K))
  have hHle : H ≤ Cc := by
    intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa using mul_comm' (⟨h, hh⟩ : H) (⟨g_u, hguH⟩ : H)
  let f : ↥H →* GL (Fin m) D := π.comp (Subgroup.inclusion hHle)
  let G : Subgroup (GL (Fin m) D) := f.range
  have hGcomm : IsMulCommutative G := inferInstance
  refine ⟨m, D, iD, iFin, ψ, G, hGcomm, ?_⟩
  intro α hαM
  obtain ⟨a, haA, hrel⟩ := hM α hαM
  obtain ⟨g_a, hga⟩ := hAI a haA
  have hgaH : g_a ∈ H := by
    change TableB.linConjAut (Fin N) K g_a ∈ A
    rw [← hga]; exact haA
  have hgacent : g_a ∈ Cc := hHle hgaH
  refine ⟨π ⟨g_a, hgacent⟩, ?_, ?_⟩
  · exact MonoidHom.mem_range.mpr ⟨⟨g_a, hgaH⟩, rfl⟩
  · ext y
    obtain ⟨x, rfl⟩ := ψ.surjective y
    induction x using QuotientGroup.induction_on with
    | H j =>
      have hcond : ((⟨a (j : LargeEvenProj (LargeEvenSLGroup (Fin N) K)),
          hAJ a haA (j : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) j.2⟩ : ↥J) :
          LargeEvenProj (LargeEvenSLGroup (Fin N) K)) =
          TableB.linConjAut (Fin N) K g_a
            (j : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) := by
        simp only [← hga]
      have hS := hsquare ⟨g_a, hgacent⟩ j
        ⟨a (j : LargeEvenProj (LargeEvenSLGroup (Fin N) K)),
          hAJ a haA (j : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) j.2⟩ hcond
      have hrelj := hrel j
        ⟨a (j : LargeEvenProj (LargeEvenSLGroup (Fin N) K)),
          hAJ a haA (j : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) j.2⟩ rfl
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [hrelj]
      exact hS.symm

theorem q2RLevel_linear : Q2RLevel .linear := by
  intro p d Q lab hΛ hfits
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hp, hp2, hpd, hpQ, ht, hl, hQ⟩ := hfits
  have ht' : t = .A := ht
  subst ht'
  have hpd' : p ∣ l := by rwa [← hl] at hpd
  have hQsub : Q = 2 ^ n := hQ
  subst hQsub
  simp only [LargeEvenInLambda2] at hΛ
  obtain ⟨hn, hdl, _⟩ := hΛ
  intro Qc hQc
  dsimp only [LargeEvenRawDatum] at hQc ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQc
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  intro A hAab hAI u hu hou J hJ hAJ Kq iq iFq hKq hne M hM
  have hN : 2 ≤ l + 1 := by omega
  have hnot : ¬ (p ∣ l + 1 ∧ p ∣ 2 ^ n - 1) := by
    rintro ⟨h1, h2⟩
    exact hp.not_dvd_one (by
      have := Nat.dvd_sub h1 hpd'
      simpa using this)
  exact q2RToral_tagA hN hn hp hp2 hnot hK hAab
    (fun a ha => TableB.exists_eq_linConjAut (hAI a ha)) hu hou hJ hAJ M hM

theorem q2RLevel_fieldTwo : Q2RLevel .fieldTwo := by
  intro p d Q lab hΛ hfits
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hp, hp2, hpd, hpQ, ht, hn1, hrank, hp3, hQ⟩ := hfits
  have ht' : t = .A := ht
  subst ht'
  have hn1' : n = 1 := hn1
  subst hn1'
  have hQsub : Q = 4 := hQ
  subst hQsub
  have hp3' : p = 3 := hp3
  subst hp3'
  simp only [LargeEvenInLambda2] at hΛ
  obtain ⟨hn, hdl, _⟩ := hΛ
  have hN : 2 ≤ l + 1 := by omega
  have hnot : ¬ (3 ∣ l + 1 ∧ 3 ∣ 2 ^ 1 - 1) := by
    rintro ⟨-, h2⟩
    exact hp.not_dvd_one (by simpa using h2)
  intro Qc hQc
  dsimp only [LargeEvenRawDatum] at hQc ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQc
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  intro A hAab hAI u hu hou J hJ hAJ Kq iq iFq hKq hne M hM
  exact q2RToral_tagA hN hn hp hp2 hnot hK hAab
    (fun a ha => TableB.exists_eq_linConjAut (hAI a ha)) hu hou hJ hAJ M hM

end CFSG.StandardType
